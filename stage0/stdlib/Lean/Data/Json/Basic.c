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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* v_i_x27_211_; uint32_t v_c_212_; uint32_t v___x_213_; uint8_t v___x_214_; 
v_i_x27_211_ = lean_string_utf8_prev(v_s_205_, v_i_207_);
v_c_212_ = lean_string_utf8_get(v_s_205_, v_i_x27_211_);
v___x_213_ = 48;
v___x_214_ = lean_uint32_dec_eq(v_c_212_, v___x_213_);
if (v___x_214_ == 0)
{
lean_dec(v_i_x27_211_);
return v_i_207_;
}
else
{
lean_dec(v_i_207_);
v_i_207_ = v_i_x27_211_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0___boxed(lean_object* v_s_216_, lean_object* v_begPos_217_, lean_object* v_i_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(v_s_216_, v_begPos_217_, v_i_218_);
lean_dec(v_begPos_217_);
lean_dec_ref(v_s_216_);
return v_res_219_;
}
}
static lean_object* _init_l_Lean_JsonNumber_toString___closed__3(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_unsigned_to_nat(9u);
v___x_224_ = lean_nat_to_int(v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toString(lean_object* v_x_226_){
_start:
{
lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v_mantissa_237_; lean_object* v_exponent_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v_mantissa_237_ = lean_ctor_get(v_x_226_, 0);
lean_inc(v_mantissa_237_);
v_exponent_238_ = lean_ctor_get(v_x_226_, 1);
lean_inc(v_exponent_238_);
lean_dec_ref(v_x_226_);
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_nat_dec_eq(v_exponent_238_, v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_276_; uint8_t v___x_285_; 
v___x_241_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_285_ = lean_int_dec_le(v___x_241_, v_mantissa_237_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; 
v___x_286_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__4));
v___y_276_ = v___x_286_;
goto v___jp_275_;
}
else
{
lean_object* v___x_287_; 
v___x_287_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_276_ = v___x_287_;
goto v___jp_275_;
}
v___jp_242_:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v_e_254_; lean_object* v_right_255_; uint8_t v___x_256_; 
v___x_248_ = lean_nat_add(v___y_245_, v___y_243_);
lean_dec(v___y_243_);
lean_dec(v___y_245_);
v___x_249_ = l_Nat_reprFast(v___x_248_);
v___x_250_ = lean_string_utf8_byte_size(v___x_249_);
lean_inc_ref(v___x_249_);
v___x_251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_239_);
lean_ctor_set(v___x_251_, 2, v___x_250_);
v___x_252_ = lean_unsigned_to_nat(1u);
v___x_253_ = l_Substring_Raw_nextn(v___x_251_, v___x_252_, v___x_239_);
lean_dec_ref_known(v___x_251_, 3);
v_e_254_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(v___x_249_, v___x_253_, v___x_250_);
v_right_255_ = lean_string_utf8_extract(v___x_249_, v___x_253_, v_e_254_);
lean_dec(v_e_254_);
lean_dec(v___x_253_);
lean_dec_ref(v___x_249_);
v___x_256_ = lean_int_dec_eq(v___y_246_, v___x_241_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__1));
v___x_258_ = l_Int_repr(v___y_246_);
lean_dec(v___y_246_);
v___x_259_ = lean_string_append(v___x_257_, v___x_258_);
lean_dec_ref(v___x_258_);
v___y_228_ = v___y_244_;
v___y_229_ = v_right_255_;
v___y_230_ = v___y_247_;
v___y_231_ = v___x_259_;
goto v___jp_227_;
}
else
{
lean_object* v___x_260_; 
lean_dec(v___y_246_);
v___x_260_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_228_ = v___y_244_;
v___y_229_ = v_right_255_;
v___y_230_ = v___y_247_;
v___y_231_ = v___x_260_;
goto v___jp_227_;
}
}
v___jp_261_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v_e_x27_268_; lean_object* v___x_269_; lean_object* v_left_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_265_ = lean_unsigned_to_nat(10u);
v___x_266_ = lean_nat_abs(v___y_264_);
v___x_267_ = lean_nat_sub(v_exponent_238_, v___x_266_);
lean_dec(v___x_266_);
lean_dec(v_exponent_238_);
v_e_x27_268_ = lean_nat_pow(v___x_265_, v___x_267_);
lean_dec(v___x_267_);
v___x_269_ = lean_nat_div(v___y_262_, v_e_x27_268_);
v_left_270_ = l_Nat_reprFast(v___x_269_);
v___x_271_ = lean_nat_mod(v___y_262_, v_e_x27_268_);
lean_dec(v___y_262_);
v___x_272_ = lean_nat_dec_eq(v___x_271_, v___x_239_);
if (v___x_272_ == 0)
{
v___y_243_ = v___x_271_;
v___y_244_ = v___y_263_;
v___y_245_ = v_e_x27_268_;
v___y_246_ = v___y_264_;
v___y_247_ = v_left_270_;
goto v___jp_242_;
}
else
{
uint8_t v___x_273_; 
v___x_273_ = lean_int_dec_eq(v___y_264_, v___x_241_);
if (v___x_273_ == 0)
{
v___y_243_ = v___x_271_;
v___y_244_ = v___y_263_;
v___y_245_ = v_e_x27_268_;
v___y_246_ = v___y_264_;
v___y_247_ = v_left_270_;
goto v___jp_242_;
}
else
{
lean_object* v___x_274_; 
lean_dec(v___x_271_);
lean_dec(v_e_x27_268_);
lean_dec(v___y_264_);
lean_inc_ref(v___y_263_);
v___x_274_ = lean_string_append(v___y_263_, v_left_270_);
lean_dec_ref(v_left_270_);
return v___x_274_;
}
}
}
v___jp_275_:
{
lean_object* v_m_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v_exp_283_; uint8_t v___x_284_; 
v_m_277_ = lean_nat_abs(v_mantissa_237_);
lean_dec(v_mantissa_237_);
v___x_278_ = lean_obj_once(&l_Lean_JsonNumber_toString___closed__3, &l_Lean_JsonNumber_toString___closed__3_once, _init_l_Lean_JsonNumber_toString___closed__3);
lean_inc(v_m_277_);
v___x_279_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_m_277_);
v___x_280_ = lean_nat_to_int(v___x_279_);
v___x_281_ = lean_int_add(v___x_278_, v___x_280_);
lean_dec(v___x_280_);
lean_inc(v_exponent_238_);
v___x_282_ = lean_nat_to_int(v_exponent_238_);
v_exp_283_ = lean_int_sub(v___x_281_, v___x_282_);
lean_dec(v___x_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_int_dec_lt(v_exp_283_, v___x_241_);
if (v___x_284_ == 0)
{
lean_dec(v_exp_283_);
v___y_262_ = v_m_277_;
v___y_263_ = v___y_276_;
v___y_264_ = v___x_241_;
goto v___jp_261_;
}
else
{
v___y_262_ = v_m_277_;
v___y_263_ = v___y_276_;
v___y_264_ = v_exp_283_;
goto v___jp_261_;
}
}
}
else
{
lean_object* v___x_288_; 
lean_dec(v_exponent_238_);
v___x_288_ = l_Int_repr(v_mantissa_237_);
lean_dec(v_mantissa_237_);
return v___x_288_;
}
v___jp_227_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
lean_inc_ref(v___y_228_);
v___x_232_ = lean_string_append(v___y_228_, v___y_230_);
lean_dec_ref(v___y_230_);
v___x_233_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__0));
v___x_234_ = lean_string_append(v___x_232_, v___x_233_);
v___x_235_ = lean_string_append(v___x_234_, v___y_229_);
lean_dec_ref(v___y_229_);
v___x_236_ = lean_string_append(v___x_235_, v___y_231_);
lean_dec_ref(v___y_231_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl(lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
lean_object* v_mantissa_291_; lean_object* v_exponent_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_305_; 
v_mantissa_291_ = lean_ctor_get(v_x_289_, 0);
v_exponent_292_ = lean_ctor_get(v_x_289_, 1);
v_isSharedCheck_305_ = !lean_is_exclusive(v_x_289_);
if (v_isSharedCheck_305_ == 0)
{
v___x_294_ = v_x_289_;
v_isShared_295_ = v_isSharedCheck_305_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_exponent_292_);
lean_inc(v_mantissa_291_);
lean_dec(v_x_289_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_305_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_296_ = lean_unsigned_to_nat(10u);
v___x_297_ = lean_nat_sub(v_x_290_, v_exponent_292_);
v___x_298_ = lean_nat_pow(v___x_296_, v___x_297_);
lean_dec(v___x_297_);
v___x_299_ = lean_nat_to_int(v___x_298_);
v___x_300_ = lean_int_mul(v_mantissa_291_, v___x_299_);
lean_dec(v___x_299_);
lean_dec(v_mantissa_291_);
v___x_301_ = lean_nat_sub(v_exponent_292_, v_x_290_);
lean_dec(v_exponent_292_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 1, v___x_301_);
lean_ctor_set(v___x_294_, 0, v___x_300_);
v___x_303_ = v___x_294_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl___boxed(lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_JsonNumber_shiftl(v_x_306_, v_x_307_);
lean_dec(v_x_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr(lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
lean_object* v_mantissa_311_; lean_object* v_exponent_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_320_; 
v_mantissa_311_ = lean_ctor_get(v_x_309_, 0);
v_exponent_312_ = lean_ctor_get(v_x_309_, 1);
v_isSharedCheck_320_ = !lean_is_exclusive(v_x_309_);
if (v_isSharedCheck_320_ == 0)
{
v___x_314_ = v_x_309_;
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_exponent_312_);
lean_inc(v_mantissa_311_);
lean_dec(v_x_309_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_316_ = lean_nat_add(v_exponent_312_, v_x_310_);
lean_dec(v_exponent_312_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v___x_316_);
v___x_318_ = v___x_314_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_mantissa_311_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr___boxed(lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_JsonNumber_shiftr(v_x_321_, v_x_322_);
lean_dec(v_x_322_);
return v_res_323_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__0));
v___x_332_ = lean_string_length(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_obj_once(&l_Lean_JsonNumber_instRepr___lam__0___closed__4, &l_Lean_JsonNumber_instRepr___lam__0___closed__4_once, _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4);
v___x_334_ = lean_nat_to_int(v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0(lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
lean_object* v_mantissa_341_; lean_object* v_exponent_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_371_; 
v_mantissa_341_ = lean_ctor_get(v_x_339_, 0);
v_exponent_342_ = lean_ctor_get(v_x_339_, 1);
v_isSharedCheck_371_ = !lean_is_exclusive(v_x_339_);
if (v_isSharedCheck_371_ == 0)
{
v___x_344_ = v_x_339_;
v_isShared_345_ = v_isSharedCheck_371_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_exponent_342_);
lean_inc(v_mantissa_341_);
lean_dec(v_x_339_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_371_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___y_347_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_365_ = lean_int_dec_lt(v_mantissa_341_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = l_Int_repr(v_mantissa_341_);
lean_dec(v_mantissa_341_);
v___x_367_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
v___y_347_ = v___x_367_;
goto v___jp_346_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = l_Int_repr(v_mantissa_341_);
lean_dec(v_mantissa_341_);
v___x_369_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
v___x_370_ = l_Repr_addAppParen(v___x_369_, v___x_363_);
v___y_347_ = v___x_370_;
goto v___jp_346_;
}
v___jp_346_:
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__2));
if (v_isShared_345_ == 0)
{
lean_ctor_set_tag(v___x_344_, 5);
lean_ctor_set(v___x_344_, 1, v___x_348_);
lean_ctor_set(v___x_344_, 0, v___y_347_);
v___x_350_ = v___x_344_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___y_347_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v___x_348_);
v___x_350_ = v_reuseFailAlloc_362_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; 
v___x_351_ = l_Nat_reprFast(v_exponent_342_);
v___x_352_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
v___x_353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_350_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_obj_once(&l_Lean_JsonNumber_instRepr___lam__0___closed__5, &l_Lean_JsonNumber_instRepr___lam__0___closed__5_once, _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5);
v___x_355_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__6));
v___x_356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___x_353_);
v___x_357_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__7));
v___x_358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_354_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = 0;
v___x_361_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*1, v___x_360_);
return v___x_361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0___boxed(lean_object* v_x_372_, lean_object* v_x_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_JsonNumber_instRepr___lam__0(v_x_372_, v_x_373_);
lean_dec(v_x_373_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0(lean_object* v_mantissa_377_, uint8_t v_exponentSign_378_, lean_object* v_decimalExponent_379_){
_start:
{
if (v_exponentSign_378_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_380_ = lean_unsigned_to_nat(10u);
v___x_381_ = lean_nat_pow(v___x_380_, v_decimalExponent_379_);
lean_dec(v_decimalExponent_379_);
v___x_382_ = lean_nat_mul(v_mantissa_377_, v___x_381_);
lean_dec(v___x_381_);
lean_dec(v_mantissa_377_);
v___x_383_ = lean_nat_to_int(v___x_382_);
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
return v___x_385_;
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_nat_to_int(v_mantissa_377_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v_decimalExponent_379_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0___boxed(lean_object* v_mantissa_388_, lean_object* v_exponentSign_389_, lean_object* v_decimalExponent_390_){
_start:
{
uint8_t v_exponentSign_boxed_391_; lean_object* v_res_392_; 
v_exponentSign_boxed_391_ = lean_unbox(v_exponentSign_389_);
v_res_392_ = l_Lean_JsonNumber_instOfScientific___lam__0(v_mantissa_388_, v_exponentSign_boxed_391_, v_decimalExponent_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instNeg___lam__0(lean_object* v_jn_395_){
_start:
{
lean_object* v_mantissa_396_; lean_object* v_exponent_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_405_; 
v_mantissa_396_ = lean_ctor_get(v_jn_395_, 0);
v_exponent_397_ = lean_ctor_get(v_jn_395_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v_jn_395_);
if (v_isSharedCheck_405_ == 0)
{
v___x_399_ = v_jn_395_;
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_exponent_397_);
lean_inc(v_mantissa_396_);
lean_dec(v_jn_395_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_int_neg(v_mantissa_396_);
lean_dec(v_mantissa_396_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_401_);
v___x_403_ = v___x_399_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_exponent_397_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
static lean_object* _init_l_Lean_JsonNumber_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = l_Lean_JsonNumber_fromNat(v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instInhabited(void){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lean_obj_once(&l_Lean_JsonNumber_instInhabited___closed__0, &l_Lean_JsonNumber_instInhabited___closed__0_once, _init_l_Lean_JsonNumber_instInhabited___closed__0);
return v___x_410_;
}
}
static double _init_l_Lean_JsonNumber_toFloat___closed__0(void){
_start:
{
lean_object* v___x_411_; uint8_t v___x_412_; lean_object* v___x_413_; double v___x_414_; 
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = 1;
v___x_413_ = lean_unsigned_to_nat(10u);
v___x_414_ = l_Float_ofScientific(v___x_413_, v___x_412_, v___x_411_);
return v___x_414_;
}
}
static double _init_l_Lean_JsonNumber_toFloat___closed__1(void){
_start:
{
double v___x_415_; double v___x_416_; 
v___x_415_ = lean_float_once(&l_Lean_JsonNumber_toFloat___closed__0, &l_Lean_JsonNumber_toFloat___closed__0_once, _init_l_Lean_JsonNumber_toFloat___closed__0);
v___x_416_ = lean_float_negate(v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT double l_Lean_JsonNumber_toFloat(lean_object* v_x_417_){
_start:
{
lean_object* v_mantissa_418_; lean_object* v_exponent_419_; double v___y_421_; lean_object* v___x_426_; uint8_t v___x_427_; 
v_mantissa_418_ = lean_ctor_get(v_x_417_, 0);
lean_inc(v_mantissa_418_);
v_exponent_419_ = lean_ctor_get(v_x_417_, 1);
lean_inc(v_exponent_419_);
lean_dec_ref(v_x_417_);
v___x_426_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_427_ = lean_int_dec_le(v___x_426_, v_mantissa_418_);
if (v___x_427_ == 0)
{
double v___x_428_; 
v___x_428_ = lean_float_once(&l_Lean_JsonNumber_toFloat___closed__1, &l_Lean_JsonNumber_toFloat___closed__1_once, _init_l_Lean_JsonNumber_toFloat___closed__1);
v___y_421_ = v___x_428_;
goto v___jp_420_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; double v___x_431_; 
v___x_429_ = lean_unsigned_to_nat(10u);
v___x_430_ = lean_unsigned_to_nat(1u);
v___x_431_ = l_Float_ofScientific(v___x_429_, v___x_427_, v___x_430_);
v___y_421_ = v___x_431_;
goto v___jp_420_;
}
v___jp_420_:
{
lean_object* v___x_422_; uint8_t v___x_423_; double v___x_424_; double v___x_425_; 
v___x_422_ = lean_nat_abs(v_mantissa_418_);
lean_dec(v_mantissa_418_);
v___x_423_ = 1;
v___x_424_ = l_Float_ofScientific(v___x_422_, v___x_423_, v_exponent_419_);
v___x_425_ = lean_float_mul(v___y_421_, v___x_424_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toFloat___boxed(lean_object* v_x_432_){
_start:
{
double v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l_Lean_JsonNumber_toFloat(v_x_432_);
v_r_434_ = lean_box_float(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(lean_object* v_msg_435_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = l_Lean_JsonNumber_instInhabited;
v___x_437_ = lean_panic_fn_borrowed(v___x_436_, v_msg_435_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(double v_x_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_float_to_string(v_x_441_);
v___x_443_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v___x_442_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_444_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_445_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1));
v___x_446_ = lean_unsigned_to_nat(164u);
v___x_447_ = lean_unsigned_to_nat(12u);
v___x_448_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2));
v___x_449_ = lean_string_append(v___x_448_, v___x_442_);
lean_dec_ref(v___x_442_);
v___x_450_ = l_mkPanicMessageWithDecl(v___x_444_, v___x_445_, v___x_446_, v___x_447_, v___x_449_);
lean_dec_ref(v___x_449_);
v___x_451_ = l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(v___x_450_);
return v___x_451_;
}
else
{
lean_object* v_val_452_; lean_object* v_snd_453_; lean_object* v_fst_454_; uint8_t v___x_455_; 
lean_dec_ref(v___x_442_);
v_val_452_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_val_452_);
lean_dec_ref_known(v___x_443_, 1);
v_snd_453_ = lean_ctor_get(v_val_452_, 1);
lean_inc(v_snd_453_);
v_fst_454_ = lean_ctor_get(v_snd_453_, 0);
v___x_455_ = lean_unbox(v_fst_454_);
if (v___x_455_ == 0)
{
lean_object* v_fst_456_; lean_object* v_snd_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_469_; 
v_fst_456_ = lean_ctor_get(v_val_452_, 0);
lean_inc(v_fst_456_);
lean_dec(v_val_452_);
v_snd_457_ = lean_ctor_get(v_snd_453_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_snd_453_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v_snd_453_, 0);
lean_dec(v_unused_470_);
v___x_459_ = v_snd_453_;
v_isShared_460_ = v_isSharedCheck_469_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_snd_457_);
lean_dec(v_snd_453_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_469_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_461_ = lean_unsigned_to_nat(10u);
v___x_462_ = lean_nat_pow(v___x_461_, v_snd_457_);
lean_dec(v_snd_457_);
v___x_463_ = lean_nat_mul(v_fst_456_, v___x_462_);
lean_dec(v___x_462_);
lean_dec(v_fst_456_);
v___x_464_ = lean_nat_to_int(v___x_463_);
v___x_465_ = lean_unsigned_to_nat(0u);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v___x_465_);
lean_ctor_set(v___x_459_, 0, v___x_464_);
v___x_467_ = v___x_459_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
else
{
lean_object* v_fst_471_; lean_object* v_snd_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_480_; 
v_fst_471_ = lean_ctor_get(v_val_452_, 0);
lean_inc(v_fst_471_);
lean_dec(v_val_452_);
v_snd_472_ = lean_ctor_get(v_snd_453_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_snd_453_);
if (v_isSharedCheck_480_ == 0)
{
lean_object* v_unused_481_; 
v_unused_481_ = lean_ctor_get(v_snd_453_, 0);
lean_dec(v_unused_481_);
v___x_474_ = v_snd_453_;
v_isShared_475_ = v_isSharedCheck_480_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_snd_472_);
lean_dec(v_snd_453_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_480_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = lean_nat_to_int(v_fst_471_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_476_);
v___x_478_ = v___x_474_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_snd_472_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___boxed(lean_object* v_x_482_){
_start:
{
double v_x_boxed_483_; lean_object* v_res_484_; 
v_x_boxed_483_ = lean_unbox_float(v_x_482_);
lean_dec_ref(v_x_482_);
v_res_484_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_boxed_483_);
return v_res_484_;
}
}
static double _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0(void){
_start:
{
lean_object* v___x_485_; uint8_t v___x_486_; lean_object* v___x_487_; double v___x_488_; 
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = 1;
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = l_Float_ofScientific(v___x_487_, v___x_486_, v___x_485_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_obj_once(&l_Lean_JsonNumber_instInhabited___closed__0, &l_Lean_JsonNumber_instInhabited___closed__0_once, _init_l_Lean_JsonNumber_instInhabited___closed__0);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
static double _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2(void){
_start:
{
lean_object* v___x_491_; double v___x_492_; 
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = lean_float_of_nat(v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f(double v_x_502_){
_start:
{
uint8_t v___x_503_; 
v___x_503_ = lean_float_isnan(v_x_502_);
if (v___x_503_ == 0)
{
uint8_t v___x_504_; 
v___x_504_ = lean_float_isinf(v_x_502_);
if (v___x_504_ == 0)
{
double v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_float_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__0, &l_Lean_JsonNumber_fromFloat_x3f___closed__0_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0);
v___x_506_ = lean_float_beq(v_x_502_, v___x_505_);
if (v___x_506_ == 0)
{
uint8_t v___x_507_; 
v___x_507_ = lean_float_decLt(v_x_502_, v___x_505_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_502_);
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
else
{
double v___x_510_; lean_object* v___x_511_; lean_object* v_mantissa_512_; lean_object* v_exponent_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_522_; 
v___x_510_ = lean_float_negate(v_x_502_);
v___x_511_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v___x_510_);
v_mantissa_512_ = lean_ctor_get(v___x_511_, 0);
v_exponent_513_ = lean_ctor_get(v___x_511_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_522_ == 0)
{
v___x_515_ = v___x_511_;
v_isShared_516_ = v_isSharedCheck_522_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_exponent_513_);
lean_inc(v_mantissa_512_);
lean_dec(v___x_511_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_522_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = lean_int_neg(v_mantissa_512_);
lean_dec(v_mantissa_512_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_517_);
v___x_519_ = v___x_515_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_exponent_513_);
v___x_519_ = v_reuseFailAlloc_521_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_520_; 
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
}
}
else
{
lean_object* v___x_523_; 
v___x_523_ = lean_obj_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__1, &l_Lean_JsonNumber_fromFloat_x3f___closed__1_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1);
return v___x_523_;
}
}
else
{
double v___x_524_; uint8_t v___x_525_; 
v___x_524_ = lean_float_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__2, &l_Lean_JsonNumber_fromFloat_x3f___closed__2_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2);
v___x_525_ = lean_float_decLt(v___x_524_, v_x_502_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; 
v___x_526_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__4));
return v___x_526_;
}
else
{
lean_object* v___x_527_; 
v___x_527_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__6));
return v___x_527_;
}
}
}
else
{
lean_object* v___x_528_; 
v___x_528_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__8));
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f___boxed(lean_object* v_x_529_){
_start:
{
double v_x_boxed_530_; lean_object* v_res_531_; 
v_x_boxed_530_ = lean_unbox_float(v_x_529_);
lean_dec_ref(v_x_529_);
v_res_531_ = l_Lean_JsonNumber_fromFloat_x3f(v_x_boxed_530_);
return v_res_531_;
}
}
LEAN_EXPORT uint8_t l_Lean_strLt(lean_object* v_a_532_, lean_object* v_b_533_){
_start:
{
uint8_t v___x_534_; 
v___x_534_ = lean_string_dec_lt(v_a_532_, v_b_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_strLt___boxed(lean_object* v_a_535_, lean_object* v_b_536_){
_start:
{
uint8_t v_res_537_; lean_object* v_r_538_; 
v_res_537_ = l_Lean_strLt(v_a_535_, v_b_536_);
lean_dec_ref(v_b_536_);
lean_dec_ref(v_a_535_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx___impl(lean_object* v_x_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = lean_obj_tag_nat(v_x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx___impl___boxed(lean_object* v_x_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Json_ctorIdx___impl(v_x_541_);
lean_dec(v_x_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___redArg(lean_object* v_t_543_, lean_object* v_k_544_){
_start:
{
switch(lean_obj_tag(v_t_543_))
{
case 0:
{
return v_k_544_;
}
case 1:
{
uint8_t v_b_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_b_545_ = lean_ctor_get_uint8(v_t_543_, 0);
lean_dec_ref_known(v_t_543_, 0);
v___x_546_ = lean_box(v_b_545_);
v___x_547_ = lean_apply_1(v_k_544_, v___x_546_);
return v___x_547_;
}
case 5:
{
lean_object* v_kvPairs_548_; lean_object* v___x_549_; 
v_kvPairs_548_ = lean_ctor_get(v_t_543_, 0);
lean_inc(v_kvPairs_548_);
lean_dec_ref_known(v_t_543_, 1);
v___x_549_ = lean_apply_1(v_k_544_, v_kvPairs_548_);
return v___x_549_;
}
default: 
{
lean_object* v_n_550_; lean_object* v___x_551_; 
v_n_550_ = lean_ctor_get(v_t_543_, 0);
lean_inc_ref(v_n_550_);
lean_dec(v_t_543_);
v___x_551_ = lean_apply_1(v_k_544_, v_n_550_);
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim(lean_object* v_motive__1_552_, lean_object* v_ctorIdx_553_, lean_object* v_t_554_, lean_object* v_h_555_, lean_object* v_k_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Json_ctorElim___redArg(v_t_554_, v_k_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___boxed(lean_object* v_motive__1_558_, lean_object* v_ctorIdx_559_, lean_object* v_t_560_, lean_object* v_h_561_, lean_object* v_k_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Json_ctorElim(v_motive__1_558_, v_ctorIdx_559_, v_t_560_, v_h_561_, v_k_562_);
lean_dec(v_ctorIdx_559_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_null_elim___redArg(lean_object* v_t_564_, lean_object* v_null_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_Json_ctorElim___redArg(v_t_564_, v_null_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_null_elim(lean_object* v_motive__1_567_, lean_object* v_t_568_, lean_object* v_h_569_, lean_object* v_null_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Json_ctorElim___redArg(v_t_568_, v_null_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim___redArg(lean_object* v_t_572_, lean_object* v_bool_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Json_ctorElim___redArg(v_t_572_, v_bool_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim(lean_object* v_motive__1_575_, lean_object* v_t_576_, lean_object* v_h_577_, lean_object* v_bool_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Json_ctorElim___redArg(v_t_576_, v_bool_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_num_elim___redArg(lean_object* v_t_580_, lean_object* v_num_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Json_ctorElim___redArg(v_t_580_, v_num_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_num_elim(lean_object* v_motive__1_583_, lean_object* v_t_584_, lean_object* v_h_585_, lean_object* v_num_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Json_ctorElim___redArg(v_t_584_, v_num_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_str_elim___redArg(lean_object* v_t_588_, lean_object* v_str_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Json_ctorElim___redArg(v_t_588_, v_str_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_str_elim(lean_object* v_motive__1_591_, lean_object* v_t_592_, lean_object* v_h_593_, lean_object* v_str_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Json_ctorElim___redArg(v_t_592_, v_str_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim___redArg(lean_object* v_t_596_, lean_object* v_arr_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Json_ctorElim___redArg(v_t_596_, v_arr_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim(lean_object* v_motive__1_599_, lean_object* v_t_600_, lean_object* v_h_601_, lean_object* v_arr_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Json_ctorElim___redArg(v_t_600_, v_arr_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim___redArg(lean_object* v_t_604_, lean_object* v_obj_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Json_ctorElim___redArg(v_t_604_, v_obj_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim(lean_object* v_motive__1_607_, lean_object* v_t_608_, lean_object* v_h_609_, lean_object* v_obj_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_Json_ctorElim___redArg(v_t_608_, v_obj_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_instInhabitedJson_default(void){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lean_box(0);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_instInhabitedJson(void){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = lean_box(0);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(lean_object* v_init_614_, lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_615_) == 0)
{
lean_object* v_l_616_; lean_object* v_r_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_l_616_ = lean_ctor_get(v_x_615_, 3);
v_r_617_ = lean_ctor_get(v_x_615_, 4);
v___x_618_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_614_, v_l_616_);
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = lean_nat_add(v___x_618_, v___x_619_);
lean_dec(v___x_618_);
v_init_614_ = v___x_620_;
v_x_615_ = v_r_617_;
goto _start;
}
else
{
return v_init_614_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1___boxed(lean_object* v_init_622_, lean_object* v_x_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_622_, v_x_623_);
lean_dec(v_x_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(lean_object* v_t_625_, lean_object* v_k_626_){
_start:
{
if (lean_obj_tag(v_t_625_) == 0)
{
lean_object* v_k_627_; lean_object* v_v_628_; lean_object* v_l_629_; lean_object* v_r_630_; uint8_t v___x_631_; 
v_k_627_ = lean_ctor_get(v_t_625_, 1);
v_v_628_ = lean_ctor_get(v_t_625_, 2);
v_l_629_ = lean_ctor_get(v_t_625_, 3);
v_r_630_ = lean_ctor_get(v_t_625_, 4);
v___x_631_ = lean_string_compare(v_k_626_, v_k_627_);
switch(v___x_631_)
{
case 0:
{
v_t_625_ = v_l_629_;
goto _start;
}
case 1:
{
lean_object* v___x_633_; 
lean_inc(v_v_628_);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v_v_628_);
return v___x_633_;
}
default: 
{
v_t_625_ = v_r_630_;
goto _start;
}
}
}
else
{
lean_object* v___x_635_; 
v___x_635_ = lean_box(0);
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg___boxed(lean_object* v_t_636_, lean_object* v_k_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_636_, v_k_637_);
lean_dec_ref(v_k_637_);
lean_dec(v_t_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(lean_object* v_szA_650_, lean_object* v_szB_651_, lean_object* v_kvPairs_652_, lean_object* v_init_653_, lean_object* v_x_654_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
lean_object* v_k_655_; lean_object* v_v_656_; lean_object* v_l_657_; lean_object* v_r_658_; uint8_t v___x_659_; lean_object* v___x_660_; 
v_k_655_ = lean_ctor_get(v_x_654_, 1);
v_v_656_ = lean_ctor_get(v_x_654_, 2);
v_l_657_ = lean_ctor_get(v_x_654_, 3);
v_r_658_ = lean_ctor_get(v_x_654_, 4);
v___x_659_ = lean_nat_dec_eq(v_szA_650_, v_szB_651_);
v___x_660_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_650_, v_szB_651_, v_kvPairs_652_, v_init_653_, v_l_657_);
if (lean_obj_tag(v___x_660_) == 0)
{
return v___x_660_;
}
else
{
lean_object* v___x_661_; lean_object* v___x_665_; 
lean_dec_ref_known(v___x_660_, 1);
v___x_661_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0));
v___x_665_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_652_, v_k_655_);
if (lean_obj_tag(v___x_665_) == 0)
{
goto v___jp_662_;
}
else
{
lean_object* v_val_666_; uint8_t v___x_667_; 
v_val_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_val_666_);
lean_dec_ref_known(v___x_665_, 1);
v___x_667_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_v_656_, v_val_666_);
lean_dec(v_val_666_);
if (v___x_667_ == 0)
{
goto v___jp_662_;
}
else
{
v_init_653_ = v___x_661_;
v_x_654_ = v_r_658_;
goto _start;
}
}
v___jp_662_:
{
if (v___x_659_ == 0)
{
v_init_653_ = v___x_661_;
v_x_654_ = v_r_658_;
goto _start;
}
else
{
lean_object* v___x_664_; 
v___x_664_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__3));
return v___x_664_;
}
}
}
}
else
{
lean_object* v___x_669_; 
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v_init_653_);
return v___x_669_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
switch(lean_obj_tag(v_x_670_))
{
case 0:
{
if (lean_obj_tag(v_x_671_) == 0)
{
uint8_t v___x_672_; 
v___x_672_ = 1;
return v___x_672_;
}
else
{
uint8_t v___x_673_; 
v___x_673_ = 0;
return v___x_673_;
}
}
case 1:
{
if (lean_obj_tag(v_x_671_) == 1)
{
uint8_t v_b_674_; 
v_b_674_ = lean_ctor_get_uint8(v_x_671_, 0);
if (v_b_674_ == 0)
{
uint8_t v_b_675_; 
v_b_675_ = lean_ctor_get_uint8(v_x_670_, 0);
if (v_b_675_ == 0)
{
uint8_t v___x_676_; 
v___x_676_ = 1;
return v___x_676_;
}
else
{
return v_b_674_;
}
}
else
{
uint8_t v_b_677_; 
v_b_677_ = lean_ctor_get_uint8(v_x_670_, 0);
return v_b_677_;
}
}
else
{
uint8_t v___x_678_; 
v___x_678_ = 0;
return v___x_678_;
}
}
case 2:
{
if (lean_obj_tag(v_x_671_) == 2)
{
lean_object* v_n_679_; lean_object* v_n_680_; uint8_t v___x_681_; 
v_n_679_ = lean_ctor_get(v_x_670_, 0);
v_n_680_ = lean_ctor_get(v_x_671_, 0);
v___x_681_ = l_Lean_instDecidableEqJsonNumber_decEq(v_n_679_, v_n_680_);
return v___x_681_;
}
else
{
uint8_t v___x_682_; 
v___x_682_ = 0;
return v___x_682_;
}
}
case 3:
{
if (lean_obj_tag(v_x_671_) == 3)
{
lean_object* v_s_683_; lean_object* v_s_684_; uint8_t v___x_685_; 
v_s_683_ = lean_ctor_get(v_x_670_, 0);
v_s_684_ = lean_ctor_get(v_x_671_, 0);
v___x_685_ = lean_string_dec_eq(v_s_683_, v_s_684_);
return v___x_685_;
}
else
{
uint8_t v___x_686_; 
v___x_686_ = 0;
return v___x_686_;
}
}
case 4:
{
if (lean_obj_tag(v_x_671_) == 4)
{
lean_object* v_elems_687_; lean_object* v_elems_688_; lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v_elems_687_ = lean_ctor_get(v_x_670_, 0);
v_elems_688_ = lean_ctor_get(v_x_671_, 0);
v___x_689_ = lean_array_get_size(v_elems_687_);
v___x_690_ = lean_array_get_size(v_elems_688_);
v___x_691_ = lean_nat_dec_eq(v___x_689_, v___x_690_);
if (v___x_691_ == 0)
{
return v___x_691_;
}
else
{
uint8_t v___x_692_; 
v___x_692_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_elems_687_, v_elems_688_, v___x_689_);
return v___x_692_;
}
}
else
{
uint8_t v___x_693_; 
v___x_693_ = 0;
return v___x_693_;
}
}
default: 
{
if (lean_obj_tag(v_x_671_) == 5)
{
lean_object* v_kvPairs_694_; lean_object* v_kvPairs_695_; lean_object* v___x_696_; lean_object* v_szA_697_; lean_object* v_szB_698_; uint8_t v___x_699_; lean_object* v___y_701_; 
v_kvPairs_694_ = lean_ctor_get(v_x_670_, 0);
v_kvPairs_695_ = lean_ctor_get(v_x_671_, 0);
v___x_696_ = lean_unsigned_to_nat(0u);
v_szA_697_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_696_, v_kvPairs_694_);
v_szB_698_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_696_, v_kvPairs_695_);
v___x_699_ = lean_nat_dec_eq(v_szA_697_, v_szB_698_);
if (v___x_699_ == 0)
{
lean_dec(v_szB_698_);
lean_dec(v_szA_697_);
return v___x_699_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_a_707_; 
v___x_705_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0));
v___x_706_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_697_, v_szB_698_, v_kvPairs_695_, v___x_705_, v_kvPairs_694_);
lean_dec(v_szB_698_);
lean_dec(v_szA_697_);
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref(v___x_706_);
v___y_701_ = v_a_707_;
goto v___jp_700_;
}
v___jp_700_:
{
lean_object* v_fst_702_; 
v_fst_702_ = lean_ctor_get(v___y_701_, 0);
lean_inc(v_fst_702_);
lean_dec_ref(v___y_701_);
if (lean_obj_tag(v_fst_702_) == 0)
{
return v___x_699_;
}
else
{
lean_object* v_val_703_; uint8_t v___x_704_; 
v_val_703_ = lean_ctor_get(v_fst_702_, 0);
lean_inc(v_val_703_);
lean_dec_ref_known(v_fst_702_, 1);
v___x_704_ = lean_unbox(v_val_703_);
lean_dec(v_val_703_);
return v___x_704_;
}
}
}
else
{
uint8_t v___x_708_; 
v___x_708_ = 0;
return v___x_708_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(lean_object* v_xs_709_, lean_object* v_ys_710_, lean_object* v_x_711_){
_start:
{
lean_object* v_zero_712_; uint8_t v_isZero_713_; 
v_zero_712_ = lean_unsigned_to_nat(0u);
v_isZero_713_ = lean_nat_dec_eq(v_x_711_, v_zero_712_);
if (v_isZero_713_ == 1)
{
lean_dec(v_x_711_);
return v_isZero_713_;
}
else
{
lean_object* v_one_714_; lean_object* v_n_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v_one_714_ = lean_unsigned_to_nat(1u);
v_n_715_ = lean_nat_sub(v_x_711_, v_one_714_);
lean_dec(v_x_711_);
v___x_716_ = lean_array_fget_borrowed(v_xs_709_, v_n_715_);
v___x_717_ = lean_array_fget_borrowed(v_ys_710_, v_n_715_);
v___x_718_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v___x_716_, v___x_717_);
if (v___x_718_ == 0)
{
lean_dec(v_n_715_);
return v___x_718_;
}
else
{
v_x_711_ = v_n_715_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg___boxed(lean_object* v_xs_720_, lean_object* v_ys_721_, lean_object* v_x_722_){
_start:
{
uint8_t v_res_723_; lean_object* v_r_724_; 
v_res_723_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_720_, v_ys_721_, v_x_722_);
lean_dec_ref(v_ys_721_);
lean_dec_ref(v_xs_720_);
v_r_724_ = lean_box(v_res_723_);
return v_r_724_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___boxed(lean_object* v_szA_725_, lean_object* v_szB_726_, lean_object* v_kvPairs_727_, lean_object* v_init_728_, lean_object* v_x_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_725_, v_szB_726_, v_kvPairs_727_, v_init_728_, v_x_729_);
lean_dec(v_x_729_);
lean_dec(v_kvPairs_727_);
lean_dec(v_szB_726_);
lean_dec(v_szA_725_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___boxed(lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
uint8_t v_res_733_; lean_object* v_r_734_; 
v_res_733_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_x_731_, v_x_732_);
lean_dec(v_x_732_);
lean_dec(v_x_731_);
v_r_734_ = lean_box(v_res_733_);
return v_r_734_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(lean_object* v_xs_735_, lean_object* v_ys_736_, lean_object* v_hsz_737_, lean_object* v_x_738_, lean_object* v_x_739_){
_start:
{
uint8_t v___x_740_; 
v___x_740_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_735_, v_ys_736_, v_x_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___boxed(lean_object* v_xs_741_, lean_object* v_ys_742_, lean_object* v_hsz_743_, lean_object* v_x_744_, lean_object* v_x_745_){
_start:
{
uint8_t v_res_746_; lean_object* v_r_747_; 
v_res_746_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(v_xs_741_, v_ys_742_, v_hsz_743_, v_x_744_, v_x_745_);
lean_dec_ref(v_ys_742_);
lean_dec_ref(v_xs_741_);
v_r_747_ = lean_box(v_res_746_);
return v_r_747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(lean_object* v_init_748_, lean_object* v_t_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_748_, v_t_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___boxed(lean_object* v_init_751_, lean_object* v_t_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(v_init_751_, v_t_752_);
lean_dec(v_t_752_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(lean_object* v_00_u03b4_754_, lean_object* v_t_755_, lean_object* v_k_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_755_, v_k_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___boxed(lean_object* v_00_u03b4_758_, lean_object* v_t_759_, lean_object* v_k_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(v_00_u03b4_758_, v_t_759_, v_k_760_);
lean_dec_ref(v_k_760_);
lean_dec(v_t_759_);
return v_res_761_;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_instBEq___private__1(lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_a_762_, v_a_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instBEq___private__1___boxed(lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
uint8_t v_res_767_; lean_object* v_r_768_; 
v_res_767_ = l_Lean_Json_instBEq___private__1(v_a_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec(v_a_765_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(lean_object* v_as_771_, size_t v_i_772_, size_t v_stop_773_, uint64_t v_b_774_){
_start:
{
uint8_t v___x_775_; 
v___x_775_ = lean_usize_dec_eq(v_i_772_, v_stop_773_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; uint64_t v___x_777_; uint64_t v___x_778_; size_t v___x_779_; size_t v___x_780_; 
v___x_776_ = lean_array_uget_borrowed(v_as_771_, v_i_772_);
v___x_777_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v___x_776_);
v___x_778_ = lean_uint64_mix_hash(v_b_774_, v___x_777_);
v___x_779_ = ((size_t)1ULL);
v___x_780_ = lean_usize_add(v_i_772_, v___x_779_);
v_i_772_ = v___x_780_;
v_b_774_ = v___x_778_;
goto _start;
}
else
{
return v_b_774_;
}
}
}
LEAN_EXPORT uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(lean_object* v_x_782_){
_start:
{
switch(lean_obj_tag(v_x_782_))
{
case 0:
{
uint64_t v___x_783_; 
v___x_783_ = 11ULL;
return v___x_783_;
}
case 1:
{
uint8_t v_b_784_; 
v_b_784_ = lean_ctor_get_uint8(v_x_782_, 0);
if (v_b_784_ == 0)
{
uint64_t v___x_785_; 
v___x_785_ = 889925284873970544ULL;
return v___x_785_;
}
else
{
uint64_t v___x_786_; 
v___x_786_ = 7849220421742680397ULL;
return v___x_786_;
}
}
case 2:
{
lean_object* v_n_787_; uint64_t v___x_788_; uint64_t v___x_789_; uint64_t v___x_790_; 
v_n_787_ = lean_ctor_get(v_x_782_, 0);
v___x_788_ = 17ULL;
v___x_789_ = l_Lean_instHashableJsonNumber_hash(v_n_787_);
v___x_790_ = lean_uint64_mix_hash(v___x_788_, v___x_789_);
return v___x_790_;
}
case 3:
{
lean_object* v_s_791_; uint64_t v___x_792_; uint64_t v___x_793_; uint64_t v___x_794_; 
v_s_791_ = lean_ctor_get(v_x_782_, 0);
v___x_792_ = 19ULL;
v___x_793_ = lean_string_hash(v_s_791_);
v___x_794_ = lean_uint64_mix_hash(v___x_792_, v___x_793_);
return v___x_794_;
}
case 4:
{
lean_object* v_elems_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v_elems_795_ = lean_ctor_get(v_x_782_, 0);
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = lean_array_get_size(v_elems_795_);
v___x_798_ = lean_nat_dec_lt(v___x_796_, v___x_797_);
if (v___x_798_ == 0)
{
uint64_t v___x_799_; 
v___x_799_ = 179905158410471120ULL;
return v___x_799_;
}
else
{
uint64_t v___x_800_; uint64_t v___x_801_; size_t v___x_802_; size_t v___x_803_; uint64_t v___x_804_; uint64_t v___x_805_; 
v___x_800_ = 23ULL;
v___x_801_ = 7ULL;
v___x_802_ = ((size_t)0ULL);
v___x_803_ = lean_usize_of_nat(v___x_797_);
v___x_804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_795_, v___x_802_, v___x_803_, v___x_801_);
v___x_805_ = lean_uint64_mix_hash(v___x_800_, v___x_804_);
return v___x_805_;
}
}
default: 
{
lean_object* v_kvPairs_806_; uint64_t v___x_807_; uint64_t v___x_808_; uint64_t v___x_809_; uint64_t v___x_810_; 
v_kvPairs_806_ = lean_ctor_get(v_x_782_, 0);
v___x_807_ = 29ULL;
v___x_808_ = 7ULL;
v___x_809_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v___x_808_, v_kvPairs_806_);
v___x_810_ = lean_uint64_mix_hash(v___x_807_, v___x_809_);
return v___x_810_;
}
}
}
}
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(uint64_t v_init_811_, lean_object* v_x_812_){
_start:
{
if (lean_obj_tag(v_x_812_) == 0)
{
lean_object* v_k_813_; lean_object* v_v_814_; lean_object* v_l_815_; lean_object* v_r_816_; uint64_t v___x_817_; uint64_t v___x_818_; uint64_t v___x_819_; uint64_t v___x_820_; uint64_t v___x_821_; 
v_k_813_ = lean_ctor_get(v_x_812_, 1);
v_v_814_ = lean_ctor_get(v_x_812_, 2);
v_l_815_ = lean_ctor_get(v_x_812_, 3);
v_r_816_ = lean_ctor_get(v_x_812_, 4);
v___x_817_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_811_, v_l_815_);
v___x_818_ = lean_string_hash(v_k_813_);
v___x_819_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_v_814_);
v___x_820_ = lean_uint64_mix_hash(v___x_818_, v___x_819_);
v___x_821_ = lean_uint64_mix_hash(v___x_817_, v___x_820_);
v_init_811_ = v___x_821_;
v_x_812_ = v_r_816_;
goto _start;
}
else
{
return v_init_811_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1___boxed(lean_object* v_init_823_, lean_object* v_x_824_){
_start:
{
uint64_t v_init_boxed_825_; uint64_t v_res_826_; lean_object* v_r_827_; 
v_init_boxed_825_ = lean_unbox_uint64(v_init_823_);
lean_dec_ref(v_init_823_);
v_res_826_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_boxed_825_, v_x_824_);
lean_dec(v_x_824_);
v_r_827_ = lean_box_uint64(v_res_826_);
return v_r_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0___boxed(lean_object* v_as_828_, lean_object* v_i_829_, lean_object* v_stop_830_, lean_object* v_b_831_){
_start:
{
size_t v_i_boxed_832_; size_t v_stop_boxed_833_; uint64_t v_b_boxed_834_; uint64_t v_res_835_; lean_object* v_r_836_; 
v_i_boxed_832_ = lean_unbox_usize(v_i_829_);
lean_dec(v_i_829_);
v_stop_boxed_833_ = lean_unbox_usize(v_stop_830_);
lean_dec(v_stop_830_);
v_b_boxed_834_ = lean_unbox_uint64(v_b_831_);
lean_dec_ref(v_b_831_);
v_res_835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_as_828_, v_i_boxed_832_, v_stop_boxed_833_, v_b_boxed_834_);
lean_dec_ref(v_as_828_);
v_r_836_ = lean_box_uint64(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___boxed(lean_object* v_x_837_){
_start:
{
uint64_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_x_837_);
lean_dec(v_x_837_);
v_r_839_ = lean_box_uint64(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(uint64_t v_init_840_, lean_object* v_t_841_){
_start:
{
uint64_t v___x_842_; 
v___x_842_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_840_, v_t_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1___boxed(lean_object* v_init_843_, lean_object* v_t_844_){
_start:
{
uint64_t v_init_boxed_845_; uint64_t v_res_846_; lean_object* v_r_847_; 
v_init_boxed_845_ = lean_unbox_uint64(v_init_843_);
lean_dec_ref(v_init_843_);
v_res_846_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(v_init_boxed_845_, v_t_844_);
lean_dec(v_t_844_);
v_r_847_ = lean_box_uint64(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT uint64_t l_Lean_Json_instHashable___private__1(lean_object* v_a_848_){
_start:
{
uint64_t v___x_849_; 
v___x_849_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_a_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instHashable___private__1___boxed(lean_object* v_a_850_){
_start:
{
uint64_t v_res_851_; lean_object* v_r_852_; 
v_res_851_ = l_Lean_Json_instHashable___private__1(v_a_850_);
lean_dec(v_a_850_);
v_r_852_ = lean_box_uint64(v_res_851_);
return v_r_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(lean_object* v_k_855_, lean_object* v_v_856_, lean_object* v_t_857_){
_start:
{
if (lean_obj_tag(v_t_857_) == 0)
{
lean_object* v_size_858_; lean_object* v_k_859_; lean_object* v_v_860_; lean_object* v_l_861_; lean_object* v_r_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_1142_; 
v_size_858_ = lean_ctor_get(v_t_857_, 0);
v_k_859_ = lean_ctor_get(v_t_857_, 1);
v_v_860_ = lean_ctor_get(v_t_857_, 2);
v_l_861_ = lean_ctor_get(v_t_857_, 3);
v_r_862_ = lean_ctor_get(v_t_857_, 4);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_t_857_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_864_ = v_t_857_;
v_isShared_865_ = v_isSharedCheck_1142_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_r_862_);
lean_inc(v_l_861_);
lean_inc(v_v_860_);
lean_inc(v_k_859_);
lean_inc(v_size_858_);
lean_dec(v_t_857_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_1142_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
uint8_t v___x_866_; 
v___x_866_ = lean_string_compare(v_k_855_, v_k_859_);
switch(v___x_866_)
{
case 0:
{
lean_object* v_impl_867_; lean_object* v___x_868_; 
lean_dec(v_size_858_);
v_impl_867_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_855_, v_v_856_, v_l_861_);
v___x_868_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_862_) == 0)
{
lean_object* v_size_869_; lean_object* v_size_870_; lean_object* v_k_871_; lean_object* v_v_872_; lean_object* v_l_873_; lean_object* v_r_874_; lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v_size_869_ = lean_ctor_get(v_r_862_, 0);
v_size_870_ = lean_ctor_get(v_impl_867_, 0);
v_k_871_ = lean_ctor_get(v_impl_867_, 1);
v_v_872_ = lean_ctor_get(v_impl_867_, 2);
v_l_873_ = lean_ctor_get(v_impl_867_, 3);
v_r_874_ = lean_ctor_get(v_impl_867_, 4);
lean_inc(v_r_874_);
v___x_875_ = lean_unsigned_to_nat(3u);
v___x_876_ = lean_nat_mul(v___x_875_, v_size_869_);
v___x_877_ = lean_nat_dec_lt(v___x_876_, v_size_870_);
lean_dec(v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
lean_dec(v_r_874_);
v___x_878_ = lean_nat_add(v___x_868_, v_size_870_);
v___x_879_ = lean_nat_add(v___x_878_, v_size_869_);
lean_dec(v___x_878_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 3, v_impl_867_);
lean_ctor_set(v___x_864_, 0, v___x_879_);
v___x_881_ = v___x_864_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_k_859_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v_v_860_);
lean_ctor_set(v_reuseFailAlloc_882_, 3, v_impl_867_);
lean_ctor_set(v_reuseFailAlloc_882_, 4, v_r_862_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
else
{
lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_948_; 
lean_inc(v_l_873_);
lean_inc(v_v_872_);
lean_inc(v_k_871_);
lean_inc(v_size_870_);
v_isSharedCheck_948_ = !lean_is_exclusive(v_impl_867_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; lean_object* v_unused_950_; lean_object* v_unused_951_; lean_object* v_unused_952_; lean_object* v_unused_953_; 
v_unused_949_ = lean_ctor_get(v_impl_867_, 4);
lean_dec(v_unused_949_);
v_unused_950_ = lean_ctor_get(v_impl_867_, 3);
lean_dec(v_unused_950_);
v_unused_951_ = lean_ctor_get(v_impl_867_, 2);
lean_dec(v_unused_951_);
v_unused_952_ = lean_ctor_get(v_impl_867_, 1);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_impl_867_, 0);
lean_dec(v_unused_953_);
v___x_884_ = v_impl_867_;
v_isShared_885_ = v_isSharedCheck_948_;
goto v_resetjp_883_;
}
else
{
lean_dec(v_impl_867_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_948_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_size_886_; lean_object* v_size_887_; lean_object* v_k_888_; lean_object* v_v_889_; lean_object* v_l_890_; lean_object* v_r_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v_size_886_ = lean_ctor_get(v_l_873_, 0);
v_size_887_ = lean_ctor_get(v_r_874_, 0);
v_k_888_ = lean_ctor_get(v_r_874_, 1);
v_v_889_ = lean_ctor_get(v_r_874_, 2);
v_l_890_ = lean_ctor_get(v_r_874_, 3);
v_r_891_ = lean_ctor_get(v_r_874_, 4);
v___x_892_ = lean_unsigned_to_nat(2u);
v___x_893_ = lean_nat_mul(v___x_892_, v_size_886_);
v___x_894_ = lean_nat_dec_lt(v_size_887_, v___x_893_);
lean_dec(v___x_893_);
if (v___x_894_ == 0)
{
lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_923_; 
lean_inc(v_r_891_);
lean_inc(v_l_890_);
lean_inc(v_v_889_);
lean_inc(v_k_888_);
v_isSharedCheck_923_ = !lean_is_exclusive(v_r_874_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; lean_object* v_unused_925_; lean_object* v_unused_926_; lean_object* v_unused_927_; lean_object* v_unused_928_; 
v_unused_924_ = lean_ctor_get(v_r_874_, 4);
lean_dec(v_unused_924_);
v_unused_925_ = lean_ctor_get(v_r_874_, 3);
lean_dec(v_unused_925_);
v_unused_926_ = lean_ctor_get(v_r_874_, 2);
lean_dec(v_unused_926_);
v_unused_927_ = lean_ctor_get(v_r_874_, 1);
lean_dec(v_unused_927_);
v_unused_928_ = lean_ctor_get(v_r_874_, 0);
lean_dec(v_unused_928_);
v___x_896_ = v_r_874_;
v_isShared_897_ = v_isSharedCheck_923_;
goto v_resetjp_895_;
}
else
{
lean_dec(v_r_874_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_923_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___x_911_; lean_object* v___y_913_; 
v___x_898_ = lean_nat_add(v___x_868_, v_size_870_);
lean_dec(v_size_870_);
v___x_899_ = lean_nat_add(v___x_898_, v_size_869_);
lean_dec(v___x_898_);
v___x_911_ = lean_nat_add(v___x_868_, v_size_886_);
if (lean_obj_tag(v_l_890_) == 0)
{
lean_object* v_size_921_; 
v_size_921_ = lean_ctor_get(v_l_890_, 0);
lean_inc(v_size_921_);
v___y_913_ = v_size_921_;
goto v___jp_912_;
}
else
{
lean_object* v___x_922_; 
v___x_922_ = lean_unsigned_to_nat(0u);
v___y_913_ = v___x_922_;
goto v___jp_912_;
}
v___jp_900_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_nat_add(v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec(v___y_902_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 4, v_r_862_);
lean_ctor_set(v___x_896_, 3, v_r_891_);
lean_ctor_set(v___x_896_, 2, v_v_860_);
lean_ctor_set(v___x_896_, 1, v_k_859_);
lean_ctor_set(v___x_896_, 0, v___x_904_);
v___x_906_ = v___x_896_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_k_859_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_v_860_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_r_891_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_r_862_);
v___x_906_ = v_reuseFailAlloc_910_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_908_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 4, v___x_906_);
lean_ctor_set(v___x_884_, 3, v___y_901_);
lean_ctor_set(v___x_884_, 2, v_v_889_);
lean_ctor_set(v___x_884_, 1, v_k_888_);
lean_ctor_set(v___x_884_, 0, v___x_899_);
v___x_908_ = v___x_884_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_k_888_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v_v_889_);
lean_ctor_set(v_reuseFailAlloc_909_, 3, v___y_901_);
lean_ctor_set(v_reuseFailAlloc_909_, 4, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
v___jp_912_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = lean_nat_add(v___x_911_, v___y_913_);
lean_dec(v___y_913_);
lean_dec(v___x_911_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 4, v_l_890_);
lean_ctor_set(v___x_864_, 3, v_l_873_);
lean_ctor_set(v___x_864_, 2, v_v_872_);
lean_ctor_set(v___x_864_, 1, v_k_871_);
lean_ctor_set(v___x_864_, 0, v___x_914_);
v___x_916_ = v___x_864_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_k_871_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_v_872_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v_l_873_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v_l_890_);
v___x_916_ = v_reuseFailAlloc_920_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_917_; 
v___x_917_ = lean_nat_add(v___x_868_, v_size_869_);
if (lean_obj_tag(v_r_891_) == 0)
{
lean_object* v_size_918_; 
v_size_918_ = lean_ctor_get(v_r_891_, 0);
lean_inc(v_size_918_);
v___y_901_ = v___x_916_;
v___y_902_ = v___x_917_;
v___y_903_ = v_size_918_;
goto v___jp_900_;
}
else
{
lean_object* v___x_919_; 
v___x_919_ = lean_unsigned_to_nat(0u);
v___y_901_ = v___x_916_;
v___y_902_ = v___x_917_;
v___y_903_ = v___x_919_;
goto v___jp_900_;
}
}
}
}
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
lean_del_object(v___x_864_);
v___x_929_ = lean_nat_add(v___x_868_, v_size_870_);
lean_dec(v_size_870_);
v___x_930_ = lean_nat_add(v___x_929_, v_size_869_);
lean_dec(v___x_929_);
v___x_931_ = lean_nat_add(v___x_868_, v_size_869_);
v___x_932_ = lean_nat_add(v___x_931_, v_size_887_);
lean_dec(v___x_931_);
lean_inc_ref(v_r_862_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 4, v_r_862_);
lean_ctor_set(v___x_884_, 3, v_r_874_);
lean_ctor_set(v___x_884_, 2, v_v_860_);
lean_ctor_set(v___x_884_, 1, v_k_859_);
lean_ctor_set(v___x_884_, 0, v___x_932_);
v___x_934_ = v___x_884_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_k_859_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_v_860_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_r_874_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v_r_862_);
v___x_934_ = v_reuseFailAlloc_947_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
v_isSharedCheck_941_ = !lean_is_exclusive(v_r_862_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; lean_object* v_unused_943_; lean_object* v_unused_944_; lean_object* v_unused_945_; lean_object* v_unused_946_; 
v_unused_942_ = lean_ctor_get(v_r_862_, 4);
lean_dec(v_unused_942_);
v_unused_943_ = lean_ctor_get(v_r_862_, 3);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v_r_862_, 2);
lean_dec(v_unused_944_);
v_unused_945_ = lean_ctor_get(v_r_862_, 1);
lean_dec(v_unused_945_);
v_unused_946_ = lean_ctor_get(v_r_862_, 0);
lean_dec(v_unused_946_);
v___x_936_ = v_r_862_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_dec(v_r_862_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 4, v___x_934_);
lean_ctor_set(v___x_936_, 3, v_l_873_);
lean_ctor_set(v___x_936_, 2, v_v_872_);
lean_ctor_set(v___x_936_, 1, v_k_871_);
lean_ctor_set(v___x_936_, 0, v___x_930_);
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_k_871_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_v_872_);
lean_ctor_set(v_reuseFailAlloc_940_, 3, v_l_873_);
lean_ctor_set(v_reuseFailAlloc_940_, 4, v___x_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_954_; 
v_l_954_ = lean_ctor_get(v_impl_867_, 3);
if (lean_obj_tag(v_l_954_) == 0)
{
lean_object* v_r_955_; lean_object* v_k_956_; lean_object* v_v_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_968_; 
lean_inc_ref(v_l_954_);
v_r_955_ = lean_ctor_get(v_impl_867_, 4);
v_k_956_ = lean_ctor_get(v_impl_867_, 1);
v_v_957_ = lean_ctor_get(v_impl_867_, 2);
v_isSharedCheck_968_ = !lean_is_exclusive(v_impl_867_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; lean_object* v_unused_970_; 
v_unused_969_ = lean_ctor_get(v_impl_867_, 3);
lean_dec(v_unused_969_);
v_unused_970_ = lean_ctor_get(v_impl_867_, 0);
lean_dec(v_unused_970_);
v___x_959_ = v_impl_867_;
v_isShared_960_ = v_isSharedCheck_968_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_r_955_);
lean_inc(v_v_957_);
lean_inc(v_k_956_);
lean_dec(v_impl_867_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_968_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_955_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 3, v_r_955_);
lean_ctor_set(v___x_959_, 2, v_v_860_);
lean_ctor_set(v___x_959_, 1, v_k_859_);
lean_ctor_set(v___x_959_, 0, v___x_868_);
v___x_963_ = v___x_959_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_k_859_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_v_860_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v_r_955_);
lean_ctor_set(v_reuseFailAlloc_967_, 4, v_r_955_);
v___x_963_ = v_reuseFailAlloc_967_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_965_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 4, v___x_963_);
lean_ctor_set(v___x_864_, 3, v_l_954_);
lean_ctor_set(v___x_864_, 2, v_v_957_);
lean_ctor_set(v___x_864_, 1, v_k_956_);
lean_ctor_set(v___x_864_, 0, v___x_961_);
v___x_965_ = v___x_864_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_k_956_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_v_957_);
lean_ctor_set(v_reuseFailAlloc_966_, 3, v_l_954_);
lean_ctor_set(v_reuseFailAlloc_966_, 4, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_object* v_r_971_; 
v_r_971_ = lean_ctor_get(v_impl_867_, 4);
lean_inc(v_r_971_);
if (lean_obj_tag(v_r_971_) == 0)
{
lean_object* v_k_972_; lean_object* v_v_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_996_; 
lean_inc(v_l_954_);
v_k_972_ = lean_ctor_get(v_impl_867_, 1);
v_v_973_ = lean_ctor_get(v_impl_867_, 2);
v_isSharedCheck_996_ = !lean_is_exclusive(v_impl_867_);
if (v_isSharedCheck_996_ == 0)
{
lean_object* v_unused_997_; lean_object* v_unused_998_; lean_object* v_unused_999_; 
v_unused_997_ = lean_ctor_get(v_impl_867_, 4);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_impl_867_, 3);
lean_dec(v_unused_998_);
v_unused_999_ = lean_ctor_get(v_impl_867_, 0);
lean_dec(v_unused_999_);
v___x_975_ = v_impl_867_;
v_isShared_976_ = v_isSharedCheck_996_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_v_973_);
lean_inc(v_k_972_);
lean_dec(v_impl_867_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_996_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_k_977_; lean_object* v_v_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_992_; 
v_k_977_ = lean_ctor_get(v_r_971_, 1);
v_v_978_ = lean_ctor_get(v_r_971_, 2);
v_isSharedCheck_992_ = !lean_is_exclusive(v_r_971_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; lean_object* v_unused_994_; lean_object* v_unused_995_; 
v_unused_993_ = lean_ctor_get(v_r_971_, 4);
lean_dec(v_unused_993_);
v_unused_994_ = lean_ctor_get(v_r_971_, 3);
lean_dec(v_unused_994_);
v_unused_995_ = lean_ctor_get(v_r_971_, 0);
lean_dec(v_unused_995_);
v___x_980_ = v_r_971_;
v_isShared_981_ = v_isSharedCheck_992_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_v_978_);
lean_inc(v_k_977_);
lean_dec(v_r_971_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_992_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = lean_unsigned_to_nat(3u);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 4, v_l_954_);
lean_ctor_set(v___x_980_, 3, v_l_954_);
lean_ctor_set(v___x_980_, 2, v_v_973_);
lean_ctor_set(v___x_980_, 1, v_k_972_);
lean_ctor_set(v___x_980_, 0, v___x_868_);
v___x_984_ = v___x_980_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_k_972_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v_v_973_);
lean_ctor_set(v_reuseFailAlloc_991_, 3, v_l_954_);
lean_ctor_set(v_reuseFailAlloc_991_, 4, v_l_954_);
v___x_984_ = v_reuseFailAlloc_991_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 4, v_l_954_);
lean_ctor_set(v___x_975_, 2, v_v_860_);
lean_ctor_set(v___x_975_, 1, v_k_859_);
lean_ctor_set(v___x_975_, 0, v___x_868_);
v___x_986_ = v___x_975_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_k_859_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_v_860_);
lean_ctor_set(v_reuseFailAlloc_990_, 3, v_l_954_);
lean_ctor_set(v_reuseFailAlloc_990_, 4, v_l_954_);
v___x_986_ = v_reuseFailAlloc_990_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_988_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 4, v___x_986_);
lean_ctor_set(v___x_864_, 3, v___x_984_);
lean_ctor_set(v___x_864_, 2, v_v_978_);
lean_ctor_set(v___x_864_, 1, v_k_977_);
lean_ctor_set(v___x_864_, 0, v___x_982_);
v___x_988_ = v___x_864_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_k_977_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_v_978_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v___x_984_);
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
}
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_1000_ = lean_unsigned_to_nat(2u);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 4, v_r_971_);
lean_ctor_set(v___x_864_, 3, v_impl_867_);
lean_ctor_set(v___x_864_, 0, v___x_1000_);
v___x_1002_ = v___x_864_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_k_859_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v_v_860_);
lean_ctor_set(v_reuseFailAlloc_1003_, 3, v_impl_867_);
lean_ctor_set(v_reuseFailAlloc_1003_, 4, v_r_971_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1005_; 
lean_dec(v_v_860_);
lean_dec(v_k_859_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 2, v_v_856_);
lean_ctor_set(v___x_864_, 1, v_k_855_);
v___x_1005_ = v___x_864_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_size_858_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_k_855_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_v_856_);
lean_ctor_set(v_reuseFailAlloc_1006_, 3, v_l_861_);
lean_ctor_set(v_reuseFailAlloc_1006_, 4, v_r_862_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
default: 
{
lean_object* v_impl_1007_; lean_object* v___x_1008_; 
lean_dec(v_size_858_);
v_impl_1007_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_855_, v_v_856_, v_r_862_);
v___x_1008_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_861_) == 0)
{
lean_object* v_size_1009_; lean_object* v_size_1010_; lean_object* v_k_1011_; lean_object* v_v_1012_; lean_object* v_l_1013_; lean_object* v_r_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_size_1009_ = lean_ctor_get(v_l_861_, 0);
v_size_1010_ = lean_ctor_get(v_impl_1007_, 0);
v_k_1011_ = lean_ctor_get(v_impl_1007_, 1);
v_v_1012_ = lean_ctor_get(v_impl_1007_, 2);
v_l_1013_ = lean_ctor_get(v_impl_1007_, 3);
lean_inc(v_l_1013_);
v_r_1014_ = lean_ctor_get(v_impl_1007_, 4);
v___x_1015_ = lean_unsigned_to_nat(3u);
v___x_1016_ = lean_nat_mul(v___x_1015_, v_size_1009_);
v___x_1017_ = lean_nat_dec_lt(v___x_1016_, v_size_1010_);
lean_dec(v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
lean_dec(v_l_1013_);
v___x_1018_ = lean_nat_add(v___x_1008_, v_size_1009_);
v___x_1019_ = lean_nat_add(v___x_1018_, v_size_1010_);
lean_dec(v___x_1018_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 4, v_impl_1007_);
lean_ctor_set(v___x_864_, 0, v___x_1019_);
v___x_1021_ = v___x_864_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_k_859_);
lean_ctor_set(v_reuseFailAlloc_1022_, 2, v_v_860_);
lean_ctor_set(v_reuseFailAlloc_1022_, 3, v_l_861_);
lean_ctor_set(v_reuseFailAlloc_1022_, 4, v_impl_1007_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
else
{
lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1086_; 
lean_inc(v_r_1014_);
lean_inc(v_v_1012_);
lean_inc(v_k_1011_);
lean_inc(v_size_1010_);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_impl_1007_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; lean_object* v_unused_1088_; lean_object* v_unused_1089_; lean_object* v_unused_1090_; lean_object* v_unused_1091_; 
v_unused_1087_ = lean_ctor_get(v_impl_1007_, 4);
lean_dec(v_unused_1087_);
v_unused_1088_ = lean_ctor_get(v_impl_1007_, 3);
lean_dec(v_unused_1088_);
v_unused_1089_ = lean_ctor_get(v_impl_1007_, 2);
lean_dec(v_unused_1089_);
v_unused_1090_ = lean_ctor_get(v_impl_1007_, 1);
lean_dec(v_unused_1090_);
v_unused_1091_ = lean_ctor_get(v_impl_1007_, 0);
lean_dec(v_unused_1091_);
v___x_1024_ = v_impl_1007_;
v_isShared_1025_ = v_isSharedCheck_1086_;
goto v_resetjp_1023_;
}
else
{
lean_dec(v_impl_1007_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1086_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v_size_1026_; lean_object* v_k_1027_; lean_object* v_v_1028_; lean_object* v_l_1029_; lean_object* v_r_1030_; lean_object* v_size_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_size_1026_ = lean_ctor_get(v_l_1013_, 0);
v_k_1027_ = lean_ctor_get(v_l_1013_, 1);
v_v_1028_ = lean_ctor_get(v_l_1013_, 2);
v_l_1029_ = lean_ctor_get(v_l_1013_, 3);
v_r_1030_ = lean_ctor_get(v_l_1013_, 4);
v_size_1031_ = lean_ctor_get(v_r_1014_, 0);
v___x_1032_ = lean_unsigned_to_nat(2u);
v___x_1033_ = lean_nat_mul(v___x_1032_, v_size_1031_);
v___x_1034_ = lean_nat_dec_lt(v_size_1026_, v___x_1033_);
lean_dec(v___x_1033_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1062_; 
lean_inc(v_r_1030_);
lean_inc(v_l_1029_);
lean_inc(v_v_1028_);
lean_inc(v_k_1027_);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_l_1013_);
if (v_isSharedCheck_1062_ == 0)
{
lean_object* v_unused_1063_; lean_object* v_unused_1064_; lean_object* v_unused_1065_; lean_object* v_unused_1066_; lean_object* v_unused_1067_; 
v_unused_1063_ = lean_ctor_get(v_l_1013_, 4);
lean_dec(v_unused_1063_);
v_unused_1064_ = lean_ctor_get(v_l_1013_, 3);
lean_dec(v_unused_1064_);
v_unused_1065_ = lean_ctor_get(v_l_1013_, 2);
lean_dec(v_unused_1065_);
v_unused_1066_ = lean_ctor_get(v_l_1013_, 1);
lean_dec(v_unused_1066_);
v_unused_1067_ = lean_ctor_get(v_l_1013_, 0);
lean_dec(v_unused_1067_);
v___x_1036_ = v_l_1013_;
v_isShared_1037_ = v_isSharedCheck_1062_;
goto v_resetjp_1035_;
}
else
{
lean_dec(v_l_1013_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1062_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1052_; 
v___x_1038_ = lean_nat_add(v___x_1008_, v_size_1009_);
v___x_1039_ = lean_nat_add(v___x_1038_, v_size_1010_);
lean_dec(v_size_1010_);
if (lean_obj_tag(v_l_1029_) == 0)
{
lean_object* v_size_1060_; 
v_size_1060_ = lean_ctor_get(v_l_1029_, 0);
lean_inc(v_size_1060_);
v___y_1052_ = v_size_1060_;
goto v___jp_1051_;
}
else
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_unsigned_to_nat(0u);
v___y_1052_ = v___x_1061_;
goto v___jp_1051_;
}
v___jp_1040_:
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1044_ = lean_nat_add(v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec(v___y_1042_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v_r_1014_);
lean_ctor_set(v___x_1036_, 3, v_r_1030_);
lean_ctor_set(v___x_1036_, 2, v_v_1012_);
lean_ctor_set(v___x_1036_, 1, v_k_1011_);
lean_ctor_set(v___x_1036_, 0, v___x_1044_);
v___x_1046_ = v___x_1036_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_k_1011_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_v_1012_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v_r_1030_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v_r_1014_);
v___x_1046_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1048_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 4, v___x_1046_);
lean_ctor_set(v___x_1024_, 3, v___y_1041_);
lean_ctor_set(v___x_1024_, 2, v_v_1028_);
lean_ctor_set(v___x_1024_, 1, v_k_1027_);
lean_ctor_set(v___x_1024_, 0, v___x_1039_);
v___x_1048_ = v___x_1024_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_k_1027_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_v_1028_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v___y_1041_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
v___jp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1053_ = lean_nat_add(v___x_1038_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec(v___x_1038_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 4, v_l_1029_);
lean_ctor_set(v___x_864_, 0, v___x_1053_);
v___x_1055_ = v___x_864_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_k_859_);
lean_ctor_set(v_reuseFailAlloc_1059_, 2, v_v_860_);
lean_ctor_set(v_reuseFailAlloc_1059_, 3, v_l_861_);
lean_ctor_set(v_reuseFailAlloc_1059_, 4, v_l_1029_);
v___x_1055_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_nat_add(v___x_1008_, v_size_1031_);
if (lean_obj_tag(v_r_1030_) == 0)
{
lean_object* v_size_1057_; 
v_size_1057_ = lean_ctor_get(v_r_1030_, 0);
lean_inc(v_size_1057_);
v___y_1041_ = v___x_1055_;
v___y_1042_ = v___x_1056_;
v___y_1043_ = v_size_1057_;
goto v___jp_1040_;
}
else
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_unsigned_to_nat(0u);
v___y_1041_ = v___x_1055_;
v___y_1042_ = v___x_1056_;
v___y_1043_ = v___x_1058_;
goto v___jp_1040_;
}
}
}
}
}
else
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
lean_del_object(v___x_864_);
v___x_1068_ = lean_nat_add(v___x_1008_, v_size_1009_);
v___x_1069_ = lean_nat_add(v___x_1068_, v_size_1010_);
lean_dec(v_size_1010_);
v___x_1070_ = lean_nat_add(v___x_1068_, v_size_1026_);
lean_dec(v___x_1068_);
lean_inc_ref(v_l_861_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 4, v_l_1013_);
lean_ctor_set(v___x_1024_, 3, v_l_861_);
lean_ctor_set(v___x_1024_, 2, v_v_860_);
lean_ctor_set(v___x_1024_, 1, v_k_859_);
lean_ctor_set(v___x_1024_, 0, v___x_1070_);
v___x_1072_ = v___x_1024_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_k_859_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v_v_860_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v_l_861_);
lean_ctor_set(v_reuseFailAlloc_1085_, 4, v_l_1013_);
v___x_1072_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
v_isSharedCheck_1079_ = !lean_is_exclusive(v_l_861_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; lean_object* v_unused_1081_; lean_object* v_unused_1082_; lean_object* v_unused_1083_; lean_object* v_unused_1084_; 
v_unused_1080_ = lean_ctor_get(v_l_861_, 4);
lean_dec(v_unused_1080_);
v_unused_1081_ = lean_ctor_get(v_l_861_, 3);
lean_dec(v_unused_1081_);
v_unused_1082_ = lean_ctor_get(v_l_861_, 2);
lean_dec(v_unused_1082_);
v_unused_1083_ = lean_ctor_get(v_l_861_, 1);
lean_dec(v_unused_1083_);
v_unused_1084_ = lean_ctor_get(v_l_861_, 0);
lean_dec(v_unused_1084_);
v___x_1074_ = v_l_861_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_dec(v_l_861_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 4, v_r_1014_);
lean_ctor_set(v___x_1074_, 3, v___x_1072_);
lean_ctor_set(v___x_1074_, 2, v_v_1012_);
lean_ctor_set(v___x_1074_, 1, v_k_1011_);
lean_ctor_set(v___x_1074_, 0, v___x_1069_);
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_k_1011_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v_v_1012_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1078_, 4, v_r_1014_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1092_; 
v_l_1092_ = lean_ctor_get(v_impl_1007_, 3);
lean_inc(v_l_1092_);
if (lean_obj_tag(v_l_1092_) == 0)
{
lean_object* v_r_1093_; lean_object* v_k_1094_; lean_object* v_v_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1118_; 
v_r_1093_ = lean_ctor_get(v_impl_1007_, 4);
v_k_1094_ = lean_ctor_get(v_impl_1007_, 1);
v_v_1095_ = lean_ctor_get(v_impl_1007_, 2);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_impl_1007_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; lean_object* v_unused_1120_; 
v_unused_1119_ = lean_ctor_get(v_impl_1007_, 3);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_impl_1007_, 0);
lean_dec(v_unused_1120_);
v___x_1097_ = v_impl_1007_;
v_isShared_1098_ = v_isSharedCheck_1118_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_r_1093_);
lean_inc(v_v_1095_);
lean_inc(v_k_1094_);
lean_dec(v_impl_1007_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1118_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v_k_1099_; lean_object* v_v_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1114_; 
v_k_1099_ = lean_ctor_get(v_l_1092_, 1);
v_v_1100_ = lean_ctor_get(v_l_1092_, 2);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_l_1092_);
if (v_isSharedCheck_1114_ == 0)
{
lean_object* v_unused_1115_; lean_object* v_unused_1116_; lean_object* v_unused_1117_; 
v_unused_1115_ = lean_ctor_get(v_l_1092_, 4);
lean_dec(v_unused_1115_);
v_unused_1116_ = lean_ctor_get(v_l_1092_, 3);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v_l_1092_, 0);
lean_dec(v_unused_1117_);
v___x_1102_ = v_l_1092_;
v_isShared_1103_ = v_isSharedCheck_1114_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_v_1100_);
lean_inc(v_k_1099_);
lean_dec(v_l_1092_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1114_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1104_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1093_, 2);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 4, v_r_1093_);
lean_ctor_set(v___x_1102_, 3, v_r_1093_);
lean_ctor_set(v___x_1102_, 2, v_v_860_);
lean_ctor_set(v___x_1102_, 1, v_k_859_);
lean_ctor_set(v___x_1102_, 0, v___x_1008_);
v___x_1106_ = v___x_1102_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_k_859_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_v_860_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v_r_1093_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v_r_1093_);
v___x_1106_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1108_; 
lean_inc(v_r_1093_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 3, v_r_1093_);
lean_ctor_set(v___x_1097_, 0, v___x_1008_);
v___x_1108_ = v___x_1097_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_k_1094_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_v_1095_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v_r_1093_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v_r_1093_);
v___x_1108_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1110_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 4, v___x_1108_);
lean_ctor_set(v___x_864_, 3, v___x_1106_);
lean_ctor_set(v___x_864_, 2, v_v_1100_);
lean_ctor_set(v___x_864_, 1, v_k_1099_);
lean_ctor_set(v___x_864_, 0, v___x_1104_);
v___x_1110_ = v___x_864_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_k_1099_);
lean_ctor_set(v_reuseFailAlloc_1111_, 2, v_v_1100_);
lean_ctor_set(v_reuseFailAlloc_1111_, 3, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1111_, 4, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
}
else
{
lean_object* v_r_1121_; 
v_r_1121_ = lean_ctor_get(v_impl_1007_, 4);
lean_inc(v_r_1121_);
if (lean_obj_tag(v_r_1121_) == 0)
{
lean_object* v_k_1122_; lean_object* v_v_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1134_; 
v_k_1122_ = lean_ctor_get(v_impl_1007_, 1);
v_v_1123_ = lean_ctor_get(v_impl_1007_, 2);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_impl_1007_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; lean_object* v_unused_1136_; lean_object* v_unused_1137_; 
v_unused_1135_ = lean_ctor_get(v_impl_1007_, 4);
lean_dec(v_unused_1135_);
v_unused_1136_ = lean_ctor_get(v_impl_1007_, 3);
lean_dec(v_unused_1136_);
v_unused_1137_ = lean_ctor_get(v_impl_1007_, 0);
lean_dec(v_unused_1137_);
v___x_1125_ = v_impl_1007_;
v_isShared_1126_ = v_isSharedCheck_1134_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_v_1123_);
lean_inc(v_k_1122_);
lean_dec(v_impl_1007_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1134_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = lean_unsigned_to_nat(3u);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 4, v_l_1092_);
lean_ctor_set(v___x_1125_, 2, v_v_860_);
lean_ctor_set(v___x_1125_, 1, v_k_859_);
lean_ctor_set(v___x_1125_, 0, v___x_1008_);
v___x_1129_ = v___x_1125_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_k_859_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_v_860_);
lean_ctor_set(v_reuseFailAlloc_1133_, 3, v_l_1092_);
lean_ctor_set(v_reuseFailAlloc_1133_, 4, v_l_1092_);
v___x_1129_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1131_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 4, v_r_1121_);
lean_ctor_set(v___x_864_, 3, v___x_1129_);
lean_ctor_set(v___x_864_, 2, v_v_1123_);
lean_ctor_set(v___x_864_, 1, v_k_1122_);
lean_ctor_set(v___x_864_, 0, v___x_1127_);
v___x_1131_ = v___x_864_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_k_1122_);
lean_ctor_set(v_reuseFailAlloc_1132_, 2, v_v_1123_);
lean_ctor_set(v_reuseFailAlloc_1132_, 3, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1132_, 4, v_r_1121_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = lean_unsigned_to_nat(2u);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 4, v_impl_1007_);
lean_ctor_set(v___x_864_, 3, v_r_1121_);
lean_ctor_set(v___x_864_, 0, v___x_1138_);
v___x_1140_ = v___x_864_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_k_859_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_v_860_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v_r_1121_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v_impl_1007_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
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
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_unsigned_to_nat(1u);
v___x_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
lean_ctor_set(v___x_1144_, 1, v_k_855_);
lean_ctor_set(v___x_1144_, 2, v_v_856_);
lean_ctor_set(v___x_1144_, 3, v_t_857_);
lean_ctor_set(v___x_1144_, 4, v_t_857_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(lean_object* v_as_x27_1145_, lean_object* v_b_1146_){
_start:
{
if (lean_obj_tag(v_as_x27_1145_) == 0)
{
return v_b_1146_;
}
else
{
lean_object* v_head_1147_; lean_object* v_tail_1148_; lean_object* v_fst_1149_; lean_object* v_snd_1150_; lean_object* v_r_1151_; 
v_head_1147_ = lean_ctor_get(v_as_x27_1145_, 0);
v_tail_1148_ = lean_ctor_get(v_as_x27_1145_, 1);
v_fst_1149_ = lean_ctor_get(v_head_1147_, 0);
v_snd_1150_ = lean_ctor_get(v_head_1147_, 1);
lean_inc(v_snd_1150_);
lean_inc(v_fst_1149_);
v_r_1151_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_fst_1149_, v_snd_1150_, v_b_1146_);
v_as_x27_1145_ = v_tail_1148_;
v_b_1146_ = v_r_1151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg___boxed(lean_object* v_as_x27_1153_, lean_object* v_b_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1153_, v_b_1154_);
lean_dec(v_as_x27_1153_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj(lean_object* v_o_1156_){
_start:
{
lean_object* v_r_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_r_1157_ = lean_box(1);
v___x_1158_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_o_1156_, v_r_1157_);
v___x_1159_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj___boxed(lean_object* v_o_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_Json_mkObj(v_o_1160_);
lean_dec(v_o_1160_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0(lean_object* v_00_u03b2_1162_, lean_object* v_k_1163_, lean_object* v_v_1164_, lean_object* v_t_1165_, lean_object* v_hl_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_1163_, v_v_1164_, v_t_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(lean_object* v_as_1168_, lean_object* v_as_x27_1169_, lean_object* v_b_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1169_, v_b_1170_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___boxed(lean_object* v_as_1173_, lean_object* v_as_x27_1174_, lean_object* v_b_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(v_as_1173_, v_as_x27_1174_, v_b_1175_, v_a_1176_);
lean_dec(v_as_x27_1174_);
lean_dec(v_as_1173_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeNat___lam__0(lean_object* v_n_1178_){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = l_Lean_JsonNumber_fromNat(v_n_1178_);
v___x_1180_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeInt___lam__0(lean_object* v_n_1183_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = l_Lean_JsonNumber_fromInt(v_n_1183_);
v___x_1185_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeString___lam__0(lean_object* v_s_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1189_, 0, v_s_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0(uint8_t v_b_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1193_, 0, v_b_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0___boxed(lean_object* v_b_1194_){
_start:
{
uint8_t v_b_boxed_1195_; lean_object* v_res_1196_; 
v_b_boxed_1195_ = lean_unbox(v_b_1194_);
v_res_1196_ = l_Lean_Json_instCoeBool___lam__0(v_b_boxed_1195_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instOfNat(lean_object* v_n_1199_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = l_Lean_JsonNumber_fromNat(v_n_1199_);
v___x_1201_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_isNull(lean_object* v_x_1202_){
_start:
{
if (lean_obj_tag(v_x_1202_) == 0)
{
uint8_t v___x_1203_; 
v___x_1203_ = 1;
return v___x_1203_;
}
else
{
uint8_t v___x_1204_; 
v___x_1204_ = 0;
return v___x_1204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_isNull___boxed(lean_object* v_x_1205_){
_start:
{
uint8_t v_res_1206_; lean_object* v_r_1207_; 
v_res_1206_ = l_Lean_Json_isNull(v_x_1205_);
lean_dec(v_x_1205_);
v_r_1207_ = lean_box(v_res_1206_);
return v_r_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObj_x3f(lean_object* v_x_1211_){
_start:
{
if (lean_obj_tag(v_x_1211_) == 5)
{
lean_object* v_kvPairs_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
v_kvPairs_1212_ = lean_ctor_get(v_x_1211_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_x_1211_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v_x_1211_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_kvPairs_1212_);
lean_dec(v_x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set_tag(v___x_1214_, 1);
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_kvPairs_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
else
{
lean_object* v___x_1220_; 
lean_dec(v_x_1211_);
v___x_1220_ = ((lean_object*)(l_Lean_Json_getObj_x3f___closed__1));
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArr_x3f(lean_object* v_x_1224_){
_start:
{
if (lean_obj_tag(v_x_1224_) == 4)
{
lean_object* v_elems_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
v_elems_1225_ = lean_ctor_get(v_x_1224_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_x_1224_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v_x_1224_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_elems_1225_);
lean_dec(v_x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set_tag(v___x_1227_, 1);
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_elems_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
else
{
lean_object* v___x_1233_; 
lean_dec(v_x_1224_);
v___x_1233_ = ((lean_object*)(l_Lean_Json_getArr_x3f___closed__1));
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getStr_x3f(lean_object* v_x_1237_){
_start:
{
if (lean_obj_tag(v_x_1237_) == 3)
{
lean_object* v_s_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
v_s_1238_ = lean_ctor_get(v_x_1237_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_x_1237_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v_x_1237_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_s_1238_);
lean_dec(v_x_1237_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set_tag(v___x_1240_, 1);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_s_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
else
{
lean_object* v___x_1246_; 
lean_dec(v_x_1237_);
v___x_1246_ = ((lean_object*)(l_Lean_Json_getStr_x3f___closed__1));
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNat_x3f(lean_object* v_x_1250_){
_start:
{
if (lean_obj_tag(v_x_1250_) == 2)
{
lean_object* v_n_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1267_; 
v_n_1253_ = lean_ctor_get(v_x_1250_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_x_1250_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1255_ = v_x_1250_;
v_isShared_1256_ = v_isSharedCheck_1267_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_n_1253_);
lean_dec(v_x_1250_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1267_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v_mantissa_1257_; lean_object* v_exponent_1258_; lean_object* v_natZero_1259_; lean_object* v_intZero_1260_; uint8_t v_isNeg_1261_; 
v_mantissa_1257_ = lean_ctor_get(v_n_1253_, 0);
lean_inc(v_mantissa_1257_);
v_exponent_1258_ = lean_ctor_get(v_n_1253_, 1);
lean_inc(v_exponent_1258_);
lean_dec_ref(v_n_1253_);
v_natZero_1259_ = lean_unsigned_to_nat(0u);
v_intZero_1260_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v_isNeg_1261_ = lean_int_dec_lt(v_mantissa_1257_, v_intZero_1260_);
if (v_isNeg_1261_ == 0)
{
uint8_t v___x_1262_; 
v___x_1262_ = lean_nat_dec_eq(v_exponent_1258_, v_natZero_1259_);
lean_dec(v_exponent_1258_);
if (v___x_1262_ == 0)
{
lean_dec(v_mantissa_1257_);
lean_del_object(v___x_1255_);
goto v___jp_1251_;
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; 
v_a_1263_ = lean_nat_abs(v_mantissa_1257_);
lean_dec(v_mantissa_1257_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set_tag(v___x_1255_, 1);
lean_ctor_set(v___x_1255_, 0, v_a_1263_);
v___x_1265_ = v___x_1255_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
else
{
lean_dec(v_exponent_1258_);
lean_dec(v_mantissa_1257_);
lean_del_object(v___x_1255_);
goto v___jp_1251_;
}
}
}
else
{
lean_dec(v_x_1250_);
goto v___jp_1251_;
}
v___jp_1251_:
{
lean_object* v___x_1252_; 
v___x_1252_ = ((lean_object*)(l_Lean_Json_getNat_x3f___closed__1));
return v___x_1252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getInt_x3f(lean_object* v_x_1271_){
_start:
{
if (lean_obj_tag(v_x_1271_) == 2)
{
lean_object* v_n_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1285_; 
v_n_1274_ = lean_ctor_get(v_x_1271_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_x_1271_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1276_ = v_x_1271_;
v_isShared_1277_ = v_isSharedCheck_1285_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_n_1274_);
lean_dec(v_x_1271_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1285_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v_mantissa_1278_; lean_object* v_exponent_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v_mantissa_1278_ = lean_ctor_get(v_n_1274_, 0);
lean_inc(v_mantissa_1278_);
v_exponent_1279_ = lean_ctor_get(v_n_1274_, 1);
lean_inc(v_exponent_1279_);
lean_dec_ref(v_n_1274_);
v___x_1280_ = lean_unsigned_to_nat(0u);
v___x_1281_ = lean_nat_dec_eq(v_exponent_1279_, v___x_1280_);
lean_dec(v_exponent_1279_);
if (v___x_1281_ == 0)
{
lean_dec(v_mantissa_1278_);
lean_del_object(v___x_1276_);
goto v___jp_1272_;
}
else
{
lean_object* v___x_1283_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set_tag(v___x_1276_, 1);
lean_ctor_set(v___x_1276_, 0, v_mantissa_1278_);
v___x_1283_ = v___x_1276_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_mantissa_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
else
{
lean_dec(v_x_1271_);
goto v___jp_1272_;
}
v___jp_1272_:
{
lean_object* v___x_1273_; 
v___x_1273_ = ((lean_object*)(l_Lean_Json_getInt_x3f___closed__1));
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f(lean_object* v_x_1289_){
_start:
{
if (lean_obj_tag(v_x_1289_) == 1)
{
uint8_t v_b_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v_b_1290_ = lean_ctor_get_uint8(v_x_1289_, 0);
v___x_1291_ = lean_box(v_b_1290_);
v___x_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
return v___x_1292_;
}
else
{
lean_object* v___x_1293_; 
v___x_1293_ = ((lean_object*)(l_Lean_Json_getBool_x3f___closed__1));
return v___x_1293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object* v_x_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Json_getBool_x3f(v_x_1294_);
lean_dec(v_x_1294_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNum_x3f(lean_object* v_x_1299_){
_start:
{
if (lean_obj_tag(v_x_1299_) == 2)
{
lean_object* v_n_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
v_n_1300_ = lean_ctor_get(v_x_1299_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v_x_1299_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v_x_1299_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_n_1300_);
lean_dec(v_x_1299_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set_tag(v___x_1302_, 1);
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_n_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
else
{
lean_object* v___x_1308_; 
lean_dec(v_x_1299_);
v___x_1308_ = ((lean_object*)(l_Lean_Json_getNum_x3f___closed__1));
return v___x_1308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f(lean_object* v_x_1312_, lean_object* v_x_1313_){
_start:
{
if (lean_obj_tag(v_x_1312_) == 5)
{
lean_object* v_kvPairs_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1332_; 
v_kvPairs_1314_ = lean_ctor_get(v_x_1312_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_x_1312_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1316_ = v_x_1312_;
v_isShared_1317_ = v_isSharedCheck_1332_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_kvPairs_1314_);
lean_dec(v_x_1312_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1332_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_1314_, v_x_1313_);
lean_dec(v_kvPairs_1314_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1319_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__0));
v___x_1320_ = lean_string_append(v___x_1319_, v_x_1313_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set_tag(v___x_1316_, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1320_);
v___x_1322_ = v___x_1316_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
else
{
lean_object* v_val_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_del_object(v___x_1316_);
v_val_1324_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1318_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_val_1324_);
lean_dec(v___x_1318_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_val_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
else
{
lean_object* v___x_1333_; 
lean_dec(v_x_1312_);
v___x_1333_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__1));
return v___x_1333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f___boxed(lean_object* v_x_1334_, lean_object* v_x_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_Json_getObjVal_x3f(v_x_1334_, v_x_1335_);
lean_dec_ref(v_x_1335_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArrVal_x3f(lean_object* v_x_1340_, lean_object* v_x_1341_){
_start:
{
if (lean_obj_tag(v_x_1340_) == 4)
{
lean_object* v_elems_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1358_; 
v_elems_1342_ = lean_ctor_get(v_x_1340_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_x_1340_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1344_ = v_x_1340_;
v_isShared_1345_ = v_isSharedCheck_1358_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_elems_1342_);
lean_dec(v_x_1340_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1358_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = lean_array_get_size(v_elems_1342_);
v___x_1347_ = lean_nat_dec_lt(v_x_1341_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
lean_dec_ref(v_elems_1342_);
v___x_1348_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__0));
v___x_1349_ = l_Nat_reprFast(v_x_1341_);
v___x_1350_ = lean_string_append(v___x_1348_, v___x_1349_);
lean_dec_ref(v___x_1349_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1350_);
v___x_1352_ = v___x_1344_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1354_ = lean_array_fget(v_elems_1342_, v_x_1341_);
lean_dec(v_x_1341_);
lean_dec_ref(v_elems_1342_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 1);
lean_ctor_set(v___x_1344_, 0, v___x_1354_);
v___x_1356_ = v___x_1344_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
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
else
{
lean_object* v___x_1359_; 
lean_dec(v_x_1341_);
lean_dec(v_x_1340_);
v___x_1359_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__1));
return v___x_1359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD(lean_object* v_j_1360_, lean_object* v_k_1361_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_Json_getObjVal_x3f(v_j_1360_, v_k_1361_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v___x_1363_; 
lean_dec_ref_known(v___x_1362_, 1);
v___x_1363_ = lean_box(0);
return v___x_1363_;
}
else
{
lean_object* v_a_1364_; 
v_a_1364_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1362_, 1);
return v_a_1364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD___boxed(lean_object* v_j_1365_, lean_object* v_k_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Json_getObjValD(v_j_1365_, v_k_1366_);
lean_dec_ref(v_k_1366_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Json_setObjVal_x21_spec__1(lean_object* v_msg_1368_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_box(0);
v___x_1370_ = lean_panic_fn_borrowed(v___x_1369_, v_msg_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(lean_object* v_msg_1371_){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_box(1);
v___x_1373_ = lean_panic_fn_borrowed(v___x_1372_, v_msg_1371_);
return v___x_1373_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1377_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1378_ = lean_unsigned_to_nat(35u);
v___x_1379_ = lean_unsigned_to_nat(182u);
v___x_1380_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1381_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1382_ = l_mkPanicMessageWithDecl(v___x_1381_, v___x_1380_, v___x_1379_, v___x_1378_, v___x_1377_);
return v___x_1382_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1383_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1384_ = lean_unsigned_to_nat(21u);
v___x_1385_ = lean_unsigned_to_nat(183u);
v___x_1386_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1387_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1388_ = l_mkPanicMessageWithDecl(v___x_1387_, v___x_1386_, v___x_1385_, v___x_1384_, v___x_1383_);
return v___x_1388_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1391_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1392_ = lean_unsigned_to_nat(35u);
v___x_1393_ = lean_unsigned_to_nat(276u);
v___x_1394_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1395_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1396_ = l_mkPanicMessageWithDecl(v___x_1395_, v___x_1394_, v___x_1393_, v___x_1392_, v___x_1391_);
return v___x_1396_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1397_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1398_ = lean_unsigned_to_nat(21u);
v___x_1399_ = lean_unsigned_to_nat(277u);
v___x_1400_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1401_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1402_ = l_mkPanicMessageWithDecl(v___x_1401_, v___x_1400_, v___x_1399_, v___x_1398_, v___x_1397_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(lean_object* v_k_1403_, lean_object* v_v_1404_, lean_object* v_t_1405_){
_start:
{
if (lean_obj_tag(v_t_1405_) == 0)
{
lean_object* v_size_1406_; lean_object* v_k_1407_; lean_object* v_v_1408_; lean_object* v_l_1409_; lean_object* v_r_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1766_; 
v_size_1406_ = lean_ctor_get(v_t_1405_, 0);
v_k_1407_ = lean_ctor_get(v_t_1405_, 1);
v_v_1408_ = lean_ctor_get(v_t_1405_, 2);
v_l_1409_ = lean_ctor_get(v_t_1405_, 3);
v_r_1410_ = lean_ctor_get(v_t_1405_, 4);
v_isSharedCheck_1766_ = !lean_is_exclusive(v_t_1405_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1412_ = v_t_1405_;
v_isShared_1413_ = v_isSharedCheck_1766_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_r_1410_);
lean_inc(v_l_1409_);
lean_inc(v_v_1408_);
lean_inc(v_k_1407_);
lean_inc(v_size_1406_);
lean_dec(v_t_1405_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1766_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
uint8_t v___x_1414_; 
v___x_1414_ = lean_string_compare(v_k_1403_, v_k_1407_);
switch(v___x_1414_)
{
case 0:
{
lean_object* v___x_1415_; 
lean_dec(v_size_1406_);
v___x_1415_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1403_, v_v_1404_, v_l_1409_);
if (lean_obj_tag(v_r_1410_) == 0)
{
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_size_1416_; lean_object* v_size_1417_; lean_object* v_k_1418_; lean_object* v_v_1419_; lean_object* v_l_1420_; lean_object* v_r_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v_size_1416_ = lean_ctor_get(v_r_1410_, 0);
v_size_1417_ = lean_ctor_get(v___x_1415_, 0);
v_k_1418_ = lean_ctor_get(v___x_1415_, 1);
v_v_1419_ = lean_ctor_get(v___x_1415_, 2);
v_l_1420_ = lean_ctor_get(v___x_1415_, 3);
v_r_1421_ = lean_ctor_get(v___x_1415_, 4);
lean_inc(v_r_1421_);
v___x_1422_ = lean_unsigned_to_nat(3u);
v___x_1423_ = lean_nat_mul(v___x_1422_, v_size_1416_);
v___x_1424_ = lean_nat_dec_lt(v___x_1423_, v_size_1417_);
lean_dec(v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
lean_dec(v_r_1421_);
v___x_1425_ = lean_unsigned_to_nat(1u);
v___x_1426_ = lean_nat_add(v___x_1425_, v_size_1417_);
v___x_1427_ = lean_nat_add(v___x_1426_, v_size_1416_);
lean_dec(v___x_1426_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 3, v___x_1415_);
lean_ctor_set(v___x_1412_, 0, v___x_1427_);
v___x_1429_ = v___x_1412_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1430_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1430_, 3, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1430_, 4, v_r_1410_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
else
{
lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1502_; 
lean_inc(v_l_1420_);
lean_inc(v_v_1419_);
lean_inc(v_k_1418_);
lean_inc(v_size_1417_);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; lean_object* v_unused_1504_; lean_object* v_unused_1505_; lean_object* v_unused_1506_; lean_object* v_unused_1507_; 
v_unused_1503_ = lean_ctor_get(v___x_1415_, 4);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v___x_1415_, 3);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v___x_1415_, 2);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v___x_1415_, 1);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v___x_1415_, 0);
lean_dec(v_unused_1507_);
v___x_1432_ = v___x_1415_;
v_isShared_1433_ = v_isSharedCheck_1502_;
goto v_resetjp_1431_;
}
else
{
lean_dec(v___x_1415_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1502_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
if (lean_obj_tag(v_l_1420_) == 0)
{
if (lean_obj_tag(v_r_1421_) == 0)
{
lean_object* v_size_1434_; lean_object* v_size_1435_; lean_object* v_k_1436_; lean_object* v_v_1437_; lean_object* v_l_1438_; lean_object* v_r_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_size_1434_ = lean_ctor_get(v_l_1420_, 0);
v_size_1435_ = lean_ctor_get(v_r_1421_, 0);
v_k_1436_ = lean_ctor_get(v_r_1421_, 1);
v_v_1437_ = lean_ctor_get(v_r_1421_, 2);
v_l_1438_ = lean_ctor_get(v_r_1421_, 3);
v_r_1439_ = lean_ctor_get(v_r_1421_, 4);
v___x_1440_ = lean_unsigned_to_nat(2u);
v___x_1441_ = lean_nat_mul(v___x_1440_, v_size_1434_);
v___x_1442_ = lean_nat_dec_lt(v_size_1435_, v___x_1441_);
lean_dec(v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1472_; 
lean_inc(v_r_1439_);
lean_inc(v_l_1438_);
lean_inc(v_v_1437_);
lean_inc(v_k_1436_);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_r_1421_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; lean_object* v_unused_1474_; lean_object* v_unused_1475_; lean_object* v_unused_1476_; lean_object* v_unused_1477_; 
v_unused_1473_ = lean_ctor_get(v_r_1421_, 4);
lean_dec(v_unused_1473_);
v_unused_1474_ = lean_ctor_get(v_r_1421_, 3);
lean_dec(v_unused_1474_);
v_unused_1475_ = lean_ctor_get(v_r_1421_, 2);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_r_1421_, 1);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v_r_1421_, 0);
lean_dec(v_unused_1477_);
v___x_1444_ = v_r_1421_;
v_isShared_1445_ = v_isSharedCheck_1472_;
goto v_resetjp_1443_;
}
else
{
lean_dec(v_r_1421_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1472_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___x_1460_; lean_object* v___y_1462_; 
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_add(v___x_1446_, v_size_1417_);
lean_dec(v_size_1417_);
v___x_1448_ = lean_nat_add(v___x_1447_, v_size_1416_);
lean_dec(v___x_1447_);
v___x_1460_ = lean_nat_add(v___x_1446_, v_size_1434_);
if (lean_obj_tag(v_l_1438_) == 0)
{
lean_object* v_size_1470_; 
v_size_1470_ = lean_ctor_get(v_l_1438_, 0);
lean_inc(v_size_1470_);
v___y_1462_ = v_size_1470_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___y_1462_ = v___x_1471_;
goto v___jp_1461_;
}
v___jp_1449_:
{
lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1453_ = lean_nat_add(v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec(v___y_1451_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 4, v_r_1410_);
lean_ctor_set(v___x_1444_, 3, v_r_1439_);
lean_ctor_set(v___x_1444_, 2, v_v_1408_);
lean_ctor_set(v___x_1444_, 1, v_k_1407_);
lean_ctor_set(v___x_1444_, 0, v___x_1453_);
v___x_1455_ = v___x_1444_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1459_, 3, v_r_1439_);
lean_ctor_set(v_reuseFailAlloc_1459_, 4, v_r_1410_);
v___x_1455_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1457_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 4, v___x_1455_);
lean_ctor_set(v___x_1432_, 3, v___y_1450_);
lean_ctor_set(v___x_1432_, 2, v_v_1437_);
lean_ctor_set(v___x_1432_, 1, v_k_1436_);
lean_ctor_set(v___x_1432_, 0, v___x_1448_);
v___x_1457_ = v___x_1432_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1458_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1458_, 3, v___y_1450_);
lean_ctor_set(v_reuseFailAlloc_1458_, 4, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
v___jp_1461_:
{
lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1463_ = lean_nat_add(v___x_1460_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec(v___x_1460_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v_l_1438_);
lean_ctor_set(v___x_1412_, 3, v_l_1420_);
lean_ctor_set(v___x_1412_, 2, v_v_1419_);
lean_ctor_set(v___x_1412_, 1, v_k_1418_);
lean_ctor_set(v___x_1412_, 0, v___x_1463_);
v___x_1465_ = v___x_1412_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v_l_1420_);
lean_ctor_set(v_reuseFailAlloc_1469_, 4, v_l_1438_);
v___x_1465_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1466_; 
v___x_1466_ = lean_nat_add(v___x_1446_, v_size_1416_);
if (lean_obj_tag(v_r_1439_) == 0)
{
lean_object* v_size_1467_; 
v_size_1467_ = lean_ctor_get(v_r_1439_, 0);
lean_inc(v_size_1467_);
v___y_1450_ = v___x_1465_;
v___y_1451_ = v___x_1466_;
v___y_1452_ = v_size_1467_;
goto v___jp_1449_;
}
else
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_unsigned_to_nat(0u);
v___y_1450_ = v___x_1465_;
v___y_1451_ = v___x_1466_;
v___y_1452_ = v___x_1468_;
goto v___jp_1449_;
}
}
}
}
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
lean_del_object(v___x_1412_);
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = lean_nat_add(v___x_1478_, v_size_1417_);
lean_dec(v_size_1417_);
v___x_1480_ = lean_nat_add(v___x_1479_, v_size_1416_);
lean_dec(v___x_1479_);
v___x_1481_ = lean_nat_add(v___x_1478_, v_size_1416_);
v___x_1482_ = lean_nat_add(v___x_1481_, v_size_1435_);
lean_dec(v___x_1481_);
lean_inc_ref(v_r_1410_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 4, v_r_1410_);
lean_ctor_set(v___x_1432_, 3, v_r_1421_);
lean_ctor_set(v___x_1432_, 2, v_v_1408_);
lean_ctor_set(v___x_1432_, 1, v_k_1407_);
lean_ctor_set(v___x_1432_, 0, v___x_1482_);
v___x_1484_ = v___x_1432_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1497_, 3, v_r_1421_);
lean_ctor_set(v_reuseFailAlloc_1497_, 4, v_r_1410_);
v___x_1484_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
v_isSharedCheck_1491_ = !lean_is_exclusive(v_r_1410_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; lean_object* v_unused_1493_; lean_object* v_unused_1494_; lean_object* v_unused_1495_; lean_object* v_unused_1496_; 
v_unused_1492_ = lean_ctor_get(v_r_1410_, 4);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_r_1410_, 3);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_r_1410_, 2);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_r_1410_, 1);
lean_dec(v_unused_1495_);
v_unused_1496_ = lean_ctor_get(v_r_1410_, 0);
lean_dec(v_unused_1496_);
v___x_1486_ = v_r_1410_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_dec(v_r_1410_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v___x_1484_);
lean_ctor_set(v___x_1486_, 3, v_l_1420_);
lean_ctor_set(v___x_1486_, 2, v_v_1419_);
lean_ctor_set(v___x_1486_, 1, v_k_1418_);
lean_ctor_set(v___x_1486_, 0, v___x_1480_);
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_l_1420_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v___x_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
else
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec_ref_known(v_l_1420_, 5);
lean_del_object(v___x_1432_);
lean_dec(v_v_1419_);
lean_dec(v_k_1418_);
lean_dec(v_size_1417_);
lean_dec_ref_known(v_r_1410_, 5);
lean_del_object(v___x_1412_);
lean_dec(v_v_1408_);
lean_dec(v_k_1407_);
v___x_1498_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3);
v___x_1499_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1498_);
return v___x_1499_;
}
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_del_object(v___x_1432_);
lean_dec(v_r_1421_);
lean_dec(v_v_1419_);
lean_dec(v_k_1418_);
lean_dec(v_size_1417_);
lean_dec_ref_known(v_r_1410_, 5);
lean_del_object(v___x_1412_);
lean_dec(v_v_1408_);
lean_dec(v_k_1407_);
v___x_1500_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4);
v___x_1501_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1500_);
return v___x_1501_;
}
}
}
}
else
{
lean_object* v_size_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v_size_1508_ = lean_ctor_get(v_r_1410_, 0);
v___x_1509_ = lean_unsigned_to_nat(1u);
v___x_1510_ = lean_nat_add(v___x_1509_, v_size_1508_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 3, v___x_1415_);
lean_ctor_set(v___x_1412_, 0, v___x_1510_);
v___x_1512_ = v___x_1412_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1513_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1513_, 3, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1513_, 4, v_r_1410_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
else
{
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_l_1514_; 
v_l_1514_ = lean_ctor_get(v___x_1415_, 3);
if (lean_obj_tag(v_l_1514_) == 0)
{
lean_object* v_r_1515_; 
lean_inc_ref(v_l_1514_);
v_r_1515_ = lean_ctor_get(v___x_1415_, 4);
lean_inc(v_r_1515_);
if (lean_obj_tag(v_r_1515_) == 0)
{
lean_object* v_size_1516_; lean_object* v_k_1517_; lean_object* v_v_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1532_; 
v_size_1516_ = lean_ctor_get(v___x_1415_, 0);
v_k_1517_ = lean_ctor_get(v___x_1415_, 1);
v_v_1518_ = lean_ctor_get(v___x_1415_, 2);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; lean_object* v_unused_1534_; 
v_unused_1533_ = lean_ctor_get(v___x_1415_, 4);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v___x_1415_, 3);
lean_dec(v_unused_1534_);
v___x_1520_ = v___x_1415_;
v_isShared_1521_ = v_isSharedCheck_1532_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_v_1518_);
lean_inc(v_k_1517_);
lean_inc(v_size_1516_);
lean_dec(v___x_1415_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1532_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v_size_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
v_size_1522_ = lean_ctor_get(v_r_1515_, 0);
v___x_1523_ = lean_unsigned_to_nat(1u);
v___x_1524_ = lean_nat_add(v___x_1523_, v_size_1516_);
lean_dec(v_size_1516_);
v___x_1525_ = lean_nat_add(v___x_1523_, v_size_1522_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 4, v_r_1410_);
lean_ctor_set(v___x_1520_, 3, v_r_1515_);
lean_ctor_set(v___x_1520_, 2, v_v_1408_);
lean_ctor_set(v___x_1520_, 1, v_k_1407_);
lean_ctor_set(v___x_1520_, 0, v___x_1525_);
v___x_1527_ = v___x_1520_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_r_1515_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_r_1410_);
v___x_1527_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1529_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v___x_1527_);
lean_ctor_set(v___x_1412_, 3, v_l_1514_);
lean_ctor_set(v___x_1412_, 2, v_v_1518_);
lean_ctor_set(v___x_1412_, 1, v_k_1517_);
lean_ctor_set(v___x_1412_, 0, v___x_1524_);
v___x_1529_ = v___x_1412_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_k_1517_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_v_1518_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_l_1514_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
else
{
lean_object* v_k_1535_; lean_object* v_v_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1548_; 
v_k_1535_ = lean_ctor_get(v___x_1415_, 1);
v_v_1536_ = lean_ctor_get(v___x_1415_, 2);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; lean_object* v_unused_1550_; lean_object* v_unused_1551_; 
v_unused_1549_ = lean_ctor_get(v___x_1415_, 4);
lean_dec(v_unused_1549_);
v_unused_1550_ = lean_ctor_get(v___x_1415_, 3);
lean_dec(v_unused_1550_);
v_unused_1551_ = lean_ctor_get(v___x_1415_, 0);
lean_dec(v_unused_1551_);
v___x_1538_ = v___x_1415_;
v_isShared_1539_ = v_isSharedCheck_1548_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_v_1536_);
lean_inc(v_k_1535_);
lean_dec(v___x_1415_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1548_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1540_ = lean_unsigned_to_nat(3u);
v___x_1541_ = lean_unsigned_to_nat(1u);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 3, v_r_1515_);
lean_ctor_set(v___x_1538_, 2, v_v_1408_);
lean_ctor_set(v___x_1538_, 1, v_k_1407_);
lean_ctor_set(v___x_1538_, 0, v___x_1541_);
v___x_1543_ = v___x_1538_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v_r_1515_);
lean_ctor_set(v_reuseFailAlloc_1547_, 4, v_r_1515_);
v___x_1543_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1545_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v___x_1543_);
lean_ctor_set(v___x_1412_, 3, v_l_1514_);
lean_ctor_set(v___x_1412_, 2, v_v_1536_);
lean_ctor_set(v___x_1412_, 1, v_k_1535_);
lean_ctor_set(v___x_1412_, 0, v___x_1540_);
v___x_1545_ = v___x_1412_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_k_1535_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_v_1536_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v_l_1514_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
}
else
{
lean_object* v_r_1552_; 
v_r_1552_ = lean_ctor_get(v___x_1415_, 4);
lean_inc(v_r_1552_);
if (lean_obj_tag(v_r_1552_) == 0)
{
lean_object* v_k_1553_; lean_object* v_v_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1578_; 
lean_inc(v_l_1514_);
v_k_1553_ = lean_ctor_get(v___x_1415_, 1);
v_v_1554_ = lean_ctor_get(v___x_1415_, 2);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; lean_object* v_unused_1580_; lean_object* v_unused_1581_; 
v_unused_1579_ = lean_ctor_get(v___x_1415_, 4);
lean_dec(v_unused_1579_);
v_unused_1580_ = lean_ctor_get(v___x_1415_, 3);
lean_dec(v_unused_1580_);
v_unused_1581_ = lean_ctor_get(v___x_1415_, 0);
lean_dec(v_unused_1581_);
v___x_1556_ = v___x_1415_;
v_isShared_1557_ = v_isSharedCheck_1578_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_v_1554_);
lean_inc(v_k_1553_);
lean_dec(v___x_1415_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1578_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v_k_1558_; lean_object* v_v_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1574_; 
v_k_1558_ = lean_ctor_get(v_r_1552_, 1);
v_v_1559_ = lean_ctor_get(v_r_1552_, 2);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_r_1552_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; lean_object* v_unused_1576_; lean_object* v_unused_1577_; 
v_unused_1575_ = lean_ctor_get(v_r_1552_, 4);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_r_1552_, 3);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v_r_1552_, 0);
lean_dec(v_unused_1577_);
v___x_1561_ = v_r_1552_;
v_isShared_1562_ = v_isSharedCheck_1574_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_v_1559_);
lean_inc(v_k_1558_);
lean_dec(v_r_1552_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1574_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1563_ = lean_unsigned_to_nat(3u);
v___x_1564_ = lean_unsigned_to_nat(1u);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 4, v_l_1514_);
lean_ctor_set(v___x_1561_, 3, v_l_1514_);
lean_ctor_set(v___x_1561_, 2, v_v_1554_);
lean_ctor_set(v___x_1561_, 1, v_k_1553_);
lean_ctor_set(v___x_1561_, 0, v___x_1564_);
v___x_1566_ = v___x_1561_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_k_1553_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v_v_1554_);
lean_ctor_set(v_reuseFailAlloc_1573_, 3, v_l_1514_);
lean_ctor_set(v_reuseFailAlloc_1573_, 4, v_l_1514_);
v___x_1566_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1568_; 
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 4, v_l_1514_);
lean_ctor_set(v___x_1556_, 2, v_v_1408_);
lean_ctor_set(v___x_1556_, 1, v_k_1407_);
lean_ctor_set(v___x_1556_, 0, v___x_1564_);
v___x_1568_ = v___x_1556_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v_l_1514_);
lean_ctor_set(v_reuseFailAlloc_1572_, 4, v_l_1514_);
v___x_1568_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1570_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v___x_1568_);
lean_ctor_set(v___x_1412_, 3, v___x_1566_);
lean_ctor_set(v___x_1412_, 2, v_v_1559_);
lean_ctor_set(v___x_1412_, 1, v_k_1558_);
lean_ctor_set(v___x_1412_, 0, v___x_1563_);
v___x_1570_ = v___x_1412_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_k_1558_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_v_1559_);
lean_ctor_set(v_reuseFailAlloc_1571_, 3, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1571_, 4, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1582_ = lean_unsigned_to_nat(2u);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v_r_1552_);
lean_ctor_set(v___x_1412_, 3, v___x_1415_);
lean_ctor_set(v___x_1412_, 0, v___x_1582_);
v___x_1584_ = v___x_1412_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v_r_1552_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1586_ = lean_unsigned_to_nat(1u);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v___x_1415_);
lean_ctor_set(v___x_1412_, 3, v___x_1415_);
lean_ctor_set(v___x_1412_, 0, v___x_1586_);
v___x_1588_ = v___x_1412_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v___x_1415_);
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
case 1:
{
lean_object* v___x_1591_; 
lean_dec(v_v_1408_);
lean_dec(v_k_1407_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 2, v_v_1404_);
lean_ctor_set(v___x_1412_, 1, v_k_1403_);
v___x_1591_ = v___x_1412_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_size_1406_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_k_1403_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_v_1404_);
lean_ctor_set(v_reuseFailAlloc_1592_, 3, v_l_1409_);
lean_ctor_set(v_reuseFailAlloc_1592_, 4, v_r_1410_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
default: 
{
lean_object* v___x_1593_; 
lean_dec(v_size_1406_);
v___x_1593_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1403_, v_v_1404_, v_r_1410_);
if (lean_obj_tag(v_l_1409_) == 0)
{
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_size_1594_; lean_object* v_size_1595_; lean_object* v_k_1596_; lean_object* v_v_1597_; lean_object* v_l_1598_; lean_object* v_r_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v_size_1594_ = lean_ctor_get(v_l_1409_, 0);
v_size_1595_ = lean_ctor_get(v___x_1593_, 0);
v_k_1596_ = lean_ctor_get(v___x_1593_, 1);
v_v_1597_ = lean_ctor_get(v___x_1593_, 2);
v_l_1598_ = lean_ctor_get(v___x_1593_, 3);
lean_inc(v_l_1598_);
v_r_1599_ = lean_ctor_get(v___x_1593_, 4);
v___x_1600_ = lean_unsigned_to_nat(3u);
v___x_1601_ = lean_nat_mul(v___x_1600_, v_size_1594_);
v___x_1602_ = lean_nat_dec_lt(v___x_1601_, v_size_1595_);
lean_dec(v___x_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
lean_dec(v_l_1598_);
v___x_1603_ = lean_unsigned_to_nat(1u);
v___x_1604_ = lean_nat_add(v___x_1603_, v_size_1594_);
v___x_1605_ = lean_nat_add(v___x_1604_, v_size_1595_);
lean_dec(v___x_1604_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v___x_1593_);
lean_ctor_set(v___x_1412_, 0, v___x_1605_);
v___x_1607_ = v___x_1412_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v_l_1409_);
lean_ctor_set(v_reuseFailAlloc_1608_, 4, v___x_1593_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
else
{
lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1678_; 
lean_inc(v_r_1599_);
lean_inc(v_v_1597_);
lean_inc(v_k_1596_);
lean_inc(v_size_1595_);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1678_ == 0)
{
lean_object* v_unused_1679_; lean_object* v_unused_1680_; lean_object* v_unused_1681_; lean_object* v_unused_1682_; lean_object* v_unused_1683_; 
v_unused_1679_ = lean_ctor_get(v___x_1593_, 4);
lean_dec(v_unused_1679_);
v_unused_1680_ = lean_ctor_get(v___x_1593_, 3);
lean_dec(v_unused_1680_);
v_unused_1681_ = lean_ctor_get(v___x_1593_, 2);
lean_dec(v_unused_1681_);
v_unused_1682_ = lean_ctor_get(v___x_1593_, 1);
lean_dec(v_unused_1682_);
v_unused_1683_ = lean_ctor_get(v___x_1593_, 0);
lean_dec(v_unused_1683_);
v___x_1610_ = v___x_1593_;
v_isShared_1611_ = v_isSharedCheck_1678_;
goto v_resetjp_1609_;
}
else
{
lean_dec(v___x_1593_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1678_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
if (lean_obj_tag(v_l_1598_) == 0)
{
if (lean_obj_tag(v_r_1599_) == 0)
{
lean_object* v_size_1612_; lean_object* v_k_1613_; lean_object* v_v_1614_; lean_object* v_l_1615_; lean_object* v_r_1616_; lean_object* v_size_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v_size_1612_ = lean_ctor_get(v_l_1598_, 0);
v_k_1613_ = lean_ctor_get(v_l_1598_, 1);
v_v_1614_ = lean_ctor_get(v_l_1598_, 2);
v_l_1615_ = lean_ctor_get(v_l_1598_, 3);
v_r_1616_ = lean_ctor_get(v_l_1598_, 4);
v_size_1617_ = lean_ctor_get(v_r_1599_, 0);
v___x_1618_ = lean_unsigned_to_nat(2u);
v___x_1619_ = lean_nat_mul(v___x_1618_, v_size_1617_);
v___x_1620_ = lean_nat_dec_lt(v_size_1612_, v___x_1619_);
lean_dec(v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1649_; 
lean_inc(v_r_1616_);
lean_inc(v_l_1615_);
lean_inc(v_v_1614_);
lean_inc(v_k_1613_);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_l_1598_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; lean_object* v_unused_1651_; lean_object* v_unused_1652_; lean_object* v_unused_1653_; lean_object* v_unused_1654_; 
v_unused_1650_ = lean_ctor_get(v_l_1598_, 4);
lean_dec(v_unused_1650_);
v_unused_1651_ = lean_ctor_get(v_l_1598_, 3);
lean_dec(v_unused_1651_);
v_unused_1652_ = lean_ctor_get(v_l_1598_, 2);
lean_dec(v_unused_1652_);
v_unused_1653_ = lean_ctor_get(v_l_1598_, 1);
lean_dec(v_unused_1653_);
v_unused_1654_ = lean_ctor_get(v_l_1598_, 0);
lean_dec(v_unused_1654_);
v___x_1622_ = v_l_1598_;
v_isShared_1623_ = v_isSharedCheck_1649_;
goto v_resetjp_1621_;
}
else
{
lean_dec(v_l_1598_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1649_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1639_; 
v___x_1624_ = lean_unsigned_to_nat(1u);
v___x_1625_ = lean_nat_add(v___x_1624_, v_size_1594_);
v___x_1626_ = lean_nat_add(v___x_1625_, v_size_1595_);
lean_dec(v_size_1595_);
if (lean_obj_tag(v_l_1615_) == 0)
{
lean_object* v_size_1647_; 
v_size_1647_ = lean_ctor_get(v_l_1615_, 0);
lean_inc(v_size_1647_);
v___y_1639_ = v_size_1647_;
goto v___jp_1638_;
}
else
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_unsigned_to_nat(0u);
v___y_1639_ = v___x_1648_;
goto v___jp_1638_;
}
v___jp_1627_:
{
lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1631_ = lean_nat_add(v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec(v___y_1629_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 4, v_r_1599_);
lean_ctor_set(v___x_1622_, 3, v_r_1616_);
lean_ctor_set(v___x_1622_, 2, v_v_1597_);
lean_ctor_set(v___x_1622_, 1, v_k_1596_);
lean_ctor_set(v___x_1622_, 0, v___x_1631_);
v___x_1633_ = v___x_1622_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_k_1596_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_v_1597_);
lean_ctor_set(v_reuseFailAlloc_1637_, 3, v_r_1616_);
lean_ctor_set(v_reuseFailAlloc_1637_, 4, v_r_1599_);
v___x_1633_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1635_; 
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 4, v___x_1633_);
lean_ctor_set(v___x_1610_, 3, v___y_1628_);
lean_ctor_set(v___x_1610_, 2, v_v_1614_);
lean_ctor_set(v___x_1610_, 1, v_k_1613_);
lean_ctor_set(v___x_1610_, 0, v___x_1626_);
v___x_1635_ = v___x_1610_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_k_1613_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_v_1614_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v___y_1628_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
v___jp_1638_:
{
lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1640_ = lean_nat_add(v___x_1625_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec(v___x_1625_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v_l_1615_);
lean_ctor_set(v___x_1412_, 0, v___x_1640_);
v___x_1642_ = v___x_1412_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1646_, 3, v_l_1409_);
lean_ctor_set(v_reuseFailAlloc_1646_, 4, v_l_1615_);
v___x_1642_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_nat_add(v___x_1624_, v_size_1617_);
if (lean_obj_tag(v_r_1616_) == 0)
{
lean_object* v_size_1644_; 
v_size_1644_ = lean_ctor_get(v_r_1616_, 0);
lean_inc(v_size_1644_);
v___y_1628_ = v___x_1642_;
v___y_1629_ = v___x_1643_;
v___y_1630_ = v_size_1644_;
goto v___jp_1627_;
}
else
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_unsigned_to_nat(0u);
v___y_1628_ = v___x_1642_;
v___y_1629_ = v___x_1643_;
v___y_1630_ = v___x_1645_;
goto v___jp_1627_;
}
}
}
}
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1660_; 
lean_del_object(v___x_1412_);
v___x_1655_ = lean_unsigned_to_nat(1u);
v___x_1656_ = lean_nat_add(v___x_1655_, v_size_1594_);
v___x_1657_ = lean_nat_add(v___x_1656_, v_size_1595_);
lean_dec(v_size_1595_);
v___x_1658_ = lean_nat_add(v___x_1656_, v_size_1612_);
lean_dec(v___x_1656_);
lean_inc_ref(v_l_1409_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 4, v_l_1598_);
lean_ctor_set(v___x_1610_, 3, v_l_1409_);
lean_ctor_set(v___x_1610_, 2, v_v_1408_);
lean_ctor_set(v___x_1610_, 1, v_k_1407_);
lean_ctor_set(v___x_1610_, 0, v___x_1658_);
v___x_1660_ = v___x_1610_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1658_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1673_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1673_, 3, v_l_1409_);
lean_ctor_set(v_reuseFailAlloc_1673_, 4, v_l_1598_);
v___x_1660_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
v_isSharedCheck_1667_ = !lean_is_exclusive(v_l_1409_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; lean_object* v_unused_1669_; lean_object* v_unused_1670_; lean_object* v_unused_1671_; lean_object* v_unused_1672_; 
v_unused_1668_ = lean_ctor_get(v_l_1409_, 4);
lean_dec(v_unused_1668_);
v_unused_1669_ = lean_ctor_get(v_l_1409_, 3);
lean_dec(v_unused_1669_);
v_unused_1670_ = lean_ctor_get(v_l_1409_, 2);
lean_dec(v_unused_1670_);
v_unused_1671_ = lean_ctor_get(v_l_1409_, 1);
lean_dec(v_unused_1671_);
v_unused_1672_ = lean_ctor_get(v_l_1409_, 0);
lean_dec(v_unused_1672_);
v___x_1662_ = v_l_1409_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_dec(v_l_1409_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 4, v_r_1599_);
lean_ctor_set(v___x_1662_, 3, v___x_1660_);
lean_ctor_set(v___x_1662_, 2, v_v_1597_);
lean_ctor_set(v___x_1662_, 1, v_k_1596_);
lean_ctor_set(v___x_1662_, 0, v___x_1657_);
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_k_1596_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v_v_1597_);
lean_ctor_set(v_reuseFailAlloc_1666_, 3, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1666_, 4, v_r_1599_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec_ref_known(v_l_1598_, 5);
lean_del_object(v___x_1610_);
lean_dec(v_v_1597_);
lean_dec(v_k_1596_);
lean_dec(v_size_1595_);
lean_dec_ref_known(v_l_1409_, 5);
lean_del_object(v___x_1412_);
lean_dec(v_v_1408_);
lean_dec(v_k_1407_);
v___x_1674_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7);
v___x_1675_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1674_);
return v___x_1675_;
}
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_del_object(v___x_1610_);
lean_dec(v_r_1599_);
lean_dec(v_v_1597_);
lean_dec(v_k_1596_);
lean_dec(v_size_1595_);
lean_dec_ref_known(v_l_1409_, 5);
lean_del_object(v___x_1412_);
lean_dec(v_v_1408_);
lean_dec(v_k_1407_);
v___x_1676_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8);
v___x_1677_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1676_);
return v___x_1677_;
}
}
}
}
else
{
lean_object* v_size_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v_size_1684_ = lean_ctor_get(v_l_1409_, 0);
v___x_1685_ = lean_unsigned_to_nat(1u);
v___x_1686_ = lean_nat_add(v___x_1685_, v_size_1684_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v___x_1593_);
lean_ctor_set(v___x_1412_, 0, v___x_1686_);
v___x_1688_ = v___x_1412_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1689_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1689_, 3, v_l_1409_);
lean_ctor_set(v_reuseFailAlloc_1689_, 4, v___x_1593_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
else
{
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_l_1690_; 
v_l_1690_ = lean_ctor_get(v___x_1593_, 3);
lean_inc(v_l_1690_);
if (lean_obj_tag(v_l_1690_) == 0)
{
lean_object* v_r_1691_; 
v_r_1691_ = lean_ctor_get(v___x_1593_, 4);
lean_inc(v_r_1691_);
if (lean_obj_tag(v_r_1691_) == 0)
{
lean_object* v_size_1692_; lean_object* v_k_1693_; lean_object* v_v_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1708_; 
v_size_1692_ = lean_ctor_get(v___x_1593_, 0);
v_k_1693_ = lean_ctor_get(v___x_1593_, 1);
v_v_1694_ = lean_ctor_get(v___x_1593_, 2);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; lean_object* v_unused_1710_; 
v_unused_1709_ = lean_ctor_get(v___x_1593_, 4);
lean_dec(v_unused_1709_);
v_unused_1710_ = lean_ctor_get(v___x_1593_, 3);
lean_dec(v_unused_1710_);
v___x_1696_ = v___x_1593_;
v_isShared_1697_ = v_isSharedCheck_1708_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_v_1694_);
lean_inc(v_k_1693_);
lean_inc(v_size_1692_);
lean_dec(v___x_1593_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1708_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v_size_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
v_size_1698_ = lean_ctor_get(v_l_1690_, 0);
v___x_1699_ = lean_unsigned_to_nat(1u);
v___x_1700_ = lean_nat_add(v___x_1699_, v_size_1692_);
lean_dec(v_size_1692_);
v___x_1701_ = lean_nat_add(v___x_1699_, v_size_1698_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 4, v_l_1690_);
lean_ctor_set(v___x_1696_, 3, v_l_1409_);
lean_ctor_set(v___x_1696_, 2, v_v_1408_);
lean_ctor_set(v___x_1696_, 1, v_k_1407_);
lean_ctor_set(v___x_1696_, 0, v___x_1701_);
v___x_1703_ = v___x_1696_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1701_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_l_1409_);
lean_ctor_set(v_reuseFailAlloc_1707_, 4, v_l_1690_);
v___x_1703_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1705_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v_r_1691_);
lean_ctor_set(v___x_1412_, 3, v___x_1703_);
lean_ctor_set(v___x_1412_, 2, v_v_1694_);
lean_ctor_set(v___x_1412_, 1, v_k_1693_);
lean_ctor_set(v___x_1412_, 0, v___x_1700_);
v___x_1705_ = v___x_1412_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_k_1693_);
lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_v_1694_);
lean_ctor_set(v_reuseFailAlloc_1706_, 3, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1706_, 4, v_r_1691_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
else
{
lean_object* v_k_1711_; lean_object* v_v_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1736_; 
v_k_1711_ = lean_ctor_get(v___x_1593_, 1);
v_v_1712_ = lean_ctor_get(v___x_1593_, 2);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; lean_object* v_unused_1738_; lean_object* v_unused_1739_; 
v_unused_1737_ = lean_ctor_get(v___x_1593_, 4);
lean_dec(v_unused_1737_);
v_unused_1738_ = lean_ctor_get(v___x_1593_, 3);
lean_dec(v_unused_1738_);
v_unused_1739_ = lean_ctor_get(v___x_1593_, 0);
lean_dec(v_unused_1739_);
v___x_1714_ = v___x_1593_;
v_isShared_1715_ = v_isSharedCheck_1736_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_v_1712_);
lean_inc(v_k_1711_);
lean_dec(v___x_1593_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1736_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v_k_1716_; lean_object* v_v_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1732_; 
v_k_1716_ = lean_ctor_get(v_l_1690_, 1);
v_v_1717_ = lean_ctor_get(v_l_1690_, 2);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_l_1690_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; lean_object* v_unused_1734_; lean_object* v_unused_1735_; 
v_unused_1733_ = lean_ctor_get(v_l_1690_, 4);
lean_dec(v_unused_1733_);
v_unused_1734_ = lean_ctor_get(v_l_1690_, 3);
lean_dec(v_unused_1734_);
v_unused_1735_ = lean_ctor_get(v_l_1690_, 0);
lean_dec(v_unused_1735_);
v___x_1719_ = v_l_1690_;
v_isShared_1720_ = v_isSharedCheck_1732_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_v_1717_);
lean_inc(v_k_1716_);
lean_dec(v_l_1690_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1732_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1721_ = lean_unsigned_to_nat(3u);
v___x_1722_ = lean_unsigned_to_nat(1u);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 4, v_r_1691_);
lean_ctor_set(v___x_1719_, 3, v_r_1691_);
lean_ctor_set(v___x_1719_, 2, v_v_1408_);
lean_ctor_set(v___x_1719_, 1, v_k_1407_);
lean_ctor_set(v___x_1719_, 0, v___x_1722_);
v___x_1724_ = v___x_1719_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1731_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1731_, 3, v_r_1691_);
lean_ctor_set(v_reuseFailAlloc_1731_, 4, v_r_1691_);
v___x_1724_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1726_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 3, v_r_1691_);
lean_ctor_set(v___x_1714_, 0, v___x_1722_);
v___x_1726_ = v___x_1714_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_k_1711_);
lean_ctor_set(v_reuseFailAlloc_1730_, 2, v_v_1712_);
lean_ctor_set(v_reuseFailAlloc_1730_, 3, v_r_1691_);
lean_ctor_set(v_reuseFailAlloc_1730_, 4, v_r_1691_);
v___x_1726_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
lean_object* v___x_1728_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v___x_1726_);
lean_ctor_set(v___x_1412_, 3, v___x_1724_);
lean_ctor_set(v___x_1412_, 2, v_v_1717_);
lean_ctor_set(v___x_1412_, 1, v_k_1716_);
lean_ctor_set(v___x_1412_, 0, v___x_1721_);
v___x_1728_ = v___x_1412_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_k_1716_);
lean_ctor_set(v_reuseFailAlloc_1729_, 2, v_v_1717_);
lean_ctor_set(v_reuseFailAlloc_1729_, 3, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1729_, 4, v___x_1726_);
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
}
}
}
else
{
lean_object* v_r_1740_; 
v_r_1740_ = lean_ctor_get(v___x_1593_, 4);
lean_inc(v_r_1740_);
if (lean_obj_tag(v_r_1740_) == 0)
{
lean_object* v_k_1741_; lean_object* v_v_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1754_; 
v_k_1741_ = lean_ctor_get(v___x_1593_, 1);
v_v_1742_ = lean_ctor_get(v___x_1593_, 2);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; lean_object* v_unused_1756_; lean_object* v_unused_1757_; 
v_unused_1755_ = lean_ctor_get(v___x_1593_, 4);
lean_dec(v_unused_1755_);
v_unused_1756_ = lean_ctor_get(v___x_1593_, 3);
lean_dec(v_unused_1756_);
v_unused_1757_ = lean_ctor_get(v___x_1593_, 0);
lean_dec(v_unused_1757_);
v___x_1744_ = v___x_1593_;
v_isShared_1745_ = v_isSharedCheck_1754_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_v_1742_);
lean_inc(v_k_1741_);
lean_dec(v___x_1593_);
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
lean_ctor_set(v___x_1744_, 4, v_l_1690_);
lean_ctor_set(v___x_1744_, 2, v_v_1408_);
lean_ctor_set(v___x_1744_, 1, v_k_1407_);
lean_ctor_set(v___x_1744_, 0, v___x_1747_);
v___x_1749_ = v___x_1744_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1753_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1753_, 3, v_l_1690_);
lean_ctor_set(v_reuseFailAlloc_1753_, 4, v_l_1690_);
v___x_1749_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1751_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v_r_1740_);
lean_ctor_set(v___x_1412_, 3, v___x_1749_);
lean_ctor_set(v___x_1412_, 2, v_v_1742_);
lean_ctor_set(v___x_1412_, 1, v_k_1741_);
lean_ctor_set(v___x_1412_, 0, v___x_1746_);
v___x_1751_ = v___x_1412_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1746_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_k_1741_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_v_1742_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1752_, 4, v_r_1740_);
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
else
{
lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1758_ = lean_unsigned_to_nat(2u);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v___x_1593_);
lean_ctor_set(v___x_1412_, 3, v_r_1740_);
lean_ctor_set(v___x_1412_, 0, v___x_1758_);
v___x_1760_ = v___x_1412_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1761_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1761_, 3, v_r_1740_);
lean_ctor_set(v_reuseFailAlloc_1761_, 4, v___x_1593_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = lean_unsigned_to_nat(1u);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v___x_1593_);
lean_ctor_set(v___x_1412_, 3, v___x_1593_);
lean_ctor_set(v___x_1412_, 0, v___x_1762_);
v___x_1764_ = v___x_1412_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1765_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1765_, 3, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1765_, 4, v___x_1593_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = lean_unsigned_to_nat(1u);
v___x_1768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
lean_ctor_set(v___x_1768_, 1, v_k_1403_);
lean_ctor_set(v___x_1768_, 2, v_v_1404_);
lean_ctor_set(v___x_1768_, 3, v_t_1405_);
lean_ctor_set(v___x_1768_, 4, v_t_1405_);
return v___x_1768_;
}
}
}
static lean_object* _init_l_Lean_Json_setObjVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1771_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__1));
v___x_1772_ = lean_unsigned_to_nat(21u);
v___x_1773_ = lean_unsigned_to_nat(290u);
v___x_1774_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__0));
v___x_1775_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_1776_ = l_mkPanicMessageWithDecl(v___x_1775_, v___x_1774_, v___x_1773_, v___x_1772_, v___x_1771_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjVal_x21(lean_object* v_x_1777_, lean_object* v_x_1778_, lean_object* v_x_1779_){
_start:
{
if (lean_obj_tag(v_x_1777_) == 5)
{
lean_object* v_kvPairs_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1788_; 
v_kvPairs_1780_ = lean_ctor_get(v_x_1777_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_x_1777_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1782_ = v_x_1777_;
v_isShared_1783_ = v_isSharedCheck_1788_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_kvPairs_1780_);
lean_dec(v_x_1777_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1788_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1784_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_x_1778_, v_x_1779_, v_kvPairs_1780_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v___x_1784_);
v___x_1786_ = v___x_1782_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec(v_x_1779_);
lean_dec_ref(v_x_1778_);
lean_dec(v_x_1777_);
v___x_1789_ = lean_obj_once(&l_Lean_Json_setObjVal_x21___closed__2, &l_Lean_Json_setObjVal_x21___closed__2_once, _init_l_Lean_Json_setObjVal_x21___closed__2);
v___x_1790_ = l_panic___at___00Lean_Json_setObjVal_x21_spec__1(v___x_1789_);
return v___x_1790_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0(lean_object* v_00_u03b2_1791_, lean_object* v_msg_1792_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v_msg_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0(lean_object* v_00_u03b2_1794_, lean_object* v_k_1795_, lean_object* v_v_1796_, lean_object* v_t_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1795_, v_v_1796_, v_t_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(lean_object* v_init_1799_, lean_object* v_x_1800_){
_start:
{
if (lean_obj_tag(v_x_1800_) == 0)
{
lean_object* v_k_1801_; lean_object* v_v_1802_; lean_object* v_l_1803_; lean_object* v_r_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v_k_1801_ = lean_ctor_get(v_x_1800_, 1);
lean_inc(v_k_1801_);
v_v_1802_ = lean_ctor_get(v_x_1800_, 2);
lean_inc(v_v_1802_);
v_l_1803_ = lean_ctor_get(v_x_1800_, 3);
lean_inc(v_l_1803_);
v_r_1804_ = lean_ctor_get(v_x_1800_, 4);
lean_inc(v_r_1804_);
lean_dec_ref_known(v_x_1800_, 5);
v___x_1805_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1799_, v_l_1803_);
v___x_1806_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1801_, v_v_1802_, v___x_1805_);
v_init_1799_ = v___x_1806_;
v_x_1800_ = v_r_1804_;
goto _start;
}
else
{
return v_init_1799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mergeObj(lean_object* v_x_1808_, lean_object* v_x_1809_){
_start:
{
if (lean_obj_tag(v_x_1808_) == 5)
{
if (lean_obj_tag(v_x_1809_) == 5)
{
lean_object* v_kvPairs_1810_; lean_object* v_kvPairs_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1819_; 
v_kvPairs_1810_ = lean_ctor_get(v_x_1808_, 0);
lean_inc(v_kvPairs_1810_);
lean_dec_ref_known(v_x_1808_, 1);
v_kvPairs_1811_ = lean_ctor_get(v_x_1809_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_x_1809_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1813_ = v_x_1809_;
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_kvPairs_1811_);
lean_dec(v_x_1809_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_kvPairs_1810_, v_kvPairs_1811_);
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
lean_dec_ref_known(v_x_1808_, 1);
return v_x_1809_;
}
}
else
{
lean_dec(v_x_1808_);
return v_x_1809_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0(lean_object* v_init_1820_, lean_object* v_t_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1820_, v_t_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___impl(lean_object* v_x_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_obj_tag_nat(v_x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___impl___boxed(lean_object* v_x_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_Json_Structured_ctorIdx___impl(v_x_1825_);
lean_dec_ref(v_x_1825_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___redArg(lean_object* v_t_1827_, lean_object* v_k_1828_){
_start:
{
if (lean_obj_tag(v_t_1827_) == 0)
{
lean_object* v_elems_1829_; lean_object* v___x_1830_; 
v_elems_1829_ = lean_ctor_get(v_t_1827_, 0);
lean_inc_ref(v_elems_1829_);
lean_dec_ref_known(v_t_1827_, 1);
v___x_1830_ = lean_apply_1(v_k_1828_, v_elems_1829_);
return v___x_1830_;
}
else
{
lean_object* v_kvPairs_1831_; lean_object* v___x_1832_; 
v_kvPairs_1831_ = lean_ctor_get(v_t_1827_, 0);
lean_inc(v_kvPairs_1831_);
lean_dec_ref_known(v_t_1827_, 1);
v___x_1832_ = lean_apply_1(v_k_1828_, v_kvPairs_1831_);
return v___x_1832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim(lean_object* v_motive_1833_, lean_object* v_ctorIdx_1834_, lean_object* v_t_1835_, lean_object* v_h_1836_, lean_object* v_k_1837_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1835_, v_k_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___boxed(lean_object* v_motive_1839_, lean_object* v_ctorIdx_1840_, lean_object* v_t_1841_, lean_object* v_h_1842_, lean_object* v_k_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Json_Structured_ctorElim(v_motive_1839_, v_ctorIdx_1840_, v_t_1841_, v_h_1842_, v_k_1843_);
lean_dec(v_ctorIdx_1840_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim___redArg(lean_object* v_t_1845_, lean_object* v_arr_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1845_, v_arr_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim(lean_object* v_motive_1848_, lean_object* v_t_1849_, lean_object* v_h_1850_, lean_object* v_arr_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1849_, v_arr_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim___redArg(lean_object* v_t_1853_, lean_object* v_obj_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1853_, v_obj_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim(lean_object* v_motive_1856_, lean_object* v_t_1857_, lean_object* v_h_1858_, lean_object* v_obj_1859_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1857_, v_obj_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeArrayStructured___lam__0(lean_object* v_elems_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v_elems_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeRawStringStructured___lam__0(lean_object* v_kvPairs_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1866_, 0, v_kvPairs_1865_);
return v___x_1866_;
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
