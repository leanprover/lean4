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
static const lean_string_object l_Lean_JsonNumber_toString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "0"};
static const lean_object* l_Lean_JsonNumber_toString___closed__5 = (const lean_object*)&l_Lean_JsonNumber_toString___closed__5_value;
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
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toString(lean_object* v_x_227_){
_start:
{
lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v_mantissa_238_; lean_object* v_exponent_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_276_; uint8_t v___x_285_; 
v_mantissa_238_ = lean_ctor_get(v_x_227_, 0);
lean_inc(v_mantissa_238_);
v_exponent_239_ = lean_ctor_get(v_x_227_, 1);
lean_inc(v_exponent_239_);
lean_dec_ref(v_x_227_);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_285_ = lean_int_dec_eq(v_mantissa_238_, v___x_241_);
if (v___x_285_ == 0)
{
uint8_t v___x_286_; 
v___x_286_ = lean_nat_dec_eq(v_exponent_239_, v___x_240_);
if (v___x_286_ == 0)
{
uint8_t v___x_287_; 
v___x_287_ = lean_int_dec_le(v___x_241_, v_mantissa_238_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; 
v___x_288_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__4));
v___y_276_ = v___x_288_;
goto v___jp_275_;
}
else
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_276_ = v___x_289_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_290_; 
lean_dec(v_exponent_239_);
v___x_290_ = l_Int_repr(v_mantissa_238_);
lean_dec(v_mantissa_238_);
return v___x_290_;
}
}
else
{
lean_object* v___x_291_; 
lean_dec(v_exponent_239_);
lean_dec(v_mantissa_238_);
v___x_291_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__5));
return v___x_291_;
}
v___jp_228_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
lean_inc_ref(v___y_230_);
v___x_233_ = lean_string_append(v___y_230_, v___y_229_);
lean_dec_ref(v___y_229_);
v___x_234_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__0));
v___x_235_ = lean_string_append(v___x_233_, v___x_234_);
v___x_236_ = lean_string_append(v___x_235_, v___y_231_);
lean_dec_ref(v___y_231_);
v___x_237_ = lean_string_append(v___x_236_, v___y_232_);
lean_dec_ref(v___y_232_);
return v___x_237_;
}
v___jp_242_:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v_e_254_; lean_object* v_right_255_; uint8_t v___x_256_; 
v___x_248_ = lean_nat_add(v___y_246_, v___y_244_);
lean_dec(v___y_244_);
lean_dec(v___y_246_);
v___x_249_ = l_Nat_reprFast(v___x_248_);
v___x_250_ = lean_string_utf8_byte_size(v___x_249_);
lean_inc_ref(v___x_249_);
v___x_251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_240_);
lean_ctor_set(v___x_251_, 2, v___x_250_);
v___x_252_ = lean_unsigned_to_nat(1u);
v___x_253_ = l_Substring_Raw_nextn(v___x_251_, v___x_252_, v___x_240_);
lean_dec_ref_known(v___x_251_, 3);
v_e_254_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(v___x_249_, v___x_253_, v___x_250_);
v_right_255_ = lean_string_utf8_extract(v___x_249_, v___x_253_, v_e_254_);
lean_dec(v_e_254_);
lean_dec(v___x_253_);
lean_dec_ref(v___x_249_);
v___x_256_ = lean_int_dec_eq(v___y_247_, v___x_241_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__1));
v___x_258_ = l_Int_repr(v___y_247_);
lean_dec(v___y_247_);
v___x_259_ = lean_string_append(v___x_257_, v___x_258_);
lean_dec_ref(v___x_258_);
v___y_229_ = v___y_243_;
v___y_230_ = v___y_245_;
v___y_231_ = v_right_255_;
v___y_232_ = v___x_259_;
goto v___jp_228_;
}
else
{
lean_object* v___x_260_; 
lean_dec(v___y_247_);
v___x_260_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_229_ = v___y_243_;
v___y_230_ = v___y_245_;
v___y_231_ = v_right_255_;
v___y_232_ = v___x_260_;
goto v___jp_228_;
}
}
v___jp_261_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v_e_x27_268_; lean_object* v___x_269_; lean_object* v_left_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_265_ = lean_unsigned_to_nat(10u);
v___x_266_ = lean_nat_abs(v___y_264_);
v___x_267_ = lean_nat_sub(v_exponent_239_, v___x_266_);
lean_dec(v___x_266_);
lean_dec(v_exponent_239_);
v_e_x27_268_ = lean_nat_pow(v___x_265_, v___x_267_);
lean_dec(v___x_267_);
v___x_269_ = lean_nat_div(v___y_263_, v_e_x27_268_);
v_left_270_ = l_Nat_reprFast(v___x_269_);
v___x_271_ = lean_nat_mod(v___y_263_, v_e_x27_268_);
lean_dec(v___y_263_);
v___x_272_ = lean_nat_dec_eq(v___x_271_, v___x_240_);
if (v___x_272_ == 0)
{
v___y_243_ = v_left_270_;
v___y_244_ = v___x_271_;
v___y_245_ = v___y_262_;
v___y_246_ = v_e_x27_268_;
v___y_247_ = v___y_264_;
goto v___jp_242_;
}
else
{
uint8_t v___x_273_; 
v___x_273_ = lean_int_dec_eq(v___y_264_, v___x_241_);
if (v___x_273_ == 0)
{
v___y_243_ = v_left_270_;
v___y_244_ = v___x_271_;
v___y_245_ = v___y_262_;
v___y_246_ = v_e_x27_268_;
v___y_247_ = v___y_264_;
goto v___jp_242_;
}
else
{
lean_object* v___x_274_; 
lean_dec(v___x_271_);
lean_dec(v_e_x27_268_);
lean_dec(v___y_264_);
lean_inc_ref(v___y_262_);
v___x_274_ = lean_string_append(v___y_262_, v_left_270_);
lean_dec_ref(v_left_270_);
return v___x_274_;
}
}
}
v___jp_275_:
{
lean_object* v_m_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v_exp_283_; uint8_t v___x_284_; 
v_m_277_ = lean_nat_abs(v_mantissa_238_);
lean_dec(v_mantissa_238_);
v___x_278_ = lean_obj_once(&l_Lean_JsonNumber_toString___closed__3, &l_Lean_JsonNumber_toString___closed__3_once, _init_l_Lean_JsonNumber_toString___closed__3);
lean_inc(v_m_277_);
v___x_279_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_m_277_);
v___x_280_ = lean_nat_to_int(v___x_279_);
v___x_281_ = lean_int_add(v___x_278_, v___x_280_);
lean_dec(v___x_280_);
lean_inc(v_exponent_239_);
v___x_282_ = lean_nat_to_int(v_exponent_239_);
v_exp_283_ = lean_int_sub(v___x_281_, v___x_282_);
lean_dec(v___x_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_int_dec_lt(v_exp_283_, v___x_241_);
if (v___x_284_ == 0)
{
lean_dec(v_exp_283_);
v___y_262_ = v___y_276_;
v___y_263_ = v_m_277_;
v___y_264_ = v___x_241_;
goto v___jp_261_;
}
else
{
v___y_262_ = v___y_276_;
v___y_263_ = v_m_277_;
v___y_264_ = v_exp_283_;
goto v___jp_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl(lean_object* v_x_292_, lean_object* v_x_293_){
_start:
{
lean_object* v_mantissa_294_; lean_object* v_exponent_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_308_; 
v_mantissa_294_ = lean_ctor_get(v_x_292_, 0);
v_exponent_295_ = lean_ctor_get(v_x_292_, 1);
v_isSharedCheck_308_ = !lean_is_exclusive(v_x_292_);
if (v_isSharedCheck_308_ == 0)
{
v___x_297_ = v_x_292_;
v_isShared_298_ = v_isSharedCheck_308_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_exponent_295_);
lean_inc(v_mantissa_294_);
lean_dec(v_x_292_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_308_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_299_ = lean_unsigned_to_nat(10u);
v___x_300_ = lean_nat_sub(v_x_293_, v_exponent_295_);
v___x_301_ = lean_nat_pow(v___x_299_, v___x_300_);
lean_dec(v___x_300_);
v___x_302_ = lean_nat_to_int(v___x_301_);
v___x_303_ = lean_int_mul(v_mantissa_294_, v___x_302_);
lean_dec(v___x_302_);
lean_dec(v_mantissa_294_);
v___x_304_ = lean_nat_sub(v_exponent_295_, v_x_293_);
lean_dec(v_exponent_295_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v___x_304_);
lean_ctor_set(v___x_297_, 0, v___x_303_);
v___x_306_ = v___x_297_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl___boxed(lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_JsonNumber_shiftl(v_x_309_, v_x_310_);
lean_dec(v_x_310_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr(lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
lean_object* v_mantissa_314_; lean_object* v_exponent_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_323_; 
v_mantissa_314_ = lean_ctor_get(v_x_312_, 0);
v_exponent_315_ = lean_ctor_get(v_x_312_, 1);
v_isSharedCheck_323_ = !lean_is_exclusive(v_x_312_);
if (v_isSharedCheck_323_ == 0)
{
v___x_317_ = v_x_312_;
v_isShared_318_ = v_isSharedCheck_323_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_exponent_315_);
lean_inc(v_mantissa_314_);
lean_dec(v_x_312_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_323_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_319_ = lean_nat_add(v_exponent_315_, v_x_313_);
lean_dec(v_exponent_315_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 1, v___x_319_);
v___x_321_ = v___x_317_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_mantissa_314_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr___boxed(lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_JsonNumber_shiftr(v_x_324_, v_x_325_);
lean_dec(v_x_325_);
return v_res_326_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__0));
v___x_335_ = lean_string_length(v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l_Lean_JsonNumber_instRepr___lam__0___closed__4, &l_Lean_JsonNumber_instRepr___lam__0___closed__4_once, _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4);
v___x_337_ = lean_nat_to_int(v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0(lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
lean_object* v_mantissa_344_; lean_object* v_exponent_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_374_; 
v_mantissa_344_ = lean_ctor_get(v_x_342_, 0);
v_exponent_345_ = lean_ctor_get(v_x_342_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_x_342_);
if (v_isSharedCheck_374_ == 0)
{
v___x_347_ = v_x_342_;
v_isShared_348_ = v_isSharedCheck_374_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_exponent_345_);
lean_inc(v_mantissa_344_);
lean_dec(v_x_342_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_374_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___y_350_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_368_ = lean_int_dec_lt(v_mantissa_344_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = l_Int_repr(v_mantissa_344_);
lean_dec(v_mantissa_344_);
v___x_370_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
v___y_350_ = v___x_370_;
goto v___jp_349_;
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = l_Int_repr(v_mantissa_344_);
lean_dec(v_mantissa_344_);
v___x_372_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
v___x_373_ = l_Repr_addAppParen(v___x_372_, v___x_366_);
v___y_350_ = v___x_373_;
goto v___jp_349_;
}
v___jp_349_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__2));
if (v_isShared_348_ == 0)
{
lean_ctor_set_tag(v___x_347_, 5);
lean_ctor_set(v___x_347_, 1, v___x_351_);
lean_ctor_set(v___x_347_, 0, v___y_350_);
v___x_353_ = v___x_347_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___y_350_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_365_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; lean_object* v___x_364_; 
v___x_354_ = l_Nat_reprFast(v_exponent_345_);
v___x_355_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
v___x_356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_353_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_obj_once(&l_Lean_JsonNumber_instRepr___lam__0___closed__5, &l_Lean_JsonNumber_instRepr___lam__0___closed__5_once, _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5);
v___x_358_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__6));
v___x_359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v___x_356_);
v___x_360_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__7));
v___x_361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_357_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = 0;
v___x_364_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*1, v___x_363_);
return v___x_364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0___boxed(lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_JsonNumber_instRepr___lam__0(v_x_375_, v_x_376_);
lean_dec(v_x_376_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0(lean_object* v_mantissa_380_, uint8_t v_exponentSign_381_, lean_object* v_decimalExponent_382_){
_start:
{
if (v_exponentSign_381_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_383_ = lean_unsigned_to_nat(10u);
v___x_384_ = lean_nat_pow(v___x_383_, v_decimalExponent_382_);
lean_dec(v_decimalExponent_382_);
v___x_385_ = lean_nat_mul(v_mantissa_380_, v___x_384_);
lean_dec(v___x_384_);
lean_dec(v_mantissa_380_);
v___x_386_ = lean_nat_to_int(v___x_385_);
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
return v___x_388_;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_nat_to_int(v_mantissa_380_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v_decimalExponent_382_);
return v___x_390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0___boxed(lean_object* v_mantissa_391_, lean_object* v_exponentSign_392_, lean_object* v_decimalExponent_393_){
_start:
{
uint8_t v_exponentSign_boxed_394_; lean_object* v_res_395_; 
v_exponentSign_boxed_394_ = lean_unbox(v_exponentSign_392_);
v_res_395_ = l_Lean_JsonNumber_instOfScientific___lam__0(v_mantissa_391_, v_exponentSign_boxed_394_, v_decimalExponent_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instNeg___lam__0(lean_object* v_jn_398_){
_start:
{
lean_object* v_mantissa_399_; lean_object* v_exponent_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_408_; 
v_mantissa_399_ = lean_ctor_get(v_jn_398_, 0);
v_exponent_400_ = lean_ctor_get(v_jn_398_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v_jn_398_);
if (v_isSharedCheck_408_ == 0)
{
v___x_402_ = v_jn_398_;
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_exponent_400_);
lean_inc(v_mantissa_399_);
lean_dec(v_jn_398_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = lean_int_neg(v_mantissa_399_);
lean_dec(v_mantissa_399_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_exponent_400_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
static lean_object* _init_l_Lean_JsonNumber_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = l_Lean_JsonNumber_fromNat(v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instInhabited(void){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_obj_once(&l_Lean_JsonNumber_instInhabited___closed__0, &l_Lean_JsonNumber_instInhabited___closed__0_once, _init_l_Lean_JsonNumber_instInhabited___closed__0);
return v___x_413_;
}
}
static double _init_l_Lean_JsonNumber_toFloat___closed__0(void){
_start:
{
lean_object* v___x_414_; uint8_t v___x_415_; lean_object* v___x_416_; double v___x_417_; 
v___x_414_ = lean_unsigned_to_nat(1u);
v___x_415_ = 1;
v___x_416_ = lean_unsigned_to_nat(10u);
v___x_417_ = l_Float_ofScientific(v___x_416_, v___x_415_, v___x_414_);
return v___x_417_;
}
}
static double _init_l_Lean_JsonNumber_toFloat___closed__1(void){
_start:
{
double v___x_418_; double v___x_419_; 
v___x_418_ = lean_float_once(&l_Lean_JsonNumber_toFloat___closed__0, &l_Lean_JsonNumber_toFloat___closed__0_once, _init_l_Lean_JsonNumber_toFloat___closed__0);
v___x_419_ = lean_float_negate(v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT double l_Lean_JsonNumber_toFloat(lean_object* v_x_420_){
_start:
{
lean_object* v_mantissa_421_; lean_object* v_exponent_422_; double v___y_424_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_mantissa_421_ = lean_ctor_get(v_x_420_, 0);
lean_inc(v_mantissa_421_);
v_exponent_422_ = lean_ctor_get(v_x_420_, 1);
lean_inc(v_exponent_422_);
lean_dec_ref(v_x_420_);
v___x_429_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_430_ = lean_int_dec_le(v___x_429_, v_mantissa_421_);
if (v___x_430_ == 0)
{
double v___x_431_; 
v___x_431_ = lean_float_once(&l_Lean_JsonNumber_toFloat___closed__1, &l_Lean_JsonNumber_toFloat___closed__1_once, _init_l_Lean_JsonNumber_toFloat___closed__1);
v___y_424_ = v___x_431_;
goto v___jp_423_;
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; double v___x_434_; 
v___x_432_ = lean_unsigned_to_nat(10u);
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = l_Float_ofScientific(v___x_432_, v___x_430_, v___x_433_);
v___y_424_ = v___x_434_;
goto v___jp_423_;
}
v___jp_423_:
{
lean_object* v___x_425_; uint8_t v___x_426_; double v___x_427_; double v___x_428_; 
v___x_425_ = lean_nat_abs(v_mantissa_421_);
lean_dec(v_mantissa_421_);
v___x_426_ = 1;
v___x_427_ = l_Float_ofScientific(v___x_425_, v___x_426_, v_exponent_422_);
v___x_428_ = lean_float_mul(v___y_424_, v___x_427_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toFloat___boxed(lean_object* v_x_435_){
_start:
{
double v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l_Lean_JsonNumber_toFloat(v_x_435_);
v_r_437_ = lean_box_float(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(lean_object* v_msg_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = l_Lean_JsonNumber_instInhabited;
v___x_440_ = lean_panic_fn_borrowed(v___x_439_, v_msg_438_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(double v_x_444_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_float_to_string(v_x_444_);
v___x_446_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v___x_445_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_447_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_448_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1));
v___x_449_ = lean_unsigned_to_nat(166u);
v___x_450_ = lean_unsigned_to_nat(12u);
v___x_451_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2));
v___x_452_ = lean_string_append(v___x_451_, v___x_445_);
lean_dec_ref(v___x_445_);
v___x_453_ = l_mkPanicMessageWithDecl(v___x_447_, v___x_448_, v___x_449_, v___x_450_, v___x_452_);
lean_dec_ref(v___x_452_);
v___x_454_ = l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(v___x_453_);
return v___x_454_;
}
else
{
lean_object* v_val_455_; lean_object* v_snd_456_; lean_object* v_fst_457_; uint8_t v___x_458_; 
lean_dec_ref(v___x_445_);
v_val_455_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_val_455_);
lean_dec_ref_known(v___x_446_, 1);
v_snd_456_ = lean_ctor_get(v_val_455_, 1);
lean_inc(v_snd_456_);
v_fst_457_ = lean_ctor_get(v_snd_456_, 0);
v___x_458_ = lean_unbox(v_fst_457_);
if (v___x_458_ == 0)
{
lean_object* v_fst_459_; lean_object* v_snd_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_472_; 
v_fst_459_ = lean_ctor_get(v_val_455_, 0);
lean_inc(v_fst_459_);
lean_dec(v_val_455_);
v_snd_460_ = lean_ctor_get(v_snd_456_, 1);
v_isSharedCheck_472_ = !lean_is_exclusive(v_snd_456_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v_snd_456_, 0);
lean_dec(v_unused_473_);
v___x_462_ = v_snd_456_;
v_isShared_463_ = v_isSharedCheck_472_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_snd_460_);
lean_dec(v_snd_456_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_472_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_464_ = lean_unsigned_to_nat(10u);
v___x_465_ = lean_nat_pow(v___x_464_, v_snd_460_);
lean_dec(v_snd_460_);
v___x_466_ = lean_nat_mul(v_fst_459_, v___x_465_);
lean_dec(v___x_465_);
lean_dec(v_fst_459_);
v___x_467_ = lean_nat_to_int(v___x_466_);
v___x_468_ = lean_unsigned_to_nat(0u);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v___x_468_);
lean_ctor_set(v___x_462_, 0, v___x_467_);
v___x_470_ = v___x_462_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
else
{
lean_object* v_fst_474_; lean_object* v_snd_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_483_; 
v_fst_474_ = lean_ctor_get(v_val_455_, 0);
lean_inc(v_fst_474_);
lean_dec(v_val_455_);
v_snd_475_ = lean_ctor_get(v_snd_456_, 1);
v_isSharedCheck_483_ = !lean_is_exclusive(v_snd_456_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v_snd_456_, 0);
lean_dec(v_unused_484_);
v___x_477_ = v_snd_456_;
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_snd_475_);
lean_dec(v_snd_456_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_479_ = lean_nat_to_int(v_fst_474_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_479_);
v___x_481_ = v___x_477_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_snd_475_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___boxed(lean_object* v_x_485_){
_start:
{
double v_x_boxed_486_; lean_object* v_res_487_; 
v_x_boxed_486_ = lean_unbox_float(v_x_485_);
lean_dec_ref(v_x_485_);
v_res_487_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_boxed_486_);
return v_res_487_;
}
}
static double _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0(void){
_start:
{
lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___x_490_; double v___x_491_; 
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = 1;
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = l_Float_ofScientific(v___x_490_, v___x_489_, v___x_488_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_obj_once(&l_Lean_JsonNumber_instInhabited___closed__0, &l_Lean_JsonNumber_instInhabited___closed__0_once, _init_l_Lean_JsonNumber_instInhabited___closed__0);
v___x_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
static double _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2(void){
_start:
{
lean_object* v___x_494_; double v___x_495_; 
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_float_of_nat(v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f(double v_x_505_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = lean_float_isnan(v_x_505_);
if (v___x_506_ == 0)
{
uint8_t v___x_507_; 
v___x_507_ = lean_float_isinf(v_x_505_);
if (v___x_507_ == 0)
{
double v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_float_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__0, &l_Lean_JsonNumber_fromFloat_x3f___closed__0_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0);
v___x_509_ = lean_float_beq(v_x_505_, v___x_508_);
if (v___x_509_ == 0)
{
uint8_t v___x_510_; 
v___x_510_ = lean_float_decLt(v_x_505_, v___x_508_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_505_);
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
else
{
double v___x_513_; lean_object* v___x_514_; lean_object* v_mantissa_515_; lean_object* v_exponent_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_525_; 
v___x_513_ = lean_float_negate(v_x_505_);
v___x_514_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v___x_513_);
v_mantissa_515_ = lean_ctor_get(v___x_514_, 0);
v_exponent_516_ = lean_ctor_get(v___x_514_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_525_ == 0)
{
v___x_518_ = v___x_514_;
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_exponent_516_);
lean_inc(v_mantissa_515_);
lean_dec(v___x_514_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = lean_int_neg(v_mantissa_515_);
lean_dec(v_mantissa_515_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_520_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_exponent_516_);
v___x_522_ = v_reuseFailAlloc_524_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; 
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
}
}
else
{
lean_object* v___x_526_; 
v___x_526_ = lean_obj_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__1, &l_Lean_JsonNumber_fromFloat_x3f___closed__1_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1);
return v___x_526_;
}
}
else
{
double v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_float_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__2, &l_Lean_JsonNumber_fromFloat_x3f___closed__2_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2);
v___x_528_ = lean_float_decLt(v___x_527_, v_x_505_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
v___x_529_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__4));
return v___x_529_;
}
else
{
lean_object* v___x_530_; 
v___x_530_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__6));
return v___x_530_;
}
}
}
else
{
lean_object* v___x_531_; 
v___x_531_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__8));
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f___boxed(lean_object* v_x_532_){
_start:
{
double v_x_boxed_533_; lean_object* v_res_534_; 
v_x_boxed_533_ = lean_unbox_float(v_x_532_);
lean_dec_ref(v_x_532_);
v_res_534_ = l_Lean_JsonNumber_fromFloat_x3f(v_x_boxed_533_);
return v_res_534_;
}
}
LEAN_EXPORT uint8_t l_Lean_strLt(lean_object* v_a_535_, lean_object* v_b_536_){
_start:
{
uint8_t v___x_537_; 
v___x_537_ = lean_string_dec_lt(v_a_535_, v_b_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_strLt___boxed(lean_object* v_a_538_, lean_object* v_b_539_){
_start:
{
uint8_t v_res_540_; lean_object* v_r_541_; 
v_res_540_ = l_Lean_strLt(v_a_538_, v_b_539_);
lean_dec_ref(v_b_539_);
lean_dec_ref(v_a_538_);
v_r_541_ = lean_box(v_res_540_);
return v_r_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx___impl(lean_object* v_x_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = lean_obj_tag_nat(v_x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx___impl___boxed(lean_object* v_x_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Json_ctorIdx___impl(v_x_544_);
lean_dec(v_x_544_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___redArg(lean_object* v_t_546_, lean_object* v_k_547_){
_start:
{
switch(lean_obj_tag(v_t_546_))
{
case 0:
{
return v_k_547_;
}
case 1:
{
uint8_t v_b_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_b_548_ = lean_ctor_get_uint8(v_t_546_, 0);
lean_dec_ref_known(v_t_546_, 0);
v___x_549_ = lean_box(v_b_548_);
v___x_550_ = lean_apply_1(v_k_547_, v___x_549_);
return v___x_550_;
}
case 5:
{
lean_object* v_kvPairs_551_; lean_object* v___x_552_; 
v_kvPairs_551_ = lean_ctor_get(v_t_546_, 0);
lean_inc(v_kvPairs_551_);
lean_dec_ref_known(v_t_546_, 1);
v___x_552_ = lean_apply_1(v_k_547_, v_kvPairs_551_);
return v___x_552_;
}
default: 
{
lean_object* v_n_553_; lean_object* v___x_554_; 
v_n_553_ = lean_ctor_get(v_t_546_, 0);
lean_inc_ref(v_n_553_);
lean_dec(v_t_546_);
v___x_554_ = lean_apply_1(v_k_547_, v_n_553_);
return v___x_554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim(lean_object* v_motive__1_555_, lean_object* v_ctorIdx_556_, lean_object* v_t_557_, lean_object* v_h_558_, lean_object* v_k_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Json_ctorElim___redArg(v_t_557_, v_k_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___boxed(lean_object* v_motive__1_561_, lean_object* v_ctorIdx_562_, lean_object* v_t_563_, lean_object* v_h_564_, lean_object* v_k_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Json_ctorElim(v_motive__1_561_, v_ctorIdx_562_, v_t_563_, v_h_564_, v_k_565_);
lean_dec(v_ctorIdx_562_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_null_elim___redArg(lean_object* v_t_567_, lean_object* v_null_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_Json_ctorElim___redArg(v_t_567_, v_null_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_null_elim(lean_object* v_motive__1_570_, lean_object* v_t_571_, lean_object* v_h_572_, lean_object* v_null_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Json_ctorElim___redArg(v_t_571_, v_null_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim___redArg(lean_object* v_t_575_, lean_object* v_bool_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_Json_ctorElim___redArg(v_t_575_, v_bool_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim(lean_object* v_motive__1_578_, lean_object* v_t_579_, lean_object* v_h_580_, lean_object* v_bool_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Json_ctorElim___redArg(v_t_579_, v_bool_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_num_elim___redArg(lean_object* v_t_583_, lean_object* v_num_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Json_ctorElim___redArg(v_t_583_, v_num_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_num_elim(lean_object* v_motive__1_586_, lean_object* v_t_587_, lean_object* v_h_588_, lean_object* v_num_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Json_ctorElim___redArg(v_t_587_, v_num_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_str_elim___redArg(lean_object* v_t_591_, lean_object* v_str_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Json_ctorElim___redArg(v_t_591_, v_str_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_str_elim(lean_object* v_motive__1_594_, lean_object* v_t_595_, lean_object* v_h_596_, lean_object* v_str_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Json_ctorElim___redArg(v_t_595_, v_str_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim___redArg(lean_object* v_t_599_, lean_object* v_arr_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Json_ctorElim___redArg(v_t_599_, v_arr_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim(lean_object* v_motive__1_602_, lean_object* v_t_603_, lean_object* v_h_604_, lean_object* v_arr_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Json_ctorElim___redArg(v_t_603_, v_arr_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim___redArg(lean_object* v_t_607_, lean_object* v_obj_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_Json_ctorElim___redArg(v_t_607_, v_obj_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim(lean_object* v_motive__1_610_, lean_object* v_t_611_, lean_object* v_h_612_, lean_object* v_obj_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_Json_ctorElim___redArg(v_t_611_, v_obj_613_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_instInhabitedJson_default(void){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_box(0);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_instInhabitedJson(void){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_box(0);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(lean_object* v_init_617_, lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_618_) == 0)
{
lean_object* v_l_619_; lean_object* v_r_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_l_619_ = lean_ctor_get(v_x_618_, 3);
v_r_620_ = lean_ctor_get(v_x_618_, 4);
v___x_621_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_617_, v_l_619_);
v___x_622_ = lean_unsigned_to_nat(1u);
v___x_623_ = lean_nat_add(v___x_621_, v___x_622_);
lean_dec(v___x_621_);
v_init_617_ = v___x_623_;
v_x_618_ = v_r_620_;
goto _start;
}
else
{
return v_init_617_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1___boxed(lean_object* v_init_625_, lean_object* v_x_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_625_, v_x_626_);
lean_dec(v_x_626_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(lean_object* v_t_628_, lean_object* v_k_629_){
_start:
{
if (lean_obj_tag(v_t_628_) == 0)
{
lean_object* v_k_630_; lean_object* v_v_631_; lean_object* v_l_632_; lean_object* v_r_633_; uint8_t v___x_634_; 
v_k_630_ = lean_ctor_get(v_t_628_, 1);
v_v_631_ = lean_ctor_get(v_t_628_, 2);
v_l_632_ = lean_ctor_get(v_t_628_, 3);
v_r_633_ = lean_ctor_get(v_t_628_, 4);
v___x_634_ = lean_string_compare(v_k_629_, v_k_630_);
switch(v___x_634_)
{
case 0:
{
v_t_628_ = v_l_632_;
goto _start;
}
case 1:
{
lean_object* v___x_636_; 
lean_inc(v_v_631_);
v___x_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_636_, 0, v_v_631_);
return v___x_636_;
}
default: 
{
v_t_628_ = v_r_633_;
goto _start;
}
}
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_box(0);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg___boxed(lean_object* v_t_639_, lean_object* v_k_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_639_, v_k_640_);
lean_dec_ref(v_k_640_);
lean_dec(v_t_639_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(lean_object* v_szA_653_, lean_object* v_szB_654_, lean_object* v_kvPairs_655_, lean_object* v_init_656_, lean_object* v_x_657_){
_start:
{
if (lean_obj_tag(v_x_657_) == 0)
{
lean_object* v_k_658_; lean_object* v_v_659_; lean_object* v_l_660_; lean_object* v_r_661_; uint8_t v___x_662_; lean_object* v___x_663_; 
v_k_658_ = lean_ctor_get(v_x_657_, 1);
v_v_659_ = lean_ctor_get(v_x_657_, 2);
v_l_660_ = lean_ctor_get(v_x_657_, 3);
v_r_661_ = lean_ctor_get(v_x_657_, 4);
v___x_662_ = lean_nat_dec_eq(v_szA_653_, v_szB_654_);
v___x_663_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_653_, v_szB_654_, v_kvPairs_655_, v_init_656_, v_l_660_);
if (lean_obj_tag(v___x_663_) == 0)
{
return v___x_663_;
}
else
{
lean_object* v___x_664_; lean_object* v___x_668_; 
lean_dec_ref_known(v___x_663_, 1);
v___x_664_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0));
v___x_668_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_655_, v_k_658_);
if (lean_obj_tag(v___x_668_) == 0)
{
goto v___jp_665_;
}
else
{
lean_object* v_val_669_; uint8_t v___x_670_; 
v_val_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_val_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_v_659_, v_val_669_);
lean_dec(v_val_669_);
if (v___x_670_ == 0)
{
goto v___jp_665_;
}
else
{
v_init_656_ = v___x_664_;
v_x_657_ = v_r_661_;
goto _start;
}
}
v___jp_665_:
{
if (v___x_662_ == 0)
{
v_init_656_ = v___x_664_;
v_x_657_ = v_r_661_;
goto _start;
}
else
{
lean_object* v___x_667_; 
v___x_667_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__3));
return v___x_667_;
}
}
}
}
else
{
lean_object* v___x_672_; 
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v_init_656_);
return v___x_672_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
switch(lean_obj_tag(v_x_673_))
{
case 0:
{
if (lean_obj_tag(v_x_674_) == 0)
{
uint8_t v___x_675_; 
v___x_675_ = 1;
return v___x_675_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = 0;
return v___x_676_;
}
}
case 1:
{
if (lean_obj_tag(v_x_674_) == 1)
{
uint8_t v_b_677_; 
v_b_677_ = lean_ctor_get_uint8(v_x_674_, 0);
if (v_b_677_ == 0)
{
uint8_t v_b_678_; 
v_b_678_ = lean_ctor_get_uint8(v_x_673_, 0);
if (v_b_678_ == 0)
{
uint8_t v___x_679_; 
v___x_679_ = 1;
return v___x_679_;
}
else
{
return v_b_677_;
}
}
else
{
uint8_t v_b_680_; 
v_b_680_ = lean_ctor_get_uint8(v_x_673_, 0);
return v_b_680_;
}
}
else
{
uint8_t v___x_681_; 
v___x_681_ = 0;
return v___x_681_;
}
}
case 2:
{
if (lean_obj_tag(v_x_674_) == 2)
{
lean_object* v_n_682_; lean_object* v_n_683_; uint8_t v___x_684_; 
v_n_682_ = lean_ctor_get(v_x_673_, 0);
v_n_683_ = lean_ctor_get(v_x_674_, 0);
v___x_684_ = l_Lean_instDecidableEqJsonNumber_decEq(v_n_682_, v_n_683_);
return v___x_684_;
}
else
{
uint8_t v___x_685_; 
v___x_685_ = 0;
return v___x_685_;
}
}
case 3:
{
if (lean_obj_tag(v_x_674_) == 3)
{
lean_object* v_s_686_; lean_object* v_s_687_; uint8_t v___x_688_; 
v_s_686_ = lean_ctor_get(v_x_673_, 0);
v_s_687_ = lean_ctor_get(v_x_674_, 0);
v___x_688_ = lean_string_dec_eq(v_s_686_, v_s_687_);
return v___x_688_;
}
else
{
uint8_t v___x_689_; 
v___x_689_ = 0;
return v___x_689_;
}
}
case 4:
{
if (lean_obj_tag(v_x_674_) == 4)
{
lean_object* v_elems_690_; lean_object* v_elems_691_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v_elems_690_ = lean_ctor_get(v_x_673_, 0);
v_elems_691_ = lean_ctor_get(v_x_674_, 0);
v___x_692_ = lean_array_get_size(v_elems_690_);
v___x_693_ = lean_array_get_size(v_elems_691_);
v___x_694_ = lean_nat_dec_eq(v___x_692_, v___x_693_);
if (v___x_694_ == 0)
{
return v___x_694_;
}
else
{
uint8_t v___x_695_; 
v___x_695_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_elems_690_, v_elems_691_, v___x_692_);
return v___x_695_;
}
}
else
{
uint8_t v___x_696_; 
v___x_696_ = 0;
return v___x_696_;
}
}
default: 
{
if (lean_obj_tag(v_x_674_) == 5)
{
lean_object* v_kvPairs_697_; lean_object* v_kvPairs_698_; lean_object* v___x_699_; lean_object* v_szA_700_; lean_object* v_szB_701_; uint8_t v___x_702_; lean_object* v___y_704_; 
v_kvPairs_697_ = lean_ctor_get(v_x_673_, 0);
v_kvPairs_698_ = lean_ctor_get(v_x_674_, 0);
v___x_699_ = lean_unsigned_to_nat(0u);
v_szA_700_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_699_, v_kvPairs_697_);
v_szB_701_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_699_, v_kvPairs_698_);
v___x_702_ = lean_nat_dec_eq(v_szA_700_, v_szB_701_);
if (v___x_702_ == 0)
{
lean_dec(v_szB_701_);
lean_dec(v_szA_700_);
return v___x_702_;
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v_a_710_; 
v___x_708_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0));
v___x_709_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_700_, v_szB_701_, v_kvPairs_698_, v___x_708_, v_kvPairs_697_);
lean_dec(v_szB_701_);
lean_dec(v_szA_700_);
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref(v___x_709_);
v___y_704_ = v_a_710_;
goto v___jp_703_;
}
v___jp_703_:
{
lean_object* v_fst_705_; 
v_fst_705_ = lean_ctor_get(v___y_704_, 0);
lean_inc(v_fst_705_);
lean_dec_ref(v___y_704_);
if (lean_obj_tag(v_fst_705_) == 0)
{
return v___x_702_;
}
else
{
lean_object* v_val_706_; uint8_t v___x_707_; 
v_val_706_ = lean_ctor_get(v_fst_705_, 0);
lean_inc(v_val_706_);
lean_dec_ref_known(v_fst_705_, 1);
v___x_707_ = lean_unbox(v_val_706_);
lean_dec(v_val_706_);
return v___x_707_;
}
}
}
else
{
uint8_t v___x_711_; 
v___x_711_ = 0;
return v___x_711_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(lean_object* v_xs_712_, lean_object* v_ys_713_, lean_object* v_x_714_){
_start:
{
lean_object* v_zero_715_; uint8_t v_isZero_716_; 
v_zero_715_ = lean_unsigned_to_nat(0u);
v_isZero_716_ = lean_nat_dec_eq(v_x_714_, v_zero_715_);
if (v_isZero_716_ == 1)
{
lean_dec(v_x_714_);
return v_isZero_716_;
}
else
{
lean_object* v_one_717_; lean_object* v_n_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v_one_717_ = lean_unsigned_to_nat(1u);
v_n_718_ = lean_nat_sub(v_x_714_, v_one_717_);
lean_dec(v_x_714_);
v___x_719_ = lean_array_fget_borrowed(v_xs_712_, v_n_718_);
v___x_720_ = lean_array_fget_borrowed(v_ys_713_, v_n_718_);
v___x_721_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v___x_719_, v___x_720_);
if (v___x_721_ == 0)
{
lean_dec(v_n_718_);
return v___x_721_;
}
else
{
v_x_714_ = v_n_718_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg___boxed(lean_object* v_xs_723_, lean_object* v_ys_724_, lean_object* v_x_725_){
_start:
{
uint8_t v_res_726_; lean_object* v_r_727_; 
v_res_726_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_723_, v_ys_724_, v_x_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_xs_723_);
v_r_727_ = lean_box(v_res_726_);
return v_r_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___boxed(lean_object* v_szA_728_, lean_object* v_szB_729_, lean_object* v_kvPairs_730_, lean_object* v_init_731_, lean_object* v_x_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_728_, v_szB_729_, v_kvPairs_730_, v_init_731_, v_x_732_);
lean_dec(v_x_732_);
lean_dec(v_kvPairs_730_);
lean_dec(v_szB_729_);
lean_dec(v_szA_728_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___boxed(lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
uint8_t v_res_736_; lean_object* v_r_737_; 
v_res_736_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_x_734_, v_x_735_);
lean_dec(v_x_735_);
lean_dec(v_x_734_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(lean_object* v_xs_738_, lean_object* v_ys_739_, lean_object* v_hsz_740_, lean_object* v_x_741_, lean_object* v_x_742_){
_start:
{
uint8_t v___x_743_; 
v___x_743_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_738_, v_ys_739_, v_x_741_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___boxed(lean_object* v_xs_744_, lean_object* v_ys_745_, lean_object* v_hsz_746_, lean_object* v_x_747_, lean_object* v_x_748_){
_start:
{
uint8_t v_res_749_; lean_object* v_r_750_; 
v_res_749_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(v_xs_744_, v_ys_745_, v_hsz_746_, v_x_747_, v_x_748_);
lean_dec_ref(v_ys_745_);
lean_dec_ref(v_xs_744_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(lean_object* v_init_751_, lean_object* v_t_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_751_, v_t_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___boxed(lean_object* v_init_754_, lean_object* v_t_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(v_init_754_, v_t_755_);
lean_dec(v_t_755_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(lean_object* v_00_u03b4_757_, lean_object* v_t_758_, lean_object* v_k_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_758_, v_k_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___boxed(lean_object* v_00_u03b4_761_, lean_object* v_t_762_, lean_object* v_k_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(v_00_u03b4_761_, v_t_762_, v_k_763_);
lean_dec_ref(v_k_763_);
lean_dec(v_t_762_);
return v_res_764_;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_instBEq___private__1(lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
uint8_t v___x_767_; 
v___x_767_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_a_765_, v_a_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instBEq___private__1___boxed(lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
uint8_t v_res_770_; lean_object* v_r_771_; 
v_res_770_ = l_Lean_Json_instBEq___private__1(v_a_768_, v_a_769_);
lean_dec(v_a_769_);
lean_dec(v_a_768_);
v_r_771_ = lean_box(v_res_770_);
return v_r_771_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(lean_object* v_as_774_, size_t v_i_775_, size_t v_stop_776_, uint64_t v_b_777_){
_start:
{
uint8_t v___x_778_; 
v___x_778_ = lean_usize_dec_eq(v_i_775_, v_stop_776_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; uint64_t v___x_780_; uint64_t v___x_781_; size_t v___x_782_; size_t v___x_783_; 
v___x_779_ = lean_array_uget_borrowed(v_as_774_, v_i_775_);
v___x_780_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v___x_779_);
v___x_781_ = lean_uint64_mix_hash(v_b_777_, v___x_780_);
v___x_782_ = ((size_t)1ULL);
v___x_783_ = lean_usize_add(v_i_775_, v___x_782_);
v_i_775_ = v___x_783_;
v_b_777_ = v___x_781_;
goto _start;
}
else
{
return v_b_777_;
}
}
}
LEAN_EXPORT uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(lean_object* v_x_785_){
_start:
{
switch(lean_obj_tag(v_x_785_))
{
case 0:
{
uint64_t v___x_786_; 
v___x_786_ = 11ULL;
return v___x_786_;
}
case 1:
{
uint8_t v_b_787_; 
v_b_787_ = lean_ctor_get_uint8(v_x_785_, 0);
if (v_b_787_ == 0)
{
uint64_t v___x_788_; 
v___x_788_ = 889925284873970544ULL;
return v___x_788_;
}
else
{
uint64_t v___x_789_; 
v___x_789_ = 7849220421742680397ULL;
return v___x_789_;
}
}
case 2:
{
lean_object* v_n_790_; uint64_t v___x_791_; uint64_t v___x_792_; uint64_t v___x_793_; 
v_n_790_ = lean_ctor_get(v_x_785_, 0);
v___x_791_ = 17ULL;
v___x_792_ = l_Lean_instHashableJsonNumber_hash(v_n_790_);
v___x_793_ = lean_uint64_mix_hash(v___x_791_, v___x_792_);
return v___x_793_;
}
case 3:
{
lean_object* v_s_794_; uint64_t v___x_795_; uint64_t v___x_796_; uint64_t v___x_797_; 
v_s_794_ = lean_ctor_get(v_x_785_, 0);
v___x_795_ = 19ULL;
v___x_796_ = lean_string_hash(v_s_794_);
v___x_797_ = lean_uint64_mix_hash(v___x_795_, v___x_796_);
return v___x_797_;
}
case 4:
{
lean_object* v_elems_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v_elems_798_ = lean_ctor_get(v_x_785_, 0);
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_array_get_size(v_elems_798_);
v___x_801_ = lean_nat_dec_lt(v___x_799_, v___x_800_);
if (v___x_801_ == 0)
{
uint64_t v___x_802_; 
v___x_802_ = 179905158410471120ULL;
return v___x_802_;
}
else
{
uint64_t v___x_803_; uint64_t v___x_804_; size_t v___x_805_; size_t v___x_806_; uint64_t v___x_807_; uint64_t v___x_808_; 
v___x_803_ = 23ULL;
v___x_804_ = 7ULL;
v___x_805_ = ((size_t)0ULL);
v___x_806_ = lean_usize_of_nat(v___x_800_);
v___x_807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_798_, v___x_805_, v___x_806_, v___x_804_);
v___x_808_ = lean_uint64_mix_hash(v___x_803_, v___x_807_);
return v___x_808_;
}
}
default: 
{
lean_object* v_kvPairs_809_; uint64_t v___x_810_; uint64_t v___x_811_; uint64_t v___x_812_; uint64_t v___x_813_; 
v_kvPairs_809_ = lean_ctor_get(v_x_785_, 0);
v___x_810_ = 29ULL;
v___x_811_ = 7ULL;
v___x_812_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v___x_811_, v_kvPairs_809_);
v___x_813_ = lean_uint64_mix_hash(v___x_810_, v___x_812_);
return v___x_813_;
}
}
}
}
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(uint64_t v_init_814_, lean_object* v_x_815_){
_start:
{
if (lean_obj_tag(v_x_815_) == 0)
{
lean_object* v_k_816_; lean_object* v_v_817_; lean_object* v_l_818_; lean_object* v_r_819_; uint64_t v___x_820_; uint64_t v___x_821_; uint64_t v___x_822_; uint64_t v___x_823_; uint64_t v___x_824_; 
v_k_816_ = lean_ctor_get(v_x_815_, 1);
v_v_817_ = lean_ctor_get(v_x_815_, 2);
v_l_818_ = lean_ctor_get(v_x_815_, 3);
v_r_819_ = lean_ctor_get(v_x_815_, 4);
v___x_820_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_814_, v_l_818_);
v___x_821_ = lean_string_hash(v_k_816_);
v___x_822_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_v_817_);
v___x_823_ = lean_uint64_mix_hash(v___x_821_, v___x_822_);
v___x_824_ = lean_uint64_mix_hash(v___x_820_, v___x_823_);
v_init_814_ = v___x_824_;
v_x_815_ = v_r_819_;
goto _start;
}
else
{
return v_init_814_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1___boxed(lean_object* v_init_826_, lean_object* v_x_827_){
_start:
{
uint64_t v_init_boxed_828_; uint64_t v_res_829_; lean_object* v_r_830_; 
v_init_boxed_828_ = lean_unbox_uint64(v_init_826_);
lean_dec_ref(v_init_826_);
v_res_829_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_boxed_828_, v_x_827_);
lean_dec(v_x_827_);
v_r_830_ = lean_box_uint64(v_res_829_);
return v_r_830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0___boxed(lean_object* v_as_831_, lean_object* v_i_832_, lean_object* v_stop_833_, lean_object* v_b_834_){
_start:
{
size_t v_i_boxed_835_; size_t v_stop_boxed_836_; uint64_t v_b_boxed_837_; uint64_t v_res_838_; lean_object* v_r_839_; 
v_i_boxed_835_ = lean_unbox_usize(v_i_832_);
lean_dec(v_i_832_);
v_stop_boxed_836_ = lean_unbox_usize(v_stop_833_);
lean_dec(v_stop_833_);
v_b_boxed_837_ = lean_unbox_uint64(v_b_834_);
lean_dec_ref(v_b_834_);
v_res_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_as_831_, v_i_boxed_835_, v_stop_boxed_836_, v_b_boxed_837_);
lean_dec_ref(v_as_831_);
v_r_839_ = lean_box_uint64(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___boxed(lean_object* v_x_840_){
_start:
{
uint64_t v_res_841_; lean_object* v_r_842_; 
v_res_841_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_x_840_);
lean_dec(v_x_840_);
v_r_842_ = lean_box_uint64(v_res_841_);
return v_r_842_;
}
}
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(uint64_t v_init_843_, lean_object* v_t_844_){
_start:
{
uint64_t v___x_845_; 
v___x_845_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_843_, v_t_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1___boxed(lean_object* v_init_846_, lean_object* v_t_847_){
_start:
{
uint64_t v_init_boxed_848_; uint64_t v_res_849_; lean_object* v_r_850_; 
v_init_boxed_848_ = lean_unbox_uint64(v_init_846_);
lean_dec_ref(v_init_846_);
v_res_849_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(v_init_boxed_848_, v_t_847_);
lean_dec(v_t_847_);
v_r_850_ = lean_box_uint64(v_res_849_);
return v_r_850_;
}
}
LEAN_EXPORT uint64_t l_Lean_Json_instHashable___private__1(lean_object* v_a_851_){
_start:
{
uint64_t v___x_852_; 
v___x_852_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_a_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instHashable___private__1___boxed(lean_object* v_a_853_){
_start:
{
uint64_t v_res_854_; lean_object* v_r_855_; 
v_res_854_ = l_Lean_Json_instHashable___private__1(v_a_853_);
lean_dec(v_a_853_);
v_r_855_ = lean_box_uint64(v_res_854_);
return v_r_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(lean_object* v_k_858_, lean_object* v_v_859_, lean_object* v_t_860_){
_start:
{
if (lean_obj_tag(v_t_860_) == 0)
{
lean_object* v_size_861_; lean_object* v_k_862_; lean_object* v_v_863_; lean_object* v_l_864_; lean_object* v_r_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_1145_; 
v_size_861_ = lean_ctor_get(v_t_860_, 0);
v_k_862_ = lean_ctor_get(v_t_860_, 1);
v_v_863_ = lean_ctor_get(v_t_860_, 2);
v_l_864_ = lean_ctor_get(v_t_860_, 3);
v_r_865_ = lean_ctor_get(v_t_860_, 4);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_t_860_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_867_ = v_t_860_;
v_isShared_868_ = v_isSharedCheck_1145_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_r_865_);
lean_inc(v_l_864_);
lean_inc(v_v_863_);
lean_inc(v_k_862_);
lean_inc(v_size_861_);
lean_dec(v_t_860_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_1145_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
uint8_t v___x_869_; 
v___x_869_ = lean_string_compare(v_k_858_, v_k_862_);
switch(v___x_869_)
{
case 0:
{
lean_object* v_impl_870_; lean_object* v___x_871_; 
lean_dec(v_size_861_);
v_impl_870_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_858_, v_v_859_, v_l_864_);
v___x_871_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_865_) == 0)
{
lean_object* v_size_872_; lean_object* v_size_873_; lean_object* v_k_874_; lean_object* v_v_875_; lean_object* v_l_876_; lean_object* v_r_877_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v_size_872_ = lean_ctor_get(v_r_865_, 0);
v_size_873_ = lean_ctor_get(v_impl_870_, 0);
v_k_874_ = lean_ctor_get(v_impl_870_, 1);
v_v_875_ = lean_ctor_get(v_impl_870_, 2);
v_l_876_ = lean_ctor_get(v_impl_870_, 3);
v_r_877_ = lean_ctor_get(v_impl_870_, 4);
lean_inc(v_r_877_);
v___x_878_ = lean_unsigned_to_nat(3u);
v___x_879_ = lean_nat_mul(v___x_878_, v_size_872_);
v___x_880_ = lean_nat_dec_lt(v___x_879_, v_size_873_);
lean_dec(v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
lean_dec(v_r_877_);
v___x_881_ = lean_nat_add(v___x_871_, v_size_873_);
v___x_882_ = lean_nat_add(v___x_881_, v_size_872_);
lean_dec(v___x_881_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 3, v_impl_870_);
lean_ctor_set(v___x_867_, 0, v___x_882_);
v___x_884_ = v___x_867_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_k_862_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_v_863_);
lean_ctor_set(v_reuseFailAlloc_885_, 3, v_impl_870_);
lean_ctor_set(v_reuseFailAlloc_885_, 4, v_r_865_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
else
{
lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_951_; 
lean_inc(v_l_876_);
lean_inc(v_v_875_);
lean_inc(v_k_874_);
lean_inc(v_size_873_);
v_isSharedCheck_951_ = !lean_is_exclusive(v_impl_870_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; lean_object* v_unused_953_; lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; 
v_unused_952_ = lean_ctor_get(v_impl_870_, 4);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_impl_870_, 3);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_impl_870_, 2);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_impl_870_, 1);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_impl_870_, 0);
lean_dec(v_unused_956_);
v___x_887_ = v_impl_870_;
v_isShared_888_ = v_isSharedCheck_951_;
goto v_resetjp_886_;
}
else
{
lean_dec(v_impl_870_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_951_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_size_889_; lean_object* v_size_890_; lean_object* v_k_891_; lean_object* v_v_892_; lean_object* v_l_893_; lean_object* v_r_894_; lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v_size_889_ = lean_ctor_get(v_l_876_, 0);
v_size_890_ = lean_ctor_get(v_r_877_, 0);
v_k_891_ = lean_ctor_get(v_r_877_, 1);
v_v_892_ = lean_ctor_get(v_r_877_, 2);
v_l_893_ = lean_ctor_get(v_r_877_, 3);
v_r_894_ = lean_ctor_get(v_r_877_, 4);
v___x_895_ = lean_unsigned_to_nat(2u);
v___x_896_ = lean_nat_mul(v___x_895_, v_size_889_);
v___x_897_ = lean_nat_dec_lt(v_size_890_, v___x_896_);
lean_dec(v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_926_; 
lean_inc(v_r_894_);
lean_inc(v_l_893_);
lean_inc(v_v_892_);
lean_inc(v_k_891_);
v_isSharedCheck_926_ = !lean_is_exclusive(v_r_877_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; lean_object* v_unused_928_; lean_object* v_unused_929_; lean_object* v_unused_930_; lean_object* v_unused_931_; 
v_unused_927_ = lean_ctor_get(v_r_877_, 4);
lean_dec(v_unused_927_);
v_unused_928_ = lean_ctor_get(v_r_877_, 3);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_r_877_, 2);
lean_dec(v_unused_929_);
v_unused_930_ = lean_ctor_get(v_r_877_, 1);
lean_dec(v_unused_930_);
v_unused_931_ = lean_ctor_get(v_r_877_, 0);
lean_dec(v_unused_931_);
v___x_899_ = v_r_877_;
v_isShared_900_ = v_isSharedCheck_926_;
goto v_resetjp_898_;
}
else
{
lean_dec(v_r_877_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_926_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___x_914_; lean_object* v___y_916_; 
v___x_901_ = lean_nat_add(v___x_871_, v_size_873_);
lean_dec(v_size_873_);
v___x_902_ = lean_nat_add(v___x_901_, v_size_872_);
lean_dec(v___x_901_);
v___x_914_ = lean_nat_add(v___x_871_, v_size_889_);
if (lean_obj_tag(v_l_893_) == 0)
{
lean_object* v_size_924_; 
v_size_924_ = lean_ctor_get(v_l_893_, 0);
lean_inc(v_size_924_);
v___y_916_ = v_size_924_;
goto v___jp_915_;
}
else
{
lean_object* v___x_925_; 
v___x_925_ = lean_unsigned_to_nat(0u);
v___y_916_ = v___x_925_;
goto v___jp_915_;
}
v___jp_903_:
{
lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_907_ = lean_nat_add(v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec(v___y_905_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 4, v_r_865_);
lean_ctor_set(v___x_899_, 3, v_r_894_);
lean_ctor_set(v___x_899_, 2, v_v_863_);
lean_ctor_set(v___x_899_, 1, v_k_862_);
lean_ctor_set(v___x_899_, 0, v___x_907_);
v___x_909_ = v___x_899_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_k_862_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_v_863_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_r_894_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_r_865_);
v___x_909_ = v_reuseFailAlloc_913_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_911_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v___x_909_);
lean_ctor_set(v___x_887_, 3, v___y_904_);
lean_ctor_set(v___x_887_, 2, v_v_892_);
lean_ctor_set(v___x_887_, 1, v_k_891_);
lean_ctor_set(v___x_887_, 0, v___x_902_);
v___x_911_ = v___x_887_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_k_891_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_v_892_);
lean_ctor_set(v_reuseFailAlloc_912_, 3, v___y_904_);
lean_ctor_set(v_reuseFailAlloc_912_, 4, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
v___jp_915_:
{
lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_917_ = lean_nat_add(v___x_914_, v___y_916_);
lean_dec(v___y_916_);
lean_dec(v___x_914_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v_l_893_);
lean_ctor_set(v___x_867_, 3, v_l_876_);
lean_ctor_set(v___x_867_, 2, v_v_875_);
lean_ctor_set(v___x_867_, 1, v_k_874_);
lean_ctor_set(v___x_867_, 0, v___x_917_);
v___x_919_ = v___x_867_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_k_874_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_v_875_);
lean_ctor_set(v_reuseFailAlloc_923_, 3, v_l_876_);
lean_ctor_set(v_reuseFailAlloc_923_, 4, v_l_893_);
v___x_919_ = v_reuseFailAlloc_923_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; 
v___x_920_ = lean_nat_add(v___x_871_, v_size_872_);
if (lean_obj_tag(v_r_894_) == 0)
{
lean_object* v_size_921_; 
v_size_921_ = lean_ctor_get(v_r_894_, 0);
lean_inc(v_size_921_);
v___y_904_ = v___x_919_;
v___y_905_ = v___x_920_;
v___y_906_ = v_size_921_;
goto v___jp_903_;
}
else
{
lean_object* v___x_922_; 
v___x_922_ = lean_unsigned_to_nat(0u);
v___y_904_ = v___x_919_;
v___y_905_ = v___x_920_;
v___y_906_ = v___x_922_;
goto v___jp_903_;
}
}
}
}
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
lean_del_object(v___x_867_);
v___x_932_ = lean_nat_add(v___x_871_, v_size_873_);
lean_dec(v_size_873_);
v___x_933_ = lean_nat_add(v___x_932_, v_size_872_);
lean_dec(v___x_932_);
v___x_934_ = lean_nat_add(v___x_871_, v_size_872_);
v___x_935_ = lean_nat_add(v___x_934_, v_size_890_);
lean_dec(v___x_934_);
lean_inc_ref(v_r_865_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v_r_865_);
lean_ctor_set(v___x_887_, 3, v_r_877_);
lean_ctor_set(v___x_887_, 2, v_v_863_);
lean_ctor_set(v___x_887_, 1, v_k_862_);
lean_ctor_set(v___x_887_, 0, v___x_935_);
v___x_937_ = v___x_887_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_k_862_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_v_863_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_r_877_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_r_865_);
v___x_937_ = v_reuseFailAlloc_950_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
v_isSharedCheck_944_ = !lean_is_exclusive(v_r_865_);
if (v_isSharedCheck_944_ == 0)
{
lean_object* v_unused_945_; lean_object* v_unused_946_; lean_object* v_unused_947_; lean_object* v_unused_948_; lean_object* v_unused_949_; 
v_unused_945_ = lean_ctor_get(v_r_865_, 4);
lean_dec(v_unused_945_);
v_unused_946_ = lean_ctor_get(v_r_865_, 3);
lean_dec(v_unused_946_);
v_unused_947_ = lean_ctor_get(v_r_865_, 2);
lean_dec(v_unused_947_);
v_unused_948_ = lean_ctor_get(v_r_865_, 1);
lean_dec(v_unused_948_);
v_unused_949_ = lean_ctor_get(v_r_865_, 0);
lean_dec(v_unused_949_);
v___x_939_ = v_r_865_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_dec(v_r_865_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 4, v___x_937_);
lean_ctor_set(v___x_939_, 3, v_l_876_);
lean_ctor_set(v___x_939_, 2, v_v_875_);
lean_ctor_set(v___x_939_, 1, v_k_874_);
lean_ctor_set(v___x_939_, 0, v___x_933_);
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_k_874_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v_v_875_);
lean_ctor_set(v_reuseFailAlloc_943_, 3, v_l_876_);
lean_ctor_set(v_reuseFailAlloc_943_, 4, v___x_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_957_; 
v_l_957_ = lean_ctor_get(v_impl_870_, 3);
if (lean_obj_tag(v_l_957_) == 0)
{
lean_object* v_r_958_; lean_object* v_k_959_; lean_object* v_v_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_971_; 
lean_inc_ref(v_l_957_);
v_r_958_ = lean_ctor_get(v_impl_870_, 4);
v_k_959_ = lean_ctor_get(v_impl_870_, 1);
v_v_960_ = lean_ctor_get(v_impl_870_, 2);
v_isSharedCheck_971_ = !lean_is_exclusive(v_impl_870_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; lean_object* v_unused_973_; 
v_unused_972_ = lean_ctor_get(v_impl_870_, 3);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v_impl_870_, 0);
lean_dec(v_unused_973_);
v___x_962_ = v_impl_870_;
v_isShared_963_ = v_isSharedCheck_971_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_r_958_);
lean_inc(v_v_960_);
lean_inc(v_k_959_);
lean_dec(v_impl_870_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_971_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_964_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_958_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 3, v_r_958_);
lean_ctor_set(v___x_962_, 2, v_v_863_);
lean_ctor_set(v___x_962_, 1, v_k_862_);
lean_ctor_set(v___x_962_, 0, v___x_871_);
v___x_966_ = v___x_962_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_k_862_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v_v_863_);
lean_ctor_set(v_reuseFailAlloc_970_, 3, v_r_958_);
lean_ctor_set(v_reuseFailAlloc_970_, 4, v_r_958_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v___x_966_);
lean_ctor_set(v___x_867_, 3, v_l_957_);
lean_ctor_set(v___x_867_, 2, v_v_960_);
lean_ctor_set(v___x_867_, 1, v_k_959_);
lean_ctor_set(v___x_867_, 0, v___x_964_);
v___x_968_ = v___x_867_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_k_959_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v_v_960_);
lean_ctor_set(v_reuseFailAlloc_969_, 3, v_l_957_);
lean_ctor_set(v_reuseFailAlloc_969_, 4, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
else
{
lean_object* v_r_974_; 
v_r_974_ = lean_ctor_get(v_impl_870_, 4);
lean_inc(v_r_974_);
if (lean_obj_tag(v_r_974_) == 0)
{
lean_object* v_k_975_; lean_object* v_v_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_999_; 
lean_inc(v_l_957_);
v_k_975_ = lean_ctor_get(v_impl_870_, 1);
v_v_976_ = lean_ctor_get(v_impl_870_, 2);
v_isSharedCheck_999_ = !lean_is_exclusive(v_impl_870_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; lean_object* v_unused_1001_; lean_object* v_unused_1002_; 
v_unused_1000_ = lean_ctor_get(v_impl_870_, 4);
lean_dec(v_unused_1000_);
v_unused_1001_ = lean_ctor_get(v_impl_870_, 3);
lean_dec(v_unused_1001_);
v_unused_1002_ = lean_ctor_get(v_impl_870_, 0);
lean_dec(v_unused_1002_);
v___x_978_ = v_impl_870_;
v_isShared_979_ = v_isSharedCheck_999_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_v_976_);
lean_inc(v_k_975_);
lean_dec(v_impl_870_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_999_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_k_980_; lean_object* v_v_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_995_; 
v_k_980_ = lean_ctor_get(v_r_974_, 1);
v_v_981_ = lean_ctor_get(v_r_974_, 2);
v_isSharedCheck_995_ = !lean_is_exclusive(v_r_974_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; lean_object* v_unused_997_; lean_object* v_unused_998_; 
v_unused_996_ = lean_ctor_get(v_r_974_, 4);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_r_974_, 3);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_r_974_, 0);
lean_dec(v_unused_998_);
v___x_983_ = v_r_974_;
v_isShared_984_ = v_isSharedCheck_995_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_v_981_);
lean_inc(v_k_980_);
lean_dec(v_r_974_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_995_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_985_ = lean_unsigned_to_nat(3u);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 4, v_l_957_);
lean_ctor_set(v___x_983_, 3, v_l_957_);
lean_ctor_set(v___x_983_, 2, v_v_976_);
lean_ctor_set(v___x_983_, 1, v_k_975_);
lean_ctor_set(v___x_983_, 0, v___x_871_);
v___x_987_ = v___x_983_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_k_975_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_v_976_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v_l_957_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v_l_957_);
v___x_987_ = v_reuseFailAlloc_994_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_989_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 4, v_l_957_);
lean_ctor_set(v___x_978_, 2, v_v_863_);
lean_ctor_set(v___x_978_, 1, v_k_862_);
lean_ctor_set(v___x_978_, 0, v___x_871_);
v___x_989_ = v___x_978_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_k_862_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_v_863_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v_l_957_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v_l_957_);
v___x_989_ = v_reuseFailAlloc_993_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_991_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v___x_989_);
lean_ctor_set(v___x_867_, 3, v___x_987_);
lean_ctor_set(v___x_867_, 2, v_v_981_);
lean_ctor_set(v___x_867_, 1, v_k_980_);
lean_ctor_set(v___x_867_, 0, v___x_985_);
v___x_991_ = v___x_867_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_k_980_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v_v_981_);
lean_ctor_set(v_reuseFailAlloc_992_, 3, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_992_, 4, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = lean_unsigned_to_nat(2u);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v_r_974_);
lean_ctor_set(v___x_867_, 3, v_impl_870_);
lean_ctor_set(v___x_867_, 0, v___x_1003_);
v___x_1005_ = v___x_867_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_k_862_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_v_863_);
lean_ctor_set(v_reuseFailAlloc_1006_, 3, v_impl_870_);
lean_ctor_set(v_reuseFailAlloc_1006_, 4, v_r_974_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1008_; 
lean_dec(v_v_863_);
lean_dec(v_k_862_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 2, v_v_859_);
lean_ctor_set(v___x_867_, 1, v_k_858_);
v___x_1008_ = v___x_867_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_size_861_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_k_858_);
lean_ctor_set(v_reuseFailAlloc_1009_, 2, v_v_859_);
lean_ctor_set(v_reuseFailAlloc_1009_, 3, v_l_864_);
lean_ctor_set(v_reuseFailAlloc_1009_, 4, v_r_865_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
default: 
{
lean_object* v_impl_1010_; lean_object* v___x_1011_; 
lean_dec(v_size_861_);
v_impl_1010_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_858_, v_v_859_, v_r_865_);
v___x_1011_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_864_) == 0)
{
lean_object* v_size_1012_; lean_object* v_size_1013_; lean_object* v_k_1014_; lean_object* v_v_1015_; lean_object* v_l_1016_; lean_object* v_r_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v_size_1012_ = lean_ctor_get(v_l_864_, 0);
v_size_1013_ = lean_ctor_get(v_impl_1010_, 0);
v_k_1014_ = lean_ctor_get(v_impl_1010_, 1);
v_v_1015_ = lean_ctor_get(v_impl_1010_, 2);
v_l_1016_ = lean_ctor_get(v_impl_1010_, 3);
lean_inc(v_l_1016_);
v_r_1017_ = lean_ctor_get(v_impl_1010_, 4);
v___x_1018_ = lean_unsigned_to_nat(3u);
v___x_1019_ = lean_nat_mul(v___x_1018_, v_size_1012_);
v___x_1020_ = lean_nat_dec_lt(v___x_1019_, v_size_1013_);
lean_dec(v___x_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
lean_dec(v_l_1016_);
v___x_1021_ = lean_nat_add(v___x_1011_, v_size_1012_);
v___x_1022_ = lean_nat_add(v___x_1021_, v_size_1013_);
lean_dec(v___x_1021_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v_impl_1010_);
lean_ctor_set(v___x_867_, 0, v___x_1022_);
v___x_1024_ = v___x_867_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_k_862_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_v_863_);
lean_ctor_set(v_reuseFailAlloc_1025_, 3, v_l_864_);
lean_ctor_set(v_reuseFailAlloc_1025_, 4, v_impl_1010_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
else
{
lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1089_; 
lean_inc(v_r_1017_);
lean_inc(v_v_1015_);
lean_inc(v_k_1014_);
lean_inc(v_size_1013_);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_impl_1010_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; lean_object* v_unused_1091_; lean_object* v_unused_1092_; lean_object* v_unused_1093_; lean_object* v_unused_1094_; 
v_unused_1090_ = lean_ctor_get(v_impl_1010_, 4);
lean_dec(v_unused_1090_);
v_unused_1091_ = lean_ctor_get(v_impl_1010_, 3);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_impl_1010_, 2);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_impl_1010_, 1);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_impl_1010_, 0);
lean_dec(v_unused_1094_);
v___x_1027_ = v_impl_1010_;
v_isShared_1028_ = v_isSharedCheck_1089_;
goto v_resetjp_1026_;
}
else
{
lean_dec(v_impl_1010_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1089_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v_size_1029_; lean_object* v_k_1030_; lean_object* v_v_1031_; lean_object* v_l_1032_; lean_object* v_r_1033_; lean_object* v_size_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v_size_1029_ = lean_ctor_get(v_l_1016_, 0);
v_k_1030_ = lean_ctor_get(v_l_1016_, 1);
v_v_1031_ = lean_ctor_get(v_l_1016_, 2);
v_l_1032_ = lean_ctor_get(v_l_1016_, 3);
v_r_1033_ = lean_ctor_get(v_l_1016_, 4);
v_size_1034_ = lean_ctor_get(v_r_1017_, 0);
v___x_1035_ = lean_unsigned_to_nat(2u);
v___x_1036_ = lean_nat_mul(v___x_1035_, v_size_1034_);
v___x_1037_ = lean_nat_dec_lt(v_size_1029_, v___x_1036_);
lean_dec(v___x_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1065_; 
lean_inc(v_r_1033_);
lean_inc(v_l_1032_);
lean_inc(v_v_1031_);
lean_inc(v_k_1030_);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_l_1016_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; lean_object* v_unused_1067_; lean_object* v_unused_1068_; lean_object* v_unused_1069_; lean_object* v_unused_1070_; 
v_unused_1066_ = lean_ctor_get(v_l_1016_, 4);
lean_dec(v_unused_1066_);
v_unused_1067_ = lean_ctor_get(v_l_1016_, 3);
lean_dec(v_unused_1067_);
v_unused_1068_ = lean_ctor_get(v_l_1016_, 2);
lean_dec(v_unused_1068_);
v_unused_1069_ = lean_ctor_get(v_l_1016_, 1);
lean_dec(v_unused_1069_);
v_unused_1070_ = lean_ctor_get(v_l_1016_, 0);
lean_dec(v_unused_1070_);
v___x_1039_ = v_l_1016_;
v_isShared_1040_ = v_isSharedCheck_1065_;
goto v_resetjp_1038_;
}
else
{
lean_dec(v_l_1016_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1065_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1055_; 
v___x_1041_ = lean_nat_add(v___x_1011_, v_size_1012_);
v___x_1042_ = lean_nat_add(v___x_1041_, v_size_1013_);
lean_dec(v_size_1013_);
if (lean_obj_tag(v_l_1032_) == 0)
{
lean_object* v_size_1063_; 
v_size_1063_ = lean_ctor_get(v_l_1032_, 0);
lean_inc(v_size_1063_);
v___y_1055_ = v_size_1063_;
goto v___jp_1054_;
}
else
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_unsigned_to_nat(0u);
v___y_1055_ = v___x_1064_;
goto v___jp_1054_;
}
v___jp_1043_:
{
lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1047_ = lean_nat_add(v___y_1044_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec(v___y_1044_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v_r_1017_);
lean_ctor_set(v___x_1039_, 3, v_r_1033_);
lean_ctor_set(v___x_1039_, 2, v_v_1015_);
lean_ctor_set(v___x_1039_, 1, v_k_1014_);
lean_ctor_set(v___x_1039_, 0, v___x_1047_);
v___x_1049_ = v___x_1039_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_k_1014_);
lean_ctor_set(v_reuseFailAlloc_1053_, 2, v_v_1015_);
lean_ctor_set(v_reuseFailAlloc_1053_, 3, v_r_1033_);
lean_ctor_set(v_reuseFailAlloc_1053_, 4, v_r_1017_);
v___x_1049_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1051_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 4, v___x_1049_);
lean_ctor_set(v___x_1027_, 3, v___y_1045_);
lean_ctor_set(v___x_1027_, 2, v_v_1031_);
lean_ctor_set(v___x_1027_, 1, v_k_1030_);
lean_ctor_set(v___x_1027_, 0, v___x_1042_);
v___x_1051_ = v___x_1027_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_k_1030_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v_v_1031_);
lean_ctor_set(v_reuseFailAlloc_1052_, 3, v___y_1045_);
lean_ctor_set(v_reuseFailAlloc_1052_, 4, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
v___jp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1056_ = lean_nat_add(v___x_1041_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec(v___x_1041_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v_l_1032_);
lean_ctor_set(v___x_867_, 0, v___x_1056_);
v___x_1058_ = v___x_867_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_k_862_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v_v_863_);
lean_ctor_set(v_reuseFailAlloc_1062_, 3, v_l_864_);
lean_ctor_set(v_reuseFailAlloc_1062_, 4, v_l_1032_);
v___x_1058_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_nat_add(v___x_1011_, v_size_1034_);
if (lean_obj_tag(v_r_1033_) == 0)
{
lean_object* v_size_1060_; 
v_size_1060_ = lean_ctor_get(v_r_1033_, 0);
lean_inc(v_size_1060_);
v___y_1044_ = v___x_1059_;
v___y_1045_ = v___x_1058_;
v___y_1046_ = v_size_1060_;
goto v___jp_1043_;
}
else
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_unsigned_to_nat(0u);
v___y_1044_ = v___x_1059_;
v___y_1045_ = v___x_1058_;
v___y_1046_ = v___x_1061_;
goto v___jp_1043_;
}
}
}
}
}
else
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
lean_del_object(v___x_867_);
v___x_1071_ = lean_nat_add(v___x_1011_, v_size_1012_);
v___x_1072_ = lean_nat_add(v___x_1071_, v_size_1013_);
lean_dec(v_size_1013_);
v___x_1073_ = lean_nat_add(v___x_1071_, v_size_1029_);
lean_dec(v___x_1071_);
lean_inc_ref(v_l_864_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 4, v_l_1016_);
lean_ctor_set(v___x_1027_, 3, v_l_864_);
lean_ctor_set(v___x_1027_, 2, v_v_863_);
lean_ctor_set(v___x_1027_, 1, v_k_862_);
lean_ctor_set(v___x_1027_, 0, v___x_1073_);
v___x_1075_ = v___x_1027_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_k_862_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_v_863_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_l_864_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v_l_1016_);
v___x_1075_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_isSharedCheck_1082_ = !lean_is_exclusive(v_l_864_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; lean_object* v_unused_1084_; lean_object* v_unused_1085_; lean_object* v_unused_1086_; lean_object* v_unused_1087_; 
v_unused_1083_ = lean_ctor_get(v_l_864_, 4);
lean_dec(v_unused_1083_);
v_unused_1084_ = lean_ctor_get(v_l_864_, 3);
lean_dec(v_unused_1084_);
v_unused_1085_ = lean_ctor_get(v_l_864_, 2);
lean_dec(v_unused_1085_);
v_unused_1086_ = lean_ctor_get(v_l_864_, 1);
lean_dec(v_unused_1086_);
v_unused_1087_ = lean_ctor_get(v_l_864_, 0);
lean_dec(v_unused_1087_);
v___x_1077_ = v_l_864_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_dec(v_l_864_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 4, v_r_1017_);
lean_ctor_set(v___x_1077_, 3, v___x_1075_);
lean_ctor_set(v___x_1077_, 2, v_v_1015_);
lean_ctor_set(v___x_1077_, 1, v_k_1014_);
lean_ctor_set(v___x_1077_, 0, v___x_1072_);
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_k_1014_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v_v_1015_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v_r_1017_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1095_; 
v_l_1095_ = lean_ctor_get(v_impl_1010_, 3);
lean_inc(v_l_1095_);
if (lean_obj_tag(v_l_1095_) == 0)
{
lean_object* v_r_1096_; lean_object* v_k_1097_; lean_object* v_v_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1121_; 
v_r_1096_ = lean_ctor_get(v_impl_1010_, 4);
v_k_1097_ = lean_ctor_get(v_impl_1010_, 1);
v_v_1098_ = lean_ctor_get(v_impl_1010_, 2);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_impl_1010_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; lean_object* v_unused_1123_; 
v_unused_1122_ = lean_ctor_get(v_impl_1010_, 3);
lean_dec(v_unused_1122_);
v_unused_1123_ = lean_ctor_get(v_impl_1010_, 0);
lean_dec(v_unused_1123_);
v___x_1100_ = v_impl_1010_;
v_isShared_1101_ = v_isSharedCheck_1121_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_r_1096_);
lean_inc(v_v_1098_);
lean_inc(v_k_1097_);
lean_dec(v_impl_1010_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1121_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_k_1102_; lean_object* v_v_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1117_; 
v_k_1102_ = lean_ctor_get(v_l_1095_, 1);
v_v_1103_ = lean_ctor_get(v_l_1095_, 2);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_l_1095_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; lean_object* v_unused_1119_; lean_object* v_unused_1120_; 
v_unused_1118_ = lean_ctor_get(v_l_1095_, 4);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v_l_1095_, 3);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_l_1095_, 0);
lean_dec(v_unused_1120_);
v___x_1105_ = v_l_1095_;
v_isShared_1106_ = v_isSharedCheck_1117_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_v_1103_);
lean_inc(v_k_1102_);
lean_dec(v_l_1095_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1117_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1107_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1096_, 2);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 4, v_r_1096_);
lean_ctor_set(v___x_1105_, 3, v_r_1096_);
lean_ctor_set(v___x_1105_, 2, v_v_863_);
lean_ctor_set(v___x_1105_, 1, v_k_862_);
lean_ctor_set(v___x_1105_, 0, v___x_1011_);
v___x_1109_ = v___x_1105_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_k_862_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_v_863_);
lean_ctor_set(v_reuseFailAlloc_1116_, 3, v_r_1096_);
lean_ctor_set(v_reuseFailAlloc_1116_, 4, v_r_1096_);
v___x_1109_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1111_; 
lean_inc(v_r_1096_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 3, v_r_1096_);
lean_ctor_set(v___x_1100_, 0, v___x_1011_);
v___x_1111_ = v___x_1100_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_k_1097_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_v_1098_);
lean_ctor_set(v_reuseFailAlloc_1115_, 3, v_r_1096_);
lean_ctor_set(v_reuseFailAlloc_1115_, 4, v_r_1096_);
v___x_1111_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1113_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v___x_1111_);
lean_ctor_set(v___x_867_, 3, v___x_1109_);
lean_ctor_set(v___x_867_, 2, v_v_1103_);
lean_ctor_set(v___x_867_, 1, v_k_1102_);
lean_ctor_set(v___x_867_, 0, v___x_1107_);
v___x_1113_ = v___x_867_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_k_1102_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_v_1103_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
}
else
{
lean_object* v_r_1124_; 
v_r_1124_ = lean_ctor_get(v_impl_1010_, 4);
lean_inc(v_r_1124_);
if (lean_obj_tag(v_r_1124_) == 0)
{
lean_object* v_k_1125_; lean_object* v_v_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1137_; 
v_k_1125_ = lean_ctor_get(v_impl_1010_, 1);
v_v_1126_ = lean_ctor_get(v_impl_1010_, 2);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_impl_1010_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; lean_object* v_unused_1139_; lean_object* v_unused_1140_; 
v_unused_1138_ = lean_ctor_get(v_impl_1010_, 4);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_impl_1010_, 3);
lean_dec(v_unused_1139_);
v_unused_1140_ = lean_ctor_get(v_impl_1010_, 0);
lean_dec(v_unused_1140_);
v___x_1128_ = v_impl_1010_;
v_isShared_1129_ = v_isSharedCheck_1137_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_v_1126_);
lean_inc(v_k_1125_);
lean_dec(v_impl_1010_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1137_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = lean_unsigned_to_nat(3u);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 4, v_l_1095_);
lean_ctor_set(v___x_1128_, 2, v_v_863_);
lean_ctor_set(v___x_1128_, 1, v_k_862_);
lean_ctor_set(v___x_1128_, 0, v___x_1011_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_k_862_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_v_863_);
lean_ctor_set(v_reuseFailAlloc_1136_, 3, v_l_1095_);
lean_ctor_set(v_reuseFailAlloc_1136_, 4, v_l_1095_);
v___x_1132_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1134_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v_r_1124_);
lean_ctor_set(v___x_867_, 3, v___x_1132_);
lean_ctor_set(v___x_867_, 2, v_v_1126_);
lean_ctor_set(v___x_867_, 1, v_k_1125_);
lean_ctor_set(v___x_867_, 0, v___x_1130_);
v___x_1134_ = v___x_867_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_k_1125_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_v_1126_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_r_1124_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1141_ = lean_unsigned_to_nat(2u);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v_impl_1010_);
lean_ctor_set(v___x_867_, 3, v_r_1124_);
lean_ctor_set(v___x_867_, 0, v___x_1141_);
v___x_1143_ = v___x_867_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_k_862_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_v_863_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v_r_1124_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v_impl_1010_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
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
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_unsigned_to_nat(1u);
v___x_1147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v_k_858_);
lean_ctor_set(v___x_1147_, 2, v_v_859_);
lean_ctor_set(v___x_1147_, 3, v_t_860_);
lean_ctor_set(v___x_1147_, 4, v_t_860_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(lean_object* v_as_x27_1148_, lean_object* v_b_1149_){
_start:
{
if (lean_obj_tag(v_as_x27_1148_) == 0)
{
return v_b_1149_;
}
else
{
lean_object* v_head_1150_; lean_object* v_tail_1151_; lean_object* v_fst_1152_; lean_object* v_snd_1153_; lean_object* v_r_1154_; 
v_head_1150_ = lean_ctor_get(v_as_x27_1148_, 0);
v_tail_1151_ = lean_ctor_get(v_as_x27_1148_, 1);
v_fst_1152_ = lean_ctor_get(v_head_1150_, 0);
v_snd_1153_ = lean_ctor_get(v_head_1150_, 1);
lean_inc(v_snd_1153_);
lean_inc(v_fst_1152_);
v_r_1154_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_fst_1152_, v_snd_1153_, v_b_1149_);
v_as_x27_1148_ = v_tail_1151_;
v_b_1149_ = v_r_1154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg___boxed(lean_object* v_as_x27_1156_, lean_object* v_b_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1156_, v_b_1157_);
lean_dec(v_as_x27_1156_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj(lean_object* v_o_1159_){
_start:
{
lean_object* v_r_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_r_1160_ = lean_box(1);
v___x_1161_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_o_1159_, v_r_1160_);
v___x_1162_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj___boxed(lean_object* v_o_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Json_mkObj(v_o_1163_);
lean_dec(v_o_1163_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0(lean_object* v_00_u03b2_1165_, lean_object* v_k_1166_, lean_object* v_v_1167_, lean_object* v_t_1168_, lean_object* v_hl_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_1166_, v_v_1167_, v_t_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(lean_object* v_as_1171_, lean_object* v_as_x27_1172_, lean_object* v_b_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1172_, v_b_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___boxed(lean_object* v_as_1176_, lean_object* v_as_x27_1177_, lean_object* v_b_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(v_as_1176_, v_as_x27_1177_, v_b_1178_, v_a_1179_);
lean_dec(v_as_x27_1177_);
lean_dec(v_as_1176_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeNat___lam__0(lean_object* v_n_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = l_Lean_JsonNumber_fromNat(v_n_1181_);
v___x_1183_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeInt___lam__0(lean_object* v_n_1186_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = l_Lean_JsonNumber_fromInt(v_n_1186_);
v___x_1188_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeString___lam__0(lean_object* v_s_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1192_, 0, v_s_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0(uint8_t v_b_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1196_, 0, v_b_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0___boxed(lean_object* v_b_1197_){
_start:
{
uint8_t v_b_boxed_1198_; lean_object* v_res_1199_; 
v_b_boxed_1198_ = lean_unbox(v_b_1197_);
v_res_1199_ = l_Lean_Json_instCoeBool___lam__0(v_b_boxed_1198_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instOfNat(lean_object* v_n_1202_){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = l_Lean_JsonNumber_fromNat(v_n_1202_);
v___x_1204_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_isNull(lean_object* v_x_1205_){
_start:
{
if (lean_obj_tag(v_x_1205_) == 0)
{
uint8_t v___x_1206_; 
v___x_1206_ = 1;
return v___x_1206_;
}
else
{
uint8_t v___x_1207_; 
v___x_1207_ = 0;
return v___x_1207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_isNull___boxed(lean_object* v_x_1208_){
_start:
{
uint8_t v_res_1209_; lean_object* v_r_1210_; 
v_res_1209_ = l_Lean_Json_isNull(v_x_1208_);
lean_dec(v_x_1208_);
v_r_1210_ = lean_box(v_res_1209_);
return v_r_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObj_x3f(lean_object* v_x_1214_){
_start:
{
if (lean_obj_tag(v_x_1214_) == 5)
{
lean_object* v_kvPairs_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
v_kvPairs_1215_ = lean_ctor_get(v_x_1214_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_x_1214_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v_x_1214_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_kvPairs_1215_);
lean_dec(v_x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set_tag(v___x_1217_, 1);
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_kvPairs_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
else
{
lean_object* v___x_1223_; 
lean_dec(v_x_1214_);
v___x_1223_ = ((lean_object*)(l_Lean_Json_getObj_x3f___closed__1));
return v___x_1223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArr_x3f(lean_object* v_x_1227_){
_start:
{
if (lean_obj_tag(v_x_1227_) == 4)
{
lean_object* v_elems_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v_elems_1228_ = lean_ctor_get(v_x_1227_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_x_1227_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v_x_1227_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_elems_1228_);
lean_dec(v_x_1227_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set_tag(v___x_1230_, 1);
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_elems_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
else
{
lean_object* v___x_1236_; 
lean_dec(v_x_1227_);
v___x_1236_ = ((lean_object*)(l_Lean_Json_getArr_x3f___closed__1));
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getStr_x3f(lean_object* v_x_1240_){
_start:
{
if (lean_obj_tag(v_x_1240_) == 3)
{
lean_object* v_s_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
v_s_1241_ = lean_ctor_get(v_x_1240_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_x_1240_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v_x_1240_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_s_1241_);
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
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_s_1241_);
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
v___x_1249_ = ((lean_object*)(l_Lean_Json_getStr_x3f___closed__1));
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNat_x3f(lean_object* v_x_1253_){
_start:
{
if (lean_obj_tag(v_x_1253_) == 2)
{
lean_object* v_n_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1270_; 
v_n_1256_ = lean_ctor_get(v_x_1253_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_x_1253_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1258_ = v_x_1253_;
v_isShared_1259_ = v_isSharedCheck_1270_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_n_1256_);
lean_dec(v_x_1253_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1270_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v_mantissa_1260_; lean_object* v_exponent_1261_; lean_object* v_natZero_1262_; lean_object* v_intZero_1263_; uint8_t v_isNeg_1264_; 
v_mantissa_1260_ = lean_ctor_get(v_n_1256_, 0);
lean_inc(v_mantissa_1260_);
v_exponent_1261_ = lean_ctor_get(v_n_1256_, 1);
lean_inc(v_exponent_1261_);
lean_dec_ref(v_n_1256_);
v_natZero_1262_ = lean_unsigned_to_nat(0u);
v_intZero_1263_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v_isNeg_1264_ = lean_int_dec_lt(v_mantissa_1260_, v_intZero_1263_);
if (v_isNeg_1264_ == 0)
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_nat_dec_eq(v_exponent_1261_, v_natZero_1262_);
lean_dec(v_exponent_1261_);
if (v___x_1265_ == 0)
{
lean_dec(v_mantissa_1260_);
lean_del_object(v___x_1258_);
goto v___jp_1254_;
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; 
v_a_1266_ = lean_nat_abs(v_mantissa_1260_);
lean_dec(v_mantissa_1260_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set_tag(v___x_1258_, 1);
lean_ctor_set(v___x_1258_, 0, v_a_1266_);
v___x_1268_ = v___x_1258_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
else
{
lean_dec(v_exponent_1261_);
lean_dec(v_mantissa_1260_);
lean_del_object(v___x_1258_);
goto v___jp_1254_;
}
}
}
else
{
lean_dec(v_x_1253_);
goto v___jp_1254_;
}
v___jp_1254_:
{
lean_object* v___x_1255_; 
v___x_1255_ = ((lean_object*)(l_Lean_Json_getNat_x3f___closed__1));
return v___x_1255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getInt_x3f(lean_object* v_x_1274_){
_start:
{
if (lean_obj_tag(v_x_1274_) == 2)
{
lean_object* v_n_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1288_; 
v_n_1277_ = lean_ctor_get(v_x_1274_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_x_1274_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1279_ = v_x_1274_;
v_isShared_1280_ = v_isSharedCheck_1288_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_n_1277_);
lean_dec(v_x_1274_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1288_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v_mantissa_1281_; lean_object* v_exponent_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v_mantissa_1281_ = lean_ctor_get(v_n_1277_, 0);
lean_inc(v_mantissa_1281_);
v_exponent_1282_ = lean_ctor_get(v_n_1277_, 1);
lean_inc(v_exponent_1282_);
lean_dec_ref(v_n_1277_);
v___x_1283_ = lean_unsigned_to_nat(0u);
v___x_1284_ = lean_nat_dec_eq(v_exponent_1282_, v___x_1283_);
lean_dec(v_exponent_1282_);
if (v___x_1284_ == 0)
{
lean_dec(v_mantissa_1281_);
lean_del_object(v___x_1279_);
goto v___jp_1275_;
}
else
{
lean_object* v___x_1286_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set_tag(v___x_1279_, 1);
lean_ctor_set(v___x_1279_, 0, v_mantissa_1281_);
v___x_1286_ = v___x_1279_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_mantissa_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_dec(v_x_1274_);
goto v___jp_1275_;
}
v___jp_1275_:
{
lean_object* v___x_1276_; 
v___x_1276_ = ((lean_object*)(l_Lean_Json_getInt_x3f___closed__1));
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f(lean_object* v_x_1292_){
_start:
{
if (lean_obj_tag(v_x_1292_) == 1)
{
uint8_t v_b_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_b_1293_ = lean_ctor_get_uint8(v_x_1292_, 0);
v___x_1294_ = lean_box(v_b_1293_);
v___x_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
else
{
lean_object* v___x_1296_; 
v___x_1296_ = ((lean_object*)(l_Lean_Json_getBool_x3f___closed__1));
return v___x_1296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object* v_x_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_Json_getBool_x3f(v_x_1297_);
lean_dec(v_x_1297_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNum_x3f(lean_object* v_x_1302_){
_start:
{
if (lean_obj_tag(v_x_1302_) == 2)
{
lean_object* v_n_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
v_n_1303_ = lean_ctor_get(v_x_1302_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_x_1302_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v_x_1302_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_n_1303_);
lean_dec(v_x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 1);
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_n_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
else
{
lean_object* v___x_1311_; 
lean_dec(v_x_1302_);
v___x_1311_ = ((lean_object*)(l_Lean_Json_getNum_x3f___closed__1));
return v___x_1311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f(lean_object* v_x_1315_, lean_object* v_x_1316_){
_start:
{
if (lean_obj_tag(v_x_1315_) == 5)
{
lean_object* v_kvPairs_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1335_; 
v_kvPairs_1317_ = lean_ctor_get(v_x_1315_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_x_1315_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1319_ = v_x_1315_;
v_isShared_1320_ = v_isSharedCheck_1335_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_kvPairs_1317_);
lean_dec(v_x_1315_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1335_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_1317_, v_x_1316_);
lean_dec(v_kvPairs_1317_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1322_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__0));
v___x_1323_ = lean_string_append(v___x_1322_, v_x_1316_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set_tag(v___x_1319_, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1323_);
v___x_1325_ = v___x_1319_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
else
{
lean_object* v_val_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_del_object(v___x_1319_);
v_val_1327_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1321_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_val_1327_);
lean_dec(v___x_1321_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_val_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
else
{
lean_object* v___x_1336_; 
lean_dec(v_x_1315_);
v___x_1336_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__1));
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f___boxed(lean_object* v_x_1337_, lean_object* v_x_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_Json_getObjVal_x3f(v_x_1337_, v_x_1338_);
lean_dec_ref(v_x_1338_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArrVal_x3f(lean_object* v_x_1343_, lean_object* v_x_1344_){
_start:
{
if (lean_obj_tag(v_x_1343_) == 4)
{
lean_object* v_elems_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1361_; 
v_elems_1345_ = lean_ctor_get(v_x_1343_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_x_1343_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1347_ = v_x_1343_;
v_isShared_1348_ = v_isSharedCheck_1361_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_elems_1345_);
lean_dec(v_x_1343_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1361_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1349_ = lean_array_get_size(v_elems_1345_);
v___x_1350_ = lean_nat_dec_lt(v_x_1344_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
lean_dec_ref(v_elems_1345_);
v___x_1351_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__0));
v___x_1352_ = l_Nat_reprFast(v_x_1344_);
v___x_1353_ = lean_string_append(v___x_1351_, v___x_1352_);
lean_dec_ref(v___x_1352_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set_tag(v___x_1347_, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1353_);
v___x_1355_ = v___x_1347_;
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
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_array_fget(v_elems_1345_, v_x_1344_);
lean_dec(v_x_1344_);
lean_dec_ref(v_elems_1345_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set_tag(v___x_1347_, 1);
lean_ctor_set(v___x_1347_, 0, v___x_1357_);
v___x_1359_ = v___x_1347_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
else
{
lean_object* v___x_1362_; 
lean_dec(v_x_1344_);
lean_dec(v_x_1343_);
v___x_1362_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__1));
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD(lean_object* v_j_1363_, lean_object* v_k_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_Json_getObjVal_x3f(v_j_1363_, v_k_1364_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v___x_1366_; 
lean_dec_ref_known(v___x_1365_, 1);
v___x_1366_ = lean_box(0);
return v___x_1366_;
}
else
{
lean_object* v_a_1367_; 
v_a_1367_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1365_, 1);
return v_a_1367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD___boxed(lean_object* v_j_1368_, lean_object* v_k_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_Json_getObjValD(v_j_1368_, v_k_1369_);
lean_dec_ref(v_k_1369_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Json_setObjVal_x21_spec__1(lean_object* v_msg_1371_){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_box(0);
v___x_1373_ = lean_panic_fn_borrowed(v___x_1372_, v_msg_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(lean_object* v_msg_1374_){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_box(1);
v___x_1376_ = lean_panic_fn_borrowed(v___x_1375_, v_msg_1374_);
return v___x_1376_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1380_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1381_ = lean_unsigned_to_nat(35u);
v___x_1382_ = lean_unsigned_to_nat(182u);
v___x_1383_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1384_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1385_ = l_mkPanicMessageWithDecl(v___x_1384_, v___x_1383_, v___x_1382_, v___x_1381_, v___x_1380_);
return v___x_1385_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1386_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1387_ = lean_unsigned_to_nat(21u);
v___x_1388_ = lean_unsigned_to_nat(183u);
v___x_1389_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1390_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1391_ = l_mkPanicMessageWithDecl(v___x_1390_, v___x_1389_, v___x_1388_, v___x_1387_, v___x_1386_);
return v___x_1391_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1394_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1395_ = lean_unsigned_to_nat(35u);
v___x_1396_ = lean_unsigned_to_nat(276u);
v___x_1397_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1398_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1399_ = l_mkPanicMessageWithDecl(v___x_1398_, v___x_1397_, v___x_1396_, v___x_1395_, v___x_1394_);
return v___x_1399_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1400_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1401_ = lean_unsigned_to_nat(21u);
v___x_1402_ = lean_unsigned_to_nat(277u);
v___x_1403_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1404_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1405_ = l_mkPanicMessageWithDecl(v___x_1404_, v___x_1403_, v___x_1402_, v___x_1401_, v___x_1400_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(lean_object* v_k_1406_, lean_object* v_v_1407_, lean_object* v_t_1408_){
_start:
{
if (lean_obj_tag(v_t_1408_) == 0)
{
lean_object* v_size_1409_; lean_object* v_k_1410_; lean_object* v_v_1411_; lean_object* v_l_1412_; lean_object* v_r_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1769_; 
v_size_1409_ = lean_ctor_get(v_t_1408_, 0);
v_k_1410_ = lean_ctor_get(v_t_1408_, 1);
v_v_1411_ = lean_ctor_get(v_t_1408_, 2);
v_l_1412_ = lean_ctor_get(v_t_1408_, 3);
v_r_1413_ = lean_ctor_get(v_t_1408_, 4);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_t_1408_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1415_ = v_t_1408_;
v_isShared_1416_ = v_isSharedCheck_1769_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_r_1413_);
lean_inc(v_l_1412_);
lean_inc(v_v_1411_);
lean_inc(v_k_1410_);
lean_inc(v_size_1409_);
lean_dec(v_t_1408_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1769_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_string_compare(v_k_1406_, v_k_1410_);
switch(v___x_1417_)
{
case 0:
{
lean_object* v___x_1418_; 
lean_dec(v_size_1409_);
v___x_1418_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1406_, v_v_1407_, v_l_1412_);
if (lean_obj_tag(v_r_1413_) == 0)
{
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_size_1419_; lean_object* v_size_1420_; lean_object* v_k_1421_; lean_object* v_v_1422_; lean_object* v_l_1423_; lean_object* v_r_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v_size_1419_ = lean_ctor_get(v_r_1413_, 0);
v_size_1420_ = lean_ctor_get(v___x_1418_, 0);
v_k_1421_ = lean_ctor_get(v___x_1418_, 1);
v_v_1422_ = lean_ctor_get(v___x_1418_, 2);
v_l_1423_ = lean_ctor_get(v___x_1418_, 3);
v_r_1424_ = lean_ctor_get(v___x_1418_, 4);
lean_inc(v_r_1424_);
v___x_1425_ = lean_unsigned_to_nat(3u);
v___x_1426_ = lean_nat_mul(v___x_1425_, v_size_1419_);
v___x_1427_ = lean_nat_dec_lt(v___x_1426_, v_size_1420_);
lean_dec(v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
lean_dec(v_r_1424_);
v___x_1428_ = lean_unsigned_to_nat(1u);
v___x_1429_ = lean_nat_add(v___x_1428_, v_size_1420_);
v___x_1430_ = lean_nat_add(v___x_1429_, v_size_1419_);
lean_dec(v___x_1429_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 3, v___x_1418_);
lean_ctor_set(v___x_1415_, 0, v___x_1430_);
v___x_1432_ = v___x_1415_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1433_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1433_, 3, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1433_, 4, v_r_1413_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
else
{
lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1505_; 
lean_inc(v_l_1423_);
lean_inc(v_v_1422_);
lean_inc(v_k_1421_);
lean_inc(v_size_1420_);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; lean_object* v_unused_1507_; lean_object* v_unused_1508_; lean_object* v_unused_1509_; lean_object* v_unused_1510_; 
v_unused_1506_ = lean_ctor_get(v___x_1418_, 4);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v___x_1418_, 3);
lean_dec(v_unused_1507_);
v_unused_1508_ = lean_ctor_get(v___x_1418_, 2);
lean_dec(v_unused_1508_);
v_unused_1509_ = lean_ctor_get(v___x_1418_, 1);
lean_dec(v_unused_1509_);
v_unused_1510_ = lean_ctor_get(v___x_1418_, 0);
lean_dec(v_unused_1510_);
v___x_1435_ = v___x_1418_;
v_isShared_1436_ = v_isSharedCheck_1505_;
goto v_resetjp_1434_;
}
else
{
lean_dec(v___x_1418_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1505_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
if (lean_obj_tag(v_l_1423_) == 0)
{
if (lean_obj_tag(v_r_1424_) == 0)
{
lean_object* v_size_1437_; lean_object* v_size_1438_; lean_object* v_k_1439_; lean_object* v_v_1440_; lean_object* v_l_1441_; lean_object* v_r_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v_size_1437_ = lean_ctor_get(v_l_1423_, 0);
v_size_1438_ = lean_ctor_get(v_r_1424_, 0);
v_k_1439_ = lean_ctor_get(v_r_1424_, 1);
v_v_1440_ = lean_ctor_get(v_r_1424_, 2);
v_l_1441_ = lean_ctor_get(v_r_1424_, 3);
v_r_1442_ = lean_ctor_get(v_r_1424_, 4);
v___x_1443_ = lean_unsigned_to_nat(2u);
v___x_1444_ = lean_nat_mul(v___x_1443_, v_size_1437_);
v___x_1445_ = lean_nat_dec_lt(v_size_1438_, v___x_1444_);
lean_dec(v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1475_; 
lean_inc(v_r_1442_);
lean_inc(v_l_1441_);
lean_inc(v_v_1440_);
lean_inc(v_k_1439_);
v_isSharedCheck_1475_ = !lean_is_exclusive(v_r_1424_);
if (v_isSharedCheck_1475_ == 0)
{
lean_object* v_unused_1476_; lean_object* v_unused_1477_; lean_object* v_unused_1478_; lean_object* v_unused_1479_; lean_object* v_unused_1480_; 
v_unused_1476_ = lean_ctor_get(v_r_1424_, 4);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v_r_1424_, 3);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_r_1424_, 2);
lean_dec(v_unused_1478_);
v_unused_1479_ = lean_ctor_get(v_r_1424_, 1);
lean_dec(v_unused_1479_);
v_unused_1480_ = lean_ctor_get(v_r_1424_, 0);
lean_dec(v_unused_1480_);
v___x_1447_ = v_r_1424_;
v_isShared_1448_ = v_isSharedCheck_1475_;
goto v_resetjp_1446_;
}
else
{
lean_dec(v_r_1424_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1475_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___x_1463_; lean_object* v___y_1465_; 
v___x_1449_ = lean_unsigned_to_nat(1u);
v___x_1450_ = lean_nat_add(v___x_1449_, v_size_1420_);
lean_dec(v_size_1420_);
v___x_1451_ = lean_nat_add(v___x_1450_, v_size_1419_);
lean_dec(v___x_1450_);
v___x_1463_ = lean_nat_add(v___x_1449_, v_size_1437_);
if (lean_obj_tag(v_l_1441_) == 0)
{
lean_object* v_size_1473_; 
v_size_1473_ = lean_ctor_get(v_l_1441_, 0);
lean_inc(v_size_1473_);
v___y_1465_ = v_size_1473_;
goto v___jp_1464_;
}
else
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_unsigned_to_nat(0u);
v___y_1465_ = v___x_1474_;
goto v___jp_1464_;
}
v___jp_1452_:
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1456_ = lean_nat_add(v___y_1453_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec(v___y_1453_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 4, v_r_1413_);
lean_ctor_set(v___x_1447_, 3, v_r_1442_);
lean_ctor_set(v___x_1447_, 2, v_v_1411_);
lean_ctor_set(v___x_1447_, 1, v_k_1410_);
lean_ctor_set(v___x_1447_, 0, v___x_1456_);
v___x_1458_ = v___x_1447_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v_r_1442_);
lean_ctor_set(v_reuseFailAlloc_1462_, 4, v_r_1413_);
v___x_1458_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1460_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v___x_1458_);
lean_ctor_set(v___x_1435_, 3, v___y_1454_);
lean_ctor_set(v___x_1435_, 2, v_v_1440_);
lean_ctor_set(v___x_1435_, 1, v_k_1439_);
lean_ctor_set(v___x_1435_, 0, v___x_1451_);
v___x_1460_ = v___x_1435_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_k_1439_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_v_1440_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v___y_1454_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
v___jp_1464_:
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1466_ = lean_nat_add(v___x_1463_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec(v___x_1463_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v_l_1441_);
lean_ctor_set(v___x_1415_, 3, v_l_1423_);
lean_ctor_set(v___x_1415_, 2, v_v_1422_);
lean_ctor_set(v___x_1415_, 1, v_k_1421_);
lean_ctor_set(v___x_1415_, 0, v___x_1466_);
v___x_1468_ = v___x_1415_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_k_1421_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v_v_1422_);
lean_ctor_set(v_reuseFailAlloc_1472_, 3, v_l_1423_);
lean_ctor_set(v_reuseFailAlloc_1472_, 4, v_l_1441_);
v___x_1468_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_nat_add(v___x_1449_, v_size_1419_);
if (lean_obj_tag(v_r_1442_) == 0)
{
lean_object* v_size_1470_; 
v_size_1470_ = lean_ctor_get(v_r_1442_, 0);
lean_inc(v_size_1470_);
v___y_1453_ = v___x_1469_;
v___y_1454_ = v___x_1468_;
v___y_1455_ = v_size_1470_;
goto v___jp_1452_;
}
else
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___y_1453_ = v___x_1469_;
v___y_1454_ = v___x_1468_;
v___y_1455_ = v___x_1471_;
goto v___jp_1452_;
}
}
}
}
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
lean_del_object(v___x_1415_);
v___x_1481_ = lean_unsigned_to_nat(1u);
v___x_1482_ = lean_nat_add(v___x_1481_, v_size_1420_);
lean_dec(v_size_1420_);
v___x_1483_ = lean_nat_add(v___x_1482_, v_size_1419_);
lean_dec(v___x_1482_);
v___x_1484_ = lean_nat_add(v___x_1481_, v_size_1419_);
v___x_1485_ = lean_nat_add(v___x_1484_, v_size_1438_);
lean_dec(v___x_1484_);
lean_inc_ref(v_r_1413_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v_r_1413_);
lean_ctor_set(v___x_1435_, 3, v_r_1424_);
lean_ctor_set(v___x_1435_, 2, v_v_1411_);
lean_ctor_set(v___x_1435_, 1, v_k_1410_);
lean_ctor_set(v___x_1435_, 0, v___x_1485_);
v___x_1487_ = v___x_1435_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_r_1424_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_r_1413_);
v___x_1487_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_isSharedCheck_1494_ = !lean_is_exclusive(v_r_1413_);
if (v_isSharedCheck_1494_ == 0)
{
lean_object* v_unused_1495_; lean_object* v_unused_1496_; lean_object* v_unused_1497_; lean_object* v_unused_1498_; lean_object* v_unused_1499_; 
v_unused_1495_ = lean_ctor_get(v_r_1413_, 4);
lean_dec(v_unused_1495_);
v_unused_1496_ = lean_ctor_get(v_r_1413_, 3);
lean_dec(v_unused_1496_);
v_unused_1497_ = lean_ctor_get(v_r_1413_, 2);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v_r_1413_, 1);
lean_dec(v_unused_1498_);
v_unused_1499_ = lean_ctor_get(v_r_1413_, 0);
lean_dec(v_unused_1499_);
v___x_1489_ = v_r_1413_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_dec(v_r_1413_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 4, v___x_1487_);
lean_ctor_set(v___x_1489_, 3, v_l_1423_);
lean_ctor_set(v___x_1489_, 2, v_v_1422_);
lean_ctor_set(v___x_1489_, 1, v_k_1421_);
lean_ctor_set(v___x_1489_, 0, v___x_1483_);
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_k_1421_);
lean_ctor_set(v_reuseFailAlloc_1493_, 2, v_v_1422_);
lean_ctor_set(v_reuseFailAlloc_1493_, 3, v_l_1423_);
lean_ctor_set(v_reuseFailAlloc_1493_, 4, v___x_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_dec_ref_known(v_l_1423_, 5);
lean_del_object(v___x_1435_);
lean_dec(v_v_1422_);
lean_dec(v_k_1421_);
lean_dec(v_size_1420_);
lean_dec_ref_known(v_r_1413_, 5);
lean_del_object(v___x_1415_);
lean_dec(v_v_1411_);
lean_dec(v_k_1410_);
v___x_1501_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3);
v___x_1502_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1501_);
return v___x_1502_;
}
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_del_object(v___x_1435_);
lean_dec(v_r_1424_);
lean_dec(v_v_1422_);
lean_dec(v_k_1421_);
lean_dec(v_size_1420_);
lean_dec_ref_known(v_r_1413_, 5);
lean_del_object(v___x_1415_);
lean_dec(v_v_1411_);
lean_dec(v_k_1410_);
v___x_1503_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4);
v___x_1504_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1503_);
return v___x_1504_;
}
}
}
}
else
{
lean_object* v_size_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v_size_1511_ = lean_ctor_get(v_r_1413_, 0);
v___x_1512_ = lean_unsigned_to_nat(1u);
v___x_1513_ = lean_nat_add(v___x_1512_, v_size_1511_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 3, v___x_1418_);
lean_ctor_set(v___x_1415_, 0, v___x_1513_);
v___x_1515_ = v___x_1415_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1516_, 4, v_r_1413_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
else
{
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_l_1517_; 
v_l_1517_ = lean_ctor_get(v___x_1418_, 3);
if (lean_obj_tag(v_l_1517_) == 0)
{
lean_object* v_r_1518_; 
lean_inc_ref(v_l_1517_);
v_r_1518_ = lean_ctor_get(v___x_1418_, 4);
lean_inc(v_r_1518_);
if (lean_obj_tag(v_r_1518_) == 0)
{
lean_object* v_size_1519_; lean_object* v_k_1520_; lean_object* v_v_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1535_; 
v_size_1519_ = lean_ctor_get(v___x_1418_, 0);
v_k_1520_ = lean_ctor_get(v___x_1418_, 1);
v_v_1521_ = lean_ctor_get(v___x_1418_, 2);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; lean_object* v_unused_1537_; 
v_unused_1536_ = lean_ctor_get(v___x_1418_, 4);
lean_dec(v_unused_1536_);
v_unused_1537_ = lean_ctor_get(v___x_1418_, 3);
lean_dec(v_unused_1537_);
v___x_1523_ = v___x_1418_;
v_isShared_1524_ = v_isSharedCheck_1535_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_v_1521_);
lean_inc(v_k_1520_);
lean_inc(v_size_1519_);
lean_dec(v___x_1418_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1535_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v_size_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
v_size_1525_ = lean_ctor_get(v_r_1518_, 0);
v___x_1526_ = lean_unsigned_to_nat(1u);
v___x_1527_ = lean_nat_add(v___x_1526_, v_size_1519_);
lean_dec(v_size_1519_);
v___x_1528_ = lean_nat_add(v___x_1526_, v_size_1525_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 4, v_r_1413_);
lean_ctor_set(v___x_1523_, 3, v_r_1518_);
lean_ctor_set(v___x_1523_, 2, v_v_1411_);
lean_ctor_set(v___x_1523_, 1, v_k_1410_);
lean_ctor_set(v___x_1523_, 0, v___x_1528_);
v___x_1530_ = v___x_1523_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1534_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1534_, 3, v_r_1518_);
lean_ctor_set(v_reuseFailAlloc_1534_, 4, v_r_1413_);
v___x_1530_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1532_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v___x_1530_);
lean_ctor_set(v___x_1415_, 3, v_l_1517_);
lean_ctor_set(v___x_1415_, 2, v_v_1521_);
lean_ctor_set(v___x_1415_, 1, v_k_1520_);
lean_ctor_set(v___x_1415_, 0, v___x_1527_);
v___x_1532_ = v___x_1415_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_k_1520_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_v_1521_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_l_1517_);
lean_ctor_set(v_reuseFailAlloc_1533_, 4, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
else
{
lean_object* v_k_1538_; lean_object* v_v_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1551_; 
v_k_1538_ = lean_ctor_get(v___x_1418_, 1);
v_v_1539_ = lean_ctor_get(v___x_1418_, 2);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; lean_object* v_unused_1553_; lean_object* v_unused_1554_; 
v_unused_1552_ = lean_ctor_get(v___x_1418_, 4);
lean_dec(v_unused_1552_);
v_unused_1553_ = lean_ctor_get(v___x_1418_, 3);
lean_dec(v_unused_1553_);
v_unused_1554_ = lean_ctor_get(v___x_1418_, 0);
lean_dec(v_unused_1554_);
v___x_1541_ = v___x_1418_;
v_isShared_1542_ = v_isSharedCheck_1551_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_v_1539_);
lean_inc(v_k_1538_);
lean_dec(v___x_1418_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1551_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1543_ = lean_unsigned_to_nat(3u);
v___x_1544_ = lean_unsigned_to_nat(1u);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 3, v_r_1518_);
lean_ctor_set(v___x_1541_, 2, v_v_1411_);
lean_ctor_set(v___x_1541_, 1, v_k_1410_);
lean_ctor_set(v___x_1541_, 0, v___x_1544_);
v___x_1546_ = v___x_1541_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1550_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1550_, 3, v_r_1518_);
lean_ctor_set(v_reuseFailAlloc_1550_, 4, v_r_1518_);
v___x_1546_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1548_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v___x_1546_);
lean_ctor_set(v___x_1415_, 3, v_l_1517_);
lean_ctor_set(v___x_1415_, 2, v_v_1539_);
lean_ctor_set(v___x_1415_, 1, v_k_1538_);
lean_ctor_set(v___x_1415_, 0, v___x_1543_);
v___x_1548_ = v___x_1415_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_k_1538_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_v_1539_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v_l_1517_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
else
{
lean_object* v_r_1555_; 
v_r_1555_ = lean_ctor_get(v___x_1418_, 4);
lean_inc(v_r_1555_);
if (lean_obj_tag(v_r_1555_) == 0)
{
lean_object* v_k_1556_; lean_object* v_v_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1581_; 
lean_inc(v_l_1517_);
v_k_1556_ = lean_ctor_get(v___x_1418_, 1);
v_v_1557_ = lean_ctor_get(v___x_1418_, 2);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1581_ == 0)
{
lean_object* v_unused_1582_; lean_object* v_unused_1583_; lean_object* v_unused_1584_; 
v_unused_1582_ = lean_ctor_get(v___x_1418_, 4);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v___x_1418_, 3);
lean_dec(v_unused_1583_);
v_unused_1584_ = lean_ctor_get(v___x_1418_, 0);
lean_dec(v_unused_1584_);
v___x_1559_ = v___x_1418_;
v_isShared_1560_ = v_isSharedCheck_1581_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_v_1557_);
lean_inc(v_k_1556_);
lean_dec(v___x_1418_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1581_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v_k_1561_; lean_object* v_v_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1577_; 
v_k_1561_ = lean_ctor_get(v_r_1555_, 1);
v_v_1562_ = lean_ctor_get(v_r_1555_, 2);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_r_1555_);
if (v_isSharedCheck_1577_ == 0)
{
lean_object* v_unused_1578_; lean_object* v_unused_1579_; lean_object* v_unused_1580_; 
v_unused_1578_ = lean_ctor_get(v_r_1555_, 4);
lean_dec(v_unused_1578_);
v_unused_1579_ = lean_ctor_get(v_r_1555_, 3);
lean_dec(v_unused_1579_);
v_unused_1580_ = lean_ctor_get(v_r_1555_, 0);
lean_dec(v_unused_1580_);
v___x_1564_ = v_r_1555_;
v_isShared_1565_ = v_isSharedCheck_1577_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_v_1562_);
lean_inc(v_k_1561_);
lean_dec(v_r_1555_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1577_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1566_ = lean_unsigned_to_nat(3u);
v___x_1567_ = lean_unsigned_to_nat(1u);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 4, v_l_1517_);
lean_ctor_set(v___x_1564_, 3, v_l_1517_);
lean_ctor_set(v___x_1564_, 2, v_v_1557_);
lean_ctor_set(v___x_1564_, 1, v_k_1556_);
lean_ctor_set(v___x_1564_, 0, v___x_1567_);
v___x_1569_ = v___x_1564_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_k_1556_);
lean_ctor_set(v_reuseFailAlloc_1576_, 2, v_v_1557_);
lean_ctor_set(v_reuseFailAlloc_1576_, 3, v_l_1517_);
lean_ctor_set(v_reuseFailAlloc_1576_, 4, v_l_1517_);
v___x_1569_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1571_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 4, v_l_1517_);
lean_ctor_set(v___x_1559_, 2, v_v_1411_);
lean_ctor_set(v___x_1559_, 1, v_k_1410_);
lean_ctor_set(v___x_1559_, 0, v___x_1567_);
v___x_1571_ = v___x_1559_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1575_, 3, v_l_1517_);
lean_ctor_set(v_reuseFailAlloc_1575_, 4, v_l_1517_);
v___x_1571_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
lean_object* v___x_1573_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v___x_1571_);
lean_ctor_set(v___x_1415_, 3, v___x_1569_);
lean_ctor_set(v___x_1415_, 2, v_v_1562_);
lean_ctor_set(v___x_1415_, 1, v_k_1561_);
lean_ctor_set(v___x_1415_, 0, v___x_1566_);
v___x_1573_ = v___x_1415_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_k_1561_);
lean_ctor_set(v_reuseFailAlloc_1574_, 2, v_v_1562_);
lean_ctor_set(v_reuseFailAlloc_1574_, 3, v___x_1569_);
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
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1585_ = lean_unsigned_to_nat(2u);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v_r_1555_);
lean_ctor_set(v___x_1415_, 3, v___x_1418_);
lean_ctor_set(v___x_1415_, 0, v___x_1585_);
v___x_1587_ = v___x_1415_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1588_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1588_, 3, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1588_, 4, v_r_1555_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1589_ = lean_unsigned_to_nat(1u);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v___x_1418_);
lean_ctor_set(v___x_1415_, 3, v___x_1418_);
lean_ctor_set(v___x_1415_, 0, v___x_1589_);
v___x_1591_ = v___x_1415_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1592_, 3, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1592_, 4, v___x_1418_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
case 1:
{
lean_object* v___x_1594_; 
lean_dec(v_v_1411_);
lean_dec(v_k_1410_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 2, v_v_1407_);
lean_ctor_set(v___x_1415_, 1, v_k_1406_);
v___x_1594_ = v___x_1415_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_size_1409_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_k_1406_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_v_1407_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v_l_1412_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v_r_1413_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
default: 
{
lean_object* v___x_1596_; 
lean_dec(v_size_1409_);
v___x_1596_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1406_, v_v_1407_, v_r_1413_);
if (lean_obj_tag(v_l_1412_) == 0)
{
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_size_1597_; lean_object* v_size_1598_; lean_object* v_k_1599_; lean_object* v_v_1600_; lean_object* v_l_1601_; lean_object* v_r_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v_size_1597_ = lean_ctor_get(v_l_1412_, 0);
v_size_1598_ = lean_ctor_get(v___x_1596_, 0);
v_k_1599_ = lean_ctor_get(v___x_1596_, 1);
v_v_1600_ = lean_ctor_get(v___x_1596_, 2);
v_l_1601_ = lean_ctor_get(v___x_1596_, 3);
lean_inc(v_l_1601_);
v_r_1602_ = lean_ctor_get(v___x_1596_, 4);
v___x_1603_ = lean_unsigned_to_nat(3u);
v___x_1604_ = lean_nat_mul(v___x_1603_, v_size_1597_);
v___x_1605_ = lean_nat_dec_lt(v___x_1604_, v_size_1598_);
lean_dec(v___x_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1610_; 
lean_dec(v_l_1601_);
v___x_1606_ = lean_unsigned_to_nat(1u);
v___x_1607_ = lean_nat_add(v___x_1606_, v_size_1597_);
v___x_1608_ = lean_nat_add(v___x_1607_, v_size_1598_);
lean_dec(v___x_1607_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v___x_1596_);
lean_ctor_set(v___x_1415_, 0, v___x_1608_);
v___x_1610_ = v___x_1415_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v_l_1412_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v___x_1596_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
else
{
lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1681_; 
lean_inc(v_r_1602_);
lean_inc(v_v_1600_);
lean_inc(v_k_1599_);
lean_inc(v_size_1598_);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1681_ == 0)
{
lean_object* v_unused_1682_; lean_object* v_unused_1683_; lean_object* v_unused_1684_; lean_object* v_unused_1685_; lean_object* v_unused_1686_; 
v_unused_1682_ = lean_ctor_get(v___x_1596_, 4);
lean_dec(v_unused_1682_);
v_unused_1683_ = lean_ctor_get(v___x_1596_, 3);
lean_dec(v_unused_1683_);
v_unused_1684_ = lean_ctor_get(v___x_1596_, 2);
lean_dec(v_unused_1684_);
v_unused_1685_ = lean_ctor_get(v___x_1596_, 1);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v___x_1596_, 0);
lean_dec(v_unused_1686_);
v___x_1613_ = v___x_1596_;
v_isShared_1614_ = v_isSharedCheck_1681_;
goto v_resetjp_1612_;
}
else
{
lean_dec(v___x_1596_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1681_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
if (lean_obj_tag(v_l_1601_) == 0)
{
if (lean_obj_tag(v_r_1602_) == 0)
{
lean_object* v_size_1615_; lean_object* v_k_1616_; lean_object* v_v_1617_; lean_object* v_l_1618_; lean_object* v_r_1619_; lean_object* v_size_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; 
v_size_1615_ = lean_ctor_get(v_l_1601_, 0);
v_k_1616_ = lean_ctor_get(v_l_1601_, 1);
v_v_1617_ = lean_ctor_get(v_l_1601_, 2);
v_l_1618_ = lean_ctor_get(v_l_1601_, 3);
v_r_1619_ = lean_ctor_get(v_l_1601_, 4);
v_size_1620_ = lean_ctor_get(v_r_1602_, 0);
v___x_1621_ = lean_unsigned_to_nat(2u);
v___x_1622_ = lean_nat_mul(v___x_1621_, v_size_1620_);
v___x_1623_ = lean_nat_dec_lt(v_size_1615_, v___x_1622_);
lean_dec(v___x_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1652_; 
lean_inc(v_r_1619_);
lean_inc(v_l_1618_);
lean_inc(v_v_1617_);
lean_inc(v_k_1616_);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_l_1601_);
if (v_isSharedCheck_1652_ == 0)
{
lean_object* v_unused_1653_; lean_object* v_unused_1654_; lean_object* v_unused_1655_; lean_object* v_unused_1656_; lean_object* v_unused_1657_; 
v_unused_1653_ = lean_ctor_get(v_l_1601_, 4);
lean_dec(v_unused_1653_);
v_unused_1654_ = lean_ctor_get(v_l_1601_, 3);
lean_dec(v_unused_1654_);
v_unused_1655_ = lean_ctor_get(v_l_1601_, 2);
lean_dec(v_unused_1655_);
v_unused_1656_ = lean_ctor_get(v_l_1601_, 1);
lean_dec(v_unused_1656_);
v_unused_1657_ = lean_ctor_get(v_l_1601_, 0);
lean_dec(v_unused_1657_);
v___x_1625_ = v_l_1601_;
v_isShared_1626_ = v_isSharedCheck_1652_;
goto v_resetjp_1624_;
}
else
{
lean_dec(v_l_1601_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1652_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1642_; 
v___x_1627_ = lean_unsigned_to_nat(1u);
v___x_1628_ = lean_nat_add(v___x_1627_, v_size_1597_);
v___x_1629_ = lean_nat_add(v___x_1628_, v_size_1598_);
lean_dec(v_size_1598_);
if (lean_obj_tag(v_l_1618_) == 0)
{
lean_object* v_size_1650_; 
v_size_1650_ = lean_ctor_get(v_l_1618_, 0);
lean_inc(v_size_1650_);
v___y_1642_ = v_size_1650_;
goto v___jp_1641_;
}
else
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_unsigned_to_nat(0u);
v___y_1642_ = v___x_1651_;
goto v___jp_1641_;
}
v___jp_1630_:
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1634_ = lean_nat_add(v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec(v___y_1632_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 4, v_r_1602_);
lean_ctor_set(v___x_1625_, 3, v_r_1619_);
lean_ctor_set(v___x_1625_, 2, v_v_1600_);
lean_ctor_set(v___x_1625_, 1, v_k_1599_);
lean_ctor_set(v___x_1625_, 0, v___x_1634_);
v___x_1636_ = v___x_1625_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_k_1599_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_v_1600_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v_r_1619_);
lean_ctor_set(v_reuseFailAlloc_1640_, 4, v_r_1602_);
v___x_1636_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1638_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 4, v___x_1636_);
lean_ctor_set(v___x_1613_, 3, v___y_1631_);
lean_ctor_set(v___x_1613_, 2, v_v_1617_);
lean_ctor_set(v___x_1613_, 1, v_k_1616_);
lean_ctor_set(v___x_1613_, 0, v___x_1629_);
v___x_1638_ = v___x_1613_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_k_1616_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_v_1617_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v___y_1631_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
v___jp_1641_:
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1643_ = lean_nat_add(v___x_1628_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec(v___x_1628_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v_l_1618_);
lean_ctor_set(v___x_1415_, 0, v___x_1643_);
v___x_1645_ = v___x_1415_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1649_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1649_, 3, v_l_1412_);
lean_ctor_set(v_reuseFailAlloc_1649_, 4, v_l_1618_);
v___x_1645_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1646_; 
v___x_1646_ = lean_nat_add(v___x_1627_, v_size_1620_);
if (lean_obj_tag(v_r_1619_) == 0)
{
lean_object* v_size_1647_; 
v_size_1647_ = lean_ctor_get(v_r_1619_, 0);
lean_inc(v_size_1647_);
v___y_1631_ = v___x_1645_;
v___y_1632_ = v___x_1646_;
v___y_1633_ = v_size_1647_;
goto v___jp_1630_;
}
else
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_unsigned_to_nat(0u);
v___y_1631_ = v___x_1645_;
v___y_1632_ = v___x_1646_;
v___y_1633_ = v___x_1648_;
goto v___jp_1630_;
}
}
}
}
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
lean_del_object(v___x_1415_);
v___x_1658_ = lean_unsigned_to_nat(1u);
v___x_1659_ = lean_nat_add(v___x_1658_, v_size_1597_);
v___x_1660_ = lean_nat_add(v___x_1659_, v_size_1598_);
lean_dec(v_size_1598_);
v___x_1661_ = lean_nat_add(v___x_1659_, v_size_1615_);
lean_dec(v___x_1659_);
lean_inc_ref(v_l_1412_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 4, v_l_1601_);
lean_ctor_set(v___x_1613_, 3, v_l_1412_);
lean_ctor_set(v___x_1613_, 2, v_v_1411_);
lean_ctor_set(v___x_1613_, 1, v_k_1410_);
lean_ctor_set(v___x_1613_, 0, v___x_1661_);
v___x_1663_ = v___x_1613_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1676_, 3, v_l_1412_);
lean_ctor_set(v_reuseFailAlloc_1676_, 4, v_l_1601_);
v___x_1663_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
v_isSharedCheck_1670_ = !lean_is_exclusive(v_l_1412_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; lean_object* v_unused_1672_; lean_object* v_unused_1673_; lean_object* v_unused_1674_; lean_object* v_unused_1675_; 
v_unused_1671_ = lean_ctor_get(v_l_1412_, 4);
lean_dec(v_unused_1671_);
v_unused_1672_ = lean_ctor_get(v_l_1412_, 3);
lean_dec(v_unused_1672_);
v_unused_1673_ = lean_ctor_get(v_l_1412_, 2);
lean_dec(v_unused_1673_);
v_unused_1674_ = lean_ctor_get(v_l_1412_, 1);
lean_dec(v_unused_1674_);
v_unused_1675_ = lean_ctor_get(v_l_1412_, 0);
lean_dec(v_unused_1675_);
v___x_1665_ = v_l_1412_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_dec(v_l_1412_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 4, v_r_1602_);
lean_ctor_set(v___x_1665_, 3, v___x_1663_);
lean_ctor_set(v___x_1665_, 2, v_v_1600_);
lean_ctor_set(v___x_1665_, 1, v_k_1599_);
lean_ctor_set(v___x_1665_, 0, v___x_1660_);
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_k_1599_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v_v_1600_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1669_, 4, v_r_1602_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec_ref_known(v_l_1601_, 5);
lean_del_object(v___x_1613_);
lean_dec(v_v_1600_);
lean_dec(v_k_1599_);
lean_dec(v_size_1598_);
lean_dec_ref_known(v_l_1412_, 5);
lean_del_object(v___x_1415_);
lean_dec(v_v_1411_);
lean_dec(v_k_1410_);
v___x_1677_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7);
v___x_1678_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1677_);
return v___x_1678_;
}
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_del_object(v___x_1613_);
lean_dec(v_r_1602_);
lean_dec(v_v_1600_);
lean_dec(v_k_1599_);
lean_dec(v_size_1598_);
lean_dec_ref_known(v_l_1412_, 5);
lean_del_object(v___x_1415_);
lean_dec(v_v_1411_);
lean_dec(v_k_1410_);
v___x_1679_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8);
v___x_1680_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1679_);
return v___x_1680_;
}
}
}
}
else
{
lean_object* v_size_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
v_size_1687_ = lean_ctor_get(v_l_1412_, 0);
v___x_1688_ = lean_unsigned_to_nat(1u);
v___x_1689_ = lean_nat_add(v___x_1688_, v_size_1687_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v___x_1596_);
lean_ctor_set(v___x_1415_, 0, v___x_1689_);
v___x_1691_ = v___x_1415_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1692_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1692_, 3, v_l_1412_);
lean_ctor_set(v_reuseFailAlloc_1692_, 4, v___x_1596_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
else
{
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_l_1693_; 
v_l_1693_ = lean_ctor_get(v___x_1596_, 3);
lean_inc(v_l_1693_);
if (lean_obj_tag(v_l_1693_) == 0)
{
lean_object* v_r_1694_; 
v_r_1694_ = lean_ctor_get(v___x_1596_, 4);
lean_inc(v_r_1694_);
if (lean_obj_tag(v_r_1694_) == 0)
{
lean_object* v_size_1695_; lean_object* v_k_1696_; lean_object* v_v_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1711_; 
v_size_1695_ = lean_ctor_get(v___x_1596_, 0);
v_k_1696_ = lean_ctor_get(v___x_1596_, 1);
v_v_1697_ = lean_ctor_get(v___x_1596_, 2);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1711_ == 0)
{
lean_object* v_unused_1712_; lean_object* v_unused_1713_; 
v_unused_1712_ = lean_ctor_get(v___x_1596_, 4);
lean_dec(v_unused_1712_);
v_unused_1713_ = lean_ctor_get(v___x_1596_, 3);
lean_dec(v_unused_1713_);
v___x_1699_ = v___x_1596_;
v_isShared_1700_ = v_isSharedCheck_1711_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_v_1697_);
lean_inc(v_k_1696_);
lean_inc(v_size_1695_);
lean_dec(v___x_1596_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1711_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v_size_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
v_size_1701_ = lean_ctor_get(v_l_1693_, 0);
v___x_1702_ = lean_unsigned_to_nat(1u);
v___x_1703_ = lean_nat_add(v___x_1702_, v_size_1695_);
lean_dec(v_size_1695_);
v___x_1704_ = lean_nat_add(v___x_1702_, v_size_1701_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v_l_1693_);
lean_ctor_set(v___x_1699_, 3, v_l_1412_);
lean_ctor_set(v___x_1699_, 2, v_v_1411_);
lean_ctor_set(v___x_1699_, 1, v_k_1410_);
lean_ctor_set(v___x_1699_, 0, v___x_1704_);
v___x_1706_ = v___x_1699_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1710_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1710_, 3, v_l_1412_);
lean_ctor_set(v_reuseFailAlloc_1710_, 4, v_l_1693_);
v___x_1706_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1708_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v_r_1694_);
lean_ctor_set(v___x_1415_, 3, v___x_1706_);
lean_ctor_set(v___x_1415_, 2, v_v_1697_);
lean_ctor_set(v___x_1415_, 1, v_k_1696_);
lean_ctor_set(v___x_1415_, 0, v___x_1703_);
v___x_1708_ = v___x_1415_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_k_1696_);
lean_ctor_set(v_reuseFailAlloc_1709_, 2, v_v_1697_);
lean_ctor_set(v_reuseFailAlloc_1709_, 3, v___x_1706_);
lean_ctor_set(v_reuseFailAlloc_1709_, 4, v_r_1694_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v_k_1714_; lean_object* v_v_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1739_; 
v_k_1714_ = lean_ctor_get(v___x_1596_, 1);
v_v_1715_ = lean_ctor_get(v___x_1596_, 2);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; lean_object* v_unused_1741_; lean_object* v_unused_1742_; 
v_unused_1740_ = lean_ctor_get(v___x_1596_, 4);
lean_dec(v_unused_1740_);
v_unused_1741_ = lean_ctor_get(v___x_1596_, 3);
lean_dec(v_unused_1741_);
v_unused_1742_ = lean_ctor_get(v___x_1596_, 0);
lean_dec(v_unused_1742_);
v___x_1717_ = v___x_1596_;
v_isShared_1718_ = v_isSharedCheck_1739_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_v_1715_);
lean_inc(v_k_1714_);
lean_dec(v___x_1596_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1739_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v_k_1719_; lean_object* v_v_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1735_; 
v_k_1719_ = lean_ctor_get(v_l_1693_, 1);
v_v_1720_ = lean_ctor_get(v_l_1693_, 2);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_l_1693_);
if (v_isSharedCheck_1735_ == 0)
{
lean_object* v_unused_1736_; lean_object* v_unused_1737_; lean_object* v_unused_1738_; 
v_unused_1736_ = lean_ctor_get(v_l_1693_, 4);
lean_dec(v_unused_1736_);
v_unused_1737_ = lean_ctor_get(v_l_1693_, 3);
lean_dec(v_unused_1737_);
v_unused_1738_ = lean_ctor_get(v_l_1693_, 0);
lean_dec(v_unused_1738_);
v___x_1722_ = v_l_1693_;
v_isShared_1723_ = v_isSharedCheck_1735_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_v_1720_);
lean_inc(v_k_1719_);
lean_dec(v_l_1693_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1735_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1724_ = lean_unsigned_to_nat(3u);
v___x_1725_ = lean_unsigned_to_nat(1u);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 4, v_r_1694_);
lean_ctor_set(v___x_1722_, 3, v_r_1694_);
lean_ctor_set(v___x_1722_, 2, v_v_1411_);
lean_ctor_set(v___x_1722_, 1, v_k_1410_);
lean_ctor_set(v___x_1722_, 0, v___x_1725_);
v___x_1727_ = v___x_1722_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1734_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1734_, 3, v_r_1694_);
lean_ctor_set(v_reuseFailAlloc_1734_, 4, v_r_1694_);
v___x_1727_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1729_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 3, v_r_1694_);
lean_ctor_set(v___x_1717_, 0, v___x_1725_);
v___x_1729_ = v___x_1717_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_k_1714_);
lean_ctor_set(v_reuseFailAlloc_1733_, 2, v_v_1715_);
lean_ctor_set(v_reuseFailAlloc_1733_, 3, v_r_1694_);
lean_ctor_set(v_reuseFailAlloc_1733_, 4, v_r_1694_);
v___x_1729_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1731_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v___x_1729_);
lean_ctor_set(v___x_1415_, 3, v___x_1727_);
lean_ctor_set(v___x_1415_, 2, v_v_1720_);
lean_ctor_set(v___x_1415_, 1, v_k_1719_);
lean_ctor_set(v___x_1415_, 0, v___x_1724_);
v___x_1731_ = v___x_1415_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_k_1719_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_v_1720_);
lean_ctor_set(v_reuseFailAlloc_1732_, 3, v___x_1727_);
lean_ctor_set(v_reuseFailAlloc_1732_, 4, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1743_; 
v_r_1743_ = lean_ctor_get(v___x_1596_, 4);
lean_inc(v_r_1743_);
if (lean_obj_tag(v_r_1743_) == 0)
{
lean_object* v_k_1744_; lean_object* v_v_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1757_; 
v_k_1744_ = lean_ctor_get(v___x_1596_, 1);
v_v_1745_ = lean_ctor_get(v___x_1596_, 2);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1757_ == 0)
{
lean_object* v_unused_1758_; lean_object* v_unused_1759_; lean_object* v_unused_1760_; 
v_unused_1758_ = lean_ctor_get(v___x_1596_, 4);
lean_dec(v_unused_1758_);
v_unused_1759_ = lean_ctor_get(v___x_1596_, 3);
lean_dec(v_unused_1759_);
v_unused_1760_ = lean_ctor_get(v___x_1596_, 0);
lean_dec(v_unused_1760_);
v___x_1747_ = v___x_1596_;
v_isShared_1748_ = v_isSharedCheck_1757_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_v_1745_);
lean_inc(v_k_1744_);
lean_dec(v___x_1596_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1757_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1749_ = lean_unsigned_to_nat(3u);
v___x_1750_ = lean_unsigned_to_nat(1u);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 4, v_l_1693_);
lean_ctor_set(v___x_1747_, 2, v_v_1411_);
lean_ctor_set(v___x_1747_, 1, v_k_1410_);
lean_ctor_set(v___x_1747_, 0, v___x_1750_);
v___x_1752_ = v___x_1747_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1756_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1756_, 3, v_l_1693_);
lean_ctor_set(v_reuseFailAlloc_1756_, 4, v_l_1693_);
v___x_1752_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1754_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v_r_1743_);
lean_ctor_set(v___x_1415_, 3, v___x_1752_);
lean_ctor_set(v___x_1415_, 2, v_v_1745_);
lean_ctor_set(v___x_1415_, 1, v_k_1744_);
lean_ctor_set(v___x_1415_, 0, v___x_1749_);
v___x_1754_ = v___x_1415_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_k_1744_);
lean_ctor_set(v_reuseFailAlloc_1755_, 2, v_v_1745_);
lean_ctor_set(v_reuseFailAlloc_1755_, 3, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1755_, 4, v_r_1743_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1761_ = lean_unsigned_to_nat(2u);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v___x_1596_);
lean_ctor_set(v___x_1415_, 3, v_r_1743_);
lean_ctor_set(v___x_1415_, 0, v___x_1761_);
v___x_1763_ = v___x_1415_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1764_, 3, v_r_1743_);
lean_ctor_set(v_reuseFailAlloc_1764_, 4, v___x_1596_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1765_ = lean_unsigned_to_nat(1u);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v___x_1596_);
lean_ctor_set(v___x_1415_, 3, v___x_1596_);
lean_ctor_set(v___x_1415_, 0, v___x_1765_);
v___x_1767_ = v___x_1415_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1768_, 4, v___x_1596_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_unsigned_to_nat(1u);
v___x_1771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v_k_1406_);
lean_ctor_set(v___x_1771_, 2, v_v_1407_);
lean_ctor_set(v___x_1771_, 3, v_t_1408_);
lean_ctor_set(v___x_1771_, 4, v_t_1408_);
return v___x_1771_;
}
}
}
static lean_object* _init_l_Lean_Json_setObjVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1774_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__1));
v___x_1775_ = lean_unsigned_to_nat(21u);
v___x_1776_ = lean_unsigned_to_nat(292u);
v___x_1777_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__0));
v___x_1778_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_1779_ = l_mkPanicMessageWithDecl(v___x_1778_, v___x_1777_, v___x_1776_, v___x_1775_, v___x_1774_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjVal_x21(lean_object* v_x_1780_, lean_object* v_x_1781_, lean_object* v_x_1782_){
_start:
{
if (lean_obj_tag(v_x_1780_) == 5)
{
lean_object* v_kvPairs_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1791_; 
v_kvPairs_1783_ = lean_ctor_get(v_x_1780_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_x_1780_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1785_ = v_x_1780_;
v_isShared_1786_ = v_isSharedCheck_1791_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_kvPairs_1783_);
lean_dec(v_x_1780_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1791_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1787_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_x_1781_, v_x_1782_, v_kvPairs_1783_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1787_);
v___x_1789_ = v___x_1785_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_dec(v_x_1782_);
lean_dec_ref(v_x_1781_);
lean_dec(v_x_1780_);
v___x_1792_ = lean_obj_once(&l_Lean_Json_setObjVal_x21___closed__2, &l_Lean_Json_setObjVal_x21___closed__2_once, _init_l_Lean_Json_setObjVal_x21___closed__2);
v___x_1793_ = l_panic___at___00Lean_Json_setObjVal_x21_spec__1(v___x_1792_);
return v___x_1793_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0(lean_object* v_00_u03b2_1794_, lean_object* v_msg_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v_msg_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0(lean_object* v_00_u03b2_1797_, lean_object* v_k_1798_, lean_object* v_v_1799_, lean_object* v_t_1800_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1798_, v_v_1799_, v_t_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(lean_object* v_init_1802_, lean_object* v_x_1803_){
_start:
{
if (lean_obj_tag(v_x_1803_) == 0)
{
lean_object* v_k_1804_; lean_object* v_v_1805_; lean_object* v_l_1806_; lean_object* v_r_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v_k_1804_ = lean_ctor_get(v_x_1803_, 1);
lean_inc(v_k_1804_);
v_v_1805_ = lean_ctor_get(v_x_1803_, 2);
lean_inc(v_v_1805_);
v_l_1806_ = lean_ctor_get(v_x_1803_, 3);
lean_inc(v_l_1806_);
v_r_1807_ = lean_ctor_get(v_x_1803_, 4);
lean_inc(v_r_1807_);
lean_dec_ref_known(v_x_1803_, 5);
v___x_1808_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1802_, v_l_1806_);
v___x_1809_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1804_, v_v_1805_, v___x_1808_);
v_init_1802_ = v___x_1809_;
v_x_1803_ = v_r_1807_;
goto _start;
}
else
{
return v_init_1802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mergeObj(lean_object* v_x_1811_, lean_object* v_x_1812_){
_start:
{
if (lean_obj_tag(v_x_1811_) == 5)
{
if (lean_obj_tag(v_x_1812_) == 5)
{
lean_object* v_kvPairs_1813_; lean_object* v_kvPairs_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1822_; 
v_kvPairs_1813_ = lean_ctor_get(v_x_1811_, 0);
lean_inc(v_kvPairs_1813_);
lean_dec_ref_known(v_x_1811_, 1);
v_kvPairs_1814_ = lean_ctor_get(v_x_1812_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_x_1812_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1816_ = v_x_1812_;
v_isShared_1817_ = v_isSharedCheck_1822_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_kvPairs_1814_);
lean_dec(v_x_1812_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1822_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1818_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_kvPairs_1813_, v_kvPairs_1814_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1818_);
v___x_1820_ = v___x_1816_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
else
{
lean_dec_ref_known(v_x_1811_, 1);
return v_x_1812_;
}
}
else
{
lean_dec(v_x_1811_);
return v_x_1812_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0(lean_object* v_init_1823_, lean_object* v_t_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1823_, v_t_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___impl(lean_object* v_x_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = lean_obj_tag_nat(v_x_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___impl___boxed(lean_object* v_x_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_Json_Structured_ctorIdx___impl(v_x_1828_);
lean_dec_ref(v_x_1828_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___redArg(lean_object* v_t_1830_, lean_object* v_k_1831_){
_start:
{
if (lean_obj_tag(v_t_1830_) == 0)
{
lean_object* v_elems_1832_; lean_object* v___x_1833_; 
v_elems_1832_ = lean_ctor_get(v_t_1830_, 0);
lean_inc_ref(v_elems_1832_);
lean_dec_ref_known(v_t_1830_, 1);
v___x_1833_ = lean_apply_1(v_k_1831_, v_elems_1832_);
return v___x_1833_;
}
else
{
lean_object* v_kvPairs_1834_; lean_object* v___x_1835_; 
v_kvPairs_1834_ = lean_ctor_get(v_t_1830_, 0);
lean_inc(v_kvPairs_1834_);
lean_dec_ref_known(v_t_1830_, 1);
v___x_1835_ = lean_apply_1(v_k_1831_, v_kvPairs_1834_);
return v___x_1835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim(lean_object* v_motive_1836_, lean_object* v_ctorIdx_1837_, lean_object* v_t_1838_, lean_object* v_h_1839_, lean_object* v_k_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1838_, v_k_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___boxed(lean_object* v_motive_1842_, lean_object* v_ctorIdx_1843_, lean_object* v_t_1844_, lean_object* v_h_1845_, lean_object* v_k_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_Json_Structured_ctorElim(v_motive_1842_, v_ctorIdx_1843_, v_t_1844_, v_h_1845_, v_k_1846_);
lean_dec(v_ctorIdx_1843_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim___redArg(lean_object* v_t_1848_, lean_object* v_arr_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1848_, v_arr_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim(lean_object* v_motive_1851_, lean_object* v_t_1852_, lean_object* v_h_1853_, lean_object* v_arr_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1852_, v_arr_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim___redArg(lean_object* v_t_1856_, lean_object* v_obj_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1856_, v_obj_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim(lean_object* v_motive_1859_, lean_object* v_t_1860_, lean_object* v_h_1861_, lean_object* v_obj_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1860_, v_obj_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeArrayStructured___lam__0(lean_object* v_elems_1864_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v_elems_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeRawStringStructured___lam__0(lean_object* v_kvPairs_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1869_, 0, v_kvPairs_1868_);
return v___x_1869_;
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
