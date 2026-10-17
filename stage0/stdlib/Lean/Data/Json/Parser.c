// Lean compiler output
// Module: Lean.Data.Json.Parser
// Imports: public import Lean.Data.Json.Basic public import Std.Internal.Parsec
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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint32_t lean_uint32_sub(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint16_t lean_uint32_to_uint16(uint32_t);
uint16_t lean_uint16_shift_left(uint16_t, uint16_t);
uint16_t lean_uint16_lor(uint16_t, uint16_t);
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
uint32_t lean_uint16_to_uint32(uint16_t);
uint32_t lean_uint32_land(uint32_t, uint32_t);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_shiftl(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_shiftr(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lean_Json_Parser_hexChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid hex character"};
static const lean_object* l_Lean_Json_Parser_hexChar___closed__0 = (const lean_object*)&l_Lean_Json_Parser_hexChar___closed__0_value;
static const lean_ctor_object l_Lean_Json_Parser_hexChar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_hexChar___closed__0_value)}};
static const lean_object* l_Lean_Json_Parser_hexChar___closed__1 = (const lean_object*)&l_Lean_Json_Parser_hexChar___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_hexChar(lean_object*);
static const lean_string_object l_Lean_Json_Parser_finishSurrogatePair___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Json_Parser_finishSurrogatePair___closed__0 = (const lean_object*)&l_Lean_Json_Parser_finishSurrogatePair___closed__0_value;
static const lean_ctor_object l_Lean_Json_Parser_finishSurrogatePair___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_finishSurrogatePair___closed__0_value)}};
static const lean_object* l_Lean_Json_Parser_finishSurrogatePair___closed__1 = (const lean_object*)&l_Lean_Json_Parser_finishSurrogatePair___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair(uint16_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Json_Parser_escapedChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "illegal \\u escape"};
static const lean_object* l_Lean_Json_Parser_escapedChar___closed__0 = (const lean_object*)&l_Lean_Json_Parser_escapedChar___closed__0_value;
static const lean_ctor_object l_Lean_Json_Parser_escapedChar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_escapedChar___closed__0_value)}};
static const lean_object* l_Lean_Json_Parser_escapedChar___closed__1 = (const lean_object*)&l_Lean_Json_Parser_escapedChar___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__2;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__3;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__4;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__5;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__6;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__7;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__8;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__9;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar(lean_object*);
static const lean_string_object l_Lean_Json_Parser_strCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "unexpected character in string"};
static const lean_object* l_Lean_Json_Parser_strCore___closed__0 = (const lean_object*)&l_Lean_Json_Parser_strCore___closed__0_value;
static const lean_ctor_object l_Lean_Json_Parser_strCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_strCore___closed__0_value)}};
static const lean_object* l_Lean_Json_Parser_strCore___closed__1 = (const lean_object*)&l_Lean_Json_Parser_strCore___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_strCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_str(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCoreNumDigits(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Json_Parser_lookahead___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "expected "};
static const lean_object* l_Lean_Json_Parser_lookahead___redArg___closed__0 = (const lean_object*)&l_Lean_Json_Parser_lookahead___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Json_Parser_natNonZero___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "expected 1-9"};
static const lean_object* l_Lean_Json_Parser_natNonZero___closed__0 = (const lean_object*)&l_Lean_Json_Parser_natNonZero___closed__0_value;
static const lean_ctor_object l_Lean_Json_Parser_natNonZero___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_natNonZero___closed__0_value)}};
static const lean_object* l_Lean_Json_Parser_natNonZero___closed__1 = (const lean_object*)&l_Lean_Json_Parser_natNonZero___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNonZero(lean_object*);
static const lean_string_object l_Lean_Json_Parser_natNumDigits___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected digit"};
static const lean_object* l_Lean_Json_Parser_natNumDigits___closed__0 = (const lean_object*)&l_Lean_Json_Parser_natNumDigits___closed__0_value;
static const lean_ctor_object l_Lean_Json_Parser_natNumDigits___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_natNumDigits___closed__0_value)}};
static const lean_object* l_Lean_Json_Parser_natNumDigits___closed__1 = (const lean_object*)&l_Lean_Json_Parser_natNumDigits___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNumDigits(lean_object*);
static const lean_string_object l_Lean_Json_Parser_natMaybeZero___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "expected 0-9"};
static const lean_object* l_Lean_Json_Parser_natMaybeZero___closed__0 = (const lean_object*)&l_Lean_Json_Parser_natMaybeZero___closed__0_value;
static const lean_ctor_object l_Lean_Json_Parser_natMaybeZero___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_natMaybeZero___closed__0_value)}};
static const lean_object* l_Lean_Json_Parser_natMaybeZero___closed__1 = (const lean_object*)&l_Lean_Json_Parser_natMaybeZero___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natMaybeZero(lean_object*);
static lean_once_cell_t l_Lean_Json_Parser_numSign___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json_Parser_numSign___closed__0;
static lean_once_cell_t l_Lean_Json_Parser_numSign___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json_Parser_numSign___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numSign(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_nat(lean_object*);
static lean_once_cell_t l_Lean_Json_Parser_numWithDecimals___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json_Parser_numWithDecimals___closed__0;
static const lean_string_object l_Lean_Json_Parser_numWithDecimals___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "too many decimals"};
static const lean_object* l_Lean_Json_Parser_numWithDecimals___closed__1 = (const lean_object*)&l_Lean_Json_Parser_numWithDecimals___closed__1_value;
static const lean_ctor_object l_Lean_Json_Parser_numWithDecimals___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_numWithDecimals___closed__1_value)}};
static const lean_object* l_Lean_Json_Parser_numWithDecimals___closed__2 = (const lean_object*)&l_Lean_Json_Parser_numWithDecimals___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numWithDecimals(lean_object*);
static const lean_string_object l_Lean_Json_Parser_exponent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "exponent too large"};
static const lean_object* l_Lean_Json_Parser_exponent___closed__0 = (const lean_object*)&l_Lean_Json_Parser_exponent___closed__0_value;
static const lean_ctor_object l_Lean_Json_Parser_exponent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_exponent___closed__0_value)}};
static const lean_object* l_Lean_Json_Parser_exponent___closed__1 = (const lean_object*)&l_Lean_Json_Parser_exponent___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Json_Parser_num_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_num(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3_spec__3___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Json_Parser_arrayCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "unexpected character in array"};
static const lean_object* l_Lean_Json_Parser_arrayCore___closed__0 = (const lean_object*)&l_Lean_Json_Parser_arrayCore___closed__0_value;
static const lean_ctor_object l_Lean_Json_Parser_arrayCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_arrayCore___closed__0_value)}};
static const lean_object* l_Lean_Json_Parser_arrayCore___closed__1 = (const lean_object*)&l_Lean_Json_Parser_arrayCore___closed__1_value;
static const lean_string_object l_Lean_Json_Parser_anyCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unexpected input"};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__0 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__0_value;
static const lean_ctor_object l_Lean_Json_Parser_anyCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_anyCore___closed__0_value)}};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__1 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__1_value;
static const lean_string_object l_Lean_Json_Parser_anyCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__2 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__2_value;
static const lean_string_object l_Lean_Json_Parser_anyCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__3 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__3_value;
static const lean_string_object l_Lean_Json_Parser_anyCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__4 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__4_value;
static const lean_string_object l_Lean_Json_Parser_objectCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "expected \""};
static const lean_object* l_Lean_Json_Parser_objectCore___closed__0 = (const lean_object*)&l_Lean_Json_Parser_objectCore___closed__0_value;
static const lean_ctor_object l_Lean_Json_Parser_objectCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_objectCore___closed__0_value)}};
static const lean_object* l_Lean_Json_Parser_objectCore___closed__1 = (const lean_object*)&l_Lean_Json_Parser_objectCore___closed__1_value;
static const lean_string_object l_Lean_Json_Parser_objectCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "expected :"};
static const lean_object* l_Lean_Json_Parser_objectCore___closed__2 = (const lean_object*)&l_Lean_Json_Parser_objectCore___closed__2_value;
static const lean_ctor_object l_Lean_Json_Parser_objectCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_objectCore___closed__2_value)}};
static const lean_object* l_Lean_Json_Parser_objectCore___closed__3 = (const lean_object*)&l_Lean_Json_Parser_objectCore___closed__3_value;
static const lean_string_object l_Lean_Json_Parser_objectCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "unexpected character in object"};
static const lean_object* l_Lean_Json_Parser_objectCore___closed__4 = (const lean_object*)&l_Lean_Json_Parser_objectCore___closed__4_value;
static const lean_ctor_object l_Lean_Json_Parser_objectCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_objectCore___closed__4_value)}};
static const lean_object* l_Lean_Json_Parser_objectCore___closed__5 = (const lean_object*)&l_Lean_Json_Parser_objectCore___closed__5_value;
static const lean_string_object l_Lean_Json_Parser_objectCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "duplicate object key "};
static const lean_object* l_Lean_Json_Parser_objectCore___closed__6 = (const lean_object*)&l_Lean_Json_Parser_objectCore___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Json_Parser_anyCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__5 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__5_value;
static const lean_array_object l_Lean_Json_Parser_anyCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__6 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__6_value;
static const lean_ctor_object l_Lean_Json_Parser_anyCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_anyCore___closed__6_value)}};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__7 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Json_Parser_any___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l_Lean_Json_Parser_any___closed__0 = (const lean_object*)&l_Lean_Json_Parser_any___closed__0_value;
static const lean_ctor_object l_Lean_Json_Parser_any___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_any___closed__0_value)}};
static const lean_object* l_Lean_Json_Parser_any___closed__1 = (const lean_object*)&l_Lean_Json_Parser_any___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_any(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_hexChar(lean_object* v_a_4_){
_start:
{
lean_object* v_fst_5_; lean_object* v_snd_6_; lean_object* v___x_7_; uint8_t v_decide_8_; 
v_fst_5_ = lean_ctor_get(v_a_4_, 0);
v_snd_6_ = lean_ctor_get(v_a_4_, 1);
v___x_7_ = lean_string_utf8_byte_size(v_fst_5_);
v_decide_8_ = lean_nat_dec_eq(v_snd_6_, v___x_7_);
if (v_decide_8_ == 0)
{
lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_50_; 
lean_inc(v_snd_6_);
lean_inc(v_fst_5_);
v_isSharedCheck_50_ = !lean_is_exclusive(v_a_4_);
if (v_isSharedCheck_50_ == 0)
{
lean_object* v_unused_51_; lean_object* v_unused_52_; 
v_unused_51_ = lean_ctor_get(v_a_4_, 1);
lean_dec(v_unused_51_);
v_unused_52_ = lean_ctor_get(v_a_4_, 0);
lean_dec(v_unused_52_);
v___x_10_ = v_a_4_;
v_isShared_11_ = v_isSharedCheck_50_;
goto v_resetjp_9_;
}
else
{
lean_dec(v_a_4_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_50_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
uint32_t v_c_12_; lean_object* v___x_13_; lean_object* v_it_x27_15_; 
v_c_12_ = lean_string_utf8_get_fast(v_fst_5_, v_snd_6_);
v___x_13_ = lean_string_utf8_next_fast(v_fst_5_, v_snd_6_);
lean_dec(v_snd_6_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 1, v___x_13_);
v_it_x27_15_ = v___x_10_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_fst_5_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___x_13_);
v_it_x27_15_ = v_reuseFailAlloc_49_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
uint32_t v___x_41_; uint8_t v___x_42_; 
v___x_41_ = 48;
v___x_42_ = lean_uint32_dec_le(v___x_41_, v_c_12_);
if (v___x_42_ == 0)
{
goto v___jp_30_;
}
else
{
uint32_t v___x_43_; uint8_t v___x_44_; 
v___x_43_ = 57;
v___x_44_ = lean_uint32_dec_le(v_c_12_, v___x_43_);
if (v___x_44_ == 0)
{
goto v___jp_30_;
}
else
{
uint32_t v___x_45_; uint16_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_45_ = lean_uint32_sub(v_c_12_, v___x_41_);
v___x_46_ = lean_uint32_to_uint16(v___x_45_);
v___x_47_ = lean_box(v___x_46_);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v_it_x27_15_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
return v___x_48_;
}
}
v___jp_16_:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = ((lean_object*)(l_Lean_Json_Parser_hexChar___closed__1));
v___x_18_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_18_, 0, v_it_x27_15_);
lean_ctor_set(v___x_18_, 1, v___x_17_);
return v___x_18_;
}
v___jp_19_:
{
uint32_t v___x_20_; uint8_t v___x_21_; 
v___x_20_ = 65;
v___x_21_ = lean_uint32_dec_le(v___x_20_, v_c_12_);
if (v___x_21_ == 0)
{
goto v___jp_16_;
}
else
{
uint32_t v___x_22_; uint8_t v___x_23_; 
v___x_22_ = 70;
v___x_23_ = lean_uint32_dec_le(v_c_12_, v___x_22_);
if (v___x_23_ == 0)
{
goto v___jp_16_;
}
else
{
uint32_t v___x_24_; uint32_t v___x_25_; uint32_t v___x_26_; uint16_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_24_ = lean_uint32_sub(v_c_12_, v___x_20_);
v___x_25_ = 10;
v___x_26_ = lean_uint32_add(v___x_24_, v___x_25_);
v___x_27_ = lean_uint32_to_uint16(v___x_26_);
v___x_28_ = lean_box(v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v_it_x27_15_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
return v___x_29_;
}
}
}
v___jp_30_:
{
uint32_t v___x_31_; uint8_t v___x_32_; 
v___x_31_ = 97;
v___x_32_ = lean_uint32_dec_le(v___x_31_, v_c_12_);
if (v___x_32_ == 0)
{
goto v___jp_19_;
}
else
{
uint32_t v___x_33_; uint8_t v___x_34_; 
v___x_33_ = 102;
v___x_34_ = lean_uint32_dec_le(v_c_12_, v___x_33_);
if (v___x_34_ == 0)
{
goto v___jp_19_;
}
else
{
uint32_t v___x_35_; uint32_t v___x_36_; uint32_t v___x_37_; uint16_t v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_35_ = lean_uint32_sub(v_c_12_, v___x_31_);
v___x_36_ = 10;
v___x_37_ = lean_uint32_add(v___x_35_, v___x_36_);
v___x_38_ = lean_uint32_to_uint16(v___x_37_);
v___x_39_ = lean_box(v___x_38_);
v___x_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_40_, 0, v_it_x27_15_);
lean_ctor_set(v___x_40_, 1, v___x_39_);
return v___x_40_;
}
}
}
}
}
}
else
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_box(0);
v___x_54_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_54_, 0, v_a_4_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair(uint16_t v_low_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___y_61_; lean_object* v_fst_64_; lean_object* v_snd_65_; lean_object* v___x_66_; uint8_t v_decide_67_; 
v_fst_64_ = lean_ctor_get(v_a_59_, 0);
v_snd_65_ = lean_ctor_get(v_a_59_, 1);
v___x_66_ = lean_string_utf8_byte_size(v_fst_64_);
v_decide_67_ = lean_nat_dec_eq(v_snd_65_, v___x_66_);
if (v_decide_67_ == 0)
{
lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_183_; 
lean_inc(v_snd_65_);
lean_inc(v_fst_64_);
v_isSharedCheck_183_ = !lean_is_exclusive(v_a_59_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; lean_object* v_unused_185_; 
v_unused_184_ = lean_ctor_get(v_a_59_, 1);
lean_dec(v_unused_184_);
v_unused_185_ = lean_ctor_get(v_a_59_, 0);
lean_dec(v_unused_185_);
v___x_69_ = v_a_59_;
v_isShared_70_ = v_isSharedCheck_183_;
goto v_resetjp_68_;
}
else
{
lean_dec(v_a_59_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_183_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
uint32_t v_c_71_; lean_object* v___x_72_; lean_object* v_it_x27_74_; 
v_c_71_ = lean_string_utf8_get_fast(v_fst_64_, v_snd_65_);
v___x_72_ = lean_string_utf8_next_fast(v_fst_64_, v_snd_65_);
lean_dec(v_snd_65_);
lean_inc(v_fst_64_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 1, v___x_72_);
v_it_x27_74_ = v___x_69_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_fst_64_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___x_72_);
v_it_x27_74_ = v_reuseFailAlloc_182_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
uint32_t v___x_75_; uint8_t v___x_76_; 
v___x_75_ = 92;
v___x_76_ = lean_uint32_dec_eq(v_c_71_, v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec(v_fst_64_);
v___x_77_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_78_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_78_, 0, v_it_x27_74_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
return v___x_78_;
}
else
{
uint8_t v_decide_79_; 
v_decide_79_ = lean_nat_dec_eq(v___x_72_, v___x_66_);
if (v_decide_79_ == 0)
{
uint32_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint32_t v___x_83_; uint8_t v___x_84_; 
lean_dec_ref(v_it_x27_74_);
v___x_80_ = lean_string_utf8_get_fast(v_fst_64_, v___x_72_);
v___x_81_ = lean_string_utf8_next_fast(v_fst_64_, v___x_72_);
lean_inc(v_fst_64_);
v___x_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_82_, 0, v_fst_64_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = 117;
v___x_84_ = lean_uint32_dec_eq(v___x_80_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec(v_fst_64_);
v___x_85_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_86_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_82_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
return v___x_86_;
}
else
{
uint8_t v_decide_87_; 
v_decide_87_ = lean_nat_dec_eq(v___x_81_, v___x_66_);
if (v_decide_87_ == 0)
{
uint32_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint32_t v___x_172_; uint8_t v___x_173_; 
lean_dec_ref_known(v___x_82_, 2);
v___x_88_ = lean_string_utf8_get_fast(v_fst_64_, v___x_81_);
v___x_89_ = lean_string_utf8_next_fast(v_fst_64_, v___x_81_);
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v_fst_64_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_172_ = 100;
v___x_173_ = lean_uint32_dec_eq(v___x_88_, v___x_172_);
if (v___x_173_ == 0)
{
uint32_t v___x_174_; uint8_t v___x_175_; 
v___x_174_ = 68;
v___x_175_ = lean_uint32_dec_eq(v___x_88_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_90_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
return v___x_177_;
}
else
{
goto v___jp_91_;
}
}
else
{
goto v___jp_91_;
}
v___jp_91_:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Json_Parser_hexChar(v___x_90_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_pos_93_; lean_object* v_res_94_; lean_object* v___x_95_; 
v_pos_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc(v_pos_93_);
v_res_94_ = lean_ctor_get(v___x_92_, 1);
lean_inc(v_res_94_);
lean_dec_ref_known(v___x_92_, 2);
v___x_95_ = l_Lean_Json_Parser_hexChar(v_pos_93_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_pos_96_; lean_object* v_res_97_; lean_object* v___x_98_; 
v_pos_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_pos_96_);
v_res_97_ = lean_ctor_get(v___x_95_, 1);
lean_inc(v_res_97_);
lean_dec_ref_known(v___x_95_, 2);
v___x_98_ = l_Lean_Json_Parser_hexChar(v_pos_96_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_pos_99_; lean_object* v_res_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_144_; 
v_pos_99_ = lean_ctor_get(v___x_98_, 0);
v_res_100_ = lean_ctor_get(v___x_98_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_144_ == 0)
{
v___x_102_ = v___x_98_;
v_isShared_103_ = v_isSharedCheck_144_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_res_100_);
lean_inc(v_pos_99_);
lean_dec(v___x_98_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_144_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
uint16_t v___x_104_; uint16_t v___x_105_; uint16_t v___x_106_; uint16_t v___x_107_; uint16_t v___x_108_; uint16_t v___x_109_; uint16_t v___x_110_; uint16_t v___x_111_; uint16_t v___x_112_; uint16_t v___x_113_; uint8_t v___x_114_; 
v___x_104_ = 8;
v___x_105_ = lean_unbox(v_res_94_);
lean_dec(v_res_94_);
v___x_106_ = lean_uint16_shift_left(v___x_105_, v___x_104_);
v___x_107_ = 4;
v___x_108_ = lean_unbox(v_res_97_);
lean_dec(v_res_97_);
v___x_109_ = lean_uint16_shift_left(v___x_108_, v___x_107_);
v___x_110_ = lean_uint16_lor(v___x_106_, v___x_109_);
v___x_111_ = lean_unbox(v_res_100_);
lean_dec(v_res_100_);
v___x_112_ = lean_uint16_lor(v___x_110_, v___x_111_);
v___x_113_ = 3072;
v___x_114_ = lean_uint16_dec_lt(v___x_112_, v___x_113_);
if (v___x_114_ == 0)
{
uint32_t v___x_115_; uint32_t v___x_116_; uint32_t v___x_117_; uint32_t v___x_118_; uint32_t v___x_119_; uint32_t v___x_120_; uint32_t v___x_121_; uint32_t v___x_122_; uint32_t v___x_123_; uint32_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_115_ = lean_uint16_to_uint32(v_low_58_);
v___x_116_ = 1023;
v___x_117_ = lean_uint32_land(v___x_115_, v___x_116_);
v___x_118_ = 10;
v___x_119_ = lean_uint32_shift_left(v___x_117_, v___x_118_);
v___x_120_ = lean_uint16_to_uint32(v___x_112_);
v___x_121_ = lean_uint32_land(v___x_120_, v___x_116_);
v___x_122_ = lean_uint32_lor(v___x_119_, v___x_121_);
v___x_123_ = 65536;
v___x_124_ = lean_uint32_add(v___x_122_, v___x_123_);
v___x_125_ = lean_uint32_to_nat(v___x_124_);
v___x_126_ = lean_unsigned_to_nat(55296u);
v___x_127_ = lean_nat_dec_lt(v___x_125_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(57343u);
v___x_129_ = lean_nat_dec_lt(v___x_128_, v___x_125_);
if (v___x_129_ == 0)
{
lean_dec(v___x_125_);
lean_del_object(v___x_102_);
v___y_61_ = v_pos_99_;
goto v___jp_60_;
}
else
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(1114112u);
v___x_131_ = lean_nat_dec_lt(v___x_125_, v___x_130_);
lean_dec(v___x_125_);
if (v___x_131_ == 0)
{
lean_del_object(v___x_102_);
v___y_61_ = v_pos_99_;
goto v___jp_60_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = lean_box_uint32(v___x_124_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_132_);
v___x_134_ = v___x_102_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_pos_99_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
else
{
lean_object* v___x_136_; lean_object* v___x_138_; 
lean_dec(v___x_125_);
v___x_136_ = lean_box_uint32(v___x_124_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_136_);
v___x_138_ = v___x_102_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_pos_99_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
else
{
lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_140_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
if (v_isShared_103_ == 0)
{
lean_ctor_set_tag(v___x_102_, 1);
lean_ctor_set(v___x_102_, 1, v___x_140_);
v___x_142_ = v___x_102_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_pos_99_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
else
{
lean_object* v_pos_145_; lean_object* v_err_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec(v_res_97_);
lean_dec(v_res_94_);
v_pos_145_ = lean_ctor_get(v___x_98_, 0);
v_err_146_ = lean_ctor_get(v___x_98_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_98_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_err_146_);
lean_inc(v_pos_145_);
lean_dec(v___x_98_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_pos_145_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_err_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
else
{
lean_object* v_pos_154_; lean_object* v_err_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
lean_dec(v_res_94_);
v_pos_154_ = lean_ctor_get(v___x_95_, 0);
v_err_155_ = lean_ctor_get(v___x_95_, 1);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_95_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_err_155_);
lean_inc(v_pos_154_);
lean_dec(v___x_95_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_pos_154_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_err_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
else
{
lean_object* v_pos_163_; lean_object* v_err_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
v_pos_163_ = lean_ctor_get(v___x_92_, 0);
v_err_164_ = lean_ctor_get(v___x_92_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_92_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_err_164_);
lean_inc(v_pos_163_);
lean_dec(v___x_92_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_pos_163_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_err_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_fst_64_);
v___x_178_ = lean_box(0);
v___x_179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_82_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
return v___x_179_;
}
}
}
else
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v_fst_64_);
v___x_180_ = lean_box(0);
v___x_181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_181_, 0, v_it_x27_74_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
return v___x_181_;
}
}
}
}
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_box(0);
v___x_187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_187_, 0, v_a_59_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
return v___x_187_;
}
v___jp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_63_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_63_, 0, v___y_61_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair___boxed(lean_object* v_low_188_, lean_object* v_a_189_){
_start:
{
uint16_t v_low_boxed_190_; lean_object* v_res_191_; 
v_low_boxed_190_ = lean_unbox(v_low_188_);
v_res_191_ = l_Lean_Json_Parser_finishSurrogatePair(v_low_boxed_190_, v_a_189_);
return v_res_191_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_195_; lean_object* v___x_196_; 
v___x_195_ = 65533;
v___x_196_ = lean_box_uint32(v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_197_; lean_object* v___x_198_; 
v___x_197_ = 9;
v___x_198_ = lean_box_uint32(v___x_197_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_199_; lean_object* v___x_200_; 
v___x_199_ = 13;
v___x_200_ = lean_box_uint32(v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_201_; lean_object* v___x_202_; 
v___x_201_ = 10;
v___x_202_ = lean_box_uint32(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_203_; lean_object* v___x_204_; 
v___x_203_ = 12;
v___x_204_ = lean_box_uint32(v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_205_; lean_object* v___x_206_; 
v___x_205_ = 8;
v___x_206_ = lean_box_uint32(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__7(void){
_start:
{
uint32_t v___x_207_; lean_object* v___x_208_; 
v___x_207_ = 47;
v___x_208_ = lean_box_uint32(v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__8(void){
_start:
{
uint32_t v___x_209_; lean_object* v___x_210_; 
v___x_209_ = 34;
v___x_210_ = lean_box_uint32(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__9(void){
_start:
{
uint32_t v___x_211_; lean_object* v___x_212_; 
v___x_211_ = 92;
v___x_212_ = lean_box_uint32(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar(lean_object* v_a_213_){
_start:
{
lean_object* v_fst_214_; lean_object* v_snd_215_; lean_object* v___x_216_; uint8_t v_decide_217_; 
v_fst_214_ = lean_ctor_get(v_a_213_, 0);
v_snd_215_ = lean_ctor_get(v_a_213_, 1);
v___x_216_ = lean_string_utf8_byte_size(v_fst_214_);
v_decide_217_ = lean_nat_dec_eq(v_snd_215_, v___x_216_);
if (v_decide_217_ == 0)
{
lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_363_; 
lean_inc(v_snd_215_);
lean_inc(v_fst_214_);
v_isSharedCheck_363_ = !lean_is_exclusive(v_a_213_);
if (v_isSharedCheck_363_ == 0)
{
lean_object* v_unused_364_; lean_object* v_unused_365_; 
v_unused_364_ = lean_ctor_get(v_a_213_, 1);
lean_dec(v_unused_364_);
v_unused_365_ = lean_ctor_get(v_a_213_, 0);
lean_dec(v_unused_365_);
v___x_219_ = v_a_213_;
v_isShared_220_ = v_isSharedCheck_363_;
goto v_resetjp_218_;
}
else
{
lean_dec(v_a_213_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_363_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
uint32_t v_c_221_; lean_object* v___x_222_; lean_object* v_it_x27_224_; 
v_c_221_ = lean_string_utf8_get_fast(v_fst_214_, v_snd_215_);
v___x_222_ = lean_string_utf8_next_fast(v_fst_214_, v_snd_215_);
lean_dec(v_snd_215_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_222_);
v_it_x27_224_ = v___x_219_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_fst_214_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v___x_222_);
v_it_x27_224_ = v_reuseFailAlloc_362_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
uint32_t v___x_225_; uint8_t v___x_226_; 
v___x_225_ = 92;
v___x_226_ = lean_uint32_dec_eq(v_c_221_, v___x_225_);
if (v___x_226_ == 0)
{
uint32_t v___x_227_; uint8_t v___x_228_; 
v___x_227_ = 34;
v___x_228_ = lean_uint32_dec_eq(v_c_221_, v___x_227_);
if (v___x_228_ == 0)
{
uint32_t v___x_229_; uint8_t v___x_230_; 
v___x_229_ = 47;
v___x_230_ = lean_uint32_dec_eq(v_c_221_, v___x_229_);
if (v___x_230_ == 0)
{
uint32_t v___x_231_; uint8_t v___x_232_; 
v___x_231_ = 98;
v___x_232_ = lean_uint32_dec_eq(v_c_221_, v___x_231_);
if (v___x_232_ == 0)
{
uint32_t v___x_233_; uint8_t v___x_234_; 
v___x_233_ = 102;
v___x_234_ = lean_uint32_dec_eq(v_c_221_, v___x_233_);
if (v___x_234_ == 0)
{
uint32_t v___x_235_; uint8_t v___x_236_; 
v___x_235_ = 110;
v___x_236_ = lean_uint32_dec_eq(v_c_221_, v___x_235_);
if (v___x_236_ == 0)
{
uint32_t v___x_237_; uint8_t v___x_238_; 
v___x_237_ = 114;
v___x_238_ = lean_uint32_dec_eq(v_c_221_, v___x_237_);
if (v___x_238_ == 0)
{
uint32_t v___x_239_; uint8_t v___x_240_; 
v___x_239_ = 116;
v___x_240_ = lean_uint32_dec_eq(v_c_221_, v___x_239_);
if (v___x_240_ == 0)
{
uint32_t v___x_241_; uint8_t v___x_242_; 
v___x_241_ = 117;
v___x_242_ = lean_uint32_dec_eq(v_c_221_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = ((lean_object*)(l_Lean_Json_Parser_escapedChar___closed__1));
v___x_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_244_, 0, v_it_x27_224_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
return v___x_244_;
}
else
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Json_Parser_hexChar(v_it_x27_224_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_pos_246_; lean_object* v_res_247_; lean_object* v___x_248_; 
v_pos_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_pos_246_);
v_res_247_ = lean_ctor_get(v___x_245_, 1);
lean_inc(v_res_247_);
lean_dec_ref_known(v___x_245_, 2);
v___x_248_ = l_Lean_Json_Parser_hexChar(v_pos_246_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_pos_249_; lean_object* v_res_250_; lean_object* v___x_251_; 
v_pos_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_pos_249_);
v_res_250_ = lean_ctor_get(v___x_248_, 1);
lean_inc(v_res_250_);
lean_dec_ref_known(v___x_248_, 2);
v___x_251_ = l_Lean_Json_Parser_hexChar(v_pos_249_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_pos_252_; lean_object* v_res_253_; lean_object* v___x_254_; 
v_pos_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_pos_252_);
v_res_253_ = lean_ctor_get(v___x_251_, 1);
lean_inc(v_res_253_);
lean_dec_ref_known(v___x_251_, 2);
v___x_254_ = l_Lean_Json_Parser_hexChar(v_pos_252_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_pos_255_; lean_object* v_res_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_309_; 
v_pos_255_ = lean_ctor_get(v___x_254_, 0);
v_res_256_ = lean_ctor_get(v___x_254_, 1);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_309_ == 0)
{
v___x_258_ = v___x_254_;
v_isShared_259_ = v_isSharedCheck_309_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_res_256_);
lean_inc(v_pos_255_);
lean_dec(v___x_254_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_309_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
uint16_t v___x_260_; uint16_t v___x_261_; uint16_t v___x_262_; uint16_t v___x_263_; uint16_t v___x_264_; uint16_t v___x_265_; uint16_t v___x_266_; uint16_t v___x_267_; uint16_t v___x_268_; uint16_t v___x_269_; uint16_t v___x_270_; uint16_t v___x_271_; uint16_t v___x_272_; uint16_t v___x_273_; uint8_t v___x_274_; 
v___x_260_ = 12;
v___x_261_ = lean_unbox(v_res_247_);
lean_dec(v_res_247_);
v___x_262_ = lean_uint16_shift_left(v___x_261_, v___x_260_);
v___x_263_ = 8;
v___x_264_ = lean_unbox(v_res_250_);
lean_dec(v_res_250_);
v___x_265_ = lean_uint16_shift_left(v___x_264_, v___x_263_);
v___x_266_ = lean_uint16_lor(v___x_262_, v___x_265_);
v___x_267_ = 4;
v___x_268_ = lean_unbox(v_res_253_);
lean_dec(v_res_253_);
v___x_269_ = lean_uint16_shift_left(v___x_268_, v___x_267_);
v___x_270_ = lean_uint16_lor(v___x_266_, v___x_269_);
v___x_271_ = lean_unbox(v_res_256_);
lean_dec(v_res_256_);
v___x_272_ = lean_uint16_lor(v___x_270_, v___x_271_);
v___x_273_ = 55296;
v___x_274_ = lean_uint16_dec_lt(v___x_272_, v___x_273_);
if (v___x_274_ == 0)
{
uint16_t v___x_275_; uint8_t v___x_276_; 
v___x_275_ = 57344;
v___x_276_ = lean_uint16_dec_lt(v___x_272_, v___x_275_);
if (v___x_276_ == 0)
{
uint32_t v___x_277_; lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_277_ = lean_uint16_to_uint32(v___x_272_);
v___x_278_ = lean_box_uint32(v___x_277_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v___x_278_);
v___x_280_ = v___x_258_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_pos_255_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
else
{
uint16_t v___x_282_; uint8_t v___x_283_; 
v___x_282_ = 56320;
v___x_283_ = lean_uint16_dec_lt(v___x_272_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_284_ = l_Lean_Json_Parser_escapedChar___boxed__const__1;
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v___x_284_);
v___x_286_ = v___x_258_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_pos_255_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
else
{
lean_object* v___x_288_; 
lean_del_object(v___x_258_);
lean_inc(v_pos_255_);
v___x_288_ = l_Lean_Json_Parser_finishSurrogatePair(v___x_272_, v_pos_255_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_dec(v_pos_255_);
return v___x_288_;
}
else
{
lean_object* v_err_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_302_; 
v_err_289_ = lean_ctor_get(v___x_288_, 1);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_302_ == 0)
{
lean_object* v_unused_303_; 
v_unused_303_ = lean_ctor_get(v___x_288_, 0);
lean_dec(v_unused_303_);
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_302_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_err_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_302_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v_snd_293_; uint8_t v_decide_294_; 
v_snd_293_ = lean_ctor_get(v_pos_255_, 1);
v_decide_294_ = lean_nat_dec_eq(v_snd_293_, v_snd_293_);
if (v_decide_294_ == 0)
{
lean_object* v___x_296_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v_pos_255_);
v___x_296_ = v___x_291_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_pos_255_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_err_289_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
else
{
lean_object* v___x_298_; lean_object* v___x_300_; 
lean_dec(v_err_289_);
v___x_298_ = l_Lean_Json_Parser_escapedChar___boxed__const__1;
if (v_isShared_292_ == 0)
{
lean_ctor_set_tag(v___x_291_, 0);
lean_ctor_set(v___x_291_, 1, v___x_298_);
lean_ctor_set(v___x_291_, 0, v_pos_255_);
v___x_300_ = v___x_291_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_pos_255_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
}
}
else
{
uint32_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_304_ = lean_uint16_to_uint32(v___x_272_);
v___x_305_ = lean_box_uint32(v___x_304_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v___x_305_);
v___x_307_ = v___x_258_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_pos_255_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
else
{
lean_object* v_pos_310_; lean_object* v_err_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_dec(v_res_253_);
lean_dec(v_res_250_);
lean_dec(v_res_247_);
v_pos_310_ = lean_ctor_get(v___x_254_, 0);
v_err_311_ = lean_ctor_get(v___x_254_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_254_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_err_311_);
lean_inc(v_pos_310_);
lean_dec(v___x_254_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_pos_310_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_err_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
else
{
lean_object* v_pos_319_; lean_object* v_err_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec(v_res_250_);
lean_dec(v_res_247_);
v_pos_319_ = lean_ctor_get(v___x_251_, 0);
v_err_320_ = lean_ctor_get(v___x_251_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_251_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_err_320_);
lean_inc(v_pos_319_);
lean_dec(v___x_251_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_pos_319_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_err_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
else
{
lean_object* v_pos_328_; lean_object* v_err_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
lean_dec(v_res_247_);
v_pos_328_ = lean_ctor_get(v___x_248_, 0);
v_err_329_ = lean_ctor_get(v___x_248_, 1);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_248_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_err_329_);
lean_inc(v_pos_328_);
lean_dec(v___x_248_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_pos_328_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_err_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
else
{
lean_object* v_pos_337_; lean_object* v_err_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
v_pos_337_ = lean_ctor_get(v___x_245_, 0);
v_err_338_ = lean_ctor_get(v___x_245_, 1);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_245_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_err_338_);
lean_inc(v_pos_337_);
lean_dec(v___x_245_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_pos_337_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_err_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = l_Lean_Json_Parser_escapedChar___boxed__const__2;
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v_it_x27_224_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
return v___x_347_;
}
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = l_Lean_Json_Parser_escapedChar___boxed__const__3;
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v_it_x27_224_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
return v___x_349_;
}
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = l_Lean_Json_Parser_escapedChar___boxed__const__4;
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v_it_x27_224_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
return v___x_351_;
}
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = l_Lean_Json_Parser_escapedChar___boxed__const__5;
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v_it_x27_224_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
return v___x_353_;
}
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = l_Lean_Json_Parser_escapedChar___boxed__const__6;
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v_it_x27_224_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
return v___x_355_;
}
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = l_Lean_Json_Parser_escapedChar___boxed__const__7;
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v_it_x27_224_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
return v___x_357_;
}
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = l_Lean_Json_Parser_escapedChar___boxed__const__8;
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_it_x27_224_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
return v___x_359_;
}
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = l_Lean_Json_Parser_escapedChar___boxed__const__9;
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_it_x27_224_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
return v___x_361_;
}
}
}
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_box(0);
v___x_367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_367_, 0, v_a_213_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_strCore(lean_object* v_acc_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_fst_373_; lean_object* v_snd_374_; lean_object* v___x_375_; uint8_t v_decide_376_; 
v_fst_373_ = lean_ctor_get(v_a_372_, 0);
v_snd_374_ = lean_ctor_get(v_a_372_, 1);
v___x_375_ = lean_string_utf8_byte_size(v_fst_373_);
v_decide_376_ = lean_nat_dec_eq(v_snd_374_, v___x_375_);
if (v_decide_376_ == 0)
{
lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_418_; 
lean_inc(v_snd_374_);
lean_inc(v_fst_373_);
v_isSharedCheck_418_ = !lean_is_exclusive(v_a_372_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; lean_object* v_unused_420_; 
v_unused_419_ = lean_ctor_get(v_a_372_, 1);
lean_dec(v_unused_419_);
v_unused_420_ = lean_ctor_get(v_a_372_, 0);
lean_dec(v_unused_420_);
v___x_378_ = v_a_372_;
v_isShared_379_ = v_isSharedCheck_418_;
goto v_resetjp_377_;
}
else
{
lean_dec(v_a_372_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_418_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
uint32_t v___x_380_; uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_380_ = lean_string_utf8_get_fast(v_fst_373_, v_snd_374_);
v___x_381_ = 34;
v___x_382_ = lean_uint32_dec_eq(v___x_380_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_383_ = lean_string_utf8_next_fast(v_fst_373_, v_snd_374_);
lean_dec(v_snd_374_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 1, v___x_383_);
v___x_385_ = v___x_378_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_fst_373_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v___x_383_);
v___x_385_ = v_reuseFailAlloc_412_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
uint32_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 92;
v___x_390_ = lean_uint32_dec_eq(v___x_380_, v___x_389_);
if (v___x_390_ == 0)
{
uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_391_ = 32;
v___x_392_ = lean_uint32_dec_le(v___x_391_, v___x_380_);
if (v___x_392_ == 0)
{
lean_dec_ref(v_acc_371_);
goto v___jp_386_;
}
else
{
uint32_t v___x_393_; uint8_t v___x_394_; 
v___x_393_ = 1114111;
v___x_394_ = lean_uint32_dec_le(v___x_380_, v___x_393_);
if (v___x_394_ == 0)
{
lean_dec_ref(v_acc_371_);
goto v___jp_386_;
}
else
{
lean_object* v___x_395_; 
v___x_395_ = lean_string_push(v_acc_371_, v___x_380_);
v_acc_371_ = v___x_395_;
v_a_372_ = v___x_385_;
goto _start;
}
}
}
else
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Json_Parser_escapedChar(v___x_385_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_pos_398_; lean_object* v_res_399_; uint32_t v___x_400_; lean_object* v___x_401_; 
v_pos_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_pos_398_);
v_res_399_ = lean_ctor_get(v___x_397_, 1);
lean_inc(v_res_399_);
lean_dec_ref_known(v___x_397_, 2);
v___x_400_ = lean_unbox_uint32(v_res_399_);
lean_dec(v_res_399_);
v___x_401_ = lean_string_push(v_acc_371_, v___x_400_);
v_acc_371_ = v___x_401_;
v_a_372_ = v_pos_398_;
goto _start;
}
else
{
lean_object* v_pos_403_; lean_object* v_err_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
lean_dec_ref(v_acc_371_);
v_pos_403_ = lean_ctor_get(v___x_397_, 0);
v_err_404_ = lean_ctor_get(v___x_397_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_397_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_err_404_);
lean_inc(v_pos_403_);
lean_dec(v___x_397_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_pos_403_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_err_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
v___jp_386_:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_Json_Parser_strCore___closed__1));
v___x_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_385_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
return v___x_388_;
}
}
}
else
{
lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_413_ = lean_string_utf8_next_fast(v_fst_373_, v_snd_374_);
lean_dec(v_snd_374_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 1, v___x_413_);
v___x_415_ = v___x_378_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_fst_373_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v___x_413_);
v___x_415_ = v_reuseFailAlloc_417_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; 
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v_acc_371_);
return v___x_416_;
}
}
}
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec_ref(v_acc_371_);
v___x_421_ = lean_box(0);
v___x_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_422_, 0, v_a_372_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_str(lean_object* v_a_423_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_425_ = l_Lean_Json_Parser_strCore(v___x_424_, v_a_423_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCore(lean_object* v_acc_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_fst_428_; lean_object* v_snd_429_; lean_object* v___x_430_; uint8_t v_decide_431_; 
v_fst_428_ = lean_ctor_get(v_a_427_, 0);
v_snd_429_ = lean_ctor_get(v_a_427_, 1);
v___x_430_ = lean_string_utf8_byte_size(v_fst_428_);
v_decide_431_ = lean_nat_dec_eq(v_snd_429_, v___x_430_);
if (v_decide_431_ == 0)
{
uint32_t v___x_432_; uint32_t v___x_433_; uint8_t v___x_434_; 
v___x_432_ = lean_string_utf8_get_fast(v_fst_428_, v_snd_429_);
v___x_433_ = 48;
v___x_434_ = lean_uint32_dec_le(v___x_433_, v___x_432_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v_a_427_);
lean_ctor_set(v___x_435_, 1, v_acc_426_);
return v___x_435_;
}
else
{
uint32_t v___x_436_; uint8_t v___x_437_; 
v___x_436_ = 57;
v___x_437_ = lean_uint32_dec_le(v___x_432_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v_a_427_);
lean_ctor_set(v___x_438_, 1, v_acc_426_);
return v___x_438_;
}
else
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_452_; 
lean_inc(v_snd_429_);
lean_inc(v_fst_428_);
v_isSharedCheck_452_ = !lean_is_exclusive(v_a_427_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; lean_object* v_unused_454_; 
v_unused_453_ = lean_ctor_get(v_a_427_, 1);
lean_dec(v_unused_453_);
v_unused_454_ = lean_ctor_get(v_a_427_, 0);
lean_dec(v_unused_454_);
v___x_440_ = v_a_427_;
v_isShared_441_ = v_isSharedCheck_452_;
goto v_resetjp_439_;
}
else
{
lean_dec(v_a_427_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_452_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = lean_string_utf8_next_fast(v_fst_428_, v_snd_429_);
lean_dec(v_snd_429_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___x_442_);
v___x_444_ = v___x_440_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_fst_428_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v___x_442_);
v___x_444_ = v_reuseFailAlloc_451_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; uint32_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_445_ = lean_unsigned_to_nat(10u);
v___x_446_ = lean_nat_mul(v___x_445_, v_acc_426_);
lean_dec(v_acc_426_);
v___x_447_ = lean_uint32_sub(v___x_432_, v___x_433_);
v___x_448_ = lean_uint32_to_nat(v___x_447_);
v___x_449_ = lean_nat_add(v___x_446_, v___x_448_);
lean_dec(v___x_448_);
lean_dec(v___x_446_);
v_acc_426_ = v___x_449_;
v_a_427_ = v___x_444_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_455_; 
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v_a_427_);
lean_ctor_set(v___x_455_, 1, v_acc_426_);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCoreNumDigits(lean_object* v_acc_456_, lean_object* v_digits_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_fst_462_; lean_object* v_snd_463_; lean_object* v___x_464_; uint8_t v_decide_465_; 
v_fst_462_ = lean_ctor_get(v_a_458_, 0);
v_snd_463_ = lean_ctor_get(v_a_458_, 1);
v___x_464_ = lean_string_utf8_byte_size(v_fst_462_);
v_decide_465_ = lean_nat_dec_eq(v_snd_463_, v___x_464_);
if (v_decide_465_ == 0)
{
uint32_t v___x_466_; uint32_t v___x_467_; uint8_t v___x_468_; 
v___x_466_ = lean_string_utf8_get_fast(v_fst_462_, v_snd_463_);
v___x_467_ = 48;
v___x_468_ = lean_uint32_dec_le(v___x_467_, v___x_466_);
if (v___x_468_ == 0)
{
goto v___jp_459_;
}
else
{
uint32_t v___x_469_; uint8_t v___x_470_; 
v___x_469_ = 57;
v___x_470_ = lean_uint32_dec_le(v___x_466_, v___x_469_);
if (v___x_470_ == 0)
{
goto v___jp_459_;
}
else
{
lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_486_; 
lean_inc(v_snd_463_);
lean_inc(v_fst_462_);
v_isSharedCheck_486_ = !lean_is_exclusive(v_a_458_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; lean_object* v_unused_488_; 
v_unused_487_ = lean_ctor_get(v_a_458_, 1);
lean_dec(v_unused_487_);
v_unused_488_ = lean_ctor_get(v_a_458_, 0);
lean_dec(v_unused_488_);
v___x_472_ = v_a_458_;
v_isShared_473_ = v_isSharedCheck_486_;
goto v_resetjp_471_;
}
else
{
lean_dec(v_a_458_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_486_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_474_ = lean_string_utf8_next_fast(v_fst_462_, v_snd_463_);
lean_dec(v_snd_463_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v___x_474_);
v___x_476_ = v___x_472_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_fst_462_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_474_);
v___x_476_ = v_reuseFailAlloc_485_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; uint32_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_477_ = lean_unsigned_to_nat(10u);
v___x_478_ = lean_nat_mul(v___x_477_, v_acc_456_);
lean_dec(v_acc_456_);
v___x_479_ = lean_uint32_sub(v___x_466_, v___x_467_);
v___x_480_ = lean_uint32_to_nat(v___x_479_);
v___x_481_ = lean_nat_add(v___x_478_, v___x_480_);
lean_dec(v___x_480_);
lean_dec(v___x_478_);
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_nat_add(v_digits_457_, v___x_482_);
lean_dec(v_digits_457_);
v_acc_456_ = v___x_481_;
v_digits_457_ = v___x_483_;
v_a_458_ = v___x_476_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v_acc_456_);
lean_ctor_set(v___x_489_, 1, v_digits_457_);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v_a_458_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
return v___x_490_;
}
v___jp_459_:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v_acc_456_);
lean_ctor_set(v___x_460_, 1, v_digits_457_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v_a_458_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg(lean_object* v_desc_492_, lean_object* v_inst_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_fst_495_; lean_object* v_snd_496_; lean_object* v___x_497_; uint8_t v_decide_498_; 
v_fst_495_ = lean_ctor_get(v_a_494_, 0);
v_snd_496_ = lean_ctor_get(v_a_494_, 1);
v___x_497_ = lean_string_utf8_byte_size(v_fst_495_);
v_decide_498_ = lean_nat_dec_eq(v_snd_496_, v___x_497_);
if (v_decide_498_ == 0)
{
uint32_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_499_ = lean_string_utf8_get_fast(v_fst_495_, v_snd_496_);
v___x_500_ = lean_box_uint32(v___x_499_);
v___x_501_ = lean_apply_1(v_inst_493_, v___x_500_);
v___x_502_ = lean_unbox(v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_503_ = ((lean_object*)(l_Lean_Json_Parser_lookahead___redArg___closed__0));
v___x_504_ = lean_string_append(v___x_503_, v_desc_492_);
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
v___x_506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_506_, 0, v_a_494_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
return v___x_506_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_box(0);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v_a_494_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
return v___x_508_;
}
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec_ref(v_inst_493_);
v___x_509_ = lean_box(0);
v___x_510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_510_, 0, v_a_494_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg___boxed(lean_object* v_desc_511_, lean_object* v_inst_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Json_Parser_lookahead___redArg(v_desc_511_, v_inst_512_, v_a_513_);
lean_dec_ref(v_desc_511_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead(lean_object* v_p_515_, lean_object* v_desc_516_, lean_object* v_inst_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_fst_519_; lean_object* v_snd_520_; lean_object* v___x_521_; uint8_t v_decide_522_; 
v_fst_519_ = lean_ctor_get(v_a_518_, 0);
v_snd_520_ = lean_ctor_get(v_a_518_, 1);
v___x_521_ = lean_string_utf8_byte_size(v_fst_519_);
v_decide_522_ = lean_nat_dec_eq(v_snd_520_, v___x_521_);
if (v_decide_522_ == 0)
{
uint32_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_523_ = lean_string_utf8_get_fast(v_fst_519_, v_snd_520_);
v___x_524_ = lean_box_uint32(v___x_523_);
v___x_525_ = lean_apply_1(v_inst_517_, v___x_524_);
v___x_526_ = lean_unbox(v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_527_ = ((lean_object*)(l_Lean_Json_Parser_lookahead___redArg___closed__0));
v___x_528_ = lean_string_append(v___x_527_, v_desc_516_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
v___x_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_530_, 0, v_a_518_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
return v___x_530_;
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_box(0);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v_a_518_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
return v___x_532_;
}
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec_ref(v_inst_517_);
v___x_533_ = lean_box(0);
v___x_534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_534_, 0, v_a_518_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___boxed(lean_object* v_p_535_, lean_object* v_desc_536_, lean_object* v_inst_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Json_Parser_lookahead(v_p_535_, v_desc_536_, v_inst_537_, v_a_538_);
lean_dec_ref(v_desc_536_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNonZero(lean_object* v_a_543_){
_start:
{
lean_object* v_fst_547_; lean_object* v_snd_548_; lean_object* v___x_549_; uint8_t v_decide_550_; 
v_fst_547_ = lean_ctor_get(v_a_543_, 0);
v_snd_548_ = lean_ctor_get(v_a_543_, 1);
v___x_549_ = lean_string_utf8_byte_size(v_fst_547_);
v_decide_550_ = lean_nat_dec_eq(v_snd_548_, v___x_549_);
if (v_decide_550_ == 0)
{
uint32_t v___x_551_; uint32_t v___x_552_; uint8_t v___x_553_; 
v___x_551_ = lean_string_utf8_get_fast(v_fst_547_, v_snd_548_);
v___x_552_ = 49;
v___x_553_ = lean_uint32_dec_le(v___x_552_, v___x_551_);
if (v___x_553_ == 0)
{
goto v___jp_544_;
}
else
{
uint32_t v___x_554_; uint8_t v___x_555_; 
v___x_554_ = 57;
v___x_555_ = lean_uint32_dec_le(v___x_551_, v___x_554_);
if (v___x_555_ == 0)
{
goto v___jp_544_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = l_Lean_Json_Parser_natCore(v___x_556_, v_a_543_);
return v___x_557_;
}
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_box(0);
v___x_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_559_, 0, v_a_543_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
return v___x_559_;
}
v___jp_544_:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_546_, 0, v_a_543_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNumDigits(lean_object* v_a_563_){
_start:
{
lean_object* v_fst_567_; lean_object* v_snd_568_; lean_object* v___x_569_; uint8_t v_decide_570_; 
v_fst_567_ = lean_ctor_get(v_a_563_, 0);
v_snd_568_ = lean_ctor_get(v_a_563_, 1);
v___x_569_ = lean_string_utf8_byte_size(v_fst_567_);
v_decide_570_ = lean_nat_dec_eq(v_snd_568_, v___x_569_);
if (v_decide_570_ == 0)
{
uint32_t v___x_571_; uint32_t v___x_572_; uint8_t v___x_573_; 
v___x_571_ = lean_string_utf8_get_fast(v_fst_567_, v_snd_568_);
v___x_572_ = 48;
v___x_573_ = lean_uint32_dec_le(v___x_572_, v___x_571_);
if (v___x_573_ == 0)
{
goto v___jp_564_;
}
else
{
uint32_t v___x_574_; uint8_t v___x_575_; 
v___x_574_ = 57;
v___x_575_ = lean_uint32_dec_le(v___x_571_, v___x_574_);
if (v___x_575_ == 0)
{
goto v___jp_564_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_576_, v___x_576_, v_a_563_);
return v___x_577_;
}
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_box(0);
v___x_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_579_, 0, v_a_563_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
return v___x_579_;
}
v___jp_564_:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_566_, 0, v_a_563_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natMaybeZero(lean_object* v_a_583_){
_start:
{
lean_object* v_fst_587_; lean_object* v_snd_588_; lean_object* v___x_589_; uint8_t v_decide_590_; 
v_fst_587_ = lean_ctor_get(v_a_583_, 0);
v_snd_588_ = lean_ctor_get(v_a_583_, 1);
v___x_589_ = lean_string_utf8_byte_size(v_fst_587_);
v_decide_590_ = lean_nat_dec_eq(v_snd_588_, v___x_589_);
if (v_decide_590_ == 0)
{
uint32_t v___x_591_; uint32_t v___x_592_; uint8_t v___x_593_; 
v___x_591_ = lean_string_utf8_get_fast(v_fst_587_, v_snd_588_);
v___x_592_ = 48;
v___x_593_ = lean_uint32_dec_le(v___x_592_, v___x_591_);
if (v___x_593_ == 0)
{
goto v___jp_584_;
}
else
{
uint32_t v___x_594_; uint8_t v___x_595_; 
v___x_594_ = 57;
v___x_595_ = lean_uint32_dec_le(v___x_591_, v___x_594_);
if (v___x_595_ == 0)
{
goto v___jp_584_;
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = l_Lean_Json_Parser_natCore(v___x_596_, v_a_583_);
return v___x_597_;
}
}
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_box(0);
v___x_599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_599_, 0, v_a_583_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
return v___x_599_;
}
v___jp_584_:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_586_, 0, v_a_583_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
return v___x_586_;
}
}
}
static lean_object* _init_l_Lean_Json_Parser_numSign___closed__0(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_to_int(v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_Json_Parser_numSign___closed__1(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v___x_603_ = lean_int_neg(v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numSign(lean_object* v_a_604_){
_start:
{
lean_object* v_fst_605_; lean_object* v_snd_606_; lean_object* v___x_607_; uint8_t v_decide_608_; 
v_fst_605_ = lean_ctor_get(v_a_604_, 0);
v_snd_606_ = lean_ctor_get(v_a_604_, 1);
v___x_607_ = lean_string_utf8_byte_size(v_fst_605_);
v_decide_608_ = lean_nat_dec_eq(v_snd_606_, v___x_607_);
if (v_decide_608_ == 0)
{
uint32_t v___x_609_; uint32_t v___x_610_; uint8_t v___x_611_; 
v___x_609_ = lean_string_utf8_get_fast(v_fst_605_, v_snd_606_);
v___x_610_ = 45;
v___x_611_ = lean_uint32_dec_eq(v___x_609_, v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v_a_604_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
return v___x_613_;
}
else
{
lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_623_; 
lean_inc(v_snd_606_);
lean_inc(v_fst_605_);
v_isSharedCheck_623_ = !lean_is_exclusive(v_a_604_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; lean_object* v_unused_625_; 
v_unused_624_ = lean_ctor_get(v_a_604_, 1);
lean_dec(v_unused_624_);
v_unused_625_ = lean_ctor_get(v_a_604_, 0);
lean_dec(v_unused_625_);
v___x_615_ = v_a_604_;
v_isShared_616_ = v_isSharedCheck_623_;
goto v_resetjp_614_;
}
else
{
lean_dec(v_a_604_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_623_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_617_ = lean_string_utf8_next_fast(v_fst_605_, v_snd_606_);
lean_dec(v_snd_606_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 1, v___x_617_);
v___x_619_ = v___x_615_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_fst_605_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v___x_617_);
v___x_619_ = v_reuseFailAlloc_622_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
return v___x_621_;
}
}
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_box(0);
v___x_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_627_, 0, v_a_604_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_nat(lean_object* v_a_628_){
_start:
{
lean_object* v_fst_632_; lean_object* v_snd_633_; lean_object* v___x_634_; uint8_t v_decide_635_; 
v_fst_632_ = lean_ctor_get(v_a_628_, 0);
v_snd_633_ = lean_ctor_get(v_a_628_, 1);
v___x_634_ = lean_string_utf8_byte_size(v_fst_632_);
v_decide_635_ = lean_nat_dec_eq(v_snd_633_, v___x_634_);
if (v_decide_635_ == 0)
{
uint32_t v___x_636_; uint32_t v___x_637_; uint8_t v___x_638_; 
v___x_636_ = lean_string_utf8_get_fast(v_fst_632_, v_snd_633_);
v___x_637_ = 48;
v___x_638_ = lean_uint32_dec_eq(v___x_636_, v___x_637_);
if (v___x_638_ == 0)
{
uint32_t v___x_639_; uint8_t v___x_640_; 
v___x_639_ = 49;
v___x_640_ = lean_uint32_dec_le(v___x_639_, v___x_636_);
if (v___x_640_ == 0)
{
goto v___jp_629_;
}
else
{
uint32_t v___x_641_; uint8_t v___x_642_; 
v___x_641_ = 57;
v___x_642_ = lean_uint32_dec_le(v___x_636_, v___x_641_);
if (v___x_642_ == 0)
{
goto v___jp_629_;
}
else
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = l_Lean_Json_Parser_natCore(v___x_643_, v_a_628_);
return v___x_644_;
}
}
}
else
{
lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_654_; 
lean_inc(v_snd_633_);
lean_inc(v_fst_632_);
v_isSharedCheck_654_ = !lean_is_exclusive(v_a_628_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; lean_object* v_unused_656_; 
v_unused_655_ = lean_ctor_get(v_a_628_, 1);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v_a_628_, 0);
lean_dec(v_unused_656_);
v___x_646_ = v_a_628_;
v_isShared_647_ = v_isSharedCheck_654_;
goto v_resetjp_645_;
}
else
{
lean_dec(v_a_628_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_654_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = lean_string_utf8_next_fast(v_fst_632_, v_snd_633_);
lean_dec(v_snd_633_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 1, v___x_648_);
v___x_650_ = v___x_646_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_fst_632_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_648_);
v___x_650_ = v_reuseFailAlloc_653_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
return v___x_652_;
}
}
}
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_box(0);
v___x_658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_658_, 0, v_a_628_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
return v___x_658_;
}
v___jp_629_:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_631_, 0, v_a_628_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
return v___x_631_;
}
}
}
static lean_object* _init_l_Lean_Json_Parser_numWithDecimals___closed__0(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = l_System_Platform_numBits;
v___x_660_ = lean_unsigned_to_nat(2u);
v___x_661_ = lean_nat_pow(v___x_660_, v___x_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numWithDecimals(lean_object* v_a_665_){
_start:
{
lean_object* v___y_667_; lean_object* v___y_671_; lean_object* v_pos_672_; lean_object* v_fst_673_; lean_object* v_snd_674_; lean_object* v_res_675_; lean_object* v___y_743_; lean_object* v_pos_747_; lean_object* v_fst_748_; lean_object* v_snd_749_; lean_object* v_res_750_; lean_object* v_fst_780_; lean_object* v_snd_781_; lean_object* v___x_782_; uint8_t v_decide_783_; 
v_fst_780_ = lean_ctor_get(v_a_665_, 0);
v_snd_781_ = lean_ctor_get(v_a_665_, 1);
v___x_782_ = lean_string_utf8_byte_size(v_fst_780_);
v_decide_783_ = lean_nat_dec_eq(v_snd_781_, v___x_782_);
if (v_decide_783_ == 0)
{
uint32_t v___x_784_; uint32_t v___x_785_; uint8_t v___x_786_; 
lean_inc(v_snd_781_);
lean_inc(v_fst_780_);
v___x_784_ = lean_string_utf8_get_fast(v_fst_780_, v_snd_781_);
v___x_785_ = 45;
v___x_786_ = lean_uint32_dec_eq(v___x_784_, v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; 
v___x_787_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v_pos_747_ = v_a_665_;
v_fst_748_ = v_fst_780_;
v_snd_749_ = v_snd_781_;
v_res_750_ = v___x_787_;
goto v___jp_746_;
}
else
{
lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_796_; 
v_isSharedCheck_796_ = !lean_is_exclusive(v_a_665_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; lean_object* v_unused_798_; 
v_unused_797_ = lean_ctor_get(v_a_665_, 1);
lean_dec(v_unused_797_);
v_unused_798_ = lean_ctor_get(v_a_665_, 0);
lean_dec(v_unused_798_);
v___x_789_ = v_a_665_;
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
else
{
lean_dec(v_a_665_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = lean_string_utf8_next_fast(v_fst_780_, v_snd_781_);
lean_dec(v_snd_781_);
lean_inc(v_fst_780_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 1, v___x_791_);
v___x_793_ = v___x_789_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_fst_780_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_791_);
v___x_793_ = v_reuseFailAlloc_795_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; 
v___x_794_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v_pos_747_ = v___x_793_;
v_fst_748_ = v_fst_780_;
v_snd_749_ = v___x_791_;
v_res_750_ = v___x_794_;
goto v___jp_746_;
}
}
}
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_box(0);
v___x_800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_800_, 0, v_a_665_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
return v___x_800_;
}
v___jp_666_:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_669_, 0, v___y_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
return v___x_669_;
}
v___jp_670_:
{
lean_object* v___x_676_; uint8_t v_decide_677_; 
v___x_676_ = lean_string_utf8_byte_size(v_fst_673_);
v_decide_677_ = lean_nat_dec_eq(v_snd_674_, v___x_676_);
if (v_decide_677_ == 0)
{
uint32_t v___x_678_; uint32_t v___x_679_; uint8_t v___x_680_; 
v___x_678_ = lean_string_utf8_get_fast(v_fst_673_, v_snd_674_);
v___x_679_ = 46;
v___x_680_ = lean_uint32_dec_eq(v___x_678_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
v___x_681_ = lean_nat_to_int(v_res_675_);
v___x_682_ = lean_int_mul(v___y_671_, v___x_681_);
lean_dec(v___x_681_);
v___x_683_ = l_Lean_JsonNumber_fromInt(v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v_pos_672_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
return v___x_684_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v_decide_687_; 
lean_dec_ref(v_pos_672_);
v___x_685_ = lean_string_utf8_next_fast(v_fst_673_, v_snd_674_);
lean_dec(v_snd_674_);
lean_inc(v_fst_673_);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v_fst_673_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v_decide_687_ = lean_nat_dec_eq(v___x_685_, v___x_676_);
if (v_decide_687_ == 0)
{
uint32_t v___x_688_; uint32_t v___x_689_; uint8_t v___x_690_; 
v___x_688_ = lean_string_utf8_get_fast(v_fst_673_, v___x_685_);
lean_dec(v_fst_673_);
v___x_689_ = 48;
v___x_690_ = lean_uint32_dec_le(v___x_689_, v___x_688_);
if (v___x_690_ == 0)
{
lean_dec(v_res_675_);
v___y_667_ = v___x_686_;
goto v___jp_666_;
}
else
{
uint32_t v___x_691_; uint8_t v___x_692_; 
v___x_691_ = 57;
v___x_692_ = lean_uint32_dec_le(v___x_688_, v___x_691_);
if (v___x_692_ == 0)
{
lean_dec(v_res_675_);
v___y_667_ = v___x_686_;
goto v___jp_666_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_693_, v___x_693_, v___x_686_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_res_695_; lean_object* v_pos_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_726_; 
v_res_695_ = lean_ctor_get(v___x_694_, 1);
v_pos_696_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_726_ == 0)
{
v___x_698_ = v___x_694_;
v_isShared_699_ = v_isSharedCheck_726_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_res_695_);
lean_inc(v_pos_696_);
lean_dec(v___x_694_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_726_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_fst_700_; lean_object* v_snd_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_725_; 
v_fst_700_ = lean_ctor_get(v_res_695_, 0);
v_snd_701_ = lean_ctor_get(v_res_695_, 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v_res_695_);
if (v_isSharedCheck_725_ == 0)
{
v___x_703_ = v_res_695_;
v_isShared_704_ = v_isSharedCheck_725_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_snd_701_);
lean_inc(v_fst_700_);
lean_dec(v_res_695_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_725_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_706_ = lean_nat_dec_lt(v___x_705_, v_snd_701_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_707_ = lean_nat_to_int(v_res_675_);
v___x_708_ = lean_unsigned_to_nat(10u);
v___x_709_ = lean_nat_pow(v___x_708_, v_snd_701_);
v___x_710_ = lean_nat_to_int(v___x_709_);
v___x_711_ = lean_int_mul(v___x_707_, v___x_710_);
lean_dec(v___x_710_);
lean_dec(v___x_707_);
v___x_712_ = lean_nat_to_int(v_fst_700_);
v___x_713_ = lean_int_add(v___x_711_, v___x_712_);
lean_dec(v___x_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_int_mul(v___y_671_, v___x_713_);
lean_dec(v___x_713_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_714_);
v___x_716_ = v___x_703_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_snd_701_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_716_);
v___x_718_ = v___x_698_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_pos_696_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
else
{
lean_object* v___x_721_; lean_object* v___x_723_; 
lean_del_object(v___x_703_);
lean_dec(v_snd_701_);
lean_dec(v_fst_700_);
lean_dec(v_res_675_);
v___x_721_ = ((lean_object*)(l_Lean_Json_Parser_numWithDecimals___closed__2));
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 1);
lean_ctor_set(v___x_698_, 1, v___x_721_);
v___x_723_ = v___x_698_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_pos_696_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
else
{
lean_object* v_pos_727_; lean_object* v_err_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec(v_res_675_);
v_pos_727_ = lean_ctor_get(v___x_694_, 0);
v_err_728_ = lean_ctor_get(v___x_694_, 1);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_694_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_err_728_);
lean_inc(v_pos_727_);
lean_dec(v___x_694_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_pos_727_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_err_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
}
else
{
lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec(v_res_675_);
lean_dec(v_fst_673_);
v___x_736_ = lean_box(0);
v___x_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_686_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
return v___x_737_;
}
}
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
v___x_738_ = lean_nat_to_int(v_res_675_);
v___x_739_ = lean_int_mul(v___y_671_, v___x_738_);
lean_dec(v___x_738_);
v___x_740_ = l_Lean_JsonNumber_fromInt(v___x_739_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v_pos_672_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
return v___x_741_;
}
}
v___jp_742_:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_745_, 0, v___y_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
return v___x_745_;
}
v___jp_746_:
{
lean_object* v___x_751_; uint8_t v_decide_752_; 
v___x_751_ = lean_string_utf8_byte_size(v_fst_748_);
v_decide_752_ = lean_nat_dec_eq(v_snd_749_, v___x_751_);
if (v_decide_752_ == 0)
{
uint32_t v___x_753_; uint32_t v___x_754_; uint8_t v___x_755_; 
v___x_753_ = lean_string_utf8_get_fast(v_fst_748_, v_snd_749_);
v___x_754_ = 48;
v___x_755_ = lean_uint32_dec_eq(v___x_753_, v___x_754_);
if (v___x_755_ == 0)
{
uint32_t v___x_756_; uint8_t v___x_757_; 
lean_dec(v_snd_749_);
lean_dec(v_fst_748_);
v___x_756_ = 49;
v___x_757_ = lean_uint32_dec_le(v___x_756_, v___x_753_);
if (v___x_757_ == 0)
{
v___y_743_ = v_pos_747_;
goto v___jp_742_;
}
else
{
uint32_t v___x_758_; uint8_t v___x_759_; 
v___x_758_ = 57;
v___x_759_ = lean_uint32_dec_le(v___x_753_, v___x_758_);
if (v___x_759_ == 0)
{
v___y_743_ = v_pos_747_;
goto v___jp_742_;
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = l_Lean_Json_Parser_natCore(v___x_760_, v_pos_747_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_pos_762_; lean_object* v_res_763_; lean_object* v_fst_764_; lean_object* v_snd_765_; 
v_pos_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_pos_762_);
v_res_763_ = lean_ctor_get(v___x_761_, 1);
lean_inc(v_res_763_);
lean_dec_ref_known(v___x_761_, 2);
v_fst_764_ = lean_ctor_get(v_pos_762_, 0);
lean_inc(v_fst_764_);
v_snd_765_ = lean_ctor_get(v_pos_762_, 1);
lean_inc(v_snd_765_);
v___y_671_ = v_res_750_;
v_pos_672_ = v_pos_762_;
v_fst_673_ = v_fst_764_;
v_snd_674_ = v_snd_765_;
v_res_675_ = v_res_763_;
goto v___jp_670_;
}
else
{
lean_object* v_pos_766_; lean_object* v_err_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
v_pos_766_ = lean_ctor_get(v___x_761_, 0);
v_err_767_ = lean_ctor_get(v___x_761_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_761_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_err_767_);
lean_inc(v_pos_766_);
lean_dec(v___x_761_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_pos_766_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_err_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
lean_dec_ref(v_pos_747_);
v___x_775_ = lean_string_utf8_next_fast(v_fst_748_, v_snd_749_);
lean_dec(v_snd_749_);
lean_inc(v_fst_748_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v_fst_748_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = lean_unsigned_to_nat(0u);
v___y_671_ = v_res_750_;
v_pos_672_ = v___x_776_;
v_fst_673_ = v_fst_748_;
v_snd_674_ = v___x_775_;
v_res_675_ = v___x_777_;
goto v___jp_670_;
}
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec(v_snd_749_);
lean_dec(v_fst_748_);
v___x_778_ = lean_box(0);
v___x_779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_779_, 0, v_pos_747_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
return v___x_779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent(lean_object* v_value_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___y_807_; lean_object* v___y_811_; lean_object* v___y_815_; lean_object* v_fst_816_; lean_object* v_snd_817_; lean_object* v_fst_854_; lean_object* v_snd_855_; lean_object* v___x_912_; uint8_t v_decide_913_; 
v_fst_854_ = lean_ctor_get(v_a_805_, 0);
v_snd_855_ = lean_ctor_get(v_a_805_, 1);
v___x_912_ = lean_string_utf8_byte_size(v_fst_854_);
v_decide_913_ = lean_nat_dec_eq(v_snd_855_, v___x_912_);
if (v_decide_913_ == 0)
{
uint32_t v___x_914_; uint32_t v___x_915_; uint8_t v___x_916_; 
v___x_914_ = lean_string_utf8_get_fast(v_fst_854_, v_snd_855_);
v___x_915_ = 101;
v___x_916_ = lean_uint32_dec_eq(v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
uint32_t v___x_917_; uint8_t v___x_918_; 
v___x_917_ = 69;
v___x_918_ = lean_uint32_dec_eq(v___x_914_, v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v_a_805_);
lean_ctor_set(v___x_919_, 1, v_value_804_);
return v___x_919_;
}
else
{
goto v___jp_856_;
}
}
else
{
goto v___jp_856_;
}
}
else
{
lean_object* v___x_920_; 
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v_a_805_);
lean_ctor_set(v___x_920_, 1, v_value_804_);
return v___x_920_;
}
v___jp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_809_, 0, v___y_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
return v___x_809_;
}
v___jp_810_:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_813_, 0, v___y_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
return v___x_813_;
}
v___jp_814_:
{
lean_object* v___x_818_; uint8_t v_decide_819_; 
v___x_818_ = lean_string_utf8_byte_size(v_fst_816_);
v_decide_819_ = lean_nat_dec_eq(v_snd_817_, v___x_818_);
if (v_decide_819_ == 0)
{
uint32_t v___x_820_; uint32_t v___x_821_; uint8_t v___x_822_; 
v___x_820_ = lean_string_utf8_get_fast(v_fst_816_, v_snd_817_);
lean_dec(v_snd_817_);
lean_dec(v_fst_816_);
v___x_821_ = 48;
v___x_822_ = lean_uint32_dec_le(v___x_821_, v___x_820_);
if (v___x_822_ == 0)
{
lean_dec_ref(v_value_804_);
v___y_811_ = v___y_815_;
goto v___jp_810_;
}
else
{
uint32_t v___x_823_; uint8_t v___x_824_; 
v___x_823_ = 57;
v___x_824_ = lean_uint32_dec_le(v___x_820_, v___x_823_);
if (v___x_824_ == 0)
{
lean_dec_ref(v_value_804_);
v___y_811_ = v___y_815_;
goto v___jp_810_;
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = l_Lean_Json_Parser_natCore(v___x_825_, v___y_815_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_pos_827_; lean_object* v_res_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_842_; 
v_pos_827_ = lean_ctor_get(v___x_826_, 0);
v_res_828_ = lean_ctor_get(v___x_826_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_842_ == 0)
{
v___x_830_ = v___x_826_;
v_isShared_831_ = v_isSharedCheck_842_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_res_828_);
lean_inc(v_pos_827_);
lean_dec(v___x_826_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_842_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = lean_unsigned_to_nat(100000u);
v___x_833_ = lean_nat_dec_lt(v___x_832_, v_res_828_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = l_Lean_JsonNumber_shiftl(v_value_804_, v_res_828_);
lean_dec(v_res_828_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 1, v___x_834_);
v___x_836_ = v___x_830_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_pos_827_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
else
{
lean_object* v___x_838_; lean_object* v___x_840_; 
lean_dec(v_res_828_);
lean_dec_ref(v_value_804_);
v___x_838_ = ((lean_object*)(l_Lean_Json_Parser_exponent___closed__1));
if (v_isShared_831_ == 0)
{
lean_ctor_set_tag(v___x_830_, 1);
lean_ctor_set(v___x_830_, 1, v___x_838_);
v___x_840_ = v___x_830_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_pos_827_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
lean_object* v_pos_843_; lean_object* v_err_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec_ref(v_value_804_);
v_pos_843_ = lean_ctor_get(v___x_826_, 0);
v_err_844_ = lean_ctor_get(v___x_826_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_826_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_err_844_);
lean_inc(v_pos_843_);
lean_dec(v___x_826_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_pos_843_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_err_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec(v_snd_817_);
lean_dec(v_fst_816_);
lean_dec_ref(v_value_804_);
v___x_852_ = lean_box(0);
v___x_853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_853_, 0, v___y_815_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
return v___x_853_;
}
}
v___jp_856_:
{
lean_object* v___x_857_; uint8_t v_decide_858_; 
v___x_857_ = lean_string_utf8_byte_size(v_fst_854_);
v_decide_858_ = lean_nat_dec_eq(v_snd_855_, v___x_857_);
if (v_decide_858_ == 0)
{
lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_907_; 
lean_inc(v_snd_855_);
lean_inc(v_fst_854_);
v_isSharedCheck_907_ = !lean_is_exclusive(v_a_805_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; lean_object* v_unused_909_; 
v_unused_908_ = lean_ctor_get(v_a_805_, 1);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v_a_805_, 0);
lean_dec(v_unused_909_);
v___x_860_ = v_a_805_;
v_isShared_861_ = v_isSharedCheck_907_;
goto v_resetjp_859_;
}
else
{
lean_dec(v_a_805_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_907_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_862_ = lean_string_utf8_next_fast(v_fst_854_, v_snd_855_);
lean_dec(v_snd_855_);
lean_inc(v_fst_854_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 1, v___x_862_);
v___x_864_ = v___x_860_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_fst_854_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_862_);
v___x_864_ = v_reuseFailAlloc_906_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
uint8_t v_decide_865_; 
v_decide_865_ = lean_nat_dec_eq(v___x_862_, v___x_857_);
if (v_decide_865_ == 0)
{
uint32_t v___x_866_; uint32_t v___x_867_; uint8_t v___x_868_; 
v___x_866_ = lean_string_utf8_get_fast(v_fst_854_, v___x_862_);
v___x_867_ = 45;
v___x_868_ = lean_uint32_dec_eq(v___x_866_, v___x_867_);
if (v___x_868_ == 0)
{
uint32_t v___x_869_; uint8_t v___x_870_; 
v___x_869_ = 43;
v___x_870_ = lean_uint32_dec_eq(v___x_866_, v___x_869_);
if (v___x_870_ == 0)
{
v___y_815_ = v___x_864_;
v_fst_816_ = v_fst_854_;
v_snd_817_ = v___x_862_;
goto v___jp_814_;
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec_ref(v___x_864_);
v___x_871_ = lean_string_utf8_next_fast(v_fst_854_, v___x_862_);
lean_inc(v_fst_854_);
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v_fst_854_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___y_815_ = v___x_872_;
v_fst_816_ = v_fst_854_;
v_snd_817_ = v___x_871_;
goto v___jp_814_;
}
}
else
{
lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v_decide_875_; 
lean_dec_ref(v___x_864_);
v___x_873_ = lean_string_utf8_next_fast(v_fst_854_, v___x_862_);
lean_inc(v_fst_854_);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v_fst_854_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v_decide_875_ = lean_nat_dec_eq(v___x_873_, v___x_857_);
if (v_decide_875_ == 0)
{
uint32_t v___x_876_; uint32_t v___x_877_; uint8_t v___x_878_; 
v___x_876_ = lean_string_utf8_get_fast(v_fst_854_, v___x_873_);
lean_dec(v_fst_854_);
v___x_877_ = 48;
v___x_878_ = lean_uint32_dec_le(v___x_877_, v___x_876_);
if (v___x_878_ == 0)
{
lean_dec_ref(v_value_804_);
v___y_807_ = v___x_874_;
goto v___jp_806_;
}
else
{
uint32_t v___x_879_; uint8_t v___x_880_; 
v___x_879_ = 57;
v___x_880_ = lean_uint32_dec_le(v___x_876_, v___x_879_);
if (v___x_880_ == 0)
{
lean_dec_ref(v_value_804_);
v___y_807_ = v___x_874_;
goto v___jp_806_;
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = l_Lean_Json_Parser_natCore(v___x_881_, v___x_874_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_pos_883_; lean_object* v_res_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_892_; 
v_pos_883_ = lean_ctor_get(v___x_882_, 0);
v_res_884_ = lean_ctor_get(v___x_882_, 1);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_892_ == 0)
{
v___x_886_ = v___x_882_;
v_isShared_887_ = v_isSharedCheck_892_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_res_884_);
lean_inc(v_pos_883_);
lean_dec(v___x_882_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_892_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_888_ = l_Lean_JsonNumber_shiftr(v_value_804_, v_res_884_);
lean_dec(v_res_884_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 1, v___x_888_);
v___x_890_ = v___x_886_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_pos_883_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
else
{
lean_object* v_pos_893_; lean_object* v_err_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v_value_804_);
v_pos_893_ = lean_ctor_get(v___x_882_, 0);
v_err_894_ = lean_ctor_get(v___x_882_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_882_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_err_894_);
lean_inc(v_pos_893_);
lean_dec(v___x_882_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_pos_893_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_err_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
else
{
lean_object* v___x_902_; lean_object* v___x_903_; 
lean_dec(v_fst_854_);
lean_dec_ref(v_value_804_);
v___x_902_ = lean_box(0);
v___x_903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_874_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
return v___x_903_;
}
}
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; 
lean_dec(v_fst_854_);
lean_dec_ref(v_value_804_);
v___x_904_ = lean_box(0);
v___x_905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_864_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
return v___x_905_;
}
}
}
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; 
lean_dec_ref(v_value_804_);
v___x_910_ = lean_box(0);
v___x_911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_911_, 0, v_a_805_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
return v___x_911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Json_Parser_num_spec__0(lean_object* v_a_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = lean_nat_to_int(v_a_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_num(lean_object* v_a_923_){
_start:
{
lean_object* v___y_925_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v_fst_931_; lean_object* v_snd_932_; lean_object* v___y_970_; lean_object* v___y_974_; lean_object* v_fst_975_; lean_object* v_snd_976_; lean_object* v___y_977_; lean_object* v___y_1026_; lean_object* v_pos_1027_; lean_object* v_fst_1028_; lean_object* v_snd_1029_; lean_object* v_res_1030_; lean_object* v___y_1039_; lean_object* v___y_1043_; lean_object* v_pos_1044_; lean_object* v_fst_1045_; lean_object* v_snd_1046_; lean_object* v_res_1047_; lean_object* v___y_1117_; lean_object* v_pos_1121_; lean_object* v_fst_1122_; lean_object* v_snd_1123_; lean_object* v_res_1124_; lean_object* v_fst_1154_; lean_object* v_snd_1155_; lean_object* v___x_1156_; uint8_t v_decide_1157_; 
v_fst_1154_ = lean_ctor_get(v_a_923_, 0);
v_snd_1155_ = lean_ctor_get(v_a_923_, 1);
v___x_1156_ = lean_string_utf8_byte_size(v_fst_1154_);
v_decide_1157_ = lean_nat_dec_eq(v_snd_1155_, v___x_1156_);
if (v_decide_1157_ == 0)
{
uint32_t v___x_1158_; uint32_t v___x_1159_; uint8_t v___x_1160_; 
lean_inc(v_snd_1155_);
lean_inc(v_fst_1154_);
v___x_1158_ = lean_string_utf8_get_fast(v_fst_1154_, v_snd_1155_);
v___x_1159_ = 45;
v___x_1160_ = lean_uint32_dec_eq(v___x_1158_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v_pos_1121_ = v_a_923_;
v_fst_1122_ = v_fst_1154_;
v_snd_1123_ = v_snd_1155_;
v_res_1124_ = v___x_1161_;
goto v___jp_1120_;
}
else
{
lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1170_; 
v_isSharedCheck_1170_ = !lean_is_exclusive(v_a_923_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; lean_object* v_unused_1172_; 
v_unused_1171_ = lean_ctor_get(v_a_923_, 1);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_a_923_, 0);
lean_dec(v_unused_1172_);
v___x_1163_ = v_a_923_;
v_isShared_1164_ = v_isSharedCheck_1170_;
goto v_resetjp_1162_;
}
else
{
lean_dec(v_a_923_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1170_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1165_ = lean_string_utf8_next_fast(v_fst_1154_, v_snd_1155_);
lean_dec(v_snd_1155_);
lean_inc(v_fst_1154_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v___x_1165_);
v___x_1167_ = v___x_1163_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_fst_1154_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v_pos_1121_ = v___x_1167_;
v_fst_1122_ = v_fst_1154_;
v_snd_1123_ = v___x_1165_;
v_res_1124_ = v___x_1168_;
goto v___jp_1120_;
}
}
}
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_box(0);
v___x_1174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1174_, 0, v_a_923_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
return v___x_1174_;
}
v___jp_924_:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_927_, 0, v___y_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
return v___x_927_;
}
v___jp_928_:
{
lean_object* v___x_933_; uint8_t v_decide_934_; 
v___x_933_ = lean_string_utf8_byte_size(v_fst_931_);
v_decide_934_ = lean_nat_dec_eq(v_snd_932_, v___x_933_);
if (v_decide_934_ == 0)
{
uint32_t v___x_935_; uint32_t v___x_936_; uint8_t v___x_937_; 
v___x_935_ = lean_string_utf8_get_fast(v_fst_931_, v_snd_932_);
lean_dec(v_snd_932_);
lean_dec(v_fst_931_);
v___x_936_ = 48;
v___x_937_ = lean_uint32_dec_le(v___x_936_, v___x_935_);
if (v___x_937_ == 0)
{
lean_dec_ref(v___y_929_);
v___y_925_ = v___y_930_;
goto v___jp_924_;
}
else
{
uint32_t v___x_938_; uint8_t v___x_939_; 
v___x_938_ = 57;
v___x_939_ = lean_uint32_dec_le(v___x_935_, v___x_938_);
if (v___x_939_ == 0)
{
lean_dec_ref(v___y_929_);
v___y_925_ = v___y_930_;
goto v___jp_924_;
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = l_Lean_Json_Parser_natCore(v___x_940_, v___y_930_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_pos_942_; lean_object* v_res_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_957_; 
v_pos_942_ = lean_ctor_get(v___x_941_, 0);
v_res_943_ = lean_ctor_get(v___x_941_, 1);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_957_ == 0)
{
v___x_945_ = v___x_941_;
v_isShared_946_ = v_isSharedCheck_957_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_res_943_);
lean_inc(v_pos_942_);
lean_dec(v___x_941_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_957_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_947_ = lean_unsigned_to_nat(100000u);
v___x_948_ = lean_nat_dec_lt(v___x_947_, v_res_943_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_949_ = l_Lean_JsonNumber_shiftl(v___y_929_, v_res_943_);
lean_dec(v_res_943_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v___x_949_);
v___x_951_ = v___x_945_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_pos_942_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
else
{
lean_object* v___x_953_; lean_object* v___x_955_; 
lean_dec(v_res_943_);
lean_dec_ref(v___y_929_);
v___x_953_ = ((lean_object*)(l_Lean_Json_Parser_exponent___closed__1));
if (v_isShared_946_ == 0)
{
lean_ctor_set_tag(v___x_945_, 1);
lean_ctor_set(v___x_945_, 1, v___x_953_);
v___x_955_ = v___x_945_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_pos_942_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_object* v_pos_958_; lean_object* v_err_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_dec_ref(v___y_929_);
v_pos_958_ = lean_ctor_get(v___x_941_, 0);
v_err_959_ = lean_ctor_get(v___x_941_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_941_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_err_959_);
lean_inc(v_pos_958_);
lean_dec(v___x_941_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_pos_958_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_err_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec(v_snd_932_);
lean_dec(v_fst_931_);
lean_dec_ref(v___y_929_);
v___x_967_ = lean_box(0);
v___x_968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_968_, 0, v___y_930_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
return v___x_968_;
}
}
v___jp_969_:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_972_, 0, v___y_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
return v___x_972_;
}
v___jp_973_:
{
lean_object* v___x_978_; uint8_t v_decide_979_; 
v___x_978_ = lean_string_utf8_byte_size(v_fst_975_);
v_decide_979_ = lean_nat_dec_eq(v_snd_976_, v___x_978_);
if (v_decide_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v_decide_982_; 
lean_dec_ref(v___y_974_);
v___x_980_ = lean_string_utf8_next_fast(v_fst_975_, v_snd_976_);
lean_dec(v_snd_976_);
lean_inc(v_fst_975_);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v_fst_975_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v_decide_982_ = lean_nat_dec_eq(v___x_980_, v___x_978_);
if (v_decide_982_ == 0)
{
uint32_t v___x_983_; uint32_t v___x_984_; uint8_t v___x_985_; 
v___x_983_ = lean_string_utf8_get_fast(v_fst_975_, v___x_980_);
v___x_984_ = 45;
v___x_985_ = lean_uint32_dec_eq(v___x_983_, v___x_984_);
if (v___x_985_ == 0)
{
uint32_t v___x_986_; uint8_t v___x_987_; 
v___x_986_ = 43;
v___x_987_ = lean_uint32_dec_eq(v___x_983_, v___x_986_);
if (v___x_987_ == 0)
{
v___y_929_ = v___y_977_;
v___y_930_ = v___x_981_;
v_fst_931_ = v_fst_975_;
v_snd_932_ = v___x_980_;
goto v___jp_928_;
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec_ref_known(v___x_981_, 2);
v___x_988_ = lean_string_utf8_next_fast(v_fst_975_, v___x_980_);
lean_inc(v_fst_975_);
v___x_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_989_, 0, v_fst_975_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___y_929_ = v___y_977_;
v___y_930_ = v___x_989_;
v_fst_931_ = v_fst_975_;
v_snd_932_ = v___x_988_;
goto v___jp_928_;
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v_decide_992_; 
lean_dec_ref_known(v___x_981_, 2);
v___x_990_ = lean_string_utf8_next_fast(v_fst_975_, v___x_980_);
lean_inc(v_fst_975_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_fst_975_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v_decide_992_ = lean_nat_dec_eq(v___x_990_, v___x_978_);
if (v_decide_992_ == 0)
{
uint32_t v___x_993_; uint32_t v___x_994_; uint8_t v___x_995_; 
v___x_993_ = lean_string_utf8_get_fast(v_fst_975_, v___x_990_);
lean_dec(v_fst_975_);
v___x_994_ = 48;
v___x_995_ = lean_uint32_dec_le(v___x_994_, v___x_993_);
if (v___x_995_ == 0)
{
lean_dec_ref(v___y_977_);
v___y_970_ = v___x_991_;
goto v___jp_969_;
}
else
{
uint32_t v___x_996_; uint8_t v___x_997_; 
v___x_996_ = 57;
v___x_997_ = lean_uint32_dec_le(v___x_993_, v___x_996_);
if (v___x_997_ == 0)
{
lean_dec_ref(v___y_977_);
v___y_970_ = v___x_991_;
goto v___jp_969_;
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_unsigned_to_nat(0u);
v___x_999_ = l_Lean_Json_Parser_natCore(v___x_998_, v___x_991_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_pos_1000_; lean_object* v_res_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1009_; 
v_pos_1000_ = lean_ctor_get(v___x_999_, 0);
v_res_1001_ = lean_ctor_get(v___x_999_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1003_ = v___x_999_;
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_res_1001_);
lean_inc(v_pos_1000_);
lean_dec(v___x_999_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1005_ = l_Lean_JsonNumber_shiftr(v___y_977_, v_res_1001_);
lean_dec(v_res_1001_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 1, v___x_1005_);
v___x_1007_ = v___x_1003_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_pos_1000_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
else
{
lean_object* v_pos_1010_; lean_object* v_err_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec_ref(v___y_977_);
v_pos_1010_ = lean_ctor_get(v___x_999_, 0);
v_err_1011_ = lean_ctor_get(v___x_999_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_999_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_err_1011_);
lean_inc(v_pos_1010_);
lean_dec(v___x_999_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_pos_1010_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_err_1011_);
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
lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec_ref(v___y_977_);
lean_dec(v_fst_975_);
v___x_1019_ = lean_box(0);
v___x_1020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_991_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
return v___x_1020_;
}
}
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec_ref(v___y_977_);
lean_dec(v_fst_975_);
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_981_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
return v___x_1022_;
}
}
else
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_dec_ref(v___y_977_);
lean_dec(v_snd_976_);
lean_dec(v_fst_975_);
v___x_1023_ = lean_box(0);
v___x_1024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___y_974_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
return v___x_1024_;
}
}
v___jp_1025_:
{
lean_object* v___x_1031_; uint8_t v_decide_1032_; 
v___x_1031_ = lean_string_utf8_byte_size(v_fst_1028_);
v_decide_1032_ = lean_nat_dec_eq(v_snd_1029_, v___x_1031_);
if (v_decide_1032_ == 0)
{
uint32_t v___x_1033_; uint32_t v___x_1034_; uint8_t v___x_1035_; 
v___x_1033_ = lean_string_utf8_get_fast(v_fst_1028_, v_snd_1029_);
v___x_1034_ = 101;
v___x_1035_ = lean_uint32_dec_eq(v___x_1033_, v___x_1034_);
if (v___x_1035_ == 0)
{
uint32_t v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = 69;
v___x_1037_ = lean_uint32_dec_eq(v___x_1033_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_dec_ref(v_res_1030_);
lean_dec(v_snd_1029_);
lean_dec(v_fst_1028_);
lean_dec_ref(v_pos_1027_);
return v___y_1026_;
}
else
{
lean_dec_ref(v___y_1026_);
v___y_974_ = v_pos_1027_;
v_fst_975_ = v_fst_1028_;
v_snd_976_ = v_snd_1029_;
v___y_977_ = v_res_1030_;
goto v___jp_973_;
}
}
else
{
lean_dec_ref(v___y_1026_);
v___y_974_ = v_pos_1027_;
v_fst_975_ = v_fst_1028_;
v_snd_976_ = v_snd_1029_;
v___y_977_ = v_res_1030_;
goto v___jp_973_;
}
}
else
{
lean_dec_ref(v_res_1030_);
lean_dec(v_snd_1029_);
lean_dec(v_fst_1028_);
lean_dec_ref(v_pos_1027_);
return v___y_1026_;
}
}
v___jp_1038_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_1041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___y_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
return v___x_1041_;
}
v___jp_1042_:
{
lean_object* v___x_1048_; uint8_t v_decide_1049_; 
v___x_1048_ = lean_string_utf8_byte_size(v_fst_1045_);
v_decide_1049_ = lean_nat_dec_eq(v_snd_1046_, v___x_1048_);
if (v_decide_1049_ == 0)
{
uint32_t v___x_1050_; uint32_t v___x_1051_; uint8_t v___x_1052_; 
v___x_1050_ = lean_string_utf8_get_fast(v_fst_1045_, v_snd_1046_);
v___x_1051_ = 46;
v___x_1052_ = lean_uint32_dec_eq(v___x_1050_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1053_ = lean_nat_to_int(v_res_1047_);
v___x_1054_ = lean_int_mul(v___y_1043_, v___x_1053_);
lean_dec(v___x_1053_);
v___x_1055_ = l_Lean_JsonNumber_fromInt(v___x_1054_);
lean_inc_ref(v___x_1055_);
lean_inc_ref(v_pos_1044_);
v___x_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_pos_1044_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___y_1026_ = v___x_1056_;
v_pos_1027_ = v_pos_1044_;
v_fst_1028_ = v_fst_1045_;
v_snd_1029_ = v_snd_1046_;
v_res_1030_ = v___x_1055_;
goto v___jp_1025_;
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v_decide_1059_; 
lean_dec_ref(v_pos_1044_);
v___x_1057_ = lean_string_utf8_next_fast(v_fst_1045_, v_snd_1046_);
lean_dec(v_snd_1046_);
lean_inc(v_fst_1045_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v_fst_1045_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v_decide_1059_ = lean_nat_dec_eq(v___x_1057_, v___x_1048_);
if (v_decide_1059_ == 0)
{
uint32_t v___x_1060_; uint32_t v___x_1061_; uint8_t v___x_1062_; 
v___x_1060_ = lean_string_utf8_get_fast(v_fst_1045_, v___x_1057_);
lean_dec(v_fst_1045_);
v___x_1061_ = 48;
v___x_1062_ = lean_uint32_dec_le(v___x_1061_, v___x_1060_);
if (v___x_1062_ == 0)
{
lean_dec(v_res_1047_);
v___y_1039_ = v___x_1058_;
goto v___jp_1038_;
}
else
{
uint32_t v___x_1063_; uint8_t v___x_1064_; 
v___x_1063_ = 57;
v___x_1064_ = lean_uint32_dec_le(v___x_1060_, v___x_1063_);
if (v___x_1064_ == 0)
{
lean_dec(v_res_1047_);
v___y_1039_ = v___x_1058_;
goto v___jp_1038_;
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_1065_, v___x_1065_, v___x_1058_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_res_1067_; lean_object* v_pos_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1100_; 
v_res_1067_ = lean_ctor_get(v___x_1066_, 1);
v_pos_1068_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1070_ = v___x_1066_;
v_isShared_1071_ = v_isSharedCheck_1100_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_res_1067_);
lean_inc(v_pos_1068_);
lean_dec(v___x_1066_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1100_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v_fst_1072_; lean_object* v_snd_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1099_; 
v_fst_1072_ = lean_ctor_get(v_res_1067_, 0);
v_snd_1073_ = lean_ctor_get(v_res_1067_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_res_1067_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1075_ = v_res_1067_;
v_isShared_1076_ = v_isSharedCheck_1099_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_snd_1073_);
lean_inc(v_fst_1072_);
lean_dec(v_res_1067_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1099_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1077_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_1078_ = lean_nat_dec_lt(v___x_1077_, v_snd_1073_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v_fst_1081_; lean_object* v_snd_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1079_ = lean_unsigned_to_nat(10u);
v___x_1080_ = lean_nat_pow(v___x_1079_, v_snd_1073_);
v_fst_1081_ = lean_ctor_get(v_pos_1068_, 0);
lean_inc(v_fst_1081_);
v_snd_1082_ = lean_ctor_get(v_pos_1068_, 1);
lean_inc(v_snd_1082_);
v___x_1083_ = lean_nat_to_int(v_res_1047_);
v___x_1084_ = lean_nat_to_int(v___x_1080_);
v___x_1085_ = lean_int_mul(v___x_1083_, v___x_1084_);
lean_dec(v___x_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_nat_to_int(v_fst_1072_);
v___x_1087_ = lean_int_add(v___x_1085_, v___x_1086_);
lean_dec(v___x_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_int_mul(v___y_1043_, v___x_1087_);
lean_dec(v___x_1087_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1088_);
v___x_1090_ = v___x_1075_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_snd_1073_);
v___x_1090_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1092_; 
lean_inc_ref(v___x_1090_);
lean_inc(v_pos_1068_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 1, v___x_1090_);
v___x_1092_ = v___x_1070_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_pos_1068_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
v___y_1026_ = v___x_1092_;
v_pos_1027_ = v_pos_1068_;
v_fst_1028_ = v_fst_1081_;
v_snd_1029_ = v_snd_1082_;
v_res_1030_ = v___x_1090_;
goto v___jp_1025_;
}
}
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
lean_del_object(v___x_1075_);
lean_dec(v_snd_1073_);
lean_dec(v_fst_1072_);
lean_dec(v_res_1047_);
v___x_1095_ = ((lean_object*)(l_Lean_Json_Parser_numWithDecimals___closed__2));
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 1);
lean_ctor_set(v___x_1070_, 1, v___x_1095_);
v___x_1097_ = v___x_1070_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_pos_1068_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
else
{
lean_object* v_pos_1101_; lean_object* v_err_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec(v_res_1047_);
v_pos_1101_ = lean_ctor_get(v___x_1066_, 0);
v_err_1102_ = lean_ctor_get(v___x_1066_, 1);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1066_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_err_1102_);
lean_inc(v_pos_1101_);
lean_dec(v___x_1066_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_pos_1101_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_err_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
}
else
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_dec(v_res_1047_);
lean_dec(v_fst_1045_);
v___x_1110_ = lean_box(0);
v___x_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1058_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
return v___x_1111_;
}
}
}
else
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1112_ = lean_nat_to_int(v_res_1047_);
v___x_1113_ = lean_int_mul(v___y_1043_, v___x_1112_);
lean_dec(v___x_1112_);
v___x_1114_ = l_Lean_JsonNumber_fromInt(v___x_1113_);
lean_inc_ref(v___x_1114_);
lean_inc_ref(v_pos_1044_);
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v_pos_1044_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___y_1026_ = v___x_1115_;
v_pos_1027_ = v_pos_1044_;
v_fst_1028_ = v_fst_1045_;
v_snd_1029_ = v_snd_1046_;
v_res_1030_ = v___x_1114_;
goto v___jp_1025_;
}
}
v___jp_1116_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_1119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___y_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
return v___x_1119_;
}
v___jp_1120_:
{
lean_object* v___x_1125_; uint8_t v_decide_1126_; 
v___x_1125_ = lean_string_utf8_byte_size(v_fst_1122_);
v_decide_1126_ = lean_nat_dec_eq(v_snd_1123_, v___x_1125_);
if (v_decide_1126_ == 0)
{
uint32_t v___x_1127_; uint32_t v___x_1128_; uint8_t v___x_1129_; 
v___x_1127_ = lean_string_utf8_get_fast(v_fst_1122_, v_snd_1123_);
v___x_1128_ = 48;
v___x_1129_ = lean_uint32_dec_eq(v___x_1127_, v___x_1128_);
if (v___x_1129_ == 0)
{
uint32_t v___x_1130_; uint8_t v___x_1131_; 
lean_dec(v_snd_1123_);
lean_dec(v_fst_1122_);
v___x_1130_ = 49;
v___x_1131_ = lean_uint32_dec_le(v___x_1130_, v___x_1127_);
if (v___x_1131_ == 0)
{
v___y_1117_ = v_pos_1121_;
goto v___jp_1116_;
}
else
{
uint32_t v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = 57;
v___x_1133_ = lean_uint32_dec_le(v___x_1127_, v___x_1132_);
if (v___x_1133_ == 0)
{
v___y_1117_ = v_pos_1121_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = l_Lean_Json_Parser_natCore(v___x_1134_, v_pos_1121_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_pos_1136_; lean_object* v_res_1137_; lean_object* v_fst_1138_; lean_object* v_snd_1139_; 
v_pos_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_pos_1136_);
v_res_1137_ = lean_ctor_get(v___x_1135_, 1);
lean_inc(v_res_1137_);
lean_dec_ref_known(v___x_1135_, 2);
v_fst_1138_ = lean_ctor_get(v_pos_1136_, 0);
lean_inc(v_fst_1138_);
v_snd_1139_ = lean_ctor_get(v_pos_1136_, 1);
lean_inc(v_snd_1139_);
v___y_1043_ = v_res_1124_;
v_pos_1044_ = v_pos_1136_;
v_fst_1045_ = v_fst_1138_;
v_snd_1046_ = v_snd_1139_;
v_res_1047_ = v_res_1137_;
goto v___jp_1042_;
}
else
{
lean_object* v_pos_1140_; lean_object* v_err_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_pos_1140_ = lean_ctor_get(v___x_1135_, 0);
v_err_1141_ = lean_ctor_get(v___x_1135_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1135_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_err_1141_);
lean_inc(v_pos_1140_);
lean_dec(v___x_1135_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_pos_1140_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_err_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec_ref(v_pos_1121_);
v___x_1149_ = lean_string_utf8_next_fast(v_fst_1122_, v_snd_1123_);
lean_dec(v_snd_1123_);
lean_inc(v_fst_1122_);
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v_fst_1122_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = lean_unsigned_to_nat(0u);
v___y_1043_ = v_res_1124_;
v_pos_1044_ = v___x_1150_;
v_fst_1045_ = v_fst_1122_;
v_snd_1046_ = v___x_1149_;
v_res_1047_ = v___x_1151_;
goto v___jp_1042_;
}
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_dec(v_snd_1123_);
lean_dec(v_fst_1122_);
v___x_1152_ = lean_box(0);
v___x_1153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_pos_1121_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
return v___x_1153_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2___redArg(lean_object* v_k_1175_, lean_object* v_t_1176_){
_start:
{
if (lean_obj_tag(v_t_1176_) == 0)
{
lean_object* v_k_1177_; lean_object* v_l_1178_; lean_object* v_r_1179_; uint8_t v___x_1180_; 
v_k_1177_ = lean_ctor_get(v_t_1176_, 1);
v_l_1178_ = lean_ctor_get(v_t_1176_, 3);
v_r_1179_ = lean_ctor_get(v_t_1176_, 4);
v___x_1180_ = lean_string_compare(v_k_1175_, v_k_1177_);
switch(v___x_1180_)
{
case 0:
{
v_t_1176_ = v_l_1178_;
goto _start;
}
case 1:
{
uint8_t v___x_1182_; 
v___x_1182_ = 1;
return v___x_1182_;
}
default: 
{
v_t_1176_ = v_r_1179_;
goto _start;
}
}
}
else
{
uint8_t v___x_1184_; 
v___x_1184_ = 0;
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2___redArg___boxed(lean_object* v_k_1185_, lean_object* v_t_1186_){
_start:
{
uint8_t v_res_1187_; lean_object* v_r_1188_; 
v_res_1187_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_1185_, v_t_1186_);
lean_dec(v_t_1186_);
lean_dec_ref(v_k_1185_);
v_r_1188_ = lean_box(v_res_1187_);
return v_r_1188_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3_spec__3___redArg(lean_object* v_msg_1189_){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_box(1);
v___x_1191_ = lean_panic_fn_borrowed(v___x_1190_, v_msg_1189_);
return v___x_1191_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1195_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__2));
v___x_1196_ = lean_unsigned_to_nat(35u);
v___x_1197_ = lean_unsigned_to_nat(182u);
v___x_1198_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__1));
v___x_1199_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__0));
v___x_1200_ = l_mkPanicMessageWithDecl(v___x_1199_, v___x_1198_, v___x_1197_, v___x_1196_, v___x_1195_);
return v___x_1200_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1201_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__2));
v___x_1202_ = lean_unsigned_to_nat(21u);
v___x_1203_ = lean_unsigned_to_nat(183u);
v___x_1204_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__1));
v___x_1205_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__0));
v___x_1206_ = l_mkPanicMessageWithDecl(v___x_1205_, v___x_1204_, v___x_1203_, v___x_1202_, v___x_1201_);
return v___x_1206_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1209_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__6));
v___x_1210_ = lean_unsigned_to_nat(35u);
v___x_1211_ = lean_unsigned_to_nat(276u);
v___x_1212_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__5));
v___x_1213_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__0));
v___x_1214_ = l_mkPanicMessageWithDecl(v___x_1213_, v___x_1212_, v___x_1211_, v___x_1210_, v___x_1209_);
return v___x_1214_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1215_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__6));
v___x_1216_ = lean_unsigned_to_nat(21u);
v___x_1217_ = lean_unsigned_to_nat(277u);
v___x_1218_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__5));
v___x_1219_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__0));
v___x_1220_ = l_mkPanicMessageWithDecl(v___x_1219_, v___x_1218_, v___x_1217_, v___x_1216_, v___x_1215_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg(lean_object* v_k_1221_, lean_object* v_v_1222_, lean_object* v_t_1223_){
_start:
{
if (lean_obj_tag(v_t_1223_) == 0)
{
lean_object* v_size_1224_; lean_object* v_k_1225_; lean_object* v_v_1226_; lean_object* v_l_1227_; lean_object* v_r_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1584_; 
v_size_1224_ = lean_ctor_get(v_t_1223_, 0);
v_k_1225_ = lean_ctor_get(v_t_1223_, 1);
v_v_1226_ = lean_ctor_get(v_t_1223_, 2);
v_l_1227_ = lean_ctor_get(v_t_1223_, 3);
v_r_1228_ = lean_ctor_get(v_t_1223_, 4);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_t_1223_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1230_ = v_t_1223_;
v_isShared_1231_ = v_isSharedCheck_1584_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_r_1228_);
lean_inc(v_l_1227_);
lean_inc(v_v_1226_);
lean_inc(v_k_1225_);
lean_inc(v_size_1224_);
lean_dec(v_t_1223_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1584_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
uint8_t v___x_1232_; 
v___x_1232_ = lean_string_compare(v_k_1221_, v_k_1225_);
switch(v___x_1232_)
{
case 0:
{
lean_object* v___x_1233_; 
lean_dec(v_size_1224_);
v___x_1233_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg(v_k_1221_, v_v_1222_, v_l_1227_);
if (lean_obj_tag(v_r_1228_) == 0)
{
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_size_1234_; lean_object* v_size_1235_; lean_object* v_k_1236_; lean_object* v_v_1237_; lean_object* v_l_1238_; lean_object* v_r_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v_size_1234_ = lean_ctor_get(v_r_1228_, 0);
v_size_1235_ = lean_ctor_get(v___x_1233_, 0);
v_k_1236_ = lean_ctor_get(v___x_1233_, 1);
v_v_1237_ = lean_ctor_get(v___x_1233_, 2);
v_l_1238_ = lean_ctor_get(v___x_1233_, 3);
v_r_1239_ = lean_ctor_get(v___x_1233_, 4);
lean_inc(v_r_1239_);
v___x_1240_ = lean_unsigned_to_nat(3u);
v___x_1241_ = lean_nat_mul(v___x_1240_, v_size_1234_);
v___x_1242_ = lean_nat_dec_lt(v___x_1241_, v_size_1235_);
lean_dec(v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; 
lean_dec(v_r_1239_);
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = lean_nat_add(v___x_1243_, v_size_1235_);
v___x_1245_ = lean_nat_add(v___x_1244_, v_size_1234_);
lean_dec(v___x_1244_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 3, v___x_1233_);
lean_ctor_set(v___x_1230_, 0, v___x_1245_);
v___x_1247_ = v___x_1230_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1248_, 3, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1248_, 4, v_r_1228_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
else
{
lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1320_; 
lean_inc(v_l_1238_);
lean_inc(v_v_1237_);
lean_inc(v_k_1236_);
lean_inc(v_size_1235_);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; lean_object* v_unused_1322_; lean_object* v_unused_1323_; lean_object* v_unused_1324_; lean_object* v_unused_1325_; 
v_unused_1321_ = lean_ctor_get(v___x_1233_, 4);
lean_dec(v_unused_1321_);
v_unused_1322_ = lean_ctor_get(v___x_1233_, 3);
lean_dec(v_unused_1322_);
v_unused_1323_ = lean_ctor_get(v___x_1233_, 2);
lean_dec(v_unused_1323_);
v_unused_1324_ = lean_ctor_get(v___x_1233_, 1);
lean_dec(v_unused_1324_);
v_unused_1325_ = lean_ctor_get(v___x_1233_, 0);
lean_dec(v_unused_1325_);
v___x_1250_ = v___x_1233_;
v_isShared_1251_ = v_isSharedCheck_1320_;
goto v_resetjp_1249_;
}
else
{
lean_dec(v___x_1233_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1320_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
if (lean_obj_tag(v_l_1238_) == 0)
{
if (lean_obj_tag(v_r_1239_) == 0)
{
lean_object* v_size_1252_; lean_object* v_size_1253_; lean_object* v_k_1254_; lean_object* v_v_1255_; lean_object* v_l_1256_; lean_object* v_r_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v_size_1252_ = lean_ctor_get(v_l_1238_, 0);
v_size_1253_ = lean_ctor_get(v_r_1239_, 0);
v_k_1254_ = lean_ctor_get(v_r_1239_, 1);
v_v_1255_ = lean_ctor_get(v_r_1239_, 2);
v_l_1256_ = lean_ctor_get(v_r_1239_, 3);
v_r_1257_ = lean_ctor_get(v_r_1239_, 4);
v___x_1258_ = lean_unsigned_to_nat(2u);
v___x_1259_ = lean_nat_mul(v___x_1258_, v_size_1252_);
v___x_1260_ = lean_nat_dec_lt(v_size_1253_, v___x_1259_);
lean_dec(v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1290_; 
lean_inc(v_r_1257_);
lean_inc(v_l_1256_);
lean_inc(v_v_1255_);
lean_inc(v_k_1254_);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_r_1239_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; lean_object* v_unused_1292_; lean_object* v_unused_1293_; lean_object* v_unused_1294_; lean_object* v_unused_1295_; 
v_unused_1291_ = lean_ctor_get(v_r_1239_, 4);
lean_dec(v_unused_1291_);
v_unused_1292_ = lean_ctor_get(v_r_1239_, 3);
lean_dec(v_unused_1292_);
v_unused_1293_ = lean_ctor_get(v_r_1239_, 2);
lean_dec(v_unused_1293_);
v_unused_1294_ = lean_ctor_get(v_r_1239_, 1);
lean_dec(v_unused_1294_);
v_unused_1295_ = lean_ctor_get(v_r_1239_, 0);
lean_dec(v_unused_1295_);
v___x_1262_ = v_r_1239_;
v_isShared_1263_ = v_isSharedCheck_1290_;
goto v_resetjp_1261_;
}
else
{
lean_dec(v_r_1239_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1290_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___x_1278_; lean_object* v___y_1280_; 
v___x_1264_ = lean_unsigned_to_nat(1u);
v___x_1265_ = lean_nat_add(v___x_1264_, v_size_1235_);
lean_dec(v_size_1235_);
v___x_1266_ = lean_nat_add(v___x_1265_, v_size_1234_);
lean_dec(v___x_1265_);
v___x_1278_ = lean_nat_add(v___x_1264_, v_size_1252_);
if (lean_obj_tag(v_l_1256_) == 0)
{
lean_object* v_size_1288_; 
v_size_1288_ = lean_ctor_get(v_l_1256_, 0);
lean_inc(v_size_1288_);
v___y_1280_ = v_size_1288_;
goto v___jp_1279_;
}
else
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_unsigned_to_nat(0u);
v___y_1280_ = v___x_1289_;
goto v___jp_1279_;
}
v___jp_1267_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = lean_nat_add(v___y_1268_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec(v___y_1268_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 4, v_r_1228_);
lean_ctor_set(v___x_1262_, 3, v_r_1257_);
lean_ctor_set(v___x_1262_, 2, v_v_1226_);
lean_ctor_set(v___x_1262_, 1, v_k_1225_);
lean_ctor_set(v___x_1262_, 0, v___x_1271_);
v___x_1273_ = v___x_1262_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v_r_1257_);
lean_ctor_set(v_reuseFailAlloc_1277_, 4, v_r_1228_);
v___x_1273_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1275_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 4, v___x_1273_);
lean_ctor_set(v___x_1250_, 3, v___y_1269_);
lean_ctor_set(v___x_1250_, 2, v_v_1255_);
lean_ctor_set(v___x_1250_, 1, v_k_1254_);
lean_ctor_set(v___x_1250_, 0, v___x_1266_);
v___x_1275_ = v___x_1250_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_k_1254_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_v_1255_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v___y_1269_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
v___jp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_nat_add(v___x_1278_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec(v___x_1278_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 4, v_l_1256_);
lean_ctor_set(v___x_1230_, 3, v_l_1238_);
lean_ctor_set(v___x_1230_, 2, v_v_1237_);
lean_ctor_set(v___x_1230_, 1, v_k_1236_);
lean_ctor_set(v___x_1230_, 0, v___x_1281_);
v___x_1283_ = v___x_1230_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_k_1236_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_v_1237_);
lean_ctor_set(v_reuseFailAlloc_1287_, 3, v_l_1238_);
lean_ctor_set(v_reuseFailAlloc_1287_, 4, v_l_1256_);
v___x_1283_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_nat_add(v___x_1264_, v_size_1234_);
if (lean_obj_tag(v_r_1257_) == 0)
{
lean_object* v_size_1285_; 
v_size_1285_ = lean_ctor_get(v_r_1257_, 0);
lean_inc(v_size_1285_);
v___y_1268_ = v___x_1284_;
v___y_1269_ = v___x_1283_;
v___y_1270_ = v_size_1285_;
goto v___jp_1267_;
}
else
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_unsigned_to_nat(0u);
v___y_1268_ = v___x_1284_;
v___y_1269_ = v___x_1283_;
v___y_1270_ = v___x_1286_;
goto v___jp_1267_;
}
}
}
}
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
lean_del_object(v___x_1230_);
v___x_1296_ = lean_unsigned_to_nat(1u);
v___x_1297_ = lean_nat_add(v___x_1296_, v_size_1235_);
lean_dec(v_size_1235_);
v___x_1298_ = lean_nat_add(v___x_1297_, v_size_1234_);
lean_dec(v___x_1297_);
v___x_1299_ = lean_nat_add(v___x_1296_, v_size_1234_);
v___x_1300_ = lean_nat_add(v___x_1299_, v_size_1253_);
lean_dec(v___x_1299_);
lean_inc_ref(v_r_1228_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 4, v_r_1228_);
lean_ctor_set(v___x_1250_, 3, v_r_1239_);
lean_ctor_set(v___x_1250_, 2, v_v_1226_);
lean_ctor_set(v___x_1250_, 1, v_k_1225_);
lean_ctor_set(v___x_1250_, 0, v___x_1300_);
v___x_1302_ = v___x_1250_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1315_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1315_, 3, v_r_1239_);
lean_ctor_set(v_reuseFailAlloc_1315_, 4, v_r_1228_);
v___x_1302_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
v_isSharedCheck_1309_ = !lean_is_exclusive(v_r_1228_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; lean_object* v_unused_1311_; lean_object* v_unused_1312_; lean_object* v_unused_1313_; lean_object* v_unused_1314_; 
v_unused_1310_ = lean_ctor_get(v_r_1228_, 4);
lean_dec(v_unused_1310_);
v_unused_1311_ = lean_ctor_get(v_r_1228_, 3);
lean_dec(v_unused_1311_);
v_unused_1312_ = lean_ctor_get(v_r_1228_, 2);
lean_dec(v_unused_1312_);
v_unused_1313_ = lean_ctor_get(v_r_1228_, 1);
lean_dec(v_unused_1313_);
v_unused_1314_ = lean_ctor_get(v_r_1228_, 0);
lean_dec(v_unused_1314_);
v___x_1304_ = v_r_1228_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_dec(v_r_1228_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 4, v___x_1302_);
lean_ctor_set(v___x_1304_, 3, v_l_1238_);
lean_ctor_set(v___x_1304_, 2, v_v_1237_);
lean_ctor_set(v___x_1304_, 1, v_k_1236_);
lean_ctor_set(v___x_1304_, 0, v___x_1298_);
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_k_1236_);
lean_ctor_set(v_reuseFailAlloc_1308_, 2, v_v_1237_);
lean_ctor_set(v_reuseFailAlloc_1308_, 3, v_l_1238_);
lean_ctor_set(v_reuseFailAlloc_1308_, 4, v___x_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec_ref_known(v_l_1238_, 5);
lean_del_object(v___x_1250_);
lean_dec(v_v_1237_);
lean_dec(v_k_1236_);
lean_dec(v_size_1235_);
lean_dec_ref_known(v_r_1228_, 5);
lean_del_object(v___x_1230_);
lean_dec(v_v_1226_);
lean_dec(v_k_1225_);
v___x_1316_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__3);
v___x_1317_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3_spec__3___redArg(v___x_1316_);
return v___x_1317_;
}
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_del_object(v___x_1250_);
lean_dec(v_r_1239_);
lean_dec(v_v_1237_);
lean_dec(v_k_1236_);
lean_dec(v_size_1235_);
lean_dec_ref_known(v_r_1228_, 5);
lean_del_object(v___x_1230_);
lean_dec(v_v_1226_);
lean_dec(v_k_1225_);
v___x_1318_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__4);
v___x_1319_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3_spec__3___redArg(v___x_1318_);
return v___x_1319_;
}
}
}
}
else
{
lean_object* v_size_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v_size_1326_ = lean_ctor_get(v_r_1228_, 0);
v___x_1327_ = lean_unsigned_to_nat(1u);
v___x_1328_ = lean_nat_add(v___x_1327_, v_size_1326_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 3, v___x_1233_);
lean_ctor_set(v___x_1230_, 0, v___x_1328_);
v___x_1330_ = v___x_1230_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1331_, 3, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1331_, 4, v_r_1228_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
else
{
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_l_1332_; 
v_l_1332_ = lean_ctor_get(v___x_1233_, 3);
if (lean_obj_tag(v_l_1332_) == 0)
{
lean_object* v_r_1333_; 
lean_inc_ref(v_l_1332_);
v_r_1333_ = lean_ctor_get(v___x_1233_, 4);
lean_inc(v_r_1333_);
if (lean_obj_tag(v_r_1333_) == 0)
{
lean_object* v_size_1334_; lean_object* v_k_1335_; lean_object* v_v_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1350_; 
v_size_1334_ = lean_ctor_get(v___x_1233_, 0);
v_k_1335_ = lean_ctor_get(v___x_1233_, 1);
v_v_1336_ = lean_ctor_get(v___x_1233_, 2);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; lean_object* v_unused_1352_; 
v_unused_1351_ = lean_ctor_get(v___x_1233_, 4);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v___x_1233_, 3);
lean_dec(v_unused_1352_);
v___x_1338_ = v___x_1233_;
v_isShared_1339_ = v_isSharedCheck_1350_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_v_1336_);
lean_inc(v_k_1335_);
lean_inc(v_size_1334_);
lean_dec(v___x_1233_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1350_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v_size_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v_size_1340_ = lean_ctor_get(v_r_1333_, 0);
v___x_1341_ = lean_unsigned_to_nat(1u);
v___x_1342_ = lean_nat_add(v___x_1341_, v_size_1334_);
lean_dec(v_size_1334_);
v___x_1343_ = lean_nat_add(v___x_1341_, v_size_1340_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 4, v_r_1228_);
lean_ctor_set(v___x_1338_, 3, v_r_1333_);
lean_ctor_set(v___x_1338_, 2, v_v_1226_);
lean_ctor_set(v___x_1338_, 1, v_k_1225_);
lean_ctor_set(v___x_1338_, 0, v___x_1343_);
v___x_1345_ = v___x_1338_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_r_1333_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v_r_1228_);
v___x_1345_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1347_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 4, v___x_1345_);
lean_ctor_set(v___x_1230_, 3, v_l_1332_);
lean_ctor_set(v___x_1230_, 2, v_v_1336_);
lean_ctor_set(v___x_1230_, 1, v_k_1335_);
lean_ctor_set(v___x_1230_, 0, v___x_1342_);
v___x_1347_ = v___x_1230_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_k_1335_);
lean_ctor_set(v_reuseFailAlloc_1348_, 2, v_v_1336_);
lean_ctor_set(v_reuseFailAlloc_1348_, 3, v_l_1332_);
lean_ctor_set(v_reuseFailAlloc_1348_, 4, v___x_1345_);
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
else
{
lean_object* v_k_1353_; lean_object* v_v_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1366_; 
v_k_1353_ = lean_ctor_get(v___x_1233_, 1);
v_v_1354_ = lean_ctor_get(v___x_1233_, 2);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; lean_object* v_unused_1368_; lean_object* v_unused_1369_; 
v_unused_1367_ = lean_ctor_get(v___x_1233_, 4);
lean_dec(v_unused_1367_);
v_unused_1368_ = lean_ctor_get(v___x_1233_, 3);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v___x_1233_, 0);
lean_dec(v_unused_1369_);
v___x_1356_ = v___x_1233_;
v_isShared_1357_ = v_isSharedCheck_1366_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_v_1354_);
lean_inc(v_k_1353_);
lean_dec(v___x_1233_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1366_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1358_ = lean_unsigned_to_nat(3u);
v___x_1359_ = lean_unsigned_to_nat(1u);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 3, v_r_1333_);
lean_ctor_set(v___x_1356_, 2, v_v_1226_);
lean_ctor_set(v___x_1356_, 1, v_k_1225_);
lean_ctor_set(v___x_1356_, 0, v___x_1359_);
v___x_1361_ = v___x_1356_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v_r_1333_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v_r_1333_);
v___x_1361_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1363_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 4, v___x_1361_);
lean_ctor_set(v___x_1230_, 3, v_l_1332_);
lean_ctor_set(v___x_1230_, 2, v_v_1354_);
lean_ctor_set(v___x_1230_, 1, v_k_1353_);
lean_ctor_set(v___x_1230_, 0, v___x_1358_);
v___x_1363_ = v___x_1230_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1364_, 3, v_l_1332_);
lean_ctor_set(v_reuseFailAlloc_1364_, 4, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
else
{
lean_object* v_r_1370_; 
v_r_1370_ = lean_ctor_get(v___x_1233_, 4);
lean_inc(v_r_1370_);
if (lean_obj_tag(v_r_1370_) == 0)
{
lean_object* v_k_1371_; lean_object* v_v_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1396_; 
lean_inc(v_l_1332_);
v_k_1371_ = lean_ctor_get(v___x_1233_, 1);
v_v_1372_ = lean_ctor_get(v___x_1233_, 2);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; lean_object* v_unused_1398_; lean_object* v_unused_1399_; 
v_unused_1397_ = lean_ctor_get(v___x_1233_, 4);
lean_dec(v_unused_1397_);
v_unused_1398_ = lean_ctor_get(v___x_1233_, 3);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v___x_1233_, 0);
lean_dec(v_unused_1399_);
v___x_1374_ = v___x_1233_;
v_isShared_1375_ = v_isSharedCheck_1396_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_v_1372_);
lean_inc(v_k_1371_);
lean_dec(v___x_1233_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1396_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v_k_1376_; lean_object* v_v_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1392_; 
v_k_1376_ = lean_ctor_get(v_r_1370_, 1);
v_v_1377_ = lean_ctor_get(v_r_1370_, 2);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_r_1370_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; lean_object* v_unused_1394_; lean_object* v_unused_1395_; 
v_unused_1393_ = lean_ctor_get(v_r_1370_, 4);
lean_dec(v_unused_1393_);
v_unused_1394_ = lean_ctor_get(v_r_1370_, 3);
lean_dec(v_unused_1394_);
v_unused_1395_ = lean_ctor_get(v_r_1370_, 0);
lean_dec(v_unused_1395_);
v___x_1379_ = v_r_1370_;
v_isShared_1380_ = v_isSharedCheck_1392_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_v_1377_);
lean_inc(v_k_1376_);
lean_dec(v_r_1370_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1392_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1381_ = lean_unsigned_to_nat(3u);
v___x_1382_ = lean_unsigned_to_nat(1u);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 4, v_l_1332_);
lean_ctor_set(v___x_1379_, 3, v_l_1332_);
lean_ctor_set(v___x_1379_, 2, v_v_1372_);
lean_ctor_set(v___x_1379_, 1, v_k_1371_);
lean_ctor_set(v___x_1379_, 0, v___x_1382_);
v___x_1384_ = v___x_1379_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_l_1332_);
lean_ctor_set(v_reuseFailAlloc_1391_, 4, v_l_1332_);
v___x_1384_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1386_; 
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 4, v_l_1332_);
lean_ctor_set(v___x_1374_, 2, v_v_1226_);
lean_ctor_set(v___x_1374_, 1, v_k_1225_);
lean_ctor_set(v___x_1374_, 0, v___x_1382_);
v___x_1386_ = v___x_1374_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_l_1332_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_l_1332_);
v___x_1386_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1388_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 4, v___x_1386_);
lean_ctor_set(v___x_1230_, 3, v___x_1384_);
lean_ctor_set(v___x_1230_, 2, v_v_1377_);
lean_ctor_set(v___x_1230_, 1, v_k_1376_);
lean_ctor_set(v___x_1230_, 0, v___x_1381_);
v___x_1388_ = v___x_1230_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_k_1376_);
lean_ctor_set(v_reuseFailAlloc_1389_, 2, v_v_1377_);
lean_ctor_set(v_reuseFailAlloc_1389_, 3, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1389_, 4, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1400_ = lean_unsigned_to_nat(2u);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 4, v_r_1370_);
lean_ctor_set(v___x_1230_, 3, v___x_1233_);
lean_ctor_set(v___x_1230_, 0, v___x_1400_);
v___x_1402_ = v___x_1230_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v_r_1370_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1404_ = lean_unsigned_to_nat(1u);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 4, v___x_1233_);
lean_ctor_set(v___x_1230_, 3, v___x_1233_);
lean_ctor_set(v___x_1230_, 0, v___x_1404_);
v___x_1406_ = v___x_1230_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1407_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1407_, 3, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1407_, 4, v___x_1233_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
case 1:
{
lean_object* v___x_1409_; 
lean_dec(v_v_1226_);
lean_dec(v_k_1225_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 2, v_v_1222_);
lean_ctor_set(v___x_1230_, 1, v_k_1221_);
v___x_1409_ = v___x_1230_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_size_1224_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_k_1221_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_v_1222_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v_l_1227_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_r_1228_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
default: 
{
lean_object* v___x_1411_; 
lean_dec(v_size_1224_);
v___x_1411_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg(v_k_1221_, v_v_1222_, v_r_1228_);
if (lean_obj_tag(v_l_1227_) == 0)
{
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_size_1412_; lean_object* v_size_1413_; lean_object* v_k_1414_; lean_object* v_v_1415_; lean_object* v_l_1416_; lean_object* v_r_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
v_size_1412_ = lean_ctor_get(v_l_1227_, 0);
v_size_1413_ = lean_ctor_get(v___x_1411_, 0);
v_k_1414_ = lean_ctor_get(v___x_1411_, 1);
v_v_1415_ = lean_ctor_get(v___x_1411_, 2);
v_l_1416_ = lean_ctor_get(v___x_1411_, 3);
lean_inc(v_l_1416_);
v_r_1417_ = lean_ctor_get(v___x_1411_, 4);
v___x_1418_ = lean_unsigned_to_nat(3u);
v___x_1419_ = lean_nat_mul(v___x_1418_, v_size_1412_);
v___x_1420_ = lean_nat_dec_lt(v___x_1419_, v_size_1413_);
lean_dec(v___x_1419_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
lean_dec(v_l_1416_);
v___x_1421_ = lean_unsigned_to_nat(1u);
v___x_1422_ = lean_nat_add(v___x_1421_, v_size_1412_);
v___x_1423_ = lean_nat_add(v___x_1422_, v_size_1413_);
lean_dec(v___x_1422_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 4, v___x_1411_);
lean_ctor_set(v___x_1230_, 0, v___x_1423_);
v___x_1425_ = v___x_1230_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1426_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1426_, 3, v_l_1227_);
lean_ctor_set(v_reuseFailAlloc_1426_, 4, v___x_1411_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
else
{
lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1496_; 
lean_inc(v_r_1417_);
lean_inc(v_v_1415_);
lean_inc(v_k_1414_);
lean_inc(v_size_1413_);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; lean_object* v_unused_1498_; lean_object* v_unused_1499_; lean_object* v_unused_1500_; lean_object* v_unused_1501_; 
v_unused_1497_ = lean_ctor_get(v___x_1411_, 4);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v___x_1411_, 3);
lean_dec(v_unused_1498_);
v_unused_1499_ = lean_ctor_get(v___x_1411_, 2);
lean_dec(v_unused_1499_);
v_unused_1500_ = lean_ctor_get(v___x_1411_, 1);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v___x_1411_, 0);
lean_dec(v_unused_1501_);
v___x_1428_ = v___x_1411_;
v_isShared_1429_ = v_isSharedCheck_1496_;
goto v_resetjp_1427_;
}
else
{
lean_dec(v___x_1411_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1496_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
if (lean_obj_tag(v_l_1416_) == 0)
{
if (lean_obj_tag(v_r_1417_) == 0)
{
lean_object* v_size_1430_; lean_object* v_k_1431_; lean_object* v_v_1432_; lean_object* v_l_1433_; lean_object* v_r_1434_; lean_object* v_size_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v_size_1430_ = lean_ctor_get(v_l_1416_, 0);
v_k_1431_ = lean_ctor_get(v_l_1416_, 1);
v_v_1432_ = lean_ctor_get(v_l_1416_, 2);
v_l_1433_ = lean_ctor_get(v_l_1416_, 3);
v_r_1434_ = lean_ctor_get(v_l_1416_, 4);
v_size_1435_ = lean_ctor_get(v_r_1417_, 0);
v___x_1436_ = lean_unsigned_to_nat(2u);
v___x_1437_ = lean_nat_mul(v___x_1436_, v_size_1435_);
v___x_1438_ = lean_nat_dec_lt(v_size_1430_, v___x_1437_);
lean_dec(v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1467_; 
lean_inc(v_r_1434_);
lean_inc(v_l_1433_);
lean_inc(v_v_1432_);
lean_inc(v_k_1431_);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_l_1416_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; lean_object* v_unused_1469_; lean_object* v_unused_1470_; lean_object* v_unused_1471_; lean_object* v_unused_1472_; 
v_unused_1468_ = lean_ctor_get(v_l_1416_, 4);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_l_1416_, 3);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_l_1416_, 2);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_l_1416_, 1);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_l_1416_, 0);
lean_dec(v_unused_1472_);
v___x_1440_ = v_l_1416_;
v_isShared_1441_ = v_isSharedCheck_1467_;
goto v_resetjp_1439_;
}
else
{
lean_dec(v_l_1416_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1467_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1457_; 
v___x_1442_ = lean_unsigned_to_nat(1u);
v___x_1443_ = lean_nat_add(v___x_1442_, v_size_1412_);
v___x_1444_ = lean_nat_add(v___x_1443_, v_size_1413_);
lean_dec(v_size_1413_);
if (lean_obj_tag(v_l_1433_) == 0)
{
lean_object* v_size_1465_; 
v_size_1465_ = lean_ctor_get(v_l_1433_, 0);
lean_inc(v_size_1465_);
v___y_1457_ = v_size_1465_;
goto v___jp_1456_;
}
else
{
lean_object* v___x_1466_; 
v___x_1466_ = lean_unsigned_to_nat(0u);
v___y_1457_ = v___x_1466_;
goto v___jp_1456_;
}
v___jp_1445_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = lean_nat_add(v___y_1446_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec(v___y_1446_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v_r_1417_);
lean_ctor_set(v___x_1440_, 3, v_r_1434_);
lean_ctor_set(v___x_1440_, 2, v_v_1415_);
lean_ctor_set(v___x_1440_, 1, v_k_1414_);
lean_ctor_set(v___x_1440_, 0, v___x_1449_);
v___x_1451_ = v___x_1440_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_k_1414_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_v_1415_);
lean_ctor_set(v_reuseFailAlloc_1455_, 3, v_r_1434_);
lean_ctor_set(v_reuseFailAlloc_1455_, 4, v_r_1417_);
v___x_1451_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1453_; 
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 4, v___x_1451_);
lean_ctor_set(v___x_1428_, 3, v___y_1447_);
lean_ctor_set(v___x_1428_, 2, v_v_1432_);
lean_ctor_set(v___x_1428_, 1, v_k_1431_);
lean_ctor_set(v___x_1428_, 0, v___x_1444_);
v___x_1453_ = v___x_1428_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_k_1431_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_v_1432_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v___y_1447_);
lean_ctor_set(v_reuseFailAlloc_1454_, 4, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
v___jp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1458_ = lean_nat_add(v___x_1443_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec(v___x_1443_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 4, v_l_1433_);
lean_ctor_set(v___x_1230_, 0, v___x_1458_);
v___x_1460_ = v___x_1230_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_l_1227_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v_l_1433_);
v___x_1460_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_nat_add(v___x_1442_, v_size_1435_);
if (lean_obj_tag(v_r_1434_) == 0)
{
lean_object* v_size_1462_; 
v_size_1462_ = lean_ctor_get(v_r_1434_, 0);
lean_inc(v_size_1462_);
v___y_1446_ = v___x_1461_;
v___y_1447_ = v___x_1460_;
v___y_1448_ = v_size_1462_;
goto v___jp_1445_;
}
else
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_unsigned_to_nat(0u);
v___y_1446_ = v___x_1461_;
v___y_1447_ = v___x_1460_;
v___y_1448_ = v___x_1463_;
goto v___jp_1445_;
}
}
}
}
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1478_; 
lean_del_object(v___x_1230_);
v___x_1473_ = lean_unsigned_to_nat(1u);
v___x_1474_ = lean_nat_add(v___x_1473_, v_size_1412_);
v___x_1475_ = lean_nat_add(v___x_1474_, v_size_1413_);
lean_dec(v_size_1413_);
v___x_1476_ = lean_nat_add(v___x_1474_, v_size_1430_);
lean_dec(v___x_1474_);
lean_inc_ref(v_l_1227_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 4, v_l_1416_);
lean_ctor_set(v___x_1428_, 3, v_l_1227_);
lean_ctor_set(v___x_1428_, 2, v_v_1226_);
lean_ctor_set(v___x_1428_, 1, v_k_1225_);
lean_ctor_set(v___x_1428_, 0, v___x_1476_);
v___x_1478_ = v___x_1428_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1491_, 3, v_l_1227_);
lean_ctor_set(v_reuseFailAlloc_1491_, 4, v_l_1416_);
v___x_1478_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
v_isSharedCheck_1485_ = !lean_is_exclusive(v_l_1227_);
if (v_isSharedCheck_1485_ == 0)
{
lean_object* v_unused_1486_; lean_object* v_unused_1487_; lean_object* v_unused_1488_; lean_object* v_unused_1489_; lean_object* v_unused_1490_; 
v_unused_1486_ = lean_ctor_get(v_l_1227_, 4);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v_l_1227_, 3);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_l_1227_, 2);
lean_dec(v_unused_1488_);
v_unused_1489_ = lean_ctor_get(v_l_1227_, 1);
lean_dec(v_unused_1489_);
v_unused_1490_ = lean_ctor_get(v_l_1227_, 0);
lean_dec(v_unused_1490_);
v___x_1480_ = v_l_1227_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_dec(v_l_1227_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 4, v_r_1417_);
lean_ctor_set(v___x_1480_, 3, v___x_1478_);
lean_ctor_set(v___x_1480_, 2, v_v_1415_);
lean_ctor_set(v___x_1480_, 1, v_k_1414_);
lean_ctor_set(v___x_1480_, 0, v___x_1475_);
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_k_1414_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_v_1415_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v_r_1417_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
else
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_dec_ref_known(v_l_1416_, 5);
lean_del_object(v___x_1428_);
lean_dec(v_v_1415_);
lean_dec(v_k_1414_);
lean_dec(v_size_1413_);
lean_dec_ref_known(v_l_1227_, 5);
lean_del_object(v___x_1230_);
lean_dec(v_v_1226_);
lean_dec(v_k_1225_);
v___x_1492_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__7);
v___x_1493_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3_spec__3___redArg(v___x_1492_);
return v___x_1493_;
}
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_del_object(v___x_1428_);
lean_dec(v_r_1417_);
lean_dec(v_v_1415_);
lean_dec(v_k_1414_);
lean_dec(v_size_1413_);
lean_dec_ref_known(v_l_1227_, 5);
lean_del_object(v___x_1230_);
lean_dec(v_v_1226_);
lean_dec(v_k_1225_);
v___x_1494_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__8);
v___x_1495_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3_spec__3___redArg(v___x_1494_);
return v___x_1495_;
}
}
}
}
else
{
lean_object* v_size_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1506_; 
v_size_1502_ = lean_ctor_get(v_l_1227_, 0);
v___x_1503_ = lean_unsigned_to_nat(1u);
v___x_1504_ = lean_nat_add(v___x_1503_, v_size_1502_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 4, v___x_1411_);
lean_ctor_set(v___x_1230_, 0, v___x_1504_);
v___x_1506_ = v___x_1230_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1507_, 3, v_l_1227_);
lean_ctor_set(v_reuseFailAlloc_1507_, 4, v___x_1411_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
else
{
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_l_1508_; 
v_l_1508_ = lean_ctor_get(v___x_1411_, 3);
lean_inc(v_l_1508_);
if (lean_obj_tag(v_l_1508_) == 0)
{
lean_object* v_r_1509_; 
v_r_1509_ = lean_ctor_get(v___x_1411_, 4);
lean_inc(v_r_1509_);
if (lean_obj_tag(v_r_1509_) == 0)
{
lean_object* v_size_1510_; lean_object* v_k_1511_; lean_object* v_v_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1526_; 
v_size_1510_ = lean_ctor_get(v___x_1411_, 0);
v_k_1511_ = lean_ctor_get(v___x_1411_, 1);
v_v_1512_ = lean_ctor_get(v___x_1411_, 2);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; lean_object* v_unused_1528_; 
v_unused_1527_ = lean_ctor_get(v___x_1411_, 4);
lean_dec(v_unused_1527_);
v_unused_1528_ = lean_ctor_get(v___x_1411_, 3);
lean_dec(v_unused_1528_);
v___x_1514_ = v___x_1411_;
v_isShared_1515_ = v_isSharedCheck_1526_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_v_1512_);
lean_inc(v_k_1511_);
lean_inc(v_size_1510_);
lean_dec(v___x_1411_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1526_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v_size_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1521_; 
v_size_1516_ = lean_ctor_get(v_l_1508_, 0);
v___x_1517_ = lean_unsigned_to_nat(1u);
v___x_1518_ = lean_nat_add(v___x_1517_, v_size_1510_);
lean_dec(v_size_1510_);
v___x_1519_ = lean_nat_add(v___x_1517_, v_size_1516_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 4, v_l_1508_);
lean_ctor_set(v___x_1514_, 3, v_l_1227_);
lean_ctor_set(v___x_1514_, 2, v_v_1226_);
lean_ctor_set(v___x_1514_, 1, v_k_1225_);
lean_ctor_set(v___x_1514_, 0, v___x_1519_);
v___x_1521_ = v___x_1514_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_l_1227_);
lean_ctor_set(v_reuseFailAlloc_1525_, 4, v_l_1508_);
v___x_1521_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1523_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 4, v_r_1509_);
lean_ctor_set(v___x_1230_, 3, v___x_1521_);
lean_ctor_set(v___x_1230_, 2, v_v_1512_);
lean_ctor_set(v___x_1230_, 1, v_k_1511_);
lean_ctor_set(v___x_1230_, 0, v___x_1518_);
v___x_1523_ = v___x_1230_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_k_1511_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_v_1512_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_r_1509_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
else
{
lean_object* v_k_1529_; lean_object* v_v_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1554_; 
v_k_1529_ = lean_ctor_get(v___x_1411_, 1);
v_v_1530_ = lean_ctor_get(v___x_1411_, 2);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; lean_object* v_unused_1556_; lean_object* v_unused_1557_; 
v_unused_1555_ = lean_ctor_get(v___x_1411_, 4);
lean_dec(v_unused_1555_);
v_unused_1556_ = lean_ctor_get(v___x_1411_, 3);
lean_dec(v_unused_1556_);
v_unused_1557_ = lean_ctor_get(v___x_1411_, 0);
lean_dec(v_unused_1557_);
v___x_1532_ = v___x_1411_;
v_isShared_1533_ = v_isSharedCheck_1554_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_v_1530_);
lean_inc(v_k_1529_);
lean_dec(v___x_1411_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1554_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v_k_1534_; lean_object* v_v_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1550_; 
v_k_1534_ = lean_ctor_get(v_l_1508_, 1);
v_v_1535_ = lean_ctor_get(v_l_1508_, 2);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_l_1508_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; lean_object* v_unused_1552_; lean_object* v_unused_1553_; 
v_unused_1551_ = lean_ctor_get(v_l_1508_, 4);
lean_dec(v_unused_1551_);
v_unused_1552_ = lean_ctor_get(v_l_1508_, 3);
lean_dec(v_unused_1552_);
v_unused_1553_ = lean_ctor_get(v_l_1508_, 0);
lean_dec(v_unused_1553_);
v___x_1537_ = v_l_1508_;
v_isShared_1538_ = v_isSharedCheck_1550_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_v_1535_);
lean_inc(v_k_1534_);
lean_dec(v_l_1508_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1550_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1539_ = lean_unsigned_to_nat(3u);
v___x_1540_ = lean_unsigned_to_nat(1u);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 4, v_r_1509_);
lean_ctor_set(v___x_1537_, 3, v_r_1509_);
lean_ctor_set(v___x_1537_, 2, v_v_1226_);
lean_ctor_set(v___x_1537_, 1, v_k_1225_);
lean_ctor_set(v___x_1537_, 0, v___x_1540_);
v___x_1542_ = v___x_1537_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v_r_1509_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v_r_1509_);
v___x_1542_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1544_; 
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 3, v_r_1509_);
lean_ctor_set(v___x_1532_, 0, v___x_1540_);
v___x_1544_ = v___x_1532_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_k_1529_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_v_1530_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_r_1509_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_r_1509_);
v___x_1544_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1546_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 4, v___x_1544_);
lean_ctor_set(v___x_1230_, 3, v___x_1542_);
lean_ctor_set(v___x_1230_, 2, v_v_1535_);
lean_ctor_set(v___x_1230_, 1, v_k_1534_);
lean_ctor_set(v___x_1230_, 0, v___x_1539_);
v___x_1546_ = v___x_1230_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_k_1534_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_v_1535_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1547_, 4, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1558_; 
v_r_1558_ = lean_ctor_get(v___x_1411_, 4);
lean_inc(v_r_1558_);
if (lean_obj_tag(v_r_1558_) == 0)
{
lean_object* v_k_1559_; lean_object* v_v_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1572_; 
v_k_1559_ = lean_ctor_get(v___x_1411_, 1);
v_v_1560_ = lean_ctor_get(v___x_1411_, 2);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1572_ == 0)
{
lean_object* v_unused_1573_; lean_object* v_unused_1574_; lean_object* v_unused_1575_; 
v_unused_1573_ = lean_ctor_get(v___x_1411_, 4);
lean_dec(v_unused_1573_);
v_unused_1574_ = lean_ctor_get(v___x_1411_, 3);
lean_dec(v_unused_1574_);
v_unused_1575_ = lean_ctor_get(v___x_1411_, 0);
lean_dec(v_unused_1575_);
v___x_1562_ = v___x_1411_;
v_isShared_1563_ = v_isSharedCheck_1572_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_v_1560_);
lean_inc(v_k_1559_);
lean_dec(v___x_1411_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1572_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1564_ = lean_unsigned_to_nat(3u);
v___x_1565_ = lean_unsigned_to_nat(1u);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 4, v_l_1508_);
lean_ctor_set(v___x_1562_, 2, v_v_1226_);
lean_ctor_set(v___x_1562_, 1, v_k_1225_);
lean_ctor_set(v___x_1562_, 0, v___x_1565_);
v___x_1567_ = v___x_1562_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1571_, 3, v_l_1508_);
lean_ctor_set(v_reuseFailAlloc_1571_, 4, v_l_1508_);
v___x_1567_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1569_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 4, v_r_1558_);
lean_ctor_set(v___x_1230_, 3, v___x_1567_);
lean_ctor_set(v___x_1230_, 2, v_v_1560_);
lean_ctor_set(v___x_1230_, 1, v_k_1559_);
lean_ctor_set(v___x_1230_, 0, v___x_1564_);
v___x_1569_ = v___x_1230_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_k_1559_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_v_1560_);
lean_ctor_set(v_reuseFailAlloc_1570_, 3, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1570_, 4, v_r_1558_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
else
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1576_ = lean_unsigned_to_nat(2u);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 4, v___x_1411_);
lean_ctor_set(v___x_1230_, 3, v_r_1558_);
lean_ctor_set(v___x_1230_, 0, v___x_1576_);
v___x_1578_ = v___x_1230_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1579_, 3, v_r_1558_);
lean_ctor_set(v_reuseFailAlloc_1579_, 4, v___x_1411_);
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
else
{
lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1580_ = lean_unsigned_to_nat(1u);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 4, v___x_1411_);
lean_ctor_set(v___x_1230_, 3, v___x_1411_);
lean_ctor_set(v___x_1230_, 0, v___x_1580_);
v___x_1582_ = v___x_1230_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1583_, 3, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1583_, 4, v___x_1411_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_unsigned_to_nat(1u);
v___x_1586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
lean_ctor_set(v___x_1586_, 1, v_k_1221_);
lean_ctor_set(v___x_1586_, 2, v_v_1222_);
lean_ctor_set(v___x_1586_, 3, v_t_1223_);
lean_ctor_set(v___x_1586_, 4, v_t_1223_);
return v___x_1586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore(lean_object* v_kvs_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_fst_1608_; lean_object* v_snd_1609_; lean_object* v___x_1610_; uint8_t v_decide_1611_; 
v_fst_1608_ = lean_ctor_get(v_a_1607_, 0);
v_snd_1609_ = lean_ctor_get(v_a_1607_, 1);
v___x_1610_ = lean_string_utf8_byte_size(v_fst_1608_);
v_decide_1611_ = lean_nat_dec_eq(v_snd_1609_, v___x_1610_);
if (v_decide_1611_ == 0)
{
uint32_t v___x_1612_; uint32_t v___x_1613_; uint8_t v___x_1614_; 
v___x_1612_ = lean_string_utf8_get_fast(v_fst_1608_, v_snd_1609_);
v___x_1613_ = 34;
v___x_1614_ = lean_uint32_dec_eq(v___x_1612_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec(v_kvs_1606_);
v___x_1615_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__1));
v___x_1616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1616_, 0, v_a_1607_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
return v___x_1616_;
}
else
{
lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1732_; 
lean_inc(v_snd_1609_);
lean_inc(v_fst_1608_);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_a_1607_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; lean_object* v_unused_1734_; 
v_unused_1733_ = lean_ctor_get(v_a_1607_, 1);
lean_dec(v_unused_1733_);
v_unused_1734_ = lean_ctor_get(v_a_1607_, 0);
lean_dec(v_unused_1734_);
v___x_1618_ = v_a_1607_;
v_isShared_1619_ = v_isSharedCheck_1732_;
goto v_resetjp_1617_;
}
else
{
lean_dec(v_a_1607_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1732_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1622_; 
v___x_1620_ = lean_string_utf8_next_fast(v_fst_1608_, v_snd_1609_);
lean_dec(v_snd_1609_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 1, v___x_1620_);
v___x_1622_ = v___x_1618_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_fst_1608_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_1624_ = l_Lean_Json_Parser_strCore(v___x_1623_, v___x_1622_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_pos_1625_; lean_object* v_res_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1721_; 
v_pos_1625_ = lean_ctor_get(v___x_1624_, 0);
v_res_1626_ = lean_ctor_get(v___x_1624_, 1);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1628_ = v___x_1624_;
v_isShared_1629_ = v_isSharedCheck_1721_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_res_1626_);
lean_inc(v_pos_1625_);
lean_dec(v___x_1624_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1721_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v_fst_1630_; lean_object* v_snd_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1720_; 
v_fst_1630_ = lean_ctor_get(v_pos_1625_, 0);
v_snd_1631_ = lean_ctor_get(v_pos_1625_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_pos_1625_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1633_ = v_pos_1625_;
v_isShared_1634_ = v_isSharedCheck_1720_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_snd_1631_);
lean_inc(v_fst_1630_);
lean_dec(v_pos_1625_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1720_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v___x_1637_; 
v___x_1635_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1630_, v_snd_1631_);
lean_inc(v___x_1635_);
lean_inc(v_fst_1630_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 1, v___x_1635_);
v___x_1637_ = v___x_1633_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_fst_1630_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
uint8_t v___x_1638_; 
v___x_1638_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_res_1626_, v_kvs_1606_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; uint8_t v_decide_1640_; 
v___x_1639_ = lean_string_utf8_byte_size(v_fst_1630_);
v_decide_1640_ = lean_nat_dec_eq(v___x_1635_, v___x_1639_);
if (v_decide_1640_ == 0)
{
uint32_t v___x_1641_; uint32_t v___x_1642_; uint8_t v___x_1643_; 
v___x_1641_ = lean_string_utf8_get_fast(v_fst_1630_, v___x_1635_);
v___x_1642_ = 58;
v___x_1643_ = lean_uint32_dec_eq(v___x_1641_, v___x_1642_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
lean_dec(v___x_1635_);
lean_dec(v_fst_1630_);
lean_dec(v_res_1626_);
lean_dec(v_kvs_1606_);
v___x_1644_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__3));
if (v_isShared_1629_ == 0)
{
lean_ctor_set_tag(v___x_1628_, 1);
lean_ctor_set(v___x_1628_, 1, v___x_1644_);
lean_ctor_set(v___x_1628_, 0, v___x_1637_);
v___x_1646_ = v___x_1628_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_dec_ref(v___x_1637_);
lean_del_object(v___x_1628_);
v___x_1648_ = lean_string_utf8_next_fast(v_fst_1630_, v___x_1635_);
lean_dec(v___x_1635_);
v___x_1649_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1630_, v___x_1648_);
v___x_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1650_, 0, v_fst_1630_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = l_Lean_Json_Parser_anyCore(v___x_1650_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_pos_1652_; lean_object* v_res_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1698_; 
v_pos_1652_ = lean_ctor_get(v___x_1651_, 0);
v_res_1653_ = lean_ctor_get(v___x_1651_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1655_ = v___x_1651_;
v_isShared_1656_ = v_isSharedCheck_1698_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_res_1653_);
lean_inc(v_pos_1652_);
lean_dec(v___x_1651_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1698_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v_fst_1657_; lean_object* v_snd_1658_; lean_object* v___x_1659_; uint8_t v_decide_1660_; 
v_fst_1657_ = lean_ctor_get(v_pos_1652_, 0);
v_snd_1658_ = lean_ctor_get(v_pos_1652_, 1);
v___x_1659_ = lean_string_utf8_byte_size(v_fst_1657_);
v_decide_1660_ = lean_nat_dec_eq(v_snd_1658_, v___x_1659_);
if (v_decide_1660_ == 0)
{
lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1691_; 
lean_inc(v_snd_1658_);
lean_inc(v_fst_1657_);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_pos_1652_);
if (v_isSharedCheck_1691_ == 0)
{
lean_object* v_unused_1692_; lean_object* v_unused_1693_; 
v_unused_1692_ = lean_ctor_get(v_pos_1652_, 1);
lean_dec(v_unused_1692_);
v_unused_1693_ = lean_ctor_get(v_pos_1652_, 0);
lean_dec(v_unused_1693_);
v___x_1662_ = v_pos_1652_;
v_isShared_1663_ = v_isSharedCheck_1691_;
goto v_resetjp_1661_;
}
else
{
lean_dec(v_pos_1652_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1691_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
uint32_t v___x_1664_; lean_object* v___x_1665_; uint32_t v___x_1666_; uint8_t v___x_1667_; 
v___x_1664_ = lean_string_utf8_get_fast(v_fst_1657_, v_snd_1658_);
v___x_1665_ = lean_string_utf8_next_fast(v_fst_1657_, v_snd_1658_);
lean_dec(v_snd_1658_);
v___x_1666_ = 125;
v___x_1667_ = lean_uint32_dec_eq(v___x_1664_, v___x_1666_);
if (v___x_1667_ == 0)
{
uint32_t v___x_1668_; uint8_t v___x_1669_; 
v___x_1668_ = 44;
v___x_1669_ = lean_uint32_dec_eq(v___x_1664_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1671_; 
lean_dec(v_res_1653_);
lean_dec(v_res_1626_);
lean_dec(v_kvs_1606_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v___x_1665_);
v___x_1671_ = v___x_1662_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_fst_1657_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v___x_1665_);
v___x_1671_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1672_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__5));
if (v_isShared_1656_ == 0)
{
lean_ctor_set_tag(v___x_1655_, 1);
lean_ctor_set(v___x_1655_, 1, v___x_1672_);
lean_ctor_set(v___x_1655_, 0, v___x_1671_);
v___x_1674_ = v___x_1655_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
lean_del_object(v___x_1655_);
v___x_1677_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1657_, v___x_1665_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v___x_1677_);
v___x_1679_ = v___x_1662_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_fst_1657_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg(v_res_1626_, v_res_1653_, v_kvs_1606_);
v_kvs_1606_ = v___x_1680_;
v_a_1607_ = v___x_1679_;
goto _start;
}
}
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1683_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1657_, v___x_1665_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v___x_1683_);
v___x_1685_ = v___x_1662_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_fst_1657_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg(v_res_1626_, v_res_1653_, v_kvs_1606_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v___x_1686_);
lean_ctor_set(v___x_1655_, 0, v___x_1685_);
v___x_1688_ = v___x_1655_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___x_1686_);
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
lean_object* v___x_1694_; lean_object* v___x_1696_; 
lean_dec(v_res_1653_);
lean_dec(v_res_1626_);
lean_dec(v_kvs_1606_);
v___x_1694_ = lean_box(0);
if (v_isShared_1656_ == 0)
{
lean_ctor_set_tag(v___x_1655_, 1);
lean_ctor_set(v___x_1655_, 1, v___x_1694_);
v___x_1696_ = v___x_1655_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_pos_1652_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v___x_1694_);
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
else
{
lean_object* v_pos_1699_; lean_object* v_err_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
lean_dec(v_res_1626_);
lean_dec(v_kvs_1606_);
v_pos_1699_ = lean_ctor_get(v___x_1651_, 0);
v_err_1700_ = lean_ctor_get(v___x_1651_, 1);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1651_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_err_1700_);
lean_inc(v_pos_1699_);
lean_dec(v___x_1651_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_pos_1699_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_err_1700_);
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
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1710_; 
lean_dec(v___x_1635_);
lean_dec(v_fst_1630_);
lean_dec(v_res_1626_);
lean_dec(v_kvs_1606_);
v___x_1708_ = lean_box(0);
if (v_isShared_1629_ == 0)
{
lean_ctor_set_tag(v___x_1628_, 1);
lean_ctor_set(v___x_1628_, 1, v___x_1708_);
lean_ctor_set(v___x_1628_, 0, v___x_1637_);
v___x_1710_ = v___x_1628_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1717_; 
lean_dec(v___x_1635_);
lean_dec(v_fst_1630_);
lean_dec(v_kvs_1606_);
v___x_1712_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__6));
v___x_1713_ = l_String_quote(v_res_1626_);
v___x_1714_ = lean_string_append(v___x_1712_, v___x_1713_);
lean_dec_ref(v___x_1713_);
v___x_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set_tag(v___x_1628_, 1);
lean_ctor_set(v___x_1628_, 1, v___x_1715_);
lean_ctor_set(v___x_1628_, 0, v___x_1637_);
v___x_1717_ = v___x_1628_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1722_; lean_object* v_err_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec(v_kvs_1606_);
v_pos_1722_ = lean_ctor_get(v___x_1624_, 0);
v_err_1723_ = lean_ctor_get(v___x_1624_, 1);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1624_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_err_1723_);
lean_inc(v_pos_1722_);
lean_dec(v___x_1624_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_pos_1722_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_err_1723_);
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
lean_object* v___x_1735_; lean_object* v___x_1736_; 
lean_dec(v_kvs_1606_);
v___x_1735_ = lean_box(0);
v___x_1736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1736_, 0, v_a_1607_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
return v___x_1736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object* v_a_1743_){
_start:
{
lean_object* v_fst_1778_; lean_object* v_snd_1779_; lean_object* v___x_1780_; uint8_t v_decide_1781_; 
v_fst_1778_ = lean_ctor_get(v_a_1743_, 0);
v_snd_1779_ = lean_ctor_get(v_a_1743_, 1);
v___x_1780_ = lean_string_utf8_byte_size(v_fst_1778_);
v_decide_1781_ = lean_nat_dec_eq(v_snd_1779_, v___x_1780_);
if (v_decide_1781_ == 0)
{
uint32_t v___x_1782_; uint32_t v___x_1783_; uint8_t v___x_1784_; 
v___x_1782_ = lean_string_utf8_get_fast(v_fst_1778_, v_snd_1779_);
v___x_1783_ = 91;
v___x_1784_ = lean_uint32_dec_eq(v___x_1782_, v___x_1783_);
if (v___x_1784_ == 0)
{
uint32_t v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = 123;
v___x_1786_ = lean_uint32_dec_eq(v___x_1782_, v___x_1785_);
if (v___x_1786_ == 0)
{
uint32_t v___x_1787_; uint8_t v___x_1788_; 
v___x_1787_ = 34;
v___x_1788_ = lean_uint32_dec_eq(v___x_1782_, v___x_1787_);
if (v___x_1788_ == 0)
{
uint32_t v___x_1789_; uint8_t v___x_1790_; 
v___x_1789_ = 102;
v___x_1790_ = lean_uint32_dec_eq(v___x_1782_, v___x_1789_);
if (v___x_1790_ == 0)
{
uint32_t v___x_1791_; uint8_t v___x_1792_; 
v___x_1791_ = 116;
v___x_1792_ = lean_uint32_dec_eq(v___x_1782_, v___x_1791_);
if (v___x_1792_ == 0)
{
uint32_t v___x_1793_; uint8_t v___x_1794_; 
v___x_1793_ = 110;
v___x_1794_ = lean_uint32_dec_eq(v___x_1782_, v___x_1793_);
if (v___x_1794_ == 0)
{
uint32_t v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = 45;
v___x_1796_ = lean_uint32_dec_eq(v___x_1782_, v___x_1795_);
if (v___x_1796_ == 0)
{
uint32_t v___x_1797_; uint8_t v___x_1798_; 
v___x_1797_ = 48;
v___x_1798_ = lean_uint32_dec_le(v___x_1797_, v___x_1782_);
if (v___x_1798_ == 0)
{
goto v___jp_1775_;
}
else
{
uint32_t v___x_1799_; uint8_t v___x_1800_; 
v___x_1799_ = 57;
v___x_1800_ = lean_uint32_dec_le(v___x_1782_, v___x_1799_);
if (v___x_1800_ == 0)
{
goto v___jp_1775_;
}
else
{
goto v___jp_1744_;
}
}
}
else
{
goto v___jp_1744_;
}
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__2));
v___x_1802_ = l_Std_Internal_Parsec_String_pstring(v___x_1801_, v_a_1743_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_pos_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1821_; 
v_pos_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1821_ == 0)
{
lean_object* v_unused_1822_; 
v_unused_1822_ = lean_ctor_get(v___x_1802_, 1);
lean_dec(v_unused_1822_);
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1821_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_pos_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1821_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v_fst_1807_; lean_object* v_snd_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1820_; 
v_fst_1807_ = lean_ctor_get(v_pos_1803_, 0);
v_snd_1808_ = lean_ctor_get(v_pos_1803_, 1);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_pos_1803_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1810_ = v_pos_1803_;
v_isShared_1811_ = v_isSharedCheck_1820_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_snd_1808_);
lean_inc(v_fst_1807_);
lean_dec(v_pos_1803_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1820_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1812_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1807_, v_snd_1808_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 1, v___x_1812_);
v___x_1814_ = v___x_1810_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_fst_1807_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = lean_box(0);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v___x_1815_);
lean_ctor_set(v___x_1805_, 0, v___x_1814_);
v___x_1817_ = v___x_1805_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1814_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
else
{
lean_object* v_pos_1823_; lean_object* v_err_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_pos_1823_ = lean_ctor_get(v___x_1802_, 0);
v_err_1824_ = lean_ctor_get(v___x_1802_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1802_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_err_1824_);
lean_inc(v_pos_1823_);
lean_dec(v___x_1802_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_pos_1823_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_err_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__3));
v___x_1833_ = l_Std_Internal_Parsec_String_pstring(v___x_1832_, v_a_1743_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_pos_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1852_; 
v_pos_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1852_ == 0)
{
lean_object* v_unused_1853_; 
v_unused_1853_ = lean_ctor_get(v___x_1833_, 1);
lean_dec(v_unused_1853_);
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1852_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_pos_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1852_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v_fst_1838_; lean_object* v_snd_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1851_; 
v_fst_1838_ = lean_ctor_get(v_pos_1834_, 0);
v_snd_1839_ = lean_ctor_get(v_pos_1834_, 1);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_pos_1834_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1841_ = v_pos_1834_;
v_isShared_1842_ = v_isSharedCheck_1851_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_snd_1839_);
lean_inc(v_fst_1838_);
lean_dec(v_pos_1834_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1851_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1843_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1838_, v_snd_1839_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 1, v___x_1843_);
v___x_1845_ = v___x_1841_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_fst_1838_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1846_, 0, v___x_1792_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 1, v___x_1846_);
lean_ctor_set(v___x_1836_, 0, v___x_1845_);
v___x_1848_ = v___x_1836_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1845_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
}
else
{
lean_object* v_pos_1854_; lean_object* v_err_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
v_pos_1854_ = lean_ctor_get(v___x_1833_, 0);
v_err_1855_ = lean_ctor_get(v___x_1833_, 1);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1833_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_err_1855_);
lean_inc(v_pos_1854_);
lean_dec(v___x_1833_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_pos_1854_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_err_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__4));
v___x_1864_ = l_Std_Internal_Parsec_String_pstring(v___x_1863_, v_a_1743_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_pos_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1883_; 
v_pos_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1883_ == 0)
{
lean_object* v_unused_1884_; 
v_unused_1884_ = lean_ctor_get(v___x_1864_, 1);
lean_dec(v_unused_1884_);
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1883_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_pos_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1883_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v_fst_1869_; lean_object* v_snd_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1882_; 
v_fst_1869_ = lean_ctor_get(v_pos_1865_, 0);
v_snd_1870_ = lean_ctor_get(v_pos_1865_, 1);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_pos_1865_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1872_ = v_pos_1865_;
v_isShared_1873_ = v_isSharedCheck_1882_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_snd_1870_);
lean_inc(v_fst_1869_);
lean_dec(v_pos_1865_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1882_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1874_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1869_, v_snd_1870_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 1, v___x_1874_);
v___x_1876_ = v___x_1872_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_fst_1869_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1877_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1877_, 0, v___x_1788_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 1, v___x_1877_);
lean_ctor_set(v___x_1867_, 0, v___x_1876_);
v___x_1879_ = v___x_1867_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1876_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
else
{
lean_object* v_pos_1885_; lean_object* v_err_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
v_pos_1885_ = lean_ctor_get(v___x_1864_, 0);
v_err_1886_ = lean_ctor_get(v___x_1864_, 1);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1864_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_err_1886_);
lean_inc(v_pos_1885_);
lean_dec(v___x_1864_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_pos_1885_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_err_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
else
{
lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1932_; 
lean_inc(v_snd_1779_);
lean_inc(v_fst_1778_);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_a_1743_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; lean_object* v_unused_1934_; 
v_unused_1933_ = lean_ctor_get(v_a_1743_, 1);
lean_dec(v_unused_1933_);
v_unused_1934_ = lean_ctor_get(v_a_1743_, 0);
lean_dec(v_unused_1934_);
v___x_1895_ = v_a_1743_;
v_isShared_1896_ = v_isSharedCheck_1932_;
goto v_resetjp_1894_;
}
else
{
lean_dec(v_a_1743_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1932_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1897_ = lean_string_utf8_next_fast(v_fst_1778_, v_snd_1779_);
lean_dec(v_snd_1779_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 1, v___x_1897_);
v___x_1899_ = v___x_1895_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_fst_1778_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_1901_ = l_Lean_Json_Parser_strCore(v___x_1900_, v___x_1899_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_pos_1902_; lean_object* v_res_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1921_; 
v_pos_1902_ = lean_ctor_get(v___x_1901_, 0);
v_res_1903_ = lean_ctor_get(v___x_1901_, 1);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1905_ = v___x_1901_;
v_isShared_1906_ = v_isSharedCheck_1921_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_res_1903_);
lean_inc(v_pos_1902_);
lean_dec(v___x_1901_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1921_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v_fst_1907_; lean_object* v_snd_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1920_; 
v_fst_1907_ = lean_ctor_get(v_pos_1902_, 0);
v_snd_1908_ = lean_ctor_get(v_pos_1902_, 1);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_pos_1902_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1910_ = v_pos_1902_;
v_isShared_1911_ = v_isSharedCheck_1920_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_snd_1908_);
lean_inc(v_fst_1907_);
lean_dec(v_pos_1902_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1920_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1912_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1907_, v_snd_1908_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 1, v___x_1912_);
v___x_1914_ = v___x_1910_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_fst_1907_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1915_; lean_object* v___x_1917_; 
v___x_1915_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1915_, 0, v_res_1903_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 1, v___x_1915_);
lean_ctor_set(v___x_1905_, 0, v___x_1914_);
v___x_1917_ = v___x_1905_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1914_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
else
{
lean_object* v_pos_1922_; lean_object* v_err_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
v_pos_1922_ = lean_ctor_get(v___x_1901_, 0);
v_err_1923_ = lean_ctor_get(v___x_1901_, 1);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1901_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_err_1923_);
lean_inc(v_pos_1922_);
lean_dec(v___x_1901_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_pos_1922_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_err_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1975_; 
lean_inc(v_snd_1779_);
lean_inc(v_fst_1778_);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_a_1743_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; lean_object* v_unused_1977_; 
v_unused_1976_ = lean_ctor_get(v_a_1743_, 1);
lean_dec(v_unused_1976_);
v_unused_1977_ = lean_ctor_get(v_a_1743_, 0);
lean_dec(v_unused_1977_);
v___x_1936_ = v_a_1743_;
v_isShared_1937_ = v_isSharedCheck_1975_;
goto v_resetjp_1935_;
}
else
{
lean_dec(v_a_1743_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1975_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1938_ = lean_string_utf8_next_fast(v_fst_1778_, v_snd_1779_);
lean_dec(v_snd_1779_);
v___x_1939_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1778_, v___x_1938_);
lean_inc(v___x_1939_);
lean_inc(v_fst_1778_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 1, v___x_1939_);
v___x_1941_ = v___x_1936_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_fst_1778_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
uint8_t v_decide_1942_; 
v_decide_1942_ = lean_nat_dec_eq(v___x_1939_, v___x_1780_);
if (v_decide_1942_ == 0)
{
uint32_t v___x_1943_; uint32_t v___x_1944_; uint8_t v___x_1945_; 
v___x_1943_ = lean_string_utf8_get_fast(v_fst_1778_, v___x_1939_);
v___x_1944_ = 125;
v___x_1945_ = lean_uint32_dec_eq(v___x_1943_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
lean_dec(v___x_1939_);
lean_dec(v_fst_1778_);
v___x_1946_ = lean_box(1);
v___x_1947_ = l_Lean_Json_Parser_objectCore(v___x_1946_, v___x_1941_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_pos_1948_; lean_object* v_res_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1957_; 
v_pos_1948_ = lean_ctor_get(v___x_1947_, 0);
v_res_1949_ = lean_ctor_get(v___x_1947_, 1);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1951_ = v___x_1947_;
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_res_1949_);
lean_inc(v_pos_1948_);
lean_dec(v___x_1947_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1953_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1953_, 0, v_res_1949_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 1, v___x_1953_);
v___x_1955_ = v___x_1951_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_pos_1948_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
else
{
lean_object* v_pos_1958_; lean_object* v_err_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
v_pos_1958_ = lean_ctor_get(v___x_1947_, 0);
v_err_1959_ = lean_ctor_get(v___x_1947_, 1);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1947_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_err_1959_);
lean_inc(v_pos_1958_);
lean_dec(v___x_1947_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_pos_1958_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v_err_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec_ref(v___x_1941_);
v___x_1967_ = lean_string_utf8_next_fast(v_fst_1778_, v___x_1939_);
lean_dec(v___x_1939_);
v___x_1968_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1778_, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1969_, 0, v_fst_1778_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__5));
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1969_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
return v___x_1971_;
}
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_dec(v___x_1939_);
lean_dec(v_fst_1778_);
v___x_1972_ = lean_box(0);
v___x_1973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1941_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
return v___x_1973_;
}
}
}
}
}
else
{
lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2019_; 
lean_inc(v_snd_1779_);
lean_inc(v_fst_1778_);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_a_1743_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; lean_object* v_unused_2021_; 
v_unused_2020_ = lean_ctor_get(v_a_1743_, 1);
lean_dec(v_unused_2020_);
v_unused_2021_ = lean_ctor_get(v_a_1743_, 0);
lean_dec(v_unused_2021_);
v___x_1979_ = v_a_1743_;
v_isShared_1980_ = v_isSharedCheck_2019_;
goto v_resetjp_1978_;
}
else
{
lean_dec(v_a_1743_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2019_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1981_ = lean_string_utf8_next_fast(v_fst_1778_, v_snd_1779_);
lean_dec(v_snd_1779_);
v___x_1982_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1778_, v___x_1981_);
lean_inc(v___x_1982_);
lean_inc(v_fst_1778_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 1, v___x_1982_);
v___x_1984_ = v___x_1979_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_fst_1778_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_2018_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
uint8_t v_decide_1985_; 
v_decide_1985_ = lean_nat_dec_eq(v___x_1982_, v___x_1780_);
if (v_decide_1985_ == 0)
{
uint32_t v___x_1986_; uint32_t v___x_1987_; uint8_t v___x_1988_; 
v___x_1986_ = lean_string_utf8_get_fast(v_fst_1778_, v___x_1982_);
v___x_1987_ = 93;
v___x_1988_ = lean_uint32_dec_eq(v___x_1986_, v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_dec(v___x_1982_);
lean_dec(v_fst_1778_);
v___x_1989_ = lean_unsigned_to_nat(4u);
v___x_1990_ = lean_mk_empty_array_with_capacity(v___x_1989_);
v___x_1991_ = l_Lean_Json_Parser_arrayCore(v___x_1990_, v___x_1984_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_pos_1992_; lean_object* v_res_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2001_; 
v_pos_1992_ = lean_ctor_get(v___x_1991_, 0);
v_res_1993_ = lean_ctor_get(v___x_1991_, 1);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1995_ = v___x_1991_;
v_isShared_1996_ = v_isSharedCheck_2001_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_res_1993_);
lean_inc(v_pos_1992_);
lean_dec(v___x_1991_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2001_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1997_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1997_, 0, v_res_1993_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 1, v___x_1997_);
v___x_1999_ = v___x_1995_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_pos_1992_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
else
{
lean_object* v_pos_2002_; lean_object* v_err_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
v_pos_2002_ = lean_ctor_get(v___x_1991_, 0);
v_err_2003_ = lean_ctor_get(v___x_1991_, 1);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1991_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_err_2003_);
lean_inc(v_pos_2002_);
lean_dec(v___x_1991_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_pos_2002_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_err_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
else
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_dec_ref(v___x_1984_);
v___x_2011_ = lean_string_utf8_next_fast(v_fst_1778_, v___x_1982_);
lean_dec(v___x_1982_);
v___x_2012_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1778_, v___x_2011_);
v___x_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2013_, 0, v_fst_1778_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__7));
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2013_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
return v___x_2015_;
}
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
lean_dec(v___x_1982_);
lean_dec(v_fst_1778_);
v___x_2016_ = lean_box(0);
v___x_2017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_1984_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
return v___x_2017_;
}
}
}
}
}
else
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = lean_box(0);
v___x_2023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2023_, 0, v_a_1743_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
return v___x_2023_;
}
v___jp_1744_:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_Json_Parser_num(v_a_1743_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_pos_1746_; lean_object* v_res_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1765_; 
v_pos_1746_ = lean_ctor_get(v___x_1745_, 0);
v_res_1747_ = lean_ctor_get(v___x_1745_, 1);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1749_ = v___x_1745_;
v_isShared_1750_ = v_isSharedCheck_1765_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_res_1747_);
lean_inc(v_pos_1746_);
lean_dec(v___x_1745_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1765_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v_fst_1751_; lean_object* v_snd_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1764_; 
v_fst_1751_ = lean_ctor_get(v_pos_1746_, 0);
v_snd_1752_ = lean_ctor_get(v_pos_1746_, 1);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_pos_1746_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1754_ = v_pos_1746_;
v_isShared_1755_ = v_isSharedCheck_1764_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_snd_1752_);
lean_inc(v_fst_1751_);
lean_dec(v_pos_1746_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1764_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1756_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1751_, v_snd_1752_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 1, v___x_1756_);
v___x_1758_ = v___x_1754_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_fst_1751_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1759_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1759_, 0, v_res_1747_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 1, v___x_1759_);
lean_ctor_set(v___x_1749_, 0, v___x_1758_);
v___x_1761_ = v___x_1749_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v___x_1759_);
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
else
{
lean_object* v_pos_1766_; lean_object* v_err_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
v_pos_1766_ = lean_ctor_get(v___x_1745_, 0);
v_err_1767_ = lean_ctor_get(v___x_1745_, 1);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1745_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_err_1767_);
lean_inc(v_pos_1766_);
lean_dec(v___x_1745_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_pos_1766_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v_err_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
v___jp_1775_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__1));
v___x_1777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1777_, 0, v_a_1743_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore(lean_object* v_acc_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_Json_Parser_anyCore(v_a_2025_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_pos_2027_; lean_object* v_res_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2072_; 
v_pos_2027_ = lean_ctor_get(v___x_2026_, 0);
v_res_2028_ = lean_ctor_get(v___x_2026_, 1);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2030_ = v___x_2026_;
v_isShared_2031_ = v_isSharedCheck_2072_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_res_2028_);
lean_inc(v_pos_2027_);
lean_dec(v___x_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2072_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v_fst_2032_; lean_object* v_snd_2033_; lean_object* v___x_2034_; uint8_t v_decide_2035_; 
v_fst_2032_ = lean_ctor_get(v_pos_2027_, 0);
v_snd_2033_ = lean_ctor_get(v_pos_2027_, 1);
v___x_2034_ = lean_string_utf8_byte_size(v_fst_2032_);
v_decide_2035_ = lean_nat_dec_eq(v_snd_2033_, v___x_2034_);
if (v_decide_2035_ == 0)
{
lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2065_; 
lean_inc(v_snd_2033_);
lean_inc(v_fst_2032_);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_pos_2027_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; lean_object* v_unused_2067_; 
v_unused_2066_ = lean_ctor_get(v_pos_2027_, 1);
lean_dec(v_unused_2066_);
v_unused_2067_ = lean_ctor_get(v_pos_2027_, 0);
lean_dec(v_unused_2067_);
v___x_2037_ = v_pos_2027_;
v_isShared_2038_ = v_isSharedCheck_2065_;
goto v_resetjp_2036_;
}
else
{
lean_dec(v_pos_2027_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2065_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; uint32_t v___x_2040_; lean_object* v___x_2041_; uint32_t v___x_2042_; uint8_t v___x_2043_; 
v___x_2039_ = lean_array_push(v_acc_2024_, v_res_2028_);
v___x_2040_ = lean_string_utf8_get_fast(v_fst_2032_, v_snd_2033_);
v___x_2041_ = lean_string_utf8_next_fast(v_fst_2032_, v_snd_2033_);
lean_dec(v_snd_2033_);
v___x_2042_ = 93;
v___x_2043_ = lean_uint32_dec_eq(v___x_2040_, v___x_2042_);
if (v___x_2043_ == 0)
{
uint32_t v___x_2044_; uint8_t v___x_2045_; 
v___x_2044_ = 44;
v___x_2045_ = lean_uint32_dec_eq(v___x_2040_, v___x_2044_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2047_; 
lean_dec_ref(v___x_2039_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 1, v___x_2041_);
v___x_2047_ = v___x_2037_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_fst_2032_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v___x_2041_);
v___x_2047_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2048_ = ((lean_object*)(l_Lean_Json_Parser_arrayCore___closed__1));
if (v_isShared_2031_ == 0)
{
lean_ctor_set_tag(v___x_2030_, 1);
lean_ctor_set(v___x_2030_, 1, v___x_2048_);
lean_ctor_set(v___x_2030_, 0, v___x_2047_);
v___x_2050_ = v___x_2030_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2055_; 
lean_del_object(v___x_2030_);
v___x_2053_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2032_, v___x_2041_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 1, v___x_2053_);
v___x_2055_ = v___x_2037_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_fst_2032_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
v_acc_2024_ = v___x_2039_;
v_a_2025_ = v___x_2055_;
goto _start;
}
}
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2058_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2032_, v___x_2041_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 1, v___x_2058_);
v___x_2060_ = v___x_2037_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_fst_2032_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2062_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v___x_2039_);
lean_ctor_set(v___x_2030_, 0, v___x_2060_);
v___x_2062_ = v___x_2030_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v___x_2039_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
lean_dec(v_res_2028_);
lean_dec_ref(v_acc_2024_);
v___x_2068_ = lean_box(0);
if (v_isShared_2031_ == 0)
{
lean_ctor_set_tag(v___x_2030_, 1);
lean_ctor_set(v___x_2030_, 1, v___x_2068_);
v___x_2070_ = v___x_2030_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_pos_2027_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
else
{
lean_object* v_pos_2073_; lean_object* v_err_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec_ref(v_acc_2024_);
v_pos_2073_ = lean_ctor_get(v___x_2026_, 0);
v_err_2074_ = lean_ctor_get(v___x_2026_, 1);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2026_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_err_2074_);
lean_inc(v_pos_2073_);
lean_dec(v___x_2026_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_pos_2073_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_err_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2(lean_object* v_00_u03b2_2082_, lean_object* v_k_2083_, lean_object* v_t_2084_){
_start:
{
uint8_t v___x_2085_; 
v___x_2085_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_2083_, v_t_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2___boxed(lean_object* v_00_u03b2_2086_, lean_object* v_k_2087_, lean_object* v_t_2088_){
_start:
{
uint8_t v_res_2089_; lean_object* v_r_2090_; 
v_res_2089_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2(v_00_u03b2_2086_, v_k_2087_, v_t_2088_);
lean_dec(v_t_2088_);
lean_dec_ref(v_k_2087_);
v_r_2090_ = lean_box(v_res_2089_);
return v_r_2090_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3_spec__3(lean_object* v_00_u03b2_2091_, lean_object* v_msg_2092_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3_spec__3___redArg(v_msg_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3(lean_object* v_00_u03b2_2094_, lean_object* v_k_2095_, lean_object* v_v_2096_, lean_object* v_t_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg(v_k_2095_, v_v_2096_, v_t_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_any(lean_object* v_a_2102_){
_start:
{
lean_object* v_fst_2103_; lean_object* v_snd_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2128_; 
v_fst_2103_ = lean_ctor_get(v_a_2102_, 0);
v_snd_2104_ = lean_ctor_get(v_a_2102_, 1);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_a_2102_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2106_ = v_a_2102_;
v_isShared_2107_ = v_isSharedCheck_2128_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_snd_2104_);
lean_inc(v_fst_2103_);
lean_dec(v_a_2102_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2128_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2108_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2103_, v_snd_2104_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 1, v___x_2108_);
v___x_2110_ = v___x_2106_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_fst_2103_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_Json_Parser_anyCore(v___x_2110_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_pos_2112_; lean_object* v_fst_2113_; lean_object* v_snd_2114_; lean_object* v___x_2115_; uint8_t v_decide_2116_; 
v_pos_2112_ = lean_ctor_get(v___x_2111_, 0);
v_fst_2113_ = lean_ctor_get(v_pos_2112_, 0);
v_snd_2114_ = lean_ctor_get(v_pos_2112_, 1);
v___x_2115_ = lean_string_utf8_byte_size(v_fst_2113_);
v_decide_2116_ = lean_nat_dec_eq(v_snd_2114_, v___x_2115_);
if (v_decide_2116_ == 0)
{
lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2124_; 
lean_inc(v_pos_2112_);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2124_ == 0)
{
lean_object* v_unused_2125_; lean_object* v_unused_2126_; 
v_unused_2125_ = lean_ctor_get(v___x_2111_, 1);
lean_dec(v_unused_2125_);
v_unused_2126_ = lean_ctor_get(v___x_2111_, 0);
lean_dec(v_unused_2126_);
v___x_2118_ = v___x_2111_;
v_isShared_2119_ = v_isSharedCheck_2124_;
goto v_resetjp_2117_;
}
else
{
lean_dec(v___x_2111_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2124_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = ((lean_object*)(l_Lean_Json_Parser_any___closed__1));
if (v_isShared_2119_ == 0)
{
lean_ctor_set_tag(v___x_2118_, 1);
lean_ctor_set(v___x_2118_, 1, v___x_2120_);
v___x_2122_ = v___x_2118_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_pos_2112_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
else
{
return v___x_2111_;
}
}
else
{
return v___x_2111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parse(lean_object* v_s_2129_){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
v___x_2131_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_2130_, v_s_2129_);
return v___x_2131_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Json_Parser(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Json_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Json_Parser_escapedChar___boxed__const__1 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__1();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__1);
l_Lean_Json_Parser_escapedChar___boxed__const__2 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__2();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__2);
l_Lean_Json_Parser_escapedChar___boxed__const__3 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__3();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__3);
l_Lean_Json_Parser_escapedChar___boxed__const__4 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__4();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__4);
l_Lean_Json_Parser_escapedChar___boxed__const__5 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__5();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__5);
l_Lean_Json_Parser_escapedChar___boxed__const__6 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__6();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__6);
l_Lean_Json_Parser_escapedChar___boxed__const__7 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__7();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__7);
l_Lean_Json_Parser_escapedChar___boxed__const__8 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__8();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__8);
l_Lean_Json_Parser_escapedChar___boxed__const__9 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__9();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__9);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Json_Parser(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Parsec(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Json_Parser(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Json_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Json_Parser(builtin);
}
#ifdef __cplusplus
}
#endif
