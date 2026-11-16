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
lean_object* l_Lean_JsonNumber_shiftl(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Json_Parser_maxDepth;
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
static const lean_ctor_object l_Lean_Json_Parser_anyCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__4 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__4_value;
static const lean_string_object l_Lean_Json_Parser_anyCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__5 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__5_value;
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
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Json_Parser_anyCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__6 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__6_value;
static const lean_array_object l_Lean_Json_Parser_anyCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__7 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__7_value;
static const lean_ctor_object l_Lean_Json_Parser_anyCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_anyCore___closed__7_value)}};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__8 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__8_value;
static const lean_string_object l_Lean_Json_Parser_anyCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "nesting deeper than 10000 levels"};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__9 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__9_value;
static const lean_ctor_object l_Lean_Json_Parser_anyCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_anyCore___closed__9_value)}};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__10 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore___boxed(lean_object*, lean_object*);
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
lean_object* v___y_925_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v_fst_931_; lean_object* v_snd_932_; lean_object* v___y_970_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v_fst_976_; lean_object* v_snd_977_; lean_object* v___y_1026_; lean_object* v_pos_1027_; lean_object* v_fst_1028_; lean_object* v_snd_1029_; lean_object* v_res_1030_; lean_object* v___y_1039_; lean_object* v___y_1043_; lean_object* v_pos_1044_; lean_object* v_fst_1045_; lean_object* v_snd_1046_; lean_object* v_res_1047_; lean_object* v___y_1117_; lean_object* v_pos_1121_; lean_object* v_fst_1122_; lean_object* v_snd_1123_; lean_object* v_res_1124_; lean_object* v_fst_1154_; lean_object* v_snd_1155_; lean_object* v___x_1156_; uint8_t v_decide_1157_; 
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
v___x_978_ = lean_string_utf8_byte_size(v_fst_976_);
v_decide_979_ = lean_nat_dec_eq(v_snd_977_, v___x_978_);
if (v_decide_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v_decide_982_; 
lean_dec_ref(v___y_975_);
v___x_980_ = lean_string_utf8_next_fast(v_fst_976_, v_snd_977_);
lean_dec(v_snd_977_);
lean_inc(v_fst_976_);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v_fst_976_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v_decide_982_ = lean_nat_dec_eq(v___x_980_, v___x_978_);
if (v_decide_982_ == 0)
{
uint32_t v___x_983_; uint32_t v___x_984_; uint8_t v___x_985_; 
v___x_983_ = lean_string_utf8_get_fast(v_fst_976_, v___x_980_);
v___x_984_ = 45;
v___x_985_ = lean_uint32_dec_eq(v___x_983_, v___x_984_);
if (v___x_985_ == 0)
{
uint32_t v___x_986_; uint8_t v___x_987_; 
v___x_986_ = 43;
v___x_987_ = lean_uint32_dec_eq(v___x_983_, v___x_986_);
if (v___x_987_ == 0)
{
v___y_929_ = v___y_974_;
v___y_930_ = v___x_981_;
v_fst_931_ = v_fst_976_;
v_snd_932_ = v___x_980_;
goto v___jp_928_;
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec_ref_known(v___x_981_, 2);
v___x_988_ = lean_string_utf8_next_fast(v_fst_976_, v___x_980_);
lean_inc(v_fst_976_);
v___x_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_989_, 0, v_fst_976_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___y_929_ = v___y_974_;
v___y_930_ = v___x_989_;
v_fst_931_ = v_fst_976_;
v_snd_932_ = v___x_988_;
goto v___jp_928_;
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v_decide_992_; 
lean_dec_ref_known(v___x_981_, 2);
v___x_990_ = lean_string_utf8_next_fast(v_fst_976_, v___x_980_);
lean_inc(v_fst_976_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_fst_976_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v_decide_992_ = lean_nat_dec_eq(v___x_990_, v___x_978_);
if (v_decide_992_ == 0)
{
uint32_t v___x_993_; uint32_t v___x_994_; uint8_t v___x_995_; 
v___x_993_ = lean_string_utf8_get_fast(v_fst_976_, v___x_990_);
lean_dec(v_fst_976_);
v___x_994_ = 48;
v___x_995_ = lean_uint32_dec_le(v___x_994_, v___x_993_);
if (v___x_995_ == 0)
{
lean_dec_ref(v___y_974_);
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
lean_dec_ref(v___y_974_);
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
v___x_1005_ = l_Lean_JsonNumber_shiftr(v___y_974_, v_res_1001_);
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
lean_dec_ref(v___y_974_);
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
lean_dec(v_fst_976_);
lean_dec_ref(v___y_974_);
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
lean_dec(v_fst_976_);
lean_dec_ref(v___y_974_);
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
lean_dec(v_snd_977_);
lean_dec(v_fst_976_);
lean_dec_ref(v___y_974_);
v___x_1023_ = lean_box(0);
v___x_1024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___y_975_);
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
v___y_974_ = v_res_1030_;
v___y_975_ = v_pos_1027_;
v_fst_976_ = v_fst_1028_;
v_snd_977_ = v_snd_1029_;
goto v___jp_973_;
}
}
else
{
lean_dec_ref(v___y_1026_);
v___y_974_ = v_res_1030_;
v___y_975_ = v_pos_1027_;
v_fst_976_ = v_fst_1028_;
v_snd_977_ = v_snd_1029_;
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
static lean_object* _init_l_Lean_Json_Parser_maxDepth(void){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_unsigned_to_nat(10000u);
return v___x_1175_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2___redArg(lean_object* v_k_1176_, lean_object* v_t_1177_){
_start:
{
if (lean_obj_tag(v_t_1177_) == 0)
{
lean_object* v_k_1178_; lean_object* v_l_1179_; lean_object* v_r_1180_; uint8_t v___x_1181_; 
v_k_1178_ = lean_ctor_get(v_t_1177_, 1);
v_l_1179_ = lean_ctor_get(v_t_1177_, 3);
v_r_1180_ = lean_ctor_get(v_t_1177_, 4);
v___x_1181_ = lean_string_compare(v_k_1176_, v_k_1178_);
switch(v___x_1181_)
{
case 0:
{
v_t_1177_ = v_l_1179_;
goto _start;
}
case 1:
{
uint8_t v___x_1183_; 
v___x_1183_ = 1;
return v___x_1183_;
}
default: 
{
v_t_1177_ = v_r_1180_;
goto _start;
}
}
}
else
{
uint8_t v___x_1185_; 
v___x_1185_ = 0;
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2___redArg___boxed(lean_object* v_k_1186_, lean_object* v_t_1187_){
_start:
{
uint8_t v_res_1188_; lean_object* v_r_1189_; 
v_res_1188_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_1186_, v_t_1187_);
lean_dec(v_t_1187_);
lean_dec_ref(v_k_1186_);
v_r_1189_ = lean_box(v_res_1188_);
return v_r_1189_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3_spec__3___redArg(lean_object* v_msg_1190_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_box(1);
v___x_1192_ = lean_panic_fn_borrowed(v___x_1191_, v_msg_1190_);
return v___x_1192_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1196_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__2));
v___x_1197_ = lean_unsigned_to_nat(35u);
v___x_1198_ = lean_unsigned_to_nat(182u);
v___x_1199_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__1));
v___x_1200_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__0));
v___x_1201_ = l_mkPanicMessageWithDecl(v___x_1200_, v___x_1199_, v___x_1198_, v___x_1197_, v___x_1196_);
return v___x_1201_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1202_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__2));
v___x_1203_ = lean_unsigned_to_nat(21u);
v___x_1204_ = lean_unsigned_to_nat(183u);
v___x_1205_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__1));
v___x_1206_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__0));
v___x_1207_ = l_mkPanicMessageWithDecl(v___x_1206_, v___x_1205_, v___x_1204_, v___x_1203_, v___x_1202_);
return v___x_1207_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1210_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__6));
v___x_1211_ = lean_unsigned_to_nat(35u);
v___x_1212_ = lean_unsigned_to_nat(276u);
v___x_1213_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__5));
v___x_1214_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__0));
v___x_1215_ = l_mkPanicMessageWithDecl(v___x_1214_, v___x_1213_, v___x_1212_, v___x_1211_, v___x_1210_);
return v___x_1215_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1216_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__6));
v___x_1217_ = lean_unsigned_to_nat(21u);
v___x_1218_ = lean_unsigned_to_nat(277u);
v___x_1219_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__5));
v___x_1220_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__0));
v___x_1221_ = l_mkPanicMessageWithDecl(v___x_1220_, v___x_1219_, v___x_1218_, v___x_1217_, v___x_1216_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg(lean_object* v_k_1222_, lean_object* v_v_1223_, lean_object* v_t_1224_){
_start:
{
if (lean_obj_tag(v_t_1224_) == 0)
{
lean_object* v_size_1225_; lean_object* v_k_1226_; lean_object* v_v_1227_; lean_object* v_l_1228_; lean_object* v_r_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1585_; 
v_size_1225_ = lean_ctor_get(v_t_1224_, 0);
v_k_1226_ = lean_ctor_get(v_t_1224_, 1);
v_v_1227_ = lean_ctor_get(v_t_1224_, 2);
v_l_1228_ = lean_ctor_get(v_t_1224_, 3);
v_r_1229_ = lean_ctor_get(v_t_1224_, 4);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_t_1224_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1231_ = v_t_1224_;
v_isShared_1232_ = v_isSharedCheck_1585_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_r_1229_);
lean_inc(v_l_1228_);
lean_inc(v_v_1227_);
lean_inc(v_k_1226_);
lean_inc(v_size_1225_);
lean_dec(v_t_1224_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1585_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
uint8_t v___x_1233_; 
v___x_1233_ = lean_string_compare(v_k_1222_, v_k_1226_);
switch(v___x_1233_)
{
case 0:
{
lean_object* v___x_1234_; 
lean_dec(v_size_1225_);
v___x_1234_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg(v_k_1222_, v_v_1223_, v_l_1228_);
if (lean_obj_tag(v_r_1229_) == 0)
{
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_size_1235_; lean_object* v_size_1236_; lean_object* v_k_1237_; lean_object* v_v_1238_; lean_object* v_l_1239_; lean_object* v_r_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_size_1235_ = lean_ctor_get(v_r_1229_, 0);
v_size_1236_ = lean_ctor_get(v___x_1234_, 0);
v_k_1237_ = lean_ctor_get(v___x_1234_, 1);
v_v_1238_ = lean_ctor_get(v___x_1234_, 2);
v_l_1239_ = lean_ctor_get(v___x_1234_, 3);
v_r_1240_ = lean_ctor_get(v___x_1234_, 4);
lean_inc(v_r_1240_);
v___x_1241_ = lean_unsigned_to_nat(3u);
v___x_1242_ = lean_nat_mul(v___x_1241_, v_size_1235_);
v___x_1243_ = lean_nat_dec_lt(v___x_1242_, v_size_1236_);
lean_dec(v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1248_; 
lean_dec(v_r_1240_);
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_add(v___x_1244_, v_size_1236_);
v___x_1246_ = lean_nat_add(v___x_1245_, v_size_1235_);
lean_dec(v___x_1245_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 3, v___x_1234_);
lean_ctor_set(v___x_1231_, 0, v___x_1246_);
v___x_1248_ = v___x_1231_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1249_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1249_, 3, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1249_, 4, v_r_1229_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
else
{
lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1321_; 
lean_inc(v_l_1239_);
lean_inc(v_v_1238_);
lean_inc(v_k_1237_);
lean_inc(v_size_1236_);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; lean_object* v_unused_1323_; lean_object* v_unused_1324_; lean_object* v_unused_1325_; lean_object* v_unused_1326_; 
v_unused_1322_ = lean_ctor_get(v___x_1234_, 4);
lean_dec(v_unused_1322_);
v_unused_1323_ = lean_ctor_get(v___x_1234_, 3);
lean_dec(v_unused_1323_);
v_unused_1324_ = lean_ctor_get(v___x_1234_, 2);
lean_dec(v_unused_1324_);
v_unused_1325_ = lean_ctor_get(v___x_1234_, 1);
lean_dec(v_unused_1325_);
v_unused_1326_ = lean_ctor_get(v___x_1234_, 0);
lean_dec(v_unused_1326_);
v___x_1251_ = v___x_1234_;
v_isShared_1252_ = v_isSharedCheck_1321_;
goto v_resetjp_1250_;
}
else
{
lean_dec(v___x_1234_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1321_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
if (lean_obj_tag(v_l_1239_) == 0)
{
if (lean_obj_tag(v_r_1240_) == 0)
{
lean_object* v_size_1253_; lean_object* v_size_1254_; lean_object* v_k_1255_; lean_object* v_v_1256_; lean_object* v_l_1257_; lean_object* v_r_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v_size_1253_ = lean_ctor_get(v_l_1239_, 0);
v_size_1254_ = lean_ctor_get(v_r_1240_, 0);
v_k_1255_ = lean_ctor_get(v_r_1240_, 1);
v_v_1256_ = lean_ctor_get(v_r_1240_, 2);
v_l_1257_ = lean_ctor_get(v_r_1240_, 3);
v_r_1258_ = lean_ctor_get(v_r_1240_, 4);
v___x_1259_ = lean_unsigned_to_nat(2u);
v___x_1260_ = lean_nat_mul(v___x_1259_, v_size_1253_);
v___x_1261_ = lean_nat_dec_lt(v_size_1254_, v___x_1260_);
lean_dec(v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1291_; 
lean_inc(v_r_1258_);
lean_inc(v_l_1257_);
lean_inc(v_v_1256_);
lean_inc(v_k_1255_);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_r_1240_);
if (v_isSharedCheck_1291_ == 0)
{
lean_object* v_unused_1292_; lean_object* v_unused_1293_; lean_object* v_unused_1294_; lean_object* v_unused_1295_; lean_object* v_unused_1296_; 
v_unused_1292_ = lean_ctor_get(v_r_1240_, 4);
lean_dec(v_unused_1292_);
v_unused_1293_ = lean_ctor_get(v_r_1240_, 3);
lean_dec(v_unused_1293_);
v_unused_1294_ = lean_ctor_get(v_r_1240_, 2);
lean_dec(v_unused_1294_);
v_unused_1295_ = lean_ctor_get(v_r_1240_, 1);
lean_dec(v_unused_1295_);
v_unused_1296_ = lean_ctor_get(v_r_1240_, 0);
lean_dec(v_unused_1296_);
v___x_1263_ = v_r_1240_;
v_isShared_1264_ = v_isSharedCheck_1291_;
goto v_resetjp_1262_;
}
else
{
lean_dec(v_r_1240_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1291_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___x_1279_; lean_object* v___y_1281_; 
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_nat_add(v___x_1265_, v_size_1236_);
lean_dec(v_size_1236_);
v___x_1267_ = lean_nat_add(v___x_1266_, v_size_1235_);
lean_dec(v___x_1266_);
v___x_1279_ = lean_nat_add(v___x_1265_, v_size_1253_);
if (lean_obj_tag(v_l_1257_) == 0)
{
lean_object* v_size_1289_; 
v_size_1289_ = lean_ctor_get(v_l_1257_, 0);
lean_inc(v_size_1289_);
v___y_1281_ = v_size_1289_;
goto v___jp_1280_;
}
else
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_unsigned_to_nat(0u);
v___y_1281_ = v___x_1290_;
goto v___jp_1280_;
}
v___jp_1268_:
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1272_ = lean_nat_add(v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec(v___y_1270_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 4, v_r_1229_);
lean_ctor_set(v___x_1263_, 3, v_r_1258_);
lean_ctor_set(v___x_1263_, 2, v_v_1227_);
lean_ctor_set(v___x_1263_, 1, v_k_1226_);
lean_ctor_set(v___x_1263_, 0, v___x_1272_);
v___x_1274_ = v___x_1263_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_r_1258_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v_r_1229_);
v___x_1274_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1276_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 4, v___x_1274_);
lean_ctor_set(v___x_1251_, 3, v___y_1269_);
lean_ctor_set(v___x_1251_, 2, v_v_1256_);
lean_ctor_set(v___x_1251_, 1, v_k_1255_);
lean_ctor_set(v___x_1251_, 0, v___x_1267_);
v___x_1276_ = v___x_1251_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1267_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_k_1255_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_v_1256_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v___y_1269_);
lean_ctor_set(v_reuseFailAlloc_1277_, 4, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
v___jp_1280_:
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1282_ = lean_nat_add(v___x_1279_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec(v___x_1279_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v_l_1257_);
lean_ctor_set(v___x_1231_, 3, v_l_1239_);
lean_ctor_set(v___x_1231_, 2, v_v_1238_);
lean_ctor_set(v___x_1231_, 1, v_k_1237_);
lean_ctor_set(v___x_1231_, 0, v___x_1282_);
v___x_1284_ = v___x_1231_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_k_1237_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v_v_1238_);
lean_ctor_set(v_reuseFailAlloc_1288_, 3, v_l_1239_);
lean_ctor_set(v_reuseFailAlloc_1288_, 4, v_l_1257_);
v___x_1284_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_nat_add(v___x_1265_, v_size_1235_);
if (lean_obj_tag(v_r_1258_) == 0)
{
lean_object* v_size_1286_; 
v_size_1286_ = lean_ctor_get(v_r_1258_, 0);
lean_inc(v_size_1286_);
v___y_1269_ = v___x_1284_;
v___y_1270_ = v___x_1285_;
v___y_1271_ = v_size_1286_;
goto v___jp_1268_;
}
else
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_unsigned_to_nat(0u);
v___y_1269_ = v___x_1284_;
v___y_1270_ = v___x_1285_;
v___y_1271_ = v___x_1287_;
goto v___jp_1268_;
}
}
}
}
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
lean_del_object(v___x_1231_);
v___x_1297_ = lean_unsigned_to_nat(1u);
v___x_1298_ = lean_nat_add(v___x_1297_, v_size_1236_);
lean_dec(v_size_1236_);
v___x_1299_ = lean_nat_add(v___x_1298_, v_size_1235_);
lean_dec(v___x_1298_);
v___x_1300_ = lean_nat_add(v___x_1297_, v_size_1235_);
v___x_1301_ = lean_nat_add(v___x_1300_, v_size_1254_);
lean_dec(v___x_1300_);
lean_inc_ref(v_r_1229_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 4, v_r_1229_);
lean_ctor_set(v___x_1251_, 3, v_r_1240_);
lean_ctor_set(v___x_1251_, 2, v_v_1227_);
lean_ctor_set(v___x_1251_, 1, v_k_1226_);
lean_ctor_set(v___x_1251_, 0, v___x_1301_);
v___x_1303_ = v___x_1251_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1316_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1316_, 3, v_r_1240_);
lean_ctor_set(v_reuseFailAlloc_1316_, 4, v_r_1229_);
v___x_1303_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
v_isSharedCheck_1310_ = !lean_is_exclusive(v_r_1229_);
if (v_isSharedCheck_1310_ == 0)
{
lean_object* v_unused_1311_; lean_object* v_unused_1312_; lean_object* v_unused_1313_; lean_object* v_unused_1314_; lean_object* v_unused_1315_; 
v_unused_1311_ = lean_ctor_get(v_r_1229_, 4);
lean_dec(v_unused_1311_);
v_unused_1312_ = lean_ctor_get(v_r_1229_, 3);
lean_dec(v_unused_1312_);
v_unused_1313_ = lean_ctor_get(v_r_1229_, 2);
lean_dec(v_unused_1313_);
v_unused_1314_ = lean_ctor_get(v_r_1229_, 1);
lean_dec(v_unused_1314_);
v_unused_1315_ = lean_ctor_get(v_r_1229_, 0);
lean_dec(v_unused_1315_);
v___x_1305_ = v_r_1229_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_dec(v_r_1229_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 4, v___x_1303_);
lean_ctor_set(v___x_1305_, 3, v_l_1239_);
lean_ctor_set(v___x_1305_, 2, v_v_1238_);
lean_ctor_set(v___x_1305_, 1, v_k_1237_);
lean_ctor_set(v___x_1305_, 0, v___x_1299_);
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_k_1237_);
lean_ctor_set(v_reuseFailAlloc_1309_, 2, v_v_1238_);
lean_ctor_set(v_reuseFailAlloc_1309_, 3, v_l_1239_);
lean_ctor_set(v_reuseFailAlloc_1309_, 4, v___x_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_dec_ref_known(v_l_1239_, 5);
lean_del_object(v___x_1251_);
lean_dec(v_v_1238_);
lean_dec(v_k_1237_);
lean_dec(v_size_1236_);
lean_dec_ref_known(v_r_1229_, 5);
lean_del_object(v___x_1231_);
lean_dec(v_v_1227_);
lean_dec(v_k_1226_);
v___x_1317_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__3);
v___x_1318_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3_spec__3___redArg(v___x_1317_);
return v___x_1318_;
}
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
lean_del_object(v___x_1251_);
lean_dec(v_r_1240_);
lean_dec(v_v_1238_);
lean_dec(v_k_1237_);
lean_dec(v_size_1236_);
lean_dec_ref_known(v_r_1229_, 5);
lean_del_object(v___x_1231_);
lean_dec(v_v_1227_);
lean_dec(v_k_1226_);
v___x_1319_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__4);
v___x_1320_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3_spec__3___redArg(v___x_1319_);
return v___x_1320_;
}
}
}
}
else
{
lean_object* v_size_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v_size_1327_ = lean_ctor_get(v_r_1229_, 0);
v___x_1328_ = lean_unsigned_to_nat(1u);
v___x_1329_ = lean_nat_add(v___x_1328_, v_size_1327_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 3, v___x_1234_);
lean_ctor_set(v___x_1231_, 0, v___x_1329_);
v___x_1331_ = v___x_1231_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v_r_1229_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
else
{
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_l_1333_; 
v_l_1333_ = lean_ctor_get(v___x_1234_, 3);
if (lean_obj_tag(v_l_1333_) == 0)
{
lean_object* v_r_1334_; 
lean_inc_ref(v_l_1333_);
v_r_1334_ = lean_ctor_get(v___x_1234_, 4);
lean_inc(v_r_1334_);
if (lean_obj_tag(v_r_1334_) == 0)
{
lean_object* v_size_1335_; lean_object* v_k_1336_; lean_object* v_v_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1351_; 
v_size_1335_ = lean_ctor_get(v___x_1234_, 0);
v_k_1336_ = lean_ctor_get(v___x_1234_, 1);
v_v_1337_ = lean_ctor_get(v___x_1234_, 2);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; lean_object* v_unused_1353_; 
v_unused_1352_ = lean_ctor_get(v___x_1234_, 4);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v___x_1234_, 3);
lean_dec(v_unused_1353_);
v___x_1339_ = v___x_1234_;
v_isShared_1340_ = v_isSharedCheck_1351_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_v_1337_);
lean_inc(v_k_1336_);
lean_inc(v_size_1335_);
lean_dec(v___x_1234_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1351_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v_size_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
v_size_1341_ = lean_ctor_get(v_r_1334_, 0);
v___x_1342_ = lean_unsigned_to_nat(1u);
v___x_1343_ = lean_nat_add(v___x_1342_, v_size_1335_);
lean_dec(v_size_1335_);
v___x_1344_ = lean_nat_add(v___x_1342_, v_size_1341_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 4, v_r_1229_);
lean_ctor_set(v___x_1339_, 3, v_r_1334_);
lean_ctor_set(v___x_1339_, 2, v_v_1227_);
lean_ctor_set(v___x_1339_, 1, v_k_1226_);
lean_ctor_set(v___x_1339_, 0, v___x_1344_);
v___x_1346_ = v___x_1339_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1344_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v_r_1334_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v_r_1229_);
v___x_1346_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1348_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v___x_1346_);
lean_ctor_set(v___x_1231_, 3, v_l_1333_);
lean_ctor_set(v___x_1231_, 2, v_v_1337_);
lean_ctor_set(v___x_1231_, 1, v_k_1336_);
lean_ctor_set(v___x_1231_, 0, v___x_1343_);
v___x_1348_ = v___x_1231_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_k_1336_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_v_1337_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_l_1333_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
lean_object* v_k_1354_; lean_object* v_v_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1367_; 
v_k_1354_ = lean_ctor_get(v___x_1234_, 1);
v_v_1355_ = lean_ctor_get(v___x_1234_, 2);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; lean_object* v_unused_1369_; lean_object* v_unused_1370_; 
v_unused_1368_ = lean_ctor_get(v___x_1234_, 4);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v___x_1234_, 3);
lean_dec(v_unused_1369_);
v_unused_1370_ = lean_ctor_get(v___x_1234_, 0);
lean_dec(v_unused_1370_);
v___x_1357_ = v___x_1234_;
v_isShared_1358_ = v_isSharedCheck_1367_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_v_1355_);
lean_inc(v_k_1354_);
lean_dec(v___x_1234_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1367_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1359_ = lean_unsigned_to_nat(3u);
v___x_1360_ = lean_unsigned_to_nat(1u);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 3, v_r_1334_);
lean_ctor_set(v___x_1357_, 2, v_v_1227_);
lean_ctor_set(v___x_1357_, 1, v_k_1226_);
lean_ctor_set(v___x_1357_, 0, v___x_1360_);
v___x_1362_ = v___x_1357_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1366_, 3, v_r_1334_);
lean_ctor_set(v_reuseFailAlloc_1366_, 4, v_r_1334_);
v___x_1362_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1364_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v___x_1362_);
lean_ctor_set(v___x_1231_, 3, v_l_1333_);
lean_ctor_set(v___x_1231_, 2, v_v_1355_);
lean_ctor_set(v___x_1231_, 1, v_k_1354_);
lean_ctor_set(v___x_1231_, 0, v___x_1359_);
v___x_1364_ = v___x_1231_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_k_1354_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_v_1355_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v_l_1333_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
else
{
lean_object* v_r_1371_; 
v_r_1371_ = lean_ctor_get(v___x_1234_, 4);
lean_inc(v_r_1371_);
if (lean_obj_tag(v_r_1371_) == 0)
{
lean_object* v_k_1372_; lean_object* v_v_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1397_; 
lean_inc(v_l_1333_);
v_k_1372_ = lean_ctor_get(v___x_1234_, 1);
v_v_1373_ = lean_ctor_get(v___x_1234_, 2);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; lean_object* v_unused_1399_; lean_object* v_unused_1400_; 
v_unused_1398_ = lean_ctor_get(v___x_1234_, 4);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v___x_1234_, 3);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v___x_1234_, 0);
lean_dec(v_unused_1400_);
v___x_1375_ = v___x_1234_;
v_isShared_1376_ = v_isSharedCheck_1397_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_v_1373_);
lean_inc(v_k_1372_);
lean_dec(v___x_1234_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1397_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v_k_1377_; lean_object* v_v_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1393_; 
v_k_1377_ = lean_ctor_get(v_r_1371_, 1);
v_v_1378_ = lean_ctor_get(v_r_1371_, 2);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_r_1371_);
if (v_isSharedCheck_1393_ == 0)
{
lean_object* v_unused_1394_; lean_object* v_unused_1395_; lean_object* v_unused_1396_; 
v_unused_1394_ = lean_ctor_get(v_r_1371_, 4);
lean_dec(v_unused_1394_);
v_unused_1395_ = lean_ctor_get(v_r_1371_, 3);
lean_dec(v_unused_1395_);
v_unused_1396_ = lean_ctor_get(v_r_1371_, 0);
lean_dec(v_unused_1396_);
v___x_1380_ = v_r_1371_;
v_isShared_1381_ = v_isSharedCheck_1393_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_v_1378_);
lean_inc(v_k_1377_);
lean_dec(v_r_1371_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1393_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1382_ = lean_unsigned_to_nat(3u);
v___x_1383_ = lean_unsigned_to_nat(1u);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 4, v_l_1333_);
lean_ctor_set(v___x_1380_, 3, v_l_1333_);
lean_ctor_set(v___x_1380_, 2, v_v_1373_);
lean_ctor_set(v___x_1380_, 1, v_k_1372_);
lean_ctor_set(v___x_1380_, 0, v___x_1383_);
v___x_1385_ = v___x_1380_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_l_1333_);
lean_ctor_set(v_reuseFailAlloc_1392_, 4, v_l_1333_);
v___x_1385_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1387_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v_l_1333_);
lean_ctor_set(v___x_1375_, 2, v_v_1227_);
lean_ctor_set(v___x_1375_, 1, v_k_1226_);
lean_ctor_set(v___x_1375_, 0, v___x_1383_);
v___x_1387_ = v___x_1375_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_l_1333_);
lean_ctor_set(v_reuseFailAlloc_1391_, 4, v_l_1333_);
v___x_1387_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1389_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v___x_1387_);
lean_ctor_set(v___x_1231_, 3, v___x_1385_);
lean_ctor_set(v___x_1231_, 2, v_v_1378_);
lean_ctor_set(v___x_1231_, 1, v_k_1377_);
lean_ctor_set(v___x_1231_, 0, v___x_1382_);
v___x_1389_ = v___x_1231_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_k_1377_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_v_1378_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v___x_1387_);
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
}
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1401_ = lean_unsigned_to_nat(2u);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v_r_1371_);
lean_ctor_set(v___x_1231_, 3, v___x_1234_);
lean_ctor_set(v___x_1231_, 0, v___x_1401_);
v___x_1403_ = v___x_1231_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1404_, 3, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1404_, 4, v_r_1371_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
else
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1405_ = lean_unsigned_to_nat(1u);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v___x_1234_);
lean_ctor_set(v___x_1231_, 3, v___x_1234_);
lean_ctor_set(v___x_1231_, 0, v___x_1405_);
v___x_1407_ = v___x_1231_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1408_, 4, v___x_1234_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
case 1:
{
lean_object* v___x_1410_; 
lean_dec(v_v_1227_);
lean_dec(v_k_1226_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 2, v_v_1223_);
lean_ctor_set(v___x_1231_, 1, v_k_1222_);
v___x_1410_ = v___x_1231_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_size_1225_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_k_1222_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v_v_1223_);
lean_ctor_set(v_reuseFailAlloc_1411_, 3, v_l_1228_);
lean_ctor_set(v_reuseFailAlloc_1411_, 4, v_r_1229_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
default: 
{
lean_object* v___x_1412_; 
lean_dec(v_size_1225_);
v___x_1412_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg(v_k_1222_, v_v_1223_, v_r_1229_);
if (lean_obj_tag(v_l_1228_) == 0)
{
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_size_1413_; lean_object* v_size_1414_; lean_object* v_k_1415_; lean_object* v_v_1416_; lean_object* v_l_1417_; lean_object* v_r_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v_size_1413_ = lean_ctor_get(v_l_1228_, 0);
v_size_1414_ = lean_ctor_get(v___x_1412_, 0);
v_k_1415_ = lean_ctor_get(v___x_1412_, 1);
v_v_1416_ = lean_ctor_get(v___x_1412_, 2);
v_l_1417_ = lean_ctor_get(v___x_1412_, 3);
lean_inc(v_l_1417_);
v_r_1418_ = lean_ctor_get(v___x_1412_, 4);
v___x_1419_ = lean_unsigned_to_nat(3u);
v___x_1420_ = lean_nat_mul(v___x_1419_, v_size_1413_);
v___x_1421_ = lean_nat_dec_lt(v___x_1420_, v_size_1414_);
lean_dec(v___x_1420_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
lean_dec(v_l_1417_);
v___x_1422_ = lean_unsigned_to_nat(1u);
v___x_1423_ = lean_nat_add(v___x_1422_, v_size_1413_);
v___x_1424_ = lean_nat_add(v___x_1423_, v_size_1414_);
lean_dec(v___x_1423_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v___x_1412_);
lean_ctor_set(v___x_1231_, 0, v___x_1424_);
v___x_1426_ = v___x_1231_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1427_, 3, v_l_1228_);
lean_ctor_set(v_reuseFailAlloc_1427_, 4, v___x_1412_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
else
{
lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1497_; 
lean_inc(v_r_1418_);
lean_inc(v_v_1416_);
lean_inc(v_k_1415_);
lean_inc(v_size_1414_);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; lean_object* v_unused_1499_; lean_object* v_unused_1500_; lean_object* v_unused_1501_; lean_object* v_unused_1502_; 
v_unused_1498_ = lean_ctor_get(v___x_1412_, 4);
lean_dec(v_unused_1498_);
v_unused_1499_ = lean_ctor_get(v___x_1412_, 3);
lean_dec(v_unused_1499_);
v_unused_1500_ = lean_ctor_get(v___x_1412_, 2);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v___x_1412_, 1);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v___x_1412_, 0);
lean_dec(v_unused_1502_);
v___x_1429_ = v___x_1412_;
v_isShared_1430_ = v_isSharedCheck_1497_;
goto v_resetjp_1428_;
}
else
{
lean_dec(v___x_1412_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1497_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
if (lean_obj_tag(v_l_1417_) == 0)
{
if (lean_obj_tag(v_r_1418_) == 0)
{
lean_object* v_size_1431_; lean_object* v_k_1432_; lean_object* v_v_1433_; lean_object* v_l_1434_; lean_object* v_r_1435_; lean_object* v_size_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_size_1431_ = lean_ctor_get(v_l_1417_, 0);
v_k_1432_ = lean_ctor_get(v_l_1417_, 1);
v_v_1433_ = lean_ctor_get(v_l_1417_, 2);
v_l_1434_ = lean_ctor_get(v_l_1417_, 3);
v_r_1435_ = lean_ctor_get(v_l_1417_, 4);
v_size_1436_ = lean_ctor_get(v_r_1418_, 0);
v___x_1437_ = lean_unsigned_to_nat(2u);
v___x_1438_ = lean_nat_mul(v___x_1437_, v_size_1436_);
v___x_1439_ = lean_nat_dec_lt(v_size_1431_, v___x_1438_);
lean_dec(v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1468_; 
lean_inc(v_r_1435_);
lean_inc(v_l_1434_);
lean_inc(v_v_1433_);
lean_inc(v_k_1432_);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_l_1417_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; lean_object* v_unused_1470_; lean_object* v_unused_1471_; lean_object* v_unused_1472_; lean_object* v_unused_1473_; 
v_unused_1469_ = lean_ctor_get(v_l_1417_, 4);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_l_1417_, 3);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_l_1417_, 2);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_l_1417_, 1);
lean_dec(v_unused_1472_);
v_unused_1473_ = lean_ctor_get(v_l_1417_, 0);
lean_dec(v_unused_1473_);
v___x_1441_ = v_l_1417_;
v_isShared_1442_ = v_isSharedCheck_1468_;
goto v_resetjp_1440_;
}
else
{
lean_dec(v_l_1417_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1468_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1458_; 
v___x_1443_ = lean_unsigned_to_nat(1u);
v___x_1444_ = lean_nat_add(v___x_1443_, v_size_1413_);
v___x_1445_ = lean_nat_add(v___x_1444_, v_size_1414_);
lean_dec(v_size_1414_);
if (lean_obj_tag(v_l_1434_) == 0)
{
lean_object* v_size_1466_; 
v_size_1466_ = lean_ctor_get(v_l_1434_, 0);
lean_inc(v_size_1466_);
v___y_1458_ = v_size_1466_;
goto v___jp_1457_;
}
else
{
lean_object* v___x_1467_; 
v___x_1467_ = lean_unsigned_to_nat(0u);
v___y_1458_ = v___x_1467_;
goto v___jp_1457_;
}
v___jp_1446_:
{
lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1450_ = lean_nat_add(v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec(v___y_1448_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v_r_1418_);
lean_ctor_set(v___x_1441_, 3, v_r_1435_);
lean_ctor_set(v___x_1441_, 2, v_v_1416_);
lean_ctor_set(v___x_1441_, 1, v_k_1415_);
lean_ctor_set(v___x_1441_, 0, v___x_1450_);
v___x_1452_ = v___x_1441_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_k_1415_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_v_1416_);
lean_ctor_set(v_reuseFailAlloc_1456_, 3, v_r_1435_);
lean_ctor_set(v_reuseFailAlloc_1456_, 4, v_r_1418_);
v___x_1452_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1454_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 4, v___x_1452_);
lean_ctor_set(v___x_1429_, 3, v___y_1447_);
lean_ctor_set(v___x_1429_, 2, v_v_1433_);
lean_ctor_set(v___x_1429_, 1, v_k_1432_);
lean_ctor_set(v___x_1429_, 0, v___x_1445_);
v___x_1454_ = v___x_1429_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_k_1432_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_v_1433_);
lean_ctor_set(v_reuseFailAlloc_1455_, 3, v___y_1447_);
lean_ctor_set(v_reuseFailAlloc_1455_, 4, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
v___jp_1457_:
{
lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1459_ = lean_nat_add(v___x_1444_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec(v___x_1444_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v_l_1434_);
lean_ctor_set(v___x_1231_, 0, v___x_1459_);
v___x_1461_ = v___x_1231_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1465_, 3, v_l_1228_);
lean_ctor_set(v_reuseFailAlloc_1465_, 4, v_l_1434_);
v___x_1461_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_nat_add(v___x_1443_, v_size_1436_);
if (lean_obj_tag(v_r_1435_) == 0)
{
lean_object* v_size_1463_; 
v_size_1463_ = lean_ctor_get(v_r_1435_, 0);
lean_inc(v_size_1463_);
v___y_1447_ = v___x_1461_;
v___y_1448_ = v___x_1462_;
v___y_1449_ = v_size_1463_;
goto v___jp_1446_;
}
else
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_unsigned_to_nat(0u);
v___y_1447_ = v___x_1461_;
v___y_1448_ = v___x_1462_;
v___y_1449_ = v___x_1464_;
goto v___jp_1446_;
}
}
}
}
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
lean_del_object(v___x_1231_);
v___x_1474_ = lean_unsigned_to_nat(1u);
v___x_1475_ = lean_nat_add(v___x_1474_, v_size_1413_);
v___x_1476_ = lean_nat_add(v___x_1475_, v_size_1414_);
lean_dec(v_size_1414_);
v___x_1477_ = lean_nat_add(v___x_1475_, v_size_1431_);
lean_dec(v___x_1475_);
lean_inc_ref(v_l_1228_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 4, v_l_1417_);
lean_ctor_set(v___x_1429_, 3, v_l_1228_);
lean_ctor_set(v___x_1429_, 2, v_v_1227_);
lean_ctor_set(v___x_1429_, 1, v_k_1226_);
lean_ctor_set(v___x_1429_, 0, v___x_1477_);
v___x_1479_ = v___x_1429_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1492_, 3, v_l_1228_);
lean_ctor_set(v_reuseFailAlloc_1492_, 4, v_l_1417_);
v___x_1479_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
v_isSharedCheck_1486_ = !lean_is_exclusive(v_l_1228_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; lean_object* v_unused_1488_; lean_object* v_unused_1489_; lean_object* v_unused_1490_; lean_object* v_unused_1491_; 
v_unused_1487_ = lean_ctor_get(v_l_1228_, 4);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_l_1228_, 3);
lean_dec(v_unused_1488_);
v_unused_1489_ = lean_ctor_get(v_l_1228_, 2);
lean_dec(v_unused_1489_);
v_unused_1490_ = lean_ctor_get(v_l_1228_, 1);
lean_dec(v_unused_1490_);
v_unused_1491_ = lean_ctor_get(v_l_1228_, 0);
lean_dec(v_unused_1491_);
v___x_1481_ = v_l_1228_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_dec(v_l_1228_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 4, v_r_1418_);
lean_ctor_set(v___x_1481_, 3, v___x_1479_);
lean_ctor_set(v___x_1481_, 2, v_v_1416_);
lean_ctor_set(v___x_1481_, 1, v_k_1415_);
lean_ctor_set(v___x_1481_, 0, v___x_1476_);
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_k_1415_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_v_1416_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1485_, 4, v_r_1418_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_dec_ref_known(v_l_1417_, 5);
lean_del_object(v___x_1429_);
lean_dec(v_v_1416_);
lean_dec(v_k_1415_);
lean_dec(v_size_1414_);
lean_dec_ref_known(v_l_1228_, 5);
lean_del_object(v___x_1231_);
lean_dec(v_v_1227_);
lean_dec(v_k_1226_);
v___x_1493_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__7);
v___x_1494_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3_spec__3___redArg(v___x_1493_);
return v___x_1494_;
}
}
else
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_del_object(v___x_1429_);
lean_dec(v_r_1418_);
lean_dec(v_v_1416_);
lean_dec(v_k_1415_);
lean_dec(v_size_1414_);
lean_dec_ref_known(v_l_1228_, 5);
lean_del_object(v___x_1231_);
lean_dec(v_v_1227_);
lean_dec(v_k_1226_);
v___x_1495_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg___closed__8);
v___x_1496_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3_spec__3___redArg(v___x_1495_);
return v___x_1496_;
}
}
}
}
else
{
lean_object* v_size_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v_size_1503_ = lean_ctor_get(v_l_1228_, 0);
v___x_1504_ = lean_unsigned_to_nat(1u);
v___x_1505_ = lean_nat_add(v___x_1504_, v_size_1503_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v___x_1412_);
lean_ctor_set(v___x_1231_, 0, v___x_1505_);
v___x_1507_ = v___x_1231_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_l_1228_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v___x_1412_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
else
{
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_l_1509_; 
v_l_1509_ = lean_ctor_get(v___x_1412_, 3);
lean_inc(v_l_1509_);
if (lean_obj_tag(v_l_1509_) == 0)
{
lean_object* v_r_1510_; 
v_r_1510_ = lean_ctor_get(v___x_1412_, 4);
lean_inc(v_r_1510_);
if (lean_obj_tag(v_r_1510_) == 0)
{
lean_object* v_size_1511_; lean_object* v_k_1512_; lean_object* v_v_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1527_; 
v_size_1511_ = lean_ctor_get(v___x_1412_, 0);
v_k_1512_ = lean_ctor_get(v___x_1412_, 1);
v_v_1513_ = lean_ctor_get(v___x_1412_, 2);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; lean_object* v_unused_1529_; 
v_unused_1528_ = lean_ctor_get(v___x_1412_, 4);
lean_dec(v_unused_1528_);
v_unused_1529_ = lean_ctor_get(v___x_1412_, 3);
lean_dec(v_unused_1529_);
v___x_1515_ = v___x_1412_;
v_isShared_1516_ = v_isSharedCheck_1527_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_v_1513_);
lean_inc(v_k_1512_);
lean_inc(v_size_1511_);
lean_dec(v___x_1412_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1527_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v_size_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1522_; 
v_size_1517_ = lean_ctor_get(v_l_1509_, 0);
v___x_1518_ = lean_unsigned_to_nat(1u);
v___x_1519_ = lean_nat_add(v___x_1518_, v_size_1511_);
lean_dec(v_size_1511_);
v___x_1520_ = lean_nat_add(v___x_1518_, v_size_1517_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 4, v_l_1509_);
lean_ctor_set(v___x_1515_, 3, v_l_1228_);
lean_ctor_set(v___x_1515_, 2, v_v_1227_);
lean_ctor_set(v___x_1515_, 1, v_k_1226_);
lean_ctor_set(v___x_1515_, 0, v___x_1520_);
v___x_1522_ = v___x_1515_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1526_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1526_, 3, v_l_1228_);
lean_ctor_set(v_reuseFailAlloc_1526_, 4, v_l_1509_);
v___x_1522_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1524_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v_r_1510_);
lean_ctor_set(v___x_1231_, 3, v___x_1522_);
lean_ctor_set(v___x_1231_, 2, v_v_1513_);
lean_ctor_set(v___x_1231_, 1, v_k_1512_);
lean_ctor_set(v___x_1231_, 0, v___x_1519_);
v___x_1524_ = v___x_1231_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_k_1512_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_v_1513_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1525_, 4, v_r_1510_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
lean_object* v_k_1530_; lean_object* v_v_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1555_; 
v_k_1530_ = lean_ctor_get(v___x_1412_, 1);
v_v_1531_ = lean_ctor_get(v___x_1412_, 2);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; lean_object* v_unused_1557_; lean_object* v_unused_1558_; 
v_unused_1556_ = lean_ctor_get(v___x_1412_, 4);
lean_dec(v_unused_1556_);
v_unused_1557_ = lean_ctor_get(v___x_1412_, 3);
lean_dec(v_unused_1557_);
v_unused_1558_ = lean_ctor_get(v___x_1412_, 0);
lean_dec(v_unused_1558_);
v___x_1533_ = v___x_1412_;
v_isShared_1534_ = v_isSharedCheck_1555_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_v_1531_);
lean_inc(v_k_1530_);
lean_dec(v___x_1412_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1555_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v_k_1535_; lean_object* v_v_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1551_; 
v_k_1535_ = lean_ctor_get(v_l_1509_, 1);
v_v_1536_ = lean_ctor_get(v_l_1509_, 2);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_l_1509_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; lean_object* v_unused_1553_; lean_object* v_unused_1554_; 
v_unused_1552_ = lean_ctor_get(v_l_1509_, 4);
lean_dec(v_unused_1552_);
v_unused_1553_ = lean_ctor_get(v_l_1509_, 3);
lean_dec(v_unused_1553_);
v_unused_1554_ = lean_ctor_get(v_l_1509_, 0);
lean_dec(v_unused_1554_);
v___x_1538_ = v_l_1509_;
v_isShared_1539_ = v_isSharedCheck_1551_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_v_1536_);
lean_inc(v_k_1535_);
lean_dec(v_l_1509_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1551_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1540_ = lean_unsigned_to_nat(3u);
v___x_1541_ = lean_unsigned_to_nat(1u);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v_r_1510_);
lean_ctor_set(v___x_1538_, 3, v_r_1510_);
lean_ctor_set(v___x_1538_, 2, v_v_1227_);
lean_ctor_set(v___x_1538_, 1, v_k_1226_);
lean_ctor_set(v___x_1538_, 0, v___x_1541_);
v___x_1543_ = v___x_1538_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1550_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1550_, 3, v_r_1510_);
lean_ctor_set(v_reuseFailAlloc_1550_, 4, v_r_1510_);
v___x_1543_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1545_; 
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 3, v_r_1510_);
lean_ctor_set(v___x_1533_, 0, v___x_1541_);
v___x_1545_ = v___x_1533_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_k_1530_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_v_1531_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v_r_1510_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v_r_1510_);
v___x_1545_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1547_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v___x_1545_);
lean_ctor_set(v___x_1231_, 3, v___x_1543_);
lean_ctor_set(v___x_1231_, 2, v_v_1536_);
lean_ctor_set(v___x_1231_, 1, v_k_1535_);
lean_ctor_set(v___x_1231_, 0, v___x_1540_);
v___x_1547_ = v___x_1231_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_k_1535_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_v_1536_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v___x_1543_);
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
}
}
}
else
{
lean_object* v_r_1559_; 
v_r_1559_ = lean_ctor_get(v___x_1412_, 4);
lean_inc(v_r_1559_);
if (lean_obj_tag(v_r_1559_) == 0)
{
lean_object* v_k_1560_; lean_object* v_v_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1573_; 
v_k_1560_ = lean_ctor_get(v___x_1412_, 1);
v_v_1561_ = lean_ctor_get(v___x_1412_, 2);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; lean_object* v_unused_1575_; lean_object* v_unused_1576_; 
v_unused_1574_ = lean_ctor_get(v___x_1412_, 4);
lean_dec(v_unused_1574_);
v_unused_1575_ = lean_ctor_get(v___x_1412_, 3);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v___x_1412_, 0);
lean_dec(v_unused_1576_);
v___x_1563_ = v___x_1412_;
v_isShared_1564_ = v_isSharedCheck_1573_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_v_1561_);
lean_inc(v_k_1560_);
lean_dec(v___x_1412_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1573_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1565_ = lean_unsigned_to_nat(3u);
v___x_1566_ = lean_unsigned_to_nat(1u);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 4, v_l_1509_);
lean_ctor_set(v___x_1563_, 2, v_v_1227_);
lean_ctor_set(v___x_1563_, 1, v_k_1226_);
lean_ctor_set(v___x_1563_, 0, v___x_1566_);
v___x_1568_ = v___x_1563_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v_l_1509_);
lean_ctor_set(v_reuseFailAlloc_1572_, 4, v_l_1509_);
v___x_1568_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1570_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v_r_1559_);
lean_ctor_set(v___x_1231_, 3, v___x_1568_);
lean_ctor_set(v___x_1231_, 2, v_v_1561_);
lean_ctor_set(v___x_1231_, 1, v_k_1560_);
lean_ctor_set(v___x_1231_, 0, v___x_1565_);
v___x_1570_ = v___x_1231_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_k_1560_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_v_1561_);
lean_ctor_set(v_reuseFailAlloc_1571_, 3, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1571_, 4, v_r_1559_);
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
else
{
lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1577_ = lean_unsigned_to_nat(2u);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v___x_1412_);
lean_ctor_set(v___x_1231_, 3, v_r_1559_);
lean_ctor_set(v___x_1231_, 0, v___x_1577_);
v___x_1579_ = v___x_1231_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1580_, 3, v_r_1559_);
lean_ctor_set(v_reuseFailAlloc_1580_, 4, v___x_1412_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1581_ = lean_unsigned_to_nat(1u);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v___x_1412_);
lean_ctor_set(v___x_1231_, 3, v___x_1412_);
lean_ctor_set(v___x_1231_, 0, v___x_1581_);
v___x_1583_ = v___x_1231_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1584_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1584_, 3, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1584_, 4, v___x_1412_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_unsigned_to_nat(1u);
v___x_1587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
lean_ctor_set(v___x_1587_, 1, v_k_1222_);
lean_ctor_set(v___x_1587_, 2, v_v_1223_);
lean_ctor_set(v___x_1587_, 3, v_t_1224_);
lean_ctor_set(v___x_1587_, 4, v_t_1224_);
return v___x_1587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore(lean_object* v_depth_1609_, lean_object* v_kvs_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v_fst_1612_; lean_object* v_snd_1613_; lean_object* v___x_1614_; uint8_t v_decide_1615_; 
v_fst_1612_ = lean_ctor_get(v_a_1611_, 0);
v_snd_1613_ = lean_ctor_get(v_a_1611_, 1);
v___x_1614_ = lean_string_utf8_byte_size(v_fst_1612_);
v_decide_1615_ = lean_nat_dec_eq(v_snd_1613_, v___x_1614_);
if (v_decide_1615_ == 0)
{
uint32_t v___x_1616_; uint32_t v___x_1617_; uint8_t v___x_1618_; 
v___x_1616_ = lean_string_utf8_get_fast(v_fst_1612_, v_snd_1613_);
v___x_1617_ = 34;
v___x_1618_ = lean_uint32_dec_eq(v___x_1616_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
lean_dec(v_kvs_1610_);
v___x_1619_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__1));
v___x_1620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1620_, 0, v_a_1611_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
return v___x_1620_;
}
else
{
lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1736_; 
lean_inc(v_snd_1613_);
lean_inc(v_fst_1612_);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_a_1611_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; lean_object* v_unused_1738_; 
v_unused_1737_ = lean_ctor_get(v_a_1611_, 1);
lean_dec(v_unused_1737_);
v_unused_1738_ = lean_ctor_get(v_a_1611_, 0);
lean_dec(v_unused_1738_);
v___x_1622_ = v_a_1611_;
v_isShared_1623_ = v_isSharedCheck_1736_;
goto v_resetjp_1621_;
}
else
{
lean_dec(v_a_1611_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1736_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1624_ = lean_string_utf8_next_fast(v_fst_1612_, v_snd_1613_);
lean_dec(v_snd_1613_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 1, v___x_1624_);
v___x_1626_ = v___x_1622_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_fst_1612_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_1628_ = l_Lean_Json_Parser_strCore(v___x_1627_, v___x_1626_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_pos_1629_; lean_object* v_res_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1725_; 
v_pos_1629_ = lean_ctor_get(v___x_1628_, 0);
v_res_1630_ = lean_ctor_get(v___x_1628_, 1);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1632_ = v___x_1628_;
v_isShared_1633_ = v_isSharedCheck_1725_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_res_1630_);
lean_inc(v_pos_1629_);
lean_dec(v___x_1628_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1725_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v_fst_1634_; lean_object* v_snd_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1724_; 
v_fst_1634_ = lean_ctor_get(v_pos_1629_, 0);
v_snd_1635_ = lean_ctor_get(v_pos_1629_, 1);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_pos_1629_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1637_ = v_pos_1629_;
v_isShared_1638_ = v_isSharedCheck_1724_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_snd_1635_);
lean_inc(v_fst_1634_);
lean_dec(v_pos_1629_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1724_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1639_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1634_, v_snd_1635_);
lean_inc(v___x_1639_);
lean_inc(v_fst_1634_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 1, v___x_1639_);
v___x_1641_ = v___x_1637_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_fst_1634_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
uint8_t v___x_1642_; 
v___x_1642_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_res_1630_, v_kvs_1610_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; uint8_t v_decide_1644_; 
v___x_1643_ = lean_string_utf8_byte_size(v_fst_1634_);
v_decide_1644_ = lean_nat_dec_eq(v___x_1639_, v___x_1643_);
if (v_decide_1644_ == 0)
{
uint32_t v___x_1645_; uint32_t v___x_1646_; uint8_t v___x_1647_; 
v___x_1645_ = lean_string_utf8_get_fast(v_fst_1634_, v___x_1639_);
v___x_1646_ = 58;
v___x_1647_ = lean_uint32_dec_eq(v___x_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
lean_dec(v___x_1639_);
lean_dec(v_fst_1634_);
lean_dec(v_res_1630_);
lean_dec(v_kvs_1610_);
v___x_1648_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__3));
if (v_isShared_1633_ == 0)
{
lean_ctor_set_tag(v___x_1632_, 1);
lean_ctor_set(v___x_1632_, 1, v___x_1648_);
lean_ctor_set(v___x_1632_, 0, v___x_1641_);
v___x_1650_ = v___x_1632_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec_ref(v___x_1641_);
lean_del_object(v___x_1632_);
v___x_1652_ = lean_string_utf8_next_fast(v_fst_1634_, v___x_1639_);
lean_dec(v___x_1639_);
v___x_1653_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1634_, v___x_1652_);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_fst_1634_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = l_Lean_Json_Parser_anyCore(v_depth_1609_, v___x_1654_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_pos_1656_; lean_object* v_res_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1702_; 
v_pos_1656_ = lean_ctor_get(v___x_1655_, 0);
v_res_1657_ = lean_ctor_get(v___x_1655_, 1);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1659_ = v___x_1655_;
v_isShared_1660_ = v_isSharedCheck_1702_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_res_1657_);
lean_inc(v_pos_1656_);
lean_dec(v___x_1655_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1702_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v_fst_1661_; lean_object* v_snd_1662_; lean_object* v___x_1663_; uint8_t v_decide_1664_; 
v_fst_1661_ = lean_ctor_get(v_pos_1656_, 0);
v_snd_1662_ = lean_ctor_get(v_pos_1656_, 1);
v___x_1663_ = lean_string_utf8_byte_size(v_fst_1661_);
v_decide_1664_ = lean_nat_dec_eq(v_snd_1662_, v___x_1663_);
if (v_decide_1664_ == 0)
{
lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1695_; 
lean_inc(v_snd_1662_);
lean_inc(v_fst_1661_);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_pos_1656_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; lean_object* v_unused_1697_; 
v_unused_1696_ = lean_ctor_get(v_pos_1656_, 1);
lean_dec(v_unused_1696_);
v_unused_1697_ = lean_ctor_get(v_pos_1656_, 0);
lean_dec(v_unused_1697_);
v___x_1666_ = v_pos_1656_;
v_isShared_1667_ = v_isSharedCheck_1695_;
goto v_resetjp_1665_;
}
else
{
lean_dec(v_pos_1656_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1695_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
uint32_t v___x_1668_; lean_object* v___x_1669_; uint32_t v___x_1670_; uint8_t v___x_1671_; 
v___x_1668_ = lean_string_utf8_get_fast(v_fst_1661_, v_snd_1662_);
v___x_1669_ = lean_string_utf8_next_fast(v_fst_1661_, v_snd_1662_);
lean_dec(v_snd_1662_);
v___x_1670_ = 125;
v___x_1671_ = lean_uint32_dec_eq(v___x_1668_, v___x_1670_);
if (v___x_1671_ == 0)
{
uint32_t v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = 44;
v___x_1673_ = lean_uint32_dec_eq(v___x_1668_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1675_; 
lean_dec(v_res_1657_);
lean_dec(v_res_1630_);
lean_dec(v_kvs_1610_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v___x_1669_);
v___x_1675_ = v___x_1666_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_fst_1661_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v___x_1669_);
v___x_1675_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1676_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__5));
if (v_isShared_1660_ == 0)
{
lean_ctor_set_tag(v___x_1659_, 1);
lean_ctor_set(v___x_1659_, 1, v___x_1676_);
lean_ctor_set(v___x_1659_, 0, v___x_1675_);
v___x_1678_ = v___x_1659_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
lean_del_object(v___x_1659_);
v___x_1681_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1661_, v___x_1669_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v___x_1681_);
v___x_1683_ = v___x_1666_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_fst_1661_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg(v_res_1630_, v_res_1657_, v_kvs_1610_);
v_kvs_1610_ = v___x_1684_;
v_a_1611_ = v___x_1683_;
goto _start;
}
}
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1687_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1661_, v___x_1669_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v___x_1687_);
v___x_1689_ = v___x_1666_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_fst_1661_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg(v_res_1630_, v_res_1657_, v_kvs_1610_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 1, v___x_1690_);
lean_ctor_set(v___x_1659_, 0, v___x_1689_);
v___x_1692_ = v___x_1659_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v___x_1690_);
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
lean_object* v___x_1698_; lean_object* v___x_1700_; 
lean_dec(v_res_1657_);
lean_dec(v_res_1630_);
lean_dec(v_kvs_1610_);
v___x_1698_ = lean_box(0);
if (v_isShared_1660_ == 0)
{
lean_ctor_set_tag(v___x_1659_, 1);
lean_ctor_set(v___x_1659_, 1, v___x_1698_);
v___x_1700_ = v___x_1659_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_pos_1656_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_object* v_pos_1703_; lean_object* v_err_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec(v_res_1630_);
lean_dec(v_kvs_1610_);
v_pos_1703_ = lean_ctor_get(v___x_1655_, 0);
v_err_1704_ = lean_ctor_get(v___x_1655_, 1);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1655_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_err_1704_);
lean_inc(v_pos_1703_);
lean_dec(v___x_1655_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_pos_1703_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_err_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
lean_dec(v___x_1639_);
lean_dec(v_fst_1634_);
lean_dec(v_res_1630_);
lean_dec(v_kvs_1610_);
v___x_1712_ = lean_box(0);
if (v_isShared_1633_ == 0)
{
lean_ctor_set_tag(v___x_1632_, 1);
lean_ctor_set(v___x_1632_, 1, v___x_1712_);
lean_ctor_set(v___x_1632_, 0, v___x_1641_);
v___x_1714_ = v___x_1632_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
lean_dec(v___x_1639_);
lean_dec(v_fst_1634_);
lean_dec(v_kvs_1610_);
v___x_1716_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__6));
v___x_1717_ = l_String_quote(v_res_1630_);
v___x_1718_ = lean_string_append(v___x_1716_, v___x_1717_);
lean_dec_ref(v___x_1717_);
v___x_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set_tag(v___x_1632_, 1);
lean_ctor_set(v___x_1632_, 1, v___x_1719_);
lean_ctor_set(v___x_1632_, 0, v___x_1641_);
v___x_1721_ = v___x_1632_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1726_; lean_object* v_err_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v_kvs_1610_);
v_pos_1726_ = lean_ctor_get(v___x_1628_, 0);
v_err_1727_ = lean_ctor_get(v___x_1628_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1628_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_err_1727_);
lean_inc(v_pos_1726_);
lean_dec(v___x_1628_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_pos_1726_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_err_1727_);
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
}
}
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_dec(v_kvs_1610_);
v___x_1739_ = lean_box(0);
v___x_1740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1740_, 0, v_a_1611_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
return v___x_1740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object* v_depth_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v_fst_1786_; lean_object* v_snd_1787_; lean_object* v___x_1788_; uint8_t v_decide_1789_; 
v_fst_1786_ = lean_ctor_get(v_a_1751_, 0);
v_snd_1787_ = lean_ctor_get(v_a_1751_, 1);
v___x_1788_ = lean_string_utf8_byte_size(v_fst_1786_);
v_decide_1789_ = lean_nat_dec_eq(v_snd_1787_, v___x_1788_);
if (v_decide_1789_ == 0)
{
uint32_t v___x_1790_; uint32_t v___x_1791_; uint8_t v___x_1792_; 
v___x_1790_ = lean_string_utf8_get_fast(v_fst_1786_, v_snd_1787_);
v___x_1791_ = 91;
v___x_1792_ = lean_uint32_dec_eq(v___x_1790_, v___x_1791_);
if (v___x_1792_ == 0)
{
uint32_t v___x_2040_; uint8_t v___x_2041_; 
v___x_2040_ = 123;
v___x_2041_ = lean_uint32_dec_eq(v___x_1790_, v___x_2040_);
if (v___x_2041_ == 0)
{
goto v___jp_1793_;
}
else
{
goto v___jp_2035_;
}
}
else
{
goto v___jp_2035_;
}
v___jp_1793_:
{
if (v___x_1792_ == 0)
{
uint32_t v___x_1794_; uint8_t v___x_1795_; 
v___x_1794_ = 123;
v___x_1795_ = lean_uint32_dec_eq(v___x_1790_, v___x_1794_);
if (v___x_1795_ == 0)
{
uint32_t v___x_1796_; uint8_t v___x_1797_; 
v___x_1796_ = 34;
v___x_1797_ = lean_uint32_dec_eq(v___x_1790_, v___x_1796_);
if (v___x_1797_ == 0)
{
uint32_t v___x_1798_; uint8_t v___x_1799_; 
v___x_1798_ = 102;
v___x_1799_ = lean_uint32_dec_eq(v___x_1790_, v___x_1798_);
if (v___x_1799_ == 0)
{
uint32_t v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = 116;
v___x_1801_ = lean_uint32_dec_eq(v___x_1790_, v___x_1800_);
if (v___x_1801_ == 0)
{
uint32_t v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = 110;
v___x_1803_ = lean_uint32_dec_eq(v___x_1790_, v___x_1802_);
if (v___x_1803_ == 0)
{
uint32_t v___x_1804_; uint8_t v___x_1805_; 
v___x_1804_ = 45;
v___x_1805_ = lean_uint32_dec_eq(v___x_1790_, v___x_1804_);
if (v___x_1805_ == 0)
{
uint32_t v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = 48;
v___x_1807_ = lean_uint32_dec_le(v___x_1806_, v___x_1790_);
if (v___x_1807_ == 0)
{
goto v___jp_1783_;
}
else
{
uint32_t v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = 57;
v___x_1809_ = lean_uint32_dec_le(v___x_1790_, v___x_1808_);
if (v___x_1809_ == 0)
{
goto v___jp_1783_;
}
else
{
goto v___jp_1752_;
}
}
}
else
{
goto v___jp_1752_;
}
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__2));
v___x_1811_ = l_Std_Internal_Parsec_String_pstring(v___x_1810_, v_a_1751_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_pos_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1830_; 
v_pos_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1830_ == 0)
{
lean_object* v_unused_1831_; 
v_unused_1831_ = lean_ctor_get(v___x_1811_, 1);
lean_dec(v_unused_1831_);
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1830_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_pos_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1830_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v_fst_1816_; lean_object* v_snd_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1829_; 
v_fst_1816_ = lean_ctor_get(v_pos_1812_, 0);
v_snd_1817_ = lean_ctor_get(v_pos_1812_, 1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_pos_1812_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1819_ = v_pos_1812_;
v_isShared_1820_ = v_isSharedCheck_1829_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_snd_1817_);
lean_inc(v_fst_1816_);
lean_dec(v_pos_1812_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1829_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1821_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1816_, v_snd_1817_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 1, v___x_1821_);
v___x_1823_ = v___x_1819_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_fst_1816_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = lean_box(0);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 1, v___x_1824_);
lean_ctor_set(v___x_1814_, 0, v___x_1823_);
v___x_1826_ = v___x_1814_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
else
{
lean_object* v_pos_1832_; lean_object* v_err_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
v_pos_1832_ = lean_ctor_get(v___x_1811_, 0);
v_err_1833_ = lean_ctor_get(v___x_1811_, 1);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1811_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_err_1833_);
lean_inc(v_pos_1832_);
lean_dec(v___x_1811_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_pos_1832_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_err_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
else
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__3));
v___x_1842_ = l_Std_Internal_Parsec_String_pstring(v___x_1841_, v_a_1751_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_pos_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1861_; 
v_pos_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1861_ == 0)
{
lean_object* v_unused_1862_; 
v_unused_1862_ = lean_ctor_get(v___x_1842_, 1);
lean_dec(v_unused_1862_);
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1861_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_pos_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1861_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v_fst_1847_; lean_object* v_snd_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1860_; 
v_fst_1847_ = lean_ctor_get(v_pos_1843_, 0);
v_snd_1848_ = lean_ctor_get(v_pos_1843_, 1);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_pos_1843_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1850_ = v_pos_1843_;
v_isShared_1851_ = v_isSharedCheck_1860_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_snd_1848_);
lean_inc(v_fst_1847_);
lean_dec(v_pos_1843_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1860_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1847_, v_snd_1848_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 1, v___x_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_fst_1847_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1855_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__4));
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 1, v___x_1855_);
lean_ctor_set(v___x_1845_, 0, v___x_1854_);
v___x_1857_ = v___x_1845_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
else
{
lean_object* v_pos_1863_; lean_object* v_err_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
v_pos_1863_ = lean_ctor_get(v___x_1842_, 0);
v_err_1864_ = lean_ctor_get(v___x_1842_, 1);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1842_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_err_1864_);
lean_inc(v_pos_1863_);
lean_dec(v___x_1842_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_pos_1863_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_err_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__5));
v___x_1873_ = l_Std_Internal_Parsec_String_pstring(v___x_1872_, v_a_1751_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_pos_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1892_; 
v_pos_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1892_ == 0)
{
lean_object* v_unused_1893_; 
v_unused_1893_ = lean_ctor_get(v___x_1873_, 1);
lean_dec(v_unused_1893_);
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1892_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_pos_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1892_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v_fst_1878_; lean_object* v_snd_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1891_; 
v_fst_1878_ = lean_ctor_get(v_pos_1874_, 0);
v_snd_1879_ = lean_ctor_get(v_pos_1874_, 1);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_pos_1874_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1881_ = v_pos_1874_;
v_isShared_1882_ = v_isSharedCheck_1891_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_snd_1879_);
lean_inc(v_fst_1878_);
lean_dec(v_pos_1874_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1891_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1883_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1878_, v_snd_1879_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 1, v___x_1883_);
v___x_1885_ = v___x_1881_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_fst_1878_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1886_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1886_, 0, v___x_1797_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 1, v___x_1886_);
lean_ctor_set(v___x_1876_, 0, v___x_1885_);
v___x_1888_ = v___x_1876_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
else
{
lean_object* v_pos_1894_; lean_object* v_err_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
v_pos_1894_ = lean_ctor_get(v___x_1873_, 0);
v_err_1895_ = lean_ctor_get(v___x_1873_, 1);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1873_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_err_1895_);
lean_inc(v_pos_1894_);
lean_dec(v___x_1873_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_pos_1894_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_err_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
else
{
lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1941_; 
lean_inc(v_snd_1787_);
lean_inc(v_fst_1786_);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_a_1751_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; lean_object* v_unused_1943_; 
v_unused_1942_ = lean_ctor_get(v_a_1751_, 1);
lean_dec(v_unused_1942_);
v_unused_1943_ = lean_ctor_get(v_a_1751_, 0);
lean_dec(v_unused_1943_);
v___x_1904_ = v_a_1751_;
v_isShared_1905_ = v_isSharedCheck_1941_;
goto v_resetjp_1903_;
}
else
{
lean_dec(v_a_1751_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1941_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1906_ = lean_string_utf8_next_fast(v_fst_1786_, v_snd_1787_);
lean_dec(v_snd_1787_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 1, v___x_1906_);
v___x_1908_ = v___x_1904_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_fst_1786_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_1910_ = l_Lean_Json_Parser_strCore(v___x_1909_, v___x_1908_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_pos_1911_; lean_object* v_res_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1930_; 
v_pos_1911_ = lean_ctor_get(v___x_1910_, 0);
v_res_1912_ = lean_ctor_get(v___x_1910_, 1);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1914_ = v___x_1910_;
v_isShared_1915_ = v_isSharedCheck_1930_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_res_1912_);
lean_inc(v_pos_1911_);
lean_dec(v___x_1910_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1930_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v_fst_1916_; lean_object* v_snd_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1929_; 
v_fst_1916_ = lean_ctor_get(v_pos_1911_, 0);
v_snd_1917_ = lean_ctor_get(v_pos_1911_, 1);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_pos_1911_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1919_ = v_pos_1911_;
v_isShared_1920_ = v_isSharedCheck_1929_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_snd_1917_);
lean_inc(v_fst_1916_);
lean_dec(v_pos_1911_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1929_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1921_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1916_, v_snd_1917_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 1, v___x_1921_);
v___x_1923_ = v___x_1919_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_fst_1916_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1924_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1924_, 0, v_res_1912_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 1, v___x_1924_);
lean_ctor_set(v___x_1914_, 0, v___x_1923_);
v___x_1926_ = v___x_1914_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
else
{
lean_object* v_pos_1931_; lean_object* v_err_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
v_pos_1931_ = lean_ctor_get(v___x_1910_, 0);
v_err_1932_ = lean_ctor_get(v___x_1910_, 1);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1910_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_err_1932_);
lean_inc(v_pos_1931_);
lean_dec(v___x_1910_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_pos_1931_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_err_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1986_; 
lean_inc(v_snd_1787_);
lean_inc(v_fst_1786_);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_a_1751_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; lean_object* v_unused_1988_; 
v_unused_1987_ = lean_ctor_get(v_a_1751_, 1);
lean_dec(v_unused_1987_);
v_unused_1988_ = lean_ctor_get(v_a_1751_, 0);
lean_dec(v_unused_1988_);
v___x_1945_ = v_a_1751_;
v_isShared_1946_ = v_isSharedCheck_1986_;
goto v_resetjp_1944_;
}
else
{
lean_dec(v_a_1751_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1986_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1950_; 
v___x_1947_ = lean_string_utf8_next_fast(v_fst_1786_, v_snd_1787_);
lean_dec(v_snd_1787_);
v___x_1948_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1786_, v___x_1947_);
lean_inc(v___x_1948_);
lean_inc(v_fst_1786_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v___x_1948_);
v___x_1950_ = v___x_1945_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_fst_1786_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
uint8_t v_decide_1951_; 
v_decide_1951_ = lean_nat_dec_eq(v___x_1948_, v___x_1788_);
if (v_decide_1951_ == 0)
{
uint32_t v___x_1952_; uint32_t v___x_1953_; uint8_t v___x_1954_; 
v___x_1952_ = lean_string_utf8_get_fast(v_fst_1786_, v___x_1948_);
v___x_1953_ = 125;
v___x_1954_ = lean_uint32_dec_eq(v___x_1952_, v___x_1953_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_dec(v___x_1948_);
lean_dec(v_fst_1786_);
v___x_1955_ = lean_unsigned_to_nat(1u);
v___x_1956_ = lean_nat_sub(v_depth_1750_, v___x_1955_);
v___x_1957_ = lean_box(1);
v___x_1958_ = l_Lean_Json_Parser_objectCore(v___x_1956_, v___x_1957_, v___x_1950_);
lean_dec(v___x_1956_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_pos_1959_; lean_object* v_res_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1968_; 
v_pos_1959_ = lean_ctor_get(v___x_1958_, 0);
v_res_1960_ = lean_ctor_get(v___x_1958_, 1);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1962_ = v___x_1958_;
v_isShared_1963_ = v_isSharedCheck_1968_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_res_1960_);
lean_inc(v_pos_1959_);
lean_dec(v___x_1958_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1968_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1964_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1964_, 0, v_res_1960_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 1, v___x_1964_);
v___x_1966_ = v___x_1962_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_pos_1959_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
else
{
lean_object* v_pos_1969_; lean_object* v_err_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
v_pos_1969_ = lean_ctor_get(v___x_1958_, 0);
v_err_1970_ = lean_ctor_get(v___x_1958_, 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1958_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_err_1970_);
lean_inc(v_pos_1969_);
lean_dec(v___x_1958_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_pos_1969_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_err_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
lean_dec_ref(v___x_1950_);
v___x_1978_ = lean_string_utf8_next_fast(v_fst_1786_, v___x_1948_);
lean_dec(v___x_1948_);
v___x_1979_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1786_, v___x_1978_);
v___x_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1980_, 0, v_fst_1786_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__6));
v___x_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
return v___x_1982_;
}
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
lean_dec(v___x_1948_);
lean_dec(v_fst_1786_);
v___x_1983_ = lean_box(0);
v___x_1984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1950_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
return v___x_1984_;
}
}
}
}
}
else
{
lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2032_; 
lean_inc(v_snd_1787_);
lean_inc(v_fst_1786_);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_a_1751_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; lean_object* v_unused_2034_; 
v_unused_2033_ = lean_ctor_get(v_a_1751_, 1);
lean_dec(v_unused_2033_);
v_unused_2034_ = lean_ctor_get(v_a_1751_, 0);
lean_dec(v_unused_2034_);
v___x_1990_ = v_a_1751_;
v_isShared_1991_ = v_isSharedCheck_2032_;
goto v_resetjp_1989_;
}
else
{
lean_dec(v_a_1751_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2032_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1992_ = lean_string_utf8_next_fast(v_fst_1786_, v_snd_1787_);
lean_dec(v_snd_1787_);
v___x_1993_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1786_, v___x_1992_);
lean_inc(v___x_1993_);
lean_inc(v_fst_1786_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 1, v___x_1993_);
v___x_1995_ = v___x_1990_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_fst_1786_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_2031_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
uint8_t v_decide_1996_; 
v_decide_1996_ = lean_nat_dec_eq(v___x_1993_, v___x_1788_);
if (v_decide_1996_ == 0)
{
uint32_t v___x_1997_; uint32_t v___x_1998_; uint8_t v___x_1999_; 
v___x_1997_ = lean_string_utf8_get_fast(v_fst_1786_, v___x_1993_);
v___x_1998_ = 93;
v___x_1999_ = lean_uint32_dec_eq(v___x_1997_, v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
lean_dec(v___x_1993_);
lean_dec(v_fst_1786_);
v___x_2000_ = lean_unsigned_to_nat(1u);
v___x_2001_ = lean_nat_sub(v_depth_1750_, v___x_2000_);
v___x_2002_ = lean_unsigned_to_nat(4u);
v___x_2003_ = lean_mk_empty_array_with_capacity(v___x_2002_);
v___x_2004_ = l_Lean_Json_Parser_arrayCore(v___x_2001_, v___x_2003_, v___x_1995_);
lean_dec(v___x_2001_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_pos_2005_; lean_object* v_res_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2014_; 
v_pos_2005_ = lean_ctor_get(v___x_2004_, 0);
v_res_2006_ = lean_ctor_get(v___x_2004_, 1);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2008_ = v___x_2004_;
v_isShared_2009_ = v_isSharedCheck_2014_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_res_2006_);
lean_inc(v_pos_2005_);
lean_dec(v___x_2004_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2014_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2010_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2010_, 0, v_res_2006_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 1, v___x_2010_);
v___x_2012_ = v___x_2008_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_pos_2005_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
else
{
lean_object* v_pos_2015_; lean_object* v_err_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
v_pos_2015_ = lean_ctor_get(v___x_2004_, 0);
v_err_2016_ = lean_ctor_get(v___x_2004_, 1);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2004_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_err_2016_);
lean_inc(v_pos_2015_);
lean_dec(v___x_2004_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_pos_2015_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_err_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
lean_dec_ref(v___x_1995_);
v___x_2024_ = lean_string_utf8_next_fast(v_fst_1786_, v___x_1993_);
lean_dec(v___x_1993_);
v___x_2025_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1786_, v___x_2024_);
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v_fst_1786_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__8));
v___x_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2026_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
return v___x_2028_;
}
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
lean_dec(v___x_1993_);
lean_dec(v_fst_1786_);
v___x_2029_ = lean_box(0);
v___x_2030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_1995_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
return v___x_2030_;
}
}
}
}
}
v___jp_2035_:
{
lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = lean_unsigned_to_nat(0u);
v___x_2037_ = lean_nat_dec_eq(v_depth_1750_, v___x_2036_);
if (v___x_2037_ == 0)
{
goto v___jp_1793_;
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__10));
v___x_2039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2039_, 0, v_a_1751_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
return v___x_2039_;
}
}
}
else
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_box(0);
v___x_2043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2043_, 0, v_a_1751_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
return v___x_2043_;
}
v___jp_1752_:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_Json_Parser_num(v_a_1751_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_pos_1754_; lean_object* v_res_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1773_; 
v_pos_1754_ = lean_ctor_get(v___x_1753_, 0);
v_res_1755_ = lean_ctor_get(v___x_1753_, 1);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1757_ = v___x_1753_;
v_isShared_1758_ = v_isSharedCheck_1773_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_res_1755_);
lean_inc(v_pos_1754_);
lean_dec(v___x_1753_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1773_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v_fst_1759_; lean_object* v_snd_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1772_; 
v_fst_1759_ = lean_ctor_get(v_pos_1754_, 0);
v_snd_1760_ = lean_ctor_get(v_pos_1754_, 1);
v_isSharedCheck_1772_ = !lean_is_exclusive(v_pos_1754_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1762_ = v_pos_1754_;
v_isShared_1763_ = v_isSharedCheck_1772_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_snd_1760_);
lean_inc(v_fst_1759_);
lean_dec(v_pos_1754_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1772_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1764_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1759_, v_snd_1760_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 1, v___x_1764_);
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_fst_1759_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1767_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1767_, 0, v_res_1755_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 1, v___x_1767_);
lean_ctor_set(v___x_1757_, 0, v___x_1766_);
v___x_1769_ = v___x_1757_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v___x_1767_);
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
}
else
{
lean_object* v_pos_1774_; lean_object* v_err_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
v_pos_1774_ = lean_ctor_get(v___x_1753_, 0);
v_err_1775_ = lean_ctor_get(v___x_1753_, 1);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1753_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_err_1775_);
lean_inc(v_pos_1774_);
lean_dec(v___x_1753_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_pos_1774_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_err_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
v___jp_1783_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__1));
v___x_1785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1785_, 0, v_a_1751_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
return v___x_1785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore(lean_object* v_depth_2044_, lean_object* v_acc_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_Json_Parser_anyCore(v_depth_2044_, v_a_2046_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_pos_2048_; lean_object* v_res_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2093_; 
v_pos_2048_ = lean_ctor_get(v___x_2047_, 0);
v_res_2049_ = lean_ctor_get(v___x_2047_, 1);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2051_ = v___x_2047_;
v_isShared_2052_ = v_isSharedCheck_2093_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_res_2049_);
lean_inc(v_pos_2048_);
lean_dec(v___x_2047_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2093_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v_fst_2053_; lean_object* v_snd_2054_; lean_object* v___x_2055_; uint8_t v_decide_2056_; 
v_fst_2053_ = lean_ctor_get(v_pos_2048_, 0);
v_snd_2054_ = lean_ctor_get(v_pos_2048_, 1);
v___x_2055_ = lean_string_utf8_byte_size(v_fst_2053_);
v_decide_2056_ = lean_nat_dec_eq(v_snd_2054_, v___x_2055_);
if (v_decide_2056_ == 0)
{
lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2086_; 
lean_inc(v_snd_2054_);
lean_inc(v_fst_2053_);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_pos_2048_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; lean_object* v_unused_2088_; 
v_unused_2087_ = lean_ctor_get(v_pos_2048_, 1);
lean_dec(v_unused_2087_);
v_unused_2088_ = lean_ctor_get(v_pos_2048_, 0);
lean_dec(v_unused_2088_);
v___x_2058_ = v_pos_2048_;
v_isShared_2059_ = v_isSharedCheck_2086_;
goto v_resetjp_2057_;
}
else
{
lean_dec(v_pos_2048_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2086_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; uint32_t v___x_2061_; lean_object* v___x_2062_; uint32_t v___x_2063_; uint8_t v___x_2064_; 
v___x_2060_ = lean_array_push(v_acc_2045_, v_res_2049_);
v___x_2061_ = lean_string_utf8_get_fast(v_fst_2053_, v_snd_2054_);
v___x_2062_ = lean_string_utf8_next_fast(v_fst_2053_, v_snd_2054_);
lean_dec(v_snd_2054_);
v___x_2063_ = 93;
v___x_2064_ = lean_uint32_dec_eq(v___x_2061_, v___x_2063_);
if (v___x_2064_ == 0)
{
uint32_t v___x_2065_; uint8_t v___x_2066_; 
v___x_2065_ = 44;
v___x_2066_ = lean_uint32_dec_eq(v___x_2061_, v___x_2065_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2068_; 
lean_dec_ref(v___x_2060_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 1, v___x_2062_);
v___x_2068_ = v___x_2058_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_fst_2053_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v___x_2062_);
v___x_2068_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2069_ = ((lean_object*)(l_Lean_Json_Parser_arrayCore___closed__1));
if (v_isShared_2052_ == 0)
{
lean_ctor_set_tag(v___x_2051_, 1);
lean_ctor_set(v___x_2051_, 1, v___x_2069_);
lean_ctor_set(v___x_2051_, 0, v___x_2068_);
v___x_2071_ = v___x_2051_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
lean_del_object(v___x_2051_);
v___x_2074_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2053_, v___x_2062_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 1, v___x_2074_);
v___x_2076_ = v___x_2058_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_fst_2053_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
v_acc_2045_ = v___x_2060_;
v_a_2046_ = v___x_2076_;
goto _start;
}
}
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2079_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2053_, v___x_2062_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 1, v___x_2079_);
v___x_2081_ = v___x_2058_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_fst_2053_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
lean_object* v___x_2083_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v___x_2060_);
lean_ctor_set(v___x_2051_, 0, v___x_2081_);
v___x_2083_ = v___x_2051_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v___x_2060_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
lean_dec(v_res_2049_);
lean_dec_ref(v_acc_2045_);
v___x_2089_ = lean_box(0);
if (v_isShared_2052_ == 0)
{
lean_ctor_set_tag(v___x_2051_, 1);
lean_ctor_set(v___x_2051_, 1, v___x_2089_);
v___x_2091_ = v___x_2051_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_pos_2048_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
lean_object* v_pos_2094_; lean_object* v_err_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec_ref(v_acc_2045_);
v_pos_2094_ = lean_ctor_get(v___x_2047_, 0);
v_err_2095_ = lean_ctor_get(v___x_2047_, 1);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2047_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_err_2095_);
lean_inc(v_pos_2094_);
lean_dec(v___x_2047_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_pos_2094_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_err_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore___boxed(lean_object* v_depth_2103_, lean_object* v_acc_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_Json_Parser_arrayCore(v_depth_2103_, v_acc_2104_, v_a_2105_);
lean_dec(v_depth_2103_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore___boxed(lean_object* v_depth_2107_, lean_object* v_kvs_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_Json_Parser_objectCore(v_depth_2107_, v_kvs_2108_, v_a_2109_);
lean_dec(v_depth_2107_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore___boxed(lean_object* v_depth_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Lean_Json_Parser_anyCore(v_depth_2111_, v_a_2112_);
lean_dec(v_depth_2111_);
return v_res_2113_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2(lean_object* v_00_u03b2_2114_, lean_object* v_k_2115_, lean_object* v_t_2116_){
_start:
{
uint8_t v___x_2117_; 
v___x_2117_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_2115_, v_t_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2___boxed(lean_object* v_00_u03b2_2118_, lean_object* v_k_2119_, lean_object* v_t_2120_){
_start:
{
uint8_t v_res_2121_; lean_object* v_r_2122_; 
v_res_2121_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Json_Parser_objectCore_spec__2(v_00_u03b2_2118_, v_k_2119_, v_t_2120_);
lean_dec(v_t_2120_);
lean_dec_ref(v_k_2119_);
v_r_2122_ = lean_box(v_res_2121_);
return v_r_2122_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3_spec__3(lean_object* v_00_u03b2_2123_, lean_object* v_msg_2124_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3_spec__3___redArg(v_msg_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3(lean_object* v_00_u03b2_2126_, lean_object* v_k_2127_, lean_object* v_v_2128_, lean_object* v_t_2129_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__3___redArg(v_k_2127_, v_v_2128_, v_t_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_any(lean_object* v_a_2134_){
_start:
{
lean_object* v_fst_2135_; lean_object* v_snd_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2161_; 
v_fst_2135_ = lean_ctor_get(v_a_2134_, 0);
v_snd_2136_ = lean_ctor_get(v_a_2134_, 1);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_a_2134_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2138_ = v_a_2134_;
v_isShared_2139_ = v_isSharedCheck_2161_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_snd_2136_);
lean_inc(v_fst_2135_);
lean_dec(v_a_2134_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2161_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2135_, v_snd_2136_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 1, v___x_2140_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_fst_2135_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_unsigned_to_nat(10000u);
v___x_2144_ = l_Lean_Json_Parser_anyCore(v___x_2143_, v___x_2142_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_pos_2145_; lean_object* v_fst_2146_; lean_object* v_snd_2147_; lean_object* v___x_2148_; uint8_t v_decide_2149_; 
v_pos_2145_ = lean_ctor_get(v___x_2144_, 0);
v_fst_2146_ = lean_ctor_get(v_pos_2145_, 0);
v_snd_2147_ = lean_ctor_get(v_pos_2145_, 1);
v___x_2148_ = lean_string_utf8_byte_size(v_fst_2146_);
v_decide_2149_ = lean_nat_dec_eq(v_snd_2147_, v___x_2148_);
if (v_decide_2149_ == 0)
{
lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2157_; 
lean_inc(v_pos_2145_);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2157_ == 0)
{
lean_object* v_unused_2158_; lean_object* v_unused_2159_; 
v_unused_2158_ = lean_ctor_get(v___x_2144_, 1);
lean_dec(v_unused_2158_);
v_unused_2159_ = lean_ctor_get(v___x_2144_, 0);
lean_dec(v_unused_2159_);
v___x_2151_ = v___x_2144_;
v_isShared_2152_ = v_isSharedCheck_2157_;
goto v_resetjp_2150_;
}
else
{
lean_dec(v___x_2144_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2157_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2153_ = ((lean_object*)(l_Lean_Json_Parser_any___closed__1));
if (v_isShared_2152_ == 0)
{
lean_ctor_set_tag(v___x_2151_, 1);
lean_ctor_set(v___x_2151_, 1, v___x_2153_);
v___x_2155_ = v___x_2151_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_pos_2145_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
else
{
return v___x_2144_;
}
}
else
{
return v___x_2144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parse(lean_object* v_s_2162_){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
v___x_2164_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_2163_, v_s_2162_);
return v___x_2164_;
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
l_Lean_Json_Parser_maxDepth = _init_l_Lean_Json_Parser_maxDepth();
lean_mark_persistent(l_Lean_Json_Parser_maxDepth);
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
