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
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint32_t lean_uint32_sub(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_shiftl(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_shiftr(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Json_Parser_exponent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "exp too large"};
static const lean_object* l_Lean_Json_Parser_exponent___closed__0 = (const lean_object*)&l_Lean_Json_Parser_exponent___closed__0_value;
static const lean_ctor_object l_Lean_Json_Parser_exponent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_exponent___closed__0_value)}};
static const lean_object* l_Lean_Json_Parser_exponent___closed__1 = (const lean_object*)&l_Lean_Json_Parser_exponent___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Json_Parser_num_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_num(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Json_Parser_anyCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__5 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__5_value;
static const lean_array_object l_Lean_Json_Parser_anyCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__6 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__6_value;
static const lean_ctor_object l_Lean_Json_Parser_anyCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_anyCore___closed__6_value)}};
static const lean_object* l_Lean_Json_Parser_anyCore___closed__7 = (const lean_object*)&l_Lean_Json_Parser_anyCore___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Json_Parser_any___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l_Lean_Json_Parser_any___closed__0 = (const lean_object*)&l_Lean_Json_Parser_any___closed__0_value;
static const lean_ctor_object l_Lean_Json_Parser_any___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_Parser_any___closed__0_value)}};
static const lean_object* l_Lean_Json_Parser_any___closed__1 = (const lean_object*)&l_Lean_Json_Parser_any___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_any(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_hexChar(lean_object* v_a_4_){
_start:
{
lean_object* v_fst_5_; lean_object* v_snd_6_; lean_object* v___x_7_; uint8_t v___x_8_; 
v_fst_5_ = lean_ctor_get(v_a_4_, 0);
v_snd_6_ = lean_ctor_get(v_a_4_, 1);
v___x_7_ = lean_string_utf8_byte_size(v_fst_5_);
v___x_8_ = lean_nat_dec_eq(v_snd_6_, v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_55_; 
lean_inc(v_snd_6_);
lean_inc(v_fst_5_);
v_isSharedCheck_55_ = !lean_is_exclusive(v_a_4_);
if (v_isSharedCheck_55_ == 0)
{
lean_object* v_unused_56_; lean_object* v_unused_57_; 
v_unused_56_ = lean_ctor_get(v_a_4_, 1);
lean_dec(v_unused_56_);
v_unused_57_ = lean_ctor_get(v_a_4_, 0);
lean_dec(v_unused_57_);
v___x_10_ = v_a_4_;
v_isShared_11_ = v_isSharedCheck_55_;
goto v_resetjp_9_;
}
else
{
lean_dec(v_a_4_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_55_;
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
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_fst_5_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v___x_13_);
v_it_x27_15_ = v_reuseFailAlloc_54_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
uint32_t v___y_17_; uint8_t v___y_18_; uint32_t v___y_28_; uint8_t v___y_29_; uint32_t v___x_40_; uint8_t v___y_42_; uint8_t v___x_51_; 
v___x_40_ = 48;
v___x_51_ = lean_uint32_dec_le(v___x_40_, v_c_12_);
if (v___x_51_ == 0)
{
v___y_42_ = v___x_51_;
goto v___jp_41_;
}
else
{
uint32_t v___x_52_; uint8_t v___x_53_; 
v___x_52_ = 57;
v___x_53_ = lean_uint32_dec_le(v_c_12_, v___x_52_);
v___y_42_ = v___x_53_;
goto v___jp_41_;
}
v___jp_16_:
{
if (v___y_18_ == 0)
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = ((lean_object*)(l_Lean_Json_Parser_hexChar___closed__1));
v___x_20_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_20_, 0, v_it_x27_15_);
lean_ctor_set(v___x_20_, 1, v___x_19_);
return v___x_20_;
}
else
{
uint32_t v___x_21_; uint32_t v___x_22_; uint32_t v___x_23_; uint16_t v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_21_ = lean_uint32_sub(v_c_12_, v___y_17_);
v___x_22_ = 10;
v___x_23_ = lean_uint32_add(v___x_21_, v___x_22_);
v___x_24_ = lean_uint32_to_uint16(v___x_23_);
v___x_25_ = lean_box(v___x_24_);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v_it_x27_15_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
return v___x_26_;
}
}
v___jp_27_:
{
if (v___y_29_ == 0)
{
uint32_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = 65;
v___x_31_ = lean_uint32_dec_le(v___x_30_, v_c_12_);
if (v___x_31_ == 0)
{
v___y_17_ = v___x_30_;
v___y_18_ = v___x_31_;
goto v___jp_16_;
}
else
{
uint32_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 70;
v___x_33_ = lean_uint32_dec_le(v_c_12_, v___x_32_);
v___y_17_ = v___x_30_;
v___y_18_ = v___x_33_;
goto v___jp_16_;
}
}
else
{
uint32_t v___x_34_; uint32_t v___x_35_; uint32_t v___x_36_; uint16_t v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_34_ = lean_uint32_sub(v_c_12_, v___y_28_);
v___x_35_ = 10;
v___x_36_ = lean_uint32_add(v___x_34_, v___x_35_);
v___x_37_ = lean_uint32_to_uint16(v___x_36_);
v___x_38_ = lean_box(v___x_37_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v_it_x27_15_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
return v___x_39_;
}
}
v___jp_41_:
{
if (v___y_42_ == 0)
{
uint32_t v___x_43_; uint8_t v___x_44_; 
v___x_43_ = 97;
v___x_44_ = lean_uint32_dec_le(v___x_43_, v_c_12_);
if (v___x_44_ == 0)
{
v___y_28_ = v___x_43_;
v___y_29_ = v___x_44_;
goto v___jp_27_;
}
else
{
uint32_t v___x_45_; uint8_t v___x_46_; 
v___x_45_ = 102;
v___x_46_ = lean_uint32_dec_le(v_c_12_, v___x_45_);
v___y_28_ = v___x_43_;
v___y_29_ = v___x_46_;
goto v___jp_27_;
}
}
else
{
uint32_t v___x_47_; uint16_t v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_47_ = lean_uint32_sub(v_c_12_, v___x_40_);
v___x_48_ = lean_uint32_to_uint16(v___x_47_);
v___x_49_ = lean_box(v___x_48_);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v_it_x27_15_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
return v___x_50_;
}
}
}
}
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_box(0);
v___x_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_59_, 0, v_a_4_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair(uint16_t v_low_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___y_66_; lean_object* v_fst_69_; lean_object* v_snd_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v_fst_69_ = lean_ctor_get(v_a_64_, 0);
v_snd_70_ = lean_ctor_get(v_a_64_, 1);
v___x_71_ = lean_string_utf8_byte_size(v_fst_69_);
v___x_72_ = lean_nat_dec_eq(v_snd_70_, v___x_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_188_; 
lean_inc(v_snd_70_);
lean_inc(v_fst_69_);
v_isSharedCheck_188_ = !lean_is_exclusive(v_a_64_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; lean_object* v_unused_190_; 
v_unused_189_ = lean_ctor_get(v_a_64_, 1);
lean_dec(v_unused_189_);
v_unused_190_ = lean_ctor_get(v_a_64_, 0);
lean_dec(v_unused_190_);
v___x_74_ = v_a_64_;
v_isShared_75_ = v_isSharedCheck_188_;
goto v_resetjp_73_;
}
else
{
lean_dec(v_a_64_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_188_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
uint32_t v_c_76_; lean_object* v___x_77_; lean_object* v_it_x27_79_; 
v_c_76_ = lean_string_utf8_get_fast(v_fst_69_, v_snd_70_);
v___x_77_ = lean_string_utf8_next_fast(v_fst_69_, v_snd_70_);
lean_dec(v_snd_70_);
lean_inc(v_fst_69_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 1, v___x_77_);
v_it_x27_79_ = v___x_74_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_fst_69_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_77_);
v_it_x27_79_ = v_reuseFailAlloc_187_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
uint32_t v___x_80_; uint8_t v___x_81_; 
v___x_80_ = 92;
v___x_81_ = lean_uint32_dec_eq(v_c_76_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_fst_69_);
v___x_82_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_83_, 0, v_it_x27_79_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
return v___x_83_;
}
else
{
uint8_t v___x_84_; 
v___x_84_ = lean_nat_dec_eq(v___x_77_, v___x_71_);
if (v___x_84_ == 0)
{
uint32_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint32_t v___x_88_; uint8_t v___x_89_; 
lean_dec_ref(v_it_x27_79_);
v___x_85_ = lean_string_utf8_get_fast(v_fst_69_, v___x_77_);
v___x_86_ = lean_string_utf8_next_fast(v_fst_69_, v___x_77_);
lean_inc(v_fst_69_);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v_fst_69_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = 117;
v___x_89_ = lean_uint32_dec_eq(v___x_85_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec(v_fst_69_);
v___x_90_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_91_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_87_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = lean_nat_dec_eq(v___x_86_, v___x_71_);
if (v___x_92_ == 0)
{
uint32_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint32_t v___x_177_; uint8_t v___x_178_; 
lean_dec_ref(v___x_87_);
v___x_93_ = lean_string_utf8_get_fast(v_fst_69_, v___x_86_);
v___x_94_ = lean_string_utf8_next_fast(v_fst_69_, v___x_86_);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v_fst_69_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_177_ = 100;
v___x_178_ = lean_uint32_dec_eq(v___x_93_, v___x_177_);
if (v___x_178_ == 0)
{
uint32_t v___x_179_; uint8_t v___x_180_; 
v___x_179_ = 68;
v___x_180_ = lean_uint32_dec_eq(v___x_93_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_95_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
return v___x_182_;
}
else
{
goto v___jp_96_;
}
}
else
{
goto v___jp_96_;
}
v___jp_96_:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Json_Parser_hexChar(v___x_95_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_pos_98_; lean_object* v_res_99_; lean_object* v___x_100_; 
v_pos_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_pos_98_);
v_res_99_ = lean_ctor_get(v___x_97_, 1);
lean_inc(v_res_99_);
lean_dec_ref(v___x_97_);
v___x_100_ = l_Lean_Json_Parser_hexChar(v_pos_98_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_pos_101_; lean_object* v_res_102_; lean_object* v___x_103_; 
v_pos_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_pos_101_);
v_res_102_ = lean_ctor_get(v___x_100_, 1);
lean_inc(v_res_102_);
lean_dec_ref(v___x_100_);
v___x_103_ = l_Lean_Json_Parser_hexChar(v_pos_101_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_pos_104_; lean_object* v_res_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_149_; 
v_pos_104_ = lean_ctor_get(v___x_103_, 0);
v_res_105_ = lean_ctor_get(v___x_103_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_149_ == 0)
{
v___x_107_ = v___x_103_;
v_isShared_108_ = v_isSharedCheck_149_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_res_105_);
lean_inc(v_pos_104_);
lean_dec(v___x_103_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_149_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
uint16_t v___x_109_; uint16_t v___x_110_; uint16_t v___x_111_; uint16_t v___x_112_; uint16_t v___x_113_; uint16_t v___x_114_; uint16_t v___x_115_; uint16_t v___x_116_; uint16_t v___x_117_; uint16_t v___x_118_; uint8_t v___x_119_; 
v___x_109_ = 8;
v___x_110_ = lean_unbox(v_res_99_);
lean_dec(v_res_99_);
v___x_111_ = lean_uint16_shift_left(v___x_110_, v___x_109_);
v___x_112_ = 4;
v___x_113_ = lean_unbox(v_res_102_);
lean_dec(v_res_102_);
v___x_114_ = lean_uint16_shift_left(v___x_113_, v___x_112_);
v___x_115_ = lean_uint16_lor(v___x_111_, v___x_114_);
v___x_116_ = lean_unbox(v_res_105_);
lean_dec(v_res_105_);
v___x_117_ = lean_uint16_lor(v___x_115_, v___x_116_);
v___x_118_ = 3072;
v___x_119_ = lean_uint16_dec_lt(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
uint32_t v___x_120_; uint32_t v___x_121_; uint32_t v___x_122_; uint32_t v___x_123_; uint32_t v___x_124_; uint32_t v___x_125_; uint32_t v___x_126_; uint32_t v___x_127_; uint32_t v___x_128_; uint32_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_120_ = lean_uint16_to_uint32(v_low_63_);
v___x_121_ = 1023;
v___x_122_ = lean_uint32_land(v___x_120_, v___x_121_);
v___x_123_ = 10;
v___x_124_ = lean_uint32_shift_left(v___x_122_, v___x_123_);
v___x_125_ = lean_uint16_to_uint32(v___x_117_);
v___x_126_ = lean_uint32_land(v___x_125_, v___x_121_);
v___x_127_ = lean_uint32_lor(v___x_124_, v___x_126_);
v___x_128_ = 65536;
v___x_129_ = lean_uint32_add(v___x_127_, v___x_128_);
v___x_130_ = lean_uint32_to_nat(v___x_129_);
v___x_131_ = lean_unsigned_to_nat(55296u);
v___x_132_ = lean_nat_dec_lt(v___x_130_, v___x_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(57343u);
v___x_134_ = lean_nat_dec_lt(v___x_133_, v___x_130_);
if (v___x_134_ == 0)
{
lean_dec(v___x_130_);
lean_del_object(v___x_107_);
v___y_66_ = v_pos_104_;
goto v___jp_65_;
}
else
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(1114112u);
v___x_136_ = lean_nat_dec_lt(v___x_130_, v___x_135_);
lean_dec(v___x_130_);
if (v___x_136_ == 0)
{
lean_del_object(v___x_107_);
v___y_66_ = v_pos_104_;
goto v___jp_65_;
}
else
{
lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_137_ = lean_box_uint32(v___x_129_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v___x_137_);
v___x_139_ = v___x_107_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_pos_104_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
else
{
lean_object* v___x_141_; lean_object* v___x_143_; 
lean_dec(v___x_130_);
v___x_141_ = lean_box_uint32(v___x_129_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v___x_141_);
v___x_143_ = v___x_107_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_pos_104_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
else
{
lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_145_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
if (v_isShared_108_ == 0)
{
lean_ctor_set_tag(v___x_107_, 1);
lean_ctor_set(v___x_107_, 1, v___x_145_);
v___x_147_ = v___x_107_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_pos_104_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
else
{
lean_object* v_pos_150_; lean_object* v_err_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_dec(v_res_102_);
lean_dec(v_res_99_);
v_pos_150_ = lean_ctor_get(v___x_103_, 0);
v_err_151_ = lean_ctor_get(v___x_103_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_103_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_err_151_);
lean_inc(v_pos_150_);
lean_dec(v___x_103_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_pos_150_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_err_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
else
{
lean_object* v_pos_159_; lean_object* v_err_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
lean_dec(v_res_99_);
v_pos_159_ = lean_ctor_get(v___x_100_, 0);
v_err_160_ = lean_ctor_get(v___x_100_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_100_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_err_160_);
lean_inc(v_pos_159_);
lean_dec(v___x_100_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_pos_159_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_err_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
else
{
lean_object* v_pos_168_; lean_object* v_err_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
v_pos_168_ = lean_ctor_get(v___x_97_, 0);
v_err_169_ = lean_ctor_get(v___x_97_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_97_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_err_169_);
lean_inc(v_pos_168_);
lean_dec(v___x_97_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_pos_168_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_err_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_fst_69_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_87_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
return v___x_184_;
}
}
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v_fst_69_);
v___x_185_ = lean_box(0);
v___x_186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_186_, 0, v_it_x27_79_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
return v___x_186_;
}
}
}
}
}
else
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_box(0);
v___x_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_192_, 0, v_a_64_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
return v___x_192_;
}
v___jp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_68_, 0, v___y_66_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair___boxed(lean_object* v_low_193_, lean_object* v_a_194_){
_start:
{
uint16_t v_low_boxed_195_; lean_object* v_res_196_; 
v_low_boxed_195_ = lean_unbox(v_low_193_);
v_res_196_ = l_Lean_Json_Parser_finishSurrogatePair(v_low_boxed_195_, v_a_194_);
return v_res_196_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_200_; lean_object* v___x_201_; 
v___x_200_ = 65533;
v___x_201_ = lean_box_uint32(v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_202_; lean_object* v___x_203_; 
v___x_202_ = 9;
v___x_203_ = lean_box_uint32(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_204_; lean_object* v___x_205_; 
v___x_204_ = 13;
v___x_205_ = lean_box_uint32(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_206_; lean_object* v___x_207_; 
v___x_206_ = 10;
v___x_207_ = lean_box_uint32(v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_208_; lean_object* v___x_209_; 
v___x_208_ = 12;
v___x_209_ = lean_box_uint32(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_210_; lean_object* v___x_211_; 
v___x_210_ = 8;
v___x_211_ = lean_box_uint32(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__7(void){
_start:
{
uint32_t v___x_212_; lean_object* v___x_213_; 
v___x_212_ = 47;
v___x_213_ = lean_box_uint32(v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__8(void){
_start:
{
uint32_t v___x_214_; lean_object* v___x_215_; 
v___x_214_ = 34;
v___x_215_ = lean_box_uint32(v___x_214_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__9(void){
_start:
{
uint32_t v___x_216_; lean_object* v___x_217_; 
v___x_216_ = 92;
v___x_217_ = lean_box_uint32(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar(lean_object* v_a_218_){
_start:
{
lean_object* v_fst_219_; lean_object* v_snd_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v_fst_219_ = lean_ctor_get(v_a_218_, 0);
v_snd_220_ = lean_ctor_get(v_a_218_, 1);
v___x_221_ = lean_string_utf8_byte_size(v_fst_219_);
v___x_222_ = lean_nat_dec_eq(v_snd_220_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_377_; 
lean_inc(v_snd_220_);
lean_inc(v_fst_219_);
v_isSharedCheck_377_ = !lean_is_exclusive(v_a_218_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; lean_object* v_unused_379_; 
v_unused_378_ = lean_ctor_get(v_a_218_, 1);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v_a_218_, 0);
lean_dec(v_unused_379_);
v___x_224_ = v_a_218_;
v_isShared_225_ = v_isSharedCheck_377_;
goto v_resetjp_223_;
}
else
{
lean_dec(v_a_218_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_377_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
uint32_t v_c_226_; lean_object* v___x_227_; lean_object* v_it_x27_229_; 
v_c_226_ = lean_string_utf8_get_fast(v_fst_219_, v_snd_220_);
v___x_227_ = lean_string_utf8_next_fast(v_fst_219_, v_snd_220_);
lean_dec(v_snd_220_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v___x_227_);
v_it_x27_229_ = v___x_224_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_fst_219_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_227_);
v_it_x27_229_ = v_reuseFailAlloc_376_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
uint32_t v___x_230_; uint8_t v___x_231_; 
v___x_230_ = 92;
v___x_231_ = lean_uint32_dec_eq(v_c_226_, v___x_230_);
if (v___x_231_ == 0)
{
uint32_t v___x_232_; uint8_t v___x_233_; 
v___x_232_ = 34;
v___x_233_ = lean_uint32_dec_eq(v_c_226_, v___x_232_);
if (v___x_233_ == 0)
{
uint32_t v___x_234_; uint8_t v___x_235_; 
v___x_234_ = 47;
v___x_235_ = lean_uint32_dec_eq(v_c_226_, v___x_234_);
if (v___x_235_ == 0)
{
uint32_t v___x_236_; uint8_t v___x_237_; 
v___x_236_ = 98;
v___x_237_ = lean_uint32_dec_eq(v_c_226_, v___x_236_);
if (v___x_237_ == 0)
{
uint32_t v___x_238_; uint8_t v___x_239_; 
v___x_238_ = 102;
v___x_239_ = lean_uint32_dec_eq(v_c_226_, v___x_238_);
if (v___x_239_ == 0)
{
uint32_t v___x_240_; uint8_t v___x_241_; 
v___x_240_ = 110;
v___x_241_ = lean_uint32_dec_eq(v_c_226_, v___x_240_);
if (v___x_241_ == 0)
{
uint32_t v___x_242_; uint8_t v___x_243_; 
v___x_242_ = 114;
v___x_243_ = lean_uint32_dec_eq(v_c_226_, v___x_242_);
if (v___x_243_ == 0)
{
uint32_t v___x_244_; uint8_t v___x_245_; 
v___x_244_ = 116;
v___x_245_ = lean_uint32_dec_eq(v_c_226_, v___x_244_);
if (v___x_245_ == 0)
{
uint32_t v___x_246_; uint8_t v___x_247_; 
v___x_246_ = 117;
v___x_247_ = lean_uint32_dec_eq(v_c_226_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l_Lean_Json_Parser_escapedChar___closed__1));
v___x_249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_249_, 0, v_it_x27_229_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
return v___x_249_;
}
else
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_Json_Parser_hexChar(v_it_x27_229_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_pos_251_; lean_object* v_res_252_; lean_object* v___x_253_; 
v_pos_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_pos_251_);
v_res_252_ = lean_ctor_get(v___x_250_, 1);
lean_inc(v_res_252_);
lean_dec_ref(v___x_250_);
v___x_253_ = l_Lean_Json_Parser_hexChar(v_pos_251_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_pos_254_; lean_object* v_res_255_; lean_object* v___x_256_; 
v_pos_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_pos_254_);
v_res_255_ = lean_ctor_get(v___x_253_, 1);
lean_inc(v_res_255_);
lean_dec_ref(v___x_253_);
v___x_256_ = l_Lean_Json_Parser_hexChar(v_pos_254_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_pos_257_; lean_object* v_res_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_332_; 
v_pos_257_ = lean_ctor_get(v___x_256_, 0);
v_res_258_ = lean_ctor_get(v___x_256_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_332_ == 0)
{
v___x_260_ = v___x_256_;
v_isShared_261_ = v_isSharedCheck_332_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_res_258_);
lean_inc(v_pos_257_);
lean_dec(v___x_256_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_332_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Json_Parser_hexChar(v_pos_257_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_pos_263_; lean_object* v_res_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_322_; 
v_pos_263_ = lean_ctor_get(v___x_262_, 0);
v_res_264_ = lean_ctor_get(v___x_262_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_322_ == 0)
{
v___x_266_ = v___x_262_;
v_isShared_267_ = v_isSharedCheck_322_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_res_264_);
lean_inc(v_pos_263_);
lean_dec(v___x_262_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_322_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___y_269_; lean_object* v_pos_270_; uint16_t v___x_278_; uint16_t v___x_279_; uint16_t v___x_280_; uint16_t v___x_281_; uint16_t v___x_282_; uint16_t v___x_283_; uint16_t v___x_284_; uint16_t v___x_285_; uint16_t v___x_286_; uint16_t v___x_287_; uint16_t v___x_288_; uint16_t v___x_289_; uint16_t v___x_290_; uint16_t v___x_291_; uint8_t v___x_292_; 
v___x_278_ = 12;
v___x_279_ = lean_unbox(v_res_252_);
lean_dec(v_res_252_);
v___x_280_ = lean_uint16_shift_left(v___x_279_, v___x_278_);
v___x_281_ = 8;
v___x_282_ = lean_unbox(v_res_255_);
lean_dec(v_res_255_);
v___x_283_ = lean_uint16_shift_left(v___x_282_, v___x_281_);
v___x_284_ = lean_uint16_lor(v___x_280_, v___x_283_);
v___x_285_ = 4;
v___x_286_ = lean_unbox(v_res_258_);
lean_dec(v_res_258_);
v___x_287_ = lean_uint16_shift_left(v___x_286_, v___x_285_);
v___x_288_ = lean_uint16_lor(v___x_284_, v___x_287_);
v___x_289_ = lean_unbox(v_res_264_);
lean_dec(v_res_264_);
v___x_290_ = lean_uint16_lor(v___x_288_, v___x_289_);
v___x_291_ = 55296;
v___x_292_ = lean_uint16_dec_lt(v___x_290_, v___x_291_);
if (v___x_292_ == 0)
{
uint16_t v___x_293_; uint8_t v___x_294_; 
v___x_293_ = 57344;
v___x_294_ = lean_uint16_dec_lt(v___x_290_, v___x_293_);
if (v___x_294_ == 0)
{
uint32_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
lean_del_object(v___x_266_);
v___x_295_ = lean_uint16_to_uint32(v___x_290_);
v___x_296_ = lean_box_uint32(v___x_295_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 1, v___x_296_);
lean_ctor_set(v___x_260_, 0, v_pos_263_);
v___x_298_ = v___x_260_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_pos_263_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
else
{
uint16_t v___x_300_; uint8_t v___x_301_; 
v___x_300_ = 56320;
v___x_301_ = lean_uint16_dec_lt(v___x_290_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_304_; 
lean_del_object(v___x_266_);
v___x_302_ = l_Lean_Json_Parser_escapedChar___boxed__const__1;
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 1, v___x_302_);
lean_ctor_set(v___x_260_, 0, v_pos_263_);
v___x_304_ = v___x_260_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_pos_263_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
else
{
lean_object* v___x_306_; 
lean_del_object(v___x_260_);
lean_inc(v_pos_263_);
v___x_306_ = l_Lean_Json_Parser_finishSurrogatePair(v___x_290_, v_pos_263_);
if (lean_obj_tag(v___x_306_) == 0)
{
if (lean_obj_tag(v___x_306_) == 0)
{
lean_del_object(v___x_266_);
lean_dec(v_pos_263_);
return v___x_306_;
}
else
{
lean_object* v_pos_307_; 
v_pos_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_pos_307_);
v___y_269_ = v___x_306_;
v_pos_270_ = v_pos_307_;
goto v___jp_268_;
}
}
else
{
lean_object* v_err_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
v_err_308_ = lean_ctor_get(v___x_306_, 1);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_315_ == 0)
{
lean_object* v_unused_316_; 
v_unused_316_ = lean_ctor_get(v___x_306_, 0);
lean_dec(v_unused_316_);
v___x_310_ = v___x_306_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_err_308_);
lean_dec(v___x_306_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
lean_inc(v_pos_263_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v_pos_263_);
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_pos_263_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_err_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_inc(v_pos_263_);
v___y_269_ = v___x_313_;
v_pos_270_ = v_pos_263_;
goto v___jp_268_;
}
}
}
}
}
}
else
{
uint32_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
lean_del_object(v___x_266_);
v___x_317_ = lean_uint16_to_uint32(v___x_290_);
v___x_318_ = lean_box_uint32(v___x_317_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 1, v___x_318_);
lean_ctor_set(v___x_260_, 0, v_pos_263_);
v___x_320_ = v___x_260_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_pos_263_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
v___jp_268_:
{
lean_object* v_snd_271_; lean_object* v_snd_272_; uint8_t v___x_273_; 
v_snd_271_ = lean_ctor_get(v_pos_263_, 1);
lean_inc(v_snd_271_);
lean_dec(v_pos_263_);
v_snd_272_ = lean_ctor_get(v_pos_270_, 1);
v___x_273_ = lean_nat_dec_eq(v_snd_271_, v_snd_272_);
lean_dec(v_snd_271_);
if (v___x_273_ == 0)
{
lean_dec_ref(v_pos_270_);
lean_del_object(v___x_266_);
return v___y_269_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_276_; 
lean_dec_ref(v___y_269_);
v___x_274_ = l_Lean_Json_Parser_escapedChar___boxed__const__1;
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 1, v___x_274_);
lean_ctor_set(v___x_266_, 0, v_pos_270_);
v___x_276_ = v___x_266_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_pos_270_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
else
{
lean_object* v_pos_323_; lean_object* v_err_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_del_object(v___x_260_);
lean_dec(v_res_258_);
lean_dec(v_res_255_);
lean_dec(v_res_252_);
v_pos_323_ = lean_ctor_get(v___x_262_, 0);
v_err_324_ = lean_ctor_get(v___x_262_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_262_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_err_324_);
lean_inc(v_pos_323_);
lean_dec(v___x_262_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_pos_323_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_err_324_);
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
}
else
{
lean_object* v_pos_333_; lean_object* v_err_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec(v_res_255_);
lean_dec(v_res_252_);
v_pos_333_ = lean_ctor_get(v___x_256_, 0);
v_err_334_ = lean_ctor_get(v___x_256_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_256_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_err_334_);
lean_inc(v_pos_333_);
lean_dec(v___x_256_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_pos_333_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_err_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
else
{
lean_object* v_pos_342_; lean_object* v_err_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec(v_res_252_);
v_pos_342_ = lean_ctor_get(v___x_253_, 0);
v_err_343_ = lean_ctor_get(v___x_253_, 1);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_253_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_err_343_);
lean_inc(v_pos_342_);
lean_dec(v___x_253_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_pos_342_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_err_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v_pos_351_; lean_object* v_err_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
v_pos_351_ = lean_ctor_get(v___x_250_, 0);
v_err_352_ = lean_ctor_get(v___x_250_, 1);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_250_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_err_352_);
lean_inc(v_pos_351_);
lean_dec(v___x_250_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_pos_351_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_err_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = l_Lean_Json_Parser_escapedChar___boxed__const__2;
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_it_x27_229_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
return v___x_361_;
}
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = l_Lean_Json_Parser_escapedChar___boxed__const__3;
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_it_x27_229_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
return v___x_363_;
}
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = l_Lean_Json_Parser_escapedChar___boxed__const__4;
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_it_x27_229_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
return v___x_365_;
}
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = l_Lean_Json_Parser_escapedChar___boxed__const__5;
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v_it_x27_229_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
return v___x_367_;
}
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = l_Lean_Json_Parser_escapedChar___boxed__const__6;
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v_it_x27_229_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
return v___x_369_;
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = l_Lean_Json_Parser_escapedChar___boxed__const__7;
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v_it_x27_229_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
return v___x_371_;
}
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = l_Lean_Json_Parser_escapedChar___boxed__const__8;
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v_it_x27_229_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
return v___x_373_;
}
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = l_Lean_Json_Parser_escapedChar___boxed__const__9;
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v_it_x27_229_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
return v___x_375_;
}
}
}
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_box(0);
v___x_381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_381_, 0, v_a_218_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_strCore(lean_object* v_acc_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_fst_387_; lean_object* v_snd_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_fst_387_ = lean_ctor_get(v_a_386_, 0);
v_snd_388_ = lean_ctor_get(v_a_386_, 1);
v___x_389_ = lean_string_utf8_byte_size(v_fst_387_);
v___x_390_ = lean_nat_dec_eq(v_snd_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_433_; 
lean_inc(v_snd_388_);
lean_inc(v_fst_387_);
v_isSharedCheck_433_ = !lean_is_exclusive(v_a_386_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; lean_object* v_unused_435_; 
v_unused_434_ = lean_ctor_get(v_a_386_, 1);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_a_386_, 0);
lean_dec(v_unused_435_);
v___x_392_ = v_a_386_;
v_isShared_393_ = v_isSharedCheck_433_;
goto v_resetjp_391_;
}
else
{
lean_dec(v_a_386_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_433_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
uint32_t v___x_394_; uint32_t v___x_395_; uint8_t v___x_396_; 
v___x_394_ = lean_string_utf8_get_fast(v_fst_387_, v_snd_388_);
v___x_395_ = 34;
v___x_396_ = lean_uint32_dec_eq(v___x_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_string_utf8_next_fast(v_fst_387_, v_snd_388_);
lean_dec(v_snd_388_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v___x_397_);
v___x_399_ = v___x_392_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_fst_387_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v___x_397_);
v___x_399_ = v_reuseFailAlloc_427_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
uint8_t v___y_401_; uint32_t v___x_406_; uint8_t v___x_407_; 
v___x_406_ = 92;
v___x_407_ = lean_uint32_dec_eq(v___x_394_, v___x_406_);
if (v___x_407_ == 0)
{
uint32_t v___x_408_; uint8_t v___x_409_; 
v___x_408_ = 32;
v___x_409_ = lean_uint32_dec_le(v___x_408_, v___x_394_);
if (v___x_409_ == 0)
{
v___y_401_ = v___x_409_;
goto v___jp_400_;
}
else
{
uint32_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = 1114111;
v___x_411_ = lean_uint32_dec_le(v___x_394_, v___x_410_);
v___y_401_ = v___x_411_;
goto v___jp_400_;
}
}
else
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Json_Parser_escapedChar(v___x_399_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_pos_413_; lean_object* v_res_414_; uint32_t v___x_415_; lean_object* v___x_416_; 
v_pos_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_pos_413_);
v_res_414_ = lean_ctor_get(v___x_412_, 1);
lean_inc(v_res_414_);
lean_dec_ref(v___x_412_);
v___x_415_ = lean_unbox_uint32(v_res_414_);
lean_dec(v_res_414_);
v___x_416_ = lean_string_push(v_acc_385_, v___x_415_);
v_acc_385_ = v___x_416_;
v_a_386_ = v_pos_413_;
goto _start;
}
else
{
lean_object* v_pos_418_; lean_object* v_err_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec_ref(v_acc_385_);
v_pos_418_ = lean_ctor_get(v___x_412_, 0);
v_err_419_ = lean_ctor_get(v___x_412_, 1);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_412_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_err_419_);
lean_inc(v_pos_418_);
lean_dec(v___x_412_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_pos_418_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_err_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
v___jp_400_:
{
if (v___y_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec_ref(v_acc_385_);
v___x_402_ = ((lean_object*)(l_Lean_Json_Parser_strCore___closed__1));
v___x_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_399_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
return v___x_403_;
}
else
{
lean_object* v___x_404_; 
v___x_404_ = lean_string_push(v_acc_385_, v___x_394_);
v_acc_385_ = v___x_404_;
v_a_386_ = v___x_399_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_428_ = lean_string_utf8_next_fast(v_fst_387_, v_snd_388_);
lean_dec(v_snd_388_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v___x_428_);
v___x_430_ = v___x_392_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_fst_387_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v___x_428_);
v___x_430_ = v_reuseFailAlloc_432_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_431_; 
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v_acc_385_);
return v___x_431_;
}
}
}
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec_ref(v_acc_385_);
v___x_436_ = lean_box(0);
v___x_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_437_, 0, v_a_386_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_str(lean_object* v_a_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_440_ = l_Lean_Json_Parser_strCore(v___x_439_, v_a_438_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCore(lean_object* v_acc_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_fst_443_; lean_object* v_snd_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v_fst_443_ = lean_ctor_get(v_a_442_, 0);
v_snd_444_ = lean_ctor_get(v_a_442_, 1);
v___x_445_ = lean_string_utf8_byte_size(v_fst_443_);
v___x_446_ = lean_nat_dec_eq(v_snd_444_, v___x_445_);
if (v___x_446_ == 0)
{
uint32_t v___x_447_; uint32_t v___x_448_; uint8_t v___y_450_; uint8_t v___x_468_; 
v___x_447_ = lean_string_utf8_get_fast(v_fst_443_, v_snd_444_);
v___x_448_ = 48;
v___x_468_ = lean_uint32_dec_le(v___x_448_, v___x_447_);
if (v___x_468_ == 0)
{
v___y_450_ = v___x_468_;
goto v___jp_449_;
}
else
{
uint32_t v___x_469_; uint8_t v___x_470_; 
v___x_469_ = 57;
v___x_470_ = lean_uint32_dec_le(v___x_447_, v___x_469_);
v___y_450_ = v___x_470_;
goto v___jp_449_;
}
v___jp_449_:
{
if (v___y_450_ == 0)
{
lean_object* v___x_451_; 
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v_a_442_);
lean_ctor_set(v___x_451_, 1, v_acc_441_);
return v___x_451_;
}
else
{
lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_465_; 
lean_inc(v_snd_444_);
lean_inc(v_fst_443_);
v_isSharedCheck_465_ = !lean_is_exclusive(v_a_442_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; lean_object* v_unused_467_; 
v_unused_466_ = lean_ctor_get(v_a_442_, 1);
lean_dec(v_unused_466_);
v_unused_467_ = lean_ctor_get(v_a_442_, 0);
lean_dec(v_unused_467_);
v___x_453_ = v_a_442_;
v_isShared_454_ = v_isSharedCheck_465_;
goto v_resetjp_452_;
}
else
{
lean_dec(v_a_442_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_465_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_455_ = lean_string_utf8_next_fast(v_fst_443_, v_snd_444_);
lean_dec(v_snd_444_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 1, v___x_455_);
v___x_457_ = v___x_453_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_fst_443_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___x_455_);
v___x_457_ = v_reuseFailAlloc_464_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; uint32_t v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_458_ = lean_unsigned_to_nat(10u);
v___x_459_ = lean_nat_mul(v___x_458_, v_acc_441_);
lean_dec(v_acc_441_);
v___x_460_ = lean_uint32_sub(v___x_447_, v___x_448_);
v___x_461_ = lean_uint32_to_nat(v___x_460_);
v___x_462_ = lean_nat_add(v___x_459_, v___x_461_);
lean_dec(v___x_461_);
lean_dec(v___x_459_);
v_acc_441_ = v___x_462_;
v_a_442_ = v___x_457_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_471_; 
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v_a_442_);
lean_ctor_set(v___x_471_, 1, v_acc_441_);
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCoreNumDigits(lean_object* v_acc_472_, lean_object* v_digits_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_fst_475_; lean_object* v_snd_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v_fst_475_ = lean_ctor_get(v_a_474_, 0);
v_snd_476_ = lean_ctor_get(v_a_474_, 1);
v___x_477_ = lean_string_utf8_byte_size(v_fst_475_);
v___x_478_ = lean_nat_dec_eq(v_snd_476_, v___x_477_);
if (v___x_478_ == 0)
{
uint32_t v___x_479_; uint32_t v___x_480_; uint8_t v___y_482_; uint8_t v___x_503_; 
v___x_479_ = lean_string_utf8_get_fast(v_fst_475_, v_snd_476_);
v___x_480_ = 48;
v___x_503_ = lean_uint32_dec_le(v___x_480_, v___x_479_);
if (v___x_503_ == 0)
{
v___y_482_ = v___x_503_;
goto v___jp_481_;
}
else
{
uint32_t v___x_504_; uint8_t v___x_505_; 
v___x_504_ = 57;
v___x_505_ = lean_uint32_dec_le(v___x_479_, v___x_504_);
v___y_482_ = v___x_505_;
goto v___jp_481_;
}
v___jp_481_:
{
if (v___y_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v_acc_472_);
lean_ctor_set(v___x_483_, 1, v_digits_473_);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v_a_474_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
return v___x_484_;
}
else
{
lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_500_; 
lean_inc(v_snd_476_);
lean_inc(v_fst_475_);
v_isSharedCheck_500_ = !lean_is_exclusive(v_a_474_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; lean_object* v_unused_502_; 
v_unused_501_ = lean_ctor_get(v_a_474_, 1);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v_a_474_, 0);
lean_dec(v_unused_502_);
v___x_486_ = v_a_474_;
v_isShared_487_ = v_isSharedCheck_500_;
goto v_resetjp_485_;
}
else
{
lean_dec(v_a_474_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_500_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_488_ = lean_string_utf8_next_fast(v_fst_475_, v_snd_476_);
lean_dec(v_snd_476_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v___x_488_);
v___x_490_ = v___x_486_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_fst_475_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_488_);
v___x_490_ = v_reuseFailAlloc_499_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; uint32_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_491_ = lean_unsigned_to_nat(10u);
v___x_492_ = lean_nat_mul(v___x_491_, v_acc_472_);
lean_dec(v_acc_472_);
v___x_493_ = lean_uint32_sub(v___x_479_, v___x_480_);
v___x_494_ = lean_uint32_to_nat(v___x_493_);
v___x_495_ = lean_nat_add(v___x_492_, v___x_494_);
lean_dec(v___x_494_);
lean_dec(v___x_492_);
v___x_496_ = lean_unsigned_to_nat(1u);
v___x_497_ = lean_nat_add(v_digits_473_, v___x_496_);
lean_dec(v_digits_473_);
v_acc_472_ = v___x_495_;
v_digits_473_ = v___x_497_;
v_a_474_ = v___x_490_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v_acc_472_);
lean_ctor_set(v___x_506_, 1, v_digits_473_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v_a_474_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg(lean_object* v_desc_509_, lean_object* v_inst_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_fst_512_; lean_object* v_snd_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_fst_512_ = lean_ctor_get(v_a_511_, 0);
v_snd_513_ = lean_ctor_get(v_a_511_, 1);
v___x_514_ = lean_string_utf8_byte_size(v_fst_512_);
v___x_515_ = lean_nat_dec_eq(v_snd_513_, v___x_514_);
if (v___x_515_ == 0)
{
uint32_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_516_ = lean_string_utf8_get_fast(v_fst_512_, v_snd_513_);
v___x_517_ = lean_box_uint32(v___x_516_);
v___x_518_ = lean_apply_1(v_inst_510_, v___x_517_);
v___x_519_ = lean_unbox(v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_520_ = ((lean_object*)(l_Lean_Json_Parser_lookahead___redArg___closed__0));
v___x_521_ = lean_string_append(v___x_520_, v_desc_509_);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
v___x_523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_523_, 0, v_a_511_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
return v___x_523_;
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_box(0);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v_a_511_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
return v___x_525_;
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec_ref(v_inst_510_);
v___x_526_ = lean_box(0);
v___x_527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_527_, 0, v_a_511_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg___boxed(lean_object* v_desc_528_, lean_object* v_inst_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Json_Parser_lookahead___redArg(v_desc_528_, v_inst_529_, v_a_530_);
lean_dec_ref(v_desc_528_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead(lean_object* v_p_532_, lean_object* v_desc_533_, lean_object* v_inst_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_fst_536_; lean_object* v_snd_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_fst_536_ = lean_ctor_get(v_a_535_, 0);
v_snd_537_ = lean_ctor_get(v_a_535_, 1);
v___x_538_ = lean_string_utf8_byte_size(v_fst_536_);
v___x_539_ = lean_nat_dec_eq(v_snd_537_, v___x_538_);
if (v___x_539_ == 0)
{
uint32_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_540_ = lean_string_utf8_get_fast(v_fst_536_, v_snd_537_);
v___x_541_ = lean_box_uint32(v___x_540_);
v___x_542_ = lean_apply_1(v_inst_534_, v___x_541_);
v___x_543_ = lean_unbox(v___x_542_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_544_ = ((lean_object*)(l_Lean_Json_Parser_lookahead___redArg___closed__0));
v___x_545_ = lean_string_append(v___x_544_, v_desc_533_);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
v___x_547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_547_, 0, v_a_535_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
return v___x_547_;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_box(0);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v_a_535_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
return v___x_549_;
}
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec_ref(v_inst_534_);
v___x_550_ = lean_box(0);
v___x_551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_551_, 0, v_a_535_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___boxed(lean_object* v_p_552_, lean_object* v_desc_553_, lean_object* v_inst_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Json_Parser_lookahead(v_p_552_, v_desc_553_, v_inst_554_, v_a_555_);
lean_dec_ref(v_desc_553_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNonZero(lean_object* v_a_560_){
_start:
{
uint8_t v___y_562_; lean_object* v_fst_567_; lean_object* v_snd_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_fst_567_ = lean_ctor_get(v_a_560_, 0);
v_snd_568_ = lean_ctor_get(v_a_560_, 1);
v___x_569_ = lean_string_utf8_byte_size(v_fst_567_);
v___x_570_ = lean_nat_dec_eq(v_snd_568_, v___x_569_);
if (v___x_570_ == 0)
{
uint32_t v___x_571_; uint32_t v___x_572_; uint8_t v___x_573_; 
v___x_571_ = lean_string_utf8_get_fast(v_fst_567_, v_snd_568_);
v___x_572_ = 49;
v___x_573_ = lean_uint32_dec_le(v___x_572_, v___x_571_);
if (v___x_573_ == 0)
{
v___y_562_ = v___x_573_;
goto v___jp_561_;
}
else
{
uint32_t v___x_574_; uint8_t v___x_575_; 
v___x_574_ = 57;
v___x_575_ = lean_uint32_dec_le(v___x_571_, v___x_574_);
v___y_562_ = v___x_575_;
goto v___jp_561_;
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_box(0);
v___x_577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_577_, 0, v_a_560_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
return v___x_577_;
}
v___jp_561_:
{
if (v___y_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_564_, 0, v_a_560_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
return v___x_564_;
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = l_Lean_Json_Parser_natCore(v___x_565_, v_a_560_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNumDigits(lean_object* v_a_581_){
_start:
{
uint8_t v___y_583_; lean_object* v_fst_588_; lean_object* v_snd_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v_fst_588_ = lean_ctor_get(v_a_581_, 0);
v_snd_589_ = lean_ctor_get(v_a_581_, 1);
v___x_590_ = lean_string_utf8_byte_size(v_fst_588_);
v___x_591_ = lean_nat_dec_eq(v_snd_589_, v___x_590_);
if (v___x_591_ == 0)
{
uint32_t v___x_592_; uint32_t v___x_593_; uint8_t v___x_594_; 
v___x_592_ = lean_string_utf8_get_fast(v_fst_588_, v_snd_589_);
v___x_593_ = 48;
v___x_594_ = lean_uint32_dec_le(v___x_593_, v___x_592_);
if (v___x_594_ == 0)
{
v___y_583_ = v___x_594_;
goto v___jp_582_;
}
else
{
uint32_t v___x_595_; uint8_t v___x_596_; 
v___x_595_ = 57;
v___x_596_ = lean_uint32_dec_le(v___x_592_, v___x_595_);
v___y_583_ = v___x_596_;
goto v___jp_582_;
}
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_box(0);
v___x_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_598_, 0, v_a_581_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
return v___x_598_;
}
v___jp_582_:
{
if (v___y_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_585_, 0, v_a_581_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
return v___x_585_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_586_, v___x_586_, v_a_581_);
return v___x_587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natMaybeZero(lean_object* v_a_602_){
_start:
{
uint8_t v___y_604_; lean_object* v_fst_609_; lean_object* v_snd_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v_fst_609_ = lean_ctor_get(v_a_602_, 0);
v_snd_610_ = lean_ctor_get(v_a_602_, 1);
v___x_611_ = lean_string_utf8_byte_size(v_fst_609_);
v___x_612_ = lean_nat_dec_eq(v_snd_610_, v___x_611_);
if (v___x_612_ == 0)
{
uint32_t v___x_613_; uint32_t v___x_614_; uint8_t v___x_615_; 
v___x_613_ = lean_string_utf8_get_fast(v_fst_609_, v_snd_610_);
v___x_614_ = 48;
v___x_615_ = lean_uint32_dec_le(v___x_614_, v___x_613_);
if (v___x_615_ == 0)
{
v___y_604_ = v___x_615_;
goto v___jp_603_;
}
else
{
uint32_t v___x_616_; uint8_t v___x_617_; 
v___x_616_ = 57;
v___x_617_ = lean_uint32_dec_le(v___x_613_, v___x_616_);
v___y_604_ = v___x_617_;
goto v___jp_603_;
}
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_box(0);
v___x_619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_619_, 0, v_a_602_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
return v___x_619_;
}
v___jp_603_:
{
if (v___y_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_606_, 0, v_a_602_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = l_Lean_Json_Parser_natCore(v___x_607_, v_a_602_);
return v___x_608_;
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_numSign___closed__0(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_nat_to_int(v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Json_Parser_numSign___closed__1(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v___x_623_ = lean_int_neg(v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numSign(lean_object* v_a_624_){
_start:
{
lean_object* v_fst_625_; lean_object* v_snd_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v_fst_625_ = lean_ctor_get(v_a_624_, 0);
v_snd_626_ = lean_ctor_get(v_a_624_, 1);
v___x_627_ = lean_string_utf8_byte_size(v_fst_625_);
v___x_628_ = lean_nat_dec_eq(v_snd_626_, v___x_627_);
if (v___x_628_ == 0)
{
uint32_t v___x_629_; uint32_t v___x_630_; uint8_t v___x_631_; 
v___x_629_ = lean_string_utf8_get_fast(v_fst_625_, v_snd_626_);
v___x_630_ = 45;
v___x_631_ = lean_uint32_dec_eq(v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v_a_624_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
return v___x_633_;
}
else
{
lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_643_; 
lean_inc(v_snd_626_);
lean_inc(v_fst_625_);
v_isSharedCheck_643_ = !lean_is_exclusive(v_a_624_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; lean_object* v_unused_645_; 
v_unused_644_ = lean_ctor_get(v_a_624_, 1);
lean_dec(v_unused_644_);
v_unused_645_ = lean_ctor_get(v_a_624_, 0);
lean_dec(v_unused_645_);
v___x_635_ = v_a_624_;
v_isShared_636_ = v_isSharedCheck_643_;
goto v_resetjp_634_;
}
else
{
lean_dec(v_a_624_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_643_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = lean_string_utf8_next_fast(v_fst_625_, v_snd_626_);
lean_dec(v_snd_626_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v___x_637_);
v___x_639_ = v___x_635_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_fst_625_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v___x_637_);
v___x_639_ = v_reuseFailAlloc_642_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
return v___x_641_;
}
}
}
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_box(0);
v___x_647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_647_, 0, v_a_624_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_nat(lean_object* v_a_648_){
_start:
{
uint8_t v___y_650_; lean_object* v_fst_655_; lean_object* v_snd_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_fst_655_ = lean_ctor_get(v_a_648_, 0);
v_snd_656_ = lean_ctor_get(v_a_648_, 1);
v___x_657_ = lean_string_utf8_byte_size(v_fst_655_);
v___x_658_ = lean_nat_dec_eq(v_snd_656_, v___x_657_);
if (v___x_658_ == 0)
{
uint32_t v___x_659_; uint32_t v___x_660_; uint8_t v___x_661_; 
v___x_659_ = lean_string_utf8_get_fast(v_fst_655_, v_snd_656_);
v___x_660_ = 48;
v___x_661_ = lean_uint32_dec_eq(v___x_659_, v___x_660_);
if (v___x_661_ == 0)
{
uint32_t v___x_662_; uint8_t v___x_663_; 
v___x_662_ = 49;
v___x_663_ = lean_uint32_dec_le(v___x_662_, v___x_659_);
if (v___x_663_ == 0)
{
v___y_650_ = v___x_663_;
goto v___jp_649_;
}
else
{
uint32_t v___x_664_; uint8_t v___x_665_; 
v___x_664_ = 57;
v___x_665_ = lean_uint32_dec_le(v___x_659_, v___x_664_);
v___y_650_ = v___x_665_;
goto v___jp_649_;
}
}
else
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_675_; 
lean_inc(v_snd_656_);
lean_inc(v_fst_655_);
v_isSharedCheck_675_ = !lean_is_exclusive(v_a_648_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; lean_object* v_unused_677_; 
v_unused_676_ = lean_ctor_get(v_a_648_, 1);
lean_dec(v_unused_676_);
v_unused_677_ = lean_ctor_get(v_a_648_, 0);
lean_dec(v_unused_677_);
v___x_667_ = v_a_648_;
v_isShared_668_ = v_isSharedCheck_675_;
goto v_resetjp_666_;
}
else
{
lean_dec(v_a_648_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_675_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = lean_string_utf8_next_fast(v_fst_655_, v_snd_656_);
lean_dec(v_snd_656_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_669_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_fst_655_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v___x_669_);
v___x_671_ = v_reuseFailAlloc_674_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_unsigned_to_nat(0u);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
return v___x_673_;
}
}
}
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_box(0);
v___x_679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_679_, 0, v_a_648_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
return v___x_679_;
}
v___jp_649_:
{
if (v___y_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_652_, 0, v_a_648_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
return v___x_652_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = l_Lean_Json_Parser_natCore(v___x_653_, v_a_648_);
return v___x_654_;
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_numWithDecimals___closed__0(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = l_System_Platform_numBits;
v___x_681_ = lean_unsigned_to_nat(2u);
v___x_682_ = lean_nat_pow(v___x_681_, v___x_680_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numWithDecimals(lean_object* v_a_686_){
_start:
{
lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; uint8_t v___y_691_; lean_object* v___y_738_; lean_object* v___y_742_; lean_object* v_pos_743_; lean_object* v_fst_744_; lean_object* v_snd_745_; lean_object* v_res_746_; lean_object* v___y_769_; lean_object* v___y_770_; uint8_t v___y_771_; lean_object* v_pos_790_; lean_object* v_fst_791_; lean_object* v_snd_792_; lean_object* v_res_793_; lean_object* v_fst_808_; lean_object* v_snd_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v_fst_808_ = lean_ctor_get(v_a_686_, 0);
v_snd_809_ = lean_ctor_get(v_a_686_, 1);
v___x_810_ = lean_string_utf8_byte_size(v_fst_808_);
v___x_811_ = lean_nat_dec_eq(v_snd_809_, v___x_810_);
if (v___x_811_ == 0)
{
uint32_t v___x_812_; uint32_t v___x_813_; uint8_t v___x_814_; 
lean_inc(v_snd_809_);
lean_inc(v_fst_808_);
v___x_812_ = lean_string_utf8_get_fast(v_fst_808_, v_snd_809_);
v___x_813_ = 45;
v___x_814_ = lean_uint32_dec_eq(v___x_812_, v___x_813_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; 
v___x_815_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v_pos_790_ = v_a_686_;
v_fst_791_ = v_fst_808_;
v_snd_792_ = v_snd_809_;
v_res_793_ = v___x_815_;
goto v___jp_789_;
}
else
{
lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_824_; 
v_isSharedCheck_824_ = !lean_is_exclusive(v_a_686_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; lean_object* v_unused_826_; 
v_unused_825_ = lean_ctor_get(v_a_686_, 1);
lean_dec(v_unused_825_);
v_unused_826_ = lean_ctor_get(v_a_686_, 0);
lean_dec(v_unused_826_);
v___x_817_ = v_a_686_;
v_isShared_818_ = v_isSharedCheck_824_;
goto v_resetjp_816_;
}
else
{
lean_dec(v_a_686_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_824_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = lean_string_utf8_next_fast(v_fst_808_, v_snd_809_);
lean_dec(v_snd_809_);
lean_inc(v_fst_808_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v___x_819_);
v___x_821_ = v___x_817_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_fst_808_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v___x_819_);
v___x_821_ = v_reuseFailAlloc_823_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; 
v___x_822_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v_pos_790_ = v___x_821_;
v_fst_791_ = v_fst_808_;
v_snd_792_ = v___x_819_;
v_res_793_ = v___x_822_;
goto v___jp_789_;
}
}
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_box(0);
v___x_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_828_, 0, v_a_686_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
return v___x_828_;
}
v___jp_687_:
{
if (v___y_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec(v___y_690_);
v___x_692_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_693_, 0, v___y_688_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_694_, v___x_694_, v___y_688_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_res_696_; lean_object* v_pos_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_727_; 
v_res_696_ = lean_ctor_get(v___x_695_, 1);
v_pos_697_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_727_ == 0)
{
v___x_699_ = v___x_695_;
v_isShared_700_ = v_isSharedCheck_727_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_res_696_);
lean_inc(v_pos_697_);
lean_dec(v___x_695_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_727_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v_fst_701_; lean_object* v_snd_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_726_; 
v_fst_701_ = lean_ctor_get(v_res_696_, 0);
v_snd_702_ = lean_ctor_get(v_res_696_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_res_696_);
if (v_isSharedCheck_726_ == 0)
{
v___x_704_ = v_res_696_;
v_isShared_705_ = v_isSharedCheck_726_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_snd_702_);
lean_inc(v_fst_701_);
lean_dec(v_res_696_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_726_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_707_ = lean_nat_dec_lt(v___x_706_, v_snd_702_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_708_ = lean_nat_to_int(v___y_690_);
v___x_709_ = lean_unsigned_to_nat(10u);
v___x_710_ = lean_nat_pow(v___x_709_, v_snd_702_);
v___x_711_ = lean_nat_to_int(v___x_710_);
v___x_712_ = lean_int_mul(v___x_708_, v___x_711_);
lean_dec(v___x_711_);
lean_dec(v___x_708_);
v___x_713_ = lean_nat_to_int(v_fst_701_);
v___x_714_ = lean_int_add(v___x_712_, v___x_713_);
lean_dec(v___x_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_int_mul(v___y_689_, v___x_714_);
lean_dec(v___x_714_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_715_);
v___x_717_ = v___x_704_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_snd_702_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v___x_717_);
v___x_719_ = v___x_699_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_pos_697_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
lean_object* v___x_722_; lean_object* v___x_724_; 
lean_del_object(v___x_704_);
lean_dec(v_snd_702_);
lean_dec(v_fst_701_);
lean_dec(v___y_690_);
v___x_722_ = ((lean_object*)(l_Lean_Json_Parser_numWithDecimals___closed__2));
if (v_isShared_700_ == 0)
{
lean_ctor_set_tag(v___x_699_, 1);
lean_ctor_set(v___x_699_, 1, v___x_722_);
v___x_724_ = v___x_699_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_pos_697_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
else
{
lean_object* v_pos_728_; lean_object* v_err_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec(v___y_690_);
v_pos_728_ = lean_ctor_get(v___x_695_, 0);
v_err_729_ = lean_ctor_get(v___x_695_, 1);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_695_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_err_729_);
lean_inc(v_pos_728_);
lean_dec(v___x_695_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_pos_728_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_err_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
v___jp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_box(0);
v___x_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_740_, 0, v___y_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
return v___x_740_;
}
v___jp_741_:
{
lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_747_ = lean_string_utf8_byte_size(v_fst_744_);
v___x_748_ = lean_nat_dec_eq(v_snd_745_, v___x_747_);
if (v___x_748_ == 0)
{
uint32_t v___x_749_; uint32_t v___x_750_; uint8_t v___x_751_; 
v___x_749_ = lean_string_utf8_get_fast(v_fst_744_, v_snd_745_);
v___x_750_ = 46;
v___x_751_ = lean_uint32_dec_eq(v___x_749_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec(v_snd_745_);
lean_dec(v_fst_744_);
v___x_752_ = lean_nat_to_int(v_res_746_);
v___x_753_ = lean_int_mul(v___y_742_, v___x_752_);
lean_dec(v___x_752_);
v___x_754_ = l_Lean_JsonNumber_fromInt(v___x_753_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_pos_743_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
return v___x_755_;
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
lean_dec_ref(v_pos_743_);
v___x_756_ = lean_string_utf8_next_fast(v_fst_744_, v_snd_745_);
lean_dec(v_snd_745_);
lean_inc(v_fst_744_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v_fst_744_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = lean_nat_dec_eq(v___x_756_, v___x_747_);
if (v___x_758_ == 0)
{
if (v___x_751_ == 0)
{
lean_dec(v_res_746_);
lean_dec(v_fst_744_);
v___y_738_ = v___x_757_;
goto v___jp_737_;
}
else
{
uint32_t v___x_759_; uint32_t v___x_760_; uint8_t v___x_761_; 
v___x_759_ = lean_string_utf8_get_fast(v_fst_744_, v___x_756_);
lean_dec(v_fst_744_);
v___x_760_ = 48;
v___x_761_ = lean_uint32_dec_le(v___x_760_, v___x_759_);
if (v___x_761_ == 0)
{
v___y_688_ = v___x_757_;
v___y_689_ = v___y_742_;
v___y_690_ = v_res_746_;
v___y_691_ = v___x_761_;
goto v___jp_687_;
}
else
{
uint32_t v___x_762_; uint8_t v___x_763_; 
v___x_762_ = 57;
v___x_763_ = lean_uint32_dec_le(v___x_759_, v___x_762_);
v___y_688_ = v___x_757_;
v___y_689_ = v___y_742_;
v___y_690_ = v_res_746_;
v___y_691_ = v___x_763_;
goto v___jp_687_;
}
}
}
else
{
lean_dec(v_res_746_);
lean_dec(v_fst_744_);
v___y_738_ = v___x_757_;
goto v___jp_737_;
}
}
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec(v_snd_745_);
lean_dec(v_fst_744_);
v___x_764_ = lean_nat_to_int(v_res_746_);
v___x_765_ = lean_int_mul(v___y_742_, v___x_764_);
lean_dec(v___x_764_);
v___x_766_ = l_Lean_JsonNumber_fromInt(v___x_765_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v_pos_743_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
return v___x_767_;
}
}
v___jp_768_:
{
if (v___y_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_773_, 0, v___y_770_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
return v___x_773_;
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = l_Lean_Json_Parser_natCore(v___x_774_, v___y_770_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_pos_776_; lean_object* v_res_777_; lean_object* v_fst_778_; lean_object* v_snd_779_; 
v_pos_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_pos_776_);
v_res_777_ = lean_ctor_get(v___x_775_, 1);
lean_inc(v_res_777_);
lean_dec_ref(v___x_775_);
v_fst_778_ = lean_ctor_get(v_pos_776_, 0);
lean_inc(v_fst_778_);
v_snd_779_ = lean_ctor_get(v_pos_776_, 1);
lean_inc(v_snd_779_);
v___y_742_ = v___y_769_;
v_pos_743_ = v_pos_776_;
v_fst_744_ = v_fst_778_;
v_snd_745_ = v_snd_779_;
v_res_746_ = v_res_777_;
goto v___jp_741_;
}
else
{
lean_object* v_pos_780_; lean_object* v_err_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
v_pos_780_ = lean_ctor_get(v___x_775_, 0);
v_err_781_ = lean_ctor_get(v___x_775_, 1);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_775_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_err_781_);
lean_inc(v_pos_780_);
lean_dec(v___x_775_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_pos_780_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_err_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
v___jp_789_:
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = lean_string_utf8_byte_size(v_fst_791_);
v___x_795_ = lean_nat_dec_eq(v_snd_792_, v___x_794_);
if (v___x_795_ == 0)
{
uint32_t v___x_796_; uint32_t v___x_797_; uint8_t v___x_798_; 
v___x_796_ = lean_string_utf8_get_fast(v_fst_791_, v_snd_792_);
v___x_797_ = 48;
v___x_798_ = lean_uint32_dec_eq(v___x_796_, v___x_797_);
if (v___x_798_ == 0)
{
uint32_t v___x_799_; uint8_t v___x_800_; 
lean_dec(v_snd_792_);
lean_dec(v_fst_791_);
v___x_799_ = 49;
v___x_800_ = lean_uint32_dec_le(v___x_799_, v___x_796_);
if (v___x_800_ == 0)
{
v___y_769_ = v_res_793_;
v___y_770_ = v_pos_790_;
v___y_771_ = v___x_800_;
goto v___jp_768_;
}
else
{
uint32_t v___x_801_; uint8_t v___x_802_; 
v___x_801_ = 57;
v___x_802_ = lean_uint32_dec_le(v___x_796_, v___x_801_);
v___y_769_ = v_res_793_;
v___y_770_ = v_pos_790_;
v___y_771_ = v___x_802_;
goto v___jp_768_;
}
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec_ref(v_pos_790_);
v___x_803_ = lean_string_utf8_next_fast(v_fst_791_, v_snd_792_);
lean_dec(v_snd_792_);
lean_inc(v_fst_791_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v_fst_791_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = lean_unsigned_to_nat(0u);
v___y_742_ = v_res_793_;
v_pos_743_ = v___x_804_;
v_fst_744_ = v_fst_791_;
v_snd_745_ = v___x_803_;
v_res_746_ = v___x_805_;
goto v___jp_741_;
}
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec(v_snd_792_);
lean_dec(v_fst_791_);
v___x_806_ = lean_box(0);
v___x_807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_807_, 0, v_pos_790_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
return v___x_807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent(lean_object* v_value_832_, lean_object* v_a_833_){
_start:
{
lean_object* v___y_835_; lean_object* v___y_839_; uint8_t v___y_840_; lean_object* v___y_865_; uint8_t v___y_866_; lean_object* v___y_897_; lean_object* v_fst_898_; lean_object* v_snd_899_; lean_object* v_fst_909_; lean_object* v_snd_910_; lean_object* v___x_944_; uint8_t v___x_945_; 
v_fst_909_ = lean_ctor_get(v_a_833_, 0);
v_snd_910_ = lean_ctor_get(v_a_833_, 1);
v___x_944_ = lean_string_utf8_byte_size(v_fst_909_);
v___x_945_ = lean_nat_dec_eq(v_snd_910_, v___x_944_);
if (v___x_945_ == 0)
{
uint32_t v___x_946_; uint32_t v___x_947_; uint8_t v___x_948_; 
v___x_946_ = lean_string_utf8_get_fast(v_fst_909_, v_snd_910_);
v___x_947_ = 101;
v___x_948_ = lean_uint32_dec_eq(v___x_946_, v___x_947_);
if (v___x_948_ == 0)
{
uint32_t v___x_949_; uint8_t v___x_950_; 
v___x_949_ = 69;
v___x_950_ = lean_uint32_dec_eq(v___x_946_, v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; 
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v_a_833_);
lean_ctor_set(v___x_951_, 1, v_value_832_);
return v___x_951_;
}
else
{
goto v___jp_911_;
}
}
else
{
goto v___jp_911_;
}
}
else
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v_a_833_);
lean_ctor_set(v___x_952_, 1, v_value_832_);
return v___x_952_;
}
v___jp_834_:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_box(0);
v___x_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_837_, 0, v___y_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
return v___x_837_;
}
v___jp_838_:
{
if (v___y_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec_ref(v_value_832_);
v___x_841_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_842_, 0, v___y_839_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
return v___x_842_;
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = l_Lean_Json_Parser_natCore(v___x_843_, v___y_839_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_pos_845_; lean_object* v_res_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_854_; 
v_pos_845_ = lean_ctor_get(v___x_844_, 0);
v_res_846_ = lean_ctor_get(v___x_844_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_854_ == 0)
{
v___x_848_ = v___x_844_;
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_res_846_);
lean_inc(v_pos_845_);
lean_dec(v___x_844_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_850_ = l_Lean_JsonNumber_shiftr(v_value_832_, v_res_846_);
lean_dec(v_res_846_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v___x_850_);
v___x_852_ = v___x_848_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_pos_845_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
else
{
lean_object* v_pos_855_; lean_object* v_err_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec_ref(v_value_832_);
v_pos_855_ = lean_ctor_get(v___x_844_, 0);
v_err_856_ = lean_ctor_get(v___x_844_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_844_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_err_856_);
lean_inc(v_pos_855_);
lean_dec(v___x_844_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_pos_855_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_err_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
v___jp_864_:
{
if (v___y_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; 
lean_dec_ref(v_value_832_);
v___x_867_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_868_, 0, v___y_865_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
return v___x_868_;
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = l_Lean_Json_Parser_natCore(v___x_869_, v___y_865_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_pos_871_; lean_object* v_res_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_886_; 
v_pos_871_ = lean_ctor_get(v___x_870_, 0);
v_res_872_ = lean_ctor_get(v___x_870_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_886_ == 0)
{
v___x_874_ = v___x_870_;
v_isShared_875_ = v_isSharedCheck_886_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_res_872_);
lean_inc(v_pos_871_);
lean_dec(v___x_870_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_886_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_876_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_877_ = lean_nat_dec_lt(v___x_876_, v_res_872_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_878_ = l_Lean_JsonNumber_shiftl(v_value_832_, v_res_872_);
lean_dec(v_res_872_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 1, v___x_878_);
v___x_880_ = v___x_874_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_pos_871_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
else
{
lean_object* v___x_882_; lean_object* v___x_884_; 
lean_dec(v_res_872_);
lean_dec_ref(v_value_832_);
v___x_882_ = ((lean_object*)(l_Lean_Json_Parser_exponent___closed__1));
if (v_isShared_875_ == 0)
{
lean_ctor_set_tag(v___x_874_, 1);
lean_ctor_set(v___x_874_, 1, v___x_882_);
v___x_884_ = v___x_874_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_pos_871_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
lean_object* v_pos_887_; lean_object* v_err_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref(v_value_832_);
v_pos_887_ = lean_ctor_get(v___x_870_, 0);
v_err_888_ = lean_ctor_get(v___x_870_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_870_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_err_888_);
lean_inc(v_pos_887_);
lean_dec(v___x_870_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_pos_887_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_err_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
v___jp_896_:
{
lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_900_ = lean_string_utf8_byte_size(v_fst_898_);
v___x_901_ = lean_nat_dec_eq(v_snd_899_, v___x_900_);
if (v___x_901_ == 0)
{
uint32_t v___x_902_; uint32_t v___x_903_; uint8_t v___x_904_; 
v___x_902_ = lean_string_utf8_get_fast(v_fst_898_, v_snd_899_);
lean_dec(v_snd_899_);
lean_dec(v_fst_898_);
v___x_903_ = 48;
v___x_904_ = lean_uint32_dec_le(v___x_903_, v___x_902_);
if (v___x_904_ == 0)
{
v___y_865_ = v___y_897_;
v___y_866_ = v___x_904_;
goto v___jp_864_;
}
else
{
uint32_t v___x_905_; uint8_t v___x_906_; 
v___x_905_ = 57;
v___x_906_ = lean_uint32_dec_le(v___x_902_, v___x_905_);
v___y_865_ = v___y_897_;
v___y_866_ = v___x_906_;
goto v___jp_864_;
}
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec(v_snd_899_);
lean_dec(v_fst_898_);
lean_dec_ref(v_value_832_);
v___x_907_ = lean_box(0);
v___x_908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_908_, 0, v___y_897_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
return v___x_908_;
}
}
v___jp_911_:
{
lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_912_ = lean_string_utf8_byte_size(v_fst_909_);
v___x_913_ = lean_nat_dec_eq(v_snd_910_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_939_; 
lean_inc(v_snd_910_);
lean_inc(v_fst_909_);
v_isSharedCheck_939_ = !lean_is_exclusive(v_a_833_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; lean_object* v_unused_941_; 
v_unused_940_ = lean_ctor_get(v_a_833_, 1);
lean_dec(v_unused_940_);
v_unused_941_ = lean_ctor_get(v_a_833_, 0);
lean_dec(v_unused_941_);
v___x_915_ = v_a_833_;
v_isShared_916_ = v_isSharedCheck_939_;
goto v_resetjp_914_;
}
else
{
lean_dec(v_a_833_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_939_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_917_ = lean_string_utf8_next_fast(v_fst_909_, v_snd_910_);
lean_dec(v_snd_910_);
lean_inc(v_fst_909_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 1, v___x_917_);
v___x_919_ = v___x_915_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_fst_909_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_917_);
v___x_919_ = v_reuseFailAlloc_938_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
uint8_t v___x_920_; 
v___x_920_ = lean_nat_dec_eq(v___x_917_, v___x_912_);
if (v___x_920_ == 0)
{
uint32_t v___x_921_; uint32_t v___x_922_; uint8_t v___x_923_; 
v___x_921_ = lean_string_utf8_get_fast(v_fst_909_, v___x_917_);
v___x_922_ = 45;
v___x_923_ = lean_uint32_dec_eq(v___x_921_, v___x_922_);
if (v___x_923_ == 0)
{
uint32_t v___x_924_; uint8_t v___x_925_; 
v___x_924_ = 43;
v___x_925_ = lean_uint32_dec_eq(v___x_921_, v___x_924_);
if (v___x_925_ == 0)
{
v___y_897_ = v___x_919_;
v_fst_898_ = v_fst_909_;
v_snd_899_ = v___x_917_;
goto v___jp_896_;
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec_ref(v___x_919_);
v___x_926_ = lean_string_utf8_next_fast(v_fst_909_, v___x_917_);
lean_inc(v_fst_909_);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v_fst_909_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___y_897_ = v___x_927_;
v_fst_898_ = v_fst_909_;
v_snd_899_ = v___x_926_;
goto v___jp_896_;
}
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
lean_dec_ref(v___x_919_);
v___x_928_ = lean_string_utf8_next_fast(v_fst_909_, v___x_917_);
lean_inc(v_fst_909_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_fst_909_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_nat_dec_eq(v___x_928_, v___x_912_);
if (v___x_930_ == 0)
{
if (v___x_923_ == 0)
{
lean_dec(v_fst_909_);
lean_dec_ref(v_value_832_);
v___y_835_ = v___x_929_;
goto v___jp_834_;
}
else
{
uint32_t v___x_931_; uint32_t v___x_932_; uint8_t v___x_933_; 
v___x_931_ = lean_string_utf8_get_fast(v_fst_909_, v___x_928_);
lean_dec(v_fst_909_);
v___x_932_ = 48;
v___x_933_ = lean_uint32_dec_le(v___x_932_, v___x_931_);
if (v___x_933_ == 0)
{
v___y_839_ = v___x_929_;
v___y_840_ = v___x_933_;
goto v___jp_838_;
}
else
{
uint32_t v___x_934_; uint8_t v___x_935_; 
v___x_934_ = 57;
v___x_935_ = lean_uint32_dec_le(v___x_931_, v___x_934_);
v___y_839_ = v___x_929_;
v___y_840_ = v___x_935_;
goto v___jp_838_;
}
}
}
else
{
lean_dec(v_fst_909_);
lean_dec_ref(v_value_832_);
v___y_835_ = v___x_929_;
goto v___jp_834_;
}
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec(v_fst_909_);
lean_dec_ref(v_value_832_);
v___x_936_ = lean_box(0);
v___x_937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_919_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
return v___x_937_;
}
}
}
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec_ref(v_value_832_);
v___x_942_ = lean_box(0);
v___x_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_943_, 0, v_a_833_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
return v___x_943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Json_Parser_num_spec__0(lean_object* v_a_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = lean_nat_to_int(v_a_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_num(lean_object* v_a_955_){
_start:
{
lean_object* v___y_957_; lean_object* v___y_958_; uint8_t v___y_959_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v_fst_992_; lean_object* v_snd_993_; lean_object* v___y_1004_; lean_object* v___y_1005_; uint8_t v___y_1006_; lean_object* v___y_1031_; lean_object* v___y_1035_; lean_object* v_fst_1036_; lean_object* v_snd_1037_; lean_object* v___y_1038_; lean_object* v___y_1064_; lean_object* v_pos_1065_; lean_object* v_fst_1066_; lean_object* v_snd_1067_; lean_object* v_res_1068_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; uint8_t v___y_1080_; lean_object* v___y_1129_; lean_object* v___y_1133_; lean_object* v_pos_1134_; lean_object* v_fst_1135_; lean_object* v_snd_1136_; lean_object* v_res_1137_; lean_object* v___y_1160_; lean_object* v___y_1161_; uint8_t v___y_1162_; lean_object* v_pos_1181_; lean_object* v_fst_1182_; lean_object* v_snd_1183_; lean_object* v_res_1184_; lean_object* v_fst_1199_; lean_object* v_snd_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_fst_1199_ = lean_ctor_get(v_a_955_, 0);
v_snd_1200_ = lean_ctor_get(v_a_955_, 1);
v___x_1201_ = lean_string_utf8_byte_size(v_fst_1199_);
v___x_1202_ = lean_nat_dec_eq(v_snd_1200_, v___x_1201_);
if (v___x_1202_ == 0)
{
uint32_t v___x_1203_; uint32_t v___x_1204_; uint8_t v___x_1205_; 
lean_inc(v_snd_1200_);
lean_inc(v_fst_1199_);
v___x_1203_ = lean_string_utf8_get_fast(v_fst_1199_, v_snd_1200_);
v___x_1204_ = 45;
v___x_1205_ = lean_uint32_dec_eq(v___x_1203_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v_pos_1181_ = v_a_955_;
v_fst_1182_ = v_fst_1199_;
v_snd_1183_ = v_snd_1200_;
v_res_1184_ = v___x_1206_;
goto v___jp_1180_;
}
else
{
lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1215_; 
v_isSharedCheck_1215_ = !lean_is_exclusive(v_a_955_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; lean_object* v_unused_1217_; 
v_unused_1216_ = lean_ctor_get(v_a_955_, 1);
lean_dec(v_unused_1216_);
v_unused_1217_ = lean_ctor_get(v_a_955_, 0);
lean_dec(v_unused_1217_);
v___x_1208_ = v_a_955_;
v_isShared_1209_ = v_isSharedCheck_1215_;
goto v_resetjp_1207_;
}
else
{
lean_dec(v_a_955_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1215_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1210_ = lean_string_utf8_next_fast(v_fst_1199_, v_snd_1200_);
lean_dec(v_snd_1200_);
lean_inc(v_fst_1199_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 1, v___x_1210_);
v___x_1212_ = v___x_1208_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_fst_1199_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v_pos_1181_ = v___x_1212_;
v_fst_1182_ = v_fst_1199_;
v_snd_1183_ = v___x_1210_;
v_res_1184_ = v___x_1213_;
goto v___jp_1180_;
}
}
}
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_box(0);
v___x_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1219_, 0, v_a_955_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
return v___x_1219_;
}
v___jp_956_:
{
if (v___y_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec_ref(v___y_958_);
v___x_960_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_961_, 0, v___y_957_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
return v___x_961_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_unsigned_to_nat(0u);
v___x_963_ = l_Lean_Json_Parser_natCore(v___x_962_, v___y_957_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_pos_964_; lean_object* v_res_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_979_; 
v_pos_964_ = lean_ctor_get(v___x_963_, 0);
v_res_965_ = lean_ctor_get(v___x_963_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_979_ == 0)
{
v___x_967_ = v___x_963_;
v_isShared_968_ = v_isSharedCheck_979_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_res_965_);
lean_inc(v_pos_964_);
lean_dec(v___x_963_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_979_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_969_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_970_ = lean_nat_dec_lt(v___x_969_, v_res_965_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_971_ = l_Lean_JsonNumber_shiftl(v___y_958_, v_res_965_);
lean_dec(v_res_965_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 1, v___x_971_);
v___x_973_ = v___x_967_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_pos_964_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
else
{
lean_object* v___x_975_; lean_object* v___x_977_; 
lean_dec(v_res_965_);
lean_dec_ref(v___y_958_);
v___x_975_ = ((lean_object*)(l_Lean_Json_Parser_exponent___closed__1));
if (v_isShared_968_ == 0)
{
lean_ctor_set_tag(v___x_967_, 1);
lean_ctor_set(v___x_967_, 1, v___x_975_);
v___x_977_ = v___x_967_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_pos_964_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
else
{
lean_object* v_pos_980_; lean_object* v_err_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec_ref(v___y_958_);
v_pos_980_ = lean_ctor_get(v___x_963_, 0);
v_err_981_ = lean_ctor_get(v___x_963_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_963_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_err_981_);
lean_inc(v_pos_980_);
lean_dec(v___x_963_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_pos_980_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_err_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
v___jp_989_:
{
lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_994_ = lean_string_utf8_byte_size(v_fst_992_);
v___x_995_ = lean_nat_dec_eq(v_snd_993_, v___x_994_);
if (v___x_995_ == 0)
{
uint32_t v___x_996_; uint32_t v___x_997_; uint8_t v___x_998_; 
v___x_996_ = lean_string_utf8_get_fast(v_fst_992_, v_snd_993_);
lean_dec(v_snd_993_);
lean_dec(v_fst_992_);
v___x_997_ = 48;
v___x_998_ = lean_uint32_dec_le(v___x_997_, v___x_996_);
if (v___x_998_ == 0)
{
v___y_957_ = v___y_991_;
v___y_958_ = v___y_990_;
v___y_959_ = v___x_998_;
goto v___jp_956_;
}
else
{
uint32_t v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = 57;
v___x_1000_ = lean_uint32_dec_le(v___x_996_, v___x_999_);
v___y_957_ = v___y_991_;
v___y_958_ = v___y_990_;
v___y_959_ = v___x_1000_;
goto v___jp_956_;
}
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_dec(v_snd_993_);
lean_dec(v_fst_992_);
lean_dec_ref(v___y_990_);
v___x_1001_ = lean_box(0);
v___x_1002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___y_991_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
return v___x_1002_;
}
}
v___jp_1003_:
{
if (v___y_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_dec_ref(v___y_1005_);
v___x_1007_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_1008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___y_1004_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_unsigned_to_nat(0u);
v___x_1010_ = l_Lean_Json_Parser_natCore(v___x_1009_, v___y_1004_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_pos_1011_; lean_object* v_res_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1020_; 
v_pos_1011_ = lean_ctor_get(v___x_1010_, 0);
v_res_1012_ = lean_ctor_get(v___x_1010_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1014_ = v___x_1010_;
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_res_1012_);
lean_inc(v_pos_1011_);
lean_dec(v___x_1010_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1016_ = l_Lean_JsonNumber_shiftr(v___y_1005_, v_res_1012_);
lean_dec(v_res_1012_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 1, v___x_1016_);
v___x_1018_ = v___x_1014_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_pos_1011_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
else
{
lean_object* v_pos_1021_; lean_object* v_err_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec_ref(v___y_1005_);
v_pos_1021_ = lean_ctor_get(v___x_1010_, 0);
v_err_1022_ = lean_ctor_get(v___x_1010_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1010_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_err_1022_);
lean_inc(v_pos_1021_);
lean_dec(v___x_1010_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_pos_1021_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_err_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
v___jp_1030_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___y_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
return v___x_1033_;
}
v___jp_1034_:
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = lean_string_utf8_byte_size(v_fst_1036_);
v___x_1040_ = lean_nat_dec_eq(v_snd_1037_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
lean_dec_ref(v___y_1035_);
v___x_1041_ = lean_string_utf8_next_fast(v_fst_1036_, v_snd_1037_);
lean_dec(v_snd_1037_);
lean_inc(v_fst_1036_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v_fst_1036_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_nat_dec_eq(v___x_1041_, v___x_1039_);
if (v___x_1043_ == 0)
{
uint32_t v___x_1044_; uint32_t v___x_1045_; uint8_t v___x_1046_; 
v___x_1044_ = lean_string_utf8_get_fast(v_fst_1036_, v___x_1041_);
v___x_1045_ = 45;
v___x_1046_ = lean_uint32_dec_eq(v___x_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
uint32_t v___x_1047_; uint8_t v___x_1048_; 
v___x_1047_ = 43;
v___x_1048_ = lean_uint32_dec_eq(v___x_1044_, v___x_1047_);
if (v___x_1048_ == 0)
{
v___y_990_ = v___y_1038_;
v___y_991_ = v___x_1042_;
v_fst_992_ = v_fst_1036_;
v_snd_993_ = v___x_1041_;
goto v___jp_989_;
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_dec_ref(v___x_1042_);
v___x_1049_ = lean_string_utf8_next_fast(v_fst_1036_, v___x_1041_);
lean_inc(v_fst_1036_);
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v_fst_1036_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___y_990_ = v___y_1038_;
v___y_991_ = v___x_1050_;
v_fst_992_ = v_fst_1036_;
v_snd_993_ = v___x_1049_;
goto v___jp_989_;
}
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
lean_dec_ref(v___x_1042_);
v___x_1051_ = lean_string_utf8_next_fast(v_fst_1036_, v___x_1041_);
lean_inc(v_fst_1036_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v_fst_1036_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_nat_dec_eq(v___x_1051_, v___x_1039_);
if (v___x_1053_ == 0)
{
if (v___x_1046_ == 0)
{
lean_dec_ref(v___y_1038_);
lean_dec(v_fst_1036_);
v___y_1031_ = v___x_1052_;
goto v___jp_1030_;
}
else
{
uint32_t v___x_1054_; uint32_t v___x_1055_; uint8_t v___x_1056_; 
v___x_1054_ = lean_string_utf8_get_fast(v_fst_1036_, v___x_1051_);
lean_dec(v_fst_1036_);
v___x_1055_ = 48;
v___x_1056_ = lean_uint32_dec_le(v___x_1055_, v___x_1054_);
if (v___x_1056_ == 0)
{
v___y_1004_ = v___x_1052_;
v___y_1005_ = v___y_1038_;
v___y_1006_ = v___x_1056_;
goto v___jp_1003_;
}
else
{
uint32_t v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = 57;
v___x_1058_ = lean_uint32_dec_le(v___x_1054_, v___x_1057_);
v___y_1004_ = v___x_1052_;
v___y_1005_ = v___y_1038_;
v___y_1006_ = v___x_1058_;
goto v___jp_1003_;
}
}
}
else
{
lean_dec_ref(v___y_1038_);
lean_dec(v_fst_1036_);
v___y_1031_ = v___x_1052_;
goto v___jp_1030_;
}
}
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_dec_ref(v___y_1038_);
lean_dec(v_fst_1036_);
v___x_1059_ = lean_box(0);
v___x_1060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1042_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
return v___x_1060_;
}
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
lean_dec_ref(v___y_1038_);
lean_dec(v_snd_1037_);
lean_dec(v_fst_1036_);
v___x_1061_ = lean_box(0);
v___x_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___y_1035_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
return v___x_1062_;
}
}
v___jp_1063_:
{
lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = lean_string_utf8_byte_size(v_fst_1066_);
v___x_1070_ = lean_nat_dec_eq(v_snd_1067_, v___x_1069_);
if (v___x_1070_ == 0)
{
uint32_t v___x_1071_; uint32_t v___x_1072_; uint8_t v___x_1073_; 
v___x_1071_ = lean_string_utf8_get_fast(v_fst_1066_, v_snd_1067_);
v___x_1072_ = 101;
v___x_1073_ = lean_uint32_dec_eq(v___x_1071_, v___x_1072_);
if (v___x_1073_ == 0)
{
uint32_t v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = 69;
v___x_1075_ = lean_uint32_dec_eq(v___x_1071_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_dec_ref(v_res_1068_);
lean_dec(v_snd_1067_);
lean_dec(v_fst_1066_);
lean_dec_ref(v_pos_1065_);
return v___y_1064_;
}
else
{
lean_dec_ref(v___y_1064_);
v___y_1035_ = v_pos_1065_;
v_fst_1036_ = v_fst_1066_;
v_snd_1037_ = v_snd_1067_;
v___y_1038_ = v_res_1068_;
goto v___jp_1034_;
}
}
else
{
lean_dec_ref(v___y_1064_);
v___y_1035_ = v_pos_1065_;
v_fst_1036_ = v_fst_1066_;
v_snd_1037_ = v_snd_1067_;
v___y_1038_ = v_res_1068_;
goto v___jp_1034_;
}
}
else
{
lean_dec_ref(v_res_1068_);
lean_dec(v_snd_1067_);
lean_dec(v_fst_1066_);
lean_dec_ref(v_pos_1065_);
return v___y_1064_;
}
}
v___jp_1076_:
{
if (v___y_1080_ == 0)
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec(v___y_1079_);
v___x_1081_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___y_1077_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
return v___x_1082_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_1083_, v___x_1083_, v___y_1077_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_res_1085_; lean_object* v_pos_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1118_; 
v_res_1085_ = lean_ctor_get(v___x_1084_, 1);
v_pos_1086_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1088_ = v___x_1084_;
v_isShared_1089_ = v_isSharedCheck_1118_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_res_1085_);
lean_inc(v_pos_1086_);
lean_dec(v___x_1084_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1118_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_fst_1090_; lean_object* v_snd_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1117_; 
v_fst_1090_ = lean_ctor_get(v_res_1085_, 0);
v_snd_1091_ = lean_ctor_get(v_res_1085_, 1);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_res_1085_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1093_ = v_res_1085_;
v_isShared_1094_ = v_isSharedCheck_1117_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_snd_1091_);
lean_inc(v_fst_1090_);
lean_dec(v_res_1085_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1117_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_1096_ = lean_nat_dec_lt(v___x_1095_, v_snd_1091_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v_fst_1099_; lean_object* v_snd_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1097_ = lean_unsigned_to_nat(10u);
v___x_1098_ = lean_nat_pow(v___x_1097_, v_snd_1091_);
v_fst_1099_ = lean_ctor_get(v_pos_1086_, 0);
lean_inc(v_fst_1099_);
v_snd_1100_ = lean_ctor_get(v_pos_1086_, 1);
lean_inc(v_snd_1100_);
v___x_1101_ = lean_nat_to_int(v___y_1079_);
v___x_1102_ = lean_nat_to_int(v___x_1098_);
v___x_1103_ = lean_int_mul(v___x_1101_, v___x_1102_);
lean_dec(v___x_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_nat_to_int(v_fst_1090_);
v___x_1105_ = lean_int_add(v___x_1103_, v___x_1104_);
lean_dec(v___x_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_int_mul(v___y_1078_, v___x_1105_);
lean_dec(v___x_1105_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1106_);
v___x_1108_ = v___x_1093_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_snd_1091_);
v___x_1108_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1110_; 
lean_inc_ref(v___x_1108_);
lean_inc(v_pos_1086_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v___x_1108_);
v___x_1110_ = v___x_1088_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_pos_1086_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
v___y_1064_ = v___x_1110_;
v_pos_1065_ = v_pos_1086_;
v_fst_1066_ = v_fst_1099_;
v_snd_1067_ = v_snd_1100_;
v_res_1068_ = v___x_1108_;
goto v___jp_1063_;
}
}
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
lean_del_object(v___x_1093_);
lean_dec(v_snd_1091_);
lean_dec(v_fst_1090_);
lean_dec(v___y_1079_);
v___x_1113_ = ((lean_object*)(l_Lean_Json_Parser_numWithDecimals___closed__2));
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 1);
lean_ctor_set(v___x_1088_, 1, v___x_1113_);
v___x_1115_ = v___x_1088_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_pos_1086_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
else
{
lean_object* v_pos_1119_; lean_object* v_err_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v___y_1079_);
v_pos_1119_ = lean_ctor_get(v___x_1084_, 0);
v_err_1120_ = lean_ctor_get(v___x_1084_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1084_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_err_1120_);
lean_inc(v_pos_1119_);
lean_dec(v___x_1084_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_pos_1119_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_err_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
v___jp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___y_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
return v___x_1131_;
}
v___jp_1132_:
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_string_utf8_byte_size(v_fst_1135_);
v___x_1139_ = lean_nat_dec_eq(v_snd_1136_, v___x_1138_);
if (v___x_1139_ == 0)
{
uint32_t v___x_1140_; uint32_t v___x_1141_; uint8_t v___x_1142_; 
v___x_1140_ = lean_string_utf8_get_fast(v_fst_1135_, v_snd_1136_);
v___x_1141_ = 46;
v___x_1142_ = lean_uint32_dec_eq(v___x_1140_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1143_ = lean_nat_to_int(v_res_1137_);
v___x_1144_ = lean_int_mul(v___y_1133_, v___x_1143_);
lean_dec(v___x_1143_);
v___x_1145_ = l_Lean_JsonNumber_fromInt(v___x_1144_);
lean_inc_ref(v___x_1145_);
lean_inc_ref(v_pos_1134_);
v___x_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1146_, 0, v_pos_1134_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___y_1064_ = v___x_1146_;
v_pos_1065_ = v_pos_1134_;
v_fst_1066_ = v_fst_1135_;
v_snd_1067_ = v_snd_1136_;
v_res_1068_ = v___x_1145_;
goto v___jp_1063_;
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
lean_dec_ref(v_pos_1134_);
v___x_1147_ = lean_string_utf8_next_fast(v_fst_1135_, v_snd_1136_);
lean_dec(v_snd_1136_);
lean_inc(v_fst_1135_);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v_fst_1135_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = lean_nat_dec_eq(v___x_1147_, v___x_1138_);
if (v___x_1149_ == 0)
{
if (v___x_1142_ == 0)
{
lean_dec(v_res_1137_);
lean_dec(v_fst_1135_);
v___y_1129_ = v___x_1148_;
goto v___jp_1128_;
}
else
{
uint32_t v___x_1150_; uint32_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1150_ = lean_string_utf8_get_fast(v_fst_1135_, v___x_1147_);
lean_dec(v_fst_1135_);
v___x_1151_ = 48;
v___x_1152_ = lean_uint32_dec_le(v___x_1151_, v___x_1150_);
if (v___x_1152_ == 0)
{
v___y_1077_ = v___x_1148_;
v___y_1078_ = v___y_1133_;
v___y_1079_ = v_res_1137_;
v___y_1080_ = v___x_1152_;
goto v___jp_1076_;
}
else
{
uint32_t v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = 57;
v___x_1154_ = lean_uint32_dec_le(v___x_1150_, v___x_1153_);
v___y_1077_ = v___x_1148_;
v___y_1078_ = v___y_1133_;
v___y_1079_ = v_res_1137_;
v___y_1080_ = v___x_1154_;
goto v___jp_1076_;
}
}
}
else
{
lean_dec(v_res_1137_);
lean_dec(v_fst_1135_);
v___y_1129_ = v___x_1148_;
goto v___jp_1128_;
}
}
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1155_ = lean_nat_to_int(v_res_1137_);
v___x_1156_ = lean_int_mul(v___y_1133_, v___x_1155_);
lean_dec(v___x_1155_);
v___x_1157_ = l_Lean_JsonNumber_fromInt(v___x_1156_);
lean_inc_ref(v___x_1157_);
lean_inc_ref(v_pos_1134_);
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v_pos_1134_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___y_1064_ = v___x_1158_;
v_pos_1065_ = v_pos_1134_;
v_fst_1066_ = v_fst_1135_;
v_snd_1067_ = v_snd_1136_;
v_res_1068_ = v___x_1157_;
goto v___jp_1063_;
}
}
v___jp_1159_:
{
if (v___y_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_1164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___y_1160_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
return v___x_1164_;
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = l_Lean_Json_Parser_natCore(v___x_1165_, v___y_1160_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_pos_1167_; lean_object* v_res_1168_; lean_object* v_fst_1169_; lean_object* v_snd_1170_; 
v_pos_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_pos_1167_);
v_res_1168_ = lean_ctor_get(v___x_1166_, 1);
lean_inc(v_res_1168_);
lean_dec_ref(v___x_1166_);
v_fst_1169_ = lean_ctor_get(v_pos_1167_, 0);
lean_inc(v_fst_1169_);
v_snd_1170_ = lean_ctor_get(v_pos_1167_, 1);
lean_inc(v_snd_1170_);
v___y_1133_ = v___y_1161_;
v_pos_1134_ = v_pos_1167_;
v_fst_1135_ = v_fst_1169_;
v_snd_1136_ = v_snd_1170_;
v_res_1137_ = v_res_1168_;
goto v___jp_1132_;
}
else
{
lean_object* v_pos_1171_; lean_object* v_err_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
v_pos_1171_ = lean_ctor_get(v___x_1166_, 0);
v_err_1172_ = lean_ctor_get(v___x_1166_, 1);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1166_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_err_1172_);
lean_inc(v_pos_1171_);
lean_dec(v___x_1166_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_pos_1171_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_err_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
v___jp_1180_:
{
lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = lean_string_utf8_byte_size(v_fst_1182_);
v___x_1186_ = lean_nat_dec_eq(v_snd_1183_, v___x_1185_);
if (v___x_1186_ == 0)
{
uint32_t v___x_1187_; uint32_t v___x_1188_; uint8_t v___x_1189_; 
v___x_1187_ = lean_string_utf8_get_fast(v_fst_1182_, v_snd_1183_);
v___x_1188_ = 48;
v___x_1189_ = lean_uint32_dec_eq(v___x_1187_, v___x_1188_);
if (v___x_1189_ == 0)
{
uint32_t v___x_1190_; uint8_t v___x_1191_; 
lean_dec(v_snd_1183_);
lean_dec(v_fst_1182_);
v___x_1190_ = 49;
v___x_1191_ = lean_uint32_dec_le(v___x_1190_, v___x_1187_);
if (v___x_1191_ == 0)
{
v___y_1160_ = v_pos_1181_;
v___y_1161_ = v_res_1184_;
v___y_1162_ = v___x_1191_;
goto v___jp_1159_;
}
else
{
uint32_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = 57;
v___x_1193_ = lean_uint32_dec_le(v___x_1187_, v___x_1192_);
v___y_1160_ = v_pos_1181_;
v___y_1161_ = v_res_1184_;
v___y_1162_ = v___x_1193_;
goto v___jp_1159_;
}
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec_ref(v_pos_1181_);
v___x_1194_ = lean_string_utf8_next_fast(v_fst_1182_, v_snd_1183_);
lean_dec(v_snd_1183_);
lean_inc(v_fst_1182_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v_fst_1182_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = lean_unsigned_to_nat(0u);
v___y_1133_ = v_res_1184_;
v_pos_1134_ = v___x_1195_;
v_fst_1135_ = v_fst_1182_;
v_snd_1136_ = v___x_1194_;
v_res_1137_ = v___x_1196_;
goto v___jp_1132_;
}
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_dec(v_snd_1183_);
lean_dec(v_fst_1182_);
v___x_1197_ = lean_box(0);
v___x_1198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1198_, 0, v_pos_1181_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
return v___x_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(lean_object* v_msg_1220_){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_box(1);
v___x_1222_ = lean_panic_fn_borrowed(v___x_1221_, v_msg_1220_);
return v___x_1222_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1226_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2));
v___x_1227_ = lean_unsigned_to_nat(35u);
v___x_1228_ = lean_unsigned_to_nat(276u);
v___x_1229_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1));
v___x_1230_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1231_ = l_mkPanicMessageWithDecl(v___x_1230_, v___x_1229_, v___x_1228_, v___x_1227_, v___x_1226_);
return v___x_1231_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1232_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2));
v___x_1233_ = lean_unsigned_to_nat(21u);
v___x_1234_ = lean_unsigned_to_nat(277u);
v___x_1235_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1));
v___x_1236_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1237_ = l_mkPanicMessageWithDecl(v___x_1236_, v___x_1235_, v___x_1234_, v___x_1233_, v___x_1232_);
return v___x_1237_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1240_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6));
v___x_1241_ = lean_unsigned_to_nat(35u);
v___x_1242_ = lean_unsigned_to_nat(182u);
v___x_1243_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5));
v___x_1244_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1245_ = l_mkPanicMessageWithDecl(v___x_1244_, v___x_1243_, v___x_1242_, v___x_1241_, v___x_1240_);
return v___x_1245_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1246_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6));
v___x_1247_ = lean_unsigned_to_nat(21u);
v___x_1248_ = lean_unsigned_to_nat(183u);
v___x_1249_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5));
v___x_1250_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1251_ = l_mkPanicMessageWithDecl(v___x_1250_, v___x_1249_, v___x_1248_, v___x_1247_, v___x_1246_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(lean_object* v_k_1252_, lean_object* v_v_1253_, lean_object* v_t_1254_){
_start:
{
if (lean_obj_tag(v_t_1254_) == 0)
{
lean_object* v_size_1255_; lean_object* v_k_1256_; lean_object* v_v_1257_; lean_object* v_l_1258_; lean_object* v_r_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1616_; 
v_size_1255_ = lean_ctor_get(v_t_1254_, 0);
v_k_1256_ = lean_ctor_get(v_t_1254_, 1);
v_v_1257_ = lean_ctor_get(v_t_1254_, 2);
v_l_1258_ = lean_ctor_get(v_t_1254_, 3);
v_r_1259_ = lean_ctor_get(v_t_1254_, 4);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_t_1254_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1261_ = v_t_1254_;
v_isShared_1262_ = v_isSharedCheck_1616_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_r_1259_);
lean_inc(v_l_1258_);
lean_inc(v_v_1257_);
lean_inc(v_k_1256_);
lean_inc(v_size_1255_);
lean_dec(v_t_1254_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1616_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
uint8_t v___x_1263_; 
v___x_1263_ = lean_string_dec_lt(v_k_1252_, v_k_1256_);
if (v___x_1263_ == 0)
{
uint8_t v___x_1264_; 
v___x_1264_ = lean_string_dec_eq(v_k_1252_, v_k_1256_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_dec(v_size_1255_);
v___x_1265_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_1252_, v_v_1253_, v_r_1259_);
if (lean_obj_tag(v_l_1258_) == 0)
{
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_size_1266_; lean_object* v_size_1267_; lean_object* v_k_1268_; lean_object* v_v_1269_; lean_object* v_l_1270_; lean_object* v_r_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v_size_1266_ = lean_ctor_get(v_l_1258_, 0);
v_size_1267_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_size_1267_);
v_k_1268_ = lean_ctor_get(v___x_1265_, 1);
lean_inc(v_k_1268_);
v_v_1269_ = lean_ctor_get(v___x_1265_, 2);
lean_inc(v_v_1269_);
v_l_1270_ = lean_ctor_get(v___x_1265_, 3);
lean_inc(v_l_1270_);
v_r_1271_ = lean_ctor_get(v___x_1265_, 4);
lean_inc(v_r_1271_);
v___x_1272_ = lean_unsigned_to_nat(3u);
v___x_1273_ = lean_nat_mul(v___x_1272_, v_size_1266_);
v___x_1274_ = lean_nat_dec_lt(v___x_1273_, v_size_1267_);
lean_dec(v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
lean_dec(v_r_1271_);
lean_dec(v_l_1270_);
lean_dec(v_v_1269_);
lean_dec(v_k_1268_);
v___x_1275_ = lean_unsigned_to_nat(1u);
v___x_1276_ = lean_nat_add(v___x_1275_, v_size_1266_);
v___x_1277_ = lean_nat_add(v___x_1276_, v_size_1267_);
lean_dec(v_size_1267_);
lean_dec(v___x_1276_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1265_);
lean_ctor_set(v___x_1261_, 0, v___x_1277_);
v___x_1279_ = v___x_1261_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1280_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1280_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1280_, 4, v___x_1265_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
else
{
lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1350_; 
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; lean_object* v_unused_1352_; lean_object* v_unused_1353_; lean_object* v_unused_1354_; lean_object* v_unused_1355_; 
v_unused_1351_ = lean_ctor_get(v___x_1265_, 4);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v___x_1265_, 3);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v___x_1265_, 2);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v___x_1265_, 1);
lean_dec(v_unused_1354_);
v_unused_1355_ = lean_ctor_get(v___x_1265_, 0);
lean_dec(v_unused_1355_);
v___x_1282_ = v___x_1265_;
v_isShared_1283_ = v_isSharedCheck_1350_;
goto v_resetjp_1281_;
}
else
{
lean_dec(v___x_1265_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1350_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
if (lean_obj_tag(v_l_1270_) == 0)
{
if (lean_obj_tag(v_r_1271_) == 0)
{
lean_object* v_size_1284_; lean_object* v_k_1285_; lean_object* v_v_1286_; lean_object* v_l_1287_; lean_object* v_r_1288_; lean_object* v_size_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v_size_1284_ = lean_ctor_get(v_l_1270_, 0);
v_k_1285_ = lean_ctor_get(v_l_1270_, 1);
v_v_1286_ = lean_ctor_get(v_l_1270_, 2);
v_l_1287_ = lean_ctor_get(v_l_1270_, 3);
v_r_1288_ = lean_ctor_get(v_l_1270_, 4);
v_size_1289_ = lean_ctor_get(v_r_1271_, 0);
v___x_1290_ = lean_unsigned_to_nat(2u);
v___x_1291_ = lean_nat_mul(v___x_1290_, v_size_1289_);
v___x_1292_ = lean_nat_dec_lt(v_size_1284_, v___x_1291_);
lean_dec(v___x_1291_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1321_; 
lean_inc(v_r_1288_);
lean_inc(v_l_1287_);
lean_inc(v_v_1286_);
lean_inc(v_k_1285_);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_l_1270_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; lean_object* v_unused_1323_; lean_object* v_unused_1324_; lean_object* v_unused_1325_; lean_object* v_unused_1326_; 
v_unused_1322_ = lean_ctor_get(v_l_1270_, 4);
lean_dec(v_unused_1322_);
v_unused_1323_ = lean_ctor_get(v_l_1270_, 3);
lean_dec(v_unused_1323_);
v_unused_1324_ = lean_ctor_get(v_l_1270_, 2);
lean_dec(v_unused_1324_);
v_unused_1325_ = lean_ctor_get(v_l_1270_, 1);
lean_dec(v_unused_1325_);
v_unused_1326_ = lean_ctor_get(v_l_1270_, 0);
lean_dec(v_unused_1326_);
v___x_1294_ = v_l_1270_;
v_isShared_1295_ = v_isSharedCheck_1321_;
goto v_resetjp_1293_;
}
else
{
lean_dec(v_l_1270_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1321_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1311_; 
v___x_1296_ = lean_unsigned_to_nat(1u);
v___x_1297_ = lean_nat_add(v___x_1296_, v_size_1266_);
v___x_1298_ = lean_nat_add(v___x_1297_, v_size_1267_);
lean_dec(v_size_1267_);
if (lean_obj_tag(v_l_1287_) == 0)
{
lean_object* v_size_1319_; 
v_size_1319_ = lean_ctor_get(v_l_1287_, 0);
lean_inc(v_size_1319_);
v___y_1311_ = v_size_1319_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_unsigned_to_nat(0u);
v___y_1311_ = v___x_1320_;
goto v___jp_1310_;
}
v___jp_1299_:
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1303_ = lean_nat_add(v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec(v___y_1301_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 4, v_r_1271_);
lean_ctor_set(v___x_1294_, 3, v_r_1288_);
lean_ctor_set(v___x_1294_, 2, v_v_1269_);
lean_ctor_set(v___x_1294_, 1, v_k_1268_);
lean_ctor_set(v___x_1294_, 0, v___x_1303_);
v___x_1305_ = v___x_1294_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_k_1268_);
lean_ctor_set(v_reuseFailAlloc_1309_, 2, v_v_1269_);
lean_ctor_set(v_reuseFailAlloc_1309_, 3, v_r_1288_);
lean_ctor_set(v_reuseFailAlloc_1309_, 4, v_r_1271_);
v___x_1305_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1307_; 
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 4, v___x_1305_);
lean_ctor_set(v___x_1282_, 3, v___y_1300_);
lean_ctor_set(v___x_1282_, 2, v_v_1286_);
lean_ctor_set(v___x_1282_, 1, v_k_1285_);
lean_ctor_set(v___x_1282_, 0, v___x_1298_);
v___x_1307_ = v___x_1282_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_k_1285_);
lean_ctor_set(v_reuseFailAlloc_1308_, 2, v_v_1286_);
lean_ctor_set(v_reuseFailAlloc_1308_, 3, v___y_1300_);
lean_ctor_set(v_reuseFailAlloc_1308_, 4, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
v___jp_1310_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = lean_nat_add(v___x_1297_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec(v___x_1297_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_l_1287_);
lean_ctor_set(v___x_1261_, 0, v___x_1312_);
v___x_1314_ = v___x_1261_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1318_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1318_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1318_, 4, v_l_1287_);
v___x_1314_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_nat_add(v___x_1296_, v_size_1289_);
if (lean_obj_tag(v_r_1288_) == 0)
{
lean_object* v_size_1316_; 
v_size_1316_ = lean_ctor_get(v_r_1288_, 0);
lean_inc(v_size_1316_);
v___y_1300_ = v___x_1314_;
v___y_1301_ = v___x_1315_;
v___y_1302_ = v_size_1316_;
goto v___jp_1299_;
}
else
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_unsigned_to_nat(0u);
v___y_1300_ = v___x_1314_;
v___y_1301_ = v___x_1315_;
v___y_1302_ = v___x_1317_;
goto v___jp_1299_;
}
}
}
}
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
lean_del_object(v___x_1261_);
v___x_1327_ = lean_unsigned_to_nat(1u);
v___x_1328_ = lean_nat_add(v___x_1327_, v_size_1266_);
v___x_1329_ = lean_nat_add(v___x_1328_, v_size_1267_);
lean_dec(v_size_1267_);
v___x_1330_ = lean_nat_add(v___x_1328_, v_size_1284_);
lean_dec(v___x_1328_);
lean_inc_ref(v_l_1258_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 4, v_l_1270_);
lean_ctor_set(v___x_1282_, 3, v_l_1258_);
lean_ctor_set(v___x_1282_, 2, v_v_1257_);
lean_ctor_set(v___x_1282_, 1, v_k_1256_);
lean_ctor_set(v___x_1282_, 0, v___x_1330_);
v___x_1332_ = v___x_1282_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1330_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1345_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1345_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1345_, 4, v_l_1270_);
v___x_1332_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
v_isSharedCheck_1339_ = !lean_is_exclusive(v_l_1258_);
if (v_isSharedCheck_1339_ == 0)
{
lean_object* v_unused_1340_; lean_object* v_unused_1341_; lean_object* v_unused_1342_; lean_object* v_unused_1343_; lean_object* v_unused_1344_; 
v_unused_1340_ = lean_ctor_get(v_l_1258_, 4);
lean_dec(v_unused_1340_);
v_unused_1341_ = lean_ctor_get(v_l_1258_, 3);
lean_dec(v_unused_1341_);
v_unused_1342_ = lean_ctor_get(v_l_1258_, 2);
lean_dec(v_unused_1342_);
v_unused_1343_ = lean_ctor_get(v_l_1258_, 1);
lean_dec(v_unused_1343_);
v_unused_1344_ = lean_ctor_get(v_l_1258_, 0);
lean_dec(v_unused_1344_);
v___x_1334_ = v_l_1258_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_dec(v_l_1258_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 4, v_r_1271_);
lean_ctor_set(v___x_1334_, 3, v___x_1332_);
lean_ctor_set(v___x_1334_, 2, v_v_1269_);
lean_ctor_set(v___x_1334_, 1, v_k_1268_);
lean_ctor_set(v___x_1334_, 0, v___x_1329_);
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_k_1268_);
lean_ctor_set(v_reuseFailAlloc_1338_, 2, v_v_1269_);
lean_ctor_set(v_reuseFailAlloc_1338_, 3, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1338_, 4, v_r_1271_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
else
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_dec_ref(v_l_1270_);
lean_del_object(v___x_1282_);
lean_dec(v_v_1269_);
lean_dec(v_k_1268_);
lean_dec(v_size_1267_);
lean_dec_ref(v_l_1258_);
lean_del_object(v___x_1261_);
lean_dec(v_v_1257_);
lean_dec(v_k_1256_);
v___x_1346_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3);
v___x_1347_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1346_);
return v___x_1347_;
}
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_del_object(v___x_1282_);
lean_dec(v_r_1271_);
lean_dec(v_v_1269_);
lean_dec(v_k_1268_);
lean_dec(v_size_1267_);
lean_dec_ref(v_l_1258_);
lean_del_object(v___x_1261_);
lean_dec(v_v_1257_);
lean_dec(v_k_1256_);
v___x_1348_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4);
v___x_1349_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1348_);
return v___x_1349_;
}
}
}
}
else
{
lean_object* v_size_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
v_size_1356_ = lean_ctor_get(v_l_1258_, 0);
v___x_1357_ = lean_unsigned_to_nat(1u);
v___x_1358_ = lean_nat_add(v___x_1357_, v_size_1356_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1265_);
lean_ctor_set(v___x_1261_, 0, v___x_1358_);
v___x_1360_ = v___x_1261_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1361_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1361_, 4, v___x_1265_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
else
{
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_l_1362_; 
v_l_1362_ = lean_ctor_get(v___x_1265_, 3);
lean_inc(v_l_1362_);
if (lean_obj_tag(v_l_1362_) == 0)
{
lean_object* v_r_1363_; 
v_r_1363_ = lean_ctor_get(v___x_1265_, 4);
lean_inc(v_r_1363_);
if (lean_obj_tag(v_r_1363_) == 0)
{
lean_object* v_size_1364_; lean_object* v_k_1365_; lean_object* v_v_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1380_; 
v_size_1364_ = lean_ctor_get(v___x_1265_, 0);
v_k_1365_ = lean_ctor_get(v___x_1265_, 1);
v_v_1366_ = lean_ctor_get(v___x_1265_, 2);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; lean_object* v_unused_1382_; 
v_unused_1381_ = lean_ctor_get(v___x_1265_, 4);
lean_dec(v_unused_1381_);
v_unused_1382_ = lean_ctor_get(v___x_1265_, 3);
lean_dec(v_unused_1382_);
v___x_1368_ = v___x_1265_;
v_isShared_1369_ = v_isSharedCheck_1380_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_v_1366_);
lean_inc(v_k_1365_);
lean_inc(v_size_1364_);
lean_dec(v___x_1265_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1380_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v_size_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v_size_1370_ = lean_ctor_get(v_l_1362_, 0);
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_add(v___x_1371_, v_size_1364_);
lean_dec(v_size_1364_);
v___x_1373_ = lean_nat_add(v___x_1371_, v_size_1370_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 4, v_l_1362_);
lean_ctor_set(v___x_1368_, 3, v_l_1258_);
lean_ctor_set(v___x_1368_, 2, v_v_1257_);
lean_ctor_set(v___x_1368_, 1, v_k_1256_);
lean_ctor_set(v___x_1368_, 0, v___x_1373_);
v___x_1375_ = v___x_1368_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1379_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1379_, 4, v_l_1362_);
v___x_1375_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1377_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_r_1363_);
lean_ctor_set(v___x_1261_, 3, v___x_1375_);
lean_ctor_set(v___x_1261_, 2, v_v_1366_);
lean_ctor_set(v___x_1261_, 1, v_k_1365_);
lean_ctor_set(v___x_1261_, 0, v___x_1372_);
v___x_1377_ = v___x_1261_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1378_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1378_, 3, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1378_, 4, v_r_1363_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
else
{
lean_object* v_k_1383_; lean_object* v_v_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1408_; 
v_k_1383_ = lean_ctor_get(v___x_1265_, 1);
v_v_1384_ = lean_ctor_get(v___x_1265_, 2);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1408_ == 0)
{
lean_object* v_unused_1409_; lean_object* v_unused_1410_; lean_object* v_unused_1411_; 
v_unused_1409_ = lean_ctor_get(v___x_1265_, 4);
lean_dec(v_unused_1409_);
v_unused_1410_ = lean_ctor_get(v___x_1265_, 3);
lean_dec(v_unused_1410_);
v_unused_1411_ = lean_ctor_get(v___x_1265_, 0);
lean_dec(v_unused_1411_);
v___x_1386_ = v___x_1265_;
v_isShared_1387_ = v_isSharedCheck_1408_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_v_1384_);
lean_inc(v_k_1383_);
lean_dec(v___x_1265_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1408_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v_k_1388_; lean_object* v_v_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1404_; 
v_k_1388_ = lean_ctor_get(v_l_1362_, 1);
v_v_1389_ = lean_ctor_get(v_l_1362_, 2);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_l_1362_);
if (v_isSharedCheck_1404_ == 0)
{
lean_object* v_unused_1405_; lean_object* v_unused_1406_; lean_object* v_unused_1407_; 
v_unused_1405_ = lean_ctor_get(v_l_1362_, 4);
lean_dec(v_unused_1405_);
v_unused_1406_ = lean_ctor_get(v_l_1362_, 3);
lean_dec(v_unused_1406_);
v_unused_1407_ = lean_ctor_get(v_l_1362_, 0);
lean_dec(v_unused_1407_);
v___x_1391_ = v_l_1362_;
v_isShared_1392_ = v_isSharedCheck_1404_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_v_1389_);
lean_inc(v_k_1388_);
lean_dec(v_l_1362_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1404_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1393_ = lean_unsigned_to_nat(3u);
v___x_1394_ = lean_unsigned_to_nat(1u);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 4, v_r_1363_);
lean_ctor_set(v___x_1391_, 3, v_r_1363_);
lean_ctor_set(v___x_1391_, 2, v_v_1257_);
lean_ctor_set(v___x_1391_, 1, v_k_1256_);
lean_ctor_set(v___x_1391_, 0, v___x_1394_);
v___x_1396_ = v___x_1391_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v_r_1363_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v_r_1363_);
v___x_1396_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1398_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 3, v_r_1363_);
lean_ctor_set(v___x_1386_, 0, v___x_1394_);
v___x_1398_ = v___x_1386_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_k_1383_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_v_1384_);
lean_ctor_set(v_reuseFailAlloc_1402_, 3, v_r_1363_);
lean_ctor_set(v_reuseFailAlloc_1402_, 4, v_r_1363_);
v___x_1398_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1400_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1398_);
lean_ctor_set(v___x_1261_, 3, v___x_1396_);
lean_ctor_set(v___x_1261_, 2, v_v_1389_);
lean_ctor_set(v___x_1261_, 1, v_k_1388_);
lean_ctor_set(v___x_1261_, 0, v___x_1393_);
v___x_1400_ = v___x_1261_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1401_, 3, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1401_, 4, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1412_; 
v_r_1412_ = lean_ctor_get(v___x_1265_, 4);
lean_inc(v_r_1412_);
if (lean_obj_tag(v_r_1412_) == 0)
{
lean_object* v_k_1413_; lean_object* v_v_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1426_; 
v_k_1413_ = lean_ctor_get(v___x_1265_, 1);
v_v_1414_ = lean_ctor_get(v___x_1265_, 2);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; lean_object* v_unused_1428_; lean_object* v_unused_1429_; 
v_unused_1427_ = lean_ctor_get(v___x_1265_, 4);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v___x_1265_, 3);
lean_dec(v_unused_1428_);
v_unused_1429_ = lean_ctor_get(v___x_1265_, 0);
lean_dec(v_unused_1429_);
v___x_1416_ = v___x_1265_;
v_isShared_1417_ = v_isSharedCheck_1426_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_v_1414_);
lean_inc(v_k_1413_);
lean_dec(v___x_1265_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1426_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1418_ = lean_unsigned_to_nat(3u);
v___x_1419_ = lean_unsigned_to_nat(1u);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 4, v_l_1362_);
lean_ctor_set(v___x_1416_, 2, v_v_1257_);
lean_ctor_set(v___x_1416_, 1, v_k_1256_);
lean_ctor_set(v___x_1416_, 0, v___x_1419_);
v___x_1421_ = v___x_1416_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1425_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1425_, 3, v_l_1362_);
lean_ctor_set(v_reuseFailAlloc_1425_, 4, v_l_1362_);
v___x_1421_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1423_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_r_1412_);
lean_ctor_set(v___x_1261_, 3, v___x_1421_);
lean_ctor_set(v___x_1261_, 2, v_v_1414_);
lean_ctor_set(v___x_1261_, 1, v_k_1413_);
lean_ctor_set(v___x_1261_, 0, v___x_1418_);
v___x_1423_ = v___x_1261_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_k_1413_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_v_1414_);
lean_ctor_set(v_reuseFailAlloc_1424_, 3, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1424_, 4, v_r_1412_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = lean_unsigned_to_nat(2u);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1265_);
lean_ctor_set(v___x_1261_, 3, v_r_1412_);
lean_ctor_set(v___x_1261_, 0, v___x_1430_);
v___x_1432_ = v___x_1261_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1433_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1433_, 3, v_r_1412_);
lean_ctor_set(v_reuseFailAlloc_1433_, 4, v___x_1265_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1434_ = lean_unsigned_to_nat(1u);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1265_);
lean_ctor_set(v___x_1261_, 3, v___x_1265_);
lean_ctor_set(v___x_1261_, 0, v___x_1434_);
v___x_1436_ = v___x_1261_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1437_, 3, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1437_, 4, v___x_1265_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v___x_1439_; 
lean_dec(v_v_1257_);
lean_dec(v_k_1256_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 2, v_v_1253_);
lean_ctor_set(v___x_1261_, 1, v_k_1252_);
v___x_1439_ = v___x_1261_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_size_1255_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_k_1252_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_v_1253_);
lean_ctor_set(v_reuseFailAlloc_1440_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1440_, 4, v_r_1259_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
else
{
lean_object* v___x_1441_; 
lean_dec(v_size_1255_);
v___x_1441_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_1252_, v_v_1253_, v_l_1258_);
if (lean_obj_tag(v_r_1259_) == 0)
{
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_size_1442_; lean_object* v_size_1443_; lean_object* v_k_1444_; lean_object* v_v_1445_; lean_object* v_l_1446_; lean_object* v_r_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v_size_1442_ = lean_ctor_get(v_r_1259_, 0);
v_size_1443_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_size_1443_);
v_k_1444_ = lean_ctor_get(v___x_1441_, 1);
lean_inc(v_k_1444_);
v_v_1445_ = lean_ctor_get(v___x_1441_, 2);
lean_inc(v_v_1445_);
v_l_1446_ = lean_ctor_get(v___x_1441_, 3);
lean_inc(v_l_1446_);
v_r_1447_ = lean_ctor_get(v___x_1441_, 4);
lean_inc(v_r_1447_);
v___x_1448_ = lean_unsigned_to_nat(3u);
v___x_1449_ = lean_nat_mul(v___x_1448_, v_size_1442_);
v___x_1450_ = lean_nat_dec_lt(v___x_1449_, v_size_1443_);
lean_dec(v___x_1449_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
lean_dec(v_r_1447_);
lean_dec(v_l_1446_);
lean_dec(v_v_1445_);
lean_dec(v_k_1444_);
v___x_1451_ = lean_unsigned_to_nat(1u);
v___x_1452_ = lean_nat_add(v___x_1451_, v_size_1443_);
lean_dec(v_size_1443_);
v___x_1453_ = lean_nat_add(v___x_1452_, v_size_1442_);
lean_dec(v___x_1452_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 3, v___x_1441_);
lean_ctor_set(v___x_1261_, 0, v___x_1453_);
v___x_1455_ = v___x_1261_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1456_, 3, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1456_, 4, v_r_1259_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
else
{
lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1528_; 
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; lean_object* v_unused_1530_; lean_object* v_unused_1531_; lean_object* v_unused_1532_; lean_object* v_unused_1533_; 
v_unused_1529_ = lean_ctor_get(v___x_1441_, 4);
lean_dec(v_unused_1529_);
v_unused_1530_ = lean_ctor_get(v___x_1441_, 3);
lean_dec(v_unused_1530_);
v_unused_1531_ = lean_ctor_get(v___x_1441_, 2);
lean_dec(v_unused_1531_);
v_unused_1532_ = lean_ctor_get(v___x_1441_, 1);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v___x_1441_, 0);
lean_dec(v_unused_1533_);
v___x_1458_ = v___x_1441_;
v_isShared_1459_ = v_isSharedCheck_1528_;
goto v_resetjp_1457_;
}
else
{
lean_dec(v___x_1441_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1528_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
if (lean_obj_tag(v_l_1446_) == 0)
{
if (lean_obj_tag(v_r_1447_) == 0)
{
lean_object* v_size_1460_; lean_object* v_size_1461_; lean_object* v_k_1462_; lean_object* v_v_1463_; lean_object* v_l_1464_; lean_object* v_r_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v_size_1460_ = lean_ctor_get(v_l_1446_, 0);
v_size_1461_ = lean_ctor_get(v_r_1447_, 0);
v_k_1462_ = lean_ctor_get(v_r_1447_, 1);
v_v_1463_ = lean_ctor_get(v_r_1447_, 2);
v_l_1464_ = lean_ctor_get(v_r_1447_, 3);
v_r_1465_ = lean_ctor_get(v_r_1447_, 4);
v___x_1466_ = lean_unsigned_to_nat(2u);
v___x_1467_ = lean_nat_mul(v___x_1466_, v_size_1460_);
v___x_1468_ = lean_nat_dec_lt(v_size_1461_, v___x_1467_);
lean_dec(v___x_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1498_; 
lean_inc(v_r_1465_);
lean_inc(v_l_1464_);
lean_inc(v_v_1463_);
lean_inc(v_k_1462_);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_r_1447_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; lean_object* v_unused_1500_; lean_object* v_unused_1501_; lean_object* v_unused_1502_; lean_object* v_unused_1503_; 
v_unused_1499_ = lean_ctor_get(v_r_1447_, 4);
lean_dec(v_unused_1499_);
v_unused_1500_ = lean_ctor_get(v_r_1447_, 3);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v_r_1447_, 2);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_r_1447_, 1);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v_r_1447_, 0);
lean_dec(v_unused_1503_);
v___x_1470_ = v_r_1447_;
v_isShared_1471_ = v_isSharedCheck_1498_;
goto v_resetjp_1469_;
}
else
{
lean_dec(v_r_1447_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1498_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___x_1486_; lean_object* v___y_1488_; 
v___x_1472_ = lean_unsigned_to_nat(1u);
v___x_1473_ = lean_nat_add(v___x_1472_, v_size_1443_);
lean_dec(v_size_1443_);
v___x_1474_ = lean_nat_add(v___x_1473_, v_size_1442_);
lean_dec(v___x_1473_);
v___x_1486_ = lean_nat_add(v___x_1472_, v_size_1460_);
if (lean_obj_tag(v_l_1464_) == 0)
{
lean_object* v_size_1496_; 
v_size_1496_ = lean_ctor_get(v_l_1464_, 0);
lean_inc(v_size_1496_);
v___y_1488_ = v_size_1496_;
goto v___jp_1487_;
}
else
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_unsigned_to_nat(0u);
v___y_1488_ = v___x_1497_;
goto v___jp_1487_;
}
v___jp_1475_:
{
lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1479_ = lean_nat_add(v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec(v___y_1477_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 4, v_r_1259_);
lean_ctor_set(v___x_1470_, 3, v_r_1465_);
lean_ctor_set(v___x_1470_, 2, v_v_1257_);
lean_ctor_set(v___x_1470_, 1, v_k_1256_);
lean_ctor_set(v___x_1470_, 0, v___x_1479_);
v___x_1481_ = v___x_1470_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v_r_1465_);
lean_ctor_set(v_reuseFailAlloc_1485_, 4, v_r_1259_);
v___x_1481_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 4, v___x_1481_);
lean_ctor_set(v___x_1458_, 3, v___y_1476_);
lean_ctor_set(v___x_1458_, 2, v_v_1463_);
lean_ctor_set(v___x_1458_, 1, v_k_1462_);
lean_ctor_set(v___x_1458_, 0, v___x_1474_);
v___x_1483_ = v___x_1458_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_k_1462_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_v_1463_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v___y_1476_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
v___jp_1487_:
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1489_ = lean_nat_add(v___x_1486_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec(v___x_1486_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_l_1464_);
lean_ctor_set(v___x_1261_, 3, v_l_1446_);
lean_ctor_set(v___x_1261_, 2, v_v_1445_);
lean_ctor_set(v___x_1261_, 1, v_k_1444_);
lean_ctor_set(v___x_1261_, 0, v___x_1489_);
v___x_1491_ = v___x_1261_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_k_1444_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_v_1445_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v_l_1446_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v_l_1464_);
v___x_1491_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_nat_add(v___x_1472_, v_size_1442_);
if (lean_obj_tag(v_r_1465_) == 0)
{
lean_object* v_size_1493_; 
v_size_1493_ = lean_ctor_get(v_r_1465_, 0);
lean_inc(v_size_1493_);
v___y_1476_ = v___x_1491_;
v___y_1477_ = v___x_1492_;
v___y_1478_ = v_size_1493_;
goto v___jp_1475_;
}
else
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_unsigned_to_nat(0u);
v___y_1476_ = v___x_1491_;
v___y_1477_ = v___x_1492_;
v___y_1478_ = v___x_1494_;
goto v___jp_1475_;
}
}
}
}
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
lean_del_object(v___x_1261_);
v___x_1504_ = lean_unsigned_to_nat(1u);
v___x_1505_ = lean_nat_add(v___x_1504_, v_size_1443_);
lean_dec(v_size_1443_);
v___x_1506_ = lean_nat_add(v___x_1505_, v_size_1442_);
lean_dec(v___x_1505_);
v___x_1507_ = lean_nat_add(v___x_1504_, v_size_1442_);
v___x_1508_ = lean_nat_add(v___x_1507_, v_size_1461_);
lean_dec(v___x_1507_);
lean_inc_ref(v_r_1259_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 4, v_r_1259_);
lean_ctor_set(v___x_1458_, 3, v_r_1447_);
lean_ctor_set(v___x_1458_, 2, v_v_1257_);
lean_ctor_set(v___x_1458_, 1, v_k_1256_);
lean_ctor_set(v___x_1458_, 0, v___x_1508_);
v___x_1510_ = v___x_1458_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_r_1447_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v_r_1259_);
v___x_1510_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
v_isSharedCheck_1517_ = !lean_is_exclusive(v_r_1259_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; lean_object* v_unused_1519_; lean_object* v_unused_1520_; lean_object* v_unused_1521_; lean_object* v_unused_1522_; 
v_unused_1518_ = lean_ctor_get(v_r_1259_, 4);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_r_1259_, 3);
lean_dec(v_unused_1519_);
v_unused_1520_ = lean_ctor_get(v_r_1259_, 2);
lean_dec(v_unused_1520_);
v_unused_1521_ = lean_ctor_get(v_r_1259_, 1);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v_r_1259_, 0);
lean_dec(v_unused_1522_);
v___x_1512_ = v_r_1259_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_dec(v_r_1259_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 4, v___x_1510_);
lean_ctor_set(v___x_1512_, 3, v_l_1446_);
lean_ctor_set(v___x_1512_, 2, v_v_1445_);
lean_ctor_set(v___x_1512_, 1, v_k_1444_);
lean_ctor_set(v___x_1512_, 0, v___x_1506_);
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_k_1444_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_v_1445_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v_l_1446_);
lean_ctor_set(v_reuseFailAlloc_1516_, 4, v___x_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
else
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec_ref(v_l_1446_);
lean_del_object(v___x_1458_);
lean_dec(v_v_1445_);
lean_dec(v_k_1444_);
lean_dec(v_size_1443_);
lean_dec_ref(v_r_1259_);
lean_del_object(v___x_1261_);
lean_dec(v_v_1257_);
lean_dec(v_k_1256_);
v___x_1524_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7);
v___x_1525_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1524_);
return v___x_1525_;
}
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_del_object(v___x_1458_);
lean_dec(v_r_1447_);
lean_dec(v_v_1445_);
lean_dec(v_k_1444_);
lean_dec(v_size_1443_);
lean_dec_ref(v_r_1259_);
lean_del_object(v___x_1261_);
lean_dec(v_v_1257_);
lean_dec(v_k_1256_);
v___x_1526_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8);
v___x_1527_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1526_);
return v___x_1527_;
}
}
}
}
else
{
lean_object* v_size_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v_size_1534_ = lean_ctor_get(v_r_1259_, 0);
v___x_1535_ = lean_unsigned_to_nat(1u);
v___x_1536_ = lean_nat_add(v___x_1535_, v_size_1534_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 3, v___x_1441_);
lean_ctor_set(v___x_1261_, 0, v___x_1536_);
v___x_1538_ = v___x_1261_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_r_1259_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
else
{
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_l_1540_; 
v_l_1540_ = lean_ctor_get(v___x_1441_, 3);
lean_inc(v_l_1540_);
if (lean_obj_tag(v_l_1540_) == 0)
{
lean_object* v_r_1541_; 
v_r_1541_ = lean_ctor_get(v___x_1441_, 4);
lean_inc(v_r_1541_);
if (lean_obj_tag(v_r_1541_) == 0)
{
lean_object* v_size_1542_; lean_object* v_k_1543_; lean_object* v_v_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1558_; 
v_size_1542_ = lean_ctor_get(v___x_1441_, 0);
v_k_1543_ = lean_ctor_get(v___x_1441_, 1);
v_v_1544_ = lean_ctor_get(v___x_1441_, 2);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; lean_object* v_unused_1560_; 
v_unused_1559_ = lean_ctor_get(v___x_1441_, 4);
lean_dec(v_unused_1559_);
v_unused_1560_ = lean_ctor_get(v___x_1441_, 3);
lean_dec(v_unused_1560_);
v___x_1546_ = v___x_1441_;
v_isShared_1547_ = v_isSharedCheck_1558_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_v_1544_);
lean_inc(v_k_1543_);
lean_inc(v_size_1542_);
lean_dec(v___x_1441_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1558_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v_size_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1553_; 
v_size_1548_ = lean_ctor_get(v_r_1541_, 0);
v___x_1549_ = lean_unsigned_to_nat(1u);
v___x_1550_ = lean_nat_add(v___x_1549_, v_size_1542_);
lean_dec(v_size_1542_);
v___x_1551_ = lean_nat_add(v___x_1549_, v_size_1548_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 4, v_r_1259_);
lean_ctor_set(v___x_1546_, 3, v_r_1541_);
lean_ctor_set(v___x_1546_, 2, v_v_1257_);
lean_ctor_set(v___x_1546_, 1, v_k_1256_);
lean_ctor_set(v___x_1546_, 0, v___x_1551_);
v___x_1553_ = v___x_1546_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1557_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1557_, 3, v_r_1541_);
lean_ctor_set(v_reuseFailAlloc_1557_, 4, v_r_1259_);
v___x_1553_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1555_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1553_);
lean_ctor_set(v___x_1261_, 3, v_l_1540_);
lean_ctor_set(v___x_1261_, 2, v_v_1544_);
lean_ctor_set(v___x_1261_, 1, v_k_1543_);
lean_ctor_set(v___x_1261_, 0, v___x_1550_);
v___x_1555_ = v___x_1261_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_k_1543_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v_v_1544_);
lean_ctor_set(v_reuseFailAlloc_1556_, 3, v_l_1540_);
lean_ctor_set(v_reuseFailAlloc_1556_, 4, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
else
{
lean_object* v_k_1561_; lean_object* v_v_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1574_; 
v_k_1561_ = lean_ctor_get(v___x_1441_, 1);
v_v_1562_ = lean_ctor_get(v___x_1441_, 2);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; lean_object* v_unused_1576_; lean_object* v_unused_1577_; 
v_unused_1575_ = lean_ctor_get(v___x_1441_, 4);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v___x_1441_, 3);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v___x_1441_, 0);
lean_dec(v_unused_1577_);
v___x_1564_ = v___x_1441_;
v_isShared_1565_ = v_isSharedCheck_1574_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_v_1562_);
lean_inc(v_k_1561_);
lean_dec(v___x_1441_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1574_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1566_ = lean_unsigned_to_nat(3u);
v___x_1567_ = lean_unsigned_to_nat(1u);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 3, v_r_1541_);
lean_ctor_set(v___x_1564_, 2, v_v_1257_);
lean_ctor_set(v___x_1564_, 1, v_k_1256_);
lean_ctor_set(v___x_1564_, 0, v___x_1567_);
v___x_1569_ = v___x_1564_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1573_, 3, v_r_1541_);
lean_ctor_set(v_reuseFailAlloc_1573_, 4, v_r_1541_);
v___x_1569_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1571_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1569_);
lean_ctor_set(v___x_1261_, 3, v_l_1540_);
lean_ctor_set(v___x_1261_, 2, v_v_1562_);
lean_ctor_set(v___x_1261_, 1, v_k_1561_);
lean_ctor_set(v___x_1261_, 0, v___x_1566_);
v___x_1571_ = v___x_1261_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_k_1561_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_v_1562_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v_l_1540_);
lean_ctor_set(v_reuseFailAlloc_1572_, 4, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
else
{
lean_object* v_r_1578_; 
v_r_1578_ = lean_ctor_get(v___x_1441_, 4);
lean_inc(v_r_1578_);
if (lean_obj_tag(v_r_1578_) == 0)
{
lean_object* v_k_1579_; lean_object* v_v_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1604_; 
v_k_1579_ = lean_ctor_get(v___x_1441_, 1);
v_v_1580_ = lean_ctor_get(v___x_1441_, 2);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1604_ == 0)
{
lean_object* v_unused_1605_; lean_object* v_unused_1606_; lean_object* v_unused_1607_; 
v_unused_1605_ = lean_ctor_get(v___x_1441_, 4);
lean_dec(v_unused_1605_);
v_unused_1606_ = lean_ctor_get(v___x_1441_, 3);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v___x_1441_, 0);
lean_dec(v_unused_1607_);
v___x_1582_ = v___x_1441_;
v_isShared_1583_ = v_isSharedCheck_1604_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_v_1580_);
lean_inc(v_k_1579_);
lean_dec(v___x_1441_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1604_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v_k_1584_; lean_object* v_v_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1600_; 
v_k_1584_ = lean_ctor_get(v_r_1578_, 1);
v_v_1585_ = lean_ctor_get(v_r_1578_, 2);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_r_1578_);
if (v_isSharedCheck_1600_ == 0)
{
lean_object* v_unused_1601_; lean_object* v_unused_1602_; lean_object* v_unused_1603_; 
v_unused_1601_ = lean_ctor_get(v_r_1578_, 4);
lean_dec(v_unused_1601_);
v_unused_1602_ = lean_ctor_get(v_r_1578_, 3);
lean_dec(v_unused_1602_);
v_unused_1603_ = lean_ctor_get(v_r_1578_, 0);
lean_dec(v_unused_1603_);
v___x_1587_ = v_r_1578_;
v_isShared_1588_ = v_isSharedCheck_1600_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_v_1585_);
lean_inc(v_k_1584_);
lean_dec(v_r_1578_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1600_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1589_ = lean_unsigned_to_nat(3u);
v___x_1590_ = lean_unsigned_to_nat(1u);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 4, v_l_1540_);
lean_ctor_set(v___x_1587_, 3, v_l_1540_);
lean_ctor_set(v___x_1587_, 2, v_v_1580_);
lean_ctor_set(v___x_1587_, 1, v_k_1579_);
lean_ctor_set(v___x_1587_, 0, v___x_1590_);
v___x_1592_ = v___x_1587_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_k_1579_);
lean_ctor_set(v_reuseFailAlloc_1599_, 2, v_v_1580_);
lean_ctor_set(v_reuseFailAlloc_1599_, 3, v_l_1540_);
lean_ctor_set(v_reuseFailAlloc_1599_, 4, v_l_1540_);
v___x_1592_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1594_; 
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 4, v_l_1540_);
lean_ctor_set(v___x_1582_, 2, v_v_1257_);
lean_ctor_set(v___x_1582_, 1, v_k_1256_);
lean_ctor_set(v___x_1582_, 0, v___x_1590_);
v___x_1594_ = v___x_1582_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1598_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1598_, 3, v_l_1540_);
lean_ctor_set(v_reuseFailAlloc_1598_, 4, v_l_1540_);
v___x_1594_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1596_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1594_);
lean_ctor_set(v___x_1261_, 3, v___x_1592_);
lean_ctor_set(v___x_1261_, 2, v_v_1585_);
lean_ctor_set(v___x_1261_, 1, v_k_1584_);
lean_ctor_set(v___x_1261_, 0, v___x_1589_);
v___x_1596_ = v___x_1261_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_k_1584_);
lean_ctor_set(v_reuseFailAlloc_1597_, 2, v_v_1585_);
lean_ctor_set(v_reuseFailAlloc_1597_, 3, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1597_, 4, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1610_; 
v___x_1608_ = lean_unsigned_to_nat(2u);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_r_1578_);
lean_ctor_set(v___x_1261_, 3, v___x_1441_);
lean_ctor_set(v___x_1261_, 0, v___x_1608_);
v___x_1610_ = v___x_1261_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v_r_1578_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1612_ = lean_unsigned_to_nat(1u);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1441_);
lean_ctor_set(v___x_1261_, 3, v___x_1441_);
lean_ctor_set(v___x_1261_, 0, v___x_1612_);
v___x_1614_ = v___x_1261_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1612_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v___x_1441_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_unsigned_to_nat(1u);
v___x_1618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
lean_ctor_set(v___x_1618_, 1, v_k_1252_);
lean_ctor_set(v___x_1618_, 2, v_v_1253_);
lean_ctor_set(v___x_1618_, 3, v_t_1254_);
lean_ctor_set(v___x_1618_, 4, v_t_1254_);
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore(lean_object* v_kvs_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v_fst_1639_; lean_object* v_snd_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v_fst_1639_ = lean_ctor_get(v_a_1638_, 0);
v_snd_1640_ = lean_ctor_get(v_a_1638_, 1);
v___x_1641_ = lean_string_utf8_byte_size(v_fst_1639_);
v___x_1642_ = lean_nat_dec_eq(v_snd_1640_, v___x_1641_);
if (v___x_1642_ == 0)
{
uint32_t v___x_1643_; uint32_t v___x_1644_; uint8_t v___x_1645_; 
v___x_1643_ = lean_string_utf8_get_fast(v_fst_1639_, v_snd_1640_);
v___x_1644_ = 34;
v___x_1645_ = lean_uint32_dec_eq(v___x_1643_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_dec(v_kvs_1637_);
v___x_1646_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__1));
v___x_1647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1647_, 0, v_a_1638_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
return v___x_1647_;
}
else
{
lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1751_; 
lean_inc(v_snd_1640_);
lean_inc(v_fst_1639_);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_a_1638_);
if (v_isSharedCheck_1751_ == 0)
{
lean_object* v_unused_1752_; lean_object* v_unused_1753_; 
v_unused_1752_ = lean_ctor_get(v_a_1638_, 1);
lean_dec(v_unused_1752_);
v_unused_1753_ = lean_ctor_get(v_a_1638_, 0);
lean_dec(v_unused_1753_);
v___x_1649_ = v_a_1638_;
v_isShared_1650_ = v_isSharedCheck_1751_;
goto v_resetjp_1648_;
}
else
{
lean_dec(v_a_1638_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1751_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = lean_string_utf8_next_fast(v_fst_1639_, v_snd_1640_);
lean_dec(v_snd_1640_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 1, v___x_1651_);
v___x_1653_ = v___x_1649_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_fst_1639_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_1655_ = l_Lean_Json_Parser_strCore(v___x_1654_, v___x_1653_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_pos_1656_; lean_object* v_res_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1740_; 
v_pos_1656_ = lean_ctor_get(v___x_1655_, 0);
v_res_1657_ = lean_ctor_get(v___x_1655_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1659_ = v___x_1655_;
v_isShared_1660_ = v_isSharedCheck_1740_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_res_1657_);
lean_inc(v_pos_1656_);
lean_dec(v___x_1655_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1740_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v_fst_1661_; lean_object* v_snd_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1739_; 
v_fst_1661_ = lean_ctor_get(v_pos_1656_, 0);
v_snd_1662_ = lean_ctor_get(v_pos_1656_, 1);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_pos_1656_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1664_ = v_pos_1656_;
v_isShared_1665_ = v_isSharedCheck_1739_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_snd_1662_);
lean_inc(v_fst_1661_);
lean_dec(v_pos_1656_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1739_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1666_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1661_, v_snd_1662_);
lean_inc(v___x_1666_);
lean_inc(v_fst_1661_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 1, v___x_1666_);
v___x_1668_ = v___x_1664_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_fst_1661_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = lean_string_utf8_byte_size(v_fst_1661_);
v___x_1675_ = lean_nat_dec_eq(v___x_1666_, v___x_1674_);
if (v___x_1675_ == 0)
{
if (v___x_1645_ == 0)
{
lean_dec(v___x_1666_);
lean_dec(v_fst_1661_);
lean_dec(v_res_1657_);
lean_dec(v_kvs_1637_);
goto v___jp_1669_;
}
else
{
uint32_t v___x_1676_; uint32_t v___x_1677_; uint8_t v___x_1678_; 
lean_del_object(v___x_1659_);
v___x_1676_ = lean_string_utf8_get_fast(v_fst_1661_, v___x_1666_);
v___x_1677_ = 58;
v___x_1678_ = lean_uint32_dec_eq(v___x_1676_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec(v___x_1666_);
lean_dec(v_fst_1661_);
lean_dec(v_res_1657_);
lean_dec(v_kvs_1637_);
v___x_1679_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__3));
v___x_1680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1668_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
return v___x_1680_;
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_dec_ref(v___x_1668_);
v___x_1681_ = lean_string_utf8_next_fast(v_fst_1661_, v___x_1666_);
lean_dec(v___x_1666_);
v___x_1682_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1661_, v___x_1681_);
v___x_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1683_, 0, v_fst_1661_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = l_Lean_Json_Parser_anyCore(v___x_1683_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_pos_1685_; lean_object* v_res_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1728_; 
v_pos_1685_ = lean_ctor_get(v___x_1684_, 0);
v_res_1686_ = lean_ctor_get(v___x_1684_, 1);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1688_ = v___x_1684_;
v_isShared_1689_ = v_isSharedCheck_1728_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_res_1686_);
lean_inc(v_pos_1685_);
lean_dec(v___x_1684_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1728_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v_fst_1695_; lean_object* v_snd_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
v_fst_1695_ = lean_ctor_get(v_pos_1685_, 0);
v_snd_1696_ = lean_ctor_get(v_pos_1685_, 1);
v___x_1697_ = lean_string_utf8_byte_size(v_fst_1695_);
v___x_1698_ = lean_nat_dec_eq(v_snd_1696_, v___x_1697_);
if (v___x_1698_ == 0)
{
if (v___x_1678_ == 0)
{
lean_dec(v_res_1686_);
lean_dec(v_res_1657_);
lean_dec(v_kvs_1637_);
goto v___jp_1690_;
}
else
{
lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1725_; 
lean_inc(v_snd_1696_);
lean_inc(v_fst_1695_);
lean_del_object(v___x_1688_);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_pos_1685_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; lean_object* v_unused_1727_; 
v_unused_1726_ = lean_ctor_get(v_pos_1685_, 1);
lean_dec(v_unused_1726_);
v_unused_1727_ = lean_ctor_get(v_pos_1685_, 0);
lean_dec(v_unused_1727_);
v___x_1700_ = v_pos_1685_;
v_isShared_1701_ = v_isSharedCheck_1725_;
goto v_resetjp_1699_;
}
else
{
lean_dec(v_pos_1685_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1725_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
uint32_t v___x_1702_; lean_object* v___x_1703_; uint32_t v___x_1704_; uint8_t v___x_1705_; 
v___x_1702_ = lean_string_utf8_get_fast(v_fst_1695_, v_snd_1696_);
v___x_1703_ = lean_string_utf8_next_fast(v_fst_1695_, v_snd_1696_);
lean_dec(v_snd_1696_);
v___x_1704_ = 125;
v___x_1705_ = lean_uint32_dec_eq(v___x_1702_, v___x_1704_);
if (v___x_1705_ == 0)
{
uint32_t v___x_1706_; uint8_t v___x_1707_; 
v___x_1706_ = 44;
v___x_1707_ = lean_uint32_dec_eq(v___x_1702_, v___x_1706_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1709_; 
lean_dec(v_res_1686_);
lean_dec(v_res_1657_);
lean_dec(v_kvs_1637_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v___x_1703_);
v___x_1709_ = v___x_1700_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_fst_1695_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v___x_1703_);
v___x_1709_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__5));
v___x_1711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1709_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
return v___x_1711_;
}
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1713_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1695_, v___x_1703_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v___x_1713_);
v___x_1715_ = v___x_1700_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_fst_1695_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_res_1657_, v_res_1686_, v_kvs_1637_);
v_kvs_1637_ = v___x_1716_;
v_a_1638_ = v___x_1715_;
goto _start;
}
}
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1719_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1695_, v___x_1703_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v___x_1719_);
v___x_1721_ = v___x_1700_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_fst_1695_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_res_1657_, v_res_1686_, v_kvs_1637_);
v___x_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
return v___x_1723_;
}
}
}
}
}
else
{
lean_dec(v_res_1686_);
lean_dec(v_res_1657_);
lean_dec(v_kvs_1637_);
goto v___jp_1690_;
}
v___jp_1690_:
{
lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1691_ = lean_box(0);
if (v_isShared_1689_ == 0)
{
lean_ctor_set_tag(v___x_1688_, 1);
lean_ctor_set(v___x_1688_, 1, v___x_1691_);
v___x_1693_ = v___x_1688_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_pos_1685_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
else
{
lean_object* v_pos_1729_; lean_object* v_err_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v_res_1657_);
lean_dec(v_kvs_1637_);
v_pos_1729_ = lean_ctor_get(v___x_1684_, 0);
v_err_1730_ = lean_ctor_get(v___x_1684_, 1);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1684_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_err_1730_);
lean_inc(v_pos_1729_);
lean_dec(v___x_1684_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_pos_1729_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_err_1730_);
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
}
}
else
{
lean_dec(v___x_1666_);
lean_dec(v_fst_1661_);
lean_dec(v_res_1657_);
lean_dec(v_kvs_1637_);
goto v___jp_1669_;
}
v___jp_1669_:
{
lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1670_ = lean_box(0);
if (v_isShared_1660_ == 0)
{
lean_ctor_set_tag(v___x_1659_, 1);
lean_ctor_set(v___x_1659_, 1, v___x_1670_);
lean_ctor_set(v___x_1659_, 0, v___x_1668_);
v___x_1672_ = v___x_1659_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1741_; lean_object* v_err_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec(v_kvs_1637_);
v_pos_1741_ = lean_ctor_get(v___x_1655_, 0);
v_err_1742_ = lean_ctor_get(v___x_1655_, 1);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1655_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_err_1742_);
lean_inc(v_pos_1741_);
lean_dec(v___x_1655_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_pos_1741_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_err_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec(v_kvs_1637_);
v___x_1754_ = lean_box(0);
v___x_1755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1755_, 0, v_a_1638_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object* v_a_1762_){
_start:
{
uint8_t v___y_1795_; lean_object* v_fst_1798_; lean_object* v_snd_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v_fst_1798_ = lean_ctor_get(v_a_1762_, 0);
v_snd_1799_ = lean_ctor_get(v_a_1762_, 1);
v___x_1800_ = lean_string_utf8_byte_size(v_fst_1798_);
v___x_1801_ = lean_nat_dec_eq(v_snd_1799_, v___x_1800_);
if (v___x_1801_ == 0)
{
uint32_t v___x_1802_; uint32_t v___x_1803_; uint8_t v___x_1804_; 
v___x_1802_ = lean_string_utf8_get_fast(v_fst_1798_, v_snd_1799_);
v___x_1803_ = 91;
v___x_1804_ = lean_uint32_dec_eq(v___x_1802_, v___x_1803_);
if (v___x_1804_ == 0)
{
uint32_t v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = 123;
v___x_1806_ = lean_uint32_dec_eq(v___x_1802_, v___x_1805_);
if (v___x_1806_ == 0)
{
uint32_t v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = 34;
v___x_1808_ = lean_uint32_dec_eq(v___x_1802_, v___x_1807_);
if (v___x_1808_ == 0)
{
uint32_t v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = 102;
v___x_1810_ = lean_uint32_dec_eq(v___x_1802_, v___x_1809_);
if (v___x_1810_ == 0)
{
uint32_t v___x_1811_; uint8_t v___x_1812_; 
v___x_1811_ = 116;
v___x_1812_ = lean_uint32_dec_eq(v___x_1802_, v___x_1811_);
if (v___x_1812_ == 0)
{
uint32_t v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = 110;
v___x_1814_ = lean_uint32_dec_eq(v___x_1802_, v___x_1813_);
if (v___x_1814_ == 0)
{
uint32_t v___x_1815_; uint8_t v___x_1816_; 
v___x_1815_ = 45;
v___x_1816_ = lean_uint32_dec_eq(v___x_1802_, v___x_1815_);
if (v___x_1816_ == 0)
{
uint32_t v___x_1817_; uint8_t v___x_1818_; 
v___x_1817_ = 48;
v___x_1818_ = lean_uint32_dec_le(v___x_1817_, v___x_1802_);
if (v___x_1818_ == 0)
{
v___y_1795_ = v___x_1818_;
goto v___jp_1794_;
}
else
{
uint32_t v___x_1819_; uint8_t v___x_1820_; 
v___x_1819_ = 57;
v___x_1820_ = lean_uint32_dec_le(v___x_1802_, v___x_1819_);
v___y_1795_ = v___x_1820_;
goto v___jp_1794_;
}
}
else
{
goto v___jp_1763_;
}
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__2));
v___x_1822_ = l_Std_Internal_Parsec_String_pstring(v___x_1821_, v_a_1762_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_pos_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1841_; 
v_pos_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1841_ == 0)
{
lean_object* v_unused_1842_; 
v_unused_1842_ = lean_ctor_get(v___x_1822_, 1);
lean_dec(v_unused_1842_);
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1841_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_pos_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1841_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v_fst_1827_; lean_object* v_snd_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1840_; 
v_fst_1827_ = lean_ctor_get(v_pos_1823_, 0);
v_snd_1828_ = lean_ctor_get(v_pos_1823_, 1);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_pos_1823_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1830_ = v_pos_1823_;
v_isShared_1831_ = v_isSharedCheck_1840_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_snd_1828_);
lean_inc(v_fst_1827_);
lean_dec(v_pos_1823_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1840_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1832_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1827_, v_snd_1828_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 1, v___x_1832_);
v___x_1834_ = v___x_1830_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_fst_1827_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1835_ = lean_box(0);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 1, v___x_1835_);
lean_ctor_set(v___x_1825_, 0, v___x_1834_);
v___x_1837_ = v___x_1825_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
else
{
lean_object* v_pos_1843_; lean_object* v_err_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
v_pos_1843_ = lean_ctor_get(v___x_1822_, 0);
v_err_1844_ = lean_ctor_get(v___x_1822_, 1);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1822_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_err_1844_);
lean_inc(v_pos_1843_);
lean_dec(v___x_1822_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_pos_1843_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_err_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__3));
v___x_1853_ = l_Std_Internal_Parsec_String_pstring(v___x_1852_, v_a_1762_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_pos_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1872_; 
v_pos_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1872_ == 0)
{
lean_object* v_unused_1873_; 
v_unused_1873_ = lean_ctor_get(v___x_1853_, 1);
lean_dec(v_unused_1873_);
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1872_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_pos_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1872_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v_fst_1858_; lean_object* v_snd_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1871_; 
v_fst_1858_ = lean_ctor_get(v_pos_1854_, 0);
v_snd_1859_ = lean_ctor_get(v_pos_1854_, 1);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_pos_1854_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1861_ = v_pos_1854_;
v_isShared_1862_ = v_isSharedCheck_1871_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_snd_1859_);
lean_inc(v_fst_1858_);
lean_dec(v_pos_1854_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1871_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1863_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1858_, v_snd_1859_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 1, v___x_1863_);
v___x_1865_ = v___x_1861_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_fst_1858_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1866_; lean_object* v___x_1868_; 
v___x_1866_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1866_, 0, v___x_1812_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 1, v___x_1866_);
lean_ctor_set(v___x_1856_, 0, v___x_1865_);
v___x_1868_ = v___x_1856_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
else
{
lean_object* v_pos_1874_; lean_object* v_err_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
v_pos_1874_ = lean_ctor_get(v___x_1853_, 0);
v_err_1875_ = lean_ctor_get(v___x_1853_, 1);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1853_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_err_1875_);
lean_inc(v_pos_1874_);
lean_dec(v___x_1853_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_pos_1874_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_err_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__4));
v___x_1884_ = l_Std_Internal_Parsec_String_pstring(v___x_1883_, v_a_1762_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_pos_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1903_; 
v_pos_1885_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1903_ == 0)
{
lean_object* v_unused_1904_; 
v_unused_1904_ = lean_ctor_get(v___x_1884_, 1);
lean_dec(v_unused_1904_);
v___x_1887_ = v___x_1884_;
v_isShared_1888_ = v_isSharedCheck_1903_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_pos_1885_);
lean_dec(v___x_1884_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1903_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v_fst_1889_; lean_object* v_snd_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1902_; 
v_fst_1889_ = lean_ctor_get(v_pos_1885_, 0);
v_snd_1890_ = lean_ctor_get(v_pos_1885_, 1);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_pos_1885_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1892_ = v_pos_1885_;
v_isShared_1893_ = v_isSharedCheck_1902_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_snd_1890_);
lean_inc(v_fst_1889_);
lean_dec(v_pos_1885_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1902_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1894_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1889_, v_snd_1890_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 1, v___x_1894_);
v___x_1896_ = v___x_1892_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_fst_1889_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1897_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1897_, 0, v___x_1808_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 1, v___x_1897_);
lean_ctor_set(v___x_1887_, 0, v___x_1896_);
v___x_1899_ = v___x_1887_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
}
else
{
lean_object* v_pos_1905_; lean_object* v_err_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
v_pos_1905_ = lean_ctor_get(v___x_1884_, 0);
v_err_1906_ = lean_ctor_get(v___x_1884_, 1);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1884_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_err_1906_);
lean_inc(v_pos_1905_);
lean_dec(v___x_1884_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_pos_1905_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_err_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
else
{
lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1952_; 
lean_inc(v_snd_1799_);
lean_inc(v_fst_1798_);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_a_1762_);
if (v_isSharedCheck_1952_ == 0)
{
lean_object* v_unused_1953_; lean_object* v_unused_1954_; 
v_unused_1953_ = lean_ctor_get(v_a_1762_, 1);
lean_dec(v_unused_1953_);
v_unused_1954_ = lean_ctor_get(v_a_1762_, 0);
lean_dec(v_unused_1954_);
v___x_1915_ = v_a_1762_;
v_isShared_1916_ = v_isSharedCheck_1952_;
goto v_resetjp_1914_;
}
else
{
lean_dec(v_a_1762_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1952_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; lean_object* v___x_1919_; 
v___x_1917_ = lean_string_utf8_next_fast(v_fst_1798_, v_snd_1799_);
lean_dec(v_snd_1799_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v___x_1917_);
v___x_1919_ = v___x_1915_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_fst_1798_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_1921_ = l_Lean_Json_Parser_strCore(v___x_1920_, v___x_1919_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_pos_1922_; lean_object* v_res_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1941_; 
v_pos_1922_ = lean_ctor_get(v___x_1921_, 0);
v_res_1923_ = lean_ctor_get(v___x_1921_, 1);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1925_ = v___x_1921_;
v_isShared_1926_ = v_isSharedCheck_1941_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_res_1923_);
lean_inc(v_pos_1922_);
lean_dec(v___x_1921_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1941_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v_fst_1927_; lean_object* v_snd_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1940_; 
v_fst_1927_ = lean_ctor_get(v_pos_1922_, 0);
v_snd_1928_ = lean_ctor_get(v_pos_1922_, 1);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_pos_1922_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1930_ = v_pos_1922_;
v_isShared_1931_ = v_isSharedCheck_1940_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_snd_1928_);
lean_inc(v_fst_1927_);
lean_dec(v_pos_1922_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1940_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1927_, v_snd_1928_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 1, v___x_1932_);
v___x_1934_ = v___x_1930_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_fst_1927_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1935_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1935_, 0, v_res_1923_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 1, v___x_1935_);
lean_ctor_set(v___x_1925_, 0, v___x_1934_);
v___x_1937_ = v___x_1925_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v___x_1935_);
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
else
{
lean_object* v_pos_1942_; lean_object* v_err_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
v_pos_1942_ = lean_ctor_get(v___x_1921_, 0);
v_err_1943_ = lean_ctor_get(v___x_1921_, 1);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1921_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_err_1943_);
lean_inc(v_pos_1942_);
lean_dec(v___x_1921_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_pos_1942_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_err_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1997_; 
lean_inc(v_snd_1799_);
lean_inc(v_fst_1798_);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_a_1762_);
if (v_isSharedCheck_1997_ == 0)
{
lean_object* v_unused_1998_; lean_object* v_unused_1999_; 
v_unused_1998_ = lean_ctor_get(v_a_1762_, 1);
lean_dec(v_unused_1998_);
v_unused_1999_ = lean_ctor_get(v_a_1762_, 0);
lean_dec(v_unused_1999_);
v___x_1956_ = v_a_1762_;
v_isShared_1957_ = v_isSharedCheck_1997_;
goto v_resetjp_1955_;
}
else
{
lean_dec(v_a_1762_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1997_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
v___x_1958_ = lean_string_utf8_next_fast(v_fst_1798_, v_snd_1799_);
lean_dec(v_snd_1799_);
v___x_1959_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1798_, v___x_1958_);
lean_inc(v___x_1959_);
lean_inc(v_fst_1798_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v___x_1959_);
v___x_1961_ = v___x_1956_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_fst_1798_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
uint8_t v___y_1963_; uint8_t v___x_1995_; 
v___x_1995_ = lean_nat_dec_eq(v___x_1959_, v___x_1800_);
if (v___x_1995_ == 0)
{
v___y_1963_ = v___x_1806_;
goto v___jp_1962_;
}
else
{
v___y_1963_ = v___x_1804_;
goto v___jp_1962_;
}
v___jp_1962_:
{
if (v___y_1963_ == 0)
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_dec(v___x_1959_);
lean_dec(v_fst_1798_);
v___x_1964_ = lean_box(0);
v___x_1965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1961_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
return v___x_1965_;
}
else
{
uint32_t v___x_1966_; uint32_t v___x_1967_; uint8_t v___x_1968_; 
v___x_1966_ = lean_string_utf8_get_fast(v_fst_1798_, v___x_1959_);
v___x_1967_ = 125;
v___x_1968_ = lean_uint32_dec_eq(v___x_1966_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_dec(v___x_1959_);
lean_dec(v_fst_1798_);
v___x_1969_ = lean_box(1);
v___x_1970_ = l_Lean_Json_Parser_objectCore(v___x_1969_, v___x_1961_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_pos_1971_; lean_object* v_res_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1980_; 
v_pos_1971_ = lean_ctor_get(v___x_1970_, 0);
v_res_1972_ = lean_ctor_get(v___x_1970_, 1);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1974_ = v___x_1970_;
v_isShared_1975_ = v_isSharedCheck_1980_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_res_1972_);
lean_inc(v_pos_1971_);
lean_dec(v___x_1970_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1980_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1976_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1976_, 0, v_res_1972_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 1, v___x_1976_);
v___x_1978_ = v___x_1974_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_pos_1971_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
else
{
lean_object* v_pos_1981_; lean_object* v_err_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
v_pos_1981_ = lean_ctor_get(v___x_1970_, 0);
v_err_1982_ = lean_ctor_get(v___x_1970_, 1);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1970_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_err_1982_);
lean_inc(v_pos_1981_);
lean_dec(v___x_1970_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_pos_1981_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_err_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
lean_dec_ref(v___x_1961_);
v___x_1990_ = lean_string_utf8_next_fast(v_fst_1798_, v___x_1959_);
lean_dec(v___x_1959_);
v___x_1991_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1798_, v___x_1990_);
v___x_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1992_, 0, v_fst_1798_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__5));
v___x_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
return v___x_1994_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2042_; 
lean_inc(v_snd_1799_);
lean_inc(v_fst_1798_);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_a_1762_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; lean_object* v_unused_2044_; 
v_unused_2043_ = lean_ctor_get(v_a_1762_, 1);
lean_dec(v_unused_2043_);
v_unused_2044_ = lean_ctor_get(v_a_1762_, 0);
lean_dec(v_unused_2044_);
v___x_2001_ = v_a_1762_;
v_isShared_2002_ = v_isSharedCheck_2042_;
goto v_resetjp_2000_;
}
else
{
lean_dec(v_a_1762_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2042_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_2003_ = lean_string_utf8_next_fast(v_fst_1798_, v_snd_1799_);
lean_dec(v_snd_1799_);
v___x_2004_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1798_, v___x_2003_);
lean_inc(v___x_2004_);
lean_inc(v_fst_1798_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 1, v___x_2004_);
v___x_2006_ = v___x_2001_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_fst_1798_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
uint8_t v___x_2010_; 
v___x_2010_ = lean_nat_dec_eq(v___x_2004_, v___x_1800_);
if (v___x_2010_ == 0)
{
if (v___x_1804_ == 0)
{
lean_dec(v___x_2004_);
lean_dec(v_fst_1798_);
goto v___jp_2007_;
}
else
{
uint32_t v___x_2011_; uint32_t v___x_2012_; uint8_t v___x_2013_; 
v___x_2011_ = lean_string_utf8_get_fast(v_fst_1798_, v___x_2004_);
v___x_2012_ = 93;
v___x_2013_ = lean_uint32_dec_eq(v___x_2011_, v___x_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
lean_dec(v___x_2004_);
lean_dec(v_fst_1798_);
v___x_2014_ = lean_unsigned_to_nat(4u);
v___x_2015_ = lean_mk_empty_array_with_capacity(v___x_2014_);
v___x_2016_ = l_Lean_Json_Parser_arrayCore(v___x_2015_, v___x_2006_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_pos_2017_; lean_object* v_res_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2026_; 
v_pos_2017_ = lean_ctor_get(v___x_2016_, 0);
v_res_2018_ = lean_ctor_get(v___x_2016_, 1);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2020_ = v___x_2016_;
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_res_2018_);
lean_inc(v_pos_2017_);
lean_dec(v___x_2016_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2022_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_res_2018_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 1, v___x_2022_);
v___x_2024_ = v___x_2020_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_pos_2017_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
else
{
lean_object* v_pos_2027_; lean_object* v_err_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
v_pos_2027_ = lean_ctor_get(v___x_2016_, 0);
v_err_2028_ = lean_ctor_get(v___x_2016_, 1);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2016_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_err_2028_);
lean_inc(v_pos_2027_);
lean_dec(v___x_2016_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_pos_2027_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_err_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec_ref(v___x_2006_);
v___x_2036_ = lean_string_utf8_next_fast(v_fst_1798_, v___x_2004_);
lean_dec(v___x_2004_);
v___x_2037_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1798_, v___x_2036_);
v___x_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2038_, 0, v_fst_1798_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__7));
v___x_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2038_);
lean_ctor_set(v___x_2040_, 1, v___x_2039_);
return v___x_2040_;
}
}
}
else
{
lean_dec(v___x_2004_);
lean_dec(v_fst_1798_);
goto v___jp_2007_;
}
v___jp_2007_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_box(0);
v___x_2009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2006_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
return v___x_2009_;
}
}
}
}
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_box(0);
v___x_2046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2046_, 0, v_a_1762_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
return v___x_2046_;
}
v___jp_1763_:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Json_Parser_num(v_a_1762_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_pos_1765_; lean_object* v_res_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1784_; 
v_pos_1765_ = lean_ctor_get(v___x_1764_, 0);
v_res_1766_ = lean_ctor_get(v___x_1764_, 1);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1768_ = v___x_1764_;
v_isShared_1769_ = v_isSharedCheck_1784_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_res_1766_);
lean_inc(v_pos_1765_);
lean_dec(v___x_1764_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1784_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v_fst_1770_; lean_object* v_snd_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1783_; 
v_fst_1770_ = lean_ctor_get(v_pos_1765_, 0);
v_snd_1771_ = lean_ctor_get(v_pos_1765_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_pos_1765_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1773_ = v_pos_1765_;
v_isShared_1774_ = v_isSharedCheck_1783_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_snd_1771_);
lean_inc(v_fst_1770_);
lean_dec(v_pos_1765_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1783_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1770_, v_snd_1771_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 1, v___x_1775_);
v___x_1777_ = v___x_1773_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_fst_1770_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1778_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_res_1766_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 1, v___x_1778_);
lean_ctor_set(v___x_1768_, 0, v___x_1777_);
v___x_1780_ = v___x_1768_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v___x_1778_);
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
}
else
{
lean_object* v_pos_1785_; lean_object* v_err_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_pos_1785_ = lean_ctor_get(v___x_1764_, 0);
v_err_1786_ = lean_ctor_get(v___x_1764_, 1);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1764_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_err_1786_);
lean_inc(v_pos_1785_);
lean_dec(v___x_1764_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_pos_1785_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_err_1786_);
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
v___jp_1794_:
{
if (v___y_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__1));
v___x_1797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1797_, 0, v_a_1762_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
return v___x_1797_;
}
else
{
goto v___jp_1763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore(lean_object* v_acc_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_Json_Parser_anyCore(v_a_2048_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_pos_2050_; lean_object* v_res_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2095_; 
v_pos_2050_ = lean_ctor_get(v___x_2049_, 0);
v_res_2051_ = lean_ctor_get(v___x_2049_, 1);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2053_ = v___x_2049_;
v_isShared_2054_ = v_isSharedCheck_2095_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_res_2051_);
lean_inc(v_pos_2050_);
lean_dec(v___x_2049_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2095_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v_fst_2055_; lean_object* v_snd_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v_fst_2055_ = lean_ctor_get(v_pos_2050_, 0);
v_snd_2056_ = lean_ctor_get(v_pos_2050_, 1);
v___x_2057_ = lean_string_utf8_byte_size(v_fst_2055_);
v___x_2058_ = lean_nat_dec_eq(v_snd_2056_, v___x_2057_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2088_; 
lean_inc(v_snd_2056_);
lean_inc(v_fst_2055_);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_pos_2050_);
if (v_isSharedCheck_2088_ == 0)
{
lean_object* v_unused_2089_; lean_object* v_unused_2090_; 
v_unused_2089_ = lean_ctor_get(v_pos_2050_, 1);
lean_dec(v_unused_2089_);
v_unused_2090_ = lean_ctor_get(v_pos_2050_, 0);
lean_dec(v_unused_2090_);
v___x_2060_ = v_pos_2050_;
v_isShared_2061_ = v_isSharedCheck_2088_;
goto v_resetjp_2059_;
}
else
{
lean_dec(v_pos_2050_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2088_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; uint32_t v___x_2063_; lean_object* v___x_2064_; uint32_t v___x_2065_; uint8_t v___x_2066_; 
v___x_2062_ = lean_array_push(v_acc_2047_, v_res_2051_);
v___x_2063_ = lean_string_utf8_get_fast(v_fst_2055_, v_snd_2056_);
v___x_2064_ = lean_string_utf8_next_fast(v_fst_2055_, v_snd_2056_);
lean_dec(v_snd_2056_);
v___x_2065_ = 93;
v___x_2066_ = lean_uint32_dec_eq(v___x_2063_, v___x_2065_);
if (v___x_2066_ == 0)
{
uint32_t v___x_2067_; uint8_t v___x_2068_; 
v___x_2067_ = 44;
v___x_2068_ = lean_uint32_dec_eq(v___x_2063_, v___x_2067_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2070_; 
lean_dec_ref(v___x_2062_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 1, v___x_2064_);
v___x_2070_ = v___x_2060_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_fst_2055_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v___x_2064_);
v___x_2070_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2071_ = ((lean_object*)(l_Lean_Json_Parser_arrayCore___closed__1));
if (v_isShared_2054_ == 0)
{
lean_ctor_set_tag(v___x_2053_, 1);
lean_ctor_set(v___x_2053_, 1, v___x_2071_);
lean_ctor_set(v___x_2053_, 0, v___x_2070_);
v___x_2073_ = v___x_2053_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
lean_del_object(v___x_2053_);
v___x_2076_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2055_, v___x_2064_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 1, v___x_2076_);
v___x_2078_ = v___x_2060_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_fst_2055_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
v_acc_2047_ = v___x_2062_;
v_a_2048_ = v___x_2078_;
goto _start;
}
}
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2055_, v___x_2064_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 1, v___x_2081_);
v___x_2083_ = v___x_2060_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_fst_2055_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2085_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v___x_2062_);
lean_ctor_set(v___x_2053_, 0, v___x_2083_);
v___x_2085_ = v___x_2053_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v___x_2062_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
lean_dec(v_res_2051_);
lean_dec_ref(v_acc_2047_);
v___x_2091_ = lean_box(0);
if (v_isShared_2054_ == 0)
{
lean_ctor_set_tag(v___x_2053_, 1);
lean_ctor_set(v___x_2053_, 1, v___x_2091_);
v___x_2093_ = v___x_2053_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_pos_2050_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
else
{
lean_object* v_pos_2096_; lean_object* v_err_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref(v_acc_2047_);
v_pos_2096_ = lean_ctor_get(v___x_2049_, 0);
v_err_2097_ = lean_ctor_get(v___x_2049_, 1);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2049_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_err_2097_);
lean_inc(v_pos_2096_);
lean_dec(v___x_2049_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_pos_2096_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_err_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2(lean_object* v_00_u03b2_2105_, lean_object* v_msg_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v_msg_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2(lean_object* v_00_u03b2_2108_, lean_object* v_k_2109_, lean_object* v_v_2110_, lean_object* v_t_2111_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_2109_, v_v_2110_, v_t_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_any(lean_object* v_a_2116_){
_start:
{
lean_object* v_fst_2117_; lean_object* v_snd_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2142_; 
v_fst_2117_ = lean_ctor_get(v_a_2116_, 0);
v_snd_2118_ = lean_ctor_get(v_a_2116_, 1);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_a_2116_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2120_ = v_a_2116_;
v_isShared_2121_ = v_isSharedCheck_2142_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_snd_2118_);
lean_inc(v_fst_2117_);
lean_dec(v_a_2116_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2142_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2122_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2117_, v_snd_2118_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 1, v___x_2122_);
v___x_2124_ = v___x_2120_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_fst_2117_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_Json_Parser_anyCore(v___x_2124_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_pos_2126_; lean_object* v_fst_2127_; lean_object* v_snd_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
v_pos_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_pos_2126_);
v_fst_2127_ = lean_ctor_get(v_pos_2126_, 0);
v_snd_2128_ = lean_ctor_get(v_pos_2126_, 1);
v___x_2129_ = lean_string_utf8_byte_size(v_fst_2127_);
v___x_2130_ = lean_nat_dec_eq(v_snd_2128_, v___x_2129_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2138_; 
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2138_ == 0)
{
lean_object* v_unused_2139_; lean_object* v_unused_2140_; 
v_unused_2139_ = lean_ctor_get(v___x_2125_, 1);
lean_dec(v_unused_2139_);
v_unused_2140_ = lean_ctor_get(v___x_2125_, 0);
lean_dec(v_unused_2140_);
v___x_2132_ = v___x_2125_;
v_isShared_2133_ = v_isSharedCheck_2138_;
goto v_resetjp_2131_;
}
else
{
lean_dec(v___x_2125_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2138_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2134_ = ((lean_object*)(l_Lean_Json_Parser_any___closed__1));
if (v_isShared_2133_ == 0)
{
lean_ctor_set_tag(v___x_2132_, 1);
lean_ctor_set(v___x_2132_, 1, v___x_2134_);
v___x_2136_ = v___x_2132_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_pos_2126_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
else
{
lean_dec(v_pos_2126_);
return v___x_2125_;
}
}
else
{
return v___x_2125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parse(lean_object* v_s_2143_){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
v___x_2145_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_2144_, v_s_2143_);
return v___x_2145_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Json_Parser(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
