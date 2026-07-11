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
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint32_t lean_uint32_sub(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
uint8_t lean_string_compare(lean_object*, lean_object*);
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
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
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
lean_object* v___y_66_; lean_object* v___y_70_; uint8_t v___y_71_; lean_object* v_fst_154_; lean_object* v_snd_155_; lean_object* v___y_157_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_fst_154_ = lean_ctor_get(v_a_64_, 0);
v_snd_155_ = lean_ctor_get(v_a_64_, 1);
v___x_167_ = lean_string_utf8_byte_size(v_fst_154_);
v___x_168_ = lean_nat_dec_eq(v_snd_155_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_197_; 
lean_inc(v_snd_155_);
lean_inc(v_fst_154_);
v_isSharedCheck_197_ = !lean_is_exclusive(v_a_64_);
if (v_isSharedCheck_197_ == 0)
{
lean_object* v_unused_198_; lean_object* v_unused_199_; 
v_unused_198_ = lean_ctor_get(v_a_64_, 1);
lean_dec(v_unused_198_);
v_unused_199_ = lean_ctor_get(v_a_64_, 0);
lean_dec(v_unused_199_);
v___x_170_ = v_a_64_;
v_isShared_171_ = v_isSharedCheck_197_;
goto v_resetjp_169_;
}
else
{
lean_dec(v_a_64_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_197_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
uint32_t v_c_172_; lean_object* v___x_173_; lean_object* v_it_x27_188_; uint32_t v___x_189_; uint8_t v___x_190_; uint8_t v___x_191_; 
v_c_172_ = lean_string_utf8_get_fast(v_fst_154_, v_snd_155_);
v___x_173_ = lean_string_utf8_next_fast(v_fst_154_, v_snd_155_);
lean_dec(v_snd_155_);
lean_inc(v_fst_154_);
v_it_x27_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_188_, 0, v_fst_154_);
lean_ctor_set(v_it_x27_188_, 1, v___x_173_);
v___x_189_ = 92;
v___x_190_ = lean_uint32_dec_eq(v_c_172_, v___x_189_);
v___x_191_ = lean_bool_not(v___x_190_);
if (v___x_191_ == 0)
{
uint8_t v___x_192_; 
v___x_192_ = lean_nat_dec_eq(v___x_173_, v___x_167_);
if (v___x_192_ == 0)
{
lean_dec_ref_known(v_it_x27_188_, 2);
goto v___jp_174_;
}
else
{
if (v___x_191_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_del_object(v___x_170_);
lean_dec(v_fst_154_);
v___x_193_ = lean_box(0);
v___x_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_194_, 0, v_it_x27_188_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
return v___x_194_;
}
else
{
lean_dec_ref_known(v_it_x27_188_, 2);
goto v___jp_174_;
}
}
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_del_object(v___x_170_);
lean_dec(v_fst_154_);
v___x_195_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_196_, 0, v_it_x27_188_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
return v___x_196_;
}
v___jp_174_:
{
uint32_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_175_ = lean_string_utf8_get_fast(v_fst_154_, v___x_173_);
v___x_176_ = lean_string_utf8_next_fast(v_fst_154_, v___x_173_);
lean_inc(v_fst_154_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v___x_176_);
v___x_178_ = v___x_170_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_fst_154_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_176_);
v___x_178_ = v_reuseFailAlloc_187_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
uint32_t v___x_179_; uint8_t v___x_180_; uint8_t v___x_181_; 
v___x_179_ = 117;
v___x_180_ = lean_uint32_dec_eq(v___x_175_, v___x_179_);
v___x_181_ = lean_bool_not(v___x_180_);
if (v___x_181_ == 0)
{
uint8_t v___x_182_; 
v___x_182_ = lean_nat_dec_eq(v___x_176_, v___x_167_);
if (v___x_182_ == 0)
{
lean_dec_ref(v___x_178_);
v___y_157_ = v___x_176_;
goto v___jp_156_;
}
else
{
if (v___x_181_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_fst_154_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_178_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
return v___x_184_;
}
else
{
lean_dec_ref(v___x_178_);
v___y_157_ = v___x_176_;
goto v___jp_156_;
}
}
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v_fst_154_);
v___x_185_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_178_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
return v___x_186_;
}
}
}
}
}
else
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_box(0);
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v_a_64_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
return v___x_201_;
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
v___jp_69_:
{
if (v___y_71_ == 0)
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Json_Parser_hexChar(v___y_70_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_pos_73_; lean_object* v_res_74_; lean_object* v___x_75_; 
v_pos_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_pos_73_);
v_res_74_ = lean_ctor_get(v___x_72_, 1);
lean_inc(v_res_74_);
lean_dec_ref_known(v___x_72_, 2);
v___x_75_ = l_Lean_Json_Parser_hexChar(v_pos_73_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_pos_76_; lean_object* v_res_77_; lean_object* v___x_78_; 
v_pos_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_pos_76_);
v_res_77_ = lean_ctor_get(v___x_75_, 1);
lean_inc(v_res_77_);
lean_dec_ref_known(v___x_75_, 2);
v___x_78_ = l_Lean_Json_Parser_hexChar(v_pos_76_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_pos_79_; lean_object* v_res_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_124_; 
v_pos_79_ = lean_ctor_get(v___x_78_, 0);
v_res_80_ = lean_ctor_get(v___x_78_, 1);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_124_ == 0)
{
v___x_82_ = v___x_78_;
v_isShared_83_ = v_isSharedCheck_124_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_res_80_);
lean_inc(v_pos_79_);
lean_dec(v___x_78_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_124_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
uint16_t v___x_84_; uint16_t v___x_85_; uint16_t v___x_86_; uint16_t v___x_87_; uint16_t v___x_88_; uint16_t v___x_89_; uint16_t v___x_90_; uint16_t v___x_91_; uint16_t v___x_92_; uint16_t v___x_93_; uint8_t v___x_94_; 
v___x_84_ = 8;
v___x_85_ = lean_unbox(v_res_74_);
lean_dec(v_res_74_);
v___x_86_ = lean_uint16_shift_left(v___x_85_, v___x_84_);
v___x_87_ = 4;
v___x_88_ = lean_unbox(v_res_77_);
lean_dec(v_res_77_);
v___x_89_ = lean_uint16_shift_left(v___x_88_, v___x_87_);
v___x_90_ = lean_uint16_lor(v___x_86_, v___x_89_);
v___x_91_ = lean_unbox(v_res_80_);
lean_dec(v_res_80_);
v___x_92_ = lean_uint16_lor(v___x_90_, v___x_91_);
v___x_93_ = 3072;
v___x_94_ = lean_uint16_dec_lt(v___x_92_, v___x_93_);
if (v___x_94_ == 0)
{
uint32_t v___x_95_; uint32_t v___x_96_; uint32_t v___x_97_; uint32_t v___x_98_; uint32_t v___x_99_; uint32_t v___x_100_; uint32_t v___x_101_; uint32_t v___x_102_; uint32_t v___x_103_; uint32_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_95_ = lean_uint16_to_uint32(v_low_63_);
v___x_96_ = 1023;
v___x_97_ = lean_uint32_land(v___x_95_, v___x_96_);
v___x_98_ = 10;
v___x_99_ = lean_uint32_shift_left(v___x_97_, v___x_98_);
v___x_100_ = lean_uint16_to_uint32(v___x_92_);
v___x_101_ = lean_uint32_land(v___x_100_, v___x_96_);
v___x_102_ = lean_uint32_lor(v___x_99_, v___x_101_);
v___x_103_ = 65536;
v___x_104_ = lean_uint32_add(v___x_102_, v___x_103_);
v___x_105_ = lean_uint32_to_nat(v___x_104_);
v___x_106_ = lean_unsigned_to_nat(55296u);
v___x_107_ = lean_nat_dec_lt(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(57343u);
v___x_109_ = lean_nat_dec_lt(v___x_108_, v___x_105_);
if (v___x_109_ == 0)
{
lean_dec(v___x_105_);
lean_del_object(v___x_82_);
v___y_66_ = v_pos_79_;
goto v___jp_65_;
}
else
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(1114112u);
v___x_111_ = lean_nat_dec_lt(v___x_105_, v___x_110_);
lean_dec(v___x_105_);
if (v___x_111_ == 0)
{
lean_del_object(v___x_82_);
v___y_66_ = v_pos_79_;
goto v___jp_65_;
}
else
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = lean_box_uint32(v___x_104_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 1, v___x_112_);
v___x_114_ = v___x_82_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_pos_79_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
else
{
lean_object* v___x_116_; lean_object* v___x_118_; 
lean_dec(v___x_105_);
v___x_116_ = lean_box_uint32(v___x_104_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 1, v___x_116_);
v___x_118_ = v___x_82_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_pos_79_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
else
{
lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_120_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
if (v_isShared_83_ == 0)
{
lean_ctor_set_tag(v___x_82_, 1);
lean_ctor_set(v___x_82_, 1, v___x_120_);
v___x_122_ = v___x_82_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_pos_79_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
else
{
lean_object* v_pos_125_; lean_object* v_err_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_133_; 
lean_dec(v_res_77_);
lean_dec(v_res_74_);
v_pos_125_ = lean_ctor_get(v___x_78_, 0);
v_err_126_ = lean_ctor_get(v___x_78_, 1);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_133_ == 0)
{
v___x_128_ = v___x_78_;
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_err_126_);
lean_inc(v_pos_125_);
lean_dec(v___x_78_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_pos_125_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_err_126_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
else
{
lean_object* v_pos_134_; lean_object* v_err_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
lean_dec(v_res_74_);
v_pos_134_ = lean_ctor_get(v___x_75_, 0);
v_err_135_ = lean_ctor_get(v___x_75_, 1);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_142_ == 0)
{
v___x_137_ = v___x_75_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_err_135_);
lean_inc(v_pos_134_);
lean_dec(v___x_75_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_pos_134_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_err_135_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
else
{
lean_object* v_pos_143_; lean_object* v_err_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
v_pos_143_ = lean_ctor_get(v___x_72_, 0);
v_err_144_ = lean_ctor_get(v___x_72_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_72_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_err_144_);
lean_inc(v_pos_143_);
lean_dec(v___x_72_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_pos_143_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_err_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_153_, 0, v___y_70_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
return v___x_153_;
}
}
v___jp_156_:
{
uint32_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint32_t v___x_161_; uint8_t v___x_162_; uint8_t v___x_163_; 
v___x_158_ = lean_string_utf8_get_fast(v_fst_154_, v___y_157_);
v___x_159_ = lean_string_utf8_next_fast(v_fst_154_, v___y_157_);
lean_dec(v___y_157_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v_fst_154_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = 100;
v___x_162_ = lean_uint32_dec_eq(v___x_158_, v___x_161_);
v___x_163_ = lean_bool_not(v___x_162_);
if (v___x_163_ == 0)
{
v___y_70_ = v___x_160_;
v___y_71_ = v___x_163_;
goto v___jp_69_;
}
else
{
uint32_t v___x_164_; uint8_t v___x_165_; uint8_t v___x_166_; 
v___x_164_ = 68;
v___x_165_ = lean_uint32_dec_eq(v___x_158_, v___x_164_);
v___x_166_ = lean_bool_not(v___x_165_);
v___y_70_ = v___x_160_;
v___y_71_ = v___x_166_;
goto v___jp_69_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair___boxed(lean_object* v_low_202_, lean_object* v_a_203_){
_start:
{
uint16_t v_low_boxed_204_; lean_object* v_res_205_; 
v_low_boxed_204_ = lean_unbox(v_low_202_);
v_res_205_ = l_Lean_Json_Parser_finishSurrogatePair(v_low_boxed_204_, v_a_203_);
return v_res_205_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_209_; lean_object* v___x_210_; 
v___x_209_ = 65533;
v___x_210_ = lean_box_uint32(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_211_; lean_object* v___x_212_; 
v___x_211_ = 9;
v___x_212_ = lean_box_uint32(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_213_; lean_object* v___x_214_; 
v___x_213_ = 13;
v___x_214_ = lean_box_uint32(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_215_; lean_object* v___x_216_; 
v___x_215_ = 10;
v___x_216_ = lean_box_uint32(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_217_; lean_object* v___x_218_; 
v___x_217_ = 12;
v___x_218_ = lean_box_uint32(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_219_; lean_object* v___x_220_; 
v___x_219_ = 8;
v___x_220_ = lean_box_uint32(v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__7(void){
_start:
{
uint32_t v___x_221_; lean_object* v___x_222_; 
v___x_221_ = 47;
v___x_222_ = lean_box_uint32(v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__8(void){
_start:
{
uint32_t v___x_223_; lean_object* v___x_224_; 
v___x_223_ = 34;
v___x_224_ = lean_box_uint32(v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__9(void){
_start:
{
uint32_t v___x_225_; lean_object* v___x_226_; 
v___x_225_ = 92;
v___x_226_ = lean_box_uint32(v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar(lean_object* v_a_227_){
_start:
{
lean_object* v_fst_228_; lean_object* v_snd_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_fst_228_ = lean_ctor_get(v_a_227_, 0);
v_snd_229_ = lean_ctor_get(v_a_227_, 1);
v___x_230_ = lean_string_utf8_byte_size(v_fst_228_);
v___x_231_ = lean_nat_dec_eq(v_snd_229_, v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_386_; 
lean_inc(v_snd_229_);
lean_inc(v_fst_228_);
v_isSharedCheck_386_ = !lean_is_exclusive(v_a_227_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; lean_object* v_unused_388_; 
v_unused_387_ = lean_ctor_get(v_a_227_, 1);
lean_dec(v_unused_387_);
v_unused_388_ = lean_ctor_get(v_a_227_, 0);
lean_dec(v_unused_388_);
v___x_233_ = v_a_227_;
v_isShared_234_ = v_isSharedCheck_386_;
goto v_resetjp_232_;
}
else
{
lean_dec(v_a_227_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_386_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
uint32_t v_c_235_; lean_object* v___x_236_; lean_object* v_it_x27_238_; 
v_c_235_ = lean_string_utf8_get_fast(v_fst_228_, v_snd_229_);
v___x_236_ = lean_string_utf8_next_fast(v_fst_228_, v_snd_229_);
lean_dec(v_snd_229_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_236_);
v_it_x27_238_ = v___x_233_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_fst_228_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v___x_236_);
v_it_x27_238_ = v_reuseFailAlloc_385_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
uint32_t v___x_239_; uint8_t v___x_240_; 
v___x_239_ = 92;
v___x_240_ = lean_uint32_dec_eq(v_c_235_, v___x_239_);
if (v___x_240_ == 0)
{
uint32_t v___x_241_; uint8_t v___x_242_; 
v___x_241_ = 34;
v___x_242_ = lean_uint32_dec_eq(v_c_235_, v___x_241_);
if (v___x_242_ == 0)
{
uint32_t v___x_243_; uint8_t v___x_244_; 
v___x_243_ = 47;
v___x_244_ = lean_uint32_dec_eq(v_c_235_, v___x_243_);
if (v___x_244_ == 0)
{
uint32_t v___x_245_; uint8_t v___x_246_; 
v___x_245_ = 98;
v___x_246_ = lean_uint32_dec_eq(v_c_235_, v___x_245_);
if (v___x_246_ == 0)
{
uint32_t v___x_247_; uint8_t v___x_248_; 
v___x_247_ = 102;
v___x_248_ = lean_uint32_dec_eq(v_c_235_, v___x_247_);
if (v___x_248_ == 0)
{
uint32_t v___x_249_; uint8_t v___x_250_; 
v___x_249_ = 110;
v___x_250_ = lean_uint32_dec_eq(v_c_235_, v___x_249_);
if (v___x_250_ == 0)
{
uint32_t v___x_251_; uint8_t v___x_252_; 
v___x_251_ = 114;
v___x_252_ = lean_uint32_dec_eq(v_c_235_, v___x_251_);
if (v___x_252_ == 0)
{
uint32_t v___x_253_; uint8_t v___x_254_; 
v___x_253_ = 116;
v___x_254_ = lean_uint32_dec_eq(v_c_235_, v___x_253_);
if (v___x_254_ == 0)
{
uint32_t v___x_255_; uint8_t v___x_256_; 
v___x_255_ = 117;
v___x_256_ = lean_uint32_dec_eq(v_c_235_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l_Lean_Json_Parser_escapedChar___closed__1));
v___x_258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_258_, 0, v_it_x27_238_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
return v___x_258_;
}
else
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_Json_Parser_hexChar(v_it_x27_238_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_pos_260_; lean_object* v_res_261_; lean_object* v___x_262_; 
v_pos_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_pos_260_);
v_res_261_ = lean_ctor_get(v___x_259_, 1);
lean_inc(v_res_261_);
lean_dec_ref_known(v___x_259_, 2);
v___x_262_ = l_Lean_Json_Parser_hexChar(v_pos_260_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_pos_263_; lean_object* v_res_264_; lean_object* v___x_265_; 
v_pos_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_pos_263_);
v_res_264_ = lean_ctor_get(v___x_262_, 1);
lean_inc(v_res_264_);
lean_dec_ref_known(v___x_262_, 2);
v___x_265_ = l_Lean_Json_Parser_hexChar(v_pos_263_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_pos_266_; lean_object* v_res_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_341_; 
v_pos_266_ = lean_ctor_get(v___x_265_, 0);
v_res_267_ = lean_ctor_get(v___x_265_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_341_ == 0)
{
v___x_269_ = v___x_265_;
v_isShared_270_ = v_isSharedCheck_341_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_res_267_);
lean_inc(v_pos_266_);
lean_dec(v___x_265_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_341_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Json_Parser_hexChar(v_pos_266_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_pos_272_; lean_object* v_res_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_331_; 
v_pos_272_ = lean_ctor_get(v___x_271_, 0);
v_res_273_ = lean_ctor_get(v___x_271_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_331_ == 0)
{
v___x_275_ = v___x_271_;
v_isShared_276_ = v_isSharedCheck_331_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_res_273_);
lean_inc(v_pos_272_);
lean_dec(v___x_271_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_331_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___y_278_; lean_object* v_pos_279_; uint16_t v___x_287_; uint16_t v___x_288_; uint16_t v___x_289_; uint16_t v___x_290_; uint16_t v___x_291_; uint16_t v___x_292_; uint16_t v___x_293_; uint16_t v___x_294_; uint16_t v___x_295_; uint16_t v___x_296_; uint16_t v___x_297_; uint16_t v___x_298_; uint16_t v___x_299_; uint16_t v___x_300_; uint8_t v___x_301_; 
v___x_287_ = 12;
v___x_288_ = lean_unbox(v_res_261_);
lean_dec(v_res_261_);
v___x_289_ = lean_uint16_shift_left(v___x_288_, v___x_287_);
v___x_290_ = 8;
v___x_291_ = lean_unbox(v_res_264_);
lean_dec(v_res_264_);
v___x_292_ = lean_uint16_shift_left(v___x_291_, v___x_290_);
v___x_293_ = lean_uint16_lor(v___x_289_, v___x_292_);
v___x_294_ = 4;
v___x_295_ = lean_unbox(v_res_267_);
lean_dec(v_res_267_);
v___x_296_ = lean_uint16_shift_left(v___x_295_, v___x_294_);
v___x_297_ = lean_uint16_lor(v___x_293_, v___x_296_);
v___x_298_ = lean_unbox(v_res_273_);
lean_dec(v_res_273_);
v___x_299_ = lean_uint16_lor(v___x_297_, v___x_298_);
v___x_300_ = 55296;
v___x_301_ = lean_uint16_dec_lt(v___x_299_, v___x_300_);
if (v___x_301_ == 0)
{
uint16_t v___x_302_; uint8_t v___x_303_; 
v___x_302_ = 57344;
v___x_303_ = lean_uint16_dec_lt(v___x_299_, v___x_302_);
if (v___x_303_ == 0)
{
uint32_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
lean_del_object(v___x_275_);
v___x_304_ = lean_uint16_to_uint32(v___x_299_);
v___x_305_ = lean_box_uint32(v___x_304_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___x_305_);
lean_ctor_set(v___x_269_, 0, v_pos_272_);
v___x_307_ = v___x_269_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_pos_272_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
else
{
uint16_t v___x_309_; uint8_t v___x_310_; 
v___x_309_ = 56320;
v___x_310_ = lean_uint16_dec_lt(v___x_299_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_313_; 
lean_del_object(v___x_275_);
v___x_311_ = l_Lean_Json_Parser_escapedChar___boxed__const__1;
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___x_311_);
lean_ctor_set(v___x_269_, 0, v_pos_272_);
v___x_313_ = v___x_269_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_pos_272_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
else
{
lean_object* v___x_315_; 
lean_del_object(v___x_269_);
lean_inc(v_pos_272_);
v___x_315_ = l_Lean_Json_Parser_finishSurrogatePair(v___x_299_, v_pos_272_);
if (lean_obj_tag(v___x_315_) == 0)
{
if (lean_obj_tag(v___x_315_) == 0)
{
lean_del_object(v___x_275_);
lean_dec(v_pos_272_);
return v___x_315_;
}
else
{
lean_object* v_pos_316_; 
v_pos_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_pos_316_);
v___y_278_ = v___x_315_;
v_pos_279_ = v_pos_316_;
goto v___jp_277_;
}
}
else
{
lean_object* v_err_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
v_err_317_ = lean_ctor_get(v___x_315_, 1);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_324_ == 0)
{
lean_object* v_unused_325_; 
v_unused_325_ = lean_ctor_get(v___x_315_, 0);
lean_dec(v_unused_325_);
v___x_319_ = v___x_315_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_err_317_);
lean_dec(v___x_315_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
lean_inc(v_pos_272_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v_pos_272_);
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_pos_272_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_err_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_inc(v_pos_272_);
v___y_278_ = v___x_322_;
v_pos_279_ = v_pos_272_;
goto v___jp_277_;
}
}
}
}
}
}
else
{
uint32_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
lean_del_object(v___x_275_);
v___x_326_ = lean_uint16_to_uint32(v___x_299_);
v___x_327_ = lean_box_uint32(v___x_326_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___x_327_);
lean_ctor_set(v___x_269_, 0, v_pos_272_);
v___x_329_ = v___x_269_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_pos_272_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
v___jp_277_:
{
lean_object* v_snd_280_; lean_object* v_snd_281_; uint8_t v___x_282_; 
v_snd_280_ = lean_ctor_get(v_pos_272_, 1);
lean_inc(v_snd_280_);
lean_dec(v_pos_272_);
v_snd_281_ = lean_ctor_get(v_pos_279_, 1);
v___x_282_ = lean_nat_dec_eq(v_snd_280_, v_snd_281_);
lean_dec(v_snd_280_);
if (v___x_282_ == 0)
{
lean_dec_ref(v_pos_279_);
lean_del_object(v___x_275_);
return v___y_278_;
}
else
{
lean_object* v___x_283_; lean_object* v___x_285_; 
lean_dec_ref(v___y_278_);
v___x_283_ = l_Lean_Json_Parser_escapedChar___boxed__const__1;
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v___x_283_);
lean_ctor_set(v___x_275_, 0, v_pos_279_);
v___x_285_ = v___x_275_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_pos_279_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
else
{
lean_object* v_pos_332_; lean_object* v_err_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_del_object(v___x_269_);
lean_dec(v_res_267_);
lean_dec(v_res_264_);
lean_dec(v_res_261_);
v_pos_332_ = lean_ctor_get(v___x_271_, 0);
v_err_333_ = lean_ctor_get(v___x_271_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_271_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_err_333_);
lean_inc(v_pos_332_);
lean_dec(v___x_271_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_pos_332_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_err_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
else
{
lean_object* v_pos_342_; lean_object* v_err_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec(v_res_264_);
lean_dec(v_res_261_);
v_pos_342_ = lean_ctor_get(v___x_265_, 0);
v_err_343_ = lean_ctor_get(v___x_265_, 1);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_265_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_err_343_);
lean_inc(v_pos_342_);
lean_dec(v___x_265_);
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
lean_dec(v_res_261_);
v_pos_351_ = lean_ctor_get(v___x_262_, 0);
v_err_352_ = lean_ctor_get(v___x_262_, 1);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_262_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_err_352_);
lean_inc(v_pos_351_);
lean_dec(v___x_262_);
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
else
{
lean_object* v_pos_360_; lean_object* v_err_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
v_pos_360_ = lean_ctor_get(v___x_259_, 0);
v_err_361_ = lean_ctor_get(v___x_259_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_259_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_err_361_);
lean_inc(v_pos_360_);
lean_dec(v___x_259_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_pos_360_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_err_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = l_Lean_Json_Parser_escapedChar___boxed__const__2;
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v_it_x27_238_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
return v___x_370_;
}
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = l_Lean_Json_Parser_escapedChar___boxed__const__3;
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v_it_x27_238_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
return v___x_372_;
}
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = l_Lean_Json_Parser_escapedChar___boxed__const__4;
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v_it_x27_238_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
return v___x_374_;
}
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = l_Lean_Json_Parser_escapedChar___boxed__const__5;
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v_it_x27_238_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
return v___x_376_;
}
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = l_Lean_Json_Parser_escapedChar___boxed__const__6;
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v_it_x27_238_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
return v___x_378_;
}
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = l_Lean_Json_Parser_escapedChar___boxed__const__7;
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v_it_x27_238_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
return v___x_380_;
}
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = l_Lean_Json_Parser_escapedChar___boxed__const__8;
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v_it_x27_238_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
return v___x_382_;
}
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = l_Lean_Json_Parser_escapedChar___boxed__const__9;
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_it_x27_238_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
return v___x_384_;
}
}
}
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_box(0);
v___x_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_390_, 0, v_a_227_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
return v___x_390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_strCore(lean_object* v_acc_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_fst_396_; lean_object* v_snd_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v_fst_396_ = lean_ctor_get(v_a_395_, 0);
v_snd_397_ = lean_ctor_get(v_a_395_, 1);
v___x_398_ = lean_string_utf8_byte_size(v_fst_396_);
v___x_399_ = lean_nat_dec_eq(v_snd_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_442_; 
lean_inc(v_snd_397_);
lean_inc(v_fst_396_);
v_isSharedCheck_442_ = !lean_is_exclusive(v_a_395_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; lean_object* v_unused_444_; 
v_unused_443_ = lean_ctor_get(v_a_395_, 1);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_a_395_, 0);
lean_dec(v_unused_444_);
v___x_401_ = v_a_395_;
v_isShared_402_ = v_isSharedCheck_442_;
goto v_resetjp_400_;
}
else
{
lean_dec(v_a_395_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_442_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
uint32_t v___x_403_; uint32_t v___x_404_; uint8_t v___x_405_; 
v___x_403_ = lean_string_utf8_get_fast(v_fst_396_, v_snd_397_);
v___x_404_ = 34;
v___x_405_ = lean_uint32_dec_eq(v___x_403_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_string_utf8_next_fast(v_fst_396_, v_snd_397_);
lean_dec(v_snd_397_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 1, v___x_406_);
v___x_408_ = v___x_401_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_fst_396_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v___x_406_);
v___x_408_ = v_reuseFailAlloc_436_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
uint8_t v___y_410_; uint32_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = 92;
v___x_416_ = lean_uint32_dec_eq(v___x_403_, v___x_415_);
if (v___x_416_ == 0)
{
uint32_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = 32;
v___x_418_ = lean_uint32_dec_le(v___x_417_, v___x_403_);
if (v___x_418_ == 0)
{
v___y_410_ = v___x_418_;
goto v___jp_409_;
}
else
{
uint32_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 1114111;
v___x_420_ = lean_uint32_dec_le(v___x_403_, v___x_419_);
v___y_410_ = v___x_420_;
goto v___jp_409_;
}
}
else
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Json_Parser_escapedChar(v___x_408_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_pos_422_; lean_object* v_res_423_; uint32_t v___x_424_; lean_object* v___x_425_; 
v_pos_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_pos_422_);
v_res_423_ = lean_ctor_get(v___x_421_, 1);
lean_inc(v_res_423_);
lean_dec_ref_known(v___x_421_, 2);
v___x_424_ = lean_unbox_uint32(v_res_423_);
lean_dec(v_res_423_);
v___x_425_ = lean_string_push(v_acc_394_, v___x_424_);
v_acc_394_ = v___x_425_;
v_a_395_ = v_pos_422_;
goto _start;
}
else
{
lean_object* v_pos_427_; lean_object* v_err_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec_ref(v_acc_394_);
v_pos_427_ = lean_ctor_get(v___x_421_, 0);
v_err_428_ = lean_ctor_get(v___x_421_, 1);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_421_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_err_428_);
lean_inc(v_pos_427_);
lean_dec(v___x_421_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_pos_427_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_err_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
v___jp_409_:
{
if (v___y_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec_ref(v_acc_394_);
v___x_411_ = ((lean_object*)(l_Lean_Json_Parser_strCore___closed__1));
v___x_412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_408_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
return v___x_412_;
}
else
{
lean_object* v___x_413_; 
v___x_413_ = lean_string_push(v_acc_394_, v___x_403_);
v_acc_394_ = v___x_413_;
v_a_395_ = v___x_408_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_437_ = lean_string_utf8_next_fast(v_fst_396_, v_snd_397_);
lean_dec(v_snd_397_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 1, v___x_437_);
v___x_439_ = v___x_401_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_fst_396_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_437_);
v___x_439_ = v_reuseFailAlloc_441_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_440_; 
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v_acc_394_);
return v___x_440_;
}
}
}
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec_ref(v_acc_394_);
v___x_445_ = lean_box(0);
v___x_446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_446_, 0, v_a_395_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_str(lean_object* v_a_447_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_449_ = l_Lean_Json_Parser_strCore(v___x_448_, v_a_447_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCore(lean_object* v_acc_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_fst_452_; lean_object* v_snd_453_; uint32_t v___y_455_; uint32_t v___y_456_; uint8_t v___y_457_; uint8_t v___y_476_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_fst_452_ = lean_ctor_get(v_a_451_, 0);
v_snd_453_ = lean_ctor_get(v_a_451_, 1);
v___x_486_ = lean_string_utf8_byte_size(v_fst_452_);
v___x_487_ = lean_nat_dec_eq(v_snd_453_, v___x_486_);
if (v___x_487_ == 0)
{
uint8_t v___x_488_; 
v___x_488_ = 1;
v___y_476_ = v___x_488_;
goto v___jp_475_;
}
else
{
uint8_t v___x_489_; 
v___x_489_ = 0;
v___y_476_ = v___x_489_;
goto v___jp_475_;
}
v___jp_454_:
{
if (v___y_457_ == 0)
{
lean_object* v___x_458_; 
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v_a_451_);
lean_ctor_set(v___x_458_, 1, v_acc_450_);
return v___x_458_;
}
else
{
lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_472_; 
lean_inc(v_snd_453_);
lean_inc(v_fst_452_);
v_isSharedCheck_472_ = !lean_is_exclusive(v_a_451_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; lean_object* v_unused_474_; 
v_unused_473_ = lean_ctor_get(v_a_451_, 1);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_a_451_, 0);
lean_dec(v_unused_474_);
v___x_460_ = v_a_451_;
v_isShared_461_ = v_isSharedCheck_472_;
goto v_resetjp_459_;
}
else
{
lean_dec(v_a_451_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_472_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = lean_string_utf8_next_fast(v_fst_452_, v_snd_453_);
lean_dec(v_snd_453_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 1, v___x_462_);
v___x_464_ = v___x_460_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_fst_452_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_462_);
v___x_464_ = v_reuseFailAlloc_471_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; uint32_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_465_ = lean_unsigned_to_nat(10u);
v___x_466_ = lean_nat_mul(v___x_465_, v_acc_450_);
lean_dec(v_acc_450_);
v___x_467_ = lean_uint32_sub(v___y_455_, v___y_456_);
v___x_468_ = lean_uint32_to_nat(v___x_467_);
v___x_469_ = lean_nat_add(v___x_466_, v___x_468_);
lean_dec(v___x_468_);
lean_dec(v___x_466_);
v_acc_450_ = v___x_469_;
v_a_451_ = v___x_464_;
goto _start;
}
}
}
}
v___jp_475_:
{
uint8_t v___x_477_; 
v___x_477_ = lean_bool_not(v___y_476_);
if (v___x_477_ == 0)
{
if (v___y_476_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v_acc_450_);
v___x_478_ = lean_box(0);
v___x_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_479_, 0, v_a_451_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
return v___x_479_;
}
else
{
uint32_t v___x_480_; uint32_t v___x_481_; uint8_t v___x_482_; 
v___x_480_ = lean_string_utf8_get_fast(v_fst_452_, v_snd_453_);
v___x_481_ = 48;
v___x_482_ = lean_uint32_dec_le(v___x_481_, v___x_480_);
if (v___x_482_ == 0)
{
v___y_455_ = v___x_480_;
v___y_456_ = v___x_481_;
v___y_457_ = v___x_482_;
goto v___jp_454_;
}
else
{
uint32_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = 57;
v___x_484_ = lean_uint32_dec_le(v___x_480_, v___x_483_);
v___y_455_ = v___x_480_;
v___y_456_ = v___x_481_;
v___y_457_ = v___x_484_;
goto v___jp_454_;
}
}
}
else
{
lean_object* v___x_485_; 
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v_a_451_);
lean_ctor_set(v___x_485_, 1, v_acc_450_);
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCoreNumDigits(lean_object* v_acc_490_, lean_object* v_digits_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_fst_493_; lean_object* v_snd_494_; uint32_t v___y_496_; uint32_t v___y_497_; uint8_t v___y_498_; uint8_t v___y_520_; lean_object* v___x_531_; uint8_t v___x_532_; 
v_fst_493_ = lean_ctor_get(v_a_492_, 0);
v_snd_494_ = lean_ctor_get(v_a_492_, 1);
v___x_531_ = lean_string_utf8_byte_size(v_fst_493_);
v___x_532_ = lean_nat_dec_eq(v_snd_494_, v___x_531_);
if (v___x_532_ == 0)
{
uint8_t v___x_533_; 
v___x_533_ = 1;
v___y_520_ = v___x_533_;
goto v___jp_519_;
}
else
{
uint8_t v___x_534_; 
v___x_534_ = 0;
v___y_520_ = v___x_534_;
goto v___jp_519_;
}
v___jp_495_:
{
if (v___y_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v_acc_490_);
lean_ctor_set(v___x_499_, 1, v_digits_491_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v_a_492_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
return v___x_500_;
}
else
{
lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_516_; 
lean_inc(v_snd_494_);
lean_inc(v_fst_493_);
v_isSharedCheck_516_ = !lean_is_exclusive(v_a_492_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; lean_object* v_unused_518_; 
v_unused_517_ = lean_ctor_get(v_a_492_, 1);
lean_dec(v_unused_517_);
v_unused_518_ = lean_ctor_get(v_a_492_, 0);
lean_dec(v_unused_518_);
v___x_502_ = v_a_492_;
v_isShared_503_ = v_isSharedCheck_516_;
goto v_resetjp_501_;
}
else
{
lean_dec(v_a_492_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_516_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_string_utf8_next_fast(v_fst_493_, v_snd_494_);
lean_dec(v_snd_494_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 1, v___x_504_);
v___x_506_ = v___x_502_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_fst_493_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v___x_504_);
v___x_506_ = v_reuseFailAlloc_515_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; uint32_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_507_ = lean_unsigned_to_nat(10u);
v___x_508_ = lean_nat_mul(v___x_507_, v_acc_490_);
lean_dec(v_acc_490_);
v___x_509_ = lean_uint32_sub(v___y_497_, v___y_496_);
v___x_510_ = lean_uint32_to_nat(v___x_509_);
v___x_511_ = lean_nat_add(v___x_508_, v___x_510_);
lean_dec(v___x_510_);
lean_dec(v___x_508_);
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = lean_nat_add(v_digits_491_, v___x_512_);
lean_dec(v_digits_491_);
v_acc_490_ = v___x_511_;
v_digits_491_ = v___x_513_;
v_a_492_ = v___x_506_;
goto _start;
}
}
}
}
v___jp_519_:
{
uint8_t v___x_521_; 
v___x_521_ = lean_bool_not(v___y_520_);
if (v___x_521_ == 0)
{
if (v___y_520_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec(v_digits_491_);
lean_dec(v_acc_490_);
v___x_522_ = lean_box(0);
v___x_523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_523_, 0, v_a_492_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
return v___x_523_;
}
else
{
uint32_t v___x_524_; uint32_t v___x_525_; uint8_t v___x_526_; 
v___x_524_ = lean_string_utf8_get_fast(v_fst_493_, v_snd_494_);
v___x_525_ = 48;
v___x_526_ = lean_uint32_dec_le(v___x_525_, v___x_524_);
if (v___x_526_ == 0)
{
v___y_496_ = v___x_525_;
v___y_497_ = v___x_524_;
v___y_498_ = v___x_526_;
goto v___jp_495_;
}
else
{
uint32_t v___x_527_; uint8_t v___x_528_; 
v___x_527_ = 57;
v___x_528_ = lean_uint32_dec_le(v___x_524_, v___x_527_);
v___y_496_ = v___x_525_;
v___y_497_ = v___x_524_;
v___y_498_ = v___x_528_;
goto v___jp_495_;
}
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_acc_490_);
lean_ctor_set(v___x_529_, 1, v_digits_491_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_a_492_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg(lean_object* v_desc_536_, lean_object* v_inst_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_fst_539_; lean_object* v_snd_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_fst_539_ = lean_ctor_get(v_a_538_, 0);
v_snd_540_ = lean_ctor_get(v_a_538_, 1);
v___x_541_ = lean_string_utf8_byte_size(v_fst_539_);
v___x_542_ = lean_nat_dec_eq(v_snd_540_, v___x_541_);
if (v___x_542_ == 0)
{
uint32_t v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_543_ = lean_string_utf8_get_fast(v_fst_539_, v_snd_540_);
v___x_544_ = lean_box_uint32(v___x_543_);
v___x_545_ = lean_apply_1(v_inst_537_, v___x_544_);
v___x_546_ = lean_unbox(v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_547_ = ((lean_object*)(l_Lean_Json_Parser_lookahead___redArg___closed__0));
v___x_548_ = lean_string_append(v___x_547_, v_desc_536_);
v___x_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
v___x_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_550_, 0, v_a_538_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_box(0);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v_a_538_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
return v___x_552_;
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec_ref(v_inst_537_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_554_, 0, v_a_538_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg___boxed(lean_object* v_desc_555_, lean_object* v_inst_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Json_Parser_lookahead___redArg(v_desc_555_, v_inst_556_, v_a_557_);
lean_dec_ref(v_desc_555_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead(lean_object* v_p_559_, lean_object* v_desc_560_, lean_object* v_inst_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_fst_563_; lean_object* v_snd_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_fst_563_ = lean_ctor_get(v_a_562_, 0);
v_snd_564_ = lean_ctor_get(v_a_562_, 1);
v___x_565_ = lean_string_utf8_byte_size(v_fst_563_);
v___x_566_ = lean_nat_dec_eq(v_snd_564_, v___x_565_);
if (v___x_566_ == 0)
{
uint32_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_567_ = lean_string_utf8_get_fast(v_fst_563_, v_snd_564_);
v___x_568_ = lean_box_uint32(v___x_567_);
v___x_569_ = lean_apply_1(v_inst_561_, v___x_568_);
v___x_570_ = lean_unbox(v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_571_ = ((lean_object*)(l_Lean_Json_Parser_lookahead___redArg___closed__0));
v___x_572_ = lean_string_append(v___x_571_, v_desc_560_);
v___x_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
v___x_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_574_, 0, v_a_562_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
return v___x_574_;
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_box(0);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v_a_562_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
return v___x_576_;
}
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec_ref(v_inst_561_);
v___x_577_ = lean_box(0);
v___x_578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_578_, 0, v_a_562_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
return v___x_578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___boxed(lean_object* v_p_579_, lean_object* v_desc_580_, lean_object* v_inst_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Json_Parser_lookahead(v_p_579_, v_desc_580_, v_inst_581_, v_a_582_);
lean_dec_ref(v_desc_580_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNonZero(lean_object* v_a_587_){
_start:
{
uint8_t v___y_589_; lean_object* v_fst_594_; lean_object* v_snd_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v_fst_594_ = lean_ctor_get(v_a_587_, 0);
v_snd_595_ = lean_ctor_get(v_a_587_, 1);
v___x_596_ = lean_string_utf8_byte_size(v_fst_594_);
v___x_597_ = lean_nat_dec_eq(v_snd_595_, v___x_596_);
if (v___x_597_ == 0)
{
uint32_t v___x_598_; uint32_t v___x_599_; uint8_t v___x_600_; 
v___x_598_ = lean_string_utf8_get_fast(v_fst_594_, v_snd_595_);
v___x_599_ = 49;
v___x_600_ = lean_uint32_dec_le(v___x_599_, v___x_598_);
if (v___x_600_ == 0)
{
v___y_589_ = v___x_600_;
goto v___jp_588_;
}
else
{
uint32_t v___x_601_; uint8_t v___x_602_; 
v___x_601_ = 57;
v___x_602_ = lean_uint32_dec_le(v___x_598_, v___x_601_);
v___y_589_ = v___x_602_;
goto v___jp_588_;
}
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_box(0);
v___x_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_604_, 0, v_a_587_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
return v___x_604_;
}
v___jp_588_:
{
if (v___y_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_591_, 0, v_a_587_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
return v___x_591_;
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = l_Lean_Json_Parser_natCore(v___x_592_, v_a_587_);
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNumDigits(lean_object* v_a_608_){
_start:
{
uint8_t v___y_610_; lean_object* v_fst_615_; lean_object* v_snd_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_fst_615_ = lean_ctor_get(v_a_608_, 0);
v_snd_616_ = lean_ctor_get(v_a_608_, 1);
v___x_617_ = lean_string_utf8_byte_size(v_fst_615_);
v___x_618_ = lean_nat_dec_eq(v_snd_616_, v___x_617_);
if (v___x_618_ == 0)
{
uint32_t v___x_619_; uint32_t v___x_620_; uint8_t v___x_621_; 
v___x_619_ = lean_string_utf8_get_fast(v_fst_615_, v_snd_616_);
v___x_620_ = 48;
v___x_621_ = lean_uint32_dec_le(v___x_620_, v___x_619_);
if (v___x_621_ == 0)
{
v___y_610_ = v___x_621_;
goto v___jp_609_;
}
else
{
uint32_t v___x_622_; uint8_t v___x_623_; 
v___x_622_ = 57;
v___x_623_ = lean_uint32_dec_le(v___x_619_, v___x_622_);
v___y_610_ = v___x_623_;
goto v___jp_609_;
}
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_box(0);
v___x_625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_625_, 0, v_a_608_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
return v___x_625_;
}
v___jp_609_:
{
if (v___y_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_612_, 0, v_a_608_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
return v___x_612_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_613_, v___x_613_, v_a_608_);
return v___x_614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natMaybeZero(lean_object* v_a_629_){
_start:
{
uint8_t v___y_631_; lean_object* v_fst_636_; lean_object* v_snd_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_fst_636_ = lean_ctor_get(v_a_629_, 0);
v_snd_637_ = lean_ctor_get(v_a_629_, 1);
v___x_638_ = lean_string_utf8_byte_size(v_fst_636_);
v___x_639_ = lean_nat_dec_eq(v_snd_637_, v___x_638_);
if (v___x_639_ == 0)
{
uint32_t v___x_640_; uint32_t v___x_641_; uint8_t v___x_642_; 
v___x_640_ = lean_string_utf8_get_fast(v_fst_636_, v_snd_637_);
v___x_641_ = 48;
v___x_642_ = lean_uint32_dec_le(v___x_641_, v___x_640_);
if (v___x_642_ == 0)
{
v___y_631_ = v___x_642_;
goto v___jp_630_;
}
else
{
uint32_t v___x_643_; uint8_t v___x_644_; 
v___x_643_ = 57;
v___x_644_ = lean_uint32_dec_le(v___x_640_, v___x_643_);
v___y_631_ = v___x_644_;
goto v___jp_630_;
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_box(0);
v___x_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_646_, 0, v_a_629_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
return v___x_646_;
}
v___jp_630_:
{
if (v___y_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_633_, 0, v_a_629_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = l_Lean_Json_Parser_natCore(v___x_634_, v_a_629_);
return v___x_635_;
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_numSign___closed__0(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = lean_nat_to_int(v___x_647_);
return v___x_648_;
}
}
static lean_object* _init_l_Lean_Json_Parser_numSign___closed__1(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v___x_650_ = lean_int_neg(v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numSign(lean_object* v_a_651_){
_start:
{
lean_object* v_fst_652_; lean_object* v_snd_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v_fst_652_ = lean_ctor_get(v_a_651_, 0);
v_snd_653_ = lean_ctor_get(v_a_651_, 1);
v___x_654_ = lean_string_utf8_byte_size(v_fst_652_);
v___x_655_ = lean_nat_dec_eq(v_snd_653_, v___x_654_);
if (v___x_655_ == 0)
{
uint32_t v___x_656_; uint32_t v___x_657_; uint8_t v___x_658_; 
v___x_656_ = lean_string_utf8_get_fast(v_fst_652_, v_snd_653_);
v___x_657_ = 45;
v___x_658_ = lean_uint32_dec_eq(v___x_656_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v_a_651_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
return v___x_660_;
}
else
{
lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_670_; 
lean_inc(v_snd_653_);
lean_inc(v_fst_652_);
v_isSharedCheck_670_ = !lean_is_exclusive(v_a_651_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; lean_object* v_unused_672_; 
v_unused_671_ = lean_ctor_get(v_a_651_, 1);
lean_dec(v_unused_671_);
v_unused_672_ = lean_ctor_get(v_a_651_, 0);
lean_dec(v_unused_672_);
v___x_662_ = v_a_651_;
v_isShared_663_ = v_isSharedCheck_670_;
goto v_resetjp_661_;
}
else
{
lean_dec(v_a_651_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_670_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_664_ = lean_string_utf8_next_fast(v_fst_652_, v_snd_653_);
lean_dec(v_snd_653_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___x_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_fst_652_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_664_);
v___x_666_ = v_reuseFailAlloc_669_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_666_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
return v___x_668_;
}
}
}
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_box(0);
v___x_674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_674_, 0, v_a_651_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_nat(lean_object* v_a_675_){
_start:
{
uint8_t v___y_677_; lean_object* v_fst_682_; lean_object* v_snd_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_fst_682_ = lean_ctor_get(v_a_675_, 0);
v_snd_683_ = lean_ctor_get(v_a_675_, 1);
v___x_684_ = lean_string_utf8_byte_size(v_fst_682_);
v___x_685_ = lean_nat_dec_eq(v_snd_683_, v___x_684_);
if (v___x_685_ == 0)
{
uint32_t v___x_686_; uint32_t v___x_687_; uint8_t v___x_688_; 
v___x_686_ = lean_string_utf8_get_fast(v_fst_682_, v_snd_683_);
v___x_687_ = 48;
v___x_688_ = lean_uint32_dec_eq(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
uint32_t v___x_689_; uint8_t v___x_690_; 
v___x_689_ = 49;
v___x_690_ = lean_uint32_dec_le(v___x_689_, v___x_686_);
if (v___x_690_ == 0)
{
v___y_677_ = v___x_690_;
goto v___jp_676_;
}
else
{
uint32_t v___x_691_; uint8_t v___x_692_; 
v___x_691_ = 57;
v___x_692_ = lean_uint32_dec_le(v___x_686_, v___x_691_);
v___y_677_ = v___x_692_;
goto v___jp_676_;
}
}
else
{
lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_702_; 
lean_inc(v_snd_683_);
lean_inc(v_fst_682_);
v_isSharedCheck_702_ = !lean_is_exclusive(v_a_675_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; lean_object* v_unused_704_; 
v_unused_703_ = lean_ctor_get(v_a_675_, 1);
lean_dec(v_unused_703_);
v_unused_704_ = lean_ctor_get(v_a_675_, 0);
lean_dec(v_unused_704_);
v___x_694_ = v_a_675_;
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
else
{
lean_dec(v_a_675_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = lean_string_utf8_next_fast(v_fst_682_, v_snd_683_);
lean_dec(v_snd_683_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v___x_696_);
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_fst_682_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_696_);
v___x_698_ = v_reuseFailAlloc_701_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
return v___x_700_;
}
}
}
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_box(0);
v___x_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_706_, 0, v_a_675_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
return v___x_706_;
}
v___jp_676_:
{
if (v___y_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_679_, 0, v_a_675_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
return v___x_679_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = l_Lean_Json_Parser_natCore(v___x_680_, v_a_675_);
return v___x_681_;
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_numWithDecimals___closed__0(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = l_System_Platform_numBits;
v___x_708_ = lean_unsigned_to_nat(2u);
v___x_709_ = lean_nat_pow(v___x_708_, v___x_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numWithDecimals(lean_object* v_a_713_){
_start:
{
lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; uint8_t v___y_718_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; uint8_t v___y_770_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; uint8_t v___y_784_; lean_object* v_fst_803_; lean_object* v_snd_804_; lean_object* v___x_805_; uint8_t v___x_806_; lean_object* v___y_808_; lean_object* v_pos_809_; lean_object* v_fst_810_; lean_object* v_snd_811_; lean_object* v_res_812_; lean_object* v___y_817_; lean_object* v___y_818_; uint8_t v___y_819_; lean_object* v_pos_838_; lean_object* v_fst_839_; lean_object* v_snd_840_; lean_object* v_res_841_; 
v_fst_803_ = lean_ctor_get(v_a_713_, 0);
v_snd_804_ = lean_ctor_get(v_a_713_, 1);
v___x_805_ = lean_string_utf8_byte_size(v_fst_803_);
v___x_806_ = lean_nat_dec_eq(v_snd_804_, v___x_805_);
if (v___x_806_ == 0)
{
uint32_t v___x_856_; uint32_t v___x_857_; uint8_t v___x_858_; 
lean_inc(v_snd_804_);
lean_inc(v_fst_803_);
v___x_856_ = lean_string_utf8_get_fast(v_fst_803_, v_snd_804_);
v___x_857_ = 45;
v___x_858_ = lean_uint32_dec_eq(v___x_856_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; 
v___x_859_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v_pos_838_ = v_a_713_;
v_fst_839_ = v_fst_803_;
v_snd_840_ = v_snd_804_;
v_res_841_ = v___x_859_;
goto v___jp_837_;
}
else
{
lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_868_; 
v_isSharedCheck_868_ = !lean_is_exclusive(v_a_713_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; lean_object* v_unused_870_; 
v_unused_869_ = lean_ctor_get(v_a_713_, 1);
lean_dec(v_unused_869_);
v_unused_870_ = lean_ctor_get(v_a_713_, 0);
lean_dec(v_unused_870_);
v___x_861_ = v_a_713_;
v_isShared_862_ = v_isSharedCheck_868_;
goto v_resetjp_860_;
}
else
{
lean_dec(v_a_713_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_868_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_863_ = lean_string_utf8_next_fast(v_fst_803_, v_snd_804_);
lean_dec(v_snd_804_);
lean_inc(v_fst_803_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v___x_863_);
v___x_865_ = v___x_861_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_fst_803_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v___x_863_);
v___x_865_ = v_reuseFailAlloc_867_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_866_; 
v___x_866_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v_pos_838_ = v___x_865_;
v_fst_839_ = v_fst_803_;
v_snd_840_ = v___x_863_;
v_res_841_ = v___x_866_;
goto v___jp_837_;
}
}
}
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_box(0);
v___x_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_872_, 0, v_a_713_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
return v___x_872_;
}
v___jp_714_:
{
if (v___y_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; 
lean_dec(v___y_715_);
v___x_719_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_720_, 0, v___y_716_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_721_, v___x_721_, v___y_716_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_res_723_; lean_object* v_pos_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_754_; 
v_res_723_ = lean_ctor_get(v___x_722_, 1);
v_pos_724_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_754_ == 0)
{
v___x_726_ = v___x_722_;
v_isShared_727_ = v_isSharedCheck_754_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_res_723_);
lean_inc(v_pos_724_);
lean_dec(v___x_722_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_754_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v_fst_728_; lean_object* v_snd_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_753_; 
v_fst_728_ = lean_ctor_get(v_res_723_, 0);
v_snd_729_ = lean_ctor_get(v_res_723_, 1);
v_isSharedCheck_753_ = !lean_is_exclusive(v_res_723_);
if (v_isSharedCheck_753_ == 0)
{
v___x_731_ = v_res_723_;
v_isShared_732_ = v_isSharedCheck_753_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_snd_729_);
lean_inc(v_fst_728_);
lean_dec(v_res_723_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_753_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_734_ = lean_nat_dec_lt(v___x_733_, v_snd_729_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_735_ = lean_nat_to_int(v___y_715_);
v___x_736_ = lean_unsigned_to_nat(10u);
v___x_737_ = lean_nat_pow(v___x_736_, v_snd_729_);
v___x_738_ = lean_nat_to_int(v___x_737_);
v___x_739_ = lean_int_mul(v___x_735_, v___x_738_);
lean_dec(v___x_738_);
lean_dec(v___x_735_);
v___x_740_ = lean_nat_to_int(v_fst_728_);
v___x_741_ = lean_int_add(v___x_739_, v___x_740_);
lean_dec(v___x_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_int_mul(v___y_717_, v___x_741_);
lean_dec(v___x_741_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_742_);
v___x_744_ = v___x_731_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_snd_729_);
v___x_744_ = v_reuseFailAlloc_748_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_746_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v___x_744_);
v___x_746_ = v___x_726_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_pos_724_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
else
{
lean_object* v___x_749_; lean_object* v___x_751_; 
lean_del_object(v___x_731_);
lean_dec(v_snd_729_);
lean_dec(v_fst_728_);
lean_dec(v___y_715_);
v___x_749_ = ((lean_object*)(l_Lean_Json_Parser_numWithDecimals___closed__2));
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 1);
lean_ctor_set(v___x_726_, 1, v___x_749_);
v___x_751_ = v___x_726_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_pos_724_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
else
{
lean_object* v_pos_755_; lean_object* v_err_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v___y_715_);
v_pos_755_ = lean_ctor_get(v___x_722_, 0);
v_err_756_ = lean_ctor_get(v___x_722_, 1);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_722_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_err_756_);
lean_inc(v_pos_755_);
lean_dec(v___x_722_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_pos_755_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_err_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
v___jp_764_:
{
if (v___y_770_ == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec(v___y_768_);
lean_dec(v___y_767_);
lean_dec(v___y_765_);
v___x_771_ = lean_box(0);
v___x_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_772_, 0, v___y_766_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
return v___x_772_;
}
else
{
uint32_t v___x_773_; uint32_t v___x_774_; uint8_t v___x_775_; 
v___x_773_ = lean_string_utf8_get_fast(v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec(v___y_767_);
v___x_774_ = 48;
v___x_775_ = lean_uint32_dec_le(v___x_774_, v___x_773_);
if (v___x_775_ == 0)
{
v___y_715_ = v___y_765_;
v___y_716_ = v___y_766_;
v___y_717_ = v___y_769_;
v___y_718_ = v___x_775_;
goto v___jp_714_;
}
else
{
uint32_t v___x_776_; uint8_t v___x_777_; 
v___x_776_ = 57;
v___x_777_ = lean_uint32_dec_le(v___x_773_, v___x_776_);
v___y_715_ = v___y_765_;
v___y_716_ = v___y_766_;
v___y_717_ = v___y_769_;
v___y_718_ = v___x_777_;
goto v___jp_714_;
}
}
}
v___jp_778_:
{
uint8_t v___x_785_; 
v___x_785_ = lean_bool_not(v___y_784_);
if (v___x_785_ == 0)
{
if (v___y_784_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; 
lean_dec(v___y_781_);
lean_dec(v___y_780_);
lean_dec(v___y_779_);
v___x_786_ = lean_box(0);
v___x_787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_787_, 0, v___y_782_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
return v___x_787_;
}
else
{
uint32_t v___x_788_; uint32_t v___x_789_; uint8_t v___x_790_; 
v___x_788_ = lean_string_utf8_get_fast(v___y_781_, v___y_780_);
v___x_789_ = 46;
v___x_790_ = lean_uint32_dec_eq(v___x_788_, v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
lean_dec(v___y_781_);
lean_dec(v___y_780_);
v___x_791_ = lean_nat_to_int(v___y_779_);
v___x_792_ = lean_int_mul(v___y_783_, v___x_791_);
lean_dec(v___x_791_);
v___x_793_ = l_Lean_JsonNumber_fromInt(v___x_792_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v___y_782_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
return v___x_794_;
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
lean_dec_ref(v___y_782_);
v___x_795_ = lean_string_utf8_next_fast(v___y_781_, v___y_780_);
lean_dec(v___y_780_);
lean_inc(v___y_781_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___y_781_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = lean_string_utf8_byte_size(v___y_781_);
v___x_798_ = lean_nat_dec_eq(v___x_795_, v___x_797_);
if (v___x_798_ == 0)
{
v___y_765_ = v___y_779_;
v___y_766_ = v___x_796_;
v___y_767_ = v___y_781_;
v___y_768_ = v___x_795_;
v___y_769_ = v___y_783_;
v___y_770_ = v___x_790_;
goto v___jp_764_;
}
else
{
v___y_765_ = v___y_779_;
v___y_766_ = v___x_796_;
v___y_767_ = v___y_781_;
v___y_768_ = v___x_795_;
v___y_769_ = v___y_783_;
v___y_770_ = v___x_785_;
goto v___jp_764_;
}
}
}
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec(v___y_781_);
lean_dec(v___y_780_);
v___x_799_ = lean_nat_to_int(v___y_779_);
v___x_800_ = lean_int_mul(v___y_783_, v___x_799_);
lean_dec(v___x_799_);
v___x_801_ = l_Lean_JsonNumber_fromInt(v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v___y_782_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
return v___x_802_;
}
}
v___jp_807_:
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = lean_string_utf8_byte_size(v_fst_810_);
v___x_814_ = lean_nat_dec_eq(v_snd_811_, v___x_813_);
if (v___x_814_ == 0)
{
uint8_t v___x_815_; 
v___x_815_ = 1;
v___y_779_ = v_res_812_;
v___y_780_ = v_snd_811_;
v___y_781_ = v_fst_810_;
v___y_782_ = v_pos_809_;
v___y_783_ = v___y_808_;
v___y_784_ = v___x_815_;
goto v___jp_778_;
}
else
{
v___y_779_ = v_res_812_;
v___y_780_ = v_snd_811_;
v___y_781_ = v_fst_810_;
v___y_782_ = v_pos_809_;
v___y_783_ = v___y_808_;
v___y_784_ = v___x_806_;
goto v___jp_778_;
}
}
v___jp_816_:
{
if (v___y_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_821_, 0, v___y_817_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
return v___x_821_;
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_unsigned_to_nat(0u);
v___x_823_ = l_Lean_Json_Parser_natCore(v___x_822_, v___y_817_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_pos_824_; lean_object* v_res_825_; lean_object* v_fst_826_; lean_object* v_snd_827_; 
v_pos_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_pos_824_);
v_res_825_ = lean_ctor_get(v___x_823_, 1);
lean_inc(v_res_825_);
lean_dec_ref_known(v___x_823_, 2);
v_fst_826_ = lean_ctor_get(v_pos_824_, 0);
lean_inc(v_fst_826_);
v_snd_827_ = lean_ctor_get(v_pos_824_, 1);
lean_inc(v_snd_827_);
v___y_808_ = v___y_818_;
v_pos_809_ = v_pos_824_;
v_fst_810_ = v_fst_826_;
v_snd_811_ = v_snd_827_;
v_res_812_ = v_res_825_;
goto v___jp_807_;
}
else
{
lean_object* v_pos_828_; lean_object* v_err_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_pos_828_ = lean_ctor_get(v___x_823_, 0);
v_err_829_ = lean_ctor_get(v___x_823_, 1);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_823_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_err_829_);
lean_inc(v_pos_828_);
lean_dec(v___x_823_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_pos_828_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_err_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
v___jp_837_:
{
lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_842_ = lean_string_utf8_byte_size(v_fst_839_);
v___x_843_ = lean_nat_dec_eq(v_snd_840_, v___x_842_);
if (v___x_843_ == 0)
{
uint32_t v___x_844_; uint32_t v___x_845_; uint8_t v___x_846_; 
v___x_844_ = lean_string_utf8_get_fast(v_fst_839_, v_snd_840_);
v___x_845_ = 48;
v___x_846_ = lean_uint32_dec_eq(v___x_844_, v___x_845_);
if (v___x_846_ == 0)
{
uint32_t v___x_847_; uint8_t v___x_848_; 
lean_dec(v_snd_840_);
lean_dec(v_fst_839_);
v___x_847_ = 49;
v___x_848_ = lean_uint32_dec_le(v___x_847_, v___x_844_);
if (v___x_848_ == 0)
{
v___y_817_ = v_pos_838_;
v___y_818_ = v_res_841_;
v___y_819_ = v___x_848_;
goto v___jp_816_;
}
else
{
uint32_t v___x_849_; uint8_t v___x_850_; 
v___x_849_ = 57;
v___x_850_ = lean_uint32_dec_le(v___x_844_, v___x_849_);
v___y_817_ = v_pos_838_;
v___y_818_ = v_res_841_;
v___y_819_ = v___x_850_;
goto v___jp_816_;
}
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec_ref(v_pos_838_);
v___x_851_ = lean_string_utf8_next_fast(v_fst_839_, v_snd_840_);
lean_dec(v_snd_840_);
lean_inc(v_fst_839_);
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v_fst_839_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = lean_unsigned_to_nat(0u);
v___y_808_ = v_res_841_;
v_pos_809_ = v___x_852_;
v_fst_810_ = v_fst_839_;
v_snd_811_ = v___x_851_;
v_res_812_ = v___x_853_;
goto v___jp_807_;
}
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec(v_snd_840_);
lean_dec(v_fst_839_);
v___x_854_ = lean_box(0);
v___x_855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_855_, 0, v_pos_838_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
return v___x_855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent(lean_object* v_value_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___y_879_; uint8_t v___y_880_; lean_object* v___y_911_; lean_object* v_fst_912_; lean_object* v_snd_913_; lean_object* v___y_924_; uint8_t v___y_925_; lean_object* v___y_950_; lean_object* v_fst_953_; lean_object* v_snd_954_; uint8_t v___y_989_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v_fst_953_ = lean_ctor_get(v_a_877_, 0);
v_snd_954_ = lean_ctor_get(v_a_877_, 1);
v___x_1000_ = lean_string_utf8_byte_size(v_fst_953_);
v___x_1001_ = lean_nat_dec_eq(v_snd_954_, v___x_1000_);
if (v___x_1001_ == 0)
{
uint8_t v___x_1002_; 
v___x_1002_ = 1;
v___y_989_ = v___x_1002_;
goto v___jp_988_;
}
else
{
uint8_t v___x_1003_; 
v___x_1003_ = 0;
v___y_989_ = v___x_1003_;
goto v___jp_988_;
}
v___jp_878_:
{
if (v___y_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec_ref(v_value_876_);
v___x_881_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_882_, 0, v___y_879_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
return v___x_882_;
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = l_Lean_Json_Parser_natCore(v___x_883_, v___y_879_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_pos_885_; lean_object* v_res_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_900_; 
v_pos_885_ = lean_ctor_get(v___x_884_, 0);
v_res_886_ = lean_ctor_get(v___x_884_, 1);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_900_ == 0)
{
v___x_888_ = v___x_884_;
v_isShared_889_ = v_isSharedCheck_900_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_res_886_);
lean_inc(v_pos_885_);
lean_dec(v___x_884_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_900_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_890_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_891_ = lean_nat_dec_lt(v___x_890_, v_res_886_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = l_Lean_JsonNumber_shiftl(v_value_876_, v_res_886_);
lean_dec(v_res_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v___x_892_);
v___x_894_ = v___x_888_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_pos_885_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
else
{
lean_object* v___x_896_; lean_object* v___x_898_; 
lean_dec(v_res_886_);
lean_dec_ref(v_value_876_);
v___x_896_ = ((lean_object*)(l_Lean_Json_Parser_exponent___closed__1));
if (v_isShared_889_ == 0)
{
lean_ctor_set_tag(v___x_888_, 1);
lean_ctor_set(v___x_888_, 1, v___x_896_);
v___x_898_ = v___x_888_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_pos_885_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_pos_901_; lean_object* v_err_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec_ref(v_value_876_);
v_pos_901_ = lean_ctor_get(v___x_884_, 0);
v_err_902_ = lean_ctor_get(v___x_884_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_884_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_err_902_);
lean_inc(v_pos_901_);
lean_dec(v___x_884_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_pos_901_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_err_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
v___jp_910_:
{
lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_914_ = lean_string_utf8_byte_size(v_fst_912_);
v___x_915_ = lean_nat_dec_eq(v_snd_913_, v___x_914_);
if (v___x_915_ == 0)
{
uint32_t v___x_916_; uint32_t v___x_917_; uint8_t v___x_918_; 
v___x_916_ = lean_string_utf8_get_fast(v_fst_912_, v_snd_913_);
lean_dec(v_snd_913_);
lean_dec(v_fst_912_);
v___x_917_ = 48;
v___x_918_ = lean_uint32_dec_le(v___x_917_, v___x_916_);
if (v___x_918_ == 0)
{
v___y_879_ = v___y_911_;
v___y_880_ = v___x_918_;
goto v___jp_878_;
}
else
{
uint32_t v___x_919_; uint8_t v___x_920_; 
v___x_919_ = 57;
v___x_920_ = lean_uint32_dec_le(v___x_916_, v___x_919_);
v___y_879_ = v___y_911_;
v___y_880_ = v___x_920_;
goto v___jp_878_;
}
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; 
lean_dec(v_snd_913_);
lean_dec(v_fst_912_);
lean_dec_ref(v_value_876_);
v___x_921_ = lean_box(0);
v___x_922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_922_, 0, v___y_911_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
return v___x_922_;
}
}
v___jp_923_:
{
if (v___y_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec_ref(v_value_876_);
v___x_926_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_927_, 0, v___y_924_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
return v___x_927_;
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = l_Lean_Json_Parser_natCore(v___x_928_, v___y_924_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_pos_930_; lean_object* v_res_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_939_; 
v_pos_930_ = lean_ctor_get(v___x_929_, 0);
v_res_931_ = lean_ctor_get(v___x_929_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_939_ == 0)
{
v___x_933_ = v___x_929_;
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_res_931_);
lean_inc(v_pos_930_);
lean_dec(v___x_929_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = l_Lean_JsonNumber_shiftr(v_value_876_, v_res_931_);
lean_dec(v_res_931_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_pos_930_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
else
{
lean_object* v_pos_940_; lean_object* v_err_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v_value_876_);
v_pos_940_ = lean_ctor_get(v___x_929_, 0);
v_err_941_ = lean_ctor_get(v___x_929_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_929_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_err_941_);
lean_inc(v_pos_940_);
lean_dec(v___x_929_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_pos_940_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_err_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
v___jp_949_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_box(0);
v___x_952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_952_, 0, v___y_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
return v___x_952_;
}
v___jp_955_:
{
lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_956_ = lean_string_utf8_byte_size(v_fst_953_);
v___x_957_ = lean_nat_dec_eq(v_snd_954_, v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_983_; 
lean_inc(v_snd_954_);
lean_inc(v_fst_953_);
v_isSharedCheck_983_ = !lean_is_exclusive(v_a_877_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; lean_object* v_unused_985_; 
v_unused_984_ = lean_ctor_get(v_a_877_, 1);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v_a_877_, 0);
lean_dec(v_unused_985_);
v___x_959_ = v_a_877_;
v_isShared_960_ = v_isSharedCheck_983_;
goto v_resetjp_958_;
}
else
{
lean_dec(v_a_877_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_983_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_string_utf8_next_fast(v_fst_953_, v_snd_954_);
lean_dec(v_snd_954_);
lean_inc(v_fst_953_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 1, v___x_961_);
v___x_963_ = v___x_959_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_fst_953_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v___x_961_);
v___x_963_ = v_reuseFailAlloc_982_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
uint8_t v___x_964_; 
v___x_964_ = lean_nat_dec_eq(v___x_961_, v___x_956_);
if (v___x_964_ == 0)
{
uint32_t v___x_965_; uint32_t v___x_966_; uint8_t v___x_967_; 
v___x_965_ = lean_string_utf8_get_fast(v_fst_953_, v___x_961_);
v___x_966_ = 45;
v___x_967_ = lean_uint32_dec_eq(v___x_965_, v___x_966_);
if (v___x_967_ == 0)
{
uint32_t v___x_968_; uint8_t v___x_969_; 
v___x_968_ = 43;
v___x_969_ = lean_uint32_dec_eq(v___x_965_, v___x_968_);
if (v___x_969_ == 0)
{
v___y_911_ = v___x_963_;
v_fst_912_ = v_fst_953_;
v_snd_913_ = v___x_961_;
goto v___jp_910_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec_ref(v___x_963_);
v___x_970_ = lean_string_utf8_next_fast(v_fst_953_, v___x_961_);
lean_inc(v_fst_953_);
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v_fst_953_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___y_911_ = v___x_971_;
v_fst_912_ = v_fst_953_;
v_snd_913_ = v___x_970_;
goto v___jp_910_;
}
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
lean_dec_ref(v___x_963_);
v___x_972_ = lean_string_utf8_next_fast(v_fst_953_, v___x_961_);
lean_inc(v_fst_953_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v_fst_953_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = lean_nat_dec_eq(v___x_972_, v___x_956_);
if (v___x_974_ == 0)
{
if (v___x_967_ == 0)
{
lean_dec(v_fst_953_);
lean_dec_ref(v_value_876_);
v___y_950_ = v___x_973_;
goto v___jp_949_;
}
else
{
uint32_t v___x_975_; uint32_t v___x_976_; uint8_t v___x_977_; 
v___x_975_ = lean_string_utf8_get_fast(v_fst_953_, v___x_972_);
lean_dec(v_fst_953_);
v___x_976_ = 48;
v___x_977_ = lean_uint32_dec_le(v___x_976_, v___x_975_);
if (v___x_977_ == 0)
{
v___y_924_ = v___x_973_;
v___y_925_ = v___x_977_;
goto v___jp_923_;
}
else
{
uint32_t v___x_978_; uint8_t v___x_979_; 
v___x_978_ = 57;
v___x_979_ = lean_uint32_dec_le(v___x_975_, v___x_978_);
v___y_924_ = v___x_973_;
v___y_925_ = v___x_979_;
goto v___jp_923_;
}
}
}
else
{
lean_dec(v_fst_953_);
lean_dec_ref(v_value_876_);
v___y_950_ = v___x_973_;
goto v___jp_949_;
}
}
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; 
lean_dec(v_fst_953_);
lean_dec_ref(v_value_876_);
v___x_980_ = lean_box(0);
v___x_981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_963_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
return v___x_981_;
}
}
}
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec_ref(v_value_876_);
v___x_986_ = lean_box(0);
v___x_987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_987_, 0, v_a_877_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
return v___x_987_;
}
}
v___jp_988_:
{
uint8_t v___x_990_; 
v___x_990_ = lean_bool_not(v___y_989_);
if (v___x_990_ == 0)
{
if (v___y_989_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; 
lean_dec_ref(v_value_876_);
v___x_991_ = lean_box(0);
v___x_992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_992_, 0, v_a_877_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
return v___x_992_;
}
else
{
uint32_t v___x_993_; uint32_t v___x_994_; uint8_t v___x_995_; 
v___x_993_ = lean_string_utf8_get_fast(v_fst_953_, v_snd_954_);
v___x_994_ = 101;
v___x_995_ = lean_uint32_dec_eq(v___x_993_, v___x_994_);
if (v___x_995_ == 0)
{
uint32_t v___x_996_; uint8_t v___x_997_; 
v___x_996_ = 69;
v___x_997_ = lean_uint32_dec_eq(v___x_993_, v___x_996_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; 
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v_a_877_);
lean_ctor_set(v___x_998_, 1, v_value_876_);
return v___x_998_;
}
else
{
goto v___jp_955_;
}
}
else
{
goto v___jp_955_;
}
}
}
else
{
lean_object* v___x_999_; 
v___x_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_999_, 0, v_a_877_);
lean_ctor_set(v___x_999_, 1, v_value_876_);
return v___x_999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Json_Parser_num_spec__0(lean_object* v_a_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_nat_to_int(v_a_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_num(lean_object* v_a_1006_){
_start:
{
lean_object* v___y_1008_; lean_object* v___y_1009_; uint8_t v___y_1010_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v_fst_1043_; lean_object* v_snd_1044_; lean_object* v___y_1055_; lean_object* v___y_1056_; uint8_t v___y_1057_; lean_object* v___y_1082_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; uint8_t v___y_1128_; lean_object* v_fst_1137_; lean_object* v_snd_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; lean_object* v___y_1142_; lean_object* v_pos_1143_; lean_object* v_res_1144_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; uint8_t v___y_1154_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; uint8_t v___y_1206_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; uint8_t v___y_1220_; lean_object* v___y_1240_; lean_object* v_pos_1241_; lean_object* v_fst_1242_; lean_object* v_snd_1243_; lean_object* v_res_1244_; lean_object* v___y_1249_; lean_object* v___y_1250_; uint8_t v___y_1251_; lean_object* v_pos_1270_; lean_object* v_fst_1271_; lean_object* v_snd_1272_; lean_object* v_res_1273_; 
v_fst_1137_ = lean_ctor_get(v_a_1006_, 0);
v_snd_1138_ = lean_ctor_get(v_a_1006_, 1);
v___x_1139_ = lean_string_utf8_byte_size(v_fst_1137_);
v___x_1140_ = lean_nat_dec_eq(v_snd_1138_, v___x_1139_);
if (v___x_1140_ == 0)
{
uint32_t v___x_1288_; uint32_t v___x_1289_; uint8_t v___x_1290_; 
lean_inc(v_snd_1138_);
lean_inc(v_fst_1137_);
v___x_1288_ = lean_string_utf8_get_fast(v_fst_1137_, v_snd_1138_);
v___x_1289_ = 45;
v___x_1290_ = lean_uint32_dec_eq(v___x_1288_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v_pos_1270_ = v_a_1006_;
v_fst_1271_ = v_fst_1137_;
v_snd_1272_ = v_snd_1138_;
v_res_1273_ = v___x_1291_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1300_; 
v_isSharedCheck_1300_ = !lean_is_exclusive(v_a_1006_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; lean_object* v_unused_1302_; 
v_unused_1301_ = lean_ctor_get(v_a_1006_, 1);
lean_dec(v_unused_1301_);
v_unused_1302_ = lean_ctor_get(v_a_1006_, 0);
lean_dec(v_unused_1302_);
v___x_1293_ = v_a_1006_;
v_isShared_1294_ = v_isSharedCheck_1300_;
goto v_resetjp_1292_;
}
else
{
lean_dec(v_a_1006_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1300_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1295_ = lean_string_utf8_next_fast(v_fst_1137_, v_snd_1138_);
lean_dec(v_snd_1138_);
lean_inc(v_fst_1137_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 1, v___x_1295_);
v___x_1297_ = v___x_1293_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_fst_1137_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_object* v___x_1298_; 
v___x_1298_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v_pos_1270_ = v___x_1297_;
v_fst_1271_ = v_fst_1137_;
v_snd_1272_ = v___x_1295_;
v_res_1273_ = v___x_1298_;
goto v___jp_1269_;
}
}
}
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1304_, 0, v_a_1006_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
return v___x_1304_;
}
v___jp_1007_:
{
if (v___y_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec_ref(v___y_1009_);
v___x_1011_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_1012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___y_1008_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
return v___x_1012_;
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = l_Lean_Json_Parser_natCore(v___x_1013_, v___y_1008_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_pos_1015_; lean_object* v_res_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1030_; 
v_pos_1015_ = lean_ctor_get(v___x_1014_, 0);
v_res_1016_ = lean_ctor_get(v___x_1014_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1018_ = v___x_1014_;
v_isShared_1019_ = v_isSharedCheck_1030_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_res_1016_);
lean_inc(v_pos_1015_);
lean_dec(v___x_1014_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1030_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_1021_ = lean_nat_dec_lt(v___x_1020_, v_res_1016_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1022_ = l_Lean_JsonNumber_shiftl(v___y_1009_, v_res_1016_);
lean_dec(v_res_1016_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v___x_1022_);
v___x_1024_ = v___x_1018_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_pos_1015_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v___x_1022_);
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
lean_object* v___x_1026_; lean_object* v___x_1028_; 
lean_dec(v_res_1016_);
lean_dec_ref(v___y_1009_);
v___x_1026_ = ((lean_object*)(l_Lean_Json_Parser_exponent___closed__1));
if (v_isShared_1019_ == 0)
{
lean_ctor_set_tag(v___x_1018_, 1);
lean_ctor_set(v___x_1018_, 1, v___x_1026_);
v___x_1028_ = v___x_1018_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_pos_1015_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_pos_1031_; lean_object* v_err_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref(v___y_1009_);
v_pos_1031_ = lean_ctor_get(v___x_1014_, 0);
v_err_1032_ = lean_ctor_get(v___x_1014_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1014_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_err_1032_);
lean_inc(v_pos_1031_);
lean_dec(v___x_1014_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_pos_1031_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_err_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
v___jp_1040_:
{
lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1045_ = lean_string_utf8_byte_size(v_fst_1043_);
v___x_1046_ = lean_nat_dec_eq(v_snd_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
uint32_t v___x_1047_; uint32_t v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = lean_string_utf8_get_fast(v_fst_1043_, v_snd_1044_);
lean_dec(v_snd_1044_);
lean_dec(v_fst_1043_);
v___x_1048_ = 48;
v___x_1049_ = lean_uint32_dec_le(v___x_1048_, v___x_1047_);
if (v___x_1049_ == 0)
{
v___y_1008_ = v___y_1042_;
v___y_1009_ = v___y_1041_;
v___y_1010_ = v___x_1049_;
goto v___jp_1007_;
}
else
{
uint32_t v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = 57;
v___x_1051_ = lean_uint32_dec_le(v___x_1047_, v___x_1050_);
v___y_1008_ = v___y_1042_;
v___y_1009_ = v___y_1041_;
v___y_1010_ = v___x_1051_;
goto v___jp_1007_;
}
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_dec(v_snd_1044_);
lean_dec(v_fst_1043_);
lean_dec_ref(v___y_1041_);
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___y_1042_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
return v___x_1053_;
}
}
v___jp_1054_:
{
if (v___y_1057_ == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_dec_ref(v___y_1056_);
v___x_1058_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_1059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___y_1055_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = l_Lean_Json_Parser_natCore(v___x_1060_, v___y_1055_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_pos_1062_; lean_object* v_res_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1071_; 
v_pos_1062_ = lean_ctor_get(v___x_1061_, 0);
v_res_1063_ = lean_ctor_get(v___x_1061_, 1);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1065_ = v___x_1061_;
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_res_1063_);
lean_inc(v_pos_1062_);
lean_dec(v___x_1061_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1067_ = l_Lean_JsonNumber_shiftr(v___y_1056_, v_res_1063_);
lean_dec(v_res_1063_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 1, v___x_1067_);
v___x_1069_ = v___x_1065_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_pos_1062_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
else
{
lean_object* v_pos_1072_; lean_object* v_err_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref(v___y_1056_);
v_pos_1072_ = lean_ctor_get(v___x_1061_, 0);
v_err_1073_ = lean_ctor_get(v___x_1061_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1061_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_err_1073_);
lean_inc(v_pos_1072_);
lean_dec(v___x_1061_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_pos_1072_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_err_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
v___jp_1081_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___y_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
return v___x_1084_;
}
v___jp_1085_:
{
lean_object* v_fst_1088_; lean_object* v_snd_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v_fst_1088_ = lean_ctor_get(v___y_1086_, 0);
v_snd_1089_ = lean_ctor_get(v___y_1086_, 1);
v___x_1090_ = lean_string_utf8_byte_size(v_fst_1088_);
v___x_1091_ = lean_nat_dec_eq(v_snd_1089_, v___x_1090_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1117_; 
lean_inc(v_snd_1089_);
lean_inc(v_fst_1088_);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___y_1086_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; lean_object* v_unused_1119_; 
v_unused_1118_ = lean_ctor_get(v___y_1086_, 1);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v___y_1086_, 0);
lean_dec(v_unused_1119_);
v___x_1093_ = v___y_1086_;
v_isShared_1094_ = v_isSharedCheck_1117_;
goto v_resetjp_1092_;
}
else
{
lean_dec(v___y_1086_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1117_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1095_ = lean_string_utf8_next_fast(v_fst_1088_, v_snd_1089_);
lean_dec(v_snd_1089_);
lean_inc(v_fst_1088_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v___x_1095_);
v___x_1097_ = v___x_1093_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_fst_1088_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
uint8_t v___x_1098_; 
v___x_1098_ = lean_nat_dec_eq(v___x_1095_, v___x_1090_);
if (v___x_1098_ == 0)
{
uint32_t v___x_1099_; uint32_t v___x_1100_; uint8_t v___x_1101_; 
v___x_1099_ = lean_string_utf8_get_fast(v_fst_1088_, v___x_1095_);
v___x_1100_ = 45;
v___x_1101_ = lean_uint32_dec_eq(v___x_1099_, v___x_1100_);
if (v___x_1101_ == 0)
{
uint32_t v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = 43;
v___x_1103_ = lean_uint32_dec_eq(v___x_1099_, v___x_1102_);
if (v___x_1103_ == 0)
{
v___y_1041_ = v___y_1087_;
v___y_1042_ = v___x_1097_;
v_fst_1043_ = v_fst_1088_;
v_snd_1044_ = v___x_1095_;
goto v___jp_1040_;
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec_ref(v___x_1097_);
v___x_1104_ = lean_string_utf8_next_fast(v_fst_1088_, v___x_1095_);
lean_inc(v_fst_1088_);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v_fst_1088_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___y_1041_ = v___y_1087_;
v___y_1042_ = v___x_1105_;
v_fst_1043_ = v_fst_1088_;
v_snd_1044_ = v___x_1104_;
goto v___jp_1040_;
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
lean_dec_ref(v___x_1097_);
v___x_1106_ = lean_string_utf8_next_fast(v_fst_1088_, v___x_1095_);
lean_inc(v_fst_1088_);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v_fst_1088_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_nat_dec_eq(v___x_1106_, v___x_1090_);
if (v___x_1108_ == 0)
{
if (v___x_1101_ == 0)
{
lean_dec(v_fst_1088_);
lean_dec_ref(v___y_1087_);
v___y_1082_ = v___x_1107_;
goto v___jp_1081_;
}
else
{
uint32_t v___x_1109_; uint32_t v___x_1110_; uint8_t v___x_1111_; 
v___x_1109_ = lean_string_utf8_get_fast(v_fst_1088_, v___x_1106_);
lean_dec(v_fst_1088_);
v___x_1110_ = 48;
v___x_1111_ = lean_uint32_dec_le(v___x_1110_, v___x_1109_);
if (v___x_1111_ == 0)
{
v___y_1055_ = v___x_1107_;
v___y_1056_ = v___y_1087_;
v___y_1057_ = v___x_1111_;
goto v___jp_1054_;
}
else
{
uint32_t v___x_1112_; uint8_t v___x_1113_; 
v___x_1112_ = 57;
v___x_1113_ = lean_uint32_dec_le(v___x_1109_, v___x_1112_);
v___y_1055_ = v___x_1107_;
v___y_1056_ = v___y_1087_;
v___y_1057_ = v___x_1113_;
goto v___jp_1054_;
}
}
}
else
{
lean_dec(v_fst_1088_);
lean_dec_ref(v___y_1087_);
v___y_1082_ = v___x_1107_;
goto v___jp_1081_;
}
}
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec(v_fst_1088_);
lean_dec_ref(v___y_1087_);
v___x_1114_ = lean_box(0);
v___x_1115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1097_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
return v___x_1115_;
}
}
}
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec_ref(v___y_1087_);
v___x_1120_ = lean_box(0);
v___x_1121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___y_1086_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
return v___x_1121_;
}
}
v___jp_1122_:
{
uint8_t v___x_1129_; 
v___x_1129_ = lean_bool_not(v___y_1128_);
if (v___x_1129_ == 0)
{
if (v___y_1128_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___y_1125_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
return v___x_1131_;
}
else
{
uint32_t v___x_1132_; uint32_t v___x_1133_; uint8_t v___x_1134_; 
v___x_1132_ = lean_string_utf8_get_fast(v___y_1124_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec(v___y_1124_);
v___x_1133_ = 101;
v___x_1134_ = lean_uint32_dec_eq(v___x_1132_, v___x_1133_);
if (v___x_1134_ == 0)
{
uint32_t v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = 69;
v___x_1136_ = lean_uint32_dec_eq(v___x_1132_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_dec_ref(v___y_1126_);
lean_dec_ref(v___y_1125_);
return v___y_1123_;
}
else
{
lean_dec_ref(v___y_1123_);
v___y_1086_ = v___y_1125_;
v___y_1087_ = v___y_1126_;
goto v___jp_1085_;
}
}
else
{
lean_dec_ref(v___y_1123_);
v___y_1086_ = v___y_1125_;
v___y_1087_ = v___y_1126_;
goto v___jp_1085_;
}
}
}
else
{
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
return v___y_1123_;
}
}
v___jp_1141_:
{
lean_object* v_fst_1145_; lean_object* v_snd_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v_fst_1145_ = lean_ctor_get(v_pos_1143_, 0);
lean_inc(v_fst_1145_);
v_snd_1146_ = lean_ctor_get(v_pos_1143_, 1);
lean_inc(v_snd_1146_);
v___x_1147_ = lean_string_utf8_byte_size(v_fst_1145_);
v___x_1148_ = lean_nat_dec_eq(v_snd_1146_, v___x_1147_);
if (v___x_1148_ == 0)
{
uint8_t v___x_1149_; 
v___x_1149_ = 1;
v___y_1123_ = v___y_1142_;
v___y_1124_ = v_fst_1145_;
v___y_1125_ = v_pos_1143_;
v___y_1126_ = v_res_1144_;
v___y_1127_ = v_snd_1146_;
v___y_1128_ = v___x_1149_;
goto v___jp_1122_;
}
else
{
v___y_1123_ = v___y_1142_;
v___y_1124_ = v_fst_1145_;
v___y_1125_ = v_pos_1143_;
v___y_1126_ = v_res_1144_;
v___y_1127_ = v_snd_1146_;
v___y_1128_ = v___x_1140_;
goto v___jp_1122_;
}
}
v___jp_1150_:
{
if (v___y_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec(v___y_1153_);
v___x_1155_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___y_1152_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_1157_, v___x_1157_, v___y_1152_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_res_1159_; lean_object* v_pos_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1190_; 
v_res_1159_ = lean_ctor_get(v___x_1158_, 1);
v_pos_1160_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1162_ = v___x_1158_;
v_isShared_1163_ = v_isSharedCheck_1190_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_res_1159_);
lean_inc(v_pos_1160_);
lean_dec(v___x_1158_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1190_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v_fst_1164_; lean_object* v_snd_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1189_; 
v_fst_1164_ = lean_ctor_get(v_res_1159_, 0);
v_snd_1165_ = lean_ctor_get(v_res_1159_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_res_1159_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1167_ = v_res_1159_;
v_isShared_1168_ = v_isSharedCheck_1189_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_snd_1165_);
lean_inc(v_fst_1164_);
lean_dec(v_res_1159_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1189_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_1170_ = lean_nat_dec_lt(v___x_1169_, v_snd_1165_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1171_ = lean_nat_to_int(v___y_1153_);
v___x_1172_ = lean_unsigned_to_nat(10u);
v___x_1173_ = lean_nat_pow(v___x_1172_, v_snd_1165_);
v___x_1174_ = lean_nat_to_int(v___x_1173_);
v___x_1175_ = lean_int_mul(v___x_1171_, v___x_1174_);
lean_dec(v___x_1174_);
lean_dec(v___x_1171_);
v___x_1176_ = lean_nat_to_int(v_fst_1164_);
v___x_1177_ = lean_int_add(v___x_1175_, v___x_1176_);
lean_dec(v___x_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_int_mul(v___y_1151_, v___x_1177_);
lean_dec(v___x_1177_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1178_);
v___x_1180_ = v___x_1167_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_snd_1165_);
v___x_1180_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1182_; 
lean_inc_ref(v___x_1180_);
lean_inc(v_pos_1160_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___x_1180_);
v___x_1182_ = v___x_1162_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_pos_1160_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
v___y_1142_ = v___x_1182_;
v_pos_1143_ = v_pos_1160_;
v_res_1144_ = v___x_1180_;
goto v___jp_1141_;
}
}
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1187_; 
lean_del_object(v___x_1167_);
lean_dec(v_snd_1165_);
lean_dec(v_fst_1164_);
lean_dec(v___y_1153_);
v___x_1185_ = ((lean_object*)(l_Lean_Json_Parser_numWithDecimals___closed__2));
if (v_isShared_1163_ == 0)
{
lean_ctor_set_tag(v___x_1162_, 1);
lean_ctor_set(v___x_1162_, 1, v___x_1185_);
v___x_1187_ = v___x_1162_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_pos_1160_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
else
{
lean_object* v_pos_1191_; lean_object* v_err_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec(v___y_1153_);
v_pos_1191_ = lean_ctor_get(v___x_1158_, 0);
v_err_1192_ = lean_ctor_get(v___x_1158_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1158_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_err_1192_);
lean_inc(v_pos_1191_);
lean_dec(v___x_1158_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_pos_1191_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_err_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
v___jp_1200_:
{
if (v___y_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
lean_dec(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec(v___y_1202_);
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___y_1203_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
return v___x_1208_;
}
else
{
uint32_t v___x_1209_; uint32_t v___x_1210_; uint8_t v___x_1211_; 
v___x_1209_ = lean_string_utf8_get_fast(v___y_1204_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec(v___y_1204_);
v___x_1210_ = 48;
v___x_1211_ = lean_uint32_dec_le(v___x_1210_, v___x_1209_);
if (v___x_1211_ == 0)
{
v___y_1151_ = v___y_1201_;
v___y_1152_ = v___y_1203_;
v___y_1153_ = v___y_1205_;
v___y_1154_ = v___x_1211_;
goto v___jp_1150_;
}
else
{
uint32_t v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = 57;
v___x_1213_ = lean_uint32_dec_le(v___x_1209_, v___x_1212_);
v___y_1151_ = v___y_1201_;
v___y_1152_ = v___y_1203_;
v___y_1153_ = v___y_1205_;
v___y_1154_ = v___x_1213_;
goto v___jp_1150_;
}
}
}
v___jp_1214_:
{
uint8_t v___x_1221_; 
v___x_1221_ = lean_bool_not(v___y_1220_);
if (v___x_1221_ == 0)
{
if (v___y_1220_ == 0)
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_dec(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec(v___y_1217_);
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___y_1216_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
return v___x_1223_;
}
else
{
uint32_t v___x_1224_; uint32_t v___x_1225_; uint8_t v___x_1226_; 
v___x_1224_ = lean_string_utf8_get_fast(v___y_1217_, v___y_1218_);
v___x_1225_ = 46;
v___x_1226_ = lean_uint32_dec_eq(v___x_1224_, v___x_1225_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_dec(v___y_1218_);
lean_dec(v___y_1217_);
v___x_1227_ = lean_nat_to_int(v___y_1219_);
v___x_1228_ = lean_int_mul(v___y_1215_, v___x_1227_);
lean_dec(v___x_1227_);
v___x_1229_ = l_Lean_JsonNumber_fromInt(v___x_1228_);
lean_inc_ref(v___x_1229_);
lean_inc_ref(v___y_1216_);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___y_1216_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___y_1142_ = v___x_1230_;
v_pos_1143_ = v___y_1216_;
v_res_1144_ = v___x_1229_;
goto v___jp_1141_;
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
lean_dec_ref(v___y_1216_);
v___x_1231_ = lean_string_utf8_next_fast(v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_inc(v___y_1217_);
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___y_1217_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = lean_string_utf8_byte_size(v___y_1217_);
v___x_1234_ = lean_nat_dec_eq(v___x_1231_, v___x_1233_);
if (v___x_1234_ == 0)
{
v___y_1201_ = v___y_1215_;
v___y_1202_ = v___x_1231_;
v___y_1203_ = v___x_1232_;
v___y_1204_ = v___y_1217_;
v___y_1205_ = v___y_1219_;
v___y_1206_ = v___x_1226_;
goto v___jp_1200_;
}
else
{
v___y_1201_ = v___y_1215_;
v___y_1202_ = v___x_1231_;
v___y_1203_ = v___x_1232_;
v___y_1204_ = v___y_1217_;
v___y_1205_ = v___y_1219_;
v___y_1206_ = v___x_1221_;
goto v___jp_1200_;
}
}
}
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v___y_1218_);
lean_dec(v___y_1217_);
v___x_1235_ = lean_nat_to_int(v___y_1219_);
v___x_1236_ = lean_int_mul(v___y_1215_, v___x_1235_);
lean_dec(v___x_1235_);
v___x_1237_ = l_Lean_JsonNumber_fromInt(v___x_1236_);
lean_inc_ref(v___x_1237_);
lean_inc_ref(v___y_1216_);
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___y_1216_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___y_1142_ = v___x_1238_;
v_pos_1143_ = v___y_1216_;
v_res_1144_ = v___x_1237_;
goto v___jp_1141_;
}
}
v___jp_1239_:
{
lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = lean_string_utf8_byte_size(v_fst_1242_);
v___x_1246_ = lean_nat_dec_eq(v_snd_1243_, v___x_1245_);
if (v___x_1246_ == 0)
{
uint8_t v___x_1247_; 
v___x_1247_ = 1;
v___y_1215_ = v___y_1240_;
v___y_1216_ = v_pos_1241_;
v___y_1217_ = v_fst_1242_;
v___y_1218_ = v_snd_1243_;
v___y_1219_ = v_res_1244_;
v___y_1220_ = v___x_1247_;
goto v___jp_1214_;
}
else
{
v___y_1215_ = v___y_1240_;
v___y_1216_ = v_pos_1241_;
v___y_1217_ = v_fst_1242_;
v___y_1218_ = v_snd_1243_;
v___y_1219_ = v_res_1244_;
v___y_1220_ = v___x_1140_;
goto v___jp_1214_;
}
}
v___jp_1248_:
{
if (v___y_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_1253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___y_1250_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_unsigned_to_nat(0u);
v___x_1255_ = l_Lean_Json_Parser_natCore(v___x_1254_, v___y_1250_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_pos_1256_; lean_object* v_res_1257_; lean_object* v_fst_1258_; lean_object* v_snd_1259_; 
v_pos_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_pos_1256_);
v_res_1257_ = lean_ctor_get(v___x_1255_, 1);
lean_inc(v_res_1257_);
lean_dec_ref_known(v___x_1255_, 2);
v_fst_1258_ = lean_ctor_get(v_pos_1256_, 0);
lean_inc(v_fst_1258_);
v_snd_1259_ = lean_ctor_get(v_pos_1256_, 1);
lean_inc(v_snd_1259_);
v___y_1240_ = v___y_1249_;
v_pos_1241_ = v_pos_1256_;
v_fst_1242_ = v_fst_1258_;
v_snd_1243_ = v_snd_1259_;
v_res_1244_ = v_res_1257_;
goto v___jp_1239_;
}
else
{
lean_object* v_pos_1260_; lean_object* v_err_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
v_pos_1260_ = lean_ctor_get(v___x_1255_, 0);
v_err_1261_ = lean_ctor_get(v___x_1255_, 1);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1255_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_err_1261_);
lean_inc(v_pos_1260_);
lean_dec(v___x_1255_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_pos_1260_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_err_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
v___jp_1269_:
{
lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1274_ = lean_string_utf8_byte_size(v_fst_1271_);
v___x_1275_ = lean_nat_dec_eq(v_snd_1272_, v___x_1274_);
if (v___x_1275_ == 0)
{
uint32_t v___x_1276_; uint32_t v___x_1277_; uint8_t v___x_1278_; 
v___x_1276_ = lean_string_utf8_get_fast(v_fst_1271_, v_snd_1272_);
v___x_1277_ = 48;
v___x_1278_ = lean_uint32_dec_eq(v___x_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
uint32_t v___x_1279_; uint8_t v___x_1280_; 
lean_dec(v_snd_1272_);
lean_dec(v_fst_1271_);
v___x_1279_ = 49;
v___x_1280_ = lean_uint32_dec_le(v___x_1279_, v___x_1276_);
if (v___x_1280_ == 0)
{
v___y_1249_ = v_res_1273_;
v___y_1250_ = v_pos_1270_;
v___y_1251_ = v___x_1280_;
goto v___jp_1248_;
}
else
{
uint32_t v___x_1281_; uint8_t v___x_1282_; 
v___x_1281_ = 57;
v___x_1282_ = lean_uint32_dec_le(v___x_1276_, v___x_1281_);
v___y_1249_ = v_res_1273_;
v___y_1250_ = v_pos_1270_;
v___y_1251_ = v___x_1282_;
goto v___jp_1248_;
}
}
else
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec_ref(v_pos_1270_);
v___x_1283_ = lean_string_utf8_next_fast(v_fst_1271_, v_snd_1272_);
lean_dec(v_snd_1272_);
lean_inc(v_fst_1271_);
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v_fst_1271_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = lean_unsigned_to_nat(0u);
v___y_1240_ = v_res_1273_;
v_pos_1241_ = v___x_1284_;
v_fst_1242_ = v_fst_1271_;
v_snd_1243_ = v___x_1283_;
v_res_1244_ = v___x_1285_;
goto v___jp_1239_;
}
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec(v_snd_1272_);
lean_dec(v_fst_1271_);
v___x_1286_ = lean_box(0);
v___x_1287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1287_, 0, v_pos_1270_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
return v___x_1287_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(lean_object* v_msg_1305_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_box(1);
v___x_1307_ = lean_panic_fn_borrowed(v___x_1306_, v_msg_1305_);
return v___x_1307_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1311_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2));
v___x_1312_ = lean_unsigned_to_nat(35u);
v___x_1313_ = lean_unsigned_to_nat(182u);
v___x_1314_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1));
v___x_1315_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1316_ = l_mkPanicMessageWithDecl(v___x_1315_, v___x_1314_, v___x_1313_, v___x_1312_, v___x_1311_);
return v___x_1316_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1317_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2));
v___x_1318_ = lean_unsigned_to_nat(21u);
v___x_1319_ = lean_unsigned_to_nat(183u);
v___x_1320_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1));
v___x_1321_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1322_ = l_mkPanicMessageWithDecl(v___x_1321_, v___x_1320_, v___x_1319_, v___x_1318_, v___x_1317_);
return v___x_1322_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1325_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6));
v___x_1326_ = lean_unsigned_to_nat(35u);
v___x_1327_ = lean_unsigned_to_nat(276u);
v___x_1328_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5));
v___x_1329_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1330_ = l_mkPanicMessageWithDecl(v___x_1329_, v___x_1328_, v___x_1327_, v___x_1326_, v___x_1325_);
return v___x_1330_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1331_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6));
v___x_1332_ = lean_unsigned_to_nat(21u);
v___x_1333_ = lean_unsigned_to_nat(277u);
v___x_1334_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5));
v___x_1335_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1336_ = l_mkPanicMessageWithDecl(v___x_1335_, v___x_1334_, v___x_1333_, v___x_1332_, v___x_1331_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(lean_object* v_k_1337_, lean_object* v_v_1338_, lean_object* v_t_1339_){
_start:
{
if (lean_obj_tag(v_t_1339_) == 0)
{
lean_object* v_size_1340_; lean_object* v_k_1341_; lean_object* v_v_1342_; lean_object* v_l_1343_; lean_object* v_r_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1700_; 
v_size_1340_ = lean_ctor_get(v_t_1339_, 0);
v_k_1341_ = lean_ctor_get(v_t_1339_, 1);
v_v_1342_ = lean_ctor_get(v_t_1339_, 2);
v_l_1343_ = lean_ctor_get(v_t_1339_, 3);
v_r_1344_ = lean_ctor_get(v_t_1339_, 4);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_t_1339_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1346_ = v_t_1339_;
v_isShared_1347_ = v_isSharedCheck_1700_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_r_1344_);
lean_inc(v_l_1343_);
lean_inc(v_v_1342_);
lean_inc(v_k_1341_);
lean_inc(v_size_1340_);
lean_dec(v_t_1339_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1700_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
uint8_t v___x_1348_; 
v___x_1348_ = lean_string_compare(v_k_1337_, v_k_1341_);
switch(v___x_1348_)
{
case 0:
{
lean_object* v___x_1349_; 
lean_dec(v_size_1340_);
v___x_1349_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_1337_, v_v_1338_, v_l_1343_);
if (lean_obj_tag(v_r_1344_) == 0)
{
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_size_1350_; lean_object* v_size_1351_; lean_object* v_k_1352_; lean_object* v_v_1353_; lean_object* v_l_1354_; lean_object* v_r_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v_size_1350_ = lean_ctor_get(v_r_1344_, 0);
v_size_1351_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_size_1351_);
v_k_1352_ = lean_ctor_get(v___x_1349_, 1);
lean_inc(v_k_1352_);
v_v_1353_ = lean_ctor_get(v___x_1349_, 2);
lean_inc(v_v_1353_);
v_l_1354_ = lean_ctor_get(v___x_1349_, 3);
lean_inc(v_l_1354_);
v_r_1355_ = lean_ctor_get(v___x_1349_, 4);
lean_inc(v_r_1355_);
v___x_1356_ = lean_unsigned_to_nat(3u);
v___x_1357_ = lean_nat_mul(v___x_1356_, v_size_1350_);
v___x_1358_ = lean_nat_dec_lt(v___x_1357_, v_size_1351_);
lean_dec(v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
lean_dec(v_r_1355_);
lean_dec(v_l_1354_);
lean_dec(v_v_1353_);
lean_dec(v_k_1352_);
v___x_1359_ = lean_unsigned_to_nat(1u);
v___x_1360_ = lean_nat_add(v___x_1359_, v_size_1351_);
lean_dec(v_size_1351_);
v___x_1361_ = lean_nat_add(v___x_1360_, v_size_1350_);
lean_dec(v___x_1360_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 3, v___x_1349_);
lean_ctor_set(v___x_1346_, 0, v___x_1361_);
v___x_1363_ = v___x_1346_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1364_, 3, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1364_, 4, v_r_1344_);
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
lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1436_; 
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1436_ == 0)
{
lean_object* v_unused_1437_; lean_object* v_unused_1438_; lean_object* v_unused_1439_; lean_object* v_unused_1440_; lean_object* v_unused_1441_; 
v_unused_1437_ = lean_ctor_get(v___x_1349_, 4);
lean_dec(v_unused_1437_);
v_unused_1438_ = lean_ctor_get(v___x_1349_, 3);
lean_dec(v_unused_1438_);
v_unused_1439_ = lean_ctor_get(v___x_1349_, 2);
lean_dec(v_unused_1439_);
v_unused_1440_ = lean_ctor_get(v___x_1349_, 1);
lean_dec(v_unused_1440_);
v_unused_1441_ = lean_ctor_get(v___x_1349_, 0);
lean_dec(v_unused_1441_);
v___x_1366_ = v___x_1349_;
v_isShared_1367_ = v_isSharedCheck_1436_;
goto v_resetjp_1365_;
}
else
{
lean_dec(v___x_1349_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1436_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
if (lean_obj_tag(v_l_1354_) == 0)
{
if (lean_obj_tag(v_r_1355_) == 0)
{
lean_object* v_size_1368_; lean_object* v_size_1369_; lean_object* v_k_1370_; lean_object* v_v_1371_; lean_object* v_l_1372_; lean_object* v_r_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v_size_1368_ = lean_ctor_get(v_l_1354_, 0);
v_size_1369_ = lean_ctor_get(v_r_1355_, 0);
v_k_1370_ = lean_ctor_get(v_r_1355_, 1);
v_v_1371_ = lean_ctor_get(v_r_1355_, 2);
v_l_1372_ = lean_ctor_get(v_r_1355_, 3);
v_r_1373_ = lean_ctor_get(v_r_1355_, 4);
v___x_1374_ = lean_unsigned_to_nat(2u);
v___x_1375_ = lean_nat_mul(v___x_1374_, v_size_1368_);
v___x_1376_ = lean_nat_dec_lt(v_size_1369_, v___x_1375_);
lean_dec(v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1406_; 
lean_inc(v_r_1373_);
lean_inc(v_l_1372_);
lean_inc(v_v_1371_);
lean_inc(v_k_1370_);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_r_1355_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; lean_object* v_unused_1408_; lean_object* v_unused_1409_; lean_object* v_unused_1410_; lean_object* v_unused_1411_; 
v_unused_1407_ = lean_ctor_get(v_r_1355_, 4);
lean_dec(v_unused_1407_);
v_unused_1408_ = lean_ctor_get(v_r_1355_, 3);
lean_dec(v_unused_1408_);
v_unused_1409_ = lean_ctor_get(v_r_1355_, 2);
lean_dec(v_unused_1409_);
v_unused_1410_ = lean_ctor_get(v_r_1355_, 1);
lean_dec(v_unused_1410_);
v_unused_1411_ = lean_ctor_get(v_r_1355_, 0);
lean_dec(v_unused_1411_);
v___x_1378_ = v_r_1355_;
v_isShared_1379_ = v_isSharedCheck_1406_;
goto v_resetjp_1377_;
}
else
{
lean_dec(v_r_1355_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1406_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___x_1394_; lean_object* v___y_1396_; 
v___x_1380_ = lean_unsigned_to_nat(1u);
v___x_1381_ = lean_nat_add(v___x_1380_, v_size_1351_);
lean_dec(v_size_1351_);
v___x_1382_ = lean_nat_add(v___x_1381_, v_size_1350_);
lean_dec(v___x_1381_);
v___x_1394_ = lean_nat_add(v___x_1380_, v_size_1368_);
if (lean_obj_tag(v_l_1372_) == 0)
{
lean_object* v_size_1404_; 
v_size_1404_ = lean_ctor_get(v_l_1372_, 0);
lean_inc(v_size_1404_);
v___y_1396_ = v_size_1404_;
goto v___jp_1395_;
}
else
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_unsigned_to_nat(0u);
v___y_1396_ = v___x_1405_;
goto v___jp_1395_;
}
v___jp_1383_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = lean_nat_add(v___y_1384_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec(v___y_1384_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 4, v_r_1344_);
lean_ctor_set(v___x_1378_, 3, v_r_1373_);
lean_ctor_set(v___x_1378_, 2, v_v_1342_);
lean_ctor_set(v___x_1378_, 1, v_k_1341_);
lean_ctor_set(v___x_1378_, 0, v___x_1387_);
v___x_1389_ = v___x_1378_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v_r_1373_);
lean_ctor_set(v_reuseFailAlloc_1393_, 4, v_r_1344_);
v___x_1389_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1391_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v___x_1389_);
lean_ctor_set(v___x_1366_, 3, v___y_1385_);
lean_ctor_set(v___x_1366_, 2, v_v_1371_);
lean_ctor_set(v___x_1366_, 1, v_k_1370_);
lean_ctor_set(v___x_1366_, 0, v___x_1382_);
v___x_1391_ = v___x_1366_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v___y_1385_);
lean_ctor_set(v_reuseFailAlloc_1392_, 4, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
v___jp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1397_ = lean_nat_add(v___x_1394_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec(v___x_1394_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v_l_1372_);
lean_ctor_set(v___x_1346_, 3, v_l_1354_);
lean_ctor_set(v___x_1346_, 2, v_v_1353_);
lean_ctor_set(v___x_1346_, 1, v_k_1352_);
lean_ctor_set(v___x_1346_, 0, v___x_1397_);
v___x_1399_ = v___x_1346_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v_l_1354_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v_l_1372_);
v___x_1399_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_nat_add(v___x_1380_, v_size_1350_);
if (lean_obj_tag(v_r_1373_) == 0)
{
lean_object* v_size_1401_; 
v_size_1401_ = lean_ctor_get(v_r_1373_, 0);
lean_inc(v_size_1401_);
v___y_1384_ = v___x_1400_;
v___y_1385_ = v___x_1399_;
v___y_1386_ = v_size_1401_;
goto v___jp_1383_;
}
else
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_unsigned_to_nat(0u);
v___y_1384_ = v___x_1400_;
v___y_1385_ = v___x_1399_;
v___y_1386_ = v___x_1402_;
goto v___jp_1383_;
}
}
}
}
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; 
lean_del_object(v___x_1346_);
v___x_1412_ = lean_unsigned_to_nat(1u);
v___x_1413_ = lean_nat_add(v___x_1412_, v_size_1351_);
lean_dec(v_size_1351_);
v___x_1414_ = lean_nat_add(v___x_1413_, v_size_1350_);
lean_dec(v___x_1413_);
v___x_1415_ = lean_nat_add(v___x_1412_, v_size_1350_);
v___x_1416_ = lean_nat_add(v___x_1415_, v_size_1369_);
lean_dec(v___x_1415_);
lean_inc_ref(v_r_1344_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v_r_1344_);
lean_ctor_set(v___x_1366_, 3, v_r_1355_);
lean_ctor_set(v___x_1366_, 2, v_v_1342_);
lean_ctor_set(v___x_1366_, 1, v_k_1341_);
lean_ctor_set(v___x_1366_, 0, v___x_1416_);
v___x_1418_ = v___x_1366_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v_r_1355_);
lean_ctor_set(v_reuseFailAlloc_1431_, 4, v_r_1344_);
v___x_1418_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
v_isSharedCheck_1425_ = !lean_is_exclusive(v_r_1344_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; lean_object* v_unused_1427_; lean_object* v_unused_1428_; lean_object* v_unused_1429_; lean_object* v_unused_1430_; 
v_unused_1426_ = lean_ctor_get(v_r_1344_, 4);
lean_dec(v_unused_1426_);
v_unused_1427_ = lean_ctor_get(v_r_1344_, 3);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v_r_1344_, 2);
lean_dec(v_unused_1428_);
v_unused_1429_ = lean_ctor_get(v_r_1344_, 1);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v_r_1344_, 0);
lean_dec(v_unused_1430_);
v___x_1420_ = v_r_1344_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_dec(v_r_1344_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v___x_1418_);
lean_ctor_set(v___x_1420_, 3, v_l_1354_);
lean_ctor_set(v___x_1420_, 2, v_v_1353_);
lean_ctor_set(v___x_1420_, 1, v_k_1352_);
lean_ctor_set(v___x_1420_, 0, v___x_1414_);
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1424_, 3, v_l_1354_);
lean_ctor_set(v_reuseFailAlloc_1424_, 4, v___x_1418_);
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
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec_ref_known(v_l_1354_, 5);
lean_del_object(v___x_1366_);
lean_dec(v_v_1353_);
lean_dec(v_k_1352_);
lean_dec(v_size_1351_);
lean_dec_ref_known(v_r_1344_, 5);
lean_del_object(v___x_1346_);
lean_dec(v_v_1342_);
lean_dec(v_k_1341_);
v___x_1432_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3);
v___x_1433_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1432_);
return v___x_1433_;
}
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_del_object(v___x_1366_);
lean_dec(v_r_1355_);
lean_dec(v_v_1353_);
lean_dec(v_k_1352_);
lean_dec(v_size_1351_);
lean_dec_ref_known(v_r_1344_, 5);
lean_del_object(v___x_1346_);
lean_dec(v_v_1342_);
lean_dec(v_k_1341_);
v___x_1434_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4);
v___x_1435_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1434_);
return v___x_1435_;
}
}
}
}
else
{
lean_object* v_size_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1446_; 
v_size_1442_ = lean_ctor_get(v_r_1344_, 0);
v___x_1443_ = lean_unsigned_to_nat(1u);
v___x_1444_ = lean_nat_add(v___x_1443_, v_size_1442_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 3, v___x_1349_);
lean_ctor_set(v___x_1346_, 0, v___x_1444_);
v___x_1446_ = v___x_1346_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1447_, 3, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1447_, 4, v_r_1344_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
else
{
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_l_1448_; 
v_l_1448_ = lean_ctor_get(v___x_1349_, 3);
lean_inc(v_l_1448_);
if (lean_obj_tag(v_l_1448_) == 0)
{
lean_object* v_r_1449_; 
v_r_1449_ = lean_ctor_get(v___x_1349_, 4);
lean_inc(v_r_1449_);
if (lean_obj_tag(v_r_1449_) == 0)
{
lean_object* v_size_1450_; lean_object* v_k_1451_; lean_object* v_v_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1466_; 
v_size_1450_ = lean_ctor_get(v___x_1349_, 0);
v_k_1451_ = lean_ctor_get(v___x_1349_, 1);
v_v_1452_ = lean_ctor_get(v___x_1349_, 2);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; lean_object* v_unused_1468_; 
v_unused_1467_ = lean_ctor_get(v___x_1349_, 4);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v___x_1349_, 3);
lean_dec(v_unused_1468_);
v___x_1454_ = v___x_1349_;
v_isShared_1455_ = v_isSharedCheck_1466_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_v_1452_);
lean_inc(v_k_1451_);
lean_inc(v_size_1450_);
lean_dec(v___x_1349_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1466_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v_size_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v_size_1456_ = lean_ctor_get(v_r_1449_, 0);
v___x_1457_ = lean_unsigned_to_nat(1u);
v___x_1458_ = lean_nat_add(v___x_1457_, v_size_1450_);
lean_dec(v_size_1450_);
v___x_1459_ = lean_nat_add(v___x_1457_, v_size_1456_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 4, v_r_1344_);
lean_ctor_set(v___x_1454_, 3, v_r_1449_);
lean_ctor_set(v___x_1454_, 2, v_v_1342_);
lean_ctor_set(v___x_1454_, 1, v_k_1341_);
lean_ctor_set(v___x_1454_, 0, v___x_1459_);
v___x_1461_ = v___x_1454_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1465_, 3, v_r_1449_);
lean_ctor_set(v_reuseFailAlloc_1465_, 4, v_r_1344_);
v___x_1461_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1463_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v___x_1461_);
lean_ctor_set(v___x_1346_, 3, v_l_1448_);
lean_ctor_set(v___x_1346_, 2, v_v_1452_);
lean_ctor_set(v___x_1346_, 1, v_k_1451_);
lean_ctor_set(v___x_1346_, 0, v___x_1458_);
v___x_1463_ = v___x_1346_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_k_1451_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_v_1452_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_l_1448_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
else
{
lean_object* v_k_1469_; lean_object* v_v_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1482_; 
v_k_1469_ = lean_ctor_get(v___x_1349_, 1);
v_v_1470_ = lean_ctor_get(v___x_1349_, 2);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; lean_object* v_unused_1484_; lean_object* v_unused_1485_; 
v_unused_1483_ = lean_ctor_get(v___x_1349_, 4);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v___x_1349_, 3);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v___x_1349_, 0);
lean_dec(v_unused_1485_);
v___x_1472_ = v___x_1349_;
v_isShared_1473_ = v_isSharedCheck_1482_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_v_1470_);
lean_inc(v_k_1469_);
lean_dec(v___x_1349_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1482_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1474_ = lean_unsigned_to_nat(3u);
v___x_1475_ = lean_unsigned_to_nat(1u);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 3, v_r_1449_);
lean_ctor_set(v___x_1472_, 2, v_v_1342_);
lean_ctor_set(v___x_1472_, 1, v_k_1341_);
lean_ctor_set(v___x_1472_, 0, v___x_1475_);
v___x_1477_ = v___x_1472_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_r_1449_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v_r_1449_);
v___x_1477_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1479_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v___x_1477_);
lean_ctor_set(v___x_1346_, 3, v_l_1448_);
lean_ctor_set(v___x_1346_, 2, v_v_1470_);
lean_ctor_set(v___x_1346_, 1, v_k_1469_);
lean_ctor_set(v___x_1346_, 0, v___x_1474_);
v___x_1479_ = v___x_1346_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_k_1469_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_v_1470_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_l_1448_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
else
{
lean_object* v_r_1486_; 
v_r_1486_ = lean_ctor_get(v___x_1349_, 4);
lean_inc(v_r_1486_);
if (lean_obj_tag(v_r_1486_) == 0)
{
lean_object* v_k_1487_; lean_object* v_v_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1512_; 
v_k_1487_ = lean_ctor_get(v___x_1349_, 1);
v_v_1488_ = lean_ctor_get(v___x_1349_, 2);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; lean_object* v_unused_1514_; lean_object* v_unused_1515_; 
v_unused_1513_ = lean_ctor_get(v___x_1349_, 4);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v___x_1349_, 3);
lean_dec(v_unused_1514_);
v_unused_1515_ = lean_ctor_get(v___x_1349_, 0);
lean_dec(v_unused_1515_);
v___x_1490_ = v___x_1349_;
v_isShared_1491_ = v_isSharedCheck_1512_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_v_1488_);
lean_inc(v_k_1487_);
lean_dec(v___x_1349_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1512_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_k_1492_; lean_object* v_v_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1508_; 
v_k_1492_ = lean_ctor_get(v_r_1486_, 1);
v_v_1493_ = lean_ctor_get(v_r_1486_, 2);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_r_1486_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; lean_object* v_unused_1510_; lean_object* v_unused_1511_; 
v_unused_1509_ = lean_ctor_get(v_r_1486_, 4);
lean_dec(v_unused_1509_);
v_unused_1510_ = lean_ctor_get(v_r_1486_, 3);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v_r_1486_, 0);
lean_dec(v_unused_1511_);
v___x_1495_ = v_r_1486_;
v_isShared_1496_ = v_isSharedCheck_1508_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_v_1493_);
lean_inc(v_k_1492_);
lean_dec(v_r_1486_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1508_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1497_ = lean_unsigned_to_nat(3u);
v___x_1498_ = lean_unsigned_to_nat(1u);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 4, v_l_1448_);
lean_ctor_set(v___x_1495_, 3, v_l_1448_);
lean_ctor_set(v___x_1495_, 2, v_v_1488_);
lean_ctor_set(v___x_1495_, 1, v_k_1487_);
lean_ctor_set(v___x_1495_, 0, v___x_1498_);
v___x_1500_ = v___x_1495_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_k_1487_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_v_1488_);
lean_ctor_set(v_reuseFailAlloc_1507_, 3, v_l_1448_);
lean_ctor_set(v_reuseFailAlloc_1507_, 4, v_l_1448_);
v___x_1500_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1502_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 4, v_l_1448_);
lean_ctor_set(v___x_1490_, 2, v_v_1342_);
lean_ctor_set(v___x_1490_, 1, v_k_1341_);
lean_ctor_set(v___x_1490_, 0, v___x_1498_);
v___x_1502_ = v___x_1490_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1506_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1506_, 3, v_l_1448_);
lean_ctor_set(v_reuseFailAlloc_1506_, 4, v_l_1448_);
v___x_1502_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1504_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v___x_1502_);
lean_ctor_set(v___x_1346_, 3, v___x_1500_);
lean_ctor_set(v___x_1346_, 2, v_v_1493_);
lean_ctor_set(v___x_1346_, 1, v_k_1492_);
lean_ctor_set(v___x_1346_, 0, v___x_1497_);
v___x_1504_ = v___x_1346_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_k_1492_);
lean_ctor_set(v_reuseFailAlloc_1505_, 2, v_v_1493_);
lean_ctor_set(v_reuseFailAlloc_1505_, 3, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1505_, 4, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1516_ = lean_unsigned_to_nat(2u);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v_r_1486_);
lean_ctor_set(v___x_1346_, 3, v___x_1349_);
lean_ctor_set(v___x_1346_, 0, v___x_1516_);
v___x_1518_ = v___x_1346_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1519_, 3, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1519_, 4, v_r_1486_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = lean_unsigned_to_nat(1u);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v___x_1349_);
lean_ctor_set(v___x_1346_, 3, v___x_1349_);
lean_ctor_set(v___x_1346_, 0, v___x_1520_);
v___x_1522_ = v___x_1346_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v___x_1349_);
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
case 1:
{
lean_object* v___x_1525_; 
lean_dec(v_v_1342_);
lean_dec(v_k_1341_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 2, v_v_1338_);
lean_ctor_set(v___x_1346_, 1, v_k_1337_);
v___x_1525_ = v___x_1346_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_size_1340_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_k_1337_);
lean_ctor_set(v_reuseFailAlloc_1526_, 2, v_v_1338_);
lean_ctor_set(v_reuseFailAlloc_1526_, 3, v_l_1343_);
lean_ctor_set(v_reuseFailAlloc_1526_, 4, v_r_1344_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
default: 
{
lean_object* v___x_1527_; 
lean_dec(v_size_1340_);
v___x_1527_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_1337_, v_v_1338_, v_r_1344_);
if (lean_obj_tag(v_l_1343_) == 0)
{
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_size_1528_; lean_object* v_size_1529_; lean_object* v_k_1530_; lean_object* v_v_1531_; lean_object* v_l_1532_; lean_object* v_r_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v_size_1528_ = lean_ctor_get(v_l_1343_, 0);
v_size_1529_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_size_1529_);
v_k_1530_ = lean_ctor_get(v___x_1527_, 1);
lean_inc(v_k_1530_);
v_v_1531_ = lean_ctor_get(v___x_1527_, 2);
lean_inc(v_v_1531_);
v_l_1532_ = lean_ctor_get(v___x_1527_, 3);
lean_inc(v_l_1532_);
v_r_1533_ = lean_ctor_get(v___x_1527_, 4);
lean_inc(v_r_1533_);
v___x_1534_ = lean_unsigned_to_nat(3u);
v___x_1535_ = lean_nat_mul(v___x_1534_, v_size_1528_);
v___x_1536_ = lean_nat_dec_lt(v___x_1535_, v_size_1529_);
lean_dec(v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1541_; 
lean_dec(v_r_1533_);
lean_dec(v_l_1532_);
lean_dec(v_v_1531_);
lean_dec(v_k_1530_);
v___x_1537_ = lean_unsigned_to_nat(1u);
v___x_1538_ = lean_nat_add(v___x_1537_, v_size_1528_);
v___x_1539_ = lean_nat_add(v___x_1538_, v_size_1529_);
lean_dec(v_size_1529_);
lean_dec(v___x_1538_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v___x_1527_);
lean_ctor_set(v___x_1346_, 0, v___x_1539_);
v___x_1541_ = v___x_1346_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_l_1343_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v___x_1527_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
else
{
lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1612_; 
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; lean_object* v_unused_1614_; lean_object* v_unused_1615_; lean_object* v_unused_1616_; lean_object* v_unused_1617_; 
v_unused_1613_ = lean_ctor_get(v___x_1527_, 4);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v___x_1527_, 3);
lean_dec(v_unused_1614_);
v_unused_1615_ = lean_ctor_get(v___x_1527_, 2);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v___x_1527_, 1);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v___x_1527_, 0);
lean_dec(v_unused_1617_);
v___x_1544_ = v___x_1527_;
v_isShared_1545_ = v_isSharedCheck_1612_;
goto v_resetjp_1543_;
}
else
{
lean_dec(v___x_1527_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1612_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
if (lean_obj_tag(v_l_1532_) == 0)
{
if (lean_obj_tag(v_r_1533_) == 0)
{
lean_object* v_size_1546_; lean_object* v_k_1547_; lean_object* v_v_1548_; lean_object* v_l_1549_; lean_object* v_r_1550_; lean_object* v_size_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v_size_1546_ = lean_ctor_get(v_l_1532_, 0);
v_k_1547_ = lean_ctor_get(v_l_1532_, 1);
v_v_1548_ = lean_ctor_get(v_l_1532_, 2);
v_l_1549_ = lean_ctor_get(v_l_1532_, 3);
v_r_1550_ = lean_ctor_get(v_l_1532_, 4);
v_size_1551_ = lean_ctor_get(v_r_1533_, 0);
v___x_1552_ = lean_unsigned_to_nat(2u);
v___x_1553_ = lean_nat_mul(v___x_1552_, v_size_1551_);
v___x_1554_ = lean_nat_dec_lt(v_size_1546_, v___x_1553_);
lean_dec(v___x_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1583_; 
lean_inc(v_r_1550_);
lean_inc(v_l_1549_);
lean_inc(v_v_1548_);
lean_inc(v_k_1547_);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_l_1532_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; lean_object* v_unused_1585_; lean_object* v_unused_1586_; lean_object* v_unused_1587_; lean_object* v_unused_1588_; 
v_unused_1584_ = lean_ctor_get(v_l_1532_, 4);
lean_dec(v_unused_1584_);
v_unused_1585_ = lean_ctor_get(v_l_1532_, 3);
lean_dec(v_unused_1585_);
v_unused_1586_ = lean_ctor_get(v_l_1532_, 2);
lean_dec(v_unused_1586_);
v_unused_1587_ = lean_ctor_get(v_l_1532_, 1);
lean_dec(v_unused_1587_);
v_unused_1588_ = lean_ctor_get(v_l_1532_, 0);
lean_dec(v_unused_1588_);
v___x_1556_ = v_l_1532_;
v_isShared_1557_ = v_isSharedCheck_1583_;
goto v_resetjp_1555_;
}
else
{
lean_dec(v_l_1532_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1583_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1573_; 
v___x_1558_ = lean_unsigned_to_nat(1u);
v___x_1559_ = lean_nat_add(v___x_1558_, v_size_1528_);
v___x_1560_ = lean_nat_add(v___x_1559_, v_size_1529_);
lean_dec(v_size_1529_);
if (lean_obj_tag(v_l_1549_) == 0)
{
lean_object* v_size_1581_; 
v_size_1581_ = lean_ctor_get(v_l_1549_, 0);
lean_inc(v_size_1581_);
v___y_1573_ = v_size_1581_;
goto v___jp_1572_;
}
else
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_unsigned_to_nat(0u);
v___y_1573_ = v___x_1582_;
goto v___jp_1572_;
}
v___jp_1561_:
{
lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1565_ = lean_nat_add(v___y_1562_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec(v___y_1562_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 4, v_r_1533_);
lean_ctor_set(v___x_1556_, 3, v_r_1550_);
lean_ctor_set(v___x_1556_, 2, v_v_1531_);
lean_ctor_set(v___x_1556_, 1, v_k_1530_);
lean_ctor_set(v___x_1556_, 0, v___x_1565_);
v___x_1567_ = v___x_1556_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_k_1530_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_v_1531_);
lean_ctor_set(v_reuseFailAlloc_1571_, 3, v_r_1550_);
lean_ctor_set(v_reuseFailAlloc_1571_, 4, v_r_1533_);
v___x_1567_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1569_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 4, v___x_1567_);
lean_ctor_set(v___x_1544_, 3, v___y_1563_);
lean_ctor_set(v___x_1544_, 2, v_v_1548_);
lean_ctor_set(v___x_1544_, 1, v_k_1547_);
lean_ctor_set(v___x_1544_, 0, v___x_1560_);
v___x_1569_ = v___x_1544_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_k_1547_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_v_1548_);
lean_ctor_set(v_reuseFailAlloc_1570_, 3, v___y_1563_);
lean_ctor_set(v_reuseFailAlloc_1570_, 4, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
v___jp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = lean_nat_add(v___x_1559_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec(v___x_1559_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v_l_1549_);
lean_ctor_set(v___x_1346_, 0, v___x_1574_);
v___x_1576_ = v___x_1346_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1580_, 3, v_l_1343_);
lean_ctor_set(v_reuseFailAlloc_1580_, 4, v_l_1549_);
v___x_1576_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_nat_add(v___x_1558_, v_size_1551_);
if (lean_obj_tag(v_r_1550_) == 0)
{
lean_object* v_size_1578_; 
v_size_1578_ = lean_ctor_get(v_r_1550_, 0);
lean_inc(v_size_1578_);
v___y_1562_ = v___x_1577_;
v___y_1563_ = v___x_1576_;
v___y_1564_ = v_size_1578_;
goto v___jp_1561_;
}
else
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_unsigned_to_nat(0u);
v___y_1562_ = v___x_1577_;
v___y_1563_ = v___x_1576_;
v___y_1564_ = v___x_1579_;
goto v___jp_1561_;
}
}
}
}
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
lean_del_object(v___x_1346_);
v___x_1589_ = lean_unsigned_to_nat(1u);
v___x_1590_ = lean_nat_add(v___x_1589_, v_size_1528_);
v___x_1591_ = lean_nat_add(v___x_1590_, v_size_1529_);
lean_dec(v_size_1529_);
v___x_1592_ = lean_nat_add(v___x_1590_, v_size_1546_);
lean_dec(v___x_1590_);
lean_inc_ref(v_l_1343_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 4, v_l_1532_);
lean_ctor_set(v___x_1544_, 3, v_l_1343_);
lean_ctor_set(v___x_1544_, 2, v_v_1342_);
lean_ctor_set(v___x_1544_, 1, v_k_1341_);
lean_ctor_set(v___x_1544_, 0, v___x_1592_);
v___x_1594_ = v___x_1544_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_l_1343_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v_l_1532_);
v___x_1594_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
v_isSharedCheck_1601_ = !lean_is_exclusive(v_l_1343_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; lean_object* v_unused_1603_; lean_object* v_unused_1604_; lean_object* v_unused_1605_; lean_object* v_unused_1606_; 
v_unused_1602_ = lean_ctor_get(v_l_1343_, 4);
lean_dec(v_unused_1602_);
v_unused_1603_ = lean_ctor_get(v_l_1343_, 3);
lean_dec(v_unused_1603_);
v_unused_1604_ = lean_ctor_get(v_l_1343_, 2);
lean_dec(v_unused_1604_);
v_unused_1605_ = lean_ctor_get(v_l_1343_, 1);
lean_dec(v_unused_1605_);
v_unused_1606_ = lean_ctor_get(v_l_1343_, 0);
lean_dec(v_unused_1606_);
v___x_1596_ = v_l_1343_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_dec(v_l_1343_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 4, v_r_1533_);
lean_ctor_set(v___x_1596_, 3, v___x_1594_);
lean_ctor_set(v___x_1596_, 2, v_v_1531_);
lean_ctor_set(v___x_1596_, 1, v_k_1530_);
lean_ctor_set(v___x_1596_, 0, v___x_1591_);
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_k_1530_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_v_1531_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v_r_1533_);
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
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_dec_ref_known(v_l_1532_, 5);
lean_del_object(v___x_1544_);
lean_dec(v_v_1531_);
lean_dec(v_k_1530_);
lean_dec(v_size_1529_);
lean_dec_ref_known(v_l_1343_, 5);
lean_del_object(v___x_1346_);
lean_dec(v_v_1342_);
lean_dec(v_k_1341_);
v___x_1608_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7);
v___x_1609_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1608_);
return v___x_1609_;
}
}
else
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_del_object(v___x_1544_);
lean_dec(v_r_1533_);
lean_dec(v_v_1531_);
lean_dec(v_k_1530_);
lean_dec(v_size_1529_);
lean_dec_ref_known(v_l_1343_, 5);
lean_del_object(v___x_1346_);
lean_dec(v_v_1342_);
lean_dec(v_k_1341_);
v___x_1610_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8);
v___x_1611_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1610_);
return v___x_1611_;
}
}
}
}
else
{
lean_object* v_size_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
v_size_1618_ = lean_ctor_get(v_l_1343_, 0);
v___x_1619_ = lean_unsigned_to_nat(1u);
v___x_1620_ = lean_nat_add(v___x_1619_, v_size_1618_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v___x_1527_);
lean_ctor_set(v___x_1346_, 0, v___x_1620_);
v___x_1622_ = v___x_1346_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1623_, 3, v_l_1343_);
lean_ctor_set(v_reuseFailAlloc_1623_, 4, v___x_1527_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
else
{
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_l_1624_; 
v_l_1624_ = lean_ctor_get(v___x_1527_, 3);
lean_inc(v_l_1624_);
if (lean_obj_tag(v_l_1624_) == 0)
{
lean_object* v_r_1625_; 
v_r_1625_ = lean_ctor_get(v___x_1527_, 4);
lean_inc(v_r_1625_);
if (lean_obj_tag(v_r_1625_) == 0)
{
lean_object* v_size_1626_; lean_object* v_k_1627_; lean_object* v_v_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1642_; 
v_size_1626_ = lean_ctor_get(v___x_1527_, 0);
v_k_1627_ = lean_ctor_get(v___x_1527_, 1);
v_v_1628_ = lean_ctor_get(v___x_1527_, 2);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; lean_object* v_unused_1644_; 
v_unused_1643_ = lean_ctor_get(v___x_1527_, 4);
lean_dec(v_unused_1643_);
v_unused_1644_ = lean_ctor_get(v___x_1527_, 3);
lean_dec(v_unused_1644_);
v___x_1630_ = v___x_1527_;
v_isShared_1631_ = v_isSharedCheck_1642_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_v_1628_);
lean_inc(v_k_1627_);
lean_inc(v_size_1626_);
lean_dec(v___x_1527_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1642_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_size_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
v_size_1632_ = lean_ctor_get(v_l_1624_, 0);
v___x_1633_ = lean_unsigned_to_nat(1u);
v___x_1634_ = lean_nat_add(v___x_1633_, v_size_1626_);
lean_dec(v_size_1626_);
v___x_1635_ = lean_nat_add(v___x_1633_, v_size_1632_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 4, v_l_1624_);
lean_ctor_set(v___x_1630_, 3, v_l_1343_);
lean_ctor_set(v___x_1630_, 2, v_v_1342_);
lean_ctor_set(v___x_1630_, 1, v_k_1341_);
lean_ctor_set(v___x_1630_, 0, v___x_1635_);
v___x_1637_ = v___x_1630_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v_l_1343_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v_l_1624_);
v___x_1637_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1639_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v_r_1625_);
lean_ctor_set(v___x_1346_, 3, v___x_1637_);
lean_ctor_set(v___x_1346_, 2, v_v_1628_);
lean_ctor_set(v___x_1346_, 1, v_k_1627_);
lean_ctor_set(v___x_1346_, 0, v___x_1634_);
v___x_1639_ = v___x_1346_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_k_1627_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_v_1628_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1640_, 4, v_r_1625_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
else
{
lean_object* v_k_1645_; lean_object* v_v_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1670_; 
v_k_1645_ = lean_ctor_get(v___x_1527_, 1);
v_v_1646_ = lean_ctor_get(v___x_1527_, 2);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; lean_object* v_unused_1672_; lean_object* v_unused_1673_; 
v_unused_1671_ = lean_ctor_get(v___x_1527_, 4);
lean_dec(v_unused_1671_);
v_unused_1672_ = lean_ctor_get(v___x_1527_, 3);
lean_dec(v_unused_1672_);
v_unused_1673_ = lean_ctor_get(v___x_1527_, 0);
lean_dec(v_unused_1673_);
v___x_1648_ = v___x_1527_;
v_isShared_1649_ = v_isSharedCheck_1670_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_v_1646_);
lean_inc(v_k_1645_);
lean_dec(v___x_1527_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1670_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v_k_1650_; lean_object* v_v_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1666_; 
v_k_1650_ = lean_ctor_get(v_l_1624_, 1);
v_v_1651_ = lean_ctor_get(v_l_1624_, 2);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_l_1624_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; lean_object* v_unused_1668_; lean_object* v_unused_1669_; 
v_unused_1667_ = lean_ctor_get(v_l_1624_, 4);
lean_dec(v_unused_1667_);
v_unused_1668_ = lean_ctor_get(v_l_1624_, 3);
lean_dec(v_unused_1668_);
v_unused_1669_ = lean_ctor_get(v_l_1624_, 0);
lean_dec(v_unused_1669_);
v___x_1653_ = v_l_1624_;
v_isShared_1654_ = v_isSharedCheck_1666_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_v_1651_);
lean_inc(v_k_1650_);
lean_dec(v_l_1624_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1666_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1655_ = lean_unsigned_to_nat(3u);
v___x_1656_ = lean_unsigned_to_nat(1u);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 4, v_r_1625_);
lean_ctor_set(v___x_1653_, 3, v_r_1625_);
lean_ctor_set(v___x_1653_, 2, v_v_1342_);
lean_ctor_set(v___x_1653_, 1, v_k_1341_);
lean_ctor_set(v___x_1653_, 0, v___x_1656_);
v___x_1658_ = v___x_1653_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1656_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v_r_1625_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v_r_1625_);
v___x_1658_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1660_; 
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 3, v_r_1625_);
lean_ctor_set(v___x_1648_, 0, v___x_1656_);
v___x_1660_ = v___x_1648_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1656_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_k_1645_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_v_1646_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v_r_1625_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v_r_1625_);
v___x_1660_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1662_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v___x_1660_);
lean_ctor_set(v___x_1346_, 3, v___x_1658_);
lean_ctor_set(v___x_1346_, 2, v_v_1651_);
lean_ctor_set(v___x_1346_, 1, v_k_1650_);
lean_ctor_set(v___x_1346_, 0, v___x_1655_);
v___x_1662_ = v___x_1346_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_k_1650_);
lean_ctor_set(v_reuseFailAlloc_1663_, 2, v_v_1651_);
lean_ctor_set(v_reuseFailAlloc_1663_, 3, v___x_1658_);
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
}
}
}
}
else
{
lean_object* v_r_1674_; 
v_r_1674_ = lean_ctor_get(v___x_1527_, 4);
lean_inc(v_r_1674_);
if (lean_obj_tag(v_r_1674_) == 0)
{
lean_object* v_k_1675_; lean_object* v_v_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1688_; 
v_k_1675_ = lean_ctor_get(v___x_1527_, 1);
v_v_1676_ = lean_ctor_get(v___x_1527_, 2);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; lean_object* v_unused_1690_; lean_object* v_unused_1691_; 
v_unused_1689_ = lean_ctor_get(v___x_1527_, 4);
lean_dec(v_unused_1689_);
v_unused_1690_ = lean_ctor_get(v___x_1527_, 3);
lean_dec(v_unused_1690_);
v_unused_1691_ = lean_ctor_get(v___x_1527_, 0);
lean_dec(v_unused_1691_);
v___x_1678_ = v___x_1527_;
v_isShared_1679_ = v_isSharedCheck_1688_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_v_1676_);
lean_inc(v_k_1675_);
lean_dec(v___x_1527_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1688_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1680_ = lean_unsigned_to_nat(3u);
v___x_1681_ = lean_unsigned_to_nat(1u);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 4, v_l_1624_);
lean_ctor_set(v___x_1678_, 2, v_v_1342_);
lean_ctor_set(v___x_1678_, 1, v_k_1341_);
lean_ctor_set(v___x_1678_, 0, v___x_1681_);
v___x_1683_ = v___x_1678_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_l_1624_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_l_1624_);
v___x_1683_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1685_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v_r_1674_);
lean_ctor_set(v___x_1346_, 3, v___x_1683_);
lean_ctor_set(v___x_1346_, 2, v_v_1676_);
lean_ctor_set(v___x_1346_, 1, v_k_1675_);
lean_ctor_set(v___x_1346_, 0, v___x_1680_);
v___x_1685_ = v___x_1346_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_k_1675_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_v_1676_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1686_, 4, v_r_1674_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1692_ = lean_unsigned_to_nat(2u);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v___x_1527_);
lean_ctor_set(v___x_1346_, 3, v_r_1674_);
lean_ctor_set(v___x_1346_, 0, v___x_1692_);
v___x_1694_ = v___x_1346_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1695_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1695_, 3, v_r_1674_);
lean_ctor_set(v_reuseFailAlloc_1695_, 4, v___x_1527_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = lean_unsigned_to_nat(1u);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v___x_1527_);
lean_ctor_set(v___x_1346_, 3, v___x_1527_);
lean_ctor_set(v___x_1346_, 0, v___x_1696_);
v___x_1698_ = v___x_1346_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1699_, 4, v___x_1527_);
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
}
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = lean_unsigned_to_nat(1u);
v___x_1702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
lean_ctor_set(v___x_1702_, 1, v_k_1337_);
lean_ctor_set(v___x_1702_, 2, v_v_1338_);
lean_ctor_set(v___x_1702_, 3, v_t_1339_);
lean_ctor_set(v___x_1702_, 4, v_t_1339_);
return v___x_1702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore(lean_object* v_kvs_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_fst_1723_; lean_object* v_snd_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v_fst_1723_ = lean_ctor_get(v_a_1722_, 0);
v_snd_1724_ = lean_ctor_get(v_a_1722_, 1);
v___x_1725_ = lean_string_utf8_byte_size(v_fst_1723_);
v___x_1726_ = lean_nat_dec_eq(v_snd_1724_, v___x_1725_);
if (v___x_1726_ == 0)
{
uint32_t v___x_1727_; uint32_t v___x_1728_; uint8_t v___x_1729_; 
v___x_1727_ = lean_string_utf8_get_fast(v_fst_1723_, v_snd_1724_);
v___x_1728_ = 34;
v___x_1729_ = lean_uint32_dec_eq(v___x_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec(v_kvs_1721_);
v___x_1730_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__1));
v___x_1731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1731_, 0, v_a_1722_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
return v___x_1731_;
}
else
{
lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1835_; 
lean_inc(v_snd_1724_);
lean_inc(v_fst_1723_);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_a_1722_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; lean_object* v_unused_1837_; 
v_unused_1836_ = lean_ctor_get(v_a_1722_, 1);
lean_dec(v_unused_1836_);
v_unused_1837_ = lean_ctor_get(v_a_1722_, 0);
lean_dec(v_unused_1837_);
v___x_1733_ = v_a_1722_;
v_isShared_1734_ = v_isSharedCheck_1835_;
goto v_resetjp_1732_;
}
else
{
lean_dec(v_a_1722_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1835_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1735_ = lean_string_utf8_next_fast(v_fst_1723_, v_snd_1724_);
lean_dec(v_snd_1724_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 1, v___x_1735_);
v___x_1737_ = v___x_1733_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_fst_1723_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_1739_ = l_Lean_Json_Parser_strCore(v___x_1738_, v___x_1737_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_pos_1740_; lean_object* v_res_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1824_; 
v_pos_1740_ = lean_ctor_get(v___x_1739_, 0);
v_res_1741_ = lean_ctor_get(v___x_1739_, 1);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1743_ = v___x_1739_;
v_isShared_1744_ = v_isSharedCheck_1824_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_res_1741_);
lean_inc(v_pos_1740_);
lean_dec(v___x_1739_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1824_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v_fst_1745_; lean_object* v_snd_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1823_; 
v_fst_1745_ = lean_ctor_get(v_pos_1740_, 0);
v_snd_1746_ = lean_ctor_get(v_pos_1740_, 1);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_pos_1740_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1748_ = v_pos_1740_;
v_isShared_1749_ = v_isSharedCheck_1823_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_snd_1746_);
lean_inc(v_fst_1745_);
lean_dec(v_pos_1740_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1823_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1750_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1745_, v_snd_1746_);
lean_inc(v___x_1750_);
lean_inc(v_fst_1745_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 1, v___x_1750_);
v___x_1752_ = v___x_1748_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_fst_1745_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = lean_string_utf8_byte_size(v_fst_1745_);
v___x_1759_ = lean_nat_dec_eq(v___x_1750_, v___x_1758_);
if (v___x_1759_ == 0)
{
if (v___x_1729_ == 0)
{
lean_dec(v___x_1750_);
lean_dec(v_fst_1745_);
lean_dec(v_res_1741_);
lean_dec(v_kvs_1721_);
goto v___jp_1753_;
}
else
{
uint32_t v___x_1760_; uint32_t v___x_1761_; uint8_t v___x_1762_; 
lean_del_object(v___x_1743_);
v___x_1760_ = lean_string_utf8_get_fast(v_fst_1745_, v___x_1750_);
v___x_1761_ = 58;
v___x_1762_ = lean_uint32_dec_eq(v___x_1760_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
lean_dec(v___x_1750_);
lean_dec(v_fst_1745_);
lean_dec(v_res_1741_);
lean_dec(v_kvs_1721_);
v___x_1763_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__3));
v___x_1764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1752_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
return v___x_1764_;
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_dec_ref(v___x_1752_);
v___x_1765_ = lean_string_utf8_next_fast(v_fst_1745_, v___x_1750_);
lean_dec(v___x_1750_);
v___x_1766_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1745_, v___x_1765_);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_fst_1745_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = l_Lean_Json_Parser_anyCore(v___x_1767_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_pos_1769_; lean_object* v_res_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1812_; 
v_pos_1769_ = lean_ctor_get(v___x_1768_, 0);
v_res_1770_ = lean_ctor_get(v___x_1768_, 1);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1772_ = v___x_1768_;
v_isShared_1773_ = v_isSharedCheck_1812_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_res_1770_);
lean_inc(v_pos_1769_);
lean_dec(v___x_1768_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1812_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v_fst_1779_; lean_object* v_snd_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v_fst_1779_ = lean_ctor_get(v_pos_1769_, 0);
v_snd_1780_ = lean_ctor_get(v_pos_1769_, 1);
v___x_1781_ = lean_string_utf8_byte_size(v_fst_1779_);
v___x_1782_ = lean_nat_dec_eq(v_snd_1780_, v___x_1781_);
if (v___x_1782_ == 0)
{
if (v___x_1762_ == 0)
{
lean_dec(v_res_1770_);
lean_dec(v_res_1741_);
lean_dec(v_kvs_1721_);
goto v___jp_1774_;
}
else
{
lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1809_; 
lean_inc(v_snd_1780_);
lean_inc(v_fst_1779_);
lean_del_object(v___x_1772_);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_pos_1769_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; lean_object* v_unused_1811_; 
v_unused_1810_ = lean_ctor_get(v_pos_1769_, 1);
lean_dec(v_unused_1810_);
v_unused_1811_ = lean_ctor_get(v_pos_1769_, 0);
lean_dec(v_unused_1811_);
v___x_1784_ = v_pos_1769_;
v_isShared_1785_ = v_isSharedCheck_1809_;
goto v_resetjp_1783_;
}
else
{
lean_dec(v_pos_1769_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1809_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
uint32_t v___x_1786_; lean_object* v___x_1787_; uint32_t v___x_1788_; uint8_t v___x_1789_; 
v___x_1786_ = lean_string_utf8_get_fast(v_fst_1779_, v_snd_1780_);
v___x_1787_ = lean_string_utf8_next_fast(v_fst_1779_, v_snd_1780_);
lean_dec(v_snd_1780_);
v___x_1788_ = 125;
v___x_1789_ = lean_uint32_dec_eq(v___x_1786_, v___x_1788_);
if (v___x_1789_ == 0)
{
uint32_t v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = 44;
v___x_1791_ = lean_uint32_dec_eq(v___x_1786_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1793_; 
lean_dec(v_res_1770_);
lean_dec(v_res_1741_);
lean_dec(v_kvs_1721_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 1, v___x_1787_);
v___x_1793_ = v___x_1784_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_fst_1779_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v___x_1787_);
v___x_1793_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__5));
v___x_1795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1793_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
return v___x_1795_;
}
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1799_; 
v___x_1797_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1779_, v___x_1787_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 1, v___x_1797_);
v___x_1799_ = v___x_1784_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_fst_1779_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_res_1741_, v_res_1770_, v_kvs_1721_);
v_kvs_1721_ = v___x_1800_;
v_a_1722_ = v___x_1799_;
goto _start;
}
}
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1803_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1779_, v___x_1787_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 1, v___x_1803_);
v___x_1805_ = v___x_1784_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_fst_1779_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_res_1741_, v_res_1770_, v_kvs_1721_);
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1805_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
return v___x_1807_;
}
}
}
}
}
else
{
lean_dec(v_res_1770_);
lean_dec(v_res_1741_);
lean_dec(v_kvs_1721_);
goto v___jp_1774_;
}
v___jp_1774_:
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = lean_box(0);
if (v_isShared_1773_ == 0)
{
lean_ctor_set_tag(v___x_1772_, 1);
lean_ctor_set(v___x_1772_, 1, v___x_1775_);
v___x_1777_ = v___x_1772_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_pos_1769_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
else
{
lean_object* v_pos_1813_; lean_object* v_err_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_dec(v_res_1741_);
lean_dec(v_kvs_1721_);
v_pos_1813_ = lean_ctor_get(v___x_1768_, 0);
v_err_1814_ = lean_ctor_get(v___x_1768_, 1);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1768_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_err_1814_);
lean_inc(v_pos_1813_);
lean_dec(v___x_1768_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_pos_1813_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_err_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1750_);
lean_dec(v_fst_1745_);
lean_dec(v_res_1741_);
lean_dec(v_kvs_1721_);
goto v___jp_1753_;
}
v___jp_1753_:
{
lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1754_ = lean_box(0);
if (v_isShared_1744_ == 0)
{
lean_ctor_set_tag(v___x_1743_, 1);
lean_ctor_set(v___x_1743_, 1, v___x_1754_);
lean_ctor_set(v___x_1743_, 0, v___x_1752_);
v___x_1756_ = v___x_1743_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1825_; lean_object* v_err_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec(v_kvs_1721_);
v_pos_1825_ = lean_ctor_get(v___x_1739_, 0);
v_err_1826_ = lean_ctor_get(v___x_1739_, 1);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1739_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_err_1826_);
lean_inc(v_pos_1825_);
lean_dec(v___x_1739_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_pos_1825_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_err_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_dec(v_kvs_1721_);
v___x_1838_ = lean_box(0);
v___x_1839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1839_, 0, v_a_1722_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
return v___x_1839_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object* v_a_1846_){
_start:
{
uint8_t v___y_1879_; lean_object* v_fst_1882_; lean_object* v_snd_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; 
v_fst_1882_ = lean_ctor_get(v_a_1846_, 0);
v_snd_1883_ = lean_ctor_get(v_a_1846_, 1);
v___x_1884_ = lean_string_utf8_byte_size(v_fst_1882_);
v___x_1885_ = lean_nat_dec_eq(v_snd_1883_, v___x_1884_);
if (v___x_1885_ == 0)
{
uint32_t v___x_1886_; uint32_t v___x_1887_; uint8_t v___x_1888_; 
v___x_1886_ = lean_string_utf8_get_fast(v_fst_1882_, v_snd_1883_);
v___x_1887_ = 91;
v___x_1888_ = lean_uint32_dec_eq(v___x_1886_, v___x_1887_);
if (v___x_1888_ == 0)
{
uint32_t v___x_1889_; uint8_t v___x_1890_; 
v___x_1889_ = 123;
v___x_1890_ = lean_uint32_dec_eq(v___x_1886_, v___x_1889_);
if (v___x_1890_ == 0)
{
uint32_t v___x_1891_; uint8_t v___x_1892_; 
v___x_1891_ = 34;
v___x_1892_ = lean_uint32_dec_eq(v___x_1886_, v___x_1891_);
if (v___x_1892_ == 0)
{
uint32_t v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = 102;
v___x_1894_ = lean_uint32_dec_eq(v___x_1886_, v___x_1893_);
if (v___x_1894_ == 0)
{
uint32_t v___x_1895_; uint8_t v___x_1896_; 
v___x_1895_ = 116;
v___x_1896_ = lean_uint32_dec_eq(v___x_1886_, v___x_1895_);
if (v___x_1896_ == 0)
{
uint32_t v___x_1897_; uint8_t v___x_1898_; 
v___x_1897_ = 110;
v___x_1898_ = lean_uint32_dec_eq(v___x_1886_, v___x_1897_);
if (v___x_1898_ == 0)
{
uint32_t v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = 45;
v___x_1900_ = lean_uint32_dec_eq(v___x_1886_, v___x_1899_);
if (v___x_1900_ == 0)
{
uint32_t v___x_1901_; uint8_t v___x_1902_; 
v___x_1901_ = 48;
v___x_1902_ = lean_uint32_dec_le(v___x_1901_, v___x_1886_);
if (v___x_1902_ == 0)
{
v___y_1879_ = v___x_1902_;
goto v___jp_1878_;
}
else
{
uint32_t v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = 57;
v___x_1904_ = lean_uint32_dec_le(v___x_1886_, v___x_1903_);
v___y_1879_ = v___x_1904_;
goto v___jp_1878_;
}
}
else
{
goto v___jp_1847_;
}
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__2));
v___x_1906_ = l_Std_Internal_Parsec_String_pstring(v___x_1905_, v_a_1846_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_pos_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1925_; 
v_pos_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1925_ == 0)
{
lean_object* v_unused_1926_; 
v_unused_1926_ = lean_ctor_get(v___x_1906_, 1);
lean_dec(v_unused_1926_);
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1925_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_pos_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1925_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v_fst_1911_; lean_object* v_snd_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1924_; 
v_fst_1911_ = lean_ctor_get(v_pos_1907_, 0);
v_snd_1912_ = lean_ctor_get(v_pos_1907_, 1);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_pos_1907_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1914_ = v_pos_1907_;
v_isShared_1915_ = v_isSharedCheck_1924_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_snd_1912_);
lean_inc(v_fst_1911_);
lean_dec(v_pos_1907_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1924_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___x_1916_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1911_, v_snd_1912_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 1, v___x_1916_);
v___x_1918_ = v___x_1914_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_fst_1911_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1919_ = lean_box(0);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 1, v___x_1919_);
lean_ctor_set(v___x_1909_, 0, v___x_1918_);
v___x_1921_ = v___x_1909_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
else
{
lean_object* v_pos_1927_; lean_object* v_err_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
v_pos_1927_ = lean_ctor_get(v___x_1906_, 0);
v_err_1928_ = lean_ctor_get(v___x_1906_, 1);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1906_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_err_1928_);
lean_inc(v_pos_1927_);
lean_dec(v___x_1906_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_pos_1927_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_err_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__3));
v___x_1937_ = l_Std_Internal_Parsec_String_pstring(v___x_1936_, v_a_1846_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_pos_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1956_; 
v_pos_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1956_ == 0)
{
lean_object* v_unused_1957_; 
v_unused_1957_ = lean_ctor_get(v___x_1937_, 1);
lean_dec(v_unused_1957_);
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1956_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_pos_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1956_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v_fst_1942_; lean_object* v_snd_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1955_; 
v_fst_1942_ = lean_ctor_get(v_pos_1938_, 0);
v_snd_1943_ = lean_ctor_get(v_pos_1938_, 1);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_pos_1938_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1945_ = v_pos_1938_;
v_isShared_1946_ = v_isSharedCheck_1955_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_snd_1943_);
lean_inc(v_fst_1942_);
lean_dec(v_pos_1938_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1955_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1947_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1942_, v_snd_1943_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v___x_1947_);
v___x_1949_ = v___x_1945_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_fst_1942_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1950_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1950_, 0, v___x_1896_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 1, v___x_1950_);
lean_ctor_set(v___x_1940_, 0, v___x_1949_);
v___x_1952_ = v___x_1940_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
else
{
lean_object* v_pos_1958_; lean_object* v_err_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
v_pos_1958_ = lean_ctor_get(v___x_1937_, 0);
v_err_1959_ = lean_ctor_get(v___x_1937_, 1);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1937_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_err_1959_);
lean_inc(v_pos_1958_);
lean_dec(v___x_1937_);
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
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__4));
v___x_1968_ = l_Std_Internal_Parsec_String_pstring(v___x_1967_, v_a_1846_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_pos_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1987_; 
v_pos_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; 
v_unused_1988_ = lean_ctor_get(v___x_1968_, 1);
lean_dec(v_unused_1988_);
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1987_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_pos_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1987_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v_fst_1973_; lean_object* v_snd_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1986_; 
v_fst_1973_ = lean_ctor_get(v_pos_1969_, 0);
v_snd_1974_ = lean_ctor_get(v_pos_1969_, 1);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_pos_1969_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1976_ = v_pos_1969_;
v_isShared_1977_ = v_isSharedCheck_1986_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_snd_1974_);
lean_inc(v_fst_1973_);
lean_dec(v_pos_1969_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1986_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1978_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1973_, v_snd_1974_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 1, v___x_1978_);
v___x_1980_ = v___x_1976_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_fst_1973_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1981_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1981_, 0, v___x_1892_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 1, v___x_1981_);
lean_ctor_set(v___x_1971_, 0, v___x_1980_);
v___x_1983_ = v___x_1971_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
else
{
lean_object* v_pos_1989_; lean_object* v_err_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
v_pos_1989_ = lean_ctor_get(v___x_1968_, 0);
v_err_1990_ = lean_ctor_get(v___x_1968_, 1);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1968_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_err_1990_);
lean_inc(v_pos_1989_);
lean_dec(v___x_1968_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_pos_1989_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_err_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
}
else
{
lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2036_; 
lean_inc(v_snd_1883_);
lean_inc(v_fst_1882_);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_a_1846_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; lean_object* v_unused_2038_; 
v_unused_2037_ = lean_ctor_get(v_a_1846_, 1);
lean_dec(v_unused_2037_);
v_unused_2038_ = lean_ctor_get(v_a_1846_, 0);
lean_dec(v_unused_2038_);
v___x_1999_ = v_a_1846_;
v_isShared_2000_ = v_isSharedCheck_2036_;
goto v_resetjp_1998_;
}
else
{
lean_dec(v_a_1846_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2036_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2001_; lean_object* v___x_2003_; 
v___x_2001_ = lean_string_utf8_next_fast(v_fst_1882_, v_snd_1883_);
lean_dec(v_snd_1883_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 1, v___x_2001_);
v___x_2003_ = v___x_1999_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_fst_1882_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_2005_ = l_Lean_Json_Parser_strCore(v___x_2004_, v___x_2003_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_pos_2006_; lean_object* v_res_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2025_; 
v_pos_2006_ = lean_ctor_get(v___x_2005_, 0);
v_res_2007_ = lean_ctor_get(v___x_2005_, 1);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2009_ = v___x_2005_;
v_isShared_2010_ = v_isSharedCheck_2025_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_res_2007_);
lean_inc(v_pos_2006_);
lean_dec(v___x_2005_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2025_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_fst_2011_; lean_object* v_snd_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2024_; 
v_fst_2011_ = lean_ctor_get(v_pos_2006_, 0);
v_snd_2012_ = lean_ctor_get(v_pos_2006_, 1);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_pos_2006_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2014_ = v_pos_2006_;
v_isShared_2015_ = v_isSharedCheck_2024_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_snd_2012_);
lean_inc(v_fst_2011_);
lean_dec(v_pos_2006_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2024_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2011_, v_snd_2012_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 1, v___x_2016_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_fst_2011_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2019_, 0, v_res_2007_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 1, v___x_2019_);
lean_ctor_set(v___x_2009_, 0, v___x_2018_);
v___x_2021_ = v___x_2009_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_2019_);
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
}
else
{
lean_object* v_pos_2026_; lean_object* v_err_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
v_pos_2026_ = lean_ctor_get(v___x_2005_, 0);
v_err_2027_ = lean_ctor_get(v___x_2005_, 1);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2005_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_err_2027_);
lean_inc(v_pos_2026_);
lean_dec(v___x_2005_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_pos_2026_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_err_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2081_; 
lean_inc(v_snd_1883_);
lean_inc(v_fst_1882_);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_a_1846_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; lean_object* v_unused_2083_; 
v_unused_2082_ = lean_ctor_get(v_a_1846_, 1);
lean_dec(v_unused_2082_);
v_unused_2083_ = lean_ctor_get(v_a_1846_, 0);
lean_dec(v_unused_2083_);
v___x_2040_ = v_a_1846_;
v_isShared_2041_ = v_isSharedCheck_2081_;
goto v_resetjp_2039_;
}
else
{
lean_dec(v_a_1846_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2081_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2042_ = lean_string_utf8_next_fast(v_fst_1882_, v_snd_1883_);
lean_dec(v_snd_1883_);
v___x_2043_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1882_, v___x_2042_);
lean_inc(v___x_2043_);
lean_inc(v_fst_1882_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 1, v___x_2043_);
v___x_2045_ = v___x_2040_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_fst_1882_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
uint8_t v___y_2047_; uint8_t v___x_2079_; 
v___x_2079_ = lean_nat_dec_eq(v___x_2043_, v___x_1884_);
if (v___x_2079_ == 0)
{
v___y_2047_ = v___x_1890_;
goto v___jp_2046_;
}
else
{
v___y_2047_ = v___x_1888_;
goto v___jp_2046_;
}
v___jp_2046_:
{
if (v___y_2047_ == 0)
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_dec(v___x_2043_);
lean_dec(v_fst_1882_);
v___x_2048_ = lean_box(0);
v___x_2049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2045_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
return v___x_2049_;
}
else
{
uint32_t v___x_2050_; uint32_t v___x_2051_; uint8_t v___x_2052_; 
v___x_2050_ = lean_string_utf8_get_fast(v_fst_1882_, v___x_2043_);
v___x_2051_ = 125;
v___x_2052_ = lean_uint32_dec_eq(v___x_2050_, v___x_2051_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
lean_dec(v___x_2043_);
lean_dec(v_fst_1882_);
v___x_2053_ = lean_box(1);
v___x_2054_ = l_Lean_Json_Parser_objectCore(v___x_2053_, v___x_2045_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_pos_2055_; lean_object* v_res_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2064_; 
v_pos_2055_ = lean_ctor_get(v___x_2054_, 0);
v_res_2056_ = lean_ctor_get(v___x_2054_, 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2058_ = v___x_2054_;
v_isShared_2059_ = v_isSharedCheck_2064_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_res_2056_);
lean_inc(v_pos_2055_);
lean_dec(v___x_2054_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2064_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2060_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2060_, 0, v_res_2056_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 1, v___x_2060_);
v___x_2062_ = v___x_2058_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_pos_2055_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
else
{
lean_object* v_pos_2065_; lean_object* v_err_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
v_pos_2065_ = lean_ctor_get(v___x_2054_, 0);
v_err_2066_ = lean_ctor_get(v___x_2054_, 1);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2054_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_err_2066_);
lean_inc(v_pos_2065_);
lean_dec(v___x_2054_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_pos_2065_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_err_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec_ref(v___x_2045_);
v___x_2074_ = lean_string_utf8_next_fast(v_fst_1882_, v___x_2043_);
lean_dec(v___x_2043_);
v___x_2075_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1882_, v___x_2074_);
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v_fst_1882_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__5));
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2076_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
return v___x_2078_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2126_; 
lean_inc(v_snd_1883_);
lean_inc(v_fst_1882_);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_a_1846_);
if (v_isSharedCheck_2126_ == 0)
{
lean_object* v_unused_2127_; lean_object* v_unused_2128_; 
v_unused_2127_ = lean_ctor_get(v_a_1846_, 1);
lean_dec(v_unused_2127_);
v_unused_2128_ = lean_ctor_get(v_a_1846_, 0);
lean_dec(v_unused_2128_);
v___x_2085_ = v_a_1846_;
v_isShared_2086_ = v_isSharedCheck_2126_;
goto v_resetjp_2084_;
}
else
{
lean_dec(v_a_1846_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2126_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2087_ = lean_string_utf8_next_fast(v_fst_1882_, v_snd_1883_);
lean_dec(v_snd_1883_);
v___x_2088_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1882_, v___x_2087_);
lean_inc(v___x_2088_);
lean_inc(v_fst_1882_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 1, v___x_2088_);
v___x_2090_ = v___x_2085_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_fst_1882_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v___x_2088_);
v___x_2090_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
uint8_t v___x_2094_; 
v___x_2094_ = lean_nat_dec_eq(v___x_2088_, v___x_1884_);
if (v___x_2094_ == 0)
{
if (v___x_1888_ == 0)
{
lean_dec(v___x_2088_);
lean_dec(v_fst_1882_);
goto v___jp_2091_;
}
else
{
uint32_t v___x_2095_; uint32_t v___x_2096_; uint8_t v___x_2097_; 
v___x_2095_ = lean_string_utf8_get_fast(v_fst_1882_, v___x_2088_);
v___x_2096_ = 93;
v___x_2097_ = lean_uint32_dec_eq(v___x_2095_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_dec(v___x_2088_);
lean_dec(v_fst_1882_);
v___x_2098_ = lean_unsigned_to_nat(4u);
v___x_2099_ = lean_mk_empty_array_with_capacity(v___x_2098_);
v___x_2100_ = l_Lean_Json_Parser_arrayCore(v___x_2099_, v___x_2090_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_pos_2101_; lean_object* v_res_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2110_; 
v_pos_2101_ = lean_ctor_get(v___x_2100_, 0);
v_res_2102_ = lean_ctor_get(v___x_2100_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2104_ = v___x_2100_;
v_isShared_2105_ = v_isSharedCheck_2110_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_res_2102_);
lean_inc(v_pos_2101_);
lean_dec(v___x_2100_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2110_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2106_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2106_, 0, v_res_2102_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 1, v___x_2106_);
v___x_2108_ = v___x_2104_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_pos_2101_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
else
{
lean_object* v_pos_2111_; lean_object* v_err_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
v_pos_2111_ = lean_ctor_get(v___x_2100_, 0);
v_err_2112_ = lean_ctor_get(v___x_2100_, 1);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2100_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_err_2112_);
lean_inc(v_pos_2111_);
lean_dec(v___x_2100_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_pos_2111_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_err_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
lean_dec_ref(v___x_2090_);
v___x_2120_ = lean_string_utf8_next_fast(v_fst_1882_, v___x_2088_);
lean_dec(v___x_2088_);
v___x_2121_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1882_, v___x_2120_);
v___x_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2122_, 0, v_fst_1882_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__7));
v___x_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
return v___x_2124_;
}
}
}
else
{
lean_dec(v___x_2088_);
lean_dec(v_fst_1882_);
goto v___jp_2091_;
}
v___jp_2091_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = lean_box(0);
v___x_2093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2090_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
return v___x_2093_;
}
}
}
}
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_box(0);
v___x_2130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2130_, 0, v_a_1846_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
return v___x_2130_;
}
v___jp_1847_:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_Json_Parser_num(v_a_1846_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_pos_1849_; lean_object* v_res_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1868_; 
v_pos_1849_ = lean_ctor_get(v___x_1848_, 0);
v_res_1850_ = lean_ctor_get(v___x_1848_, 1);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1852_ = v___x_1848_;
v_isShared_1853_ = v_isSharedCheck_1868_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_res_1850_);
lean_inc(v_pos_1849_);
lean_dec(v___x_1848_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1868_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v_fst_1854_; lean_object* v_snd_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1867_; 
v_fst_1854_ = lean_ctor_get(v_pos_1849_, 0);
v_snd_1855_ = lean_ctor_get(v_pos_1849_, 1);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_pos_1849_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1857_ = v_pos_1849_;
v_isShared_1858_ = v_isSharedCheck_1867_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_snd_1855_);
lean_inc(v_fst_1854_);
lean_dec(v_pos_1849_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1867_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1854_, v_snd_1855_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 1, v___x_1859_);
v___x_1861_ = v___x_1857_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_fst_1854_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1862_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1862_, 0, v_res_1850_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 1, v___x_1862_);
lean_ctor_set(v___x_1852_, 0, v___x_1861_);
v___x_1864_ = v___x_1852_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
else
{
lean_object* v_pos_1869_; lean_object* v_err_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
v_pos_1869_ = lean_ctor_get(v___x_1848_, 0);
v_err_1870_ = lean_ctor_get(v___x_1848_, 1);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1848_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_err_1870_);
lean_inc(v_pos_1869_);
lean_dec(v___x_1848_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_pos_1869_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_err_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
v___jp_1878_:
{
if (v___y_1879_ == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__1));
v___x_1881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1881_, 0, v_a_1846_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
return v___x_1881_;
}
else
{
goto v___jp_1847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore(lean_object* v_acc_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Lean_Json_Parser_anyCore(v_a_2132_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_pos_2134_; lean_object* v_res_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2179_; 
v_pos_2134_ = lean_ctor_get(v___x_2133_, 0);
v_res_2135_ = lean_ctor_get(v___x_2133_, 1);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2137_ = v___x_2133_;
v_isShared_2138_ = v_isSharedCheck_2179_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_res_2135_);
lean_inc(v_pos_2134_);
lean_dec(v___x_2133_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2179_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v_fst_2139_; lean_object* v_snd_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v_fst_2139_ = lean_ctor_get(v_pos_2134_, 0);
v_snd_2140_ = lean_ctor_get(v_pos_2134_, 1);
v___x_2141_ = lean_string_utf8_byte_size(v_fst_2139_);
v___x_2142_ = lean_nat_dec_eq(v_snd_2140_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2172_; 
lean_inc(v_snd_2140_);
lean_inc(v_fst_2139_);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_pos_2134_);
if (v_isSharedCheck_2172_ == 0)
{
lean_object* v_unused_2173_; lean_object* v_unused_2174_; 
v_unused_2173_ = lean_ctor_get(v_pos_2134_, 1);
lean_dec(v_unused_2173_);
v_unused_2174_ = lean_ctor_get(v_pos_2134_, 0);
lean_dec(v_unused_2174_);
v___x_2144_ = v_pos_2134_;
v_isShared_2145_ = v_isSharedCheck_2172_;
goto v_resetjp_2143_;
}
else
{
lean_dec(v_pos_2134_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2172_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; uint32_t v___x_2147_; lean_object* v___x_2148_; uint32_t v___x_2149_; uint8_t v___x_2150_; 
v___x_2146_ = lean_array_push(v_acc_2131_, v_res_2135_);
v___x_2147_ = lean_string_utf8_get_fast(v_fst_2139_, v_snd_2140_);
v___x_2148_ = lean_string_utf8_next_fast(v_fst_2139_, v_snd_2140_);
lean_dec(v_snd_2140_);
v___x_2149_ = 93;
v___x_2150_ = lean_uint32_dec_eq(v___x_2147_, v___x_2149_);
if (v___x_2150_ == 0)
{
uint32_t v___x_2151_; uint8_t v___x_2152_; 
v___x_2151_ = 44;
v___x_2152_ = lean_uint32_dec_eq(v___x_2147_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2154_; 
lean_dec_ref(v___x_2146_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 1, v___x_2148_);
v___x_2154_ = v___x_2144_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_fst_2139_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2148_);
v___x_2154_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2157_; 
v___x_2155_ = ((lean_object*)(l_Lean_Json_Parser_arrayCore___closed__1));
if (v_isShared_2138_ == 0)
{
lean_ctor_set_tag(v___x_2137_, 1);
lean_ctor_set(v___x_2137_, 1, v___x_2155_);
lean_ctor_set(v___x_2137_, 0, v___x_2154_);
v___x_2157_ = v___x_2137_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2154_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
else
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
lean_del_object(v___x_2137_);
v___x_2160_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2139_, v___x_2148_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 1, v___x_2160_);
v___x_2162_ = v___x_2144_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_fst_2139_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
v_acc_2131_ = v___x_2146_;
v_a_2132_ = v___x_2162_;
goto _start;
}
}
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2165_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2139_, v___x_2148_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 1, v___x_2165_);
v___x_2167_ = v___x_2144_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_fst_2139_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2169_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 1, v___x_2146_);
lean_ctor_set(v___x_2137_, 0, v___x_2167_);
v___x_2169_ = v___x_2137_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v___x_2146_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
lean_dec(v_res_2135_);
lean_dec_ref(v_acc_2131_);
v___x_2175_ = lean_box(0);
if (v_isShared_2138_ == 0)
{
lean_ctor_set_tag(v___x_2137_, 1);
lean_ctor_set(v___x_2137_, 1, v___x_2175_);
v___x_2177_ = v___x_2137_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_pos_2134_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v_pos_2180_; lean_object* v_err_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec_ref(v_acc_2131_);
v_pos_2180_ = lean_ctor_get(v___x_2133_, 0);
v_err_2181_ = lean_ctor_get(v___x_2133_, 1);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2133_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_err_2181_);
lean_inc(v_pos_2180_);
lean_dec(v___x_2133_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_pos_2180_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_err_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2(lean_object* v_00_u03b2_2189_, lean_object* v_msg_2190_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v_msg_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2(lean_object* v_00_u03b2_2192_, lean_object* v_k_2193_, lean_object* v_v_2194_, lean_object* v_t_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_2193_, v_v_2194_, v_t_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_any(lean_object* v_a_2200_){
_start:
{
lean_object* v_fst_2201_; lean_object* v_snd_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2226_; 
v_fst_2201_ = lean_ctor_get(v_a_2200_, 0);
v_snd_2202_ = lean_ctor_get(v_a_2200_, 1);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_a_2200_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2204_ = v_a_2200_;
v_isShared_2205_ = v_isSharedCheck_2226_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_snd_2202_);
lean_inc(v_fst_2201_);
lean_dec(v_a_2200_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2226_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2206_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2201_, v_snd_2202_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 1, v___x_2206_);
v___x_2208_ = v___x_2204_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_fst_2201_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Lean_Json_Parser_anyCore(v___x_2208_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_pos_2210_; lean_object* v_fst_2211_; lean_object* v_snd_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; 
v_pos_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_pos_2210_);
v_fst_2211_ = lean_ctor_get(v_pos_2210_, 0);
v_snd_2212_ = lean_ctor_get(v_pos_2210_, 1);
v___x_2213_ = lean_string_utf8_byte_size(v_fst_2211_);
v___x_2214_ = lean_nat_dec_eq(v_snd_2212_, v___x_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2222_; 
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; lean_object* v_unused_2224_; 
v_unused_2223_ = lean_ctor_get(v___x_2209_, 1);
lean_dec(v_unused_2223_);
v_unused_2224_ = lean_ctor_get(v___x_2209_, 0);
lean_dec(v_unused_2224_);
v___x_2216_ = v___x_2209_;
v_isShared_2217_ = v_isSharedCheck_2222_;
goto v_resetjp_2215_;
}
else
{
lean_dec(v___x_2209_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2222_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2218_ = ((lean_object*)(l_Lean_Json_Parser_any___closed__1));
if (v_isShared_2217_ == 0)
{
lean_ctor_set_tag(v___x_2216_, 1);
lean_ctor_set(v___x_2216_, 1, v___x_2218_);
v___x_2220_ = v___x_2216_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_pos_2210_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
else
{
lean_dec(v_pos_2210_);
return v___x_2209_;
}
}
else
{
return v___x_2209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parse(lean_object* v_s_2227_){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
v___x_2229_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_2228_, v_s_2227_);
return v___x_2229_;
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
