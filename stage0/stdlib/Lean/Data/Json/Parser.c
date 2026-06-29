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
lean_dec_ref_known(v___x_87_, 2);
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
lean_dec_ref_known(v___x_97_, 2);
v___x_100_ = l_Lean_Json_Parser_hexChar(v_pos_98_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_pos_101_; lean_object* v_res_102_; lean_object* v___x_103_; 
v_pos_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_pos_101_);
v_res_102_ = lean_ctor_get(v___x_100_, 1);
lean_inc(v_res_102_);
lean_dec_ref_known(v___x_100_, 2);
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
lean_dec_ref_known(v___x_250_, 2);
v___x_253_ = l_Lean_Json_Parser_hexChar(v_pos_251_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_pos_254_; lean_object* v_res_255_; lean_object* v___x_256_; 
v_pos_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_pos_254_);
v_res_255_ = lean_ctor_get(v___x_253_, 1);
lean_inc(v_res_255_);
lean_dec_ref_known(v___x_253_, 2);
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
lean_dec_ref_known(v___x_412_, 2);
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
lean_dec(v___y_689_);
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
v___x_708_ = lean_nat_to_int(v___y_689_);
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
v___x_715_ = lean_int_mul(v___y_690_, v___x_714_);
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
lean_dec(v___y_689_);
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
lean_dec(v___y_689_);
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
v___y_689_ = v_res_746_;
v___y_690_ = v___y_742_;
v___y_691_ = v___x_761_;
goto v___jp_687_;
}
else
{
uint32_t v___x_762_; uint8_t v___x_763_; 
v___x_762_ = 57;
v___x_763_ = lean_uint32_dec_le(v___x_759_, v___x_762_);
v___y_688_ = v___x_757_;
v___y_689_ = v_res_746_;
v___y_690_ = v___y_742_;
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
lean_ctor_set(v___x_773_, 0, v___y_769_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
return v___x_773_;
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = l_Lean_Json_Parser_natCore(v___x_774_, v___y_769_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_pos_776_; lean_object* v_res_777_; lean_object* v_fst_778_; lean_object* v_snd_779_; 
v_pos_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_pos_776_);
v_res_777_ = lean_ctor_get(v___x_775_, 1);
lean_inc(v_res_777_);
lean_dec_ref_known(v___x_775_, 2);
v_fst_778_ = lean_ctor_get(v_pos_776_, 0);
lean_inc(v_fst_778_);
v_snd_779_ = lean_ctor_get(v_pos_776_, 1);
lean_inc(v_snd_779_);
v___y_742_ = v___y_770_;
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
v___y_769_ = v_pos_790_;
v___y_770_ = v_res_793_;
v___y_771_ = v___x_800_;
goto v___jp_768_;
}
else
{
uint32_t v___x_801_; uint8_t v___x_802_; 
v___x_801_ = 57;
v___x_802_ = lean_uint32_dec_le(v___x_796_, v___x_801_);
v___y_769_ = v_pos_790_;
v___y_770_ = v_res_793_;
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
lean_object* v___y_957_; lean_object* v___y_958_; uint8_t v___y_959_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v_fst_992_; lean_object* v_snd_993_; lean_object* v___y_1004_; lean_object* v___y_1005_; uint8_t v___y_1006_; lean_object* v___y_1031_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v_fst_1037_; lean_object* v_snd_1038_; lean_object* v___y_1064_; lean_object* v_pos_1065_; lean_object* v_fst_1066_; lean_object* v_snd_1067_; lean_object* v_res_1068_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; uint8_t v___y_1080_; lean_object* v___y_1129_; lean_object* v___y_1133_; lean_object* v_pos_1134_; lean_object* v_fst_1135_; lean_object* v_snd_1136_; lean_object* v_res_1137_; lean_object* v___y_1160_; lean_object* v___y_1161_; uint8_t v___y_1162_; lean_object* v_pos_1181_; lean_object* v_fst_1182_; lean_object* v_snd_1183_; lean_object* v_res_1184_; lean_object* v_fst_1199_; lean_object* v_snd_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
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
lean_dec_ref(v___y_1004_);
v___x_1007_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_1008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___y_1005_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_unsigned_to_nat(0u);
v___x_1010_ = l_Lean_Json_Parser_natCore(v___x_1009_, v___y_1005_);
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
v___x_1016_ = l_Lean_JsonNumber_shiftr(v___y_1004_, v_res_1012_);
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
lean_dec_ref(v___y_1004_);
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
v___x_1039_ = lean_string_utf8_byte_size(v_fst_1037_);
v___x_1040_ = lean_nat_dec_eq(v_snd_1038_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
lean_dec_ref(v___y_1036_);
v___x_1041_ = lean_string_utf8_next_fast(v_fst_1037_, v_snd_1038_);
lean_dec(v_snd_1038_);
lean_inc(v_fst_1037_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v_fst_1037_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_nat_dec_eq(v___x_1041_, v___x_1039_);
if (v___x_1043_ == 0)
{
uint32_t v___x_1044_; uint32_t v___x_1045_; uint8_t v___x_1046_; 
v___x_1044_ = lean_string_utf8_get_fast(v_fst_1037_, v___x_1041_);
v___x_1045_ = 45;
v___x_1046_ = lean_uint32_dec_eq(v___x_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
uint32_t v___x_1047_; uint8_t v___x_1048_; 
v___x_1047_ = 43;
v___x_1048_ = lean_uint32_dec_eq(v___x_1044_, v___x_1047_);
if (v___x_1048_ == 0)
{
v___y_990_ = v___y_1035_;
v___y_991_ = v___x_1042_;
v_fst_992_ = v_fst_1037_;
v_snd_993_ = v___x_1041_;
goto v___jp_989_;
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_dec_ref_known(v___x_1042_, 2);
v___x_1049_ = lean_string_utf8_next_fast(v_fst_1037_, v___x_1041_);
lean_inc(v_fst_1037_);
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v_fst_1037_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___y_990_ = v___y_1035_;
v___y_991_ = v___x_1050_;
v_fst_992_ = v_fst_1037_;
v_snd_993_ = v___x_1049_;
goto v___jp_989_;
}
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
lean_dec_ref_known(v___x_1042_, 2);
v___x_1051_ = lean_string_utf8_next_fast(v_fst_1037_, v___x_1041_);
lean_inc(v_fst_1037_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v_fst_1037_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_nat_dec_eq(v___x_1051_, v___x_1039_);
if (v___x_1053_ == 0)
{
if (v___x_1046_ == 0)
{
lean_dec(v_fst_1037_);
lean_dec_ref(v___y_1035_);
v___y_1031_ = v___x_1052_;
goto v___jp_1030_;
}
else
{
uint32_t v___x_1054_; uint32_t v___x_1055_; uint8_t v___x_1056_; 
v___x_1054_ = lean_string_utf8_get_fast(v_fst_1037_, v___x_1051_);
lean_dec(v_fst_1037_);
v___x_1055_ = 48;
v___x_1056_ = lean_uint32_dec_le(v___x_1055_, v___x_1054_);
if (v___x_1056_ == 0)
{
v___y_1004_ = v___y_1035_;
v___y_1005_ = v___x_1052_;
v___y_1006_ = v___x_1056_;
goto v___jp_1003_;
}
else
{
uint32_t v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = 57;
v___x_1058_ = lean_uint32_dec_le(v___x_1054_, v___x_1057_);
v___y_1004_ = v___y_1035_;
v___y_1005_ = v___x_1052_;
v___y_1006_ = v___x_1058_;
goto v___jp_1003_;
}
}
}
else
{
lean_dec(v_fst_1037_);
lean_dec_ref(v___y_1035_);
v___y_1031_ = v___x_1052_;
goto v___jp_1030_;
}
}
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_dec(v_fst_1037_);
lean_dec_ref(v___y_1035_);
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
lean_dec(v_snd_1038_);
lean_dec(v_fst_1037_);
lean_dec_ref(v___y_1035_);
v___x_1061_ = lean_box(0);
v___x_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___y_1036_);
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
v___y_1035_ = v_res_1068_;
v___y_1036_ = v_pos_1065_;
v_fst_1037_ = v_fst_1066_;
v_snd_1038_ = v_snd_1067_;
goto v___jp_1034_;
}
}
else
{
lean_dec_ref(v___y_1064_);
v___y_1035_ = v_res_1068_;
v___y_1036_ = v_pos_1065_;
v_fst_1037_ = v_fst_1066_;
v_snd_1038_ = v_snd_1067_;
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
lean_dec(v___y_1077_);
v___x_1081_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___y_1079_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
return v___x_1082_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_1083_, v___x_1083_, v___y_1079_);
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
v___x_1101_ = lean_nat_to_int(v___y_1077_);
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
lean_dec(v___y_1077_);
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
lean_dec(v___y_1077_);
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
v___y_1077_ = v_res_1137_;
v___y_1078_ = v___y_1133_;
v___y_1079_ = v___x_1148_;
v___y_1080_ = v___x_1152_;
goto v___jp_1076_;
}
else
{
uint32_t v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = 57;
v___x_1154_ = lean_uint32_dec_le(v___x_1150_, v___x_1153_);
v___y_1077_ = v_res_1137_;
v___y_1078_ = v___y_1133_;
v___y_1079_ = v___x_1148_;
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
lean_ctor_set(v___x_1164_, 0, v___y_1161_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
return v___x_1164_;
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = l_Lean_Json_Parser_natCore(v___x_1165_, v___y_1161_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_pos_1167_; lean_object* v_res_1168_; lean_object* v_fst_1169_; lean_object* v_snd_1170_; 
v_pos_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_pos_1167_);
v_res_1168_ = lean_ctor_get(v___x_1166_, 1);
lean_inc(v_res_1168_);
lean_dec_ref_known(v___x_1166_, 2);
v_fst_1169_ = lean_ctor_get(v_pos_1167_, 0);
lean_inc(v_fst_1169_);
v_snd_1170_ = lean_ctor_get(v_pos_1167_, 1);
lean_inc(v_snd_1170_);
v___y_1133_ = v___y_1160_;
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
v___y_1160_ = v_res_1184_;
v___y_1161_ = v_pos_1181_;
v___y_1162_ = v___x_1191_;
goto v___jp_1159_;
}
else
{
uint32_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = 57;
v___x_1193_ = lean_uint32_dec_le(v___x_1187_, v___x_1192_);
v___y_1160_ = v_res_1184_;
v___y_1161_ = v_pos_1181_;
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
v___x_1228_ = lean_unsigned_to_nat(182u);
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
v___x_1234_ = lean_unsigned_to_nat(183u);
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
v___x_1242_ = lean_unsigned_to_nat(276u);
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
v___x_1248_ = lean_unsigned_to_nat(277u);
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
lean_object* v_size_1255_; lean_object* v_k_1256_; lean_object* v_v_1257_; lean_object* v_l_1258_; lean_object* v_r_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1615_; 
v_size_1255_ = lean_ctor_get(v_t_1254_, 0);
v_k_1256_ = lean_ctor_get(v_t_1254_, 1);
v_v_1257_ = lean_ctor_get(v_t_1254_, 2);
v_l_1258_ = lean_ctor_get(v_t_1254_, 3);
v_r_1259_ = lean_ctor_get(v_t_1254_, 4);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_t_1254_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1261_ = v_t_1254_;
v_isShared_1262_ = v_isSharedCheck_1615_;
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
v_isShared_1262_ = v_isSharedCheck_1615_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
uint8_t v___x_1263_; 
v___x_1263_ = lean_string_compare(v_k_1252_, v_k_1256_);
switch(v___x_1263_)
{
case 0:
{
lean_object* v___x_1264_; 
lean_dec(v_size_1255_);
v___x_1264_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_1252_, v_v_1253_, v_l_1258_);
if (lean_obj_tag(v_r_1259_) == 0)
{
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_size_1265_; lean_object* v_size_1266_; lean_object* v_k_1267_; lean_object* v_v_1268_; lean_object* v_l_1269_; lean_object* v_r_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v_size_1265_ = lean_ctor_get(v_r_1259_, 0);
v_size_1266_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_size_1266_);
v_k_1267_ = lean_ctor_get(v___x_1264_, 1);
lean_inc(v_k_1267_);
v_v_1268_ = lean_ctor_get(v___x_1264_, 2);
lean_inc(v_v_1268_);
v_l_1269_ = lean_ctor_get(v___x_1264_, 3);
lean_inc(v_l_1269_);
v_r_1270_ = lean_ctor_get(v___x_1264_, 4);
lean_inc(v_r_1270_);
v___x_1271_ = lean_unsigned_to_nat(3u);
v___x_1272_ = lean_nat_mul(v___x_1271_, v_size_1265_);
v___x_1273_ = lean_nat_dec_lt(v___x_1272_, v_size_1266_);
lean_dec(v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
lean_dec(v_r_1270_);
lean_dec(v_l_1269_);
lean_dec(v_v_1268_);
lean_dec(v_k_1267_);
v___x_1274_ = lean_unsigned_to_nat(1u);
v___x_1275_ = lean_nat_add(v___x_1274_, v_size_1266_);
lean_dec(v_size_1266_);
v___x_1276_ = lean_nat_add(v___x_1275_, v_size_1265_);
lean_dec(v___x_1275_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 3, v___x_1264_);
lean_ctor_set(v___x_1261_, 0, v___x_1276_);
v___x_1278_ = v___x_1261_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1279_, 3, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1279_, 4, v_r_1259_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
else
{
lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1351_; 
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; lean_object* v_unused_1353_; lean_object* v_unused_1354_; lean_object* v_unused_1355_; lean_object* v_unused_1356_; 
v_unused_1352_ = lean_ctor_get(v___x_1264_, 4);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v___x_1264_, 3);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v___x_1264_, 2);
lean_dec(v_unused_1354_);
v_unused_1355_ = lean_ctor_get(v___x_1264_, 1);
lean_dec(v_unused_1355_);
v_unused_1356_ = lean_ctor_get(v___x_1264_, 0);
lean_dec(v_unused_1356_);
v___x_1281_ = v___x_1264_;
v_isShared_1282_ = v_isSharedCheck_1351_;
goto v_resetjp_1280_;
}
else
{
lean_dec(v___x_1264_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1351_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
if (lean_obj_tag(v_l_1269_) == 0)
{
if (lean_obj_tag(v_r_1270_) == 0)
{
lean_object* v_size_1283_; lean_object* v_size_1284_; lean_object* v_k_1285_; lean_object* v_v_1286_; lean_object* v_l_1287_; lean_object* v_r_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_size_1283_ = lean_ctor_get(v_l_1269_, 0);
v_size_1284_ = lean_ctor_get(v_r_1270_, 0);
v_k_1285_ = lean_ctor_get(v_r_1270_, 1);
v_v_1286_ = lean_ctor_get(v_r_1270_, 2);
v_l_1287_ = lean_ctor_get(v_r_1270_, 3);
v_r_1288_ = lean_ctor_get(v_r_1270_, 4);
v___x_1289_ = lean_unsigned_to_nat(2u);
v___x_1290_ = lean_nat_mul(v___x_1289_, v_size_1283_);
v___x_1291_ = lean_nat_dec_lt(v_size_1284_, v___x_1290_);
lean_dec(v___x_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1321_; 
lean_inc(v_r_1288_);
lean_inc(v_l_1287_);
lean_inc(v_v_1286_);
lean_inc(v_k_1285_);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_r_1270_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; lean_object* v_unused_1323_; lean_object* v_unused_1324_; lean_object* v_unused_1325_; lean_object* v_unused_1326_; 
v_unused_1322_ = lean_ctor_get(v_r_1270_, 4);
lean_dec(v_unused_1322_);
v_unused_1323_ = lean_ctor_get(v_r_1270_, 3);
lean_dec(v_unused_1323_);
v_unused_1324_ = lean_ctor_get(v_r_1270_, 2);
lean_dec(v_unused_1324_);
v_unused_1325_ = lean_ctor_get(v_r_1270_, 1);
lean_dec(v_unused_1325_);
v_unused_1326_ = lean_ctor_get(v_r_1270_, 0);
lean_dec(v_unused_1326_);
v___x_1293_ = v_r_1270_;
v_isShared_1294_ = v_isSharedCheck_1321_;
goto v_resetjp_1292_;
}
else
{
lean_dec(v_r_1270_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1321_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___x_1309_; lean_object* v___y_1311_; 
v___x_1295_ = lean_unsigned_to_nat(1u);
v___x_1296_ = lean_nat_add(v___x_1295_, v_size_1266_);
lean_dec(v_size_1266_);
v___x_1297_ = lean_nat_add(v___x_1296_, v_size_1265_);
lean_dec(v___x_1296_);
v___x_1309_ = lean_nat_add(v___x_1295_, v_size_1283_);
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
v___jp_1298_:
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1302_ = lean_nat_add(v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec(v___y_1300_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v_r_1259_);
lean_ctor_set(v___x_1293_, 3, v_r_1288_);
lean_ctor_set(v___x_1293_, 2, v_v_1257_);
lean_ctor_set(v___x_1293_, 1, v_k_1256_);
lean_ctor_set(v___x_1293_, 0, v___x_1302_);
v___x_1304_ = v___x_1293_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1302_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1308_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1308_, 3, v_r_1288_);
lean_ctor_set(v_reuseFailAlloc_1308_, 4, v_r_1259_);
v___x_1304_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1306_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 4, v___x_1304_);
lean_ctor_set(v___x_1281_, 3, v___y_1299_);
lean_ctor_set(v___x_1281_, 2, v_v_1286_);
lean_ctor_set(v___x_1281_, 1, v_k_1285_);
lean_ctor_set(v___x_1281_, 0, v___x_1297_);
v___x_1306_ = v___x_1281_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_k_1285_);
lean_ctor_set(v_reuseFailAlloc_1307_, 2, v_v_1286_);
lean_ctor_set(v_reuseFailAlloc_1307_, 3, v___y_1299_);
lean_ctor_set(v_reuseFailAlloc_1307_, 4, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
v___jp_1310_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = lean_nat_add(v___x_1309_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec(v___x_1309_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_l_1287_);
lean_ctor_set(v___x_1261_, 3, v_l_1269_);
lean_ctor_set(v___x_1261_, 2, v_v_1268_);
lean_ctor_set(v___x_1261_, 1, v_k_1267_);
lean_ctor_set(v___x_1261_, 0, v___x_1312_);
v___x_1314_ = v___x_1261_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_k_1267_);
lean_ctor_set(v_reuseFailAlloc_1318_, 2, v_v_1268_);
lean_ctor_set(v_reuseFailAlloc_1318_, 3, v_l_1269_);
lean_ctor_set(v_reuseFailAlloc_1318_, 4, v_l_1287_);
v___x_1314_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_nat_add(v___x_1295_, v_size_1265_);
if (lean_obj_tag(v_r_1288_) == 0)
{
lean_object* v_size_1316_; 
v_size_1316_ = lean_ctor_get(v_r_1288_, 0);
lean_inc(v_size_1316_);
v___y_1299_ = v___x_1314_;
v___y_1300_ = v___x_1315_;
v___y_1301_ = v_size_1316_;
goto v___jp_1298_;
}
else
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_unsigned_to_nat(0u);
v___y_1299_ = v___x_1314_;
v___y_1300_ = v___x_1315_;
v___y_1301_ = v___x_1317_;
goto v___jp_1298_;
}
}
}
}
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
lean_del_object(v___x_1261_);
v___x_1327_ = lean_unsigned_to_nat(1u);
v___x_1328_ = lean_nat_add(v___x_1327_, v_size_1266_);
lean_dec(v_size_1266_);
v___x_1329_ = lean_nat_add(v___x_1328_, v_size_1265_);
lean_dec(v___x_1328_);
v___x_1330_ = lean_nat_add(v___x_1327_, v_size_1265_);
v___x_1331_ = lean_nat_add(v___x_1330_, v_size_1284_);
lean_dec(v___x_1330_);
lean_inc_ref(v_r_1259_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 4, v_r_1259_);
lean_ctor_set(v___x_1281_, 3, v_r_1270_);
lean_ctor_set(v___x_1281_, 2, v_v_1257_);
lean_ctor_set(v___x_1281_, 1, v_k_1256_);
lean_ctor_set(v___x_1281_, 0, v___x_1331_);
v___x_1333_ = v___x_1281_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1331_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_r_1270_);
lean_ctor_set(v_reuseFailAlloc_1346_, 4, v_r_1259_);
v___x_1333_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
v_isSharedCheck_1340_ = !lean_is_exclusive(v_r_1259_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; lean_object* v_unused_1342_; lean_object* v_unused_1343_; lean_object* v_unused_1344_; lean_object* v_unused_1345_; 
v_unused_1341_ = lean_ctor_get(v_r_1259_, 4);
lean_dec(v_unused_1341_);
v_unused_1342_ = lean_ctor_get(v_r_1259_, 3);
lean_dec(v_unused_1342_);
v_unused_1343_ = lean_ctor_get(v_r_1259_, 2);
lean_dec(v_unused_1343_);
v_unused_1344_ = lean_ctor_get(v_r_1259_, 1);
lean_dec(v_unused_1344_);
v_unused_1345_ = lean_ctor_get(v_r_1259_, 0);
lean_dec(v_unused_1345_);
v___x_1335_ = v_r_1259_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_dec(v_r_1259_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 4, v___x_1333_);
lean_ctor_set(v___x_1335_, 3, v_l_1269_);
lean_ctor_set(v___x_1335_, 2, v_v_1268_);
lean_ctor_set(v___x_1335_, 1, v_k_1267_);
lean_ctor_set(v___x_1335_, 0, v___x_1329_);
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_k_1267_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_v_1268_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_l_1269_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v___x_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_dec_ref_known(v_l_1269_, 5);
lean_del_object(v___x_1281_);
lean_dec(v_v_1268_);
lean_dec(v_k_1267_);
lean_dec(v_size_1266_);
lean_dec_ref_known(v_r_1259_, 5);
lean_del_object(v___x_1261_);
lean_dec(v_v_1257_);
lean_dec(v_k_1256_);
v___x_1347_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3);
v___x_1348_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1347_);
return v___x_1348_;
}
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_del_object(v___x_1281_);
lean_dec(v_r_1270_);
lean_dec(v_v_1268_);
lean_dec(v_k_1267_);
lean_dec(v_size_1266_);
lean_dec_ref_known(v_r_1259_, 5);
lean_del_object(v___x_1261_);
lean_dec(v_v_1257_);
lean_dec(v_k_1256_);
v___x_1349_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4);
v___x_1350_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1349_);
return v___x_1350_;
}
}
}
}
else
{
lean_object* v_size_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v_size_1357_ = lean_ctor_get(v_r_1259_, 0);
v___x_1358_ = lean_unsigned_to_nat(1u);
v___x_1359_ = lean_nat_add(v___x_1358_, v_size_1357_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 3, v___x_1264_);
lean_ctor_set(v___x_1261_, 0, v___x_1359_);
v___x_1361_ = v___x_1261_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1362_, 4, v_r_1259_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
else
{
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_l_1363_; 
v_l_1363_ = lean_ctor_get(v___x_1264_, 3);
lean_inc(v_l_1363_);
if (lean_obj_tag(v_l_1363_) == 0)
{
lean_object* v_r_1364_; 
v_r_1364_ = lean_ctor_get(v___x_1264_, 4);
lean_inc(v_r_1364_);
if (lean_obj_tag(v_r_1364_) == 0)
{
lean_object* v_size_1365_; lean_object* v_k_1366_; lean_object* v_v_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1381_; 
v_size_1365_ = lean_ctor_get(v___x_1264_, 0);
v_k_1366_ = lean_ctor_get(v___x_1264_, 1);
v_v_1367_ = lean_ctor_get(v___x_1264_, 2);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; lean_object* v_unused_1383_; 
v_unused_1382_ = lean_ctor_get(v___x_1264_, 4);
lean_dec(v_unused_1382_);
v_unused_1383_ = lean_ctor_get(v___x_1264_, 3);
lean_dec(v_unused_1383_);
v___x_1369_ = v___x_1264_;
v_isShared_1370_ = v_isSharedCheck_1381_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_v_1367_);
lean_inc(v_k_1366_);
lean_inc(v_size_1365_);
lean_dec(v___x_1264_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1381_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v_size_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v_size_1371_ = lean_ctor_get(v_r_1364_, 0);
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = lean_nat_add(v___x_1372_, v_size_1365_);
lean_dec(v_size_1365_);
v___x_1374_ = lean_nat_add(v___x_1372_, v_size_1371_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 4, v_r_1259_);
lean_ctor_set(v___x_1369_, 3, v_r_1364_);
lean_ctor_set(v___x_1369_, 2, v_v_1257_);
lean_ctor_set(v___x_1369_, 1, v_k_1256_);
lean_ctor_set(v___x_1369_, 0, v___x_1374_);
v___x_1376_ = v___x_1369_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1380_, 3, v_r_1364_);
lean_ctor_set(v_reuseFailAlloc_1380_, 4, v_r_1259_);
v___x_1376_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1378_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1376_);
lean_ctor_set(v___x_1261_, 3, v_l_1363_);
lean_ctor_set(v___x_1261_, 2, v_v_1367_);
lean_ctor_set(v___x_1261_, 1, v_k_1366_);
lean_ctor_set(v___x_1261_, 0, v___x_1373_);
v___x_1378_ = v___x_1261_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1379_, 3, v_l_1363_);
lean_ctor_set(v_reuseFailAlloc_1379_, 4, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
else
{
lean_object* v_k_1384_; lean_object* v_v_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1397_; 
v_k_1384_ = lean_ctor_get(v___x_1264_, 1);
v_v_1385_ = lean_ctor_get(v___x_1264_, 2);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; lean_object* v_unused_1399_; lean_object* v_unused_1400_; 
v_unused_1398_ = lean_ctor_get(v___x_1264_, 4);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v___x_1264_, 3);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v___x_1264_, 0);
lean_dec(v_unused_1400_);
v___x_1387_ = v___x_1264_;
v_isShared_1388_ = v_isSharedCheck_1397_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_v_1385_);
lean_inc(v_k_1384_);
lean_dec(v___x_1264_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1397_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1389_ = lean_unsigned_to_nat(3u);
v___x_1390_ = lean_unsigned_to_nat(1u);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 3, v_r_1364_);
lean_ctor_set(v___x_1387_, 2, v_v_1257_);
lean_ctor_set(v___x_1387_, 1, v_k_1256_);
lean_ctor_set(v___x_1387_, 0, v___x_1390_);
v___x_1392_ = v___x_1387_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1396_, 3, v_r_1364_);
lean_ctor_set(v_reuseFailAlloc_1396_, 4, v_r_1364_);
v___x_1392_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1394_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1392_);
lean_ctor_set(v___x_1261_, 3, v_l_1363_);
lean_ctor_set(v___x_1261_, 2, v_v_1385_);
lean_ctor_set(v___x_1261_, 1, v_k_1384_);
lean_ctor_set(v___x_1261_, 0, v___x_1389_);
v___x_1394_ = v___x_1261_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1395_, 3, v_l_1363_);
lean_ctor_set(v_reuseFailAlloc_1395_, 4, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
else
{
lean_object* v_r_1401_; 
v_r_1401_ = lean_ctor_get(v___x_1264_, 4);
lean_inc(v_r_1401_);
if (lean_obj_tag(v_r_1401_) == 0)
{
lean_object* v_k_1402_; lean_object* v_v_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1427_; 
v_k_1402_ = lean_ctor_get(v___x_1264_, 1);
v_v_1403_ = lean_ctor_get(v___x_1264_, 2);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; lean_object* v_unused_1429_; lean_object* v_unused_1430_; 
v_unused_1428_ = lean_ctor_get(v___x_1264_, 4);
lean_dec(v_unused_1428_);
v_unused_1429_ = lean_ctor_get(v___x_1264_, 3);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v___x_1264_, 0);
lean_dec(v_unused_1430_);
v___x_1405_ = v___x_1264_;
v_isShared_1406_ = v_isSharedCheck_1427_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_v_1403_);
lean_inc(v_k_1402_);
lean_dec(v___x_1264_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1427_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v_k_1407_; lean_object* v_v_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1423_; 
v_k_1407_ = lean_ctor_get(v_r_1401_, 1);
v_v_1408_ = lean_ctor_get(v_r_1401_, 2);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_r_1401_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; lean_object* v_unused_1425_; lean_object* v_unused_1426_; 
v_unused_1424_ = lean_ctor_get(v_r_1401_, 4);
lean_dec(v_unused_1424_);
v_unused_1425_ = lean_ctor_get(v_r_1401_, 3);
lean_dec(v_unused_1425_);
v_unused_1426_ = lean_ctor_get(v_r_1401_, 0);
lean_dec(v_unused_1426_);
v___x_1410_ = v_r_1401_;
v_isShared_1411_ = v_isSharedCheck_1423_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_v_1408_);
lean_inc(v_k_1407_);
lean_dec(v_r_1401_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1423_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1412_ = lean_unsigned_to_nat(3u);
v___x_1413_ = lean_unsigned_to_nat(1u);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 4, v_l_1363_);
lean_ctor_set(v___x_1410_, 3, v_l_1363_);
lean_ctor_set(v___x_1410_, 2, v_v_1403_);
lean_ctor_set(v___x_1410_, 1, v_k_1402_);
lean_ctor_set(v___x_1410_, 0, v___x_1413_);
v___x_1415_ = v___x_1410_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_k_1402_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_v_1403_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v_l_1363_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v_l_1363_);
v___x_1415_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1417_; 
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 4, v_l_1363_);
lean_ctor_set(v___x_1405_, 2, v_v_1257_);
lean_ctor_set(v___x_1405_, 1, v_k_1256_);
lean_ctor_set(v___x_1405_, 0, v___x_1413_);
v___x_1417_ = v___x_1405_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v_l_1363_);
lean_ctor_set(v_reuseFailAlloc_1421_, 4, v_l_1363_);
v___x_1417_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1419_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1417_);
lean_ctor_set(v___x_1261_, 3, v___x_1415_);
lean_ctor_set(v___x_1261_, 2, v_v_1408_);
lean_ctor_set(v___x_1261_, 1, v_k_1407_);
lean_ctor_set(v___x_1261_, 0, v___x_1412_);
v___x_1419_ = v___x_1261_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1431_ = lean_unsigned_to_nat(2u);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_r_1401_);
lean_ctor_set(v___x_1261_, 3, v___x_1264_);
lean_ctor_set(v___x_1261_, 0, v___x_1431_);
v___x_1433_ = v___x_1261_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v_r_1401_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1435_ = lean_unsigned_to_nat(1u);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1264_);
lean_ctor_set(v___x_1261_, 3, v___x_1264_);
lean_ctor_set(v___x_1261_, 0, v___x_1435_);
v___x_1437_ = v___x_1261_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1438_, 3, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1438_, 4, v___x_1264_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
case 1:
{
lean_object* v___x_1440_; 
lean_dec(v_v_1257_);
lean_dec(v_k_1256_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 2, v_v_1253_);
lean_ctor_set(v___x_1261_, 1, v_k_1252_);
v___x_1440_ = v___x_1261_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_size_1255_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_k_1252_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_v_1253_);
lean_ctor_set(v_reuseFailAlloc_1441_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1441_, 4, v_r_1259_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
default: 
{
lean_object* v___x_1442_; 
lean_dec(v_size_1255_);
v___x_1442_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_1252_, v_v_1253_, v_r_1259_);
if (lean_obj_tag(v_l_1258_) == 0)
{
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_size_1443_; lean_object* v_size_1444_; lean_object* v_k_1445_; lean_object* v_v_1446_; lean_object* v_l_1447_; lean_object* v_r_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v_size_1443_ = lean_ctor_get(v_l_1258_, 0);
v_size_1444_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_size_1444_);
v_k_1445_ = lean_ctor_get(v___x_1442_, 1);
lean_inc(v_k_1445_);
v_v_1446_ = lean_ctor_get(v___x_1442_, 2);
lean_inc(v_v_1446_);
v_l_1447_ = lean_ctor_get(v___x_1442_, 3);
lean_inc(v_l_1447_);
v_r_1448_ = lean_ctor_get(v___x_1442_, 4);
lean_inc(v_r_1448_);
v___x_1449_ = lean_unsigned_to_nat(3u);
v___x_1450_ = lean_nat_mul(v___x_1449_, v_size_1443_);
v___x_1451_ = lean_nat_dec_lt(v___x_1450_, v_size_1444_);
lean_dec(v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
lean_dec(v_r_1448_);
lean_dec(v_l_1447_);
lean_dec(v_v_1446_);
lean_dec(v_k_1445_);
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = lean_nat_add(v___x_1452_, v_size_1443_);
v___x_1454_ = lean_nat_add(v___x_1453_, v_size_1444_);
lean_dec(v_size_1444_);
lean_dec(v___x_1453_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1442_);
lean_ctor_set(v___x_1261_, 0, v___x_1454_);
v___x_1456_ = v___x_1261_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v___x_1442_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
else
{
lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1527_; 
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; lean_object* v_unused_1529_; lean_object* v_unused_1530_; lean_object* v_unused_1531_; lean_object* v_unused_1532_; 
v_unused_1528_ = lean_ctor_get(v___x_1442_, 4);
lean_dec(v_unused_1528_);
v_unused_1529_ = lean_ctor_get(v___x_1442_, 3);
lean_dec(v_unused_1529_);
v_unused_1530_ = lean_ctor_get(v___x_1442_, 2);
lean_dec(v_unused_1530_);
v_unused_1531_ = lean_ctor_get(v___x_1442_, 1);
lean_dec(v_unused_1531_);
v_unused_1532_ = lean_ctor_get(v___x_1442_, 0);
lean_dec(v_unused_1532_);
v___x_1459_ = v___x_1442_;
v_isShared_1460_ = v_isSharedCheck_1527_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v___x_1442_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1527_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
if (lean_obj_tag(v_l_1447_) == 0)
{
if (lean_obj_tag(v_r_1448_) == 0)
{
lean_object* v_size_1461_; lean_object* v_k_1462_; lean_object* v_v_1463_; lean_object* v_l_1464_; lean_object* v_r_1465_; lean_object* v_size_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v_size_1461_ = lean_ctor_get(v_l_1447_, 0);
v_k_1462_ = lean_ctor_get(v_l_1447_, 1);
v_v_1463_ = lean_ctor_get(v_l_1447_, 2);
v_l_1464_ = lean_ctor_get(v_l_1447_, 3);
v_r_1465_ = lean_ctor_get(v_l_1447_, 4);
v_size_1466_ = lean_ctor_get(v_r_1448_, 0);
v___x_1467_ = lean_unsigned_to_nat(2u);
v___x_1468_ = lean_nat_mul(v___x_1467_, v_size_1466_);
v___x_1469_ = lean_nat_dec_lt(v_size_1461_, v___x_1468_);
lean_dec(v___x_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1498_; 
lean_inc(v_r_1465_);
lean_inc(v_l_1464_);
lean_inc(v_v_1463_);
lean_inc(v_k_1462_);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_l_1447_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; lean_object* v_unused_1500_; lean_object* v_unused_1501_; lean_object* v_unused_1502_; lean_object* v_unused_1503_; 
v_unused_1499_ = lean_ctor_get(v_l_1447_, 4);
lean_dec(v_unused_1499_);
v_unused_1500_ = lean_ctor_get(v_l_1447_, 3);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v_l_1447_, 2);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_l_1447_, 1);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v_l_1447_, 0);
lean_dec(v_unused_1503_);
v___x_1471_ = v_l_1447_;
v_isShared_1472_ = v_isSharedCheck_1498_;
goto v_resetjp_1470_;
}
else
{
lean_dec(v_l_1447_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1498_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1488_; 
v___x_1473_ = lean_unsigned_to_nat(1u);
v___x_1474_ = lean_nat_add(v___x_1473_, v_size_1443_);
v___x_1475_ = lean_nat_add(v___x_1474_, v_size_1444_);
lean_dec(v_size_1444_);
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
v___jp_1476_:
{
lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1480_ = lean_nat_add(v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec(v___y_1478_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 4, v_r_1448_);
lean_ctor_set(v___x_1471_, 3, v_r_1465_);
lean_ctor_set(v___x_1471_, 2, v_v_1446_);
lean_ctor_set(v___x_1471_, 1, v_k_1445_);
lean_ctor_set(v___x_1471_, 0, v___x_1480_);
v___x_1482_ = v___x_1471_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_k_1445_);
lean_ctor_set(v_reuseFailAlloc_1486_, 2, v_v_1446_);
lean_ctor_set(v_reuseFailAlloc_1486_, 3, v_r_1465_);
lean_ctor_set(v_reuseFailAlloc_1486_, 4, v_r_1448_);
v___x_1482_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 4, v___x_1482_);
lean_ctor_set(v___x_1459_, 3, v___y_1477_);
lean_ctor_set(v___x_1459_, 2, v_v_1463_);
lean_ctor_set(v___x_1459_, 1, v_k_1462_);
lean_ctor_set(v___x_1459_, 0, v___x_1475_);
v___x_1484_ = v___x_1459_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_k_1462_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_v_1463_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v___y_1477_);
lean_ctor_set(v_reuseFailAlloc_1485_, 4, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
v___jp_1487_:
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1489_ = lean_nat_add(v___x_1474_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec(v___x_1474_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_l_1464_);
lean_ctor_set(v___x_1261_, 0, v___x_1489_);
v___x_1491_ = v___x_1261_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v_l_1464_);
v___x_1491_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_nat_add(v___x_1473_, v_size_1466_);
if (lean_obj_tag(v_r_1465_) == 0)
{
lean_object* v_size_1493_; 
v_size_1493_ = lean_ctor_get(v_r_1465_, 0);
lean_inc(v_size_1493_);
v___y_1477_ = v___x_1491_;
v___y_1478_ = v___x_1492_;
v___y_1479_ = v_size_1493_;
goto v___jp_1476_;
}
else
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_unsigned_to_nat(0u);
v___y_1477_ = v___x_1491_;
v___y_1478_ = v___x_1492_;
v___y_1479_ = v___x_1494_;
goto v___jp_1476_;
}
}
}
}
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
lean_del_object(v___x_1261_);
v___x_1504_ = lean_unsigned_to_nat(1u);
v___x_1505_ = lean_nat_add(v___x_1504_, v_size_1443_);
v___x_1506_ = lean_nat_add(v___x_1505_, v_size_1444_);
lean_dec(v_size_1444_);
v___x_1507_ = lean_nat_add(v___x_1505_, v_size_1461_);
lean_dec(v___x_1505_);
lean_inc_ref(v_l_1258_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 4, v_l_1447_);
lean_ctor_set(v___x_1459_, 3, v_l_1258_);
lean_ctor_set(v___x_1459_, 2, v_v_1257_);
lean_ctor_set(v___x_1459_, 1, v_k_1256_);
lean_ctor_set(v___x_1459_, 0, v___x_1507_);
v___x_1509_ = v___x_1459_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1522_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1522_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1522_, 4, v_l_1447_);
v___x_1509_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
v_isSharedCheck_1516_ = !lean_is_exclusive(v_l_1258_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; lean_object* v_unused_1518_; lean_object* v_unused_1519_; lean_object* v_unused_1520_; lean_object* v_unused_1521_; 
v_unused_1517_ = lean_ctor_get(v_l_1258_, 4);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v_l_1258_, 3);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_l_1258_, 2);
lean_dec(v_unused_1519_);
v_unused_1520_ = lean_ctor_get(v_l_1258_, 1);
lean_dec(v_unused_1520_);
v_unused_1521_ = lean_ctor_get(v_l_1258_, 0);
lean_dec(v_unused_1521_);
v___x_1511_ = v_l_1258_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_dec(v_l_1258_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 4, v_r_1448_);
lean_ctor_set(v___x_1511_, 3, v___x_1509_);
lean_ctor_set(v___x_1511_, 2, v_v_1446_);
lean_ctor_set(v___x_1511_, 1, v_k_1445_);
lean_ctor_set(v___x_1511_, 0, v___x_1506_);
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_k_1445_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_v_1446_);
lean_ctor_set(v_reuseFailAlloc_1515_, 3, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1515_, 4, v_r_1448_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
else
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_dec_ref_known(v_l_1447_, 5);
lean_del_object(v___x_1459_);
lean_dec(v_v_1446_);
lean_dec(v_k_1445_);
lean_dec(v_size_1444_);
lean_dec_ref_known(v_l_1258_, 5);
lean_del_object(v___x_1261_);
lean_dec(v_v_1257_);
lean_dec(v_k_1256_);
v___x_1523_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7);
v___x_1524_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1523_);
return v___x_1524_;
}
}
else
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_del_object(v___x_1459_);
lean_dec(v_r_1448_);
lean_dec(v_v_1446_);
lean_dec(v_k_1445_);
lean_dec(v_size_1444_);
lean_dec_ref_known(v_l_1258_, 5);
lean_del_object(v___x_1261_);
lean_dec(v_v_1257_);
lean_dec(v_k_1256_);
v___x_1525_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8);
v___x_1526_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1525_);
return v___x_1526_;
}
}
}
}
else
{
lean_object* v_size_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1537_; 
v_size_1533_ = lean_ctor_get(v_l_1258_, 0);
v___x_1534_ = lean_unsigned_to_nat(1u);
v___x_1535_ = lean_nat_add(v___x_1534_, v_size_1533_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1442_);
lean_ctor_set(v___x_1261_, 0, v___x_1535_);
v___x_1537_ = v___x_1261_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1538_, 4, v___x_1442_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
else
{
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_l_1539_; 
v_l_1539_ = lean_ctor_get(v___x_1442_, 3);
lean_inc(v_l_1539_);
if (lean_obj_tag(v_l_1539_) == 0)
{
lean_object* v_r_1540_; 
v_r_1540_ = lean_ctor_get(v___x_1442_, 4);
lean_inc(v_r_1540_);
if (lean_obj_tag(v_r_1540_) == 0)
{
lean_object* v_size_1541_; lean_object* v_k_1542_; lean_object* v_v_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1557_; 
v_size_1541_ = lean_ctor_get(v___x_1442_, 0);
v_k_1542_ = lean_ctor_get(v___x_1442_, 1);
v_v_1543_ = lean_ctor_get(v___x_1442_, 2);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; lean_object* v_unused_1559_; 
v_unused_1558_ = lean_ctor_get(v___x_1442_, 4);
lean_dec(v_unused_1558_);
v_unused_1559_ = lean_ctor_get(v___x_1442_, 3);
lean_dec(v_unused_1559_);
v___x_1545_ = v___x_1442_;
v_isShared_1546_ = v_isSharedCheck_1557_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_v_1543_);
lean_inc(v_k_1542_);
lean_inc(v_size_1541_);
lean_dec(v___x_1442_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1557_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v_size_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
v_size_1547_ = lean_ctor_get(v_l_1539_, 0);
v___x_1548_ = lean_unsigned_to_nat(1u);
v___x_1549_ = lean_nat_add(v___x_1548_, v_size_1541_);
lean_dec(v_size_1541_);
v___x_1550_ = lean_nat_add(v___x_1548_, v_size_1547_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 4, v_l_1539_);
lean_ctor_set(v___x_1545_, 3, v_l_1258_);
lean_ctor_set(v___x_1545_, 2, v_v_1257_);
lean_ctor_set(v___x_1545_, 1, v_k_1256_);
lean_ctor_set(v___x_1545_, 0, v___x_1550_);
v___x_1552_ = v___x_1545_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1556_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1556_, 4, v_l_1539_);
v___x_1552_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1554_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_r_1540_);
lean_ctor_set(v___x_1261_, 3, v___x_1552_);
lean_ctor_set(v___x_1261_, 2, v_v_1543_);
lean_ctor_set(v___x_1261_, 1, v_k_1542_);
lean_ctor_set(v___x_1261_, 0, v___x_1549_);
v___x_1554_ = v___x_1261_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_k_1542_);
lean_ctor_set(v_reuseFailAlloc_1555_, 2, v_v_1543_);
lean_ctor_set(v_reuseFailAlloc_1555_, 3, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1555_, 4, v_r_1540_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
else
{
lean_object* v_k_1560_; lean_object* v_v_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1585_; 
v_k_1560_ = lean_ctor_get(v___x_1442_, 1);
v_v_1561_ = lean_ctor_get(v___x_1442_, 2);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; lean_object* v_unused_1587_; lean_object* v_unused_1588_; 
v_unused_1586_ = lean_ctor_get(v___x_1442_, 4);
lean_dec(v_unused_1586_);
v_unused_1587_ = lean_ctor_get(v___x_1442_, 3);
lean_dec(v_unused_1587_);
v_unused_1588_ = lean_ctor_get(v___x_1442_, 0);
lean_dec(v_unused_1588_);
v___x_1563_ = v___x_1442_;
v_isShared_1564_ = v_isSharedCheck_1585_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_v_1561_);
lean_inc(v_k_1560_);
lean_dec(v___x_1442_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1585_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v_k_1565_; lean_object* v_v_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1581_; 
v_k_1565_ = lean_ctor_get(v_l_1539_, 1);
v_v_1566_ = lean_ctor_get(v_l_1539_, 2);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_l_1539_);
if (v_isSharedCheck_1581_ == 0)
{
lean_object* v_unused_1582_; lean_object* v_unused_1583_; lean_object* v_unused_1584_; 
v_unused_1582_ = lean_ctor_get(v_l_1539_, 4);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v_l_1539_, 3);
lean_dec(v_unused_1583_);
v_unused_1584_ = lean_ctor_get(v_l_1539_, 0);
lean_dec(v_unused_1584_);
v___x_1568_ = v_l_1539_;
v_isShared_1569_ = v_isSharedCheck_1581_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_v_1566_);
lean_inc(v_k_1565_);
lean_dec(v_l_1539_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1581_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1570_ = lean_unsigned_to_nat(3u);
v___x_1571_ = lean_unsigned_to_nat(1u);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 4, v_r_1540_);
lean_ctor_set(v___x_1568_, 3, v_r_1540_);
lean_ctor_set(v___x_1568_, 2, v_v_1257_);
lean_ctor_set(v___x_1568_, 1, v_k_1256_);
lean_ctor_set(v___x_1568_, 0, v___x_1571_);
v___x_1573_ = v___x_1568_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1580_, 3, v_r_1540_);
lean_ctor_set(v_reuseFailAlloc_1580_, 4, v_r_1540_);
v___x_1573_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1575_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 3, v_r_1540_);
lean_ctor_set(v___x_1563_, 0, v___x_1571_);
v___x_1575_ = v___x_1563_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_k_1560_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_v_1561_);
lean_ctor_set(v_reuseFailAlloc_1579_, 3, v_r_1540_);
lean_ctor_set(v_reuseFailAlloc_1579_, 4, v_r_1540_);
v___x_1575_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1577_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1575_);
lean_ctor_set(v___x_1261_, 3, v___x_1573_);
lean_ctor_set(v___x_1261_, 2, v_v_1566_);
lean_ctor_set(v___x_1261_, 1, v_k_1565_);
lean_ctor_set(v___x_1261_, 0, v___x_1570_);
v___x_1577_ = v___x_1261_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_k_1565_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_v_1566_);
lean_ctor_set(v_reuseFailAlloc_1578_, 3, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1578_, 4, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1589_; 
v_r_1589_ = lean_ctor_get(v___x_1442_, 4);
lean_inc(v_r_1589_);
if (lean_obj_tag(v_r_1589_) == 0)
{
lean_object* v_k_1590_; lean_object* v_v_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1603_; 
v_k_1590_ = lean_ctor_get(v___x_1442_, 1);
v_v_1591_ = lean_ctor_get(v___x_1442_, 2);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1603_ == 0)
{
lean_object* v_unused_1604_; lean_object* v_unused_1605_; lean_object* v_unused_1606_; 
v_unused_1604_ = lean_ctor_get(v___x_1442_, 4);
lean_dec(v_unused_1604_);
v_unused_1605_ = lean_ctor_get(v___x_1442_, 3);
lean_dec(v_unused_1605_);
v_unused_1606_ = lean_ctor_get(v___x_1442_, 0);
lean_dec(v_unused_1606_);
v___x_1593_ = v___x_1442_;
v_isShared_1594_ = v_isSharedCheck_1603_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_v_1591_);
lean_inc(v_k_1590_);
lean_dec(v___x_1442_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1603_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1595_ = lean_unsigned_to_nat(3u);
v___x_1596_ = lean_unsigned_to_nat(1u);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 4, v_l_1539_);
lean_ctor_set(v___x_1593_, 2, v_v_1257_);
lean_ctor_set(v___x_1593_, 1, v_k_1256_);
lean_ctor_set(v___x_1593_, 0, v___x_1596_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1602_, 3, v_l_1539_);
lean_ctor_set(v_reuseFailAlloc_1602_, 4, v_l_1539_);
v___x_1598_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1600_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_r_1589_);
lean_ctor_set(v___x_1261_, 3, v___x_1598_);
lean_ctor_set(v___x_1261_, 2, v_v_1591_);
lean_ctor_set(v___x_1261_, 1, v_k_1590_);
lean_ctor_set(v___x_1261_, 0, v___x_1595_);
v___x_1600_ = v___x_1261_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_k_1590_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_v_1591_);
lean_ctor_set(v_reuseFailAlloc_1601_, 3, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_r_1589_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1607_ = lean_unsigned_to_nat(2u);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1442_);
lean_ctor_set(v___x_1261_, 3, v_r_1589_);
lean_ctor_set(v___x_1261_, 0, v___x_1607_);
v___x_1609_ = v___x_1261_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v_r_1589_);
lean_ctor_set(v_reuseFailAlloc_1610_, 4, v___x_1442_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1611_ = lean_unsigned_to_nat(1u);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1442_);
lean_ctor_set(v___x_1261_, 3, v___x_1442_);
lean_ctor_set(v___x_1261_, 0, v___x_1611_);
v___x_1613_ = v___x_1261_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1614_, 4, v___x_1442_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_unsigned_to_nat(1u);
v___x_1617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
lean_ctor_set(v___x_1617_, 1, v_k_1252_);
lean_ctor_set(v___x_1617_, 2, v_v_1253_);
lean_ctor_set(v___x_1617_, 3, v_t_1254_);
lean_ctor_set(v___x_1617_, 4, v_t_1254_);
return v___x_1617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore(lean_object* v_kvs_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v_fst_1638_; lean_object* v_snd_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v_fst_1638_ = lean_ctor_get(v_a_1637_, 0);
v_snd_1639_ = lean_ctor_get(v_a_1637_, 1);
v___x_1640_ = lean_string_utf8_byte_size(v_fst_1638_);
v___x_1641_ = lean_nat_dec_eq(v_snd_1639_, v___x_1640_);
if (v___x_1641_ == 0)
{
uint32_t v___x_1642_; uint32_t v___x_1643_; uint8_t v___x_1644_; 
v___x_1642_ = lean_string_utf8_get_fast(v_fst_1638_, v_snd_1639_);
v___x_1643_ = 34;
v___x_1644_ = lean_uint32_dec_eq(v___x_1642_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec(v_kvs_1636_);
v___x_1645_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__1));
v___x_1646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1646_, 0, v_a_1637_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
return v___x_1646_;
}
else
{
lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1750_; 
lean_inc(v_snd_1639_);
lean_inc(v_fst_1638_);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_a_1637_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; lean_object* v_unused_1752_; 
v_unused_1751_ = lean_ctor_get(v_a_1637_, 1);
lean_dec(v_unused_1751_);
v_unused_1752_ = lean_ctor_get(v_a_1637_, 0);
lean_dec(v_unused_1752_);
v___x_1648_ = v_a_1637_;
v_isShared_1649_ = v_isSharedCheck_1750_;
goto v_resetjp_1647_;
}
else
{
lean_dec(v_a_1637_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1750_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = lean_string_utf8_next_fast(v_fst_1638_, v_snd_1639_);
lean_dec(v_snd_1639_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 1, v___x_1650_);
v___x_1652_ = v___x_1648_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_fst_1638_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_1654_ = l_Lean_Json_Parser_strCore(v___x_1653_, v___x_1652_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_pos_1655_; lean_object* v_res_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1739_; 
v_pos_1655_ = lean_ctor_get(v___x_1654_, 0);
v_res_1656_ = lean_ctor_get(v___x_1654_, 1);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1658_ = v___x_1654_;
v_isShared_1659_ = v_isSharedCheck_1739_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_res_1656_);
lean_inc(v_pos_1655_);
lean_dec(v___x_1654_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1739_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v_fst_1660_; lean_object* v_snd_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1738_; 
v_fst_1660_ = lean_ctor_get(v_pos_1655_, 0);
v_snd_1661_ = lean_ctor_get(v_pos_1655_, 1);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_pos_1655_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1663_ = v_pos_1655_;
v_isShared_1664_ = v_isSharedCheck_1738_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_snd_1661_);
lean_inc(v_fst_1660_);
lean_dec(v_pos_1655_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1738_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1665_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1660_, v_snd_1661_);
lean_inc(v___x_1665_);
lean_inc(v_fst_1660_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 1, v___x_1665_);
v___x_1667_ = v___x_1663_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_fst_1660_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1673_; uint8_t v___x_1674_; 
v___x_1673_ = lean_string_utf8_byte_size(v_fst_1660_);
v___x_1674_ = lean_nat_dec_eq(v___x_1665_, v___x_1673_);
if (v___x_1674_ == 0)
{
if (v___x_1644_ == 0)
{
lean_dec(v___x_1665_);
lean_dec(v_fst_1660_);
lean_dec(v_res_1656_);
lean_dec(v_kvs_1636_);
goto v___jp_1668_;
}
else
{
uint32_t v___x_1675_; uint32_t v___x_1676_; uint8_t v___x_1677_; 
lean_del_object(v___x_1658_);
v___x_1675_ = lean_string_utf8_get_fast(v_fst_1660_, v___x_1665_);
v___x_1676_ = 58;
v___x_1677_ = lean_uint32_dec_eq(v___x_1675_, v___x_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec(v___x_1665_);
lean_dec(v_fst_1660_);
lean_dec(v_res_1656_);
lean_dec(v_kvs_1636_);
v___x_1678_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__3));
v___x_1679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1667_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
return v___x_1679_;
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_dec_ref(v___x_1667_);
v___x_1680_ = lean_string_utf8_next_fast(v_fst_1660_, v___x_1665_);
lean_dec(v___x_1665_);
v___x_1681_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1660_, v___x_1680_);
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v_fst_1660_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = l_Lean_Json_Parser_anyCore(v___x_1682_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_pos_1684_; lean_object* v_res_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1727_; 
v_pos_1684_ = lean_ctor_get(v___x_1683_, 0);
v_res_1685_ = lean_ctor_get(v___x_1683_, 1);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1687_ = v___x_1683_;
v_isShared_1688_ = v_isSharedCheck_1727_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_res_1685_);
lean_inc(v_pos_1684_);
lean_dec(v___x_1683_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1727_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v_fst_1694_; lean_object* v_snd_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v_fst_1694_ = lean_ctor_get(v_pos_1684_, 0);
v_snd_1695_ = lean_ctor_get(v_pos_1684_, 1);
v___x_1696_ = lean_string_utf8_byte_size(v_fst_1694_);
v___x_1697_ = lean_nat_dec_eq(v_snd_1695_, v___x_1696_);
if (v___x_1697_ == 0)
{
if (v___x_1677_ == 0)
{
lean_dec(v_res_1685_);
lean_dec(v_res_1656_);
lean_dec(v_kvs_1636_);
goto v___jp_1689_;
}
else
{
lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1724_; 
lean_inc(v_snd_1695_);
lean_inc(v_fst_1694_);
lean_del_object(v___x_1687_);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_pos_1684_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; lean_object* v_unused_1726_; 
v_unused_1725_ = lean_ctor_get(v_pos_1684_, 1);
lean_dec(v_unused_1725_);
v_unused_1726_ = lean_ctor_get(v_pos_1684_, 0);
lean_dec(v_unused_1726_);
v___x_1699_ = v_pos_1684_;
v_isShared_1700_ = v_isSharedCheck_1724_;
goto v_resetjp_1698_;
}
else
{
lean_dec(v_pos_1684_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1724_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
uint32_t v___x_1701_; lean_object* v___x_1702_; uint32_t v___x_1703_; uint8_t v___x_1704_; 
v___x_1701_ = lean_string_utf8_get_fast(v_fst_1694_, v_snd_1695_);
v___x_1702_ = lean_string_utf8_next_fast(v_fst_1694_, v_snd_1695_);
lean_dec(v_snd_1695_);
v___x_1703_ = 125;
v___x_1704_ = lean_uint32_dec_eq(v___x_1701_, v___x_1703_);
if (v___x_1704_ == 0)
{
uint32_t v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = 44;
v___x_1706_ = lean_uint32_dec_eq(v___x_1701_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1708_; 
lean_dec(v_res_1685_);
lean_dec(v_res_1656_);
lean_dec(v_kvs_1636_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 1, v___x_1702_);
v___x_1708_ = v___x_1699_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_fst_1694_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v___x_1702_);
v___x_1708_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__5));
v___x_1710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
return v___x_1710_;
}
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1712_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1694_, v___x_1702_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 1, v___x_1712_);
v___x_1714_ = v___x_1699_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_fst_1694_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_res_1656_, v_res_1685_, v_kvs_1636_);
v_kvs_1636_ = v___x_1715_;
v_a_1637_ = v___x_1714_;
goto _start;
}
}
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1718_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1694_, v___x_1702_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 1, v___x_1718_);
v___x_1720_ = v___x_1699_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_fst_1694_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_res_1656_, v_res_1685_, v_kvs_1636_);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1720_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
return v___x_1722_;
}
}
}
}
}
else
{
lean_dec(v_res_1685_);
lean_dec(v_res_1656_);
lean_dec(v_kvs_1636_);
goto v___jp_1689_;
}
v___jp_1689_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = lean_box(0);
if (v_isShared_1688_ == 0)
{
lean_ctor_set_tag(v___x_1687_, 1);
lean_ctor_set(v___x_1687_, 1, v___x_1690_);
v___x_1692_ = v___x_1687_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_pos_1684_);
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
else
{
lean_object* v_pos_1728_; lean_object* v_err_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec(v_res_1656_);
lean_dec(v_kvs_1636_);
v_pos_1728_ = lean_ctor_get(v___x_1683_, 0);
v_err_1729_ = lean_ctor_get(v___x_1683_, 1);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1683_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_err_1729_);
lean_inc(v_pos_1728_);
lean_dec(v___x_1683_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_pos_1728_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_err_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1665_);
lean_dec(v_fst_1660_);
lean_dec(v_res_1656_);
lean_dec(v_kvs_1636_);
goto v___jp_1668_;
}
v___jp_1668_:
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1669_ = lean_box(0);
if (v_isShared_1659_ == 0)
{
lean_ctor_set_tag(v___x_1658_, 1);
lean_ctor_set(v___x_1658_, 1, v___x_1669_);
lean_ctor_set(v___x_1658_, 0, v___x_1667_);
v___x_1671_ = v___x_1658_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1740_; lean_object* v_err_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v_kvs_1636_);
v_pos_1740_ = lean_ctor_get(v___x_1654_, 0);
v_err_1741_ = lean_ctor_get(v___x_1654_, 1);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1654_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_err_1741_);
lean_inc(v_pos_1740_);
lean_dec(v___x_1654_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_pos_1740_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_err_1741_);
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
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec(v_kvs_1636_);
v___x_1753_ = lean_box(0);
v___x_1754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1754_, 0, v_a_1637_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
return v___x_1754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object* v_a_1761_){
_start:
{
uint8_t v___y_1794_; lean_object* v_fst_1797_; lean_object* v_snd_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v_fst_1797_ = lean_ctor_get(v_a_1761_, 0);
v_snd_1798_ = lean_ctor_get(v_a_1761_, 1);
v___x_1799_ = lean_string_utf8_byte_size(v_fst_1797_);
v___x_1800_ = lean_nat_dec_eq(v_snd_1798_, v___x_1799_);
if (v___x_1800_ == 0)
{
uint32_t v___x_1801_; uint32_t v___x_1802_; uint8_t v___x_1803_; 
v___x_1801_ = lean_string_utf8_get_fast(v_fst_1797_, v_snd_1798_);
v___x_1802_ = 91;
v___x_1803_ = lean_uint32_dec_eq(v___x_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
uint32_t v___x_1804_; uint8_t v___x_1805_; 
v___x_1804_ = 123;
v___x_1805_ = lean_uint32_dec_eq(v___x_1801_, v___x_1804_);
if (v___x_1805_ == 0)
{
uint32_t v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = 34;
v___x_1807_ = lean_uint32_dec_eq(v___x_1801_, v___x_1806_);
if (v___x_1807_ == 0)
{
uint32_t v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = 102;
v___x_1809_ = lean_uint32_dec_eq(v___x_1801_, v___x_1808_);
if (v___x_1809_ == 0)
{
uint32_t v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = 116;
v___x_1811_ = lean_uint32_dec_eq(v___x_1801_, v___x_1810_);
if (v___x_1811_ == 0)
{
uint32_t v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = 110;
v___x_1813_ = lean_uint32_dec_eq(v___x_1801_, v___x_1812_);
if (v___x_1813_ == 0)
{
uint32_t v___x_1814_; uint8_t v___x_1815_; 
v___x_1814_ = 45;
v___x_1815_ = lean_uint32_dec_eq(v___x_1801_, v___x_1814_);
if (v___x_1815_ == 0)
{
uint32_t v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = 48;
v___x_1817_ = lean_uint32_dec_le(v___x_1816_, v___x_1801_);
if (v___x_1817_ == 0)
{
v___y_1794_ = v___x_1817_;
goto v___jp_1793_;
}
else
{
uint32_t v___x_1818_; uint8_t v___x_1819_; 
v___x_1818_ = 57;
v___x_1819_ = lean_uint32_dec_le(v___x_1801_, v___x_1818_);
v___y_1794_ = v___x_1819_;
goto v___jp_1793_;
}
}
else
{
goto v___jp_1762_;
}
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__2));
v___x_1821_ = l_Std_Internal_Parsec_String_pstring(v___x_1820_, v_a_1761_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_pos_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1840_; 
v_pos_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1840_ == 0)
{
lean_object* v_unused_1841_; 
v_unused_1841_ = lean_ctor_get(v___x_1821_, 1);
lean_dec(v_unused_1841_);
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1840_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_pos_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1840_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v_fst_1826_; lean_object* v_snd_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1839_; 
v_fst_1826_ = lean_ctor_get(v_pos_1822_, 0);
v_snd_1827_ = lean_ctor_get(v_pos_1822_, 1);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_pos_1822_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1829_ = v_pos_1822_;
v_isShared_1830_ = v_isSharedCheck_1839_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_snd_1827_);
lean_inc(v_fst_1826_);
lean_dec(v_pos_1822_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1839_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1831_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1826_, v_snd_1827_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 1, v___x_1831_);
v___x_1833_ = v___x_1829_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_fst_1826_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1834_ = lean_box(0);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 1, v___x_1834_);
lean_ctor_set(v___x_1824_, 0, v___x_1833_);
v___x_1836_ = v___x_1824_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
else
{
lean_object* v_pos_1842_; lean_object* v_err_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
v_pos_1842_ = lean_ctor_get(v___x_1821_, 0);
v_err_1843_ = lean_ctor_get(v___x_1821_, 1);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1821_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_err_1843_);
lean_inc(v_pos_1842_);
lean_dec(v___x_1821_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_pos_1842_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_err_1843_);
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
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__3));
v___x_1852_ = l_Std_Internal_Parsec_String_pstring(v___x_1851_, v_a_1761_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_pos_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1871_; 
v_pos_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1871_ == 0)
{
lean_object* v_unused_1872_; 
v_unused_1872_ = lean_ctor_get(v___x_1852_, 1);
lean_dec(v_unused_1872_);
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1871_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_pos_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1871_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v_fst_1857_; lean_object* v_snd_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1870_; 
v_fst_1857_ = lean_ctor_get(v_pos_1853_, 0);
v_snd_1858_ = lean_ctor_get(v_pos_1853_, 1);
v_isSharedCheck_1870_ = !lean_is_exclusive(v_pos_1853_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1860_ = v_pos_1853_;
v_isShared_1861_ = v_isSharedCheck_1870_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_snd_1858_);
lean_inc(v_fst_1857_);
lean_dec(v_pos_1853_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1870_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1862_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1857_, v_snd_1858_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 1, v___x_1862_);
v___x_1864_ = v___x_1860_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_fst_1857_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1865_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1865_, 0, v___x_1811_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 1, v___x_1865_);
lean_ctor_set(v___x_1855_, 0, v___x_1864_);
v___x_1867_ = v___x_1855_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1864_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
else
{
lean_object* v_pos_1873_; lean_object* v_err_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
v_pos_1873_ = lean_ctor_get(v___x_1852_, 0);
v_err_1874_ = lean_ctor_get(v___x_1852_, 1);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1852_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_err_1874_);
lean_inc(v_pos_1873_);
lean_dec(v___x_1852_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_pos_1873_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_err_1874_);
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
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__4));
v___x_1883_ = l_Std_Internal_Parsec_String_pstring(v___x_1882_, v_a_1761_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_pos_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1902_; 
v_pos_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v___x_1883_, 1);
lean_dec(v_unused_1903_);
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1902_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_pos_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1902_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v_fst_1888_; lean_object* v_snd_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1901_; 
v_fst_1888_ = lean_ctor_get(v_pos_1884_, 0);
v_snd_1889_ = lean_ctor_get(v_pos_1884_, 1);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_pos_1884_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1891_ = v_pos_1884_;
v_isShared_1892_ = v_isSharedCheck_1901_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_snd_1889_);
lean_inc(v_fst_1888_);
lean_dec(v_pos_1884_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1901_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1888_, v_snd_1889_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 1, v___x_1893_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_fst_1888_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1896_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1896_, 0, v___x_1807_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 1, v___x_1896_);
lean_ctor_set(v___x_1886_, 0, v___x_1895_);
v___x_1898_ = v___x_1886_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1895_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
else
{
lean_object* v_pos_1904_; lean_object* v_err_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
v_pos_1904_ = lean_ctor_get(v___x_1883_, 0);
v_err_1905_ = lean_ctor_get(v___x_1883_, 1);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1883_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_err_1905_);
lean_inc(v_pos_1904_);
lean_dec(v___x_1883_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_pos_1904_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_err_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
else
{
lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1951_; 
lean_inc(v_snd_1798_);
lean_inc(v_fst_1797_);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_a_1761_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; lean_object* v_unused_1953_; 
v_unused_1952_ = lean_ctor_get(v_a_1761_, 1);
lean_dec(v_unused_1952_);
v_unused_1953_ = lean_ctor_get(v_a_1761_, 0);
lean_dec(v_unused_1953_);
v___x_1914_ = v_a_1761_;
v_isShared_1915_ = v_isSharedCheck_1951_;
goto v_resetjp_1913_;
}
else
{
lean_dec(v_a_1761_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1951_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___x_1916_ = lean_string_utf8_next_fast(v_fst_1797_, v_snd_1798_);
lean_dec(v_snd_1798_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 1, v___x_1916_);
v___x_1918_ = v___x_1914_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_fst_1797_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_1920_ = l_Lean_Json_Parser_strCore(v___x_1919_, v___x_1918_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_pos_1921_; lean_object* v_res_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1940_; 
v_pos_1921_ = lean_ctor_get(v___x_1920_, 0);
v_res_1922_ = lean_ctor_get(v___x_1920_, 1);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1924_ = v___x_1920_;
v_isShared_1925_ = v_isSharedCheck_1940_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_res_1922_);
lean_inc(v_pos_1921_);
lean_dec(v___x_1920_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1940_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v_fst_1926_; lean_object* v_snd_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1939_; 
v_fst_1926_ = lean_ctor_get(v_pos_1921_, 0);
v_snd_1927_ = lean_ctor_get(v_pos_1921_, 1);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_pos_1921_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1929_ = v_pos_1921_;
v_isShared_1930_ = v_isSharedCheck_1939_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_snd_1927_);
lean_inc(v_fst_1926_);
lean_dec(v_pos_1921_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1939_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1931_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1926_, v_snd_1927_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 1, v___x_1931_);
v___x_1933_ = v___x_1929_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_fst_1926_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1934_, 0, v_res_1922_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 1, v___x_1934_);
lean_ctor_set(v___x_1924_, 0, v___x_1933_);
v___x_1936_ = v___x_1924_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
else
{
lean_object* v_pos_1941_; lean_object* v_err_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_pos_1941_ = lean_ctor_get(v___x_1920_, 0);
v_err_1942_ = lean_ctor_get(v___x_1920_, 1);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1920_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_err_1942_);
lean_inc(v_pos_1941_);
lean_dec(v___x_1920_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_pos_1941_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_err_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1996_; 
lean_inc(v_snd_1798_);
lean_inc(v_fst_1797_);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_a_1761_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; lean_object* v_unused_1998_; 
v_unused_1997_ = lean_ctor_get(v_a_1761_, 1);
lean_dec(v_unused_1997_);
v_unused_1998_ = lean_ctor_get(v_a_1761_, 0);
lean_dec(v_unused_1998_);
v___x_1955_ = v_a_1761_;
v_isShared_1956_ = v_isSharedCheck_1996_;
goto v_resetjp_1954_;
}
else
{
lean_dec(v_a_1761_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1996_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1957_ = lean_string_utf8_next_fast(v_fst_1797_, v_snd_1798_);
lean_dec(v_snd_1798_);
v___x_1958_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1797_, v___x_1957_);
lean_inc(v___x_1958_);
lean_inc(v_fst_1797_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 1, v___x_1958_);
v___x_1960_ = v___x_1955_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_fst_1797_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
uint8_t v___y_1962_; uint8_t v___x_1994_; 
v___x_1994_ = lean_nat_dec_eq(v___x_1958_, v___x_1799_);
if (v___x_1994_ == 0)
{
v___y_1962_ = v___x_1805_;
goto v___jp_1961_;
}
else
{
v___y_1962_ = v___x_1803_;
goto v___jp_1961_;
}
v___jp_1961_:
{
if (v___y_1962_ == 0)
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_dec(v___x_1958_);
lean_dec(v_fst_1797_);
v___x_1963_ = lean_box(0);
v___x_1964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1960_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
return v___x_1964_;
}
else
{
uint32_t v___x_1965_; uint32_t v___x_1966_; uint8_t v___x_1967_; 
v___x_1965_ = lean_string_utf8_get_fast(v_fst_1797_, v___x_1958_);
v___x_1966_ = 125;
v___x_1967_ = lean_uint32_dec_eq(v___x_1965_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_dec(v___x_1958_);
lean_dec(v_fst_1797_);
v___x_1968_ = lean_box(1);
v___x_1969_ = l_Lean_Json_Parser_objectCore(v___x_1968_, v___x_1960_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_pos_1970_; lean_object* v_res_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1979_; 
v_pos_1970_ = lean_ctor_get(v___x_1969_, 0);
v_res_1971_ = lean_ctor_get(v___x_1969_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1973_ = v___x_1969_;
v_isShared_1974_ = v_isSharedCheck_1979_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_res_1971_);
lean_inc(v_pos_1970_);
lean_dec(v___x_1969_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1979_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1975_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1975_, 0, v_res_1971_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 1, v___x_1975_);
v___x_1977_ = v___x_1973_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_pos_1970_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
else
{
lean_object* v_pos_1980_; lean_object* v_err_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
v_pos_1980_ = lean_ctor_get(v___x_1969_, 0);
v_err_1981_ = lean_ctor_get(v___x_1969_, 1);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1969_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_err_1981_);
lean_inc(v_pos_1980_);
lean_dec(v___x_1969_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_pos_1980_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_err_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
lean_dec_ref(v___x_1960_);
v___x_1989_ = lean_string_utf8_next_fast(v_fst_1797_, v___x_1958_);
lean_dec(v___x_1958_);
v___x_1990_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1797_, v___x_1989_);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v_fst_1797_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__5));
v___x_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
return v___x_1993_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2041_; 
lean_inc(v_snd_1798_);
lean_inc(v_fst_1797_);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_a_1761_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; lean_object* v_unused_2043_; 
v_unused_2042_ = lean_ctor_get(v_a_1761_, 1);
lean_dec(v_unused_2042_);
v_unused_2043_ = lean_ctor_get(v_a_1761_, 0);
lean_dec(v_unused_2043_);
v___x_2000_ = v_a_1761_;
v_isShared_2001_ = v_isSharedCheck_2041_;
goto v_resetjp_1999_;
}
else
{
lean_dec(v_a_1761_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2041_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2002_ = lean_string_utf8_next_fast(v_fst_1797_, v_snd_1798_);
lean_dec(v_snd_1798_);
v___x_2003_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1797_, v___x_2002_);
lean_inc(v___x_2003_);
lean_inc(v_fst_1797_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v___x_2003_);
v___x_2005_ = v___x_2000_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_fst_1797_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
uint8_t v___x_2009_; 
v___x_2009_ = lean_nat_dec_eq(v___x_2003_, v___x_1799_);
if (v___x_2009_ == 0)
{
if (v___x_1803_ == 0)
{
lean_dec(v___x_2003_);
lean_dec(v_fst_1797_);
goto v___jp_2006_;
}
else
{
uint32_t v___x_2010_; uint32_t v___x_2011_; uint8_t v___x_2012_; 
v___x_2010_ = lean_string_utf8_get_fast(v_fst_1797_, v___x_2003_);
v___x_2011_ = 93;
v___x_2012_ = lean_uint32_dec_eq(v___x_2010_, v___x_2011_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_dec(v___x_2003_);
lean_dec(v_fst_1797_);
v___x_2013_ = lean_unsigned_to_nat(4u);
v___x_2014_ = lean_mk_empty_array_with_capacity(v___x_2013_);
v___x_2015_ = l_Lean_Json_Parser_arrayCore(v___x_2014_, v___x_2005_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_pos_2016_; lean_object* v_res_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2025_; 
v_pos_2016_ = lean_ctor_get(v___x_2015_, 0);
v_res_2017_ = lean_ctor_get(v___x_2015_, 1);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2019_ = v___x_2015_;
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_res_2017_);
lean_inc(v_pos_2016_);
lean_dec(v___x_2015_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_res_2017_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 1, v___x_2021_);
v___x_2023_ = v___x_2019_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_pos_2016_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
else
{
lean_object* v_pos_2026_; lean_object* v_err_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
v_pos_2026_ = lean_ctor_get(v___x_2015_, 0);
v_err_2027_ = lean_ctor_get(v___x_2015_, 1);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2015_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_err_2027_);
lean_inc(v_pos_2026_);
lean_dec(v___x_2015_);
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
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec_ref(v___x_2005_);
v___x_2035_ = lean_string_utf8_next_fast(v_fst_1797_, v___x_2003_);
lean_dec(v___x_2003_);
v___x_2036_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1797_, v___x_2035_);
v___x_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2037_, 0, v_fst_1797_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v___x_2038_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__7));
v___x_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2037_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
return v___x_2039_;
}
}
}
else
{
lean_dec(v___x_2003_);
lean_dec(v_fst_1797_);
goto v___jp_2006_;
}
v___jp_2006_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = lean_box(0);
v___x_2008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2005_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
return v___x_2008_;
}
}
}
}
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = lean_box(0);
v___x_2045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2045_, 0, v_a_1761_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
return v___x_2045_;
}
v___jp_1762_:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_Json_Parser_num(v_a_1761_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_pos_1764_; lean_object* v_res_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1783_; 
v_pos_1764_ = lean_ctor_get(v___x_1763_, 0);
v_res_1765_ = lean_ctor_get(v___x_1763_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1767_ = v___x_1763_;
v_isShared_1768_ = v_isSharedCheck_1783_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_res_1765_);
lean_inc(v_pos_1764_);
lean_dec(v___x_1763_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1783_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v_fst_1769_; lean_object* v_snd_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1782_; 
v_fst_1769_ = lean_ctor_get(v_pos_1764_, 0);
v_snd_1770_ = lean_ctor_get(v_pos_1764_, 1);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_pos_1764_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1772_ = v_pos_1764_;
v_isShared_1773_ = v_isSharedCheck_1782_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_snd_1770_);
lean_inc(v_fst_1769_);
lean_dec(v_pos_1764_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1782_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1774_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1769_, v_snd_1770_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 1, v___x_1774_);
v___x_1776_ = v___x_1772_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_fst_1769_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1777_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_res_1765_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 1, v___x_1777_);
lean_ctor_set(v___x_1767_, 0, v___x_1776_);
v___x_1779_ = v___x_1767_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
else
{
lean_object* v_pos_1784_; lean_object* v_err_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
v_pos_1784_ = lean_ctor_get(v___x_1763_, 0);
v_err_1785_ = lean_ctor_get(v___x_1763_, 1);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1763_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_err_1785_);
lean_inc(v_pos_1784_);
lean_dec(v___x_1763_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_pos_1784_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_err_1785_);
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
v___jp_1793_:
{
if (v___y_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__1));
v___x_1796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1796_, 0, v_a_1761_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
return v___x_1796_;
}
else
{
goto v___jp_1762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore(lean_object* v_acc_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_Json_Parser_anyCore(v_a_2047_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_pos_2049_; lean_object* v_res_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2094_; 
v_pos_2049_ = lean_ctor_get(v___x_2048_, 0);
v_res_2050_ = lean_ctor_get(v___x_2048_, 1);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2052_ = v___x_2048_;
v_isShared_2053_ = v_isSharedCheck_2094_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_res_2050_);
lean_inc(v_pos_2049_);
lean_dec(v___x_2048_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2094_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v_fst_2054_; lean_object* v_snd_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
v_fst_2054_ = lean_ctor_get(v_pos_2049_, 0);
v_snd_2055_ = lean_ctor_get(v_pos_2049_, 1);
v___x_2056_ = lean_string_utf8_byte_size(v_fst_2054_);
v___x_2057_ = lean_nat_dec_eq(v_snd_2055_, v___x_2056_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2087_; 
lean_inc(v_snd_2055_);
lean_inc(v_fst_2054_);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_pos_2049_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; lean_object* v_unused_2089_; 
v_unused_2088_ = lean_ctor_get(v_pos_2049_, 1);
lean_dec(v_unused_2088_);
v_unused_2089_ = lean_ctor_get(v_pos_2049_, 0);
lean_dec(v_unused_2089_);
v___x_2059_ = v_pos_2049_;
v_isShared_2060_ = v_isSharedCheck_2087_;
goto v_resetjp_2058_;
}
else
{
lean_dec(v_pos_2049_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2087_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; uint32_t v___x_2062_; lean_object* v___x_2063_; uint32_t v___x_2064_; uint8_t v___x_2065_; 
v___x_2061_ = lean_array_push(v_acc_2046_, v_res_2050_);
v___x_2062_ = lean_string_utf8_get_fast(v_fst_2054_, v_snd_2055_);
v___x_2063_ = lean_string_utf8_next_fast(v_fst_2054_, v_snd_2055_);
lean_dec(v_snd_2055_);
v___x_2064_ = 93;
v___x_2065_ = lean_uint32_dec_eq(v___x_2062_, v___x_2064_);
if (v___x_2065_ == 0)
{
uint32_t v___x_2066_; uint8_t v___x_2067_; 
v___x_2066_ = 44;
v___x_2067_ = lean_uint32_dec_eq(v___x_2062_, v___x_2066_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2069_; 
lean_dec_ref(v___x_2061_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v___x_2063_);
v___x_2069_ = v___x_2059_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_fst_2054_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v___x_2063_);
v___x_2069_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2070_ = ((lean_object*)(l_Lean_Json_Parser_arrayCore___closed__1));
if (v_isShared_2053_ == 0)
{
lean_ctor_set_tag(v___x_2052_, 1);
lean_ctor_set(v___x_2052_, 1, v___x_2070_);
lean_ctor_set(v___x_2052_, 0, v___x_2069_);
v___x_2072_ = v___x_2052_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
lean_del_object(v___x_2052_);
v___x_2075_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2054_, v___x_2063_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v___x_2075_);
v___x_2077_ = v___x_2059_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_fst_2054_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
v_acc_2046_ = v___x_2061_;
v_a_2047_ = v___x_2077_;
goto _start;
}
}
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2054_, v___x_2063_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v___x_2080_);
v___x_2082_ = v___x_2059_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_fst_2054_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2084_; 
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 1, v___x_2061_);
lean_ctor_set(v___x_2052_, 0, v___x_2082_);
v___x_2084_ = v___x_2052_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___x_2061_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
lean_dec(v_res_2050_);
lean_dec_ref(v_acc_2046_);
v___x_2090_ = lean_box(0);
if (v_isShared_2053_ == 0)
{
lean_ctor_set_tag(v___x_2052_, 1);
lean_ctor_set(v___x_2052_, 1, v___x_2090_);
v___x_2092_ = v___x_2052_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_pos_2049_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
else
{
lean_object* v_pos_2095_; lean_object* v_err_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref(v_acc_2046_);
v_pos_2095_ = lean_ctor_get(v___x_2048_, 0);
v_err_2096_ = lean_ctor_get(v___x_2048_, 1);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2048_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_err_2096_);
lean_inc(v_pos_2095_);
lean_dec(v___x_2048_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_pos_2095_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_err_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2(lean_object* v_00_u03b2_2104_, lean_object* v_msg_2105_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v_msg_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2(lean_object* v_00_u03b2_2107_, lean_object* v_k_2108_, lean_object* v_v_2109_, lean_object* v_t_2110_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_2108_, v_v_2109_, v_t_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_any(lean_object* v_a_2115_){
_start:
{
lean_object* v_fst_2116_; lean_object* v_snd_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2141_; 
v_fst_2116_ = lean_ctor_get(v_a_2115_, 0);
v_snd_2117_ = lean_ctor_get(v_a_2115_, 1);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_a_2115_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2119_ = v_a_2115_;
v_isShared_2120_ = v_isSharedCheck_2141_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_snd_2117_);
lean_inc(v_fst_2116_);
lean_dec(v_a_2115_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2141_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; lean_object* v___x_2123_; 
v___x_2121_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2116_, v_snd_2117_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 1, v___x_2121_);
v___x_2123_ = v___x_2119_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_fst_2116_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Lean_Json_Parser_anyCore(v___x_2123_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_pos_2125_; lean_object* v_fst_2126_; lean_object* v_snd_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v_pos_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_pos_2125_);
v_fst_2126_ = lean_ctor_get(v_pos_2125_, 0);
v_snd_2127_ = lean_ctor_get(v_pos_2125_, 1);
v___x_2128_ = lean_string_utf8_byte_size(v_fst_2126_);
v___x_2129_ = lean_nat_dec_eq(v_snd_2127_, v___x_2128_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2137_; 
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; lean_object* v_unused_2139_; 
v_unused_2138_ = lean_ctor_get(v___x_2124_, 1);
lean_dec(v_unused_2138_);
v_unused_2139_ = lean_ctor_get(v___x_2124_, 0);
lean_dec(v_unused_2139_);
v___x_2131_ = v___x_2124_;
v_isShared_2132_ = v_isSharedCheck_2137_;
goto v_resetjp_2130_;
}
else
{
lean_dec(v___x_2124_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2137_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2133_ = ((lean_object*)(l_Lean_Json_Parser_any___closed__1));
if (v_isShared_2132_ == 0)
{
lean_ctor_set_tag(v___x_2131_, 1);
lean_ctor_set(v___x_2131_, 1, v___x_2133_);
v___x_2135_ = v___x_2131_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_pos_2125_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
else
{
lean_dec(v_pos_2125_);
return v___x_2124_;
}
}
else
{
return v___x_2124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parse(lean_object* v_s_2142_){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
v___x_2144_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_2143_, v_s_2142_);
return v___x_2144_;
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
