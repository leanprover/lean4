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
lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_185_; 
lean_inc(v_snd_65_);
lean_inc(v_fst_64_);
v_isSharedCheck_185_ = !lean_is_exclusive(v_a_59_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; lean_object* v_unused_187_; 
v_unused_186_ = lean_ctor_get(v_a_59_, 1);
lean_dec(v_unused_186_);
v_unused_187_ = lean_ctor_get(v_a_59_, 0);
lean_dec(v_unused_187_);
v___x_69_ = v_a_59_;
v_isShared_70_ = v_isSharedCheck_185_;
goto v_resetjp_68_;
}
else
{
lean_dec(v_a_59_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_185_;
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
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_fst_64_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_72_);
v_it_x27_74_ = v_reuseFailAlloc_184_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
uint32_t v___x_78_; uint8_t v___x_79_; 
v___x_78_ = 92;
v___x_79_ = lean_uint32_dec_eq(v_c_71_, v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v_fst_64_);
v___x_80_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_81_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_81_, 0, v_it_x27_74_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
return v___x_81_;
}
else
{
uint8_t v_decide_82_; 
v_decide_82_ = lean_nat_dec_eq(v___x_72_, v___x_66_);
if (v_decide_82_ == 0)
{
if (v___x_79_ == 0)
{
lean_dec(v_fst_64_);
goto v___jp_75_;
}
else
{
uint32_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint32_t v___x_89_; uint8_t v___x_90_; 
lean_dec_ref(v_it_x27_74_);
v___x_83_ = lean_string_utf8_get_fast(v_fst_64_, v___x_72_);
v___x_84_ = lean_string_utf8_next_fast(v_fst_64_, v___x_72_);
lean_inc(v_fst_64_);
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v_fst_64_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_89_ = 117;
v___x_90_ = lean_uint32_dec_eq(v___x_83_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_fst_64_);
v___x_91_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_92_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_85_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
return v___x_92_;
}
else
{
uint8_t v_decide_93_; 
v_decide_93_ = lean_nat_dec_eq(v___x_84_, v___x_66_);
if (v_decide_93_ == 0)
{
if (v___x_90_ == 0)
{
lean_dec(v_fst_64_);
goto v___jp_86_;
}
else
{
uint32_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint32_t v___x_178_; uint8_t v___x_179_; 
lean_dec_ref_known(v___x_85_, 2);
v___x_94_ = lean_string_utf8_get_fast(v_fst_64_, v___x_84_);
v___x_95_ = lean_string_utf8_next_fast(v_fst_64_, v___x_84_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v_fst_64_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_178_ = 100;
v___x_179_ = lean_uint32_dec_eq(v___x_94_, v___x_178_);
if (v___x_179_ == 0)
{
uint32_t v___x_180_; uint8_t v___x_181_; 
v___x_180_ = 68;
v___x_181_ = lean_uint32_dec_eq(v___x_94_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_96_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
return v___x_183_;
}
else
{
goto v___jp_97_;
}
}
else
{
goto v___jp_97_;
}
v___jp_97_:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Json_Parser_hexChar(v___x_96_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_pos_99_; lean_object* v_res_100_; lean_object* v___x_101_; 
v_pos_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_pos_99_);
v_res_100_ = lean_ctor_get(v___x_98_, 1);
lean_inc(v_res_100_);
lean_dec_ref_known(v___x_98_, 2);
v___x_101_ = l_Lean_Json_Parser_hexChar(v_pos_99_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_pos_102_; lean_object* v_res_103_; lean_object* v___x_104_; 
v_pos_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_pos_102_);
v_res_103_ = lean_ctor_get(v___x_101_, 1);
lean_inc(v_res_103_);
lean_dec_ref_known(v___x_101_, 2);
v___x_104_ = l_Lean_Json_Parser_hexChar(v_pos_102_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_pos_105_; lean_object* v_res_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_150_; 
v_pos_105_ = lean_ctor_get(v___x_104_, 0);
v_res_106_ = lean_ctor_get(v___x_104_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_150_ == 0)
{
v___x_108_ = v___x_104_;
v_isShared_109_ = v_isSharedCheck_150_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_res_106_);
lean_inc(v_pos_105_);
lean_dec(v___x_104_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_150_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
uint16_t v___x_110_; uint16_t v___x_111_; uint16_t v___x_112_; uint16_t v___x_113_; uint16_t v___x_114_; uint16_t v___x_115_; uint16_t v___x_116_; uint16_t v___x_117_; uint16_t v___x_118_; uint16_t v___x_119_; uint8_t v___x_120_; 
v___x_110_ = 8;
v___x_111_ = lean_unbox(v_res_100_);
lean_dec(v_res_100_);
v___x_112_ = lean_uint16_shift_left(v___x_111_, v___x_110_);
v___x_113_ = 4;
v___x_114_ = lean_unbox(v_res_103_);
lean_dec(v_res_103_);
v___x_115_ = lean_uint16_shift_left(v___x_114_, v___x_113_);
v___x_116_ = lean_uint16_lor(v___x_112_, v___x_115_);
v___x_117_ = lean_unbox(v_res_106_);
lean_dec(v_res_106_);
v___x_118_ = lean_uint16_lor(v___x_116_, v___x_117_);
v___x_119_ = 3072;
v___x_120_ = lean_uint16_dec_lt(v___x_118_, v___x_119_);
if (v___x_120_ == 0)
{
uint32_t v___x_121_; uint32_t v___x_122_; uint32_t v___x_123_; uint32_t v___x_124_; uint32_t v___x_125_; uint32_t v___x_126_; uint32_t v___x_127_; uint32_t v___x_128_; uint32_t v___x_129_; uint32_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_121_ = lean_uint16_to_uint32(v_low_58_);
v___x_122_ = 1023;
v___x_123_ = lean_uint32_land(v___x_121_, v___x_122_);
v___x_124_ = 10;
v___x_125_ = lean_uint32_shift_left(v___x_123_, v___x_124_);
v___x_126_ = lean_uint16_to_uint32(v___x_118_);
v___x_127_ = lean_uint32_land(v___x_126_, v___x_122_);
v___x_128_ = lean_uint32_lor(v___x_125_, v___x_127_);
v___x_129_ = 65536;
v___x_130_ = lean_uint32_add(v___x_128_, v___x_129_);
v___x_131_ = lean_uint32_to_nat(v___x_130_);
v___x_132_ = lean_unsigned_to_nat(55296u);
v___x_133_ = lean_nat_dec_lt(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(57343u);
v___x_135_ = lean_nat_dec_lt(v___x_134_, v___x_131_);
if (v___x_135_ == 0)
{
lean_dec(v___x_131_);
lean_del_object(v___x_108_);
v___y_61_ = v_pos_105_;
goto v___jp_60_;
}
else
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(1114112u);
v___x_137_ = lean_nat_dec_lt(v___x_131_, v___x_136_);
lean_dec(v___x_131_);
if (v___x_137_ == 0)
{
lean_del_object(v___x_108_);
v___y_61_ = v_pos_105_;
goto v___jp_60_;
}
else
{
lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_138_ = lean_box_uint32(v___x_130_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v___x_138_);
v___x_140_ = v___x_108_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_pos_105_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v___x_138_);
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
lean_object* v___x_142_; lean_object* v___x_144_; 
lean_dec(v___x_131_);
v___x_142_ = lean_box_uint32(v___x_130_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v___x_142_);
v___x_144_ = v___x_108_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_pos_105_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
else
{
lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_146_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
if (v_isShared_109_ == 0)
{
lean_ctor_set_tag(v___x_108_, 1);
lean_ctor_set(v___x_108_, 1, v___x_146_);
v___x_148_ = v___x_108_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_pos_105_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v___x_146_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
else
{
lean_object* v_pos_151_; lean_object* v_err_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
lean_dec(v_res_103_);
lean_dec(v_res_100_);
v_pos_151_ = lean_ctor_get(v___x_104_, 0);
v_err_152_ = lean_ctor_get(v___x_104_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_104_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_err_152_);
lean_inc(v_pos_151_);
lean_dec(v___x_104_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_pos_151_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_err_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
else
{
lean_object* v_pos_160_; lean_object* v_err_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
lean_dec(v_res_100_);
v_pos_160_ = lean_ctor_get(v___x_101_, 0);
v_err_161_ = lean_ctor_get(v___x_101_, 1);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_168_ == 0)
{
v___x_163_ = v___x_101_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_err_161_);
lean_inc(v_pos_160_);
lean_dec(v___x_101_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_pos_160_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_err_161_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
else
{
lean_object* v_pos_169_; lean_object* v_err_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_pos_169_ = lean_ctor_get(v___x_98_, 0);
v_err_170_ = lean_ctor_get(v___x_98_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_98_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_err_170_);
lean_inc(v_pos_169_);
lean_dec(v___x_98_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_pos_169_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_err_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_64_);
goto v___jp_86_;
}
}
v___jp_86_:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_box(0);
v___x_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_85_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
return v___x_88_;
}
}
}
else
{
lean_dec(v_fst_64_);
goto v___jp_75_;
}
}
v___jp_75_:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_box(0);
v___x_77_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_77_, 0, v_it_x27_74_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
return v___x_77_;
}
}
}
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_box(0);
v___x_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_189_, 0, v_a_59_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
return v___x_189_;
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
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair___boxed(lean_object* v_low_190_, lean_object* v_a_191_){
_start:
{
uint16_t v_low_boxed_192_; lean_object* v_res_193_; 
v_low_boxed_192_ = lean_unbox(v_low_190_);
v_res_193_ = l_Lean_Json_Parser_finishSurrogatePair(v_low_boxed_192_, v_a_191_);
return v_res_193_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_197_; lean_object* v___x_198_; 
v___x_197_ = 65533;
v___x_198_ = lean_box_uint32(v___x_197_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_199_; lean_object* v___x_200_; 
v___x_199_ = 9;
v___x_200_ = lean_box_uint32(v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_201_; lean_object* v___x_202_; 
v___x_201_ = 13;
v___x_202_ = lean_box_uint32(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_203_; lean_object* v___x_204_; 
v___x_203_ = 10;
v___x_204_ = lean_box_uint32(v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_205_; lean_object* v___x_206_; 
v___x_205_ = 12;
v___x_206_ = lean_box_uint32(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_207_; lean_object* v___x_208_; 
v___x_207_ = 8;
v___x_208_ = lean_box_uint32(v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__7(void){
_start:
{
uint32_t v___x_209_; lean_object* v___x_210_; 
v___x_209_ = 47;
v___x_210_ = lean_box_uint32(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__8(void){
_start:
{
uint32_t v___x_211_; lean_object* v___x_212_; 
v___x_211_ = 34;
v___x_212_ = lean_box_uint32(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__9(void){
_start:
{
uint32_t v___x_213_; lean_object* v___x_214_; 
v___x_213_ = 92;
v___x_214_ = lean_box_uint32(v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar(lean_object* v_a_215_){
_start:
{
lean_object* v_fst_216_; lean_object* v_snd_217_; lean_object* v___x_218_; uint8_t v_decide_219_; 
v_fst_216_ = lean_ctor_get(v_a_215_, 0);
v_snd_217_ = lean_ctor_get(v_a_215_, 1);
v___x_218_ = lean_string_utf8_byte_size(v_fst_216_);
v_decide_219_ = lean_nat_dec_eq(v_snd_217_, v___x_218_);
if (v_decide_219_ == 0)
{
lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_374_; 
lean_inc(v_snd_217_);
lean_inc(v_fst_216_);
v_isSharedCheck_374_ = !lean_is_exclusive(v_a_215_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; lean_object* v_unused_376_; 
v_unused_375_ = lean_ctor_get(v_a_215_, 1);
lean_dec(v_unused_375_);
v_unused_376_ = lean_ctor_get(v_a_215_, 0);
lean_dec(v_unused_376_);
v___x_221_ = v_a_215_;
v_isShared_222_ = v_isSharedCheck_374_;
goto v_resetjp_220_;
}
else
{
lean_dec(v_a_215_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_374_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
uint32_t v_c_223_; lean_object* v___x_224_; lean_object* v_it_x27_226_; 
v_c_223_ = lean_string_utf8_get_fast(v_fst_216_, v_snd_217_);
v___x_224_ = lean_string_utf8_next_fast(v_fst_216_, v_snd_217_);
lean_dec(v_snd_217_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 1, v___x_224_);
v_it_x27_226_ = v___x_221_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_fst_216_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_224_);
v_it_x27_226_ = v_reuseFailAlloc_373_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
uint32_t v___x_227_; uint8_t v___x_228_; 
v___x_227_ = 92;
v___x_228_ = lean_uint32_dec_eq(v_c_223_, v___x_227_);
if (v___x_228_ == 0)
{
uint32_t v___x_229_; uint8_t v___x_230_; 
v___x_229_ = 34;
v___x_230_ = lean_uint32_dec_eq(v_c_223_, v___x_229_);
if (v___x_230_ == 0)
{
uint32_t v___x_231_; uint8_t v___x_232_; 
v___x_231_ = 47;
v___x_232_ = lean_uint32_dec_eq(v_c_223_, v___x_231_);
if (v___x_232_ == 0)
{
uint32_t v___x_233_; uint8_t v___x_234_; 
v___x_233_ = 98;
v___x_234_ = lean_uint32_dec_eq(v_c_223_, v___x_233_);
if (v___x_234_ == 0)
{
uint32_t v___x_235_; uint8_t v___x_236_; 
v___x_235_ = 102;
v___x_236_ = lean_uint32_dec_eq(v_c_223_, v___x_235_);
if (v___x_236_ == 0)
{
uint32_t v___x_237_; uint8_t v___x_238_; 
v___x_237_ = 110;
v___x_238_ = lean_uint32_dec_eq(v_c_223_, v___x_237_);
if (v___x_238_ == 0)
{
uint32_t v___x_239_; uint8_t v___x_240_; 
v___x_239_ = 114;
v___x_240_ = lean_uint32_dec_eq(v_c_223_, v___x_239_);
if (v___x_240_ == 0)
{
uint32_t v___x_241_; uint8_t v___x_242_; 
v___x_241_ = 116;
v___x_242_ = lean_uint32_dec_eq(v_c_223_, v___x_241_);
if (v___x_242_ == 0)
{
uint32_t v___x_243_; uint8_t v___x_244_; 
v___x_243_ = 117;
v___x_244_ = lean_uint32_dec_eq(v_c_223_, v___x_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_Json_Parser_escapedChar___closed__1));
v___x_246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_246_, 0, v_it_x27_226_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
return v___x_246_;
}
else
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Json_Parser_hexChar(v_it_x27_226_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_pos_248_; lean_object* v_res_249_; lean_object* v___x_250_; 
v_pos_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_pos_248_);
v_res_249_ = lean_ctor_get(v___x_247_, 1);
lean_inc(v_res_249_);
lean_dec_ref_known(v___x_247_, 2);
v___x_250_ = l_Lean_Json_Parser_hexChar(v_pos_248_);
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
lean_object* v_pos_254_; lean_object* v_res_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_329_; 
v_pos_254_ = lean_ctor_get(v___x_253_, 0);
v_res_255_ = lean_ctor_get(v___x_253_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_329_ == 0)
{
v___x_257_ = v___x_253_;
v_isShared_258_ = v_isSharedCheck_329_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_res_255_);
lean_inc(v_pos_254_);
lean_dec(v___x_253_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_329_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_Json_Parser_hexChar(v_pos_254_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_pos_260_; lean_object* v_res_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_319_; 
v_pos_260_ = lean_ctor_get(v___x_259_, 0);
v_res_261_ = lean_ctor_get(v___x_259_, 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_319_ == 0)
{
v___x_263_ = v___x_259_;
v_isShared_264_ = v_isSharedCheck_319_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_res_261_);
lean_inc(v_pos_260_);
lean_dec(v___x_259_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_319_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___y_266_; lean_object* v_pos_267_; uint16_t v___x_275_; uint16_t v___x_276_; uint16_t v___x_277_; uint16_t v___x_278_; uint16_t v___x_279_; uint16_t v___x_280_; uint16_t v___x_281_; uint16_t v___x_282_; uint16_t v___x_283_; uint16_t v___x_284_; uint16_t v___x_285_; uint16_t v___x_286_; uint16_t v___x_287_; uint16_t v___x_288_; uint8_t v___x_289_; 
v___x_275_ = 12;
v___x_276_ = lean_unbox(v_res_249_);
lean_dec(v_res_249_);
v___x_277_ = lean_uint16_shift_left(v___x_276_, v___x_275_);
v___x_278_ = 8;
v___x_279_ = lean_unbox(v_res_252_);
lean_dec(v_res_252_);
v___x_280_ = lean_uint16_shift_left(v___x_279_, v___x_278_);
v___x_281_ = lean_uint16_lor(v___x_277_, v___x_280_);
v___x_282_ = 4;
v___x_283_ = lean_unbox(v_res_255_);
lean_dec(v_res_255_);
v___x_284_ = lean_uint16_shift_left(v___x_283_, v___x_282_);
v___x_285_ = lean_uint16_lor(v___x_281_, v___x_284_);
v___x_286_ = lean_unbox(v_res_261_);
lean_dec(v_res_261_);
v___x_287_ = lean_uint16_lor(v___x_285_, v___x_286_);
v___x_288_ = 55296;
v___x_289_ = lean_uint16_dec_lt(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
uint16_t v___x_290_; uint8_t v___x_291_; 
v___x_290_ = 57344;
v___x_291_ = lean_uint16_dec_lt(v___x_287_, v___x_290_);
if (v___x_291_ == 0)
{
uint32_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
lean_del_object(v___x_263_);
v___x_292_ = lean_uint16_to_uint32(v___x_287_);
v___x_293_ = lean_box_uint32(v___x_292_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v___x_293_);
lean_ctor_set(v___x_257_, 0, v_pos_260_);
v___x_295_ = v___x_257_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_pos_260_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
else
{
uint16_t v___x_297_; uint8_t v___x_298_; 
v___x_297_ = 56320;
v___x_298_ = lean_uint16_dec_lt(v___x_287_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_301_; 
lean_del_object(v___x_263_);
v___x_299_ = l_Lean_Json_Parser_escapedChar___boxed__const__1;
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v___x_299_);
lean_ctor_set(v___x_257_, 0, v_pos_260_);
v___x_301_ = v___x_257_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_pos_260_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
else
{
lean_object* v___x_303_; 
lean_del_object(v___x_257_);
lean_inc(v_pos_260_);
v___x_303_ = l_Lean_Json_Parser_finishSurrogatePair(v___x_287_, v_pos_260_);
if (lean_obj_tag(v___x_303_) == 0)
{
if (lean_obj_tag(v___x_303_) == 0)
{
lean_del_object(v___x_263_);
lean_dec(v_pos_260_);
return v___x_303_;
}
else
{
lean_object* v_pos_304_; 
v_pos_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_pos_304_);
v___y_266_ = v___x_303_;
v_pos_267_ = v_pos_304_;
goto v___jp_265_;
}
}
else
{
lean_object* v_err_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
v_err_305_ = lean_ctor_get(v___x_303_, 1);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_312_ == 0)
{
lean_object* v_unused_313_; 
v_unused_313_ = lean_ctor_get(v___x_303_, 0);
lean_dec(v_unused_313_);
v___x_307_ = v___x_303_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_err_305_);
lean_dec(v___x_303_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
lean_inc(v_pos_260_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v_pos_260_);
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_pos_260_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_err_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_inc(v_pos_260_);
v___y_266_ = v___x_310_;
v_pos_267_ = v_pos_260_;
goto v___jp_265_;
}
}
}
}
}
}
else
{
uint32_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
lean_del_object(v___x_263_);
v___x_314_ = lean_uint16_to_uint32(v___x_287_);
v___x_315_ = lean_box_uint32(v___x_314_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v___x_315_);
lean_ctor_set(v___x_257_, 0, v_pos_260_);
v___x_317_ = v___x_257_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_pos_260_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
v___jp_265_:
{
lean_object* v_snd_268_; lean_object* v_snd_269_; uint8_t v_decide_270_; 
v_snd_268_ = lean_ctor_get(v_pos_260_, 1);
lean_inc(v_snd_268_);
lean_dec(v_pos_260_);
v_snd_269_ = lean_ctor_get(v_pos_267_, 1);
v_decide_270_ = lean_nat_dec_eq(v_snd_268_, v_snd_269_);
lean_dec(v_snd_268_);
if (v_decide_270_ == 0)
{
lean_dec_ref(v_pos_267_);
lean_del_object(v___x_263_);
return v___y_266_;
}
else
{
lean_object* v___x_271_; lean_object* v___x_273_; 
lean_dec_ref(v___y_266_);
v___x_271_ = l_Lean_Json_Parser_escapedChar___boxed__const__1;
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v___x_271_);
lean_ctor_set(v___x_263_, 0, v_pos_267_);
v___x_273_ = v___x_263_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_pos_267_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
else
{
lean_object* v_pos_320_; lean_object* v_err_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_del_object(v___x_257_);
lean_dec(v_res_255_);
lean_dec(v_res_252_);
lean_dec(v_res_249_);
v_pos_320_ = lean_ctor_get(v___x_259_, 0);
v_err_321_ = lean_ctor_get(v___x_259_, 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_259_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_err_321_);
lean_inc(v_pos_320_);
lean_dec(v___x_259_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_pos_320_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_err_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
else
{
lean_object* v_pos_330_; lean_object* v_err_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec(v_res_252_);
lean_dec(v_res_249_);
v_pos_330_ = lean_ctor_get(v___x_253_, 0);
v_err_331_ = lean_ctor_get(v___x_253_, 1);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_253_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_err_331_);
lean_inc(v_pos_330_);
lean_dec(v___x_253_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_pos_330_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_err_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
else
{
lean_object* v_pos_339_; lean_object* v_err_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec(v_res_249_);
v_pos_339_ = lean_ctor_get(v___x_250_, 0);
v_err_340_ = lean_ctor_get(v___x_250_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_250_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_err_340_);
lean_inc(v_pos_339_);
lean_dec(v___x_250_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_pos_339_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_err_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_object* v_pos_348_; lean_object* v_err_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
v_pos_348_ = lean_ctor_get(v___x_247_, 0);
v_err_349_ = lean_ctor_get(v___x_247_, 1);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_247_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_err_349_);
lean_inc(v_pos_348_);
lean_dec(v___x_247_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_pos_348_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_err_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = l_Lean_Json_Parser_escapedChar___boxed__const__2;
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v_it_x27_226_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
return v___x_358_;
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = l_Lean_Json_Parser_escapedChar___boxed__const__3;
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v_it_x27_226_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
return v___x_360_;
}
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = l_Lean_Json_Parser_escapedChar___boxed__const__4;
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v_it_x27_226_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
return v___x_362_;
}
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = l_Lean_Json_Parser_escapedChar___boxed__const__5;
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v_it_x27_226_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
return v___x_364_;
}
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = l_Lean_Json_Parser_escapedChar___boxed__const__6;
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_it_x27_226_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
return v___x_366_;
}
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = l_Lean_Json_Parser_escapedChar___boxed__const__7;
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v_it_x27_226_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
return v___x_368_;
}
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = l_Lean_Json_Parser_escapedChar___boxed__const__8;
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v_it_x27_226_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
return v___x_370_;
}
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = l_Lean_Json_Parser_escapedChar___boxed__const__9;
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v_it_x27_226_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
return v___x_372_;
}
}
}
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_box(0);
v___x_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_378_, 0, v_a_215_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_strCore(lean_object* v_acc_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_fst_384_; lean_object* v_snd_385_; lean_object* v___x_386_; uint8_t v_decide_387_; 
v_fst_384_ = lean_ctor_get(v_a_383_, 0);
v_snd_385_ = lean_ctor_get(v_a_383_, 1);
v___x_386_ = lean_string_utf8_byte_size(v_fst_384_);
v_decide_387_ = lean_nat_dec_eq(v_snd_385_, v___x_386_);
if (v_decide_387_ == 0)
{
lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_429_; 
lean_inc(v_snd_385_);
lean_inc(v_fst_384_);
v_isSharedCheck_429_ = !lean_is_exclusive(v_a_383_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; lean_object* v_unused_431_; 
v_unused_430_ = lean_ctor_get(v_a_383_, 1);
lean_dec(v_unused_430_);
v_unused_431_ = lean_ctor_get(v_a_383_, 0);
lean_dec(v_unused_431_);
v___x_389_ = v_a_383_;
v_isShared_390_ = v_isSharedCheck_429_;
goto v_resetjp_388_;
}
else
{
lean_dec(v_a_383_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_429_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
uint32_t v___x_391_; uint32_t v___x_392_; uint8_t v___x_393_; 
v___x_391_ = lean_string_utf8_get_fast(v_fst_384_, v_snd_385_);
v___x_392_ = 34;
v___x_393_ = lean_uint32_dec_eq(v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_string_utf8_next_fast(v_fst_384_, v_snd_385_);
lean_dec(v_snd_385_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v___x_394_);
v___x_396_ = v___x_389_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_fst_384_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___x_394_);
v___x_396_ = v_reuseFailAlloc_423_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
uint32_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 92;
v___x_401_ = lean_uint32_dec_eq(v___x_391_, v___x_400_);
if (v___x_401_ == 0)
{
uint32_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 32;
v___x_403_ = lean_uint32_dec_le(v___x_402_, v___x_391_);
if (v___x_403_ == 0)
{
lean_dec_ref(v_acc_382_);
goto v___jp_397_;
}
else
{
uint32_t v___x_404_; uint8_t v___x_405_; 
v___x_404_ = 1114111;
v___x_405_ = lean_uint32_dec_le(v___x_391_, v___x_404_);
if (v___x_405_ == 0)
{
lean_dec_ref(v_acc_382_);
goto v___jp_397_;
}
else
{
lean_object* v___x_406_; 
v___x_406_ = lean_string_push(v_acc_382_, v___x_391_);
v_acc_382_ = v___x_406_;
v_a_383_ = v___x_396_;
goto _start;
}
}
}
else
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Json_Parser_escapedChar(v___x_396_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_pos_409_; lean_object* v_res_410_; uint32_t v___x_411_; lean_object* v___x_412_; 
v_pos_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_pos_409_);
v_res_410_ = lean_ctor_get(v___x_408_, 1);
lean_inc(v_res_410_);
lean_dec_ref_known(v___x_408_, 2);
v___x_411_ = lean_unbox_uint32(v_res_410_);
lean_dec(v_res_410_);
v___x_412_ = lean_string_push(v_acc_382_, v___x_411_);
v_acc_382_ = v___x_412_;
v_a_383_ = v_pos_409_;
goto _start;
}
else
{
lean_object* v_pos_414_; lean_object* v_err_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec_ref(v_acc_382_);
v_pos_414_ = lean_ctor_get(v___x_408_, 0);
v_err_415_ = lean_ctor_get(v___x_408_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_408_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_err_415_);
lean_inc(v_pos_414_);
lean_dec(v___x_408_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_pos_414_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_err_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
v___jp_397_:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = ((lean_object*)(l_Lean_Json_Parser_strCore___closed__1));
v___x_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_396_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
return v___x_399_;
}
}
}
else
{
lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_424_ = lean_string_utf8_next_fast(v_fst_384_, v_snd_385_);
lean_dec(v_snd_385_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v___x_424_);
v___x_426_ = v___x_389_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_fst_384_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v___x_424_);
v___x_426_ = v_reuseFailAlloc_428_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; 
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v_acc_382_);
return v___x_427_;
}
}
}
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec_ref(v_acc_382_);
v___x_432_ = lean_box(0);
v___x_433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_433_, 0, v_a_383_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_str(lean_object* v_a_434_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_436_ = l_Lean_Json_Parser_strCore(v___x_435_, v_a_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCore(lean_object* v_acc_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_fst_439_; lean_object* v_snd_440_; lean_object* v___x_441_; uint8_t v_decide_442_; 
v_fst_439_ = lean_ctor_get(v_a_438_, 0);
v_snd_440_ = lean_ctor_get(v_a_438_, 1);
v___x_441_ = lean_string_utf8_byte_size(v_fst_439_);
v_decide_442_ = lean_nat_dec_eq(v_snd_440_, v___x_441_);
if (v_decide_442_ == 0)
{
uint32_t v___x_443_; uint32_t v___x_444_; uint8_t v___x_445_; 
v___x_443_ = lean_string_utf8_get_fast(v_fst_439_, v_snd_440_);
v___x_444_ = 48;
v___x_445_ = lean_uint32_dec_le(v___x_444_, v___x_443_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; 
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_a_438_);
lean_ctor_set(v___x_446_, 1, v_acc_437_);
return v___x_446_;
}
else
{
uint32_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = 57;
v___x_448_ = lean_uint32_dec_le(v___x_443_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v_a_438_);
lean_ctor_set(v___x_449_, 1, v_acc_437_);
return v___x_449_;
}
else
{
lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_463_; 
lean_inc(v_snd_440_);
lean_inc(v_fst_439_);
v_isSharedCheck_463_ = !lean_is_exclusive(v_a_438_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; lean_object* v_unused_465_; 
v_unused_464_ = lean_ctor_get(v_a_438_, 1);
lean_dec(v_unused_464_);
v_unused_465_ = lean_ctor_get(v_a_438_, 0);
lean_dec(v_unused_465_);
v___x_451_ = v_a_438_;
v_isShared_452_ = v_isSharedCheck_463_;
goto v_resetjp_450_;
}
else
{
lean_dec(v_a_438_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_463_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_453_ = lean_string_utf8_next_fast(v_fst_439_, v_snd_440_);
lean_dec(v_snd_440_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_453_);
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_fst_439_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v___x_453_);
v___x_455_ = v_reuseFailAlloc_462_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; uint32_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_456_ = lean_unsigned_to_nat(10u);
v___x_457_ = lean_nat_mul(v___x_456_, v_acc_437_);
lean_dec(v_acc_437_);
v___x_458_ = lean_uint32_sub(v___x_443_, v___x_444_);
v___x_459_ = lean_uint32_to_nat(v___x_458_);
v___x_460_ = lean_nat_add(v___x_457_, v___x_459_);
lean_dec(v___x_459_);
lean_dec(v___x_457_);
v_acc_437_ = v___x_460_;
v_a_438_ = v___x_455_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_466_; 
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v_a_438_);
lean_ctor_set(v___x_466_, 1, v_acc_437_);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCoreNumDigits(lean_object* v_acc_467_, lean_object* v_digits_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_fst_473_; lean_object* v_snd_474_; lean_object* v___x_475_; uint8_t v_decide_476_; 
v_fst_473_ = lean_ctor_get(v_a_469_, 0);
v_snd_474_ = lean_ctor_get(v_a_469_, 1);
v___x_475_ = lean_string_utf8_byte_size(v_fst_473_);
v_decide_476_ = lean_nat_dec_eq(v_snd_474_, v___x_475_);
if (v_decide_476_ == 0)
{
uint32_t v___x_477_; uint32_t v___x_478_; uint8_t v___x_479_; 
v___x_477_ = lean_string_utf8_get_fast(v_fst_473_, v_snd_474_);
v___x_478_ = 48;
v___x_479_ = lean_uint32_dec_le(v___x_478_, v___x_477_);
if (v___x_479_ == 0)
{
goto v___jp_470_;
}
else
{
uint32_t v___x_480_; uint8_t v___x_481_; 
v___x_480_ = 57;
v___x_481_ = lean_uint32_dec_le(v___x_477_, v___x_480_);
if (v___x_481_ == 0)
{
goto v___jp_470_;
}
else
{
lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_497_; 
lean_inc(v_snd_474_);
lean_inc(v_fst_473_);
v_isSharedCheck_497_ = !lean_is_exclusive(v_a_469_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; lean_object* v_unused_499_; 
v_unused_498_ = lean_ctor_get(v_a_469_, 1);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v_a_469_, 0);
lean_dec(v_unused_499_);
v___x_483_ = v_a_469_;
v_isShared_484_ = v_isSharedCheck_497_;
goto v_resetjp_482_;
}
else
{
lean_dec(v_a_469_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_497_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = lean_string_utf8_next_fast(v_fst_473_, v_snd_474_);
lean_dec(v_snd_474_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v___x_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_fst_473_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v___x_485_);
v___x_487_ = v_reuseFailAlloc_496_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; uint32_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_488_ = lean_unsigned_to_nat(10u);
v___x_489_ = lean_nat_mul(v___x_488_, v_acc_467_);
lean_dec(v_acc_467_);
v___x_490_ = lean_uint32_sub(v___x_477_, v___x_478_);
v___x_491_ = lean_uint32_to_nat(v___x_490_);
v___x_492_ = lean_nat_add(v___x_489_, v___x_491_);
lean_dec(v___x_491_);
lean_dec(v___x_489_);
v___x_493_ = lean_unsigned_to_nat(1u);
v___x_494_ = lean_nat_add(v_digits_468_, v___x_493_);
lean_dec(v_digits_468_);
v_acc_467_ = v___x_492_;
v_digits_468_ = v___x_494_;
v_a_469_ = v___x_487_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v_acc_467_);
lean_ctor_set(v___x_500_, 1, v_digits_468_);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v_a_469_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
return v___x_501_;
}
v___jp_470_:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v_acc_467_);
lean_ctor_set(v___x_471_, 1, v_digits_468_);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v_a_469_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg(lean_object* v_desc_503_, lean_object* v_inst_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_fst_506_; lean_object* v_snd_507_; lean_object* v___x_508_; uint8_t v_decide_509_; 
v_fst_506_ = lean_ctor_get(v_a_505_, 0);
v_snd_507_ = lean_ctor_get(v_a_505_, 1);
v___x_508_ = lean_string_utf8_byte_size(v_fst_506_);
v_decide_509_ = lean_nat_dec_eq(v_snd_507_, v___x_508_);
if (v_decide_509_ == 0)
{
uint32_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_510_ = lean_string_utf8_get_fast(v_fst_506_, v_snd_507_);
v___x_511_ = lean_box_uint32(v___x_510_);
v___x_512_ = lean_apply_1(v_inst_504_, v___x_511_);
v___x_513_ = lean_unbox(v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_514_ = ((lean_object*)(l_Lean_Json_Parser_lookahead___redArg___closed__0));
v___x_515_ = lean_string_append(v___x_514_, v_desc_503_);
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
v___x_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_517_, 0, v_a_505_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
return v___x_517_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_box(0);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v_a_505_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
return v___x_519_;
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec_ref(v_inst_504_);
v___x_520_ = lean_box(0);
v___x_521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_521_, 0, v_a_505_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg___boxed(lean_object* v_desc_522_, lean_object* v_inst_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_Json_Parser_lookahead___redArg(v_desc_522_, v_inst_523_, v_a_524_);
lean_dec_ref(v_desc_522_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead(lean_object* v_p_526_, lean_object* v_desc_527_, lean_object* v_inst_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_fst_530_; lean_object* v_snd_531_; lean_object* v___x_532_; uint8_t v_decide_533_; 
v_fst_530_ = lean_ctor_get(v_a_529_, 0);
v_snd_531_ = lean_ctor_get(v_a_529_, 1);
v___x_532_ = lean_string_utf8_byte_size(v_fst_530_);
v_decide_533_ = lean_nat_dec_eq(v_snd_531_, v___x_532_);
if (v_decide_533_ == 0)
{
uint32_t v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_534_ = lean_string_utf8_get_fast(v_fst_530_, v_snd_531_);
v___x_535_ = lean_box_uint32(v___x_534_);
v___x_536_ = lean_apply_1(v_inst_528_, v___x_535_);
v___x_537_ = lean_unbox(v___x_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_538_ = ((lean_object*)(l_Lean_Json_Parser_lookahead___redArg___closed__0));
v___x_539_ = lean_string_append(v___x_538_, v_desc_527_);
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
v___x_541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_541_, 0, v_a_529_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
return v___x_541_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_box(0);
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v_a_529_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
return v___x_543_;
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec_ref(v_inst_528_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_545_, 0, v_a_529_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___boxed(lean_object* v_p_546_, lean_object* v_desc_547_, lean_object* v_inst_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Json_Parser_lookahead(v_p_546_, v_desc_547_, v_inst_548_, v_a_549_);
lean_dec_ref(v_desc_547_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNonZero(lean_object* v_a_554_){
_start:
{
uint8_t v___y_556_; lean_object* v_fst_561_; lean_object* v_snd_562_; lean_object* v___x_563_; uint8_t v_decide_564_; 
v_fst_561_ = lean_ctor_get(v_a_554_, 0);
v_snd_562_ = lean_ctor_get(v_a_554_, 1);
v___x_563_ = lean_string_utf8_byte_size(v_fst_561_);
v_decide_564_ = lean_nat_dec_eq(v_snd_562_, v___x_563_);
if (v_decide_564_ == 0)
{
uint32_t v___x_565_; uint32_t v___x_566_; uint8_t v___x_567_; 
v___x_565_ = lean_string_utf8_get_fast(v_fst_561_, v_snd_562_);
v___x_566_ = 49;
v___x_567_ = lean_uint32_dec_le(v___x_566_, v___x_565_);
if (v___x_567_ == 0)
{
v___y_556_ = v___x_567_;
goto v___jp_555_;
}
else
{
uint32_t v___x_568_; uint8_t v___x_569_; 
v___x_568_ = 57;
v___x_569_ = lean_uint32_dec_le(v___x_565_, v___x_568_);
v___y_556_ = v___x_569_;
goto v___jp_555_;
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_box(0);
v___x_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_571_, 0, v_a_554_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
return v___x_571_;
}
v___jp_555_:
{
if (v___y_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_558_, 0, v_a_554_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
return v___x_558_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = l_Lean_Json_Parser_natCore(v___x_559_, v_a_554_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNumDigits(lean_object* v_a_575_){
_start:
{
uint8_t v___y_577_; lean_object* v_fst_582_; lean_object* v_snd_583_; lean_object* v___x_584_; uint8_t v_decide_585_; 
v_fst_582_ = lean_ctor_get(v_a_575_, 0);
v_snd_583_ = lean_ctor_get(v_a_575_, 1);
v___x_584_ = lean_string_utf8_byte_size(v_fst_582_);
v_decide_585_ = lean_nat_dec_eq(v_snd_583_, v___x_584_);
if (v_decide_585_ == 0)
{
uint32_t v___x_586_; uint32_t v___x_587_; uint8_t v___x_588_; 
v___x_586_ = lean_string_utf8_get_fast(v_fst_582_, v_snd_583_);
v___x_587_ = 48;
v___x_588_ = lean_uint32_dec_le(v___x_587_, v___x_586_);
if (v___x_588_ == 0)
{
v___y_577_ = v___x_588_;
goto v___jp_576_;
}
else
{
uint32_t v___x_589_; uint8_t v___x_590_; 
v___x_589_ = 57;
v___x_590_ = lean_uint32_dec_le(v___x_586_, v___x_589_);
v___y_577_ = v___x_590_;
goto v___jp_576_;
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_box(0);
v___x_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_592_, 0, v_a_575_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
return v___x_592_;
}
v___jp_576_:
{
if (v___y_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_579_, 0, v_a_575_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_580_, v___x_580_, v_a_575_);
return v___x_581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natMaybeZero(lean_object* v_a_596_){
_start:
{
uint8_t v___y_598_; lean_object* v_fst_603_; lean_object* v_snd_604_; lean_object* v___x_605_; uint8_t v_decide_606_; 
v_fst_603_ = lean_ctor_get(v_a_596_, 0);
v_snd_604_ = lean_ctor_get(v_a_596_, 1);
v___x_605_ = lean_string_utf8_byte_size(v_fst_603_);
v_decide_606_ = lean_nat_dec_eq(v_snd_604_, v___x_605_);
if (v_decide_606_ == 0)
{
uint32_t v___x_607_; uint32_t v___x_608_; uint8_t v___x_609_; 
v___x_607_ = lean_string_utf8_get_fast(v_fst_603_, v_snd_604_);
v___x_608_ = 48;
v___x_609_ = lean_uint32_dec_le(v___x_608_, v___x_607_);
if (v___x_609_ == 0)
{
v___y_598_ = v___x_609_;
goto v___jp_597_;
}
else
{
uint32_t v___x_610_; uint8_t v___x_611_; 
v___x_610_ = 57;
v___x_611_ = lean_uint32_dec_le(v___x_607_, v___x_610_);
v___y_598_ = v___x_611_;
goto v___jp_597_;
}
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_box(0);
v___x_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_613_, 0, v_a_596_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
return v___x_613_;
}
v___jp_597_:
{
if (v___y_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_600_, 0, v_a_596_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
return v___x_600_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = l_Lean_Json_Parser_natCore(v___x_601_, v_a_596_);
return v___x_602_;
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_numSign___closed__0(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = lean_nat_to_int(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Json_Parser_numSign___closed__1(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v___x_617_ = lean_int_neg(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numSign(lean_object* v_a_618_){
_start:
{
lean_object* v_fst_619_; lean_object* v_snd_620_; lean_object* v___x_621_; uint8_t v_decide_622_; 
v_fst_619_ = lean_ctor_get(v_a_618_, 0);
v_snd_620_ = lean_ctor_get(v_a_618_, 1);
v___x_621_ = lean_string_utf8_byte_size(v_fst_619_);
v_decide_622_ = lean_nat_dec_eq(v_snd_620_, v___x_621_);
if (v_decide_622_ == 0)
{
uint32_t v___x_623_; uint32_t v___x_624_; uint8_t v___x_625_; 
v___x_623_ = lean_string_utf8_get_fast(v_fst_619_, v_snd_620_);
v___x_624_ = 45;
v___x_625_ = lean_uint32_dec_eq(v___x_623_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v_a_618_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
return v___x_627_;
}
else
{
lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_637_; 
lean_inc(v_snd_620_);
lean_inc(v_fst_619_);
v_isSharedCheck_637_ = !lean_is_exclusive(v_a_618_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; lean_object* v_unused_639_; 
v_unused_638_ = lean_ctor_get(v_a_618_, 1);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_a_618_, 0);
lean_dec(v_unused_639_);
v___x_629_ = v_a_618_;
v_isShared_630_ = v_isSharedCheck_637_;
goto v_resetjp_628_;
}
else
{
lean_dec(v_a_618_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_637_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_631_ = lean_string_utf8_next_fast(v_fst_619_, v_snd_620_);
lean_dec(v_snd_620_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v___x_631_);
v___x_633_ = v___x_629_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_fst_619_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v___x_631_);
v___x_633_ = v_reuseFailAlloc_636_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
return v___x_635_;
}
}
}
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_box(0);
v___x_641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_641_, 0, v_a_618_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_nat(lean_object* v_a_642_){
_start:
{
uint8_t v___y_644_; lean_object* v_fst_649_; lean_object* v_snd_650_; lean_object* v___x_651_; uint8_t v_decide_652_; 
v_fst_649_ = lean_ctor_get(v_a_642_, 0);
v_snd_650_ = lean_ctor_get(v_a_642_, 1);
v___x_651_ = lean_string_utf8_byte_size(v_fst_649_);
v_decide_652_ = lean_nat_dec_eq(v_snd_650_, v___x_651_);
if (v_decide_652_ == 0)
{
uint32_t v___x_653_; uint32_t v___x_654_; uint8_t v___x_655_; 
v___x_653_ = lean_string_utf8_get_fast(v_fst_649_, v_snd_650_);
v___x_654_ = 48;
v___x_655_ = lean_uint32_dec_eq(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
uint32_t v___x_656_; uint8_t v___x_657_; 
v___x_656_ = 49;
v___x_657_ = lean_uint32_dec_le(v___x_656_, v___x_653_);
if (v___x_657_ == 0)
{
v___y_644_ = v___x_657_;
goto v___jp_643_;
}
else
{
uint32_t v___x_658_; uint8_t v___x_659_; 
v___x_658_ = 57;
v___x_659_ = lean_uint32_dec_le(v___x_653_, v___x_658_);
v___y_644_ = v___x_659_;
goto v___jp_643_;
}
}
else
{
lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_669_; 
lean_inc(v_snd_650_);
lean_inc(v_fst_649_);
v_isSharedCheck_669_ = !lean_is_exclusive(v_a_642_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; lean_object* v_unused_671_; 
v_unused_670_ = lean_ctor_get(v_a_642_, 1);
lean_dec(v_unused_670_);
v_unused_671_ = lean_ctor_get(v_a_642_, 0);
lean_dec(v_unused_671_);
v___x_661_ = v_a_642_;
v_isShared_662_ = v_isSharedCheck_669_;
goto v_resetjp_660_;
}
else
{
lean_dec(v_a_642_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_669_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_665_; 
v___x_663_ = lean_string_utf8_next_fast(v_fst_649_, v_snd_650_);
lean_dec(v_snd_650_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v___x_663_);
v___x_665_ = v___x_661_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_fst_649_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_663_);
v___x_665_ = v_reuseFailAlloc_668_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
return v___x_667_;
}
}
}
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_box(0);
v___x_673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_673_, 0, v_a_642_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
return v___x_673_;
}
v___jp_643_:
{
if (v___y_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_646_, 0, v_a_642_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
return v___x_646_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = l_Lean_Json_Parser_natCore(v___x_647_, v_a_642_);
return v___x_648_;
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_numWithDecimals___closed__0(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = l_System_Platform_numBits;
v___x_675_ = lean_unsigned_to_nat(2u);
v___x_676_ = lean_nat_pow(v___x_675_, v___x_674_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numWithDecimals(lean_object* v_a_680_){
_start:
{
lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; uint8_t v___y_685_; lean_object* v___y_732_; lean_object* v___y_736_; lean_object* v_pos_737_; lean_object* v_fst_738_; lean_object* v_snd_739_; lean_object* v_res_740_; lean_object* v___y_763_; lean_object* v___y_764_; uint8_t v___y_765_; lean_object* v_pos_784_; lean_object* v_fst_785_; lean_object* v_snd_786_; lean_object* v_res_787_; lean_object* v_fst_802_; lean_object* v_snd_803_; lean_object* v___x_804_; uint8_t v_decide_805_; 
v_fst_802_ = lean_ctor_get(v_a_680_, 0);
v_snd_803_ = lean_ctor_get(v_a_680_, 1);
v___x_804_ = lean_string_utf8_byte_size(v_fst_802_);
v_decide_805_ = lean_nat_dec_eq(v_snd_803_, v___x_804_);
if (v_decide_805_ == 0)
{
uint32_t v___x_806_; uint32_t v___x_807_; uint8_t v___x_808_; 
lean_inc(v_snd_803_);
lean_inc(v_fst_802_);
v___x_806_ = lean_string_utf8_get_fast(v_fst_802_, v_snd_803_);
v___x_807_ = 45;
v___x_808_ = lean_uint32_dec_eq(v___x_806_, v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
v___x_809_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v_pos_784_ = v_a_680_;
v_fst_785_ = v_fst_802_;
v_snd_786_ = v_snd_803_;
v_res_787_ = v___x_809_;
goto v___jp_783_;
}
else
{
lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_818_; 
v_isSharedCheck_818_ = !lean_is_exclusive(v_a_680_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; lean_object* v_unused_820_; 
v_unused_819_ = lean_ctor_get(v_a_680_, 1);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_a_680_, 0);
lean_dec(v_unused_820_);
v___x_811_ = v_a_680_;
v_isShared_812_ = v_isSharedCheck_818_;
goto v_resetjp_810_;
}
else
{
lean_dec(v_a_680_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_818_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_string_utf8_next_fast(v_fst_802_, v_snd_803_);
lean_dec(v_snd_803_);
lean_inc(v_fst_802_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 1, v___x_813_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_fst_802_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_813_);
v___x_815_ = v_reuseFailAlloc_817_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; 
v___x_816_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v_pos_784_ = v___x_815_;
v_fst_785_ = v_fst_802_;
v_snd_786_ = v___x_813_;
v_res_787_ = v___x_816_;
goto v___jp_783_;
}
}
}
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_box(0);
v___x_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_822_, 0, v_a_680_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
return v___x_822_;
}
v___jp_681_:
{
if (v___y_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec(v___y_683_);
v___x_686_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_687_, 0, v___y_684_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
return v___x_687_;
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_688_, v___x_688_, v___y_684_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_res_690_; lean_object* v_pos_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_721_; 
v_res_690_ = lean_ctor_get(v___x_689_, 1);
v_pos_691_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_721_ == 0)
{
v___x_693_ = v___x_689_;
v_isShared_694_ = v_isSharedCheck_721_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_res_690_);
lean_inc(v_pos_691_);
lean_dec(v___x_689_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_721_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_fst_695_; lean_object* v_snd_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_720_; 
v_fst_695_ = lean_ctor_get(v_res_690_, 0);
v_snd_696_ = lean_ctor_get(v_res_690_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_res_690_);
if (v_isSharedCheck_720_ == 0)
{
v___x_698_ = v_res_690_;
v_isShared_699_ = v_isSharedCheck_720_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_snd_696_);
lean_inc(v_fst_695_);
lean_dec(v_res_690_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_720_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_701_ = lean_nat_dec_lt(v___x_700_, v_snd_696_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_702_ = lean_nat_to_int(v___y_683_);
v___x_703_ = lean_unsigned_to_nat(10u);
v___x_704_ = lean_nat_pow(v___x_703_, v_snd_696_);
v___x_705_ = lean_nat_to_int(v___x_704_);
v___x_706_ = lean_int_mul(v___x_702_, v___x_705_);
lean_dec(v___x_705_);
lean_dec(v___x_702_);
v___x_707_ = lean_nat_to_int(v_fst_695_);
v___x_708_ = lean_int_add(v___x_706_, v___x_707_);
lean_dec(v___x_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_int_mul(v___y_682_, v___x_708_);
lean_dec(v___x_708_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_709_);
v___x_711_ = v___x_698_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_snd_696_);
v___x_711_ = v_reuseFailAlloc_715_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_713_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v___x_711_);
v___x_713_ = v___x_693_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_pos_691_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_718_; 
lean_del_object(v___x_698_);
lean_dec(v_snd_696_);
lean_dec(v_fst_695_);
lean_dec(v___y_683_);
v___x_716_ = ((lean_object*)(l_Lean_Json_Parser_numWithDecimals___closed__2));
if (v_isShared_694_ == 0)
{
lean_ctor_set_tag(v___x_693_, 1);
lean_ctor_set(v___x_693_, 1, v___x_716_);
v___x_718_ = v___x_693_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_pos_691_);
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
}
}
else
{
lean_object* v_pos_722_; lean_object* v_err_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v___y_683_);
v_pos_722_ = lean_ctor_get(v___x_689_, 0);
v_err_723_ = lean_ctor_get(v___x_689_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_689_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_err_723_);
lean_inc(v_pos_722_);
lean_dec(v___x_689_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_pos_722_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_err_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
v___jp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_box(0);
v___x_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_734_, 0, v___y_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
return v___x_734_;
}
v___jp_735_:
{
lean_object* v___x_741_; uint8_t v_decide_742_; 
v___x_741_ = lean_string_utf8_byte_size(v_fst_738_);
v_decide_742_ = lean_nat_dec_eq(v_snd_739_, v___x_741_);
if (v_decide_742_ == 0)
{
uint32_t v___x_743_; uint32_t v___x_744_; uint8_t v___x_745_; 
v___x_743_ = lean_string_utf8_get_fast(v_fst_738_, v_snd_739_);
v___x_744_ = 46;
v___x_745_ = lean_uint32_dec_eq(v___x_743_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec(v_snd_739_);
lean_dec(v_fst_738_);
v___x_746_ = lean_nat_to_int(v_res_740_);
v___x_747_ = lean_int_mul(v___y_736_, v___x_746_);
lean_dec(v___x_746_);
v___x_748_ = l_Lean_JsonNumber_fromInt(v___x_747_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v_pos_737_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
return v___x_749_;
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v_decide_752_; 
lean_dec_ref(v_pos_737_);
v___x_750_ = lean_string_utf8_next_fast(v_fst_738_, v_snd_739_);
lean_dec(v_snd_739_);
lean_inc(v_fst_738_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v_fst_738_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v_decide_752_ = lean_nat_dec_eq(v___x_750_, v___x_741_);
if (v_decide_752_ == 0)
{
if (v___x_745_ == 0)
{
lean_dec(v_res_740_);
lean_dec(v_fst_738_);
v___y_732_ = v___x_751_;
goto v___jp_731_;
}
else
{
uint32_t v___x_753_; uint32_t v___x_754_; uint8_t v___x_755_; 
v___x_753_ = lean_string_utf8_get_fast(v_fst_738_, v___x_750_);
lean_dec(v_fst_738_);
v___x_754_ = 48;
v___x_755_ = lean_uint32_dec_le(v___x_754_, v___x_753_);
if (v___x_755_ == 0)
{
v___y_682_ = v___y_736_;
v___y_683_ = v_res_740_;
v___y_684_ = v___x_751_;
v___y_685_ = v___x_755_;
goto v___jp_681_;
}
else
{
uint32_t v___x_756_; uint8_t v___x_757_; 
v___x_756_ = 57;
v___x_757_ = lean_uint32_dec_le(v___x_753_, v___x_756_);
v___y_682_ = v___y_736_;
v___y_683_ = v_res_740_;
v___y_684_ = v___x_751_;
v___y_685_ = v___x_757_;
goto v___jp_681_;
}
}
}
else
{
lean_dec(v_res_740_);
lean_dec(v_fst_738_);
v___y_732_ = v___x_751_;
goto v___jp_731_;
}
}
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec(v_snd_739_);
lean_dec(v_fst_738_);
v___x_758_ = lean_nat_to_int(v_res_740_);
v___x_759_ = lean_int_mul(v___y_736_, v___x_758_);
lean_dec(v___x_758_);
v___x_760_ = l_Lean_JsonNumber_fromInt(v___x_759_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v_pos_737_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
return v___x_761_;
}
}
v___jp_762_:
{
if (v___y_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_767_, 0, v___y_763_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
return v___x_767_;
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = l_Lean_Json_Parser_natCore(v___x_768_, v___y_763_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_pos_770_; lean_object* v_res_771_; lean_object* v_fst_772_; lean_object* v_snd_773_; 
v_pos_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_pos_770_);
v_res_771_ = lean_ctor_get(v___x_769_, 1);
lean_inc(v_res_771_);
lean_dec_ref_known(v___x_769_, 2);
v_fst_772_ = lean_ctor_get(v_pos_770_, 0);
lean_inc(v_fst_772_);
v_snd_773_ = lean_ctor_get(v_pos_770_, 1);
lean_inc(v_snd_773_);
v___y_736_ = v___y_764_;
v_pos_737_ = v_pos_770_;
v_fst_738_ = v_fst_772_;
v_snd_739_ = v_snd_773_;
v_res_740_ = v_res_771_;
goto v___jp_735_;
}
else
{
lean_object* v_pos_774_; lean_object* v_err_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
v_pos_774_ = lean_ctor_get(v___x_769_, 0);
v_err_775_ = lean_ctor_get(v___x_769_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_769_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_err_775_);
lean_inc(v_pos_774_);
lean_dec(v___x_769_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_pos_774_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_err_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
v___jp_783_:
{
lean_object* v___x_788_; uint8_t v_decide_789_; 
v___x_788_ = lean_string_utf8_byte_size(v_fst_785_);
v_decide_789_ = lean_nat_dec_eq(v_snd_786_, v___x_788_);
if (v_decide_789_ == 0)
{
uint32_t v___x_790_; uint32_t v___x_791_; uint8_t v___x_792_; 
v___x_790_ = lean_string_utf8_get_fast(v_fst_785_, v_snd_786_);
v___x_791_ = 48;
v___x_792_ = lean_uint32_dec_eq(v___x_790_, v___x_791_);
if (v___x_792_ == 0)
{
uint32_t v___x_793_; uint8_t v___x_794_; 
lean_dec(v_snd_786_);
lean_dec(v_fst_785_);
v___x_793_ = 49;
v___x_794_ = lean_uint32_dec_le(v___x_793_, v___x_790_);
if (v___x_794_ == 0)
{
v___y_763_ = v_pos_784_;
v___y_764_ = v_res_787_;
v___y_765_ = v___x_794_;
goto v___jp_762_;
}
else
{
uint32_t v___x_795_; uint8_t v___x_796_; 
v___x_795_ = 57;
v___x_796_ = lean_uint32_dec_le(v___x_790_, v___x_795_);
v___y_763_ = v_pos_784_;
v___y_764_ = v_res_787_;
v___y_765_ = v___x_796_;
goto v___jp_762_;
}
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v_pos_784_);
v___x_797_ = lean_string_utf8_next_fast(v_fst_785_, v_snd_786_);
lean_dec(v_snd_786_);
lean_inc(v_fst_785_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v_fst_785_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = lean_unsigned_to_nat(0u);
v___y_736_ = v_res_787_;
v_pos_737_ = v___x_798_;
v_fst_738_ = v_fst_785_;
v_snd_739_ = v___x_797_;
v_res_740_ = v___x_799_;
goto v___jp_735_;
}
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec(v_snd_786_);
lean_dec(v_fst_785_);
v___x_800_ = lean_box(0);
v___x_801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_801_, 0, v_pos_784_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent(lean_object* v_value_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___y_829_; lean_object* v___y_833_; uint8_t v___y_834_; lean_object* v___y_859_; uint8_t v___y_860_; lean_object* v___y_891_; lean_object* v_fst_892_; lean_object* v_snd_893_; lean_object* v_fst_903_; lean_object* v_snd_904_; lean_object* v___x_938_; uint8_t v_decide_939_; 
v_fst_903_ = lean_ctor_get(v_a_827_, 0);
v_snd_904_ = lean_ctor_get(v_a_827_, 1);
v___x_938_ = lean_string_utf8_byte_size(v_fst_903_);
v_decide_939_ = lean_nat_dec_eq(v_snd_904_, v___x_938_);
if (v_decide_939_ == 0)
{
uint32_t v___x_940_; uint32_t v___x_941_; uint8_t v___x_942_; 
v___x_940_ = lean_string_utf8_get_fast(v_fst_903_, v_snd_904_);
v___x_941_ = 101;
v___x_942_ = lean_uint32_dec_eq(v___x_940_, v___x_941_);
if (v___x_942_ == 0)
{
uint32_t v___x_943_; uint8_t v___x_944_; 
v___x_943_ = 69;
v___x_944_ = lean_uint32_dec_eq(v___x_940_, v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_a_827_);
lean_ctor_set(v___x_945_, 1, v_value_826_);
return v___x_945_;
}
else
{
goto v___jp_905_;
}
}
else
{
goto v___jp_905_;
}
}
else
{
lean_object* v___x_946_; 
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v_a_827_);
lean_ctor_set(v___x_946_, 1, v_value_826_);
return v___x_946_;
}
v___jp_828_:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_box(0);
v___x_831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_831_, 0, v___y_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
return v___x_831_;
}
v___jp_832_:
{
if (v___y_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec_ref(v_value_826_);
v___x_835_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_836_, 0, v___y_833_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
return v___x_836_;
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = l_Lean_Json_Parser_natCore(v___x_837_, v___y_833_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_pos_839_; lean_object* v_res_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_848_; 
v_pos_839_ = lean_ctor_get(v___x_838_, 0);
v_res_840_ = lean_ctor_get(v___x_838_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_848_ == 0)
{
v___x_842_ = v___x_838_;
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_res_840_);
lean_inc(v_pos_839_);
lean_dec(v___x_838_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_844_ = l_Lean_JsonNumber_shiftr(v_value_826_, v_res_840_);
lean_dec(v_res_840_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v___x_844_);
v___x_846_ = v___x_842_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_pos_839_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
else
{
lean_object* v_pos_849_; lean_object* v_err_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec_ref(v_value_826_);
v_pos_849_ = lean_ctor_get(v___x_838_, 0);
v_err_850_ = lean_ctor_get(v___x_838_, 1);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_838_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_err_850_);
lean_inc(v_pos_849_);
lean_dec(v___x_838_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_pos_849_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_err_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
v___jp_858_:
{
if (v___y_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec_ref(v_value_826_);
v___x_861_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_862_, 0, v___y_859_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
return v___x_862_;
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = l_Lean_Json_Parser_natCore(v___x_863_, v___y_859_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_pos_865_; lean_object* v_res_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_880_; 
v_pos_865_ = lean_ctor_get(v___x_864_, 0);
v_res_866_ = lean_ctor_get(v___x_864_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_880_ == 0)
{
v___x_868_ = v___x_864_;
v_isShared_869_ = v_isSharedCheck_880_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_res_866_);
lean_inc(v_pos_865_);
lean_dec(v___x_864_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_880_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_870_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_871_ = lean_nat_dec_lt(v___x_870_, v_res_866_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = l_Lean_JsonNumber_shiftl(v_value_826_, v_res_866_);
lean_dec(v_res_866_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v___x_872_);
v___x_874_ = v___x_868_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_pos_865_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
else
{
lean_object* v___x_876_; lean_object* v___x_878_; 
lean_dec(v_res_866_);
lean_dec_ref(v_value_826_);
v___x_876_ = ((lean_object*)(l_Lean_Json_Parser_exponent___closed__1));
if (v_isShared_869_ == 0)
{
lean_ctor_set_tag(v___x_868_, 1);
lean_ctor_set(v___x_868_, 1, v___x_876_);
v___x_878_ = v___x_868_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_pos_865_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
else
{
lean_object* v_pos_881_; lean_object* v_err_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec_ref(v_value_826_);
v_pos_881_ = lean_ctor_get(v___x_864_, 0);
v_err_882_ = lean_ctor_get(v___x_864_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_864_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_err_882_);
lean_inc(v_pos_881_);
lean_dec(v___x_864_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_pos_881_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_err_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
v___jp_890_:
{
lean_object* v___x_894_; uint8_t v_decide_895_; 
v___x_894_ = lean_string_utf8_byte_size(v_fst_892_);
v_decide_895_ = lean_nat_dec_eq(v_snd_893_, v___x_894_);
if (v_decide_895_ == 0)
{
uint32_t v___x_896_; uint32_t v___x_897_; uint8_t v___x_898_; 
v___x_896_ = lean_string_utf8_get_fast(v_fst_892_, v_snd_893_);
lean_dec(v_snd_893_);
lean_dec(v_fst_892_);
v___x_897_ = 48;
v___x_898_ = lean_uint32_dec_le(v___x_897_, v___x_896_);
if (v___x_898_ == 0)
{
v___y_859_ = v___y_891_;
v___y_860_ = v___x_898_;
goto v___jp_858_;
}
else
{
uint32_t v___x_899_; uint8_t v___x_900_; 
v___x_899_ = 57;
v___x_900_ = lean_uint32_dec_le(v___x_896_, v___x_899_);
v___y_859_ = v___y_891_;
v___y_860_ = v___x_900_;
goto v___jp_858_;
}
}
else
{
lean_object* v___x_901_; lean_object* v___x_902_; 
lean_dec(v_snd_893_);
lean_dec(v_fst_892_);
lean_dec_ref(v_value_826_);
v___x_901_ = lean_box(0);
v___x_902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_902_, 0, v___y_891_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
return v___x_902_;
}
}
v___jp_905_:
{
lean_object* v___x_906_; uint8_t v_decide_907_; 
v___x_906_ = lean_string_utf8_byte_size(v_fst_903_);
v_decide_907_ = lean_nat_dec_eq(v_snd_904_, v___x_906_);
if (v_decide_907_ == 0)
{
lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_933_; 
lean_inc(v_snd_904_);
lean_inc(v_fst_903_);
v_isSharedCheck_933_ = !lean_is_exclusive(v_a_827_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; lean_object* v_unused_935_; 
v_unused_934_ = lean_ctor_get(v_a_827_, 1);
lean_dec(v_unused_934_);
v_unused_935_ = lean_ctor_get(v_a_827_, 0);
lean_dec(v_unused_935_);
v___x_909_ = v_a_827_;
v_isShared_910_ = v_isSharedCheck_933_;
goto v_resetjp_908_;
}
else
{
lean_dec(v_a_827_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_933_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_911_ = lean_string_utf8_next_fast(v_fst_903_, v_snd_904_);
lean_dec(v_snd_904_);
lean_inc(v_fst_903_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v___x_911_);
v___x_913_ = v___x_909_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_fst_903_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_911_);
v___x_913_ = v_reuseFailAlloc_932_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
uint8_t v_decide_914_; 
v_decide_914_ = lean_nat_dec_eq(v___x_911_, v___x_906_);
if (v_decide_914_ == 0)
{
uint32_t v___x_915_; uint32_t v___x_916_; uint8_t v___x_917_; 
v___x_915_ = lean_string_utf8_get_fast(v_fst_903_, v___x_911_);
v___x_916_ = 45;
v___x_917_ = lean_uint32_dec_eq(v___x_915_, v___x_916_);
if (v___x_917_ == 0)
{
uint32_t v___x_918_; uint8_t v___x_919_; 
v___x_918_ = 43;
v___x_919_ = lean_uint32_dec_eq(v___x_915_, v___x_918_);
if (v___x_919_ == 0)
{
v___y_891_ = v___x_913_;
v_fst_892_ = v_fst_903_;
v_snd_893_ = v___x_911_;
goto v___jp_890_;
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; 
lean_dec_ref(v___x_913_);
v___x_920_ = lean_string_utf8_next_fast(v_fst_903_, v___x_911_);
lean_inc(v_fst_903_);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v_fst_903_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___y_891_ = v___x_921_;
v_fst_892_ = v_fst_903_;
v_snd_893_ = v___x_920_;
goto v___jp_890_;
}
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v_decide_924_; 
lean_dec_ref(v___x_913_);
v___x_922_ = lean_string_utf8_next_fast(v_fst_903_, v___x_911_);
lean_inc(v_fst_903_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v_fst_903_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v_decide_924_ = lean_nat_dec_eq(v___x_922_, v___x_906_);
if (v_decide_924_ == 0)
{
if (v___x_917_ == 0)
{
lean_dec(v_fst_903_);
lean_dec_ref(v_value_826_);
v___y_829_ = v___x_923_;
goto v___jp_828_;
}
else
{
uint32_t v___x_925_; uint32_t v___x_926_; uint8_t v___x_927_; 
v___x_925_ = lean_string_utf8_get_fast(v_fst_903_, v___x_922_);
lean_dec(v_fst_903_);
v___x_926_ = 48;
v___x_927_ = lean_uint32_dec_le(v___x_926_, v___x_925_);
if (v___x_927_ == 0)
{
v___y_833_ = v___x_923_;
v___y_834_ = v___x_927_;
goto v___jp_832_;
}
else
{
uint32_t v___x_928_; uint8_t v___x_929_; 
v___x_928_ = 57;
v___x_929_ = lean_uint32_dec_le(v___x_925_, v___x_928_);
v___y_833_ = v___x_923_;
v___y_834_ = v___x_929_;
goto v___jp_832_;
}
}
}
else
{
lean_dec(v_fst_903_);
lean_dec_ref(v_value_826_);
v___y_829_ = v___x_923_;
goto v___jp_828_;
}
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec(v_fst_903_);
lean_dec_ref(v_value_826_);
v___x_930_ = lean_box(0);
v___x_931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_913_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
return v___x_931_;
}
}
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec_ref(v_value_826_);
v___x_936_ = lean_box(0);
v___x_937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_937_, 0, v_a_827_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Json_Parser_num_spec__0(lean_object* v_a_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = lean_nat_to_int(v_a_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_num(lean_object* v_a_949_){
_start:
{
lean_object* v___y_951_; lean_object* v___y_952_; uint8_t v___y_953_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v_fst_986_; lean_object* v_snd_987_; lean_object* v___y_998_; lean_object* v___y_999_; uint8_t v___y_1000_; lean_object* v___y_1025_; lean_object* v___y_1029_; lean_object* v_fst_1030_; lean_object* v_snd_1031_; lean_object* v___y_1032_; lean_object* v___y_1058_; lean_object* v_pos_1059_; lean_object* v_fst_1060_; lean_object* v_snd_1061_; lean_object* v_res_1062_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; uint8_t v___y_1074_; lean_object* v___y_1123_; lean_object* v___y_1127_; lean_object* v_pos_1128_; lean_object* v_fst_1129_; lean_object* v_snd_1130_; lean_object* v_res_1131_; lean_object* v___y_1154_; lean_object* v___y_1155_; uint8_t v___y_1156_; lean_object* v_pos_1175_; lean_object* v_fst_1176_; lean_object* v_snd_1177_; lean_object* v_res_1178_; lean_object* v_fst_1193_; lean_object* v_snd_1194_; lean_object* v___x_1195_; uint8_t v_decide_1196_; 
v_fst_1193_ = lean_ctor_get(v_a_949_, 0);
v_snd_1194_ = lean_ctor_get(v_a_949_, 1);
v___x_1195_ = lean_string_utf8_byte_size(v_fst_1193_);
v_decide_1196_ = lean_nat_dec_eq(v_snd_1194_, v___x_1195_);
if (v_decide_1196_ == 0)
{
uint32_t v___x_1197_; uint32_t v___x_1198_; uint8_t v___x_1199_; 
lean_inc(v_snd_1194_);
lean_inc(v_fst_1193_);
v___x_1197_ = lean_string_utf8_get_fast(v_fst_1193_, v_snd_1194_);
v___x_1198_ = 45;
v___x_1199_ = lean_uint32_dec_eq(v___x_1197_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v_pos_1175_ = v_a_949_;
v_fst_1176_ = v_fst_1193_;
v_snd_1177_ = v_snd_1194_;
v_res_1178_ = v___x_1200_;
goto v___jp_1174_;
}
else
{
lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1209_; 
v_isSharedCheck_1209_ = !lean_is_exclusive(v_a_949_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; lean_object* v_unused_1211_; 
v_unused_1210_ = lean_ctor_get(v_a_949_, 1);
lean_dec(v_unused_1210_);
v_unused_1211_ = lean_ctor_get(v_a_949_, 0);
lean_dec(v_unused_1211_);
v___x_1202_ = v_a_949_;
v_isShared_1203_ = v_isSharedCheck_1209_;
goto v_resetjp_1201_;
}
else
{
lean_dec(v_a_949_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1209_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = lean_string_utf8_next_fast(v_fst_1193_, v_snd_1194_);
lean_dec(v_snd_1194_);
lean_inc(v_fst_1193_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 1, v___x_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_fst_1193_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v_pos_1175_ = v___x_1206_;
v_fst_1176_ = v_fst_1193_;
v_snd_1177_ = v___x_1204_;
v_res_1178_ = v___x_1207_;
goto v___jp_1174_;
}
}
}
}
else
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_box(0);
v___x_1213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1213_, 0, v_a_949_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
return v___x_1213_;
}
v___jp_950_:
{
if (v___y_953_ == 0)
{
lean_object* v___x_954_; lean_object* v___x_955_; 
lean_dec_ref(v___y_952_);
v___x_954_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_955_, 0, v___y_951_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = l_Lean_Json_Parser_natCore(v___x_956_, v___y_951_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_pos_958_; lean_object* v_res_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_973_; 
v_pos_958_ = lean_ctor_get(v___x_957_, 0);
v_res_959_ = lean_ctor_get(v___x_957_, 1);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_973_ == 0)
{
v___x_961_ = v___x_957_;
v_isShared_962_ = v_isSharedCheck_973_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_res_959_);
lean_inc(v_pos_958_);
lean_dec(v___x_957_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_973_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_964_ = lean_nat_dec_lt(v___x_963_, v_res_959_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_965_ = l_Lean_JsonNumber_shiftl(v___y_952_, v_res_959_);
lean_dec(v_res_959_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v___x_965_);
v___x_967_ = v___x_961_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_pos_958_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
else
{
lean_object* v___x_969_; lean_object* v___x_971_; 
lean_dec(v_res_959_);
lean_dec_ref(v___y_952_);
v___x_969_ = ((lean_object*)(l_Lean_Json_Parser_exponent___closed__1));
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 1);
lean_ctor_set(v___x_961_, 1, v___x_969_);
v___x_971_ = v___x_961_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_pos_958_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v_pos_974_; lean_object* v_err_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec_ref(v___y_952_);
v_pos_974_ = lean_ctor_get(v___x_957_, 0);
v_err_975_ = lean_ctor_get(v___x_957_, 1);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_957_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_err_975_);
lean_inc(v_pos_974_);
lean_dec(v___x_957_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_pos_974_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_err_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
v___jp_983_:
{
lean_object* v___x_988_; uint8_t v_decide_989_; 
v___x_988_ = lean_string_utf8_byte_size(v_fst_986_);
v_decide_989_ = lean_nat_dec_eq(v_snd_987_, v___x_988_);
if (v_decide_989_ == 0)
{
uint32_t v___x_990_; uint32_t v___x_991_; uint8_t v___x_992_; 
v___x_990_ = lean_string_utf8_get_fast(v_fst_986_, v_snd_987_);
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
v___x_991_ = 48;
v___x_992_ = lean_uint32_dec_le(v___x_991_, v___x_990_);
if (v___x_992_ == 0)
{
v___y_951_ = v___y_985_;
v___y_952_ = v___y_984_;
v___y_953_ = v___x_992_;
goto v___jp_950_;
}
else
{
uint32_t v___x_993_; uint8_t v___x_994_; 
v___x_993_ = 57;
v___x_994_ = lean_uint32_dec_le(v___x_990_, v___x_993_);
v___y_951_ = v___y_985_;
v___y_952_ = v___y_984_;
v___y_953_ = v___x_994_;
goto v___jp_950_;
}
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; 
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
lean_dec_ref(v___y_984_);
v___x_995_ = lean_box(0);
v___x_996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_996_, 0, v___y_985_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
return v___x_996_;
}
}
v___jp_997_:
{
if (v___y_1000_ == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_dec_ref(v___y_998_);
v___x_1001_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_1002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___y_999_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
return v___x_1002_;
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = l_Lean_Json_Parser_natCore(v___x_1003_, v___y_999_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_pos_1005_; lean_object* v_res_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1014_; 
v_pos_1005_ = lean_ctor_get(v___x_1004_, 0);
v_res_1006_ = lean_ctor_get(v___x_1004_, 1);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1008_ = v___x_1004_;
v_isShared_1009_ = v_isSharedCheck_1014_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_res_1006_);
lean_inc(v_pos_1005_);
lean_dec(v___x_1004_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1014_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = l_Lean_JsonNumber_shiftr(v___y_998_, v_res_1006_);
lean_dec(v_res_1006_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v___x_1010_);
v___x_1012_ = v___x_1008_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_pos_1005_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
else
{
lean_object* v_pos_1015_; lean_object* v_err_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec_ref(v___y_998_);
v_pos_1015_ = lean_ctor_get(v___x_1004_, 0);
v_err_1016_ = lean_ctor_get(v___x_1004_, 1);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1004_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_err_1016_);
lean_inc(v_pos_1015_);
lean_dec(v___x_1004_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_pos_1015_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_err_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
v___jp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___y_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
return v___x_1027_;
}
v___jp_1028_:
{
lean_object* v___x_1033_; uint8_t v_decide_1034_; 
v___x_1033_ = lean_string_utf8_byte_size(v_fst_1030_);
v_decide_1034_ = lean_nat_dec_eq(v_snd_1031_, v___x_1033_);
if (v_decide_1034_ == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1036_; uint8_t v_decide_1037_; 
lean_dec_ref(v___y_1029_);
v___x_1035_ = lean_string_utf8_next_fast(v_fst_1030_, v_snd_1031_);
lean_dec(v_snd_1031_);
lean_inc(v_fst_1030_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v_fst_1030_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v_decide_1037_ = lean_nat_dec_eq(v___x_1035_, v___x_1033_);
if (v_decide_1037_ == 0)
{
uint32_t v___x_1038_; uint32_t v___x_1039_; uint8_t v___x_1040_; 
v___x_1038_ = lean_string_utf8_get_fast(v_fst_1030_, v___x_1035_);
v___x_1039_ = 45;
v___x_1040_ = lean_uint32_dec_eq(v___x_1038_, v___x_1039_);
if (v___x_1040_ == 0)
{
uint32_t v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = 43;
v___x_1042_ = lean_uint32_dec_eq(v___x_1038_, v___x_1041_);
if (v___x_1042_ == 0)
{
v___y_984_ = v___y_1032_;
v___y_985_ = v___x_1036_;
v_fst_986_ = v_fst_1030_;
v_snd_987_ = v___x_1035_;
goto v___jp_983_;
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec_ref_known(v___x_1036_, 2);
v___x_1043_ = lean_string_utf8_next_fast(v_fst_1030_, v___x_1035_);
lean_inc(v_fst_1030_);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v_fst_1030_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___y_984_ = v___y_1032_;
v___y_985_ = v___x_1044_;
v_fst_986_ = v_fst_1030_;
v_snd_987_ = v___x_1043_;
goto v___jp_983_;
}
}
else
{
lean_object* v___x_1045_; lean_object* v___x_1046_; uint8_t v_decide_1047_; 
lean_dec_ref_known(v___x_1036_, 2);
v___x_1045_ = lean_string_utf8_next_fast(v_fst_1030_, v___x_1035_);
lean_inc(v_fst_1030_);
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v_fst_1030_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v_decide_1047_ = lean_nat_dec_eq(v___x_1045_, v___x_1033_);
if (v_decide_1047_ == 0)
{
if (v___x_1040_ == 0)
{
lean_dec_ref(v___y_1032_);
lean_dec(v_fst_1030_);
v___y_1025_ = v___x_1046_;
goto v___jp_1024_;
}
else
{
uint32_t v___x_1048_; uint32_t v___x_1049_; uint8_t v___x_1050_; 
v___x_1048_ = lean_string_utf8_get_fast(v_fst_1030_, v___x_1045_);
lean_dec(v_fst_1030_);
v___x_1049_ = 48;
v___x_1050_ = lean_uint32_dec_le(v___x_1049_, v___x_1048_);
if (v___x_1050_ == 0)
{
v___y_998_ = v___y_1032_;
v___y_999_ = v___x_1046_;
v___y_1000_ = v___x_1050_;
goto v___jp_997_;
}
else
{
uint32_t v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = 57;
v___x_1052_ = lean_uint32_dec_le(v___x_1048_, v___x_1051_);
v___y_998_ = v___y_1032_;
v___y_999_ = v___x_1046_;
v___y_1000_ = v___x_1052_;
goto v___jp_997_;
}
}
}
else
{
lean_dec_ref(v___y_1032_);
lean_dec(v_fst_1030_);
v___y_1025_ = v___x_1046_;
goto v___jp_1024_;
}
}
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec_ref(v___y_1032_);
lean_dec(v_fst_1030_);
v___x_1053_ = lean_box(0);
v___x_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1036_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
return v___x_1054_;
}
}
else
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
lean_dec_ref(v___y_1032_);
lean_dec(v_snd_1031_);
lean_dec(v_fst_1030_);
v___x_1055_ = lean_box(0);
v___x_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___y_1029_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
return v___x_1056_;
}
}
v___jp_1057_:
{
lean_object* v___x_1063_; uint8_t v_decide_1064_; 
v___x_1063_ = lean_string_utf8_byte_size(v_fst_1060_);
v_decide_1064_ = lean_nat_dec_eq(v_snd_1061_, v___x_1063_);
if (v_decide_1064_ == 0)
{
uint32_t v___x_1065_; uint32_t v___x_1066_; uint8_t v___x_1067_; 
v___x_1065_ = lean_string_utf8_get_fast(v_fst_1060_, v_snd_1061_);
v___x_1066_ = 101;
v___x_1067_ = lean_uint32_dec_eq(v___x_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
uint32_t v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = 69;
v___x_1069_ = lean_uint32_dec_eq(v___x_1065_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_dec_ref(v_res_1062_);
lean_dec(v_snd_1061_);
lean_dec(v_fst_1060_);
lean_dec_ref(v_pos_1059_);
return v___y_1058_;
}
else
{
lean_dec_ref(v___y_1058_);
v___y_1029_ = v_pos_1059_;
v_fst_1030_ = v_fst_1060_;
v_snd_1031_ = v_snd_1061_;
v___y_1032_ = v_res_1062_;
goto v___jp_1028_;
}
}
else
{
lean_dec_ref(v___y_1058_);
v___y_1029_ = v_pos_1059_;
v_fst_1030_ = v_fst_1060_;
v_snd_1031_ = v_snd_1061_;
v___y_1032_ = v_res_1062_;
goto v___jp_1028_;
}
}
else
{
lean_dec_ref(v_res_1062_);
lean_dec(v_snd_1061_);
lean_dec(v_fst_1060_);
lean_dec_ref(v_pos_1059_);
return v___y_1058_;
}
}
v___jp_1070_:
{
if (v___y_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec(v___y_1071_);
v___x_1075_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___y_1073_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
return v___x_1076_;
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1078_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_1077_, v___x_1077_, v___y_1073_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_res_1079_; lean_object* v_pos_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1112_; 
v_res_1079_ = lean_ctor_get(v___x_1078_, 1);
v_pos_1080_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1082_ = v___x_1078_;
v_isShared_1083_ = v_isSharedCheck_1112_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_res_1079_);
lean_inc(v_pos_1080_);
lean_dec(v___x_1078_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1112_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v_fst_1084_; lean_object* v_snd_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1111_; 
v_fst_1084_ = lean_ctor_get(v_res_1079_, 0);
v_snd_1085_ = lean_ctor_get(v_res_1079_, 1);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_res_1079_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1087_ = v_res_1079_;
v_isShared_1088_ = v_isSharedCheck_1111_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_snd_1085_);
lean_inc(v_fst_1084_);
lean_dec(v_res_1079_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1111_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1089_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_1090_ = lean_nat_dec_lt(v___x_1089_, v_snd_1085_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v_fst_1093_; lean_object* v_snd_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1091_ = lean_unsigned_to_nat(10u);
v___x_1092_ = lean_nat_pow(v___x_1091_, v_snd_1085_);
v_fst_1093_ = lean_ctor_get(v_pos_1080_, 0);
lean_inc(v_fst_1093_);
v_snd_1094_ = lean_ctor_get(v_pos_1080_, 1);
lean_inc(v_snd_1094_);
v___x_1095_ = lean_nat_to_int(v___y_1071_);
v___x_1096_ = lean_nat_to_int(v___x_1092_);
v___x_1097_ = lean_int_mul(v___x_1095_, v___x_1096_);
lean_dec(v___x_1096_);
lean_dec(v___x_1095_);
v___x_1098_ = lean_nat_to_int(v_fst_1084_);
v___x_1099_ = lean_int_add(v___x_1097_, v___x_1098_);
lean_dec(v___x_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_int_mul(v___y_1072_, v___x_1099_);
lean_dec(v___x_1099_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1100_);
v___x_1102_ = v___x_1087_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_snd_1085_);
v___x_1102_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1104_; 
lean_inc_ref(v___x_1102_);
lean_inc(v_pos_1080_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 1, v___x_1102_);
v___x_1104_ = v___x_1082_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_pos_1080_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
v___y_1058_ = v___x_1104_;
v_pos_1059_ = v_pos_1080_;
v_fst_1060_ = v_fst_1093_;
v_snd_1061_ = v_snd_1094_;
v_res_1062_ = v___x_1102_;
goto v___jp_1057_;
}
}
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
lean_del_object(v___x_1087_);
lean_dec(v_snd_1085_);
lean_dec(v_fst_1084_);
lean_dec(v___y_1071_);
v___x_1107_ = ((lean_object*)(l_Lean_Json_Parser_numWithDecimals___closed__2));
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 1);
lean_ctor_set(v___x_1082_, 1, v___x_1107_);
v___x_1109_ = v___x_1082_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_pos_1080_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
else
{
lean_object* v_pos_1113_; lean_object* v_err_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v___y_1071_);
v_pos_1113_ = lean_ctor_get(v___x_1078_, 0);
v_err_1114_ = lean_ctor_get(v___x_1078_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1078_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_err_1114_);
lean_inc(v_pos_1113_);
lean_dec(v___x_1078_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_pos_1113_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_err_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
v___jp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_box(0);
v___x_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___y_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
return v___x_1125_;
}
v___jp_1126_:
{
lean_object* v___x_1132_; uint8_t v_decide_1133_; 
v___x_1132_ = lean_string_utf8_byte_size(v_fst_1129_);
v_decide_1133_ = lean_nat_dec_eq(v_snd_1130_, v___x_1132_);
if (v_decide_1133_ == 0)
{
uint32_t v___x_1134_; uint32_t v___x_1135_; uint8_t v___x_1136_; 
v___x_1134_ = lean_string_utf8_get_fast(v_fst_1129_, v_snd_1130_);
v___x_1135_ = 46;
v___x_1136_ = lean_uint32_dec_eq(v___x_1134_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1137_ = lean_nat_to_int(v_res_1131_);
v___x_1138_ = lean_int_mul(v___y_1127_, v___x_1137_);
lean_dec(v___x_1137_);
v___x_1139_ = l_Lean_JsonNumber_fromInt(v___x_1138_);
lean_inc_ref(v___x_1139_);
lean_inc_ref(v_pos_1128_);
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v_pos_1128_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___y_1058_ = v___x_1140_;
v_pos_1059_ = v_pos_1128_;
v_fst_1060_ = v_fst_1129_;
v_snd_1061_ = v_snd_1130_;
v_res_1062_ = v___x_1139_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; uint8_t v_decide_1143_; 
lean_dec_ref(v_pos_1128_);
v___x_1141_ = lean_string_utf8_next_fast(v_fst_1129_, v_snd_1130_);
lean_dec(v_snd_1130_);
lean_inc(v_fst_1129_);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v_fst_1129_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v_decide_1143_ = lean_nat_dec_eq(v___x_1141_, v___x_1132_);
if (v_decide_1143_ == 0)
{
if (v___x_1136_ == 0)
{
lean_dec(v_res_1131_);
lean_dec(v_fst_1129_);
v___y_1123_ = v___x_1142_;
goto v___jp_1122_;
}
else
{
uint32_t v___x_1144_; uint32_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1144_ = lean_string_utf8_get_fast(v_fst_1129_, v___x_1141_);
lean_dec(v_fst_1129_);
v___x_1145_ = 48;
v___x_1146_ = lean_uint32_dec_le(v___x_1145_, v___x_1144_);
if (v___x_1146_ == 0)
{
v___y_1071_ = v_res_1131_;
v___y_1072_ = v___y_1127_;
v___y_1073_ = v___x_1142_;
v___y_1074_ = v___x_1146_;
goto v___jp_1070_;
}
else
{
uint32_t v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = 57;
v___x_1148_ = lean_uint32_dec_le(v___x_1144_, v___x_1147_);
v___y_1071_ = v_res_1131_;
v___y_1072_ = v___y_1127_;
v___y_1073_ = v___x_1142_;
v___y_1074_ = v___x_1148_;
goto v___jp_1070_;
}
}
}
else
{
lean_dec(v_res_1131_);
lean_dec(v_fst_1129_);
v___y_1123_ = v___x_1142_;
goto v___jp_1122_;
}
}
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1149_ = lean_nat_to_int(v_res_1131_);
v___x_1150_ = lean_int_mul(v___y_1127_, v___x_1149_);
lean_dec(v___x_1149_);
v___x_1151_ = l_Lean_JsonNumber_fromInt(v___x_1150_);
lean_inc_ref(v___x_1151_);
lean_inc_ref(v_pos_1128_);
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v_pos_1128_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___y_1058_ = v___x_1152_;
v_pos_1059_ = v_pos_1128_;
v_fst_1060_ = v_fst_1129_;
v_snd_1061_ = v_snd_1130_;
v_res_1062_ = v___x_1151_;
goto v___jp_1057_;
}
}
v___jp_1153_:
{
if (v___y_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___y_1155_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
return v___x_1158_;
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_unsigned_to_nat(0u);
v___x_1160_ = l_Lean_Json_Parser_natCore(v___x_1159_, v___y_1155_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_pos_1161_; lean_object* v_res_1162_; lean_object* v_fst_1163_; lean_object* v_snd_1164_; 
v_pos_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_pos_1161_);
v_res_1162_ = lean_ctor_get(v___x_1160_, 1);
lean_inc(v_res_1162_);
lean_dec_ref_known(v___x_1160_, 2);
v_fst_1163_ = lean_ctor_get(v_pos_1161_, 0);
lean_inc(v_fst_1163_);
v_snd_1164_ = lean_ctor_get(v_pos_1161_, 1);
lean_inc(v_snd_1164_);
v___y_1127_ = v___y_1154_;
v_pos_1128_ = v_pos_1161_;
v_fst_1129_ = v_fst_1163_;
v_snd_1130_ = v_snd_1164_;
v_res_1131_ = v_res_1162_;
goto v___jp_1126_;
}
else
{
lean_object* v_pos_1165_; lean_object* v_err_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v_pos_1165_ = lean_ctor_get(v___x_1160_, 0);
v_err_1166_ = lean_ctor_get(v___x_1160_, 1);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1160_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_err_1166_);
lean_inc(v_pos_1165_);
lean_dec(v___x_1160_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_pos_1165_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_err_1166_);
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
v___jp_1174_:
{
lean_object* v___x_1179_; uint8_t v_decide_1180_; 
v___x_1179_ = lean_string_utf8_byte_size(v_fst_1176_);
v_decide_1180_ = lean_nat_dec_eq(v_snd_1177_, v___x_1179_);
if (v_decide_1180_ == 0)
{
uint32_t v___x_1181_; uint32_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1181_ = lean_string_utf8_get_fast(v_fst_1176_, v_snd_1177_);
v___x_1182_ = 48;
v___x_1183_ = lean_uint32_dec_eq(v___x_1181_, v___x_1182_);
if (v___x_1183_ == 0)
{
uint32_t v___x_1184_; uint8_t v___x_1185_; 
lean_dec(v_snd_1177_);
lean_dec(v_fst_1176_);
v___x_1184_ = 49;
v___x_1185_ = lean_uint32_dec_le(v___x_1184_, v___x_1181_);
if (v___x_1185_ == 0)
{
v___y_1154_ = v_res_1178_;
v___y_1155_ = v_pos_1175_;
v___y_1156_ = v___x_1185_;
goto v___jp_1153_;
}
else
{
uint32_t v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = 57;
v___x_1187_ = lean_uint32_dec_le(v___x_1181_, v___x_1186_);
v___y_1154_ = v_res_1178_;
v___y_1155_ = v_pos_1175_;
v___y_1156_ = v___x_1187_;
goto v___jp_1153_;
}
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_dec_ref(v_pos_1175_);
v___x_1188_ = lean_string_utf8_next_fast(v_fst_1176_, v_snd_1177_);
lean_dec(v_snd_1177_);
lean_inc(v_fst_1176_);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v_fst_1176_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = lean_unsigned_to_nat(0u);
v___y_1127_ = v_res_1178_;
v_pos_1128_ = v___x_1189_;
v_fst_1129_ = v_fst_1176_;
v_snd_1130_ = v___x_1188_;
v_res_1131_ = v___x_1190_;
goto v___jp_1126_;
}
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_dec(v_snd_1177_);
lean_dec(v_fst_1176_);
v___x_1191_ = lean_box(0);
v___x_1192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1192_, 0, v_pos_1175_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
return v___x_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(lean_object* v_msg_1214_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_box(1);
v___x_1216_ = lean_panic_fn_borrowed(v___x_1215_, v_msg_1214_);
return v___x_1216_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1220_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2));
v___x_1221_ = lean_unsigned_to_nat(35u);
v___x_1222_ = lean_unsigned_to_nat(182u);
v___x_1223_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1));
v___x_1224_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1225_ = l_mkPanicMessageWithDecl(v___x_1224_, v___x_1223_, v___x_1222_, v___x_1221_, v___x_1220_);
return v___x_1225_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1226_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2));
v___x_1227_ = lean_unsigned_to_nat(21u);
v___x_1228_ = lean_unsigned_to_nat(183u);
v___x_1229_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1));
v___x_1230_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1231_ = l_mkPanicMessageWithDecl(v___x_1230_, v___x_1229_, v___x_1228_, v___x_1227_, v___x_1226_);
return v___x_1231_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1234_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6));
v___x_1235_ = lean_unsigned_to_nat(35u);
v___x_1236_ = lean_unsigned_to_nat(276u);
v___x_1237_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5));
v___x_1238_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1239_ = l_mkPanicMessageWithDecl(v___x_1238_, v___x_1237_, v___x_1236_, v___x_1235_, v___x_1234_);
return v___x_1239_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1240_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6));
v___x_1241_ = lean_unsigned_to_nat(21u);
v___x_1242_ = lean_unsigned_to_nat(277u);
v___x_1243_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5));
v___x_1244_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1245_ = l_mkPanicMessageWithDecl(v___x_1244_, v___x_1243_, v___x_1242_, v___x_1241_, v___x_1240_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(lean_object* v_k_1246_, lean_object* v_v_1247_, lean_object* v_t_1248_){
_start:
{
if (lean_obj_tag(v_t_1248_) == 0)
{
lean_object* v_size_1249_; lean_object* v_k_1250_; lean_object* v_v_1251_; lean_object* v_l_1252_; lean_object* v_r_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1609_; 
v_size_1249_ = lean_ctor_get(v_t_1248_, 0);
v_k_1250_ = lean_ctor_get(v_t_1248_, 1);
v_v_1251_ = lean_ctor_get(v_t_1248_, 2);
v_l_1252_ = lean_ctor_get(v_t_1248_, 3);
v_r_1253_ = lean_ctor_get(v_t_1248_, 4);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_t_1248_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1255_ = v_t_1248_;
v_isShared_1256_ = v_isSharedCheck_1609_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_r_1253_);
lean_inc(v_l_1252_);
lean_inc(v_v_1251_);
lean_inc(v_k_1250_);
lean_inc(v_size_1249_);
lean_dec(v_t_1248_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1609_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
uint8_t v___x_1257_; 
v___x_1257_ = lean_string_compare(v_k_1246_, v_k_1250_);
switch(v___x_1257_)
{
case 0:
{
lean_object* v___x_1258_; 
lean_dec(v_size_1249_);
v___x_1258_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_1246_, v_v_1247_, v_l_1252_);
if (lean_obj_tag(v_r_1253_) == 0)
{
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_size_1259_; lean_object* v_size_1260_; lean_object* v_k_1261_; lean_object* v_v_1262_; lean_object* v_l_1263_; lean_object* v_r_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v_size_1259_ = lean_ctor_get(v_r_1253_, 0);
v_size_1260_ = lean_ctor_get(v___x_1258_, 0);
v_k_1261_ = lean_ctor_get(v___x_1258_, 1);
v_v_1262_ = lean_ctor_get(v___x_1258_, 2);
v_l_1263_ = lean_ctor_get(v___x_1258_, 3);
v_r_1264_ = lean_ctor_get(v___x_1258_, 4);
lean_inc(v_r_1264_);
v___x_1265_ = lean_unsigned_to_nat(3u);
v___x_1266_ = lean_nat_mul(v___x_1265_, v_size_1259_);
v___x_1267_ = lean_nat_dec_lt(v___x_1266_, v_size_1260_);
lean_dec(v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1272_; 
lean_dec(v_r_1264_);
v___x_1268_ = lean_unsigned_to_nat(1u);
v___x_1269_ = lean_nat_add(v___x_1268_, v_size_1260_);
v___x_1270_ = lean_nat_add(v___x_1269_, v_size_1259_);
lean_dec(v___x_1269_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 3, v___x_1258_);
lean_ctor_set(v___x_1255_, 0, v___x_1270_);
v___x_1272_ = v___x_1255_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1273_, 4, v_r_1253_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
else
{
lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1345_; 
lean_inc(v_l_1263_);
lean_inc(v_v_1262_);
lean_inc(v_k_1261_);
lean_inc(v_size_1260_);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1345_ == 0)
{
lean_object* v_unused_1346_; lean_object* v_unused_1347_; lean_object* v_unused_1348_; lean_object* v_unused_1349_; lean_object* v_unused_1350_; 
v_unused_1346_ = lean_ctor_get(v___x_1258_, 4);
lean_dec(v_unused_1346_);
v_unused_1347_ = lean_ctor_get(v___x_1258_, 3);
lean_dec(v_unused_1347_);
v_unused_1348_ = lean_ctor_get(v___x_1258_, 2);
lean_dec(v_unused_1348_);
v_unused_1349_ = lean_ctor_get(v___x_1258_, 1);
lean_dec(v_unused_1349_);
v_unused_1350_ = lean_ctor_get(v___x_1258_, 0);
lean_dec(v_unused_1350_);
v___x_1275_ = v___x_1258_;
v_isShared_1276_ = v_isSharedCheck_1345_;
goto v_resetjp_1274_;
}
else
{
lean_dec(v___x_1258_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1345_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
if (lean_obj_tag(v_l_1263_) == 0)
{
if (lean_obj_tag(v_r_1264_) == 0)
{
lean_object* v_size_1277_; lean_object* v_size_1278_; lean_object* v_k_1279_; lean_object* v_v_1280_; lean_object* v_l_1281_; lean_object* v_r_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_size_1277_ = lean_ctor_get(v_l_1263_, 0);
v_size_1278_ = lean_ctor_get(v_r_1264_, 0);
v_k_1279_ = lean_ctor_get(v_r_1264_, 1);
v_v_1280_ = lean_ctor_get(v_r_1264_, 2);
v_l_1281_ = lean_ctor_get(v_r_1264_, 3);
v_r_1282_ = lean_ctor_get(v_r_1264_, 4);
v___x_1283_ = lean_unsigned_to_nat(2u);
v___x_1284_ = lean_nat_mul(v___x_1283_, v_size_1277_);
v___x_1285_ = lean_nat_dec_lt(v_size_1278_, v___x_1284_);
lean_dec(v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1315_; 
lean_inc(v_r_1282_);
lean_inc(v_l_1281_);
lean_inc(v_v_1280_);
lean_inc(v_k_1279_);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_r_1264_);
if (v_isSharedCheck_1315_ == 0)
{
lean_object* v_unused_1316_; lean_object* v_unused_1317_; lean_object* v_unused_1318_; lean_object* v_unused_1319_; lean_object* v_unused_1320_; 
v_unused_1316_ = lean_ctor_get(v_r_1264_, 4);
lean_dec(v_unused_1316_);
v_unused_1317_ = lean_ctor_get(v_r_1264_, 3);
lean_dec(v_unused_1317_);
v_unused_1318_ = lean_ctor_get(v_r_1264_, 2);
lean_dec(v_unused_1318_);
v_unused_1319_ = lean_ctor_get(v_r_1264_, 1);
lean_dec(v_unused_1319_);
v_unused_1320_ = lean_ctor_get(v_r_1264_, 0);
lean_dec(v_unused_1320_);
v___x_1287_ = v_r_1264_;
v_isShared_1288_ = v_isSharedCheck_1315_;
goto v_resetjp_1286_;
}
else
{
lean_dec(v_r_1264_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1315_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___x_1303_; lean_object* v___y_1305_; 
v___x_1289_ = lean_unsigned_to_nat(1u);
v___x_1290_ = lean_nat_add(v___x_1289_, v_size_1260_);
lean_dec(v_size_1260_);
v___x_1291_ = lean_nat_add(v___x_1290_, v_size_1259_);
lean_dec(v___x_1290_);
v___x_1303_ = lean_nat_add(v___x_1289_, v_size_1277_);
if (lean_obj_tag(v_l_1281_) == 0)
{
lean_object* v_size_1313_; 
v_size_1313_ = lean_ctor_get(v_l_1281_, 0);
lean_inc(v_size_1313_);
v___y_1305_ = v_size_1313_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_unsigned_to_nat(0u);
v___y_1305_ = v___x_1314_;
goto v___jp_1304_;
}
v___jp_1292_:
{
lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1296_ = lean_nat_add(v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec(v___y_1294_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v_r_1253_);
lean_ctor_set(v___x_1287_, 3, v_r_1282_);
lean_ctor_set(v___x_1287_, 2, v_v_1251_);
lean_ctor_set(v___x_1287_, 1, v_k_1250_);
lean_ctor_set(v___x_1287_, 0, v___x_1296_);
v___x_1298_ = v___x_1287_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1302_, 3, v_r_1282_);
lean_ctor_set(v_reuseFailAlloc_1302_, 4, v_r_1253_);
v___x_1298_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1300_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 4, v___x_1298_);
lean_ctor_set(v___x_1275_, 3, v___y_1293_);
lean_ctor_set(v___x_1275_, 2, v_v_1280_);
lean_ctor_set(v___x_1275_, 1, v_k_1279_);
lean_ctor_set(v___x_1275_, 0, v___x_1291_);
v___x_1300_ = v___x_1275_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_k_1279_);
lean_ctor_set(v_reuseFailAlloc_1301_, 2, v_v_1280_);
lean_ctor_set(v_reuseFailAlloc_1301_, 3, v___y_1293_);
lean_ctor_set(v_reuseFailAlloc_1301_, 4, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
v___jp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1306_ = lean_nat_add(v___x_1303_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec(v___x_1303_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v_l_1281_);
lean_ctor_set(v___x_1255_, 3, v_l_1263_);
lean_ctor_set(v___x_1255_, 2, v_v_1262_);
lean_ctor_set(v___x_1255_, 1, v_k_1261_);
lean_ctor_set(v___x_1255_, 0, v___x_1306_);
v___x_1308_ = v___x_1255_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_k_1261_);
lean_ctor_set(v_reuseFailAlloc_1312_, 2, v_v_1262_);
lean_ctor_set(v_reuseFailAlloc_1312_, 3, v_l_1263_);
lean_ctor_set(v_reuseFailAlloc_1312_, 4, v_l_1281_);
v___x_1308_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_nat_add(v___x_1289_, v_size_1259_);
if (lean_obj_tag(v_r_1282_) == 0)
{
lean_object* v_size_1310_; 
v_size_1310_ = lean_ctor_get(v_r_1282_, 0);
lean_inc(v_size_1310_);
v___y_1293_ = v___x_1308_;
v___y_1294_ = v___x_1309_;
v___y_1295_ = v_size_1310_;
goto v___jp_1292_;
}
else
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_unsigned_to_nat(0u);
v___y_1293_ = v___x_1308_;
v___y_1294_ = v___x_1309_;
v___y_1295_ = v___x_1311_;
goto v___jp_1292_;
}
}
}
}
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
lean_del_object(v___x_1255_);
v___x_1321_ = lean_unsigned_to_nat(1u);
v___x_1322_ = lean_nat_add(v___x_1321_, v_size_1260_);
lean_dec(v_size_1260_);
v___x_1323_ = lean_nat_add(v___x_1322_, v_size_1259_);
lean_dec(v___x_1322_);
v___x_1324_ = lean_nat_add(v___x_1321_, v_size_1259_);
v___x_1325_ = lean_nat_add(v___x_1324_, v_size_1278_);
lean_dec(v___x_1324_);
lean_inc_ref(v_r_1253_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 4, v_r_1253_);
lean_ctor_set(v___x_1275_, 3, v_r_1264_);
lean_ctor_set(v___x_1275_, 2, v_v_1251_);
lean_ctor_set(v___x_1275_, 1, v_k_1250_);
lean_ctor_set(v___x_1275_, 0, v___x_1325_);
v___x_1327_ = v___x_1275_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v_r_1264_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v_r_1253_);
v___x_1327_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
v_isSharedCheck_1334_ = !lean_is_exclusive(v_r_1253_);
if (v_isSharedCheck_1334_ == 0)
{
lean_object* v_unused_1335_; lean_object* v_unused_1336_; lean_object* v_unused_1337_; lean_object* v_unused_1338_; lean_object* v_unused_1339_; 
v_unused_1335_ = lean_ctor_get(v_r_1253_, 4);
lean_dec(v_unused_1335_);
v_unused_1336_ = lean_ctor_get(v_r_1253_, 3);
lean_dec(v_unused_1336_);
v_unused_1337_ = lean_ctor_get(v_r_1253_, 2);
lean_dec(v_unused_1337_);
v_unused_1338_ = lean_ctor_get(v_r_1253_, 1);
lean_dec(v_unused_1338_);
v_unused_1339_ = lean_ctor_get(v_r_1253_, 0);
lean_dec(v_unused_1339_);
v___x_1329_ = v_r_1253_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_dec(v_r_1253_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 4, v___x_1327_);
lean_ctor_set(v___x_1329_, 3, v_l_1263_);
lean_ctor_set(v___x_1329_, 2, v_v_1262_);
lean_ctor_set(v___x_1329_, 1, v_k_1261_);
lean_ctor_set(v___x_1329_, 0, v___x_1323_);
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_k_1261_);
lean_ctor_set(v_reuseFailAlloc_1333_, 2, v_v_1262_);
lean_ctor_set(v_reuseFailAlloc_1333_, 3, v_l_1263_);
lean_ctor_set(v_reuseFailAlloc_1333_, 4, v___x_1327_);
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
lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec_ref_known(v_l_1263_, 5);
lean_del_object(v___x_1275_);
lean_dec(v_v_1262_);
lean_dec(v_k_1261_);
lean_dec(v_size_1260_);
lean_dec_ref_known(v_r_1253_, 5);
lean_del_object(v___x_1255_);
lean_dec(v_v_1251_);
lean_dec(v_k_1250_);
v___x_1341_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3);
v___x_1342_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1341_);
return v___x_1342_;
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_del_object(v___x_1275_);
lean_dec(v_r_1264_);
lean_dec(v_v_1262_);
lean_dec(v_k_1261_);
lean_dec(v_size_1260_);
lean_dec_ref_known(v_r_1253_, 5);
lean_del_object(v___x_1255_);
lean_dec(v_v_1251_);
lean_dec(v_k_1250_);
v___x_1343_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4);
v___x_1344_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1343_);
return v___x_1344_;
}
}
}
}
else
{
lean_object* v_size_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v_size_1351_ = lean_ctor_get(v_r_1253_, 0);
v___x_1352_ = lean_unsigned_to_nat(1u);
v___x_1353_ = lean_nat_add(v___x_1352_, v_size_1351_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 3, v___x_1258_);
lean_ctor_set(v___x_1255_, 0, v___x_1353_);
v___x_1355_ = v___x_1255_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1356_, 4, v_r_1253_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
else
{
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_l_1357_; 
v_l_1357_ = lean_ctor_get(v___x_1258_, 3);
if (lean_obj_tag(v_l_1357_) == 0)
{
lean_object* v_r_1358_; 
lean_inc_ref(v_l_1357_);
v_r_1358_ = lean_ctor_get(v___x_1258_, 4);
lean_inc(v_r_1358_);
if (lean_obj_tag(v_r_1358_) == 0)
{
lean_object* v_size_1359_; lean_object* v_k_1360_; lean_object* v_v_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1375_; 
v_size_1359_ = lean_ctor_get(v___x_1258_, 0);
v_k_1360_ = lean_ctor_get(v___x_1258_, 1);
v_v_1361_ = lean_ctor_get(v___x_1258_, 2);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; lean_object* v_unused_1377_; 
v_unused_1376_ = lean_ctor_get(v___x_1258_, 4);
lean_dec(v_unused_1376_);
v_unused_1377_ = lean_ctor_get(v___x_1258_, 3);
lean_dec(v_unused_1377_);
v___x_1363_ = v___x_1258_;
v_isShared_1364_ = v_isSharedCheck_1375_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_v_1361_);
lean_inc(v_k_1360_);
lean_inc(v_size_1359_);
lean_dec(v___x_1258_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1375_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v_size_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v_size_1365_ = lean_ctor_get(v_r_1358_, 0);
v___x_1366_ = lean_unsigned_to_nat(1u);
v___x_1367_ = lean_nat_add(v___x_1366_, v_size_1359_);
lean_dec(v_size_1359_);
v___x_1368_ = lean_nat_add(v___x_1366_, v_size_1365_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 4, v_r_1253_);
lean_ctor_set(v___x_1363_, 3, v_r_1358_);
lean_ctor_set(v___x_1363_, 2, v_v_1251_);
lean_ctor_set(v___x_1363_, 1, v_k_1250_);
lean_ctor_set(v___x_1363_, 0, v___x_1368_);
v___x_1370_ = v___x_1363_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v_r_1358_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v_r_1253_);
v___x_1370_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1372_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v___x_1370_);
lean_ctor_set(v___x_1255_, 3, v_l_1357_);
lean_ctor_set(v___x_1255_, 2, v_v_1361_);
lean_ctor_set(v___x_1255_, 1, v_k_1360_);
lean_ctor_set(v___x_1255_, 0, v___x_1367_);
v___x_1372_ = v___x_1255_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_k_1360_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_v_1361_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_l_1357_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
else
{
lean_object* v_k_1378_; lean_object* v_v_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1391_; 
v_k_1378_ = lean_ctor_get(v___x_1258_, 1);
v_v_1379_ = lean_ctor_get(v___x_1258_, 2);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1391_ == 0)
{
lean_object* v_unused_1392_; lean_object* v_unused_1393_; lean_object* v_unused_1394_; 
v_unused_1392_ = lean_ctor_get(v___x_1258_, 4);
lean_dec(v_unused_1392_);
v_unused_1393_ = lean_ctor_get(v___x_1258_, 3);
lean_dec(v_unused_1393_);
v_unused_1394_ = lean_ctor_get(v___x_1258_, 0);
lean_dec(v_unused_1394_);
v___x_1381_ = v___x_1258_;
v_isShared_1382_ = v_isSharedCheck_1391_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_v_1379_);
lean_inc(v_k_1378_);
lean_dec(v___x_1258_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1391_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1383_ = lean_unsigned_to_nat(3u);
v___x_1384_ = lean_unsigned_to_nat(1u);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 3, v_r_1358_);
lean_ctor_set(v___x_1381_, 2, v_v_1251_);
lean_ctor_set(v___x_1381_, 1, v_k_1250_);
lean_ctor_set(v___x_1381_, 0, v___x_1384_);
v___x_1386_ = v___x_1381_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_r_1358_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_r_1358_);
v___x_1386_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1388_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v___x_1386_);
lean_ctor_set(v___x_1255_, 3, v_l_1357_);
lean_ctor_set(v___x_1255_, 2, v_v_1379_);
lean_ctor_set(v___x_1255_, 1, v_k_1378_);
lean_ctor_set(v___x_1255_, 0, v___x_1383_);
v___x_1388_ = v___x_1255_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1389_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1389_, 3, v_l_1357_);
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
else
{
lean_object* v_r_1395_; 
v_r_1395_ = lean_ctor_get(v___x_1258_, 4);
lean_inc(v_r_1395_);
if (lean_obj_tag(v_r_1395_) == 0)
{
lean_object* v_k_1396_; lean_object* v_v_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1421_; 
lean_inc(v_l_1357_);
v_k_1396_ = lean_ctor_get(v___x_1258_, 1);
v_v_1397_ = lean_ctor_get(v___x_1258_, 2);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; lean_object* v_unused_1423_; lean_object* v_unused_1424_; 
v_unused_1422_ = lean_ctor_get(v___x_1258_, 4);
lean_dec(v_unused_1422_);
v_unused_1423_ = lean_ctor_get(v___x_1258_, 3);
lean_dec(v_unused_1423_);
v_unused_1424_ = lean_ctor_get(v___x_1258_, 0);
lean_dec(v_unused_1424_);
v___x_1399_ = v___x_1258_;
v_isShared_1400_ = v_isSharedCheck_1421_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_v_1397_);
lean_inc(v_k_1396_);
lean_dec(v___x_1258_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1421_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v_k_1401_; lean_object* v_v_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1417_; 
v_k_1401_ = lean_ctor_get(v_r_1395_, 1);
v_v_1402_ = lean_ctor_get(v_r_1395_, 2);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_r_1395_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; lean_object* v_unused_1419_; lean_object* v_unused_1420_; 
v_unused_1418_ = lean_ctor_get(v_r_1395_, 4);
lean_dec(v_unused_1418_);
v_unused_1419_ = lean_ctor_get(v_r_1395_, 3);
lean_dec(v_unused_1419_);
v_unused_1420_ = lean_ctor_get(v_r_1395_, 0);
lean_dec(v_unused_1420_);
v___x_1404_ = v_r_1395_;
v_isShared_1405_ = v_isSharedCheck_1417_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_v_1402_);
lean_inc(v_k_1401_);
lean_dec(v_r_1395_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1417_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1406_ = lean_unsigned_to_nat(3u);
v___x_1407_ = lean_unsigned_to_nat(1u);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v_l_1357_);
lean_ctor_set(v___x_1404_, 3, v_l_1357_);
lean_ctor_set(v___x_1404_, 2, v_v_1397_);
lean_ctor_set(v___x_1404_, 1, v_k_1396_);
lean_ctor_set(v___x_1404_, 0, v___x_1407_);
v___x_1409_ = v___x_1404_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_k_1396_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_v_1397_);
lean_ctor_set(v_reuseFailAlloc_1416_, 3, v_l_1357_);
lean_ctor_set(v_reuseFailAlloc_1416_, 4, v_l_1357_);
v___x_1409_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1411_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 4, v_l_1357_);
lean_ctor_set(v___x_1399_, 2, v_v_1251_);
lean_ctor_set(v___x_1399_, 1, v_k_1250_);
lean_ctor_set(v___x_1399_, 0, v___x_1407_);
v___x_1411_ = v___x_1399_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v_l_1357_);
lean_ctor_set(v_reuseFailAlloc_1415_, 4, v_l_1357_);
v___x_1411_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1413_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v___x_1411_);
lean_ctor_set(v___x_1255_, 3, v___x_1409_);
lean_ctor_set(v___x_1255_, 2, v_v_1402_);
lean_ctor_set(v___x_1255_, 1, v_k_1401_);
lean_ctor_set(v___x_1255_, 0, v___x_1406_);
v___x_1413_ = v___x_1255_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_k_1401_);
lean_ctor_set(v_reuseFailAlloc_1414_, 2, v_v_1402_);
lean_ctor_set(v_reuseFailAlloc_1414_, 3, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1414_, 4, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1425_ = lean_unsigned_to_nat(2u);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v_r_1395_);
lean_ctor_set(v___x_1255_, 3, v___x_1258_);
lean_ctor_set(v___x_1255_, 0, v___x_1425_);
v___x_1427_ = v___x_1255_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1428_, 3, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1428_, 4, v_r_1395_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1429_ = lean_unsigned_to_nat(1u);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v___x_1258_);
lean_ctor_set(v___x_1255_, 3, v___x_1258_);
lean_ctor_set(v___x_1255_, 0, v___x_1429_);
v___x_1431_ = v___x_1255_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1432_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1432_, 3, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1432_, 4, v___x_1258_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
case 1:
{
lean_object* v___x_1434_; 
lean_dec(v_v_1251_);
lean_dec(v_k_1250_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 2, v_v_1247_);
lean_ctor_set(v___x_1255_, 1, v_k_1246_);
v___x_1434_ = v___x_1255_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_size_1249_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_k_1246_);
lean_ctor_set(v_reuseFailAlloc_1435_, 2, v_v_1247_);
lean_ctor_set(v_reuseFailAlloc_1435_, 3, v_l_1252_);
lean_ctor_set(v_reuseFailAlloc_1435_, 4, v_r_1253_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
default: 
{
lean_object* v___x_1436_; 
lean_dec(v_size_1249_);
v___x_1436_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_1246_, v_v_1247_, v_r_1253_);
if (lean_obj_tag(v_l_1252_) == 0)
{
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_size_1437_; lean_object* v_size_1438_; lean_object* v_k_1439_; lean_object* v_v_1440_; lean_object* v_l_1441_; lean_object* v_r_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v_size_1437_ = lean_ctor_get(v_l_1252_, 0);
v_size_1438_ = lean_ctor_get(v___x_1436_, 0);
v_k_1439_ = lean_ctor_get(v___x_1436_, 1);
v_v_1440_ = lean_ctor_get(v___x_1436_, 2);
v_l_1441_ = lean_ctor_get(v___x_1436_, 3);
lean_inc(v_l_1441_);
v_r_1442_ = lean_ctor_get(v___x_1436_, 4);
v___x_1443_ = lean_unsigned_to_nat(3u);
v___x_1444_ = lean_nat_mul(v___x_1443_, v_size_1437_);
v___x_1445_ = lean_nat_dec_lt(v___x_1444_, v_size_1438_);
lean_dec(v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
lean_dec(v_l_1441_);
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_add(v___x_1446_, v_size_1437_);
v___x_1448_ = lean_nat_add(v___x_1447_, v_size_1438_);
lean_dec(v___x_1447_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v___x_1436_);
lean_ctor_set(v___x_1255_, 0, v___x_1448_);
v___x_1450_ = v___x_1255_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1451_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1451_, 3, v_l_1252_);
lean_ctor_set(v_reuseFailAlloc_1451_, 4, v___x_1436_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
else
{
lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1521_; 
lean_inc(v_r_1442_);
lean_inc(v_v_1440_);
lean_inc(v_k_1439_);
lean_inc(v_size_1438_);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; lean_object* v_unused_1523_; lean_object* v_unused_1524_; lean_object* v_unused_1525_; lean_object* v_unused_1526_; 
v_unused_1522_ = lean_ctor_get(v___x_1436_, 4);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v___x_1436_, 3);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v___x_1436_, 2);
lean_dec(v_unused_1524_);
v_unused_1525_ = lean_ctor_get(v___x_1436_, 1);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v___x_1436_, 0);
lean_dec(v_unused_1526_);
v___x_1453_ = v___x_1436_;
v_isShared_1454_ = v_isSharedCheck_1521_;
goto v_resetjp_1452_;
}
else
{
lean_dec(v___x_1436_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1521_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
if (lean_obj_tag(v_l_1441_) == 0)
{
if (lean_obj_tag(v_r_1442_) == 0)
{
lean_object* v_size_1455_; lean_object* v_k_1456_; lean_object* v_v_1457_; lean_object* v_l_1458_; lean_object* v_r_1459_; lean_object* v_size_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v_size_1455_ = lean_ctor_get(v_l_1441_, 0);
v_k_1456_ = lean_ctor_get(v_l_1441_, 1);
v_v_1457_ = lean_ctor_get(v_l_1441_, 2);
v_l_1458_ = lean_ctor_get(v_l_1441_, 3);
v_r_1459_ = lean_ctor_get(v_l_1441_, 4);
v_size_1460_ = lean_ctor_get(v_r_1442_, 0);
v___x_1461_ = lean_unsigned_to_nat(2u);
v___x_1462_ = lean_nat_mul(v___x_1461_, v_size_1460_);
v___x_1463_ = lean_nat_dec_lt(v_size_1455_, v___x_1462_);
lean_dec(v___x_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1492_; 
lean_inc(v_r_1459_);
lean_inc(v_l_1458_);
lean_inc(v_v_1457_);
lean_inc(v_k_1456_);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_l_1441_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; lean_object* v_unused_1494_; lean_object* v_unused_1495_; lean_object* v_unused_1496_; lean_object* v_unused_1497_; 
v_unused_1493_ = lean_ctor_get(v_l_1441_, 4);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_l_1441_, 3);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_l_1441_, 2);
lean_dec(v_unused_1495_);
v_unused_1496_ = lean_ctor_get(v_l_1441_, 1);
lean_dec(v_unused_1496_);
v_unused_1497_ = lean_ctor_get(v_l_1441_, 0);
lean_dec(v_unused_1497_);
v___x_1465_ = v_l_1441_;
v_isShared_1466_ = v_isSharedCheck_1492_;
goto v_resetjp_1464_;
}
else
{
lean_dec(v_l_1441_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1492_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1482_; 
v___x_1467_ = lean_unsigned_to_nat(1u);
v___x_1468_ = lean_nat_add(v___x_1467_, v_size_1437_);
v___x_1469_ = lean_nat_add(v___x_1468_, v_size_1438_);
lean_dec(v_size_1438_);
if (lean_obj_tag(v_l_1458_) == 0)
{
lean_object* v_size_1490_; 
v_size_1490_ = lean_ctor_get(v_l_1458_, 0);
lean_inc(v_size_1490_);
v___y_1482_ = v_size_1490_;
goto v___jp_1481_;
}
else
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_unsigned_to_nat(0u);
v___y_1482_ = v___x_1491_;
goto v___jp_1481_;
}
v___jp_1470_:
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1474_ = lean_nat_add(v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec(v___y_1472_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 4, v_r_1442_);
lean_ctor_set(v___x_1465_, 3, v_r_1459_);
lean_ctor_set(v___x_1465_, 2, v_v_1440_);
lean_ctor_set(v___x_1465_, 1, v_k_1439_);
lean_ctor_set(v___x_1465_, 0, v___x_1474_);
v___x_1476_ = v___x_1465_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_k_1439_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_v_1440_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_r_1459_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_r_1442_);
v___x_1476_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1478_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 4, v___x_1476_);
lean_ctor_set(v___x_1453_, 3, v___y_1471_);
lean_ctor_set(v___x_1453_, 2, v_v_1457_);
lean_ctor_set(v___x_1453_, 1, v_k_1456_);
lean_ctor_set(v___x_1453_, 0, v___x_1469_);
v___x_1478_ = v___x_1453_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_k_1456_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_v_1457_);
lean_ctor_set(v_reuseFailAlloc_1479_, 3, v___y_1471_);
lean_ctor_set(v_reuseFailAlloc_1479_, 4, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
v___jp_1481_:
{
lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1483_ = lean_nat_add(v___x_1468_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec(v___x_1468_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v_l_1458_);
lean_ctor_set(v___x_1255_, 0, v___x_1483_);
v___x_1485_ = v___x_1255_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v_l_1252_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v_l_1458_);
v___x_1485_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_nat_add(v___x_1467_, v_size_1460_);
if (lean_obj_tag(v_r_1459_) == 0)
{
lean_object* v_size_1487_; 
v_size_1487_ = lean_ctor_get(v_r_1459_, 0);
lean_inc(v_size_1487_);
v___y_1471_ = v___x_1485_;
v___y_1472_ = v___x_1486_;
v___y_1473_ = v_size_1487_;
goto v___jp_1470_;
}
else
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_unsigned_to_nat(0u);
v___y_1471_ = v___x_1485_;
v___y_1472_ = v___x_1486_;
v___y_1473_ = v___x_1488_;
goto v___jp_1470_;
}
}
}
}
}
else
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
lean_del_object(v___x_1255_);
v___x_1498_ = lean_unsigned_to_nat(1u);
v___x_1499_ = lean_nat_add(v___x_1498_, v_size_1437_);
v___x_1500_ = lean_nat_add(v___x_1499_, v_size_1438_);
lean_dec(v_size_1438_);
v___x_1501_ = lean_nat_add(v___x_1499_, v_size_1455_);
lean_dec(v___x_1499_);
lean_inc_ref(v_l_1252_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 4, v_l_1441_);
lean_ctor_set(v___x_1453_, 3, v_l_1252_);
lean_ctor_set(v___x_1453_, 2, v_v_1251_);
lean_ctor_set(v___x_1453_, 1, v_k_1250_);
lean_ctor_set(v___x_1453_, 0, v___x_1501_);
v___x_1503_ = v___x_1453_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v_l_1252_);
lean_ctor_set(v_reuseFailAlloc_1516_, 4, v_l_1441_);
v___x_1503_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
v_isSharedCheck_1510_ = !lean_is_exclusive(v_l_1252_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; lean_object* v_unused_1512_; lean_object* v_unused_1513_; lean_object* v_unused_1514_; lean_object* v_unused_1515_; 
v_unused_1511_ = lean_ctor_get(v_l_1252_, 4);
lean_dec(v_unused_1511_);
v_unused_1512_ = lean_ctor_get(v_l_1252_, 3);
lean_dec(v_unused_1512_);
v_unused_1513_ = lean_ctor_get(v_l_1252_, 2);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v_l_1252_, 1);
lean_dec(v_unused_1514_);
v_unused_1515_ = lean_ctor_get(v_l_1252_, 0);
lean_dec(v_unused_1515_);
v___x_1505_ = v_l_1252_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_dec(v_l_1252_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 4, v_r_1442_);
lean_ctor_set(v___x_1505_, 3, v___x_1503_);
lean_ctor_set(v___x_1505_, 2, v_v_1440_);
lean_ctor_set(v___x_1505_, 1, v_k_1439_);
lean_ctor_set(v___x_1505_, 0, v___x_1500_);
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_k_1439_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_v_1440_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_r_1442_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
else
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_dec_ref_known(v_l_1441_, 5);
lean_del_object(v___x_1453_);
lean_dec(v_v_1440_);
lean_dec(v_k_1439_);
lean_dec(v_size_1438_);
lean_dec_ref_known(v_l_1252_, 5);
lean_del_object(v___x_1255_);
lean_dec(v_v_1251_);
lean_dec(v_k_1250_);
v___x_1517_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7);
v___x_1518_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1517_);
return v___x_1518_;
}
}
else
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_del_object(v___x_1453_);
lean_dec(v_r_1442_);
lean_dec(v_v_1440_);
lean_dec(v_k_1439_);
lean_dec(v_size_1438_);
lean_dec_ref_known(v_l_1252_, 5);
lean_del_object(v___x_1255_);
lean_dec(v_v_1251_);
lean_dec(v_k_1250_);
v___x_1519_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8);
v___x_1520_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1519_);
return v___x_1520_;
}
}
}
}
else
{
lean_object* v_size_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v_size_1527_ = lean_ctor_get(v_l_1252_, 0);
v___x_1528_ = lean_unsigned_to_nat(1u);
v___x_1529_ = lean_nat_add(v___x_1528_, v_size_1527_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v___x_1436_);
lean_ctor_set(v___x_1255_, 0, v___x_1529_);
v___x_1531_ = v___x_1255_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1532_, 3, v_l_1252_);
lean_ctor_set(v_reuseFailAlloc_1532_, 4, v___x_1436_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
else
{
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_l_1533_; 
v_l_1533_ = lean_ctor_get(v___x_1436_, 3);
lean_inc(v_l_1533_);
if (lean_obj_tag(v_l_1533_) == 0)
{
lean_object* v_r_1534_; 
v_r_1534_ = lean_ctor_get(v___x_1436_, 4);
lean_inc(v_r_1534_);
if (lean_obj_tag(v_r_1534_) == 0)
{
lean_object* v_size_1535_; lean_object* v_k_1536_; lean_object* v_v_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1551_; 
v_size_1535_ = lean_ctor_get(v___x_1436_, 0);
v_k_1536_ = lean_ctor_get(v___x_1436_, 1);
v_v_1537_ = lean_ctor_get(v___x_1436_, 2);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; lean_object* v_unused_1553_; 
v_unused_1552_ = lean_ctor_get(v___x_1436_, 4);
lean_dec(v_unused_1552_);
v_unused_1553_ = lean_ctor_get(v___x_1436_, 3);
lean_dec(v_unused_1553_);
v___x_1539_ = v___x_1436_;
v_isShared_1540_ = v_isSharedCheck_1551_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_v_1537_);
lean_inc(v_k_1536_);
lean_inc(v_size_1535_);
lean_dec(v___x_1436_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1551_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v_size_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1546_; 
v_size_1541_ = lean_ctor_get(v_l_1533_, 0);
v___x_1542_ = lean_unsigned_to_nat(1u);
v___x_1543_ = lean_nat_add(v___x_1542_, v_size_1535_);
lean_dec(v_size_1535_);
v___x_1544_ = lean_nat_add(v___x_1542_, v_size_1541_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 4, v_l_1533_);
lean_ctor_set(v___x_1539_, 3, v_l_1252_);
lean_ctor_set(v___x_1539_, 2, v_v_1251_);
lean_ctor_set(v___x_1539_, 1, v_k_1250_);
lean_ctor_set(v___x_1539_, 0, v___x_1544_);
v___x_1546_ = v___x_1539_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1550_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1550_, 3, v_l_1252_);
lean_ctor_set(v_reuseFailAlloc_1550_, 4, v_l_1533_);
v___x_1546_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1548_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v_r_1534_);
lean_ctor_set(v___x_1255_, 3, v___x_1546_);
lean_ctor_set(v___x_1255_, 2, v_v_1537_);
lean_ctor_set(v___x_1255_, 1, v_k_1536_);
lean_ctor_set(v___x_1255_, 0, v___x_1543_);
v___x_1548_ = v___x_1255_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v_r_1534_);
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
else
{
lean_object* v_k_1554_; lean_object* v_v_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1579_; 
v_k_1554_ = lean_ctor_get(v___x_1436_, 1);
v_v_1555_ = lean_ctor_get(v___x_1436_, 2);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; lean_object* v_unused_1581_; lean_object* v_unused_1582_; 
v_unused_1580_ = lean_ctor_get(v___x_1436_, 4);
lean_dec(v_unused_1580_);
v_unused_1581_ = lean_ctor_get(v___x_1436_, 3);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v___x_1436_, 0);
lean_dec(v_unused_1582_);
v___x_1557_ = v___x_1436_;
v_isShared_1558_ = v_isSharedCheck_1579_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_v_1555_);
lean_inc(v_k_1554_);
lean_dec(v___x_1436_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1579_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v_k_1559_; lean_object* v_v_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1575_; 
v_k_1559_ = lean_ctor_get(v_l_1533_, 1);
v_v_1560_ = lean_ctor_get(v_l_1533_, 2);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_l_1533_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; lean_object* v_unused_1577_; lean_object* v_unused_1578_; 
v_unused_1576_ = lean_ctor_get(v_l_1533_, 4);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v_l_1533_, 3);
lean_dec(v_unused_1577_);
v_unused_1578_ = lean_ctor_get(v_l_1533_, 0);
lean_dec(v_unused_1578_);
v___x_1562_ = v_l_1533_;
v_isShared_1563_ = v_isSharedCheck_1575_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_v_1560_);
lean_inc(v_k_1559_);
lean_dec(v_l_1533_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1575_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1564_ = lean_unsigned_to_nat(3u);
v___x_1565_ = lean_unsigned_to_nat(1u);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 4, v_r_1534_);
lean_ctor_set(v___x_1562_, 3, v_r_1534_);
lean_ctor_set(v___x_1562_, 2, v_v_1251_);
lean_ctor_set(v___x_1562_, 1, v_k_1250_);
lean_ctor_set(v___x_1562_, 0, v___x_1565_);
v___x_1567_ = v___x_1562_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1574_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1574_, 3, v_r_1534_);
lean_ctor_set(v_reuseFailAlloc_1574_, 4, v_r_1534_);
v___x_1567_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1569_; 
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 3, v_r_1534_);
lean_ctor_set(v___x_1557_, 0, v___x_1565_);
v___x_1569_ = v___x_1557_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_k_1554_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v_v_1555_);
lean_ctor_set(v_reuseFailAlloc_1573_, 3, v_r_1534_);
lean_ctor_set(v_reuseFailAlloc_1573_, 4, v_r_1534_);
v___x_1569_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1571_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v___x_1569_);
lean_ctor_set(v___x_1255_, 3, v___x_1567_);
lean_ctor_set(v___x_1255_, 2, v_v_1560_);
lean_ctor_set(v___x_1255_, 1, v_k_1559_);
lean_ctor_set(v___x_1255_, 0, v___x_1564_);
v___x_1571_ = v___x_1255_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_k_1559_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_v_1560_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v___x_1567_);
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
}
}
else
{
lean_object* v_r_1583_; 
v_r_1583_ = lean_ctor_get(v___x_1436_, 4);
lean_inc(v_r_1583_);
if (lean_obj_tag(v_r_1583_) == 0)
{
lean_object* v_k_1584_; lean_object* v_v_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1597_; 
v_k_1584_ = lean_ctor_get(v___x_1436_, 1);
v_v_1585_ = lean_ctor_get(v___x_1436_, 2);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; 
v_unused_1598_ = lean_ctor_get(v___x_1436_, 4);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v___x_1436_, 3);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v___x_1436_, 0);
lean_dec(v_unused_1600_);
v___x_1587_ = v___x_1436_;
v_isShared_1588_ = v_isSharedCheck_1597_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_v_1585_);
lean_inc(v_k_1584_);
lean_dec(v___x_1436_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1597_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1589_ = lean_unsigned_to_nat(3u);
v___x_1590_ = lean_unsigned_to_nat(1u);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 4, v_l_1533_);
lean_ctor_set(v___x_1587_, 2, v_v_1251_);
lean_ctor_set(v___x_1587_, 1, v_k_1250_);
lean_ctor_set(v___x_1587_, 0, v___x_1590_);
v___x_1592_ = v___x_1587_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1596_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1596_, 3, v_l_1533_);
lean_ctor_set(v_reuseFailAlloc_1596_, 4, v_l_1533_);
v___x_1592_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1594_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v_r_1583_);
lean_ctor_set(v___x_1255_, 3, v___x_1592_);
lean_ctor_set(v___x_1255_, 2, v_v_1585_);
lean_ctor_set(v___x_1255_, 1, v_k_1584_);
lean_ctor_set(v___x_1255_, 0, v___x_1589_);
v___x_1594_ = v___x_1255_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_k_1584_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_v_1585_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v_r_1583_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1601_ = lean_unsigned_to_nat(2u);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v___x_1436_);
lean_ctor_set(v___x_1255_, 3, v_r_1583_);
lean_ctor_set(v___x_1255_, 0, v___x_1601_);
v___x_1603_ = v___x_1255_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v_r_1583_);
lean_ctor_set(v_reuseFailAlloc_1604_, 4, v___x_1436_);
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
else
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1605_ = lean_unsigned_to_nat(1u);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v___x_1436_);
lean_ctor_set(v___x_1255_, 3, v___x_1436_);
lean_ctor_set(v___x_1255_, 0, v___x_1605_);
v___x_1607_ = v___x_1255_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1608_, 4, v___x_1436_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_unsigned_to_nat(1u);
v___x_1611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
lean_ctor_set(v___x_1611_, 1, v_k_1246_);
lean_ctor_set(v___x_1611_, 2, v_v_1247_);
lean_ctor_set(v___x_1611_, 3, v_t_1248_);
lean_ctor_set(v___x_1611_, 4, v_t_1248_);
return v___x_1611_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore(lean_object* v_kvs_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_fst_1632_; lean_object* v_snd_1633_; lean_object* v___x_1634_; uint8_t v_decide_1635_; 
v_fst_1632_ = lean_ctor_get(v_a_1631_, 0);
v_snd_1633_ = lean_ctor_get(v_a_1631_, 1);
v___x_1634_ = lean_string_utf8_byte_size(v_fst_1632_);
v_decide_1635_ = lean_nat_dec_eq(v_snd_1633_, v___x_1634_);
if (v_decide_1635_ == 0)
{
uint32_t v___x_1636_; uint32_t v___x_1637_; uint8_t v___x_1638_; 
v___x_1636_ = lean_string_utf8_get_fast(v_fst_1632_, v_snd_1633_);
v___x_1637_ = 34;
v___x_1638_ = lean_uint32_dec_eq(v___x_1636_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec(v_kvs_1630_);
v___x_1639_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__1));
v___x_1640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1640_, 0, v_a_1631_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
return v___x_1640_;
}
else
{
lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1744_; 
lean_inc(v_snd_1633_);
lean_inc(v_fst_1632_);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_a_1631_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; lean_object* v_unused_1746_; 
v_unused_1745_ = lean_ctor_get(v_a_1631_, 1);
lean_dec(v_unused_1745_);
v_unused_1746_ = lean_ctor_get(v_a_1631_, 0);
lean_dec(v_unused_1746_);
v___x_1642_ = v_a_1631_;
v_isShared_1643_ = v_isSharedCheck_1744_;
goto v_resetjp_1641_;
}
else
{
lean_dec(v_a_1631_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1744_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = lean_string_utf8_next_fast(v_fst_1632_, v_snd_1633_);
lean_dec(v_snd_1633_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 1, v___x_1644_);
v___x_1646_ = v___x_1642_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_fst_1632_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_1648_ = l_Lean_Json_Parser_strCore(v___x_1647_, v___x_1646_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_pos_1649_; lean_object* v_res_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1733_; 
v_pos_1649_ = lean_ctor_get(v___x_1648_, 0);
v_res_1650_ = lean_ctor_get(v___x_1648_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1652_ = v___x_1648_;
v_isShared_1653_ = v_isSharedCheck_1733_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_res_1650_);
lean_inc(v_pos_1649_);
lean_dec(v___x_1648_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1733_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v_fst_1654_; lean_object* v_snd_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1732_; 
v_fst_1654_ = lean_ctor_get(v_pos_1649_, 0);
v_snd_1655_ = lean_ctor_get(v_pos_1649_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_pos_1649_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1657_ = v_pos_1649_;
v_isShared_1658_ = v_isSharedCheck_1732_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_snd_1655_);
lean_inc(v_fst_1654_);
lean_dec(v_pos_1649_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1732_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1654_, v_snd_1655_);
lean_inc(v___x_1659_);
lean_inc(v_fst_1654_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 1, v___x_1659_);
v___x_1661_ = v___x_1657_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_fst_1654_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1667_; uint8_t v_decide_1668_; 
v___x_1667_ = lean_string_utf8_byte_size(v_fst_1654_);
v_decide_1668_ = lean_nat_dec_eq(v___x_1659_, v___x_1667_);
if (v_decide_1668_ == 0)
{
if (v___x_1638_ == 0)
{
lean_dec(v___x_1659_);
lean_dec(v_fst_1654_);
lean_dec(v_res_1650_);
lean_dec(v_kvs_1630_);
goto v___jp_1662_;
}
else
{
uint32_t v___x_1669_; uint32_t v___x_1670_; uint8_t v___x_1671_; 
lean_del_object(v___x_1652_);
v___x_1669_ = lean_string_utf8_get_fast(v_fst_1654_, v___x_1659_);
v___x_1670_ = 58;
v___x_1671_ = lean_uint32_dec_eq(v___x_1669_, v___x_1670_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_dec(v___x_1659_);
lean_dec(v_fst_1654_);
lean_dec(v_res_1650_);
lean_dec(v_kvs_1630_);
v___x_1672_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__3));
v___x_1673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1661_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
return v___x_1673_;
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec_ref(v___x_1661_);
v___x_1674_ = lean_string_utf8_next_fast(v_fst_1654_, v___x_1659_);
lean_dec(v___x_1659_);
v___x_1675_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1654_, v___x_1674_);
v___x_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1676_, 0, v_fst_1654_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = l_Lean_Json_Parser_anyCore(v___x_1676_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_pos_1678_; lean_object* v_res_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1721_; 
v_pos_1678_ = lean_ctor_get(v___x_1677_, 0);
v_res_1679_ = lean_ctor_get(v___x_1677_, 1);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1681_ = v___x_1677_;
v_isShared_1682_ = v_isSharedCheck_1721_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_res_1679_);
lean_inc(v_pos_1678_);
lean_dec(v___x_1677_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1721_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v_fst_1688_; lean_object* v_snd_1689_; lean_object* v___x_1690_; uint8_t v_decide_1691_; 
v_fst_1688_ = lean_ctor_get(v_pos_1678_, 0);
v_snd_1689_ = lean_ctor_get(v_pos_1678_, 1);
v___x_1690_ = lean_string_utf8_byte_size(v_fst_1688_);
v_decide_1691_ = lean_nat_dec_eq(v_snd_1689_, v___x_1690_);
if (v_decide_1691_ == 0)
{
if (v___x_1671_ == 0)
{
lean_dec(v_res_1679_);
lean_dec(v_res_1650_);
lean_dec(v_kvs_1630_);
goto v___jp_1683_;
}
else
{
lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1718_; 
lean_inc(v_snd_1689_);
lean_inc(v_fst_1688_);
lean_del_object(v___x_1681_);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_pos_1678_);
if (v_isSharedCheck_1718_ == 0)
{
lean_object* v_unused_1719_; lean_object* v_unused_1720_; 
v_unused_1719_ = lean_ctor_get(v_pos_1678_, 1);
lean_dec(v_unused_1719_);
v_unused_1720_ = lean_ctor_get(v_pos_1678_, 0);
lean_dec(v_unused_1720_);
v___x_1693_ = v_pos_1678_;
v_isShared_1694_ = v_isSharedCheck_1718_;
goto v_resetjp_1692_;
}
else
{
lean_dec(v_pos_1678_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1718_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
uint32_t v___x_1695_; lean_object* v___x_1696_; uint32_t v___x_1697_; uint8_t v___x_1698_; 
v___x_1695_ = lean_string_utf8_get_fast(v_fst_1688_, v_snd_1689_);
v___x_1696_ = lean_string_utf8_next_fast(v_fst_1688_, v_snd_1689_);
lean_dec(v_snd_1689_);
v___x_1697_ = 125;
v___x_1698_ = lean_uint32_dec_eq(v___x_1695_, v___x_1697_);
if (v___x_1698_ == 0)
{
uint32_t v___x_1699_; uint8_t v___x_1700_; 
v___x_1699_ = 44;
v___x_1700_ = lean_uint32_dec_eq(v___x_1695_, v___x_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1702_; 
lean_dec(v_res_1679_);
lean_dec(v_res_1650_);
lean_dec(v_kvs_1630_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 1, v___x_1696_);
v___x_1702_ = v___x_1693_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_fst_1688_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v___x_1696_);
v___x_1702_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__5));
v___x_1704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1702_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
return v___x_1704_;
}
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1688_, v___x_1696_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 1, v___x_1706_);
v___x_1708_ = v___x_1693_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_fst_1688_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_res_1650_, v_res_1679_, v_kvs_1630_);
v_kvs_1630_ = v___x_1709_;
v_a_1631_ = v___x_1708_;
goto _start;
}
}
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1712_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1688_, v___x_1696_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 1, v___x_1712_);
v___x_1714_ = v___x_1693_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_fst_1688_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_res_1650_, v_res_1679_, v_kvs_1630_);
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1714_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
return v___x_1716_;
}
}
}
}
}
else
{
lean_dec(v_res_1679_);
lean_dec(v_res_1650_);
lean_dec(v_kvs_1630_);
goto v___jp_1683_;
}
v___jp_1683_:
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1684_ = lean_box(0);
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 1);
lean_ctor_set(v___x_1681_, 1, v___x_1684_);
v___x_1686_ = v___x_1681_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_pos_1678_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
else
{
lean_object* v_pos_1722_; lean_object* v_err_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec(v_res_1650_);
lean_dec(v_kvs_1630_);
v_pos_1722_ = lean_ctor_get(v___x_1677_, 0);
v_err_1723_ = lean_ctor_get(v___x_1677_, 1);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1677_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_err_1723_);
lean_inc(v_pos_1722_);
lean_dec(v___x_1677_);
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
else
{
lean_dec(v___x_1659_);
lean_dec(v_fst_1654_);
lean_dec(v_res_1650_);
lean_dec(v_kvs_1630_);
goto v___jp_1662_;
}
v___jp_1662_:
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1663_ = lean_box(0);
if (v_isShared_1653_ == 0)
{
lean_ctor_set_tag(v___x_1652_, 1);
lean_ctor_set(v___x_1652_, 1, v___x_1663_);
lean_ctor_set(v___x_1652_, 0, v___x_1661_);
v___x_1665_ = v___x_1652_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v___x_1663_);
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
}
else
{
lean_object* v_pos_1734_; lean_object* v_err_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec(v_kvs_1630_);
v_pos_1734_ = lean_ctor_get(v___x_1648_, 0);
v_err_1735_ = lean_ctor_get(v___x_1648_, 1);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1648_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_err_1735_);
lean_inc(v_pos_1734_);
lean_dec(v___x_1648_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_pos_1734_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_err_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_dec(v_kvs_1630_);
v___x_1747_ = lean_box(0);
v___x_1748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1748_, 0, v_a_1631_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
return v___x_1748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object* v_a_1755_){
_start:
{
lean_object* v_fst_1790_; lean_object* v_snd_1791_; lean_object* v___x_1792_; uint8_t v_decide_1793_; 
v_fst_1790_ = lean_ctor_get(v_a_1755_, 0);
v_snd_1791_ = lean_ctor_get(v_a_1755_, 1);
v___x_1792_ = lean_string_utf8_byte_size(v_fst_1790_);
v_decide_1793_ = lean_nat_dec_eq(v_snd_1791_, v___x_1792_);
if (v_decide_1793_ == 0)
{
uint32_t v___x_1794_; uint32_t v___x_1795_; uint8_t v___x_1796_; 
v___x_1794_ = lean_string_utf8_get_fast(v_fst_1790_, v_snd_1791_);
v___x_1795_ = 91;
v___x_1796_ = lean_uint32_dec_eq(v___x_1794_, v___x_1795_);
if (v___x_1796_ == 0)
{
uint32_t v___x_1797_; uint8_t v___x_1798_; 
v___x_1797_ = 123;
v___x_1798_ = lean_uint32_dec_eq(v___x_1794_, v___x_1797_);
if (v___x_1798_ == 0)
{
uint32_t v___x_1799_; uint8_t v___x_1800_; 
v___x_1799_ = 34;
v___x_1800_ = lean_uint32_dec_eq(v___x_1794_, v___x_1799_);
if (v___x_1800_ == 0)
{
uint32_t v___x_1801_; uint8_t v___x_1802_; 
v___x_1801_ = 102;
v___x_1802_ = lean_uint32_dec_eq(v___x_1794_, v___x_1801_);
if (v___x_1802_ == 0)
{
uint32_t v___x_1803_; uint8_t v___x_1804_; 
v___x_1803_ = 116;
v___x_1804_ = lean_uint32_dec_eq(v___x_1794_, v___x_1803_);
if (v___x_1804_ == 0)
{
uint32_t v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = 110;
v___x_1806_ = lean_uint32_dec_eq(v___x_1794_, v___x_1805_);
if (v___x_1806_ == 0)
{
uint32_t v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = 45;
v___x_1808_ = lean_uint32_dec_eq(v___x_1794_, v___x_1807_);
if (v___x_1808_ == 0)
{
uint32_t v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = 48;
v___x_1810_ = lean_uint32_dec_le(v___x_1809_, v___x_1794_);
if (v___x_1810_ == 0)
{
goto v___jp_1787_;
}
else
{
uint32_t v___x_1811_; uint8_t v___x_1812_; 
v___x_1811_ = 57;
v___x_1812_ = lean_uint32_dec_le(v___x_1794_, v___x_1811_);
if (v___x_1812_ == 0)
{
goto v___jp_1787_;
}
else
{
goto v___jp_1756_;
}
}
}
else
{
goto v___jp_1756_;
}
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__2));
v___x_1814_ = l_Std_Internal_Parsec_String_pstring(v___x_1813_, v_a_1755_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_pos_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1833_; 
v_pos_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1833_ == 0)
{
lean_object* v_unused_1834_; 
v_unused_1834_ = lean_ctor_get(v___x_1814_, 1);
lean_dec(v_unused_1834_);
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1833_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_pos_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1833_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v_fst_1819_; lean_object* v_snd_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1832_; 
v_fst_1819_ = lean_ctor_get(v_pos_1815_, 0);
v_snd_1820_ = lean_ctor_get(v_pos_1815_, 1);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_pos_1815_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1822_ = v_pos_1815_;
v_isShared_1823_ = v_isSharedCheck_1832_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_snd_1820_);
lean_inc(v_fst_1819_);
lean_dec(v_pos_1815_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1832_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1819_, v_snd_1820_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 1, v___x_1824_);
v___x_1826_ = v___x_1822_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_fst_1819_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1827_ = lean_box(0);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 1, v___x_1827_);
lean_ctor_set(v___x_1817_, 0, v___x_1826_);
v___x_1829_ = v___x_1817_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v___x_1827_);
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
lean_object* v_pos_1835_; lean_object* v_err_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
v_pos_1835_ = lean_ctor_get(v___x_1814_, 0);
v_err_1836_ = lean_ctor_get(v___x_1814_, 1);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1814_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_err_1836_);
lean_inc(v_pos_1835_);
lean_dec(v___x_1814_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_pos_1835_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_err_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__3));
v___x_1845_ = l_Std_Internal_Parsec_String_pstring(v___x_1844_, v_a_1755_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_pos_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1864_; 
v_pos_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1864_ == 0)
{
lean_object* v_unused_1865_; 
v_unused_1865_ = lean_ctor_get(v___x_1845_, 1);
lean_dec(v_unused_1865_);
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1864_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_pos_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1864_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v_fst_1850_; lean_object* v_snd_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1863_; 
v_fst_1850_ = lean_ctor_get(v_pos_1846_, 0);
v_snd_1851_ = lean_ctor_get(v_pos_1846_, 1);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_pos_1846_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1853_ = v_pos_1846_;
v_isShared_1854_ = v_isSharedCheck_1863_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_snd_1851_);
lean_inc(v_fst_1850_);
lean_dec(v_pos_1846_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1863_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1855_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1850_, v_snd_1851_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 1, v___x_1855_);
v___x_1857_ = v___x_1853_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_fst_1850_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1858_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1858_, 0, v___x_1804_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 1, v___x_1858_);
lean_ctor_set(v___x_1848_, 0, v___x_1857_);
v___x_1860_ = v___x_1848_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1857_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v___x_1858_);
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
lean_object* v_pos_1866_; lean_object* v_err_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
v_pos_1866_ = lean_ctor_get(v___x_1845_, 0);
v_err_1867_ = lean_ctor_get(v___x_1845_, 1);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1845_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_err_1867_);
lean_inc(v_pos_1866_);
lean_dec(v___x_1845_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_pos_1866_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_err_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__4));
v___x_1876_ = l_Std_Internal_Parsec_String_pstring(v___x_1875_, v_a_1755_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_pos_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1895_; 
v_pos_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; 
v_unused_1896_ = lean_ctor_get(v___x_1876_, 1);
lean_dec(v_unused_1896_);
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1895_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_pos_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1895_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v_fst_1881_; lean_object* v_snd_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1894_; 
v_fst_1881_ = lean_ctor_get(v_pos_1877_, 0);
v_snd_1882_ = lean_ctor_get(v_pos_1877_, 1);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_pos_1877_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1884_ = v_pos_1877_;
v_isShared_1885_ = v_isSharedCheck_1894_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_snd_1882_);
lean_inc(v_fst_1881_);
lean_dec(v_pos_1877_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1894_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1886_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1881_, v_snd_1882_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 1, v___x_1886_);
v___x_1888_ = v___x_1884_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_fst_1881_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1889_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1889_, 0, v___x_1800_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v___x_1889_);
lean_ctor_set(v___x_1879_, 0, v___x_1888_);
v___x_1891_ = v___x_1879_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v___x_1889_);
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
lean_object* v_pos_1897_; lean_object* v_err_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_pos_1897_ = lean_ctor_get(v___x_1876_, 0);
v_err_1898_ = lean_ctor_get(v___x_1876_, 1);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1876_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_err_1898_);
lean_inc(v_pos_1897_);
lean_dec(v___x_1876_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_pos_1897_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_err_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
else
{
lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1944_; 
lean_inc(v_snd_1791_);
lean_inc(v_fst_1790_);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_a_1755_);
if (v_isSharedCheck_1944_ == 0)
{
lean_object* v_unused_1945_; lean_object* v_unused_1946_; 
v_unused_1945_ = lean_ctor_get(v_a_1755_, 1);
lean_dec(v_unused_1945_);
v_unused_1946_ = lean_ctor_get(v_a_1755_, 0);
lean_dec(v_unused_1946_);
v___x_1907_ = v_a_1755_;
v_isShared_1908_ = v_isSharedCheck_1944_;
goto v_resetjp_1906_;
}
else
{
lean_dec(v_a_1755_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1944_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = lean_string_utf8_next_fast(v_fst_1790_, v_snd_1791_);
lean_dec(v_snd_1791_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 1, v___x_1909_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_fst_1790_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_1913_ = l_Lean_Json_Parser_strCore(v___x_1912_, v___x_1911_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_pos_1914_; lean_object* v_res_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1933_; 
v_pos_1914_ = lean_ctor_get(v___x_1913_, 0);
v_res_1915_ = lean_ctor_get(v___x_1913_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1917_ = v___x_1913_;
v_isShared_1918_ = v_isSharedCheck_1933_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_res_1915_);
lean_inc(v_pos_1914_);
lean_dec(v___x_1913_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1933_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v_fst_1919_; lean_object* v_snd_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1932_; 
v_fst_1919_ = lean_ctor_get(v_pos_1914_, 0);
v_snd_1920_ = lean_ctor_get(v_pos_1914_, 1);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_pos_1914_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1922_ = v_pos_1914_;
v_isShared_1923_ = v_isSharedCheck_1932_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_snd_1920_);
lean_inc(v_fst_1919_);
lean_dec(v_pos_1914_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1932_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1924_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1919_, v_snd_1920_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 1, v___x_1924_);
v___x_1926_ = v___x_1922_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_fst_1919_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1927_, 0, v_res_1915_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 1, v___x_1927_);
lean_ctor_set(v___x_1917_, 0, v___x_1926_);
v___x_1929_ = v___x_1917_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
}
else
{
lean_object* v_pos_1934_; lean_object* v_err_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
v_pos_1934_ = lean_ctor_get(v___x_1913_, 0);
v_err_1935_ = lean_ctor_get(v___x_1913_, 1);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1913_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_err_1935_);
lean_inc(v_pos_1934_);
lean_dec(v___x_1913_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_pos_1934_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_err_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1989_; 
lean_inc(v_snd_1791_);
lean_inc(v_fst_1790_);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_a_1755_);
if (v_isSharedCheck_1989_ == 0)
{
lean_object* v_unused_1990_; lean_object* v_unused_1991_; 
v_unused_1990_ = lean_ctor_get(v_a_1755_, 1);
lean_dec(v_unused_1990_);
v_unused_1991_ = lean_ctor_get(v_a_1755_, 0);
lean_dec(v_unused_1991_);
v___x_1948_ = v_a_1755_;
v_isShared_1949_ = v_isSharedCheck_1989_;
goto v_resetjp_1947_;
}
else
{
lean_dec(v_a_1755_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1989_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1953_; 
v___x_1950_ = lean_string_utf8_next_fast(v_fst_1790_, v_snd_1791_);
lean_dec(v_snd_1791_);
v___x_1951_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1790_, v___x_1950_);
lean_inc(v___x_1951_);
lean_inc(v_fst_1790_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 1, v___x_1951_);
v___x_1953_ = v___x_1948_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_fst_1790_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v___x_1951_);
v___x_1953_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
uint8_t v___y_1955_; uint8_t v_decide_1987_; 
v_decide_1987_ = lean_nat_dec_eq(v___x_1951_, v___x_1792_);
if (v_decide_1987_ == 0)
{
v___y_1955_ = v___x_1798_;
goto v___jp_1954_;
}
else
{
v___y_1955_ = v___x_1796_;
goto v___jp_1954_;
}
v___jp_1954_:
{
if (v___y_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
lean_dec(v___x_1951_);
lean_dec(v_fst_1790_);
v___x_1956_ = lean_box(0);
v___x_1957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1953_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
return v___x_1957_;
}
else
{
uint32_t v___x_1958_; uint32_t v___x_1959_; uint8_t v___x_1960_; 
v___x_1958_ = lean_string_utf8_get_fast(v_fst_1790_, v___x_1951_);
v___x_1959_ = 125;
v___x_1960_ = lean_uint32_dec_eq(v___x_1958_, v___x_1959_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec(v___x_1951_);
lean_dec(v_fst_1790_);
v___x_1961_ = lean_box(1);
v___x_1962_ = l_Lean_Json_Parser_objectCore(v___x_1961_, v___x_1953_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_pos_1963_; lean_object* v_res_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1972_; 
v_pos_1963_ = lean_ctor_get(v___x_1962_, 0);
v_res_1964_ = lean_ctor_get(v___x_1962_, 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1966_ = v___x_1962_;
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_res_1964_);
lean_inc(v_pos_1963_);
lean_dec(v___x_1962_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1968_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1968_, 0, v_res_1964_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 1, v___x_1968_);
v___x_1970_ = v___x_1966_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_pos_1963_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
else
{
lean_object* v_pos_1973_; lean_object* v_err_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
v_pos_1973_ = lean_ctor_get(v___x_1962_, 0);
v_err_1974_ = lean_ctor_get(v___x_1962_, 1);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1962_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_err_1974_);
lean_inc(v_pos_1973_);
lean_dec(v___x_1962_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_pos_1973_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_err_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
lean_dec_ref(v___x_1953_);
v___x_1982_ = lean_string_utf8_next_fast(v_fst_1790_, v___x_1951_);
lean_dec(v___x_1951_);
v___x_1983_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1790_, v___x_1982_);
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v_fst_1790_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__5));
v___x_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1984_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
return v___x_1986_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2034_; 
lean_inc(v_snd_1791_);
lean_inc(v_fst_1790_);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_a_1755_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; lean_object* v_unused_2036_; 
v_unused_2035_ = lean_ctor_get(v_a_1755_, 1);
lean_dec(v_unused_2035_);
v_unused_2036_ = lean_ctor_get(v_a_1755_, 0);
lean_dec(v_unused_2036_);
v___x_1993_ = v_a_1755_;
v_isShared_1994_ = v_isSharedCheck_2034_;
goto v_resetjp_1992_;
}
else
{
lean_dec(v_a_1755_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2034_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1995_ = lean_string_utf8_next_fast(v_fst_1790_, v_snd_1791_);
lean_dec(v_snd_1791_);
v___x_1996_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1790_, v___x_1995_);
lean_inc(v___x_1996_);
lean_inc(v_fst_1790_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 1, v___x_1996_);
v___x_1998_ = v___x_1993_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_fst_1790_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_2033_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
uint8_t v_decide_2002_; 
v_decide_2002_ = lean_nat_dec_eq(v___x_1996_, v___x_1792_);
if (v_decide_2002_ == 0)
{
if (v___x_1796_ == 0)
{
lean_dec(v___x_1996_);
lean_dec(v_fst_1790_);
goto v___jp_1999_;
}
else
{
uint32_t v___x_2003_; uint32_t v___x_2004_; uint8_t v___x_2005_; 
v___x_2003_ = lean_string_utf8_get_fast(v_fst_1790_, v___x_1996_);
v___x_2004_ = 93;
v___x_2005_ = lean_uint32_dec_eq(v___x_2003_, v___x_2004_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec(v___x_1996_);
lean_dec(v_fst_1790_);
v___x_2006_ = lean_unsigned_to_nat(4u);
v___x_2007_ = lean_mk_empty_array_with_capacity(v___x_2006_);
v___x_2008_ = l_Lean_Json_Parser_arrayCore(v___x_2007_, v___x_1998_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_pos_2009_; lean_object* v_res_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2018_; 
v_pos_2009_ = lean_ctor_get(v___x_2008_, 0);
v_res_2010_ = lean_ctor_get(v___x_2008_, 1);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2012_ = v___x_2008_;
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_res_2010_);
lean_inc(v_pos_2009_);
lean_dec(v___x_2008_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2014_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2014_, 0, v_res_2010_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 1, v___x_2014_);
v___x_2016_ = v___x_2012_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_pos_2009_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
else
{
lean_object* v_pos_2019_; lean_object* v_err_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
v_pos_2019_ = lean_ctor_get(v___x_2008_, 0);
v_err_2020_ = lean_ctor_get(v___x_2008_, 1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2008_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_err_2020_);
lean_inc(v_pos_2019_);
lean_dec(v___x_2008_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_pos_2019_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_err_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_dec_ref(v___x_1998_);
v___x_2028_ = lean_string_utf8_next_fast(v_fst_1790_, v___x_1996_);
lean_dec(v___x_1996_);
v___x_2029_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1790_, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v_fst_1790_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__7));
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2030_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
return v___x_2032_;
}
}
}
else
{
lean_dec(v___x_1996_);
lean_dec(v_fst_1790_);
goto v___jp_1999_;
}
v___jp_1999_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_box(0);
v___x_2001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1998_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
return v___x_2001_;
}
}
}
}
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = lean_box(0);
v___x_2038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2038_, 0, v_a_1755_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
return v___x_2038_;
}
v___jp_1756_:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_Json_Parser_num(v_a_1755_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_pos_1758_; lean_object* v_res_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1777_; 
v_pos_1758_ = lean_ctor_get(v___x_1757_, 0);
v_res_1759_ = lean_ctor_get(v___x_1757_, 1);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1761_ = v___x_1757_;
v_isShared_1762_ = v_isSharedCheck_1777_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_res_1759_);
lean_inc(v_pos_1758_);
lean_dec(v___x_1757_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1777_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v_fst_1763_; lean_object* v_snd_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1776_; 
v_fst_1763_ = lean_ctor_get(v_pos_1758_, 0);
v_snd_1764_ = lean_ctor_get(v_pos_1758_, 1);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_pos_1758_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1766_ = v_pos_1758_;
v_isShared_1767_ = v_isSharedCheck_1776_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_snd_1764_);
lean_inc(v_fst_1763_);
lean_dec(v_pos_1758_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1776_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1768_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1763_, v_snd_1764_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 1, v___x_1768_);
v___x_1770_ = v___x_1766_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_fst_1763_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1771_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1771_, 0, v_res_1759_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v___x_1771_);
lean_ctor_set(v___x_1761_, 0, v___x_1770_);
v___x_1773_ = v___x_1761_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
else
{
lean_object* v_pos_1778_; lean_object* v_err_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
v_pos_1778_ = lean_ctor_get(v___x_1757_, 0);
v_err_1779_ = lean_ctor_get(v___x_1757_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1757_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_err_1779_);
lean_inc(v_pos_1778_);
lean_dec(v___x_1757_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_pos_1778_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_err_1779_);
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
v___jp_1787_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__1));
v___x_1789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_a_1755_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
return v___x_1789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore(lean_object* v_acc_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l_Lean_Json_Parser_anyCore(v_a_2040_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_pos_2042_; lean_object* v_res_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2087_; 
v_pos_2042_ = lean_ctor_get(v___x_2041_, 0);
v_res_2043_ = lean_ctor_get(v___x_2041_, 1);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2045_ = v___x_2041_;
v_isShared_2046_ = v_isSharedCheck_2087_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_res_2043_);
lean_inc(v_pos_2042_);
lean_dec(v___x_2041_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2087_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v_fst_2047_; lean_object* v_snd_2048_; lean_object* v___x_2049_; uint8_t v_decide_2050_; 
v_fst_2047_ = lean_ctor_get(v_pos_2042_, 0);
v_snd_2048_ = lean_ctor_get(v_pos_2042_, 1);
v___x_2049_ = lean_string_utf8_byte_size(v_fst_2047_);
v_decide_2050_ = lean_nat_dec_eq(v_snd_2048_, v___x_2049_);
if (v_decide_2050_ == 0)
{
lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2080_; 
lean_inc(v_snd_2048_);
lean_inc(v_fst_2047_);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_pos_2042_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; lean_object* v_unused_2082_; 
v_unused_2081_ = lean_ctor_get(v_pos_2042_, 1);
lean_dec(v_unused_2081_);
v_unused_2082_ = lean_ctor_get(v_pos_2042_, 0);
lean_dec(v_unused_2082_);
v___x_2052_ = v_pos_2042_;
v_isShared_2053_ = v_isSharedCheck_2080_;
goto v_resetjp_2051_;
}
else
{
lean_dec(v_pos_2042_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2080_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2054_; uint32_t v___x_2055_; lean_object* v___x_2056_; uint32_t v___x_2057_; uint8_t v___x_2058_; 
v___x_2054_ = lean_array_push(v_acc_2039_, v_res_2043_);
v___x_2055_ = lean_string_utf8_get_fast(v_fst_2047_, v_snd_2048_);
v___x_2056_ = lean_string_utf8_next_fast(v_fst_2047_, v_snd_2048_);
lean_dec(v_snd_2048_);
v___x_2057_ = 93;
v___x_2058_ = lean_uint32_dec_eq(v___x_2055_, v___x_2057_);
if (v___x_2058_ == 0)
{
uint32_t v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = 44;
v___x_2060_ = lean_uint32_dec_eq(v___x_2055_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2062_; 
lean_dec_ref(v___x_2054_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 1, v___x_2056_);
v___x_2062_ = v___x_2052_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_fst_2047_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v___x_2056_);
v___x_2062_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2063_ = ((lean_object*)(l_Lean_Json_Parser_arrayCore___closed__1));
if (v_isShared_2046_ == 0)
{
lean_ctor_set_tag(v___x_2045_, 1);
lean_ctor_set(v___x_2045_, 1, v___x_2063_);
lean_ctor_set(v___x_2045_, 0, v___x_2062_);
v___x_2065_ = v___x_2045_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
lean_del_object(v___x_2045_);
v___x_2068_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2047_, v___x_2056_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 1, v___x_2068_);
v___x_2070_ = v___x_2052_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_fst_2047_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
v_acc_2039_ = v___x_2054_;
v_a_2040_ = v___x_2070_;
goto _start;
}
}
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2073_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2047_, v___x_2056_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 1, v___x_2073_);
v___x_2075_ = v___x_2052_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_fst_2047_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2077_; 
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 1, v___x_2054_);
lean_ctor_set(v___x_2045_, 0, v___x_2075_);
v___x_2077_ = v___x_2045_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___x_2054_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
lean_dec(v_res_2043_);
lean_dec_ref(v_acc_2039_);
v___x_2083_ = lean_box(0);
if (v_isShared_2046_ == 0)
{
lean_ctor_set_tag(v___x_2045_, 1);
lean_ctor_set(v___x_2045_, 1, v___x_2083_);
v___x_2085_ = v___x_2045_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_pos_2042_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v___x_2083_);
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
else
{
lean_object* v_pos_2088_; lean_object* v_err_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v_acc_2039_);
v_pos_2088_ = lean_ctor_get(v___x_2041_, 0);
v_err_2089_ = lean_ctor_get(v___x_2041_, 1);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2041_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_err_2089_);
lean_inc(v_pos_2088_);
lean_dec(v___x_2041_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_pos_2088_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_err_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2(lean_object* v_00_u03b2_2097_, lean_object* v_msg_2098_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v_msg_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2(lean_object* v_00_u03b2_2100_, lean_object* v_k_2101_, lean_object* v_v_2102_, lean_object* v_t_2103_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_2101_, v_v_2102_, v_t_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_any(lean_object* v_a_2108_){
_start:
{
lean_object* v_fst_2109_; lean_object* v_snd_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2134_; 
v_fst_2109_ = lean_ctor_get(v_a_2108_, 0);
v_snd_2110_ = lean_ctor_get(v_a_2108_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_a_2108_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2112_ = v_a_2108_;
v_isShared_2113_ = v_isSharedCheck_2134_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_snd_2110_);
lean_inc(v_fst_2109_);
lean_dec(v_a_2108_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2134_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2114_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2109_, v_snd_2110_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 1, v___x_2114_);
v___x_2116_ = v___x_2112_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_fst_2109_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lean_Json_Parser_anyCore(v___x_2116_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_pos_2118_; lean_object* v_fst_2119_; lean_object* v_snd_2120_; lean_object* v___x_2121_; uint8_t v_decide_2122_; 
v_pos_2118_ = lean_ctor_get(v___x_2117_, 0);
v_fst_2119_ = lean_ctor_get(v_pos_2118_, 0);
v_snd_2120_ = lean_ctor_get(v_pos_2118_, 1);
v___x_2121_ = lean_string_utf8_byte_size(v_fst_2119_);
v_decide_2122_ = lean_nat_dec_eq(v_snd_2120_, v___x_2121_);
if (v_decide_2122_ == 0)
{
lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2130_; 
lean_inc(v_pos_2118_);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; lean_object* v_unused_2132_; 
v_unused_2131_ = lean_ctor_get(v___x_2117_, 1);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v___x_2117_, 0);
lean_dec(v_unused_2132_);
v___x_2124_ = v___x_2117_;
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
else
{
lean_dec(v___x_2117_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2126_ = ((lean_object*)(l_Lean_Json_Parser_any___closed__1));
if (v_isShared_2125_ == 0)
{
lean_ctor_set_tag(v___x_2124_, 1);
lean_ctor_set(v___x_2124_, 1, v___x_2126_);
v___x_2128_ = v___x_2124_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_pos_2118_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
else
{
return v___x_2117_;
}
}
else
{
return v___x_2117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parse(lean_object* v_s_2135_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
v___x_2137_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_2136_, v_s_2135_);
return v___x_2137_;
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
