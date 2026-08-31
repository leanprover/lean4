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
uint8_t v___y_61_; uint32_t v___y_62_; lean_object* v___y_63_; uint8_t v___y_64_; lean_object* v_fst_71_; lean_object* v_snd_72_; lean_object* v___x_73_; uint8_t v_decide_74_; 
v_fst_71_ = lean_ctor_get(v_a_59_, 0);
v_snd_72_ = lean_ctor_get(v_a_59_, 1);
v___x_73_ = lean_string_utf8_byte_size(v_fst_71_);
v_decide_74_ = lean_nat_dec_eq(v_snd_72_, v___x_73_);
if (v_decide_74_ == 0)
{
lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_184_; 
lean_inc(v_snd_72_);
lean_inc(v_fst_71_);
v_isSharedCheck_184_ = !lean_is_exclusive(v_a_59_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; lean_object* v_unused_186_; 
v_unused_185_ = lean_ctor_get(v_a_59_, 1);
lean_dec(v_unused_185_);
v_unused_186_ = lean_ctor_get(v_a_59_, 0);
lean_dec(v_unused_186_);
v___x_76_ = v_a_59_;
v_isShared_77_ = v_isSharedCheck_184_;
goto v_resetjp_75_;
}
else
{
lean_dec(v_a_59_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_184_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
uint32_t v_c_78_; lean_object* v___x_79_; lean_object* v_it_x27_81_; 
v_c_78_ = lean_string_utf8_get_fast(v_fst_71_, v_snd_72_);
v___x_79_ = lean_string_utf8_next_fast(v_fst_71_, v_snd_72_);
lean_dec(v_snd_72_);
lean_inc(v_fst_71_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 1, v___x_79_);
v_it_x27_81_ = v___x_76_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_fst_71_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_79_);
v_it_x27_81_ = v_reuseFailAlloc_183_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
uint32_t v___x_85_; uint8_t v___x_86_; 
v___x_85_ = 92;
v___x_86_ = lean_uint32_dec_eq(v_c_78_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec(v_fst_71_);
v___x_87_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_88_, 0, v_it_x27_81_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
return v___x_88_;
}
else
{
uint8_t v_decide_89_; 
v_decide_89_ = lean_nat_dec_eq(v___x_79_, v___x_73_);
if (v_decide_89_ == 0)
{
if (v___x_86_ == 0)
{
lean_dec(v_fst_71_);
goto v___jp_82_;
}
else
{
uint32_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint32_t v___x_96_; uint8_t v___x_97_; 
lean_dec_ref(v_it_x27_81_);
v___x_90_ = lean_string_utf8_get_fast(v_fst_71_, v___x_79_);
v___x_91_ = lean_string_utf8_next_fast(v_fst_71_, v___x_79_);
lean_inc(v_fst_71_);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v_fst_71_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_96_ = 117;
v___x_97_ = lean_uint32_dec_eq(v___x_90_, v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec(v_fst_71_);
v___x_98_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_99_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_92_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
return v___x_99_;
}
else
{
uint8_t v_decide_100_; 
v_decide_100_ = lean_nat_dec_eq(v___x_91_, v___x_73_);
if (v_decide_100_ == 0)
{
if (v___x_97_ == 0)
{
lean_dec(v_fst_71_);
goto v___jp_93_;
}
else
{
uint32_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint32_t v___x_177_; uint8_t v___x_178_; 
lean_dec_ref_known(v___x_92_, 2);
v___x_101_ = lean_string_utf8_get_fast(v_fst_71_, v___x_91_);
v___x_102_ = lean_string_utf8_next_fast(v_fst_71_, v___x_91_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v_fst_71_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_177_ = 100;
v___x_178_ = lean_uint32_dec_eq(v___x_101_, v___x_177_);
if (v___x_178_ == 0)
{
uint32_t v___x_179_; uint8_t v___x_180_; 
v___x_179_ = 68;
v___x_180_ = lean_uint32_dec_eq(v___x_101_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_103_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
return v___x_182_;
}
else
{
goto v___jp_104_;
}
}
else
{
goto v___jp_104_;
}
v___jp_104_:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Json_Parser_hexChar(v___x_103_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_pos_106_; lean_object* v_res_107_; lean_object* v___x_108_; 
v_pos_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_pos_106_);
v_res_107_ = lean_ctor_get(v___x_105_, 1);
lean_inc(v_res_107_);
lean_dec_ref_known(v___x_105_, 2);
v___x_108_ = l_Lean_Json_Parser_hexChar(v_pos_106_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_pos_109_; lean_object* v_res_110_; lean_object* v___x_111_; 
v_pos_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_pos_109_);
v_res_110_ = lean_ctor_get(v___x_108_, 1);
lean_inc(v_res_110_);
lean_dec_ref_known(v___x_108_, 2);
v___x_111_ = l_Lean_Json_Parser_hexChar(v_pos_109_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_pos_112_; lean_object* v_res_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_149_; 
v_pos_112_ = lean_ctor_get(v___x_111_, 0);
v_res_113_ = lean_ctor_get(v___x_111_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_149_ == 0)
{
v___x_115_ = v___x_111_;
v_isShared_116_ = v_isSharedCheck_149_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_res_113_);
lean_inc(v_pos_112_);
lean_dec(v___x_111_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_149_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
uint16_t v___x_117_; uint16_t v___x_118_; uint16_t v___x_119_; uint16_t v___x_120_; uint16_t v___x_121_; uint16_t v___x_122_; uint16_t v___x_123_; uint16_t v___x_124_; uint16_t v___x_125_; uint16_t v___x_126_; uint8_t v___x_127_; 
v___x_117_ = 8;
v___x_118_ = lean_unbox(v_res_107_);
lean_dec(v_res_107_);
v___x_119_ = lean_uint16_shift_left(v___x_118_, v___x_117_);
v___x_120_ = 4;
v___x_121_ = lean_unbox(v_res_110_);
lean_dec(v_res_110_);
v___x_122_ = lean_uint16_shift_left(v___x_121_, v___x_120_);
v___x_123_ = lean_uint16_lor(v___x_119_, v___x_122_);
v___x_124_ = lean_unbox(v_res_113_);
lean_dec(v_res_113_);
v___x_125_ = lean_uint16_lor(v___x_123_, v___x_124_);
v___x_126_ = 3072;
v___x_127_ = lean_uint16_dec_lt(v___x_125_, v___x_126_);
if (v___x_127_ == 0)
{
uint32_t v___x_128_; uint32_t v___x_129_; uint32_t v___x_130_; uint32_t v___x_131_; uint32_t v___x_132_; uint32_t v___x_133_; uint32_t v___x_134_; uint32_t v___x_135_; uint32_t v___x_136_; uint32_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
lean_del_object(v___x_115_);
v___x_128_ = lean_uint16_to_uint32(v_low_58_);
v___x_129_ = 1023;
v___x_130_ = lean_uint32_land(v___x_128_, v___x_129_);
v___x_131_ = 10;
v___x_132_ = lean_uint32_shift_left(v___x_130_, v___x_131_);
v___x_133_ = lean_uint16_to_uint32(v___x_125_);
v___x_134_ = lean_uint32_land(v___x_133_, v___x_129_);
v___x_135_ = lean_uint32_lor(v___x_132_, v___x_134_);
v___x_136_ = 65536;
v___x_137_ = lean_uint32_add(v___x_135_, v___x_136_);
v___x_138_ = lean_uint32_to_nat(v___x_137_);
v___x_139_ = lean_unsigned_to_nat(55296u);
v___x_140_ = lean_nat_dec_lt(v___x_138_, v___x_139_);
v___x_141_ = lean_unsigned_to_nat(57343u);
v___x_142_ = lean_nat_dec_lt(v___x_141_, v___x_138_);
if (v___x_142_ == 0)
{
lean_dec(v___x_138_);
v___y_61_ = v___x_140_;
v___y_62_ = v___x_137_;
v___y_63_ = v_pos_112_;
v___y_64_ = v___x_142_;
goto v___jp_60_;
}
else
{
lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_143_ = lean_unsigned_to_nat(1114112u);
v___x_144_ = lean_nat_dec_lt(v___x_138_, v___x_143_);
lean_dec(v___x_138_);
v___y_61_ = v___x_140_;
v___y_62_ = v___x_137_;
v___y_63_ = v_pos_112_;
v___y_64_ = v___x_144_;
goto v___jp_60_;
}
}
else
{
lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_145_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
if (v_isShared_116_ == 0)
{
lean_ctor_set_tag(v___x_115_, 1);
lean_ctor_set(v___x_115_, 1, v___x_145_);
v___x_147_ = v___x_115_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_pos_112_);
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
lean_dec(v_res_110_);
lean_dec(v_res_107_);
v_pos_150_ = lean_ctor_get(v___x_111_, 0);
v_err_151_ = lean_ctor_get(v___x_111_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_111_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_err_151_);
lean_inc(v_pos_150_);
lean_dec(v___x_111_);
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
lean_dec(v_res_107_);
v_pos_159_ = lean_ctor_get(v___x_108_, 0);
v_err_160_ = lean_ctor_get(v___x_108_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_108_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_err_160_);
lean_inc(v_pos_159_);
lean_dec(v___x_108_);
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
v_pos_168_ = lean_ctor_get(v___x_105_, 0);
v_err_169_ = lean_ctor_get(v___x_105_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_105_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_err_169_);
lean_inc(v_pos_168_);
lean_dec(v___x_105_);
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
}
else
{
lean_dec(v_fst_71_);
goto v___jp_93_;
}
}
v___jp_93_:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_box(0);
v___x_95_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_92_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
return v___x_95_;
}
}
}
else
{
lean_dec(v_fst_71_);
goto v___jp_82_;
}
}
v___jp_82_:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_box(0);
v___x_84_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_84_, 0, v_it_x27_81_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
return v___x_84_;
}
}
}
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_box(0);
v___x_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_188_, 0, v_a_59_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
return v___x_188_;
}
v___jp_60_:
{
if (v___y_61_ == 0)
{
if (v___y_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__1));
v___x_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_66_, 0, v___y_63_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
return v___x_66_;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_box_uint32(v___y_62_);
v___x_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_68_, 0, v___y_63_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
return v___x_68_;
}
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_box_uint32(v___y_62_);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v___y_63_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair___boxed(lean_object* v_low_189_, lean_object* v_a_190_){
_start:
{
uint16_t v_low_boxed_191_; lean_object* v_res_192_; 
v_low_boxed_191_ = lean_unbox(v_low_189_);
v_res_192_ = l_Lean_Json_Parser_finishSurrogatePair(v_low_boxed_191_, v_a_190_);
return v_res_192_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_196_; lean_object* v___x_197_; 
v___x_196_ = 65533;
v___x_197_ = lean_box_uint32(v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_198_; lean_object* v___x_199_; 
v___x_198_ = 9;
v___x_199_ = lean_box_uint32(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_200_; lean_object* v___x_201_; 
v___x_200_ = 13;
v___x_201_ = lean_box_uint32(v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_202_; lean_object* v___x_203_; 
v___x_202_ = 10;
v___x_203_ = lean_box_uint32(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_204_; lean_object* v___x_205_; 
v___x_204_ = 12;
v___x_205_ = lean_box_uint32(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_206_; lean_object* v___x_207_; 
v___x_206_ = 8;
v___x_207_ = lean_box_uint32(v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__7(void){
_start:
{
uint32_t v___x_208_; lean_object* v___x_209_; 
v___x_208_ = 47;
v___x_209_ = lean_box_uint32(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__8(void){
_start:
{
uint32_t v___x_210_; lean_object* v___x_211_; 
v___x_210_ = 34;
v___x_211_ = lean_box_uint32(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__9(void){
_start:
{
uint32_t v___x_212_; lean_object* v___x_213_; 
v___x_212_ = 92;
v___x_213_ = lean_box_uint32(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar(lean_object* v_a_214_){
_start:
{
lean_object* v_fst_215_; lean_object* v_snd_216_; lean_object* v___x_217_; uint8_t v_decide_218_; 
v_fst_215_ = lean_ctor_get(v_a_214_, 0);
v_snd_216_ = lean_ctor_get(v_a_214_, 1);
v___x_217_ = lean_string_utf8_byte_size(v_fst_215_);
v_decide_218_ = lean_nat_dec_eq(v_snd_216_, v___x_217_);
if (v_decide_218_ == 0)
{
lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_373_; 
lean_inc(v_snd_216_);
lean_inc(v_fst_215_);
v_isSharedCheck_373_ = !lean_is_exclusive(v_a_214_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; lean_object* v_unused_375_; 
v_unused_374_ = lean_ctor_get(v_a_214_, 1);
lean_dec(v_unused_374_);
v_unused_375_ = lean_ctor_get(v_a_214_, 0);
lean_dec(v_unused_375_);
v___x_220_ = v_a_214_;
v_isShared_221_ = v_isSharedCheck_373_;
goto v_resetjp_219_;
}
else
{
lean_dec(v_a_214_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_373_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
uint32_t v_c_222_; lean_object* v___x_223_; lean_object* v_it_x27_225_; 
v_c_222_ = lean_string_utf8_get_fast(v_fst_215_, v_snd_216_);
v___x_223_ = lean_string_utf8_next_fast(v_fst_215_, v_snd_216_);
lean_dec(v_snd_216_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v___x_223_);
v_it_x27_225_ = v___x_220_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_fst_215_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_223_);
v_it_x27_225_ = v_reuseFailAlloc_372_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
uint32_t v___x_226_; uint8_t v___x_227_; 
v___x_226_ = 92;
v___x_227_ = lean_uint32_dec_eq(v_c_222_, v___x_226_);
if (v___x_227_ == 0)
{
uint32_t v___x_228_; uint8_t v___x_229_; 
v___x_228_ = 34;
v___x_229_ = lean_uint32_dec_eq(v_c_222_, v___x_228_);
if (v___x_229_ == 0)
{
uint32_t v___x_230_; uint8_t v___x_231_; 
v___x_230_ = 47;
v___x_231_ = lean_uint32_dec_eq(v_c_222_, v___x_230_);
if (v___x_231_ == 0)
{
uint32_t v___x_232_; uint8_t v___x_233_; 
v___x_232_ = 98;
v___x_233_ = lean_uint32_dec_eq(v_c_222_, v___x_232_);
if (v___x_233_ == 0)
{
uint32_t v___x_234_; uint8_t v___x_235_; 
v___x_234_ = 102;
v___x_235_ = lean_uint32_dec_eq(v_c_222_, v___x_234_);
if (v___x_235_ == 0)
{
uint32_t v___x_236_; uint8_t v___x_237_; 
v___x_236_ = 110;
v___x_237_ = lean_uint32_dec_eq(v_c_222_, v___x_236_);
if (v___x_237_ == 0)
{
uint32_t v___x_238_; uint8_t v___x_239_; 
v___x_238_ = 114;
v___x_239_ = lean_uint32_dec_eq(v_c_222_, v___x_238_);
if (v___x_239_ == 0)
{
uint32_t v___x_240_; uint8_t v___x_241_; 
v___x_240_ = 116;
v___x_241_ = lean_uint32_dec_eq(v_c_222_, v___x_240_);
if (v___x_241_ == 0)
{
uint32_t v___x_242_; uint8_t v___x_243_; 
v___x_242_ = 117;
v___x_243_ = lean_uint32_dec_eq(v_c_222_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = ((lean_object*)(l_Lean_Json_Parser_escapedChar___closed__1));
v___x_245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_245_, 0, v_it_x27_225_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Json_Parser_hexChar(v_it_x27_225_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_pos_247_; lean_object* v_res_248_; lean_object* v___x_249_; 
v_pos_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_pos_247_);
v_res_248_ = lean_ctor_get(v___x_246_, 1);
lean_inc(v_res_248_);
lean_dec_ref_known(v___x_246_, 2);
v___x_249_ = l_Lean_Json_Parser_hexChar(v_pos_247_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_pos_250_; lean_object* v_res_251_; lean_object* v___x_252_; 
v_pos_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_pos_250_);
v_res_251_ = lean_ctor_get(v___x_249_, 1);
lean_inc(v_res_251_);
lean_dec_ref_known(v___x_249_, 2);
v___x_252_ = l_Lean_Json_Parser_hexChar(v_pos_250_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_pos_253_; lean_object* v_res_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_328_; 
v_pos_253_ = lean_ctor_get(v___x_252_, 0);
v_res_254_ = lean_ctor_get(v___x_252_, 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_328_ == 0)
{
v___x_256_ = v___x_252_;
v_isShared_257_ = v_isSharedCheck_328_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_res_254_);
lean_inc(v_pos_253_);
lean_dec(v___x_252_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_328_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_Json_Parser_hexChar(v_pos_253_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_pos_259_; lean_object* v_res_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_318_; 
v_pos_259_ = lean_ctor_get(v___x_258_, 0);
v_res_260_ = lean_ctor_get(v___x_258_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_318_ == 0)
{
v___x_262_ = v___x_258_;
v_isShared_263_ = v_isSharedCheck_318_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_res_260_);
lean_inc(v_pos_259_);
lean_dec(v___x_258_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_318_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___y_265_; lean_object* v_pos_266_; uint16_t v___x_274_; uint16_t v___x_275_; uint16_t v___x_276_; uint16_t v___x_277_; uint16_t v___x_278_; uint16_t v___x_279_; uint16_t v___x_280_; uint16_t v___x_281_; uint16_t v___x_282_; uint16_t v___x_283_; uint16_t v___x_284_; uint16_t v___x_285_; uint16_t v___x_286_; uint16_t v___x_287_; uint8_t v___x_288_; 
v___x_274_ = 12;
v___x_275_ = lean_unbox(v_res_248_);
lean_dec(v_res_248_);
v___x_276_ = lean_uint16_shift_left(v___x_275_, v___x_274_);
v___x_277_ = 8;
v___x_278_ = lean_unbox(v_res_251_);
lean_dec(v_res_251_);
v___x_279_ = lean_uint16_shift_left(v___x_278_, v___x_277_);
v___x_280_ = lean_uint16_lor(v___x_276_, v___x_279_);
v___x_281_ = 4;
v___x_282_ = lean_unbox(v_res_254_);
lean_dec(v_res_254_);
v___x_283_ = lean_uint16_shift_left(v___x_282_, v___x_281_);
v___x_284_ = lean_uint16_lor(v___x_280_, v___x_283_);
v___x_285_ = lean_unbox(v_res_260_);
lean_dec(v_res_260_);
v___x_286_ = lean_uint16_lor(v___x_284_, v___x_285_);
v___x_287_ = 55296;
v___x_288_ = lean_uint16_dec_lt(v___x_286_, v___x_287_);
if (v___x_288_ == 0)
{
uint16_t v___x_289_; uint8_t v___x_290_; 
v___x_289_ = 57344;
v___x_290_ = lean_uint16_dec_lt(v___x_286_, v___x_289_);
if (v___x_290_ == 0)
{
uint32_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
lean_del_object(v___x_262_);
v___x_291_ = lean_uint16_to_uint32(v___x_286_);
v___x_292_ = lean_box_uint32(v___x_291_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 1, v___x_292_);
lean_ctor_set(v___x_256_, 0, v_pos_259_);
v___x_294_ = v___x_256_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_pos_259_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
else
{
uint16_t v___x_296_; uint8_t v___x_297_; 
v___x_296_ = 56320;
v___x_297_ = lean_uint16_dec_lt(v___x_286_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_300_; 
lean_del_object(v___x_262_);
v___x_298_ = l_Lean_Json_Parser_escapedChar___boxed__const__1;
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 1, v___x_298_);
lean_ctor_set(v___x_256_, 0, v_pos_259_);
v___x_300_ = v___x_256_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_pos_259_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
else
{
lean_object* v___x_302_; 
lean_del_object(v___x_256_);
lean_inc(v_pos_259_);
v___x_302_ = l_Lean_Json_Parser_finishSurrogatePair(v___x_286_, v_pos_259_);
if (lean_obj_tag(v___x_302_) == 0)
{
if (lean_obj_tag(v___x_302_) == 0)
{
lean_del_object(v___x_262_);
lean_dec(v_pos_259_);
return v___x_302_;
}
else
{
lean_object* v_pos_303_; 
v_pos_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_pos_303_);
v___y_265_ = v___x_302_;
v_pos_266_ = v_pos_303_;
goto v___jp_264_;
}
}
else
{
lean_object* v_err_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
v_err_304_ = lean_ctor_get(v___x_302_, 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; 
v_unused_312_ = lean_ctor_get(v___x_302_, 0);
lean_dec(v_unused_312_);
v___x_306_ = v___x_302_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_err_304_);
lean_dec(v___x_302_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
lean_inc(v_pos_259_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v_pos_259_);
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_pos_259_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_err_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_inc(v_pos_259_);
v___y_265_ = v___x_309_;
v_pos_266_ = v_pos_259_;
goto v___jp_264_;
}
}
}
}
}
}
else
{
uint32_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
lean_del_object(v___x_262_);
v___x_313_ = lean_uint16_to_uint32(v___x_286_);
v___x_314_ = lean_box_uint32(v___x_313_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 1, v___x_314_);
lean_ctor_set(v___x_256_, 0, v_pos_259_);
v___x_316_ = v___x_256_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_pos_259_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
v___jp_264_:
{
lean_object* v_snd_267_; lean_object* v_snd_268_; uint8_t v_decide_269_; 
v_snd_267_ = lean_ctor_get(v_pos_259_, 1);
lean_inc(v_snd_267_);
lean_dec(v_pos_259_);
v_snd_268_ = lean_ctor_get(v_pos_266_, 1);
v_decide_269_ = lean_nat_dec_eq(v_snd_267_, v_snd_268_);
lean_dec(v_snd_267_);
if (v_decide_269_ == 0)
{
lean_dec_ref(v_pos_266_);
lean_del_object(v___x_262_);
return v___y_265_;
}
else
{
lean_object* v___x_270_; lean_object* v___x_272_; 
lean_dec_ref(v___y_265_);
v___x_270_ = l_Lean_Json_Parser_escapedChar___boxed__const__1;
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_270_);
lean_ctor_set(v___x_262_, 0, v_pos_266_);
v___x_272_ = v___x_262_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_pos_266_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
else
{
lean_object* v_pos_319_; lean_object* v_err_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_del_object(v___x_256_);
lean_dec(v_res_254_);
lean_dec(v_res_251_);
lean_dec(v_res_248_);
v_pos_319_ = lean_ctor_get(v___x_258_, 0);
v_err_320_ = lean_ctor_get(v___x_258_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_258_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_err_320_);
lean_inc(v_pos_319_);
lean_dec(v___x_258_);
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
}
else
{
lean_object* v_pos_329_; lean_object* v_err_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec(v_res_251_);
lean_dec(v_res_248_);
v_pos_329_ = lean_ctor_get(v___x_252_, 0);
v_err_330_ = lean_ctor_get(v___x_252_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_252_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_err_330_);
lean_inc(v_pos_329_);
lean_dec(v___x_252_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_pos_329_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_err_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
else
{
lean_object* v_pos_338_; lean_object* v_err_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec(v_res_248_);
v_pos_338_ = lean_ctor_get(v___x_249_, 0);
v_err_339_ = lean_ctor_get(v___x_249_, 1);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_249_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_err_339_);
lean_inc(v_pos_338_);
lean_dec(v___x_249_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_pos_338_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_err_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
else
{
lean_object* v_pos_347_; lean_object* v_err_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
v_pos_347_ = lean_ctor_get(v___x_246_, 0);
v_err_348_ = lean_ctor_get(v___x_246_, 1);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_246_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_err_348_);
lean_inc(v_pos_347_);
lean_dec(v___x_246_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_pos_347_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_err_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = l_Lean_Json_Parser_escapedChar___boxed__const__2;
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v_it_x27_225_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
return v___x_357_;
}
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = l_Lean_Json_Parser_escapedChar___boxed__const__3;
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_it_x27_225_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
return v___x_359_;
}
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = l_Lean_Json_Parser_escapedChar___boxed__const__4;
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_it_x27_225_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
return v___x_361_;
}
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = l_Lean_Json_Parser_escapedChar___boxed__const__5;
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_it_x27_225_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
return v___x_363_;
}
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = l_Lean_Json_Parser_escapedChar___boxed__const__6;
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_it_x27_225_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
return v___x_365_;
}
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = l_Lean_Json_Parser_escapedChar___boxed__const__7;
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v_it_x27_225_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
return v___x_367_;
}
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = l_Lean_Json_Parser_escapedChar___boxed__const__8;
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v_it_x27_225_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
return v___x_369_;
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = l_Lean_Json_Parser_escapedChar___boxed__const__9;
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v_it_x27_225_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
return v___x_371_;
}
}
}
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_box(0);
v___x_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_377_, 0, v_a_214_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_strCore(lean_object* v_acc_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_fst_383_; lean_object* v_snd_384_; lean_object* v___x_385_; uint8_t v_decide_386_; 
v_fst_383_ = lean_ctor_get(v_a_382_, 0);
v_snd_384_ = lean_ctor_get(v_a_382_, 1);
v___x_385_ = lean_string_utf8_byte_size(v_fst_383_);
v_decide_386_ = lean_nat_dec_eq(v_snd_384_, v___x_385_);
if (v_decide_386_ == 0)
{
lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_428_; 
lean_inc(v_snd_384_);
lean_inc(v_fst_383_);
v_isSharedCheck_428_ = !lean_is_exclusive(v_a_382_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; lean_object* v_unused_430_; 
v_unused_429_ = lean_ctor_get(v_a_382_, 1);
lean_dec(v_unused_429_);
v_unused_430_ = lean_ctor_get(v_a_382_, 0);
lean_dec(v_unused_430_);
v___x_388_ = v_a_382_;
v_isShared_389_ = v_isSharedCheck_428_;
goto v_resetjp_387_;
}
else
{
lean_dec(v_a_382_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_428_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
uint32_t v___x_390_; uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_390_ = lean_string_utf8_get_fast(v_fst_383_, v_snd_384_);
v___x_391_ = 34;
v___x_392_ = lean_uint32_dec_eq(v___x_390_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_393_ = lean_string_utf8_next_fast(v_fst_383_, v_snd_384_);
lean_dec(v_snd_384_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v___x_393_);
v___x_395_ = v___x_388_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_fst_383_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___x_393_);
v___x_395_ = v_reuseFailAlloc_422_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
uint32_t v___x_399_; uint8_t v___x_400_; 
v___x_399_ = 92;
v___x_400_ = lean_uint32_dec_eq(v___x_390_, v___x_399_);
if (v___x_400_ == 0)
{
uint32_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = 32;
v___x_402_ = lean_uint32_dec_le(v___x_401_, v___x_390_);
if (v___x_402_ == 0)
{
lean_dec_ref(v_acc_381_);
goto v___jp_396_;
}
else
{
uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 1114111;
v___x_404_ = lean_uint32_dec_le(v___x_390_, v___x_403_);
if (v___x_404_ == 0)
{
lean_dec_ref(v_acc_381_);
goto v___jp_396_;
}
else
{
lean_object* v___x_405_; 
v___x_405_ = lean_string_push(v_acc_381_, v___x_390_);
v_acc_381_ = v___x_405_;
v_a_382_ = v___x_395_;
goto _start;
}
}
}
else
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Json_Parser_escapedChar(v___x_395_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_pos_408_; lean_object* v_res_409_; uint32_t v___x_410_; lean_object* v___x_411_; 
v_pos_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_pos_408_);
v_res_409_ = lean_ctor_get(v___x_407_, 1);
lean_inc(v_res_409_);
lean_dec_ref_known(v___x_407_, 2);
v___x_410_ = lean_unbox_uint32(v_res_409_);
lean_dec(v_res_409_);
v___x_411_ = lean_string_push(v_acc_381_, v___x_410_);
v_acc_381_ = v___x_411_;
v_a_382_ = v_pos_408_;
goto _start;
}
else
{
lean_object* v_pos_413_; lean_object* v_err_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec_ref(v_acc_381_);
v_pos_413_ = lean_ctor_get(v___x_407_, 0);
v_err_414_ = lean_ctor_get(v___x_407_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_407_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_err_414_);
lean_inc(v_pos_413_);
lean_dec(v___x_407_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_pos_413_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_err_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
v___jp_396_:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l_Lean_Json_Parser_strCore___closed__1));
v___x_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_395_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
return v___x_398_;
}
}
}
else
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = lean_string_utf8_next_fast(v_fst_383_, v_snd_384_);
lean_dec(v_snd_384_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v___x_423_);
v___x_425_ = v___x_388_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_fst_383_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v___x_423_);
v___x_425_ = v_reuseFailAlloc_427_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; 
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v_acc_381_);
return v___x_426_;
}
}
}
}
else
{
lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec_ref(v_acc_381_);
v___x_431_ = lean_box(0);
v___x_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_432_, 0, v_a_382_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_str(lean_object* v_a_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_435_ = l_Lean_Json_Parser_strCore(v___x_434_, v_a_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCore(lean_object* v_acc_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_fst_438_; lean_object* v_snd_439_; lean_object* v___x_440_; uint8_t v_decide_441_; 
v_fst_438_ = lean_ctor_get(v_a_437_, 0);
v_snd_439_ = lean_ctor_get(v_a_437_, 1);
v___x_440_ = lean_string_utf8_byte_size(v_fst_438_);
v_decide_441_ = lean_nat_dec_eq(v_snd_439_, v___x_440_);
if (v_decide_441_ == 0)
{
uint32_t v___x_442_; uint32_t v___x_443_; uint8_t v___x_444_; 
v___x_442_ = lean_string_utf8_get_fast(v_fst_438_, v_snd_439_);
v___x_443_ = 48;
v___x_444_ = lean_uint32_dec_le(v___x_443_, v___x_442_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v_a_437_);
lean_ctor_set(v___x_445_, 1, v_acc_436_);
return v___x_445_;
}
else
{
uint32_t v___x_446_; uint8_t v___x_447_; 
v___x_446_ = 57;
v___x_447_ = lean_uint32_dec_le(v___x_442_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v_a_437_);
lean_ctor_set(v___x_448_, 1, v_acc_436_);
return v___x_448_;
}
else
{
lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_462_; 
lean_inc(v_snd_439_);
lean_inc(v_fst_438_);
v_isSharedCheck_462_ = !lean_is_exclusive(v_a_437_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; lean_object* v_unused_464_; 
v_unused_463_ = lean_ctor_get(v_a_437_, 1);
lean_dec(v_unused_463_);
v_unused_464_ = lean_ctor_get(v_a_437_, 0);
lean_dec(v_unused_464_);
v___x_450_ = v_a_437_;
v_isShared_451_ = v_isSharedCheck_462_;
goto v_resetjp_449_;
}
else
{
lean_dec(v_a_437_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_462_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_452_ = lean_string_utf8_next_fast(v_fst_438_, v_snd_439_);
lean_dec(v_snd_439_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___x_452_);
v___x_454_ = v___x_450_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_fst_438_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_452_);
v___x_454_ = v_reuseFailAlloc_461_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; uint32_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_455_ = lean_unsigned_to_nat(10u);
v___x_456_ = lean_nat_mul(v___x_455_, v_acc_436_);
lean_dec(v_acc_436_);
v___x_457_ = lean_uint32_sub(v___x_442_, v___x_443_);
v___x_458_ = lean_uint32_to_nat(v___x_457_);
v___x_459_ = lean_nat_add(v___x_456_, v___x_458_);
lean_dec(v___x_458_);
lean_dec(v___x_456_);
v_acc_436_ = v___x_459_;
v_a_437_ = v___x_454_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_465_; 
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v_a_437_);
lean_ctor_set(v___x_465_, 1, v_acc_436_);
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCoreNumDigits(lean_object* v_acc_466_, lean_object* v_digits_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_fst_472_; lean_object* v_snd_473_; lean_object* v___x_474_; uint8_t v_decide_475_; 
v_fst_472_ = lean_ctor_get(v_a_468_, 0);
v_snd_473_ = lean_ctor_get(v_a_468_, 1);
v___x_474_ = lean_string_utf8_byte_size(v_fst_472_);
v_decide_475_ = lean_nat_dec_eq(v_snd_473_, v___x_474_);
if (v_decide_475_ == 0)
{
uint32_t v___x_476_; uint32_t v___x_477_; uint8_t v___x_478_; 
v___x_476_ = lean_string_utf8_get_fast(v_fst_472_, v_snd_473_);
v___x_477_ = 48;
v___x_478_ = lean_uint32_dec_le(v___x_477_, v___x_476_);
if (v___x_478_ == 0)
{
goto v___jp_469_;
}
else
{
uint32_t v___x_479_; uint8_t v___x_480_; 
v___x_479_ = 57;
v___x_480_ = lean_uint32_dec_le(v___x_476_, v___x_479_);
if (v___x_480_ == 0)
{
goto v___jp_469_;
}
else
{
lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_496_; 
lean_inc(v_snd_473_);
lean_inc(v_fst_472_);
v_isSharedCheck_496_ = !lean_is_exclusive(v_a_468_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; lean_object* v_unused_498_; 
v_unused_497_ = lean_ctor_get(v_a_468_, 1);
lean_dec(v_unused_497_);
v_unused_498_ = lean_ctor_get(v_a_468_, 0);
lean_dec(v_unused_498_);
v___x_482_ = v_a_468_;
v_isShared_483_ = v_isSharedCheck_496_;
goto v_resetjp_481_;
}
else
{
lean_dec(v_a_468_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_496_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = lean_string_utf8_next_fast(v_fst_472_, v_snd_473_);
lean_dec(v_snd_473_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 1, v___x_484_);
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_fst_472_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_495_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; uint32_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_487_ = lean_unsigned_to_nat(10u);
v___x_488_ = lean_nat_mul(v___x_487_, v_acc_466_);
lean_dec(v_acc_466_);
v___x_489_ = lean_uint32_sub(v___x_476_, v___x_477_);
v___x_490_ = lean_uint32_to_nat(v___x_489_);
v___x_491_ = lean_nat_add(v___x_488_, v___x_490_);
lean_dec(v___x_490_);
lean_dec(v___x_488_);
v___x_492_ = lean_unsigned_to_nat(1u);
v___x_493_ = lean_nat_add(v_digits_467_, v___x_492_);
lean_dec(v_digits_467_);
v_acc_466_ = v___x_491_;
v_digits_467_ = v___x_493_;
v_a_468_ = v___x_486_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v_acc_466_);
lean_ctor_set(v___x_499_, 1, v_digits_467_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v_a_468_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
return v___x_500_;
}
v___jp_469_:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v_acc_466_);
lean_ctor_set(v___x_470_, 1, v_digits_467_);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v_a_468_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg(lean_object* v_desc_502_, lean_object* v_inst_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_fst_505_; lean_object* v_snd_506_; lean_object* v___x_507_; uint8_t v_decide_508_; 
v_fst_505_ = lean_ctor_get(v_a_504_, 0);
v_snd_506_ = lean_ctor_get(v_a_504_, 1);
v___x_507_ = lean_string_utf8_byte_size(v_fst_505_);
v_decide_508_ = lean_nat_dec_eq(v_snd_506_, v___x_507_);
if (v_decide_508_ == 0)
{
uint32_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_509_ = lean_string_utf8_get_fast(v_fst_505_, v_snd_506_);
v___x_510_ = lean_box_uint32(v___x_509_);
v___x_511_ = lean_apply_1(v_inst_503_, v___x_510_);
v___x_512_ = lean_unbox(v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_513_ = ((lean_object*)(l_Lean_Json_Parser_lookahead___redArg___closed__0));
v___x_514_ = lean_string_append(v___x_513_, v_desc_502_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
v___x_516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_516_, 0, v_a_504_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
return v___x_516_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_box(0);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_a_504_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
return v___x_518_;
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec_ref(v_inst_503_);
v___x_519_ = lean_box(0);
v___x_520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_520_, 0, v_a_504_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg___boxed(lean_object* v_desc_521_, lean_object* v_inst_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Json_Parser_lookahead___redArg(v_desc_521_, v_inst_522_, v_a_523_);
lean_dec_ref(v_desc_521_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead(lean_object* v_p_525_, lean_object* v_desc_526_, lean_object* v_inst_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_fst_529_; lean_object* v_snd_530_; lean_object* v___x_531_; uint8_t v_decide_532_; 
v_fst_529_ = lean_ctor_get(v_a_528_, 0);
v_snd_530_ = lean_ctor_get(v_a_528_, 1);
v___x_531_ = lean_string_utf8_byte_size(v_fst_529_);
v_decide_532_ = lean_nat_dec_eq(v_snd_530_, v___x_531_);
if (v_decide_532_ == 0)
{
uint32_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_533_ = lean_string_utf8_get_fast(v_fst_529_, v_snd_530_);
v___x_534_ = lean_box_uint32(v___x_533_);
v___x_535_ = lean_apply_1(v_inst_527_, v___x_534_);
v___x_536_ = lean_unbox(v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_537_ = ((lean_object*)(l_Lean_Json_Parser_lookahead___redArg___closed__0));
v___x_538_ = lean_string_append(v___x_537_, v_desc_526_);
v___x_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
v___x_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_540_, 0, v_a_528_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
return v___x_540_;
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_box(0);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v_a_528_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
return v___x_542_;
}
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec_ref(v_inst_527_);
v___x_543_ = lean_box(0);
v___x_544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_544_, 0, v_a_528_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___boxed(lean_object* v_p_545_, lean_object* v_desc_546_, lean_object* v_inst_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Json_Parser_lookahead(v_p_545_, v_desc_546_, v_inst_547_, v_a_548_);
lean_dec_ref(v_desc_546_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNonZero(lean_object* v_a_553_){
_start:
{
uint8_t v___y_555_; lean_object* v_fst_560_; lean_object* v_snd_561_; lean_object* v___x_562_; uint8_t v_decide_563_; 
v_fst_560_ = lean_ctor_get(v_a_553_, 0);
v_snd_561_ = lean_ctor_get(v_a_553_, 1);
v___x_562_ = lean_string_utf8_byte_size(v_fst_560_);
v_decide_563_ = lean_nat_dec_eq(v_snd_561_, v___x_562_);
if (v_decide_563_ == 0)
{
uint32_t v___x_564_; uint32_t v___x_565_; uint8_t v___x_566_; 
v___x_564_ = lean_string_utf8_get_fast(v_fst_560_, v_snd_561_);
v___x_565_ = 49;
v___x_566_ = lean_uint32_dec_le(v___x_565_, v___x_564_);
if (v___x_566_ == 0)
{
v___y_555_ = v___x_566_;
goto v___jp_554_;
}
else
{
uint32_t v___x_567_; uint8_t v___x_568_; 
v___x_567_ = 57;
v___x_568_ = lean_uint32_dec_le(v___x_564_, v___x_567_);
v___y_555_ = v___x_568_;
goto v___jp_554_;
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_box(0);
v___x_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_570_, 0, v_a_553_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
return v___x_570_;
}
v___jp_554_:
{
if (v___y_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_557_, 0, v_a_553_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = l_Lean_Json_Parser_natCore(v___x_558_, v_a_553_);
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNumDigits(lean_object* v_a_574_){
_start:
{
uint8_t v___y_576_; lean_object* v_fst_581_; lean_object* v_snd_582_; lean_object* v___x_583_; uint8_t v_decide_584_; 
v_fst_581_ = lean_ctor_get(v_a_574_, 0);
v_snd_582_ = lean_ctor_get(v_a_574_, 1);
v___x_583_ = lean_string_utf8_byte_size(v_fst_581_);
v_decide_584_ = lean_nat_dec_eq(v_snd_582_, v___x_583_);
if (v_decide_584_ == 0)
{
uint32_t v___x_585_; uint32_t v___x_586_; uint8_t v___x_587_; 
v___x_585_ = lean_string_utf8_get_fast(v_fst_581_, v_snd_582_);
v___x_586_ = 48;
v___x_587_ = lean_uint32_dec_le(v___x_586_, v___x_585_);
if (v___x_587_ == 0)
{
v___y_576_ = v___x_587_;
goto v___jp_575_;
}
else
{
uint32_t v___x_588_; uint8_t v___x_589_; 
v___x_588_ = 57;
v___x_589_ = lean_uint32_dec_le(v___x_585_, v___x_588_);
v___y_576_ = v___x_589_;
goto v___jp_575_;
}
}
else
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_box(0);
v___x_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_591_, 0, v_a_574_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
return v___x_591_;
}
v___jp_575_:
{
if (v___y_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_578_, 0, v_a_574_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
return v___x_578_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_579_, v___x_579_, v_a_574_);
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natMaybeZero(lean_object* v_a_595_){
_start:
{
uint8_t v___y_597_; lean_object* v_fst_602_; lean_object* v_snd_603_; lean_object* v___x_604_; uint8_t v_decide_605_; 
v_fst_602_ = lean_ctor_get(v_a_595_, 0);
v_snd_603_ = lean_ctor_get(v_a_595_, 1);
v___x_604_ = lean_string_utf8_byte_size(v_fst_602_);
v_decide_605_ = lean_nat_dec_eq(v_snd_603_, v___x_604_);
if (v_decide_605_ == 0)
{
uint32_t v___x_606_; uint32_t v___x_607_; uint8_t v___x_608_; 
v___x_606_ = lean_string_utf8_get_fast(v_fst_602_, v_snd_603_);
v___x_607_ = 48;
v___x_608_ = lean_uint32_dec_le(v___x_607_, v___x_606_);
if (v___x_608_ == 0)
{
v___y_597_ = v___x_608_;
goto v___jp_596_;
}
else
{
uint32_t v___x_609_; uint8_t v___x_610_; 
v___x_609_ = 57;
v___x_610_ = lean_uint32_dec_le(v___x_606_, v___x_609_);
v___y_597_ = v___x_610_;
goto v___jp_596_;
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_box(0);
v___x_612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_612_, 0, v_a_595_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
return v___x_612_;
}
v___jp_596_:
{
if (v___y_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_599_, 0, v_a_595_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
return v___x_599_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = l_Lean_Json_Parser_natCore(v___x_600_, v_a_595_);
return v___x_601_;
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_numSign___closed__0(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_to_int(v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_Json_Parser_numSign___closed__1(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v___x_616_ = lean_int_neg(v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numSign(lean_object* v_a_617_){
_start:
{
lean_object* v_fst_618_; lean_object* v_snd_619_; lean_object* v___x_620_; uint8_t v_decide_621_; 
v_fst_618_ = lean_ctor_get(v_a_617_, 0);
v_snd_619_ = lean_ctor_get(v_a_617_, 1);
v___x_620_ = lean_string_utf8_byte_size(v_fst_618_);
v_decide_621_ = lean_nat_dec_eq(v_snd_619_, v___x_620_);
if (v_decide_621_ == 0)
{
uint32_t v___x_622_; uint32_t v___x_623_; uint8_t v___x_624_; 
v___x_622_ = lean_string_utf8_get_fast(v_fst_618_, v_snd_619_);
v___x_623_ = 45;
v___x_624_ = lean_uint32_dec_eq(v___x_622_, v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v_a_617_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
return v___x_626_;
}
else
{
lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_636_; 
lean_inc(v_snd_619_);
lean_inc(v_fst_618_);
v_isSharedCheck_636_ = !lean_is_exclusive(v_a_617_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; lean_object* v_unused_638_; 
v_unused_637_ = lean_ctor_get(v_a_617_, 1);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v_a_617_, 0);
lean_dec(v_unused_638_);
v___x_628_ = v_a_617_;
v_isShared_629_ = v_isSharedCheck_636_;
goto v_resetjp_627_;
}
else
{
lean_dec(v_a_617_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_636_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = lean_string_utf8_next_fast(v_fst_618_, v_snd_619_);
lean_dec(v_snd_619_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v___x_630_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_fst_618_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v___x_630_);
v___x_632_ = v_reuseFailAlloc_635_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
return v___x_634_;
}
}
}
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_box(0);
v___x_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_640_, 0, v_a_617_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_nat(lean_object* v_a_641_){
_start:
{
uint8_t v___y_643_; lean_object* v_fst_648_; lean_object* v_snd_649_; lean_object* v___x_650_; uint8_t v_decide_651_; 
v_fst_648_ = lean_ctor_get(v_a_641_, 0);
v_snd_649_ = lean_ctor_get(v_a_641_, 1);
v___x_650_ = lean_string_utf8_byte_size(v_fst_648_);
v_decide_651_ = lean_nat_dec_eq(v_snd_649_, v___x_650_);
if (v_decide_651_ == 0)
{
uint32_t v___x_652_; uint32_t v___x_653_; uint8_t v___x_654_; 
v___x_652_ = lean_string_utf8_get_fast(v_fst_648_, v_snd_649_);
v___x_653_ = 48;
v___x_654_ = lean_uint32_dec_eq(v___x_652_, v___x_653_);
if (v___x_654_ == 0)
{
uint32_t v___x_655_; uint8_t v___x_656_; 
v___x_655_ = 49;
v___x_656_ = lean_uint32_dec_le(v___x_655_, v___x_652_);
if (v___x_656_ == 0)
{
v___y_643_ = v___x_656_;
goto v___jp_642_;
}
else
{
uint32_t v___x_657_; uint8_t v___x_658_; 
v___x_657_ = 57;
v___x_658_ = lean_uint32_dec_le(v___x_652_, v___x_657_);
v___y_643_ = v___x_658_;
goto v___jp_642_;
}
}
else
{
lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_668_; 
lean_inc(v_snd_649_);
lean_inc(v_fst_648_);
v_isSharedCheck_668_ = !lean_is_exclusive(v_a_641_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; lean_object* v_unused_670_; 
v_unused_669_ = lean_ctor_get(v_a_641_, 1);
lean_dec(v_unused_669_);
v_unused_670_ = lean_ctor_get(v_a_641_, 0);
lean_dec(v_unused_670_);
v___x_660_ = v_a_641_;
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
else
{
lean_dec(v_a_641_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = lean_string_utf8_next_fast(v_fst_648_, v_snd_649_);
lean_dec(v_snd_649_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v___x_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_fst_648_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_662_);
v___x_664_ = v_reuseFailAlloc_667_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
return v___x_666_;
}
}
}
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_box(0);
v___x_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_672_, 0, v_a_641_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
return v___x_672_;
}
v___jp_642_:
{
if (v___y_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_645_, 0, v_a_641_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
return v___x_645_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = l_Lean_Json_Parser_natCore(v___x_646_, v_a_641_);
return v___x_647_;
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_numWithDecimals___closed__0(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = l_System_Platform_numBits;
v___x_674_ = lean_unsigned_to_nat(2u);
v___x_675_ = lean_nat_pow(v___x_674_, v___x_673_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numWithDecimals(lean_object* v_a_679_){
_start:
{
lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; uint8_t v___y_684_; lean_object* v___y_731_; lean_object* v___y_735_; lean_object* v_pos_736_; lean_object* v_fst_737_; lean_object* v_snd_738_; lean_object* v_res_739_; lean_object* v___y_762_; lean_object* v___y_763_; uint8_t v___y_764_; lean_object* v_pos_783_; lean_object* v_fst_784_; lean_object* v_snd_785_; lean_object* v_res_786_; lean_object* v_fst_801_; lean_object* v_snd_802_; lean_object* v___x_803_; uint8_t v_decide_804_; 
v_fst_801_ = lean_ctor_get(v_a_679_, 0);
v_snd_802_ = lean_ctor_get(v_a_679_, 1);
v___x_803_ = lean_string_utf8_byte_size(v_fst_801_);
v_decide_804_ = lean_nat_dec_eq(v_snd_802_, v___x_803_);
if (v_decide_804_ == 0)
{
uint32_t v___x_805_; uint32_t v___x_806_; uint8_t v___x_807_; 
lean_inc(v_snd_802_);
lean_inc(v_fst_801_);
v___x_805_ = lean_string_utf8_get_fast(v_fst_801_, v_snd_802_);
v___x_806_ = 45;
v___x_807_ = lean_uint32_dec_eq(v___x_805_, v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; 
v___x_808_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v_pos_783_ = v_a_679_;
v_fst_784_ = v_fst_801_;
v_snd_785_ = v_snd_802_;
v_res_786_ = v___x_808_;
goto v___jp_782_;
}
else
{
lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_817_; 
v_isSharedCheck_817_ = !lean_is_exclusive(v_a_679_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; lean_object* v_unused_819_; 
v_unused_818_ = lean_ctor_get(v_a_679_, 1);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v_a_679_, 0);
lean_dec(v_unused_819_);
v___x_810_ = v_a_679_;
v_isShared_811_ = v_isSharedCheck_817_;
goto v_resetjp_809_;
}
else
{
lean_dec(v_a_679_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_817_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = lean_string_utf8_next_fast(v_fst_801_, v_snd_802_);
lean_dec(v_snd_802_);
lean_inc(v_fst_801_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 1, v___x_812_);
v___x_814_ = v___x_810_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_fst_801_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v___x_812_);
v___x_814_ = v_reuseFailAlloc_816_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; 
v___x_815_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v_pos_783_ = v___x_814_;
v_fst_784_ = v_fst_801_;
v_snd_785_ = v___x_812_;
v_res_786_ = v___x_815_;
goto v___jp_782_;
}
}
}
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_box(0);
v___x_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_821_, 0, v_a_679_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
return v___x_821_;
}
v___jp_680_:
{
if (v___y_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec(v___y_682_);
v___x_685_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_686_, 0, v___y_681_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
return v___x_686_;
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_687_, v___x_687_, v___y_681_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_res_689_; lean_object* v_pos_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_720_; 
v_res_689_ = lean_ctor_get(v___x_688_, 1);
v_pos_690_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_720_ == 0)
{
v___x_692_ = v___x_688_;
v_isShared_693_ = v_isSharedCheck_720_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_res_689_);
lean_inc(v_pos_690_);
lean_dec(v___x_688_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_720_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_fst_694_; lean_object* v_snd_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_719_; 
v_fst_694_ = lean_ctor_get(v_res_689_, 0);
v_snd_695_ = lean_ctor_get(v_res_689_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_res_689_);
if (v_isSharedCheck_719_ == 0)
{
v___x_697_ = v_res_689_;
v_isShared_698_ = v_isSharedCheck_719_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_snd_695_);
lean_inc(v_fst_694_);
lean_dec(v_res_689_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_719_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_700_ = lean_nat_dec_lt(v___x_699_, v_snd_695_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_701_ = lean_nat_to_int(v___y_682_);
v___x_702_ = lean_unsigned_to_nat(10u);
v___x_703_ = lean_nat_pow(v___x_702_, v_snd_695_);
v___x_704_ = lean_nat_to_int(v___x_703_);
v___x_705_ = lean_int_mul(v___x_701_, v___x_704_);
lean_dec(v___x_704_);
lean_dec(v___x_701_);
v___x_706_ = lean_nat_to_int(v_fst_694_);
v___x_707_ = lean_int_add(v___x_705_, v___x_706_);
lean_dec(v___x_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_int_mul(v___y_683_, v___x_707_);
lean_dec(v___x_707_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_708_);
v___x_710_ = v___x_697_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_snd_695_);
v___x_710_ = v_reuseFailAlloc_714_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_712_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_710_);
v___x_712_ = v___x_692_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_pos_690_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
else
{
lean_object* v___x_715_; lean_object* v___x_717_; 
lean_del_object(v___x_697_);
lean_dec(v_snd_695_);
lean_dec(v_fst_694_);
lean_dec(v___y_682_);
v___x_715_ = ((lean_object*)(l_Lean_Json_Parser_numWithDecimals___closed__2));
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 1);
lean_ctor_set(v___x_692_, 1, v___x_715_);
v___x_717_ = v___x_692_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_pos_690_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
else
{
lean_object* v_pos_721_; lean_object* v_err_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v___y_682_);
v_pos_721_ = lean_ctor_get(v___x_688_, 0);
v_err_722_ = lean_ctor_get(v___x_688_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_688_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_err_722_);
lean_inc(v_pos_721_);
lean_dec(v___x_688_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_pos_721_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_err_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
v___jp_730_:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_box(0);
v___x_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_733_, 0, v___y_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
return v___x_733_;
}
v___jp_734_:
{
lean_object* v___x_740_; uint8_t v_decide_741_; 
v___x_740_ = lean_string_utf8_byte_size(v_fst_737_);
v_decide_741_ = lean_nat_dec_eq(v_snd_738_, v___x_740_);
if (v_decide_741_ == 0)
{
uint32_t v___x_742_; uint32_t v___x_743_; uint8_t v___x_744_; 
v___x_742_ = lean_string_utf8_get_fast(v_fst_737_, v_snd_738_);
v___x_743_ = 46;
v___x_744_ = lean_uint32_dec_eq(v___x_742_, v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec(v_snd_738_);
lean_dec(v_fst_737_);
v___x_745_ = lean_nat_to_int(v_res_739_);
v___x_746_ = lean_int_mul(v___y_735_, v___x_745_);
lean_dec(v___x_745_);
v___x_747_ = l_Lean_JsonNumber_fromInt(v___x_746_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v_pos_736_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
return v___x_748_;
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v_decide_751_; 
lean_dec_ref(v_pos_736_);
v___x_749_ = lean_string_utf8_next_fast(v_fst_737_, v_snd_738_);
lean_dec(v_snd_738_);
lean_inc(v_fst_737_);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v_fst_737_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v_decide_751_ = lean_nat_dec_eq(v___x_749_, v___x_740_);
if (v_decide_751_ == 0)
{
if (v___x_744_ == 0)
{
lean_dec(v_res_739_);
lean_dec(v_fst_737_);
v___y_731_ = v___x_750_;
goto v___jp_730_;
}
else
{
uint32_t v___x_752_; uint32_t v___x_753_; uint8_t v___x_754_; 
v___x_752_ = lean_string_utf8_get_fast(v_fst_737_, v___x_749_);
lean_dec(v_fst_737_);
v___x_753_ = 48;
v___x_754_ = lean_uint32_dec_le(v___x_753_, v___x_752_);
if (v___x_754_ == 0)
{
v___y_681_ = v___x_750_;
v___y_682_ = v_res_739_;
v___y_683_ = v___y_735_;
v___y_684_ = v___x_754_;
goto v___jp_680_;
}
else
{
uint32_t v___x_755_; uint8_t v___x_756_; 
v___x_755_ = 57;
v___x_756_ = lean_uint32_dec_le(v___x_752_, v___x_755_);
v___y_681_ = v___x_750_;
v___y_682_ = v_res_739_;
v___y_683_ = v___y_735_;
v___y_684_ = v___x_756_;
goto v___jp_680_;
}
}
}
else
{
lean_dec(v_res_739_);
lean_dec(v_fst_737_);
v___y_731_ = v___x_750_;
goto v___jp_730_;
}
}
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
lean_dec(v_snd_738_);
lean_dec(v_fst_737_);
v___x_757_ = lean_nat_to_int(v_res_739_);
v___x_758_ = lean_int_mul(v___y_735_, v___x_757_);
lean_dec(v___x_757_);
v___x_759_ = l_Lean_JsonNumber_fromInt(v___x_758_);
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v_pos_736_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
return v___x_760_;
}
}
v___jp_761_:
{
if (v___y_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_766_, 0, v___y_763_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
return v___x_766_;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = l_Lean_Json_Parser_natCore(v___x_767_, v___y_763_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_pos_769_; lean_object* v_res_770_; lean_object* v_fst_771_; lean_object* v_snd_772_; 
v_pos_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_pos_769_);
v_res_770_ = lean_ctor_get(v___x_768_, 1);
lean_inc(v_res_770_);
lean_dec_ref_known(v___x_768_, 2);
v_fst_771_ = lean_ctor_get(v_pos_769_, 0);
lean_inc(v_fst_771_);
v_snd_772_ = lean_ctor_get(v_pos_769_, 1);
lean_inc(v_snd_772_);
v___y_735_ = v___y_762_;
v_pos_736_ = v_pos_769_;
v_fst_737_ = v_fst_771_;
v_snd_738_ = v_snd_772_;
v_res_739_ = v_res_770_;
goto v___jp_734_;
}
else
{
lean_object* v_pos_773_; lean_object* v_err_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
v_pos_773_ = lean_ctor_get(v___x_768_, 0);
v_err_774_ = lean_ctor_get(v___x_768_, 1);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_768_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_err_774_);
lean_inc(v_pos_773_);
lean_dec(v___x_768_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_pos_773_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_err_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
v___jp_782_:
{
lean_object* v___x_787_; uint8_t v_decide_788_; 
v___x_787_ = lean_string_utf8_byte_size(v_fst_784_);
v_decide_788_ = lean_nat_dec_eq(v_snd_785_, v___x_787_);
if (v_decide_788_ == 0)
{
uint32_t v___x_789_; uint32_t v___x_790_; uint8_t v___x_791_; 
v___x_789_ = lean_string_utf8_get_fast(v_fst_784_, v_snd_785_);
v___x_790_ = 48;
v___x_791_ = lean_uint32_dec_eq(v___x_789_, v___x_790_);
if (v___x_791_ == 0)
{
uint32_t v___x_792_; uint8_t v___x_793_; 
lean_dec(v_snd_785_);
lean_dec(v_fst_784_);
v___x_792_ = 49;
v___x_793_ = lean_uint32_dec_le(v___x_792_, v___x_789_);
if (v___x_793_ == 0)
{
v___y_762_ = v_res_786_;
v___y_763_ = v_pos_783_;
v___y_764_ = v___x_793_;
goto v___jp_761_;
}
else
{
uint32_t v___x_794_; uint8_t v___x_795_; 
v___x_794_ = 57;
v___x_795_ = lean_uint32_dec_le(v___x_789_, v___x_794_);
v___y_762_ = v_res_786_;
v___y_763_ = v_pos_783_;
v___y_764_ = v___x_795_;
goto v___jp_761_;
}
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec_ref(v_pos_783_);
v___x_796_ = lean_string_utf8_next_fast(v_fst_784_, v_snd_785_);
lean_dec(v_snd_785_);
lean_inc(v_fst_784_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_fst_784_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = lean_unsigned_to_nat(0u);
v___y_735_ = v_res_786_;
v_pos_736_ = v___x_797_;
v_fst_737_ = v_fst_784_;
v_snd_738_ = v___x_796_;
v_res_739_ = v___x_798_;
goto v___jp_734_;
}
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec(v_snd_785_);
lean_dec(v_fst_784_);
v___x_799_ = lean_box(0);
v___x_800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_800_, 0, v_pos_783_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
return v___x_800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent(lean_object* v_value_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___y_828_; lean_object* v___y_832_; uint8_t v___y_833_; lean_object* v___y_858_; uint8_t v___y_859_; lean_object* v___y_890_; lean_object* v_fst_891_; lean_object* v_snd_892_; lean_object* v_fst_902_; lean_object* v_snd_903_; lean_object* v___x_937_; uint8_t v_decide_938_; 
v_fst_902_ = lean_ctor_get(v_a_826_, 0);
v_snd_903_ = lean_ctor_get(v_a_826_, 1);
v___x_937_ = lean_string_utf8_byte_size(v_fst_902_);
v_decide_938_ = lean_nat_dec_eq(v_snd_903_, v___x_937_);
if (v_decide_938_ == 0)
{
uint32_t v___x_939_; uint32_t v___x_940_; uint8_t v___x_941_; 
v___x_939_ = lean_string_utf8_get_fast(v_fst_902_, v_snd_903_);
v___x_940_ = 101;
v___x_941_ = lean_uint32_dec_eq(v___x_939_, v___x_940_);
if (v___x_941_ == 0)
{
uint32_t v___x_942_; uint8_t v___x_943_; 
v___x_942_ = 69;
v___x_943_ = lean_uint32_dec_eq(v___x_939_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v_a_826_);
lean_ctor_set(v___x_944_, 1, v_value_825_);
return v___x_944_;
}
else
{
goto v___jp_904_;
}
}
else
{
goto v___jp_904_;
}
}
else
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_a_826_);
lean_ctor_set(v___x_945_, 1, v_value_825_);
return v___x_945_;
}
v___jp_827_:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_box(0);
v___x_830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_830_, 0, v___y_828_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
return v___x_830_;
}
v___jp_831_:
{
if (v___y_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec_ref(v_value_825_);
v___x_834_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_835_, 0, v___y_832_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
return v___x_835_;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = l_Lean_Json_Parser_natCore(v___x_836_, v___y_832_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_pos_838_; lean_object* v_res_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_847_; 
v_pos_838_ = lean_ctor_get(v___x_837_, 0);
v_res_839_ = lean_ctor_get(v___x_837_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_847_ == 0)
{
v___x_841_ = v___x_837_;
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_res_839_);
lean_inc(v_pos_838_);
lean_dec(v___x_837_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = l_Lean_JsonNumber_shiftr(v_value_825_, v_res_839_);
lean_dec(v_res_839_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v___x_843_);
v___x_845_ = v___x_841_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_pos_838_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
else
{
lean_object* v_pos_848_; lean_object* v_err_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec_ref(v_value_825_);
v_pos_848_ = lean_ctor_get(v___x_837_, 0);
v_err_849_ = lean_ctor_get(v___x_837_, 1);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_837_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_err_849_);
lean_inc(v_pos_848_);
lean_dec(v___x_837_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_pos_848_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_err_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
v___jp_857_:
{
if (v___y_859_ == 0)
{
lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec_ref(v_value_825_);
v___x_860_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_861_, 0, v___y_858_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
return v___x_861_;
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = l_Lean_Json_Parser_natCore(v___x_862_, v___y_858_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_pos_864_; lean_object* v_res_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_879_; 
v_pos_864_ = lean_ctor_get(v___x_863_, 0);
v_res_865_ = lean_ctor_get(v___x_863_, 1);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_879_ == 0)
{
v___x_867_ = v___x_863_;
v_isShared_868_ = v_isSharedCheck_879_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_res_865_);
lean_inc(v_pos_864_);
lean_dec(v___x_863_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_879_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_869_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_870_ = lean_nat_dec_lt(v___x_869_, v_res_865_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = l_Lean_JsonNumber_shiftl(v_value_825_, v_res_865_);
lean_dec(v_res_865_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_871_);
v___x_873_ = v___x_867_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_pos_864_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
else
{
lean_object* v___x_875_; lean_object* v___x_877_; 
lean_dec(v_res_865_);
lean_dec_ref(v_value_825_);
v___x_875_ = ((lean_object*)(l_Lean_Json_Parser_exponent___closed__1));
if (v_isShared_868_ == 0)
{
lean_ctor_set_tag(v___x_867_, 1);
lean_ctor_set(v___x_867_, 1, v___x_875_);
v___x_877_ = v___x_867_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_pos_864_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v_pos_880_; lean_object* v_err_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref(v_value_825_);
v_pos_880_ = lean_ctor_get(v___x_863_, 0);
v_err_881_ = lean_ctor_get(v___x_863_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_863_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_err_881_);
lean_inc(v_pos_880_);
lean_dec(v___x_863_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_pos_880_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_err_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
v___jp_889_:
{
lean_object* v___x_893_; uint8_t v_decide_894_; 
v___x_893_ = lean_string_utf8_byte_size(v_fst_891_);
v_decide_894_ = lean_nat_dec_eq(v_snd_892_, v___x_893_);
if (v_decide_894_ == 0)
{
uint32_t v___x_895_; uint32_t v___x_896_; uint8_t v___x_897_; 
v___x_895_ = lean_string_utf8_get_fast(v_fst_891_, v_snd_892_);
lean_dec(v_snd_892_);
lean_dec(v_fst_891_);
v___x_896_ = 48;
v___x_897_ = lean_uint32_dec_le(v___x_896_, v___x_895_);
if (v___x_897_ == 0)
{
v___y_858_ = v___y_890_;
v___y_859_ = v___x_897_;
goto v___jp_857_;
}
else
{
uint32_t v___x_898_; uint8_t v___x_899_; 
v___x_898_ = 57;
v___x_899_ = lean_uint32_dec_le(v___x_895_, v___x_898_);
v___y_858_ = v___y_890_;
v___y_859_ = v___x_899_;
goto v___jp_857_;
}
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec(v_snd_892_);
lean_dec(v_fst_891_);
lean_dec_ref(v_value_825_);
v___x_900_ = lean_box(0);
v___x_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_901_, 0, v___y_890_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
return v___x_901_;
}
}
v___jp_904_:
{
lean_object* v___x_905_; uint8_t v_decide_906_; 
v___x_905_ = lean_string_utf8_byte_size(v_fst_902_);
v_decide_906_ = lean_nat_dec_eq(v_snd_903_, v___x_905_);
if (v_decide_906_ == 0)
{
lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_932_; 
lean_inc(v_snd_903_);
lean_inc(v_fst_902_);
v_isSharedCheck_932_ = !lean_is_exclusive(v_a_826_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; lean_object* v_unused_934_; 
v_unused_933_ = lean_ctor_get(v_a_826_, 1);
lean_dec(v_unused_933_);
v_unused_934_ = lean_ctor_get(v_a_826_, 0);
lean_dec(v_unused_934_);
v___x_908_ = v_a_826_;
v_isShared_909_ = v_isSharedCheck_932_;
goto v_resetjp_907_;
}
else
{
lean_dec(v_a_826_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_932_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = lean_string_utf8_next_fast(v_fst_902_, v_snd_903_);
lean_dec(v_snd_903_);
lean_inc(v_fst_902_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 1, v___x_910_);
v___x_912_ = v___x_908_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_fst_902_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_910_);
v___x_912_ = v_reuseFailAlloc_931_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
uint8_t v_decide_913_; 
v_decide_913_ = lean_nat_dec_eq(v___x_910_, v___x_905_);
if (v_decide_913_ == 0)
{
uint32_t v___x_914_; uint32_t v___x_915_; uint8_t v___x_916_; 
v___x_914_ = lean_string_utf8_get_fast(v_fst_902_, v___x_910_);
v___x_915_ = 45;
v___x_916_ = lean_uint32_dec_eq(v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
uint32_t v___x_917_; uint8_t v___x_918_; 
v___x_917_ = 43;
v___x_918_ = lean_uint32_dec_eq(v___x_914_, v___x_917_);
if (v___x_918_ == 0)
{
v___y_890_ = v___x_912_;
v_fst_891_ = v_fst_902_;
v_snd_892_ = v___x_910_;
goto v___jp_889_;
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec_ref(v___x_912_);
v___x_919_ = lean_string_utf8_next_fast(v_fst_902_, v___x_910_);
lean_inc(v_fst_902_);
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v_fst_902_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___y_890_ = v___x_920_;
v_fst_891_ = v_fst_902_;
v_snd_892_ = v___x_919_;
goto v___jp_889_;
}
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v_decide_923_; 
lean_dec_ref(v___x_912_);
v___x_921_ = lean_string_utf8_next_fast(v_fst_902_, v___x_910_);
lean_inc(v_fst_902_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_fst_902_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v_decide_923_ = lean_nat_dec_eq(v___x_921_, v___x_905_);
if (v_decide_923_ == 0)
{
if (v___x_916_ == 0)
{
lean_dec(v_fst_902_);
lean_dec_ref(v_value_825_);
v___y_828_ = v___x_922_;
goto v___jp_827_;
}
else
{
uint32_t v___x_924_; uint32_t v___x_925_; uint8_t v___x_926_; 
v___x_924_ = lean_string_utf8_get_fast(v_fst_902_, v___x_921_);
lean_dec(v_fst_902_);
v___x_925_ = 48;
v___x_926_ = lean_uint32_dec_le(v___x_925_, v___x_924_);
if (v___x_926_ == 0)
{
v___y_832_ = v___x_922_;
v___y_833_ = v___x_926_;
goto v___jp_831_;
}
else
{
uint32_t v___x_927_; uint8_t v___x_928_; 
v___x_927_ = 57;
v___x_928_ = lean_uint32_dec_le(v___x_924_, v___x_927_);
v___y_832_ = v___x_922_;
v___y_833_ = v___x_928_;
goto v___jp_831_;
}
}
}
else
{
lean_dec(v_fst_902_);
lean_dec_ref(v_value_825_);
v___y_828_ = v___x_922_;
goto v___jp_827_;
}
}
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec(v_fst_902_);
lean_dec_ref(v_value_825_);
v___x_929_ = lean_box(0);
v___x_930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_912_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
return v___x_930_;
}
}
}
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec_ref(v_value_825_);
v___x_935_ = lean_box(0);
v___x_936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_936_, 0, v_a_826_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
return v___x_936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Json_Parser_num_spec__0(lean_object* v_a_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = lean_nat_to_int(v_a_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_num(lean_object* v_a_948_){
_start:
{
lean_object* v___y_950_; lean_object* v___y_951_; uint8_t v___y_952_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v___y_997_; lean_object* v___y_998_; uint8_t v___y_999_; lean_object* v___y_1024_; lean_object* v___y_1028_; lean_object* v_fst_1029_; lean_object* v_snd_1030_; lean_object* v___y_1031_; lean_object* v___y_1057_; lean_object* v_pos_1058_; lean_object* v_fst_1059_; lean_object* v_snd_1060_; lean_object* v_res_1061_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; uint8_t v___y_1073_; lean_object* v___y_1122_; lean_object* v___y_1126_; lean_object* v_pos_1127_; lean_object* v_fst_1128_; lean_object* v_snd_1129_; lean_object* v_res_1130_; lean_object* v___y_1153_; lean_object* v___y_1154_; uint8_t v___y_1155_; lean_object* v_pos_1174_; lean_object* v_fst_1175_; lean_object* v_snd_1176_; lean_object* v_res_1177_; lean_object* v_fst_1192_; lean_object* v_snd_1193_; lean_object* v___x_1194_; uint8_t v_decide_1195_; 
v_fst_1192_ = lean_ctor_get(v_a_948_, 0);
v_snd_1193_ = lean_ctor_get(v_a_948_, 1);
v___x_1194_ = lean_string_utf8_byte_size(v_fst_1192_);
v_decide_1195_ = lean_nat_dec_eq(v_snd_1193_, v___x_1194_);
if (v_decide_1195_ == 0)
{
uint32_t v___x_1196_; uint32_t v___x_1197_; uint8_t v___x_1198_; 
lean_inc(v_snd_1193_);
lean_inc(v_fst_1192_);
v___x_1196_ = lean_string_utf8_get_fast(v_fst_1192_, v_snd_1193_);
v___x_1197_ = 45;
v___x_1198_ = lean_uint32_dec_eq(v___x_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v_pos_1174_ = v_a_948_;
v_fst_1175_ = v_fst_1192_;
v_snd_1176_ = v_snd_1193_;
v_res_1177_ = v___x_1199_;
goto v___jp_1173_;
}
else
{
lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1208_; 
v_isSharedCheck_1208_ = !lean_is_exclusive(v_a_948_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; lean_object* v_unused_1210_; 
v_unused_1209_ = lean_ctor_get(v_a_948_, 1);
lean_dec(v_unused_1209_);
v_unused_1210_ = lean_ctor_get(v_a_948_, 0);
lean_dec(v_unused_1210_);
v___x_1201_ = v_a_948_;
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
else
{
lean_dec(v_a_948_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = lean_string_utf8_next_fast(v_fst_1192_, v_snd_1193_);
lean_dec(v_snd_1193_);
lean_inc(v_fst_1192_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 1, v___x_1203_);
v___x_1205_ = v___x_1201_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_fst_1192_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v_pos_1174_ = v___x_1205_;
v_fst_1175_ = v_fst_1192_;
v_snd_1176_ = v___x_1203_;
v_res_1177_ = v___x_1206_;
goto v___jp_1173_;
}
}
}
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_box(0);
v___x_1212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1212_, 0, v_a_948_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
return v___x_1212_;
}
v___jp_949_:
{
if (v___y_952_ == 0)
{
lean_object* v___x_953_; lean_object* v___x_954_; 
lean_dec_ref(v___y_950_);
v___x_953_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_954_, 0, v___y_951_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
return v___x_954_;
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_unsigned_to_nat(0u);
v___x_956_ = l_Lean_Json_Parser_natCore(v___x_955_, v___y_951_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_pos_957_; lean_object* v_res_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_972_; 
v_pos_957_ = lean_ctor_get(v___x_956_, 0);
v_res_958_ = lean_ctor_get(v___x_956_, 1);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_972_ == 0)
{
v___x_960_ = v___x_956_;
v_isShared_961_ = v_isSharedCheck_972_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_res_958_);
lean_inc(v_pos_957_);
lean_dec(v___x_956_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_972_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_962_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_963_ = lean_nat_dec_lt(v___x_962_, v_res_958_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_964_ = l_Lean_JsonNumber_shiftl(v___y_950_, v_res_958_);
lean_dec(v_res_958_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v___x_964_);
v___x_966_ = v___x_960_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_pos_957_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
else
{
lean_object* v___x_968_; lean_object* v___x_970_; 
lean_dec(v_res_958_);
lean_dec_ref(v___y_950_);
v___x_968_ = ((lean_object*)(l_Lean_Json_Parser_exponent___closed__1));
if (v_isShared_961_ == 0)
{
lean_ctor_set_tag(v___x_960_, 1);
lean_ctor_set(v___x_960_, 1, v___x_968_);
v___x_970_ = v___x_960_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_pos_957_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v___x_968_);
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
else
{
lean_object* v_pos_973_; lean_object* v_err_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec_ref(v___y_950_);
v_pos_973_ = lean_ctor_get(v___x_956_, 0);
v_err_974_ = lean_ctor_get(v___x_956_, 1);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_956_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_err_974_);
lean_inc(v_pos_973_);
lean_dec(v___x_956_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_pos_973_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_err_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
v___jp_982_:
{
lean_object* v___x_987_; uint8_t v_decide_988_; 
v___x_987_ = lean_string_utf8_byte_size(v_fst_985_);
v_decide_988_ = lean_nat_dec_eq(v_snd_986_, v___x_987_);
if (v_decide_988_ == 0)
{
uint32_t v___x_989_; uint32_t v___x_990_; uint8_t v___x_991_; 
v___x_989_ = lean_string_utf8_get_fast(v_fst_985_, v_snd_986_);
lean_dec(v_snd_986_);
lean_dec(v_fst_985_);
v___x_990_ = 48;
v___x_991_ = lean_uint32_dec_le(v___x_990_, v___x_989_);
if (v___x_991_ == 0)
{
v___y_950_ = v___y_983_;
v___y_951_ = v___y_984_;
v___y_952_ = v___x_991_;
goto v___jp_949_;
}
else
{
uint32_t v___x_992_; uint8_t v___x_993_; 
v___x_992_ = 57;
v___x_993_ = lean_uint32_dec_le(v___x_989_, v___x_992_);
v___y_950_ = v___y_983_;
v___y_951_ = v___y_984_;
v___y_952_ = v___x_993_;
goto v___jp_949_;
}
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; 
lean_dec(v_snd_986_);
lean_dec(v_fst_985_);
lean_dec_ref(v___y_983_);
v___x_994_ = lean_box(0);
v___x_995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_995_, 0, v___y_984_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
return v___x_995_;
}
}
v___jp_996_:
{
if (v___y_999_ == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_dec_ref(v___y_998_);
v___x_1000_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_1001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___y_997_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = l_Lean_Json_Parser_natCore(v___x_1002_, v___y_997_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_pos_1004_; lean_object* v_res_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1013_; 
v_pos_1004_ = lean_ctor_get(v___x_1003_, 0);
v_res_1005_ = lean_ctor_get(v___x_1003_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1007_ = v___x_1003_;
v_isShared_1008_ = v_isSharedCheck_1013_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_res_1005_);
lean_inc(v_pos_1004_);
lean_dec(v___x_1003_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1013_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1009_ = l_Lean_JsonNumber_shiftr(v___y_998_, v_res_1005_);
lean_dec(v_res_1005_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 1, v___x_1009_);
v___x_1011_ = v___x_1007_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_pos_1004_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
else
{
lean_object* v_pos_1014_; lean_object* v_err_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref(v___y_998_);
v_pos_1014_ = lean_ctor_get(v___x_1003_, 0);
v_err_1015_ = lean_ctor_get(v___x_1003_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1003_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_err_1015_);
lean_inc(v_pos_1014_);
lean_dec(v___x_1003_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_pos_1014_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_err_1015_);
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
v___jp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___y_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
return v___x_1026_;
}
v___jp_1027_:
{
lean_object* v___x_1032_; uint8_t v_decide_1033_; 
v___x_1032_ = lean_string_utf8_byte_size(v_fst_1029_);
v_decide_1033_ = lean_nat_dec_eq(v_snd_1030_, v___x_1032_);
if (v_decide_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v_decide_1036_; 
lean_dec_ref(v___y_1028_);
v___x_1034_ = lean_string_utf8_next_fast(v_fst_1029_, v_snd_1030_);
lean_dec(v_snd_1030_);
lean_inc(v_fst_1029_);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v_fst_1029_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v_decide_1036_ = lean_nat_dec_eq(v___x_1034_, v___x_1032_);
if (v_decide_1036_ == 0)
{
uint32_t v___x_1037_; uint32_t v___x_1038_; uint8_t v___x_1039_; 
v___x_1037_ = lean_string_utf8_get_fast(v_fst_1029_, v___x_1034_);
v___x_1038_ = 45;
v___x_1039_ = lean_uint32_dec_eq(v___x_1037_, v___x_1038_);
if (v___x_1039_ == 0)
{
uint32_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = 43;
v___x_1041_ = lean_uint32_dec_eq(v___x_1037_, v___x_1040_);
if (v___x_1041_ == 0)
{
v___y_983_ = v___y_1031_;
v___y_984_ = v___x_1035_;
v_fst_985_ = v_fst_1029_;
v_snd_986_ = v___x_1034_;
goto v___jp_982_;
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_dec_ref_known(v___x_1035_, 2);
v___x_1042_ = lean_string_utf8_next_fast(v_fst_1029_, v___x_1034_);
lean_inc(v_fst_1029_);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_fst_1029_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___y_983_ = v___y_1031_;
v___y_984_ = v___x_1043_;
v_fst_985_ = v_fst_1029_;
v_snd_986_ = v___x_1042_;
goto v___jp_982_;
}
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v_decide_1046_; 
lean_dec_ref_known(v___x_1035_, 2);
v___x_1044_ = lean_string_utf8_next_fast(v_fst_1029_, v___x_1034_);
lean_inc(v_fst_1029_);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v_fst_1029_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v_decide_1046_ = lean_nat_dec_eq(v___x_1044_, v___x_1032_);
if (v_decide_1046_ == 0)
{
if (v___x_1039_ == 0)
{
lean_dec_ref(v___y_1031_);
lean_dec(v_fst_1029_);
v___y_1024_ = v___x_1045_;
goto v___jp_1023_;
}
else
{
uint32_t v___x_1047_; uint32_t v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = lean_string_utf8_get_fast(v_fst_1029_, v___x_1044_);
lean_dec(v_fst_1029_);
v___x_1048_ = 48;
v___x_1049_ = lean_uint32_dec_le(v___x_1048_, v___x_1047_);
if (v___x_1049_ == 0)
{
v___y_997_ = v___x_1045_;
v___y_998_ = v___y_1031_;
v___y_999_ = v___x_1049_;
goto v___jp_996_;
}
else
{
uint32_t v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = 57;
v___x_1051_ = lean_uint32_dec_le(v___x_1047_, v___x_1050_);
v___y_997_ = v___x_1045_;
v___y_998_ = v___y_1031_;
v___y_999_ = v___x_1051_;
goto v___jp_996_;
}
}
}
else
{
lean_dec_ref(v___y_1031_);
lean_dec(v_fst_1029_);
v___y_1024_ = v___x_1045_;
goto v___jp_1023_;
}
}
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_dec_ref(v___y_1031_);
lean_dec(v_fst_1029_);
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1035_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
return v___x_1053_;
}
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec_ref(v___y_1031_);
lean_dec(v_snd_1030_);
lean_dec(v_fst_1029_);
v___x_1054_ = lean_box(0);
v___x_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___y_1028_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
return v___x_1055_;
}
}
v___jp_1056_:
{
lean_object* v___x_1062_; uint8_t v_decide_1063_; 
v___x_1062_ = lean_string_utf8_byte_size(v_fst_1059_);
v_decide_1063_ = lean_nat_dec_eq(v_snd_1060_, v___x_1062_);
if (v_decide_1063_ == 0)
{
uint32_t v___x_1064_; uint32_t v___x_1065_; uint8_t v___x_1066_; 
v___x_1064_ = lean_string_utf8_get_fast(v_fst_1059_, v_snd_1060_);
v___x_1065_ = 101;
v___x_1066_ = lean_uint32_dec_eq(v___x_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
uint32_t v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = 69;
v___x_1068_ = lean_uint32_dec_eq(v___x_1064_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_dec_ref(v_res_1061_);
lean_dec(v_snd_1060_);
lean_dec(v_fst_1059_);
lean_dec_ref(v_pos_1058_);
return v___y_1057_;
}
else
{
lean_dec_ref(v___y_1057_);
v___y_1028_ = v_pos_1058_;
v_fst_1029_ = v_fst_1059_;
v_snd_1030_ = v_snd_1060_;
v___y_1031_ = v_res_1061_;
goto v___jp_1027_;
}
}
else
{
lean_dec_ref(v___y_1057_);
v___y_1028_ = v_pos_1058_;
v_fst_1029_ = v_fst_1059_;
v_snd_1030_ = v_snd_1060_;
v___y_1031_ = v_res_1061_;
goto v___jp_1027_;
}
}
else
{
lean_dec_ref(v_res_1061_);
lean_dec(v_snd_1060_);
lean_dec(v_fst_1059_);
lean_dec_ref(v_pos_1058_);
return v___y_1057_;
}
}
v___jp_1069_:
{
if (v___y_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec(v___y_1072_);
v___x_1074_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___y_1071_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
return v___x_1075_;
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_unsigned_to_nat(0u);
v___x_1077_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_1076_, v___x_1076_, v___y_1071_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_res_1078_; lean_object* v_pos_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1111_; 
v_res_1078_ = lean_ctor_get(v___x_1077_, 1);
v_pos_1079_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1081_ = v___x_1077_;
v_isShared_1082_ = v_isSharedCheck_1111_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_res_1078_);
lean_inc(v_pos_1079_);
lean_dec(v___x_1077_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1111_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v_fst_1083_; lean_object* v_snd_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1110_; 
v_fst_1083_ = lean_ctor_get(v_res_1078_, 0);
v_snd_1084_ = lean_ctor_get(v_res_1078_, 1);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_res_1078_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1086_ = v_res_1078_;
v_isShared_1087_ = v_isSharedCheck_1110_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_snd_1084_);
lean_inc(v_fst_1083_);
lean_dec(v_res_1078_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1110_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1088_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_1089_ = lean_nat_dec_lt(v___x_1088_, v_snd_1084_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v_fst_1092_; lean_object* v_snd_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1090_ = lean_unsigned_to_nat(10u);
v___x_1091_ = lean_nat_pow(v___x_1090_, v_snd_1084_);
v_fst_1092_ = lean_ctor_get(v_pos_1079_, 0);
lean_inc(v_fst_1092_);
v_snd_1093_ = lean_ctor_get(v_pos_1079_, 1);
lean_inc(v_snd_1093_);
v___x_1094_ = lean_nat_to_int(v___y_1072_);
v___x_1095_ = lean_nat_to_int(v___x_1091_);
v___x_1096_ = lean_int_mul(v___x_1094_, v___x_1095_);
lean_dec(v___x_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_nat_to_int(v_fst_1083_);
v___x_1098_ = lean_int_add(v___x_1096_, v___x_1097_);
lean_dec(v___x_1097_);
lean_dec(v___x_1096_);
v___x_1099_ = lean_int_mul(v___y_1070_, v___x_1098_);
lean_dec(v___x_1098_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1099_);
v___x_1101_ = v___x_1086_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_snd_1084_);
v___x_1101_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1103_; 
lean_inc_ref(v___x_1101_);
lean_inc(v_pos_1079_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 1, v___x_1101_);
v___x_1103_ = v___x_1081_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_pos_1079_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
v___y_1057_ = v___x_1103_;
v_pos_1058_ = v_pos_1079_;
v_fst_1059_ = v_fst_1092_;
v_snd_1060_ = v_snd_1093_;
v_res_1061_ = v___x_1101_;
goto v___jp_1056_;
}
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
lean_del_object(v___x_1086_);
lean_dec(v_snd_1084_);
lean_dec(v_fst_1083_);
lean_dec(v___y_1072_);
v___x_1106_ = ((lean_object*)(l_Lean_Json_Parser_numWithDecimals___closed__2));
if (v_isShared_1082_ == 0)
{
lean_ctor_set_tag(v___x_1081_, 1);
lean_ctor_set(v___x_1081_, 1, v___x_1106_);
v___x_1108_ = v___x_1081_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_pos_1079_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v___x_1106_);
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
else
{
lean_object* v_pos_1112_; lean_object* v_err_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v___y_1072_);
v_pos_1112_ = lean_ctor_get(v___x_1077_, 0);
v_err_1113_ = lean_ctor_get(v___x_1077_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1077_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_err_1113_);
lean_inc(v_pos_1112_);
lean_dec(v___x_1077_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_pos_1112_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_err_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
v___jp_1121_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_box(0);
v___x_1124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___y_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
return v___x_1124_;
}
v___jp_1125_:
{
lean_object* v___x_1131_; uint8_t v_decide_1132_; 
v___x_1131_ = lean_string_utf8_byte_size(v_fst_1128_);
v_decide_1132_ = lean_nat_dec_eq(v_snd_1129_, v___x_1131_);
if (v_decide_1132_ == 0)
{
uint32_t v___x_1133_; uint32_t v___x_1134_; uint8_t v___x_1135_; 
v___x_1133_ = lean_string_utf8_get_fast(v_fst_1128_, v_snd_1129_);
v___x_1134_ = 46;
v___x_1135_ = lean_uint32_dec_eq(v___x_1133_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1136_ = lean_nat_to_int(v_res_1130_);
v___x_1137_ = lean_int_mul(v___y_1126_, v___x_1136_);
lean_dec(v___x_1136_);
v___x_1138_ = l_Lean_JsonNumber_fromInt(v___x_1137_);
lean_inc_ref(v___x_1138_);
lean_inc_ref(v_pos_1127_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_pos_1127_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___y_1057_ = v___x_1139_;
v_pos_1058_ = v_pos_1127_;
v_fst_1059_ = v_fst_1128_;
v_snd_1060_ = v_snd_1129_;
v_res_1061_ = v___x_1138_;
goto v___jp_1056_;
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v_decide_1142_; 
lean_dec_ref(v_pos_1127_);
v___x_1140_ = lean_string_utf8_next_fast(v_fst_1128_, v_snd_1129_);
lean_dec(v_snd_1129_);
lean_inc(v_fst_1128_);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v_fst_1128_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v_decide_1142_ = lean_nat_dec_eq(v___x_1140_, v___x_1131_);
if (v_decide_1142_ == 0)
{
if (v___x_1135_ == 0)
{
lean_dec(v_res_1130_);
lean_dec(v_fst_1128_);
v___y_1122_ = v___x_1141_;
goto v___jp_1121_;
}
else
{
uint32_t v___x_1143_; uint32_t v___x_1144_; uint8_t v___x_1145_; 
v___x_1143_ = lean_string_utf8_get_fast(v_fst_1128_, v___x_1140_);
lean_dec(v_fst_1128_);
v___x_1144_ = 48;
v___x_1145_ = lean_uint32_dec_le(v___x_1144_, v___x_1143_);
if (v___x_1145_ == 0)
{
v___y_1070_ = v___y_1126_;
v___y_1071_ = v___x_1141_;
v___y_1072_ = v_res_1130_;
v___y_1073_ = v___x_1145_;
goto v___jp_1069_;
}
else
{
uint32_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = 57;
v___x_1147_ = lean_uint32_dec_le(v___x_1143_, v___x_1146_);
v___y_1070_ = v___y_1126_;
v___y_1071_ = v___x_1141_;
v___y_1072_ = v_res_1130_;
v___y_1073_ = v___x_1147_;
goto v___jp_1069_;
}
}
}
else
{
lean_dec(v_res_1130_);
lean_dec(v_fst_1128_);
v___y_1122_ = v___x_1141_;
goto v___jp_1121_;
}
}
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1148_ = lean_nat_to_int(v_res_1130_);
v___x_1149_ = lean_int_mul(v___y_1126_, v___x_1148_);
lean_dec(v___x_1148_);
v___x_1150_ = l_Lean_JsonNumber_fromInt(v___x_1149_);
lean_inc_ref(v___x_1150_);
lean_inc_ref(v_pos_1127_);
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v_pos_1127_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___y_1057_ = v___x_1151_;
v_pos_1058_ = v_pos_1127_;
v_fst_1059_ = v_fst_1128_;
v_snd_1060_ = v_snd_1129_;
v_res_1061_ = v___x_1150_;
goto v___jp_1056_;
}
}
v___jp_1152_:
{
if (v___y_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_1157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___y_1153_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
return v___x_1157_;
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_unsigned_to_nat(0u);
v___x_1159_ = l_Lean_Json_Parser_natCore(v___x_1158_, v___y_1153_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_pos_1160_; lean_object* v_res_1161_; lean_object* v_fst_1162_; lean_object* v_snd_1163_; 
v_pos_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_pos_1160_);
v_res_1161_ = lean_ctor_get(v___x_1159_, 1);
lean_inc(v_res_1161_);
lean_dec_ref_known(v___x_1159_, 2);
v_fst_1162_ = lean_ctor_get(v_pos_1160_, 0);
lean_inc(v_fst_1162_);
v_snd_1163_ = lean_ctor_get(v_pos_1160_, 1);
lean_inc(v_snd_1163_);
v___y_1126_ = v___y_1154_;
v_pos_1127_ = v_pos_1160_;
v_fst_1128_ = v_fst_1162_;
v_snd_1129_ = v_snd_1163_;
v_res_1130_ = v_res_1161_;
goto v___jp_1125_;
}
else
{
lean_object* v_pos_1164_; lean_object* v_err_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_pos_1164_ = lean_ctor_get(v___x_1159_, 0);
v_err_1165_ = lean_ctor_get(v___x_1159_, 1);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1159_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_err_1165_);
lean_inc(v_pos_1164_);
lean_dec(v___x_1159_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_pos_1164_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_err_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
v___jp_1173_:
{
lean_object* v___x_1178_; uint8_t v_decide_1179_; 
v___x_1178_ = lean_string_utf8_byte_size(v_fst_1175_);
v_decide_1179_ = lean_nat_dec_eq(v_snd_1176_, v___x_1178_);
if (v_decide_1179_ == 0)
{
uint32_t v___x_1180_; uint32_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1180_ = lean_string_utf8_get_fast(v_fst_1175_, v_snd_1176_);
v___x_1181_ = 48;
v___x_1182_ = lean_uint32_dec_eq(v___x_1180_, v___x_1181_);
if (v___x_1182_ == 0)
{
uint32_t v___x_1183_; uint8_t v___x_1184_; 
lean_dec(v_snd_1176_);
lean_dec(v_fst_1175_);
v___x_1183_ = 49;
v___x_1184_ = lean_uint32_dec_le(v___x_1183_, v___x_1180_);
if (v___x_1184_ == 0)
{
v___y_1153_ = v_pos_1174_;
v___y_1154_ = v_res_1177_;
v___y_1155_ = v___x_1184_;
goto v___jp_1152_;
}
else
{
uint32_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = 57;
v___x_1186_ = lean_uint32_dec_le(v___x_1180_, v___x_1185_);
v___y_1153_ = v_pos_1174_;
v___y_1154_ = v_res_1177_;
v___y_1155_ = v___x_1186_;
goto v___jp_1152_;
}
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec_ref(v_pos_1174_);
v___x_1187_ = lean_string_utf8_next_fast(v_fst_1175_, v_snd_1176_);
lean_dec(v_snd_1176_);
lean_inc(v_fst_1175_);
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v_fst_1175_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = lean_unsigned_to_nat(0u);
v___y_1126_ = v_res_1177_;
v_pos_1127_ = v___x_1188_;
v_fst_1128_ = v_fst_1175_;
v_snd_1129_ = v___x_1187_;
v_res_1130_ = v___x_1189_;
goto v___jp_1125_;
}
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec(v_snd_1176_);
lean_dec(v_fst_1175_);
v___x_1190_ = lean_box(0);
v___x_1191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1191_, 0, v_pos_1174_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
return v___x_1191_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(lean_object* v_msg_1213_){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = lean_box(1);
v___x_1215_ = lean_panic_fn_borrowed(v___x_1214_, v_msg_1213_);
return v___x_1215_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1219_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2));
v___x_1220_ = lean_unsigned_to_nat(35u);
v___x_1221_ = lean_unsigned_to_nat(182u);
v___x_1222_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1));
v___x_1223_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1224_ = l_mkPanicMessageWithDecl(v___x_1223_, v___x_1222_, v___x_1221_, v___x_1220_, v___x_1219_);
return v___x_1224_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1225_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2));
v___x_1226_ = lean_unsigned_to_nat(21u);
v___x_1227_ = lean_unsigned_to_nat(183u);
v___x_1228_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1));
v___x_1229_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1230_ = l_mkPanicMessageWithDecl(v___x_1229_, v___x_1228_, v___x_1227_, v___x_1226_, v___x_1225_);
return v___x_1230_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1233_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6));
v___x_1234_ = lean_unsigned_to_nat(35u);
v___x_1235_ = lean_unsigned_to_nat(276u);
v___x_1236_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5));
v___x_1237_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1238_ = l_mkPanicMessageWithDecl(v___x_1237_, v___x_1236_, v___x_1235_, v___x_1234_, v___x_1233_);
return v___x_1238_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1239_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6));
v___x_1240_ = lean_unsigned_to_nat(21u);
v___x_1241_ = lean_unsigned_to_nat(277u);
v___x_1242_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5));
v___x_1243_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1244_ = l_mkPanicMessageWithDecl(v___x_1243_, v___x_1242_, v___x_1241_, v___x_1240_, v___x_1239_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(lean_object* v_k_1245_, lean_object* v_v_1246_, lean_object* v_t_1247_){
_start:
{
if (lean_obj_tag(v_t_1247_) == 0)
{
lean_object* v_size_1248_; lean_object* v_k_1249_; lean_object* v_v_1250_; lean_object* v_l_1251_; lean_object* v_r_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1608_; 
v_size_1248_ = lean_ctor_get(v_t_1247_, 0);
v_k_1249_ = lean_ctor_get(v_t_1247_, 1);
v_v_1250_ = lean_ctor_get(v_t_1247_, 2);
v_l_1251_ = lean_ctor_get(v_t_1247_, 3);
v_r_1252_ = lean_ctor_get(v_t_1247_, 4);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_t_1247_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1254_ = v_t_1247_;
v_isShared_1255_ = v_isSharedCheck_1608_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_r_1252_);
lean_inc(v_l_1251_);
lean_inc(v_v_1250_);
lean_inc(v_k_1249_);
lean_inc(v_size_1248_);
lean_dec(v_t_1247_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1608_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
uint8_t v___x_1256_; 
v___x_1256_ = lean_string_compare(v_k_1245_, v_k_1249_);
switch(v___x_1256_)
{
case 0:
{
lean_object* v___x_1257_; 
lean_dec(v_size_1248_);
v___x_1257_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_1245_, v_v_1246_, v_l_1251_);
if (lean_obj_tag(v_r_1252_) == 0)
{
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_size_1258_; lean_object* v_size_1259_; lean_object* v_k_1260_; lean_object* v_v_1261_; lean_object* v_l_1262_; lean_object* v_r_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v_size_1258_ = lean_ctor_get(v_r_1252_, 0);
v_size_1259_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_size_1259_);
v_k_1260_ = lean_ctor_get(v___x_1257_, 1);
lean_inc(v_k_1260_);
v_v_1261_ = lean_ctor_get(v___x_1257_, 2);
lean_inc(v_v_1261_);
v_l_1262_ = lean_ctor_get(v___x_1257_, 3);
lean_inc(v_l_1262_);
v_r_1263_ = lean_ctor_get(v___x_1257_, 4);
lean_inc(v_r_1263_);
v___x_1264_ = lean_unsigned_to_nat(3u);
v___x_1265_ = lean_nat_mul(v___x_1264_, v_size_1258_);
v___x_1266_ = lean_nat_dec_lt(v___x_1265_, v_size_1259_);
lean_dec(v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
lean_dec(v_r_1263_);
lean_dec(v_l_1262_);
lean_dec(v_v_1261_);
lean_dec(v_k_1260_);
v___x_1267_ = lean_unsigned_to_nat(1u);
v___x_1268_ = lean_nat_add(v___x_1267_, v_size_1259_);
lean_dec(v_size_1259_);
v___x_1269_ = lean_nat_add(v___x_1268_, v_size_1258_);
lean_dec(v___x_1268_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 3, v___x_1257_);
lean_ctor_set(v___x_1254_, 0, v___x_1269_);
v___x_1271_ = v___x_1254_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1272_, 3, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1272_, 4, v_r_1252_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
else
{
lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1344_; 
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; lean_object* v_unused_1346_; lean_object* v_unused_1347_; lean_object* v_unused_1348_; lean_object* v_unused_1349_; 
v_unused_1345_ = lean_ctor_get(v___x_1257_, 4);
lean_dec(v_unused_1345_);
v_unused_1346_ = lean_ctor_get(v___x_1257_, 3);
lean_dec(v_unused_1346_);
v_unused_1347_ = lean_ctor_get(v___x_1257_, 2);
lean_dec(v_unused_1347_);
v_unused_1348_ = lean_ctor_get(v___x_1257_, 1);
lean_dec(v_unused_1348_);
v_unused_1349_ = lean_ctor_get(v___x_1257_, 0);
lean_dec(v_unused_1349_);
v___x_1274_ = v___x_1257_;
v_isShared_1275_ = v_isSharedCheck_1344_;
goto v_resetjp_1273_;
}
else
{
lean_dec(v___x_1257_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1344_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
if (lean_obj_tag(v_l_1262_) == 0)
{
if (lean_obj_tag(v_r_1263_) == 0)
{
lean_object* v_size_1276_; lean_object* v_size_1277_; lean_object* v_k_1278_; lean_object* v_v_1279_; lean_object* v_l_1280_; lean_object* v_r_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v_size_1276_ = lean_ctor_get(v_l_1262_, 0);
v_size_1277_ = lean_ctor_get(v_r_1263_, 0);
v_k_1278_ = lean_ctor_get(v_r_1263_, 1);
v_v_1279_ = lean_ctor_get(v_r_1263_, 2);
v_l_1280_ = lean_ctor_get(v_r_1263_, 3);
v_r_1281_ = lean_ctor_get(v_r_1263_, 4);
v___x_1282_ = lean_unsigned_to_nat(2u);
v___x_1283_ = lean_nat_mul(v___x_1282_, v_size_1276_);
v___x_1284_ = lean_nat_dec_lt(v_size_1277_, v___x_1283_);
lean_dec(v___x_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1314_; 
lean_inc(v_r_1281_);
lean_inc(v_l_1280_);
lean_inc(v_v_1279_);
lean_inc(v_k_1278_);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_r_1263_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; lean_object* v_unused_1316_; lean_object* v_unused_1317_; lean_object* v_unused_1318_; lean_object* v_unused_1319_; 
v_unused_1315_ = lean_ctor_get(v_r_1263_, 4);
lean_dec(v_unused_1315_);
v_unused_1316_ = lean_ctor_get(v_r_1263_, 3);
lean_dec(v_unused_1316_);
v_unused_1317_ = lean_ctor_get(v_r_1263_, 2);
lean_dec(v_unused_1317_);
v_unused_1318_ = lean_ctor_get(v_r_1263_, 1);
lean_dec(v_unused_1318_);
v_unused_1319_ = lean_ctor_get(v_r_1263_, 0);
lean_dec(v_unused_1319_);
v___x_1286_ = v_r_1263_;
v_isShared_1287_ = v_isSharedCheck_1314_;
goto v_resetjp_1285_;
}
else
{
lean_dec(v_r_1263_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1314_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___x_1302_; lean_object* v___y_1304_; 
v___x_1288_ = lean_unsigned_to_nat(1u);
v___x_1289_ = lean_nat_add(v___x_1288_, v_size_1259_);
lean_dec(v_size_1259_);
v___x_1290_ = lean_nat_add(v___x_1289_, v_size_1258_);
lean_dec(v___x_1289_);
v___x_1302_ = lean_nat_add(v___x_1288_, v_size_1276_);
if (lean_obj_tag(v_l_1280_) == 0)
{
lean_object* v_size_1312_; 
v_size_1312_ = lean_ctor_get(v_l_1280_, 0);
lean_inc(v_size_1312_);
v___y_1304_ = v_size_1312_;
goto v___jp_1303_;
}
else
{
lean_object* v___x_1313_; 
v___x_1313_ = lean_unsigned_to_nat(0u);
v___y_1304_ = v___x_1313_;
goto v___jp_1303_;
}
v___jp_1291_:
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1295_ = lean_nat_add(v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec(v___y_1293_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 4, v_r_1252_);
lean_ctor_set(v___x_1286_, 3, v_r_1281_);
lean_ctor_set(v___x_1286_, 2, v_v_1250_);
lean_ctor_set(v___x_1286_, 1, v_k_1249_);
lean_ctor_set(v___x_1286_, 0, v___x_1295_);
v___x_1297_ = v___x_1286_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1301_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1301_, 3, v_r_1281_);
lean_ctor_set(v_reuseFailAlloc_1301_, 4, v_r_1252_);
v___x_1297_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_object* v___x_1299_; 
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 4, v___x_1297_);
lean_ctor_set(v___x_1274_, 3, v___y_1292_);
lean_ctor_set(v___x_1274_, 2, v_v_1279_);
lean_ctor_set(v___x_1274_, 1, v_k_1278_);
lean_ctor_set(v___x_1274_, 0, v___x_1290_);
v___x_1299_ = v___x_1274_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_k_1278_);
lean_ctor_set(v_reuseFailAlloc_1300_, 2, v_v_1279_);
lean_ctor_set(v_reuseFailAlloc_1300_, 3, v___y_1292_);
lean_ctor_set(v_reuseFailAlloc_1300_, 4, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
v___jp_1303_:
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1305_ = lean_nat_add(v___x_1302_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec(v___x_1302_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v_l_1280_);
lean_ctor_set(v___x_1254_, 3, v_l_1262_);
lean_ctor_set(v___x_1254_, 2, v_v_1261_);
lean_ctor_set(v___x_1254_, 1, v_k_1260_);
lean_ctor_set(v___x_1254_, 0, v___x_1305_);
v___x_1307_ = v___x_1254_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_k_1260_);
lean_ctor_set(v_reuseFailAlloc_1311_, 2, v_v_1261_);
lean_ctor_set(v_reuseFailAlloc_1311_, 3, v_l_1262_);
lean_ctor_set(v_reuseFailAlloc_1311_, 4, v_l_1280_);
v___x_1307_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_nat_add(v___x_1288_, v_size_1258_);
if (lean_obj_tag(v_r_1281_) == 0)
{
lean_object* v_size_1309_; 
v_size_1309_ = lean_ctor_get(v_r_1281_, 0);
lean_inc(v_size_1309_);
v___y_1292_ = v___x_1307_;
v___y_1293_ = v___x_1308_;
v___y_1294_ = v_size_1309_;
goto v___jp_1291_;
}
else
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_unsigned_to_nat(0u);
v___y_1292_ = v___x_1307_;
v___y_1293_ = v___x_1308_;
v___y_1294_ = v___x_1310_;
goto v___jp_1291_;
}
}
}
}
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
lean_del_object(v___x_1254_);
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_nat_add(v___x_1320_, v_size_1259_);
lean_dec(v_size_1259_);
v___x_1322_ = lean_nat_add(v___x_1321_, v_size_1258_);
lean_dec(v___x_1321_);
v___x_1323_ = lean_nat_add(v___x_1320_, v_size_1258_);
v___x_1324_ = lean_nat_add(v___x_1323_, v_size_1277_);
lean_dec(v___x_1323_);
lean_inc_ref(v_r_1252_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 4, v_r_1252_);
lean_ctor_set(v___x_1274_, 3, v_r_1263_);
lean_ctor_set(v___x_1274_, 2, v_v_1250_);
lean_ctor_set(v___x_1274_, 1, v_k_1249_);
lean_ctor_set(v___x_1274_, 0, v___x_1324_);
v___x_1326_ = v___x_1274_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_r_1263_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v_r_1252_);
v___x_1326_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
v_isSharedCheck_1333_ = !lean_is_exclusive(v_r_1252_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; lean_object* v_unused_1335_; lean_object* v_unused_1336_; lean_object* v_unused_1337_; lean_object* v_unused_1338_; 
v_unused_1334_ = lean_ctor_get(v_r_1252_, 4);
lean_dec(v_unused_1334_);
v_unused_1335_ = lean_ctor_get(v_r_1252_, 3);
lean_dec(v_unused_1335_);
v_unused_1336_ = lean_ctor_get(v_r_1252_, 2);
lean_dec(v_unused_1336_);
v_unused_1337_ = lean_ctor_get(v_r_1252_, 1);
lean_dec(v_unused_1337_);
v_unused_1338_ = lean_ctor_get(v_r_1252_, 0);
lean_dec(v_unused_1338_);
v___x_1328_ = v_r_1252_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_dec(v_r_1252_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 4, v___x_1326_);
lean_ctor_set(v___x_1328_, 3, v_l_1262_);
lean_ctor_set(v___x_1328_, 2, v_v_1261_);
lean_ctor_set(v___x_1328_, 1, v_k_1260_);
lean_ctor_set(v___x_1328_, 0, v___x_1322_);
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_k_1260_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_v_1261_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v_l_1262_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v___x_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec_ref_known(v_l_1262_, 5);
lean_del_object(v___x_1274_);
lean_dec(v_v_1261_);
lean_dec(v_k_1260_);
lean_dec(v_size_1259_);
lean_dec_ref_known(v_r_1252_, 5);
lean_del_object(v___x_1254_);
lean_dec(v_v_1250_);
lean_dec(v_k_1249_);
v___x_1340_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3);
v___x_1341_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1340_);
return v___x_1341_;
}
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_del_object(v___x_1274_);
lean_dec(v_r_1263_);
lean_dec(v_v_1261_);
lean_dec(v_k_1260_);
lean_dec(v_size_1259_);
lean_dec_ref_known(v_r_1252_, 5);
lean_del_object(v___x_1254_);
lean_dec(v_v_1250_);
lean_dec(v_k_1249_);
v___x_1342_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4);
v___x_1343_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1342_);
return v___x_1343_;
}
}
}
}
else
{
lean_object* v_size_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v_size_1350_ = lean_ctor_get(v_r_1252_, 0);
v___x_1351_ = lean_unsigned_to_nat(1u);
v___x_1352_ = lean_nat_add(v___x_1351_, v_size_1350_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 3, v___x_1257_);
lean_ctor_set(v___x_1254_, 0, v___x_1352_);
v___x_1354_ = v___x_1254_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1355_, 4, v_r_1252_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
else
{
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_l_1356_; 
v_l_1356_ = lean_ctor_get(v___x_1257_, 3);
lean_inc(v_l_1356_);
if (lean_obj_tag(v_l_1356_) == 0)
{
lean_object* v_r_1357_; 
v_r_1357_ = lean_ctor_get(v___x_1257_, 4);
lean_inc(v_r_1357_);
if (lean_obj_tag(v_r_1357_) == 0)
{
lean_object* v_size_1358_; lean_object* v_k_1359_; lean_object* v_v_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1374_; 
v_size_1358_ = lean_ctor_get(v___x_1257_, 0);
v_k_1359_ = lean_ctor_get(v___x_1257_, 1);
v_v_1360_ = lean_ctor_get(v___x_1257_, 2);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; lean_object* v_unused_1376_; 
v_unused_1375_ = lean_ctor_get(v___x_1257_, 4);
lean_dec(v_unused_1375_);
v_unused_1376_ = lean_ctor_get(v___x_1257_, 3);
lean_dec(v_unused_1376_);
v___x_1362_ = v___x_1257_;
v_isShared_1363_ = v_isSharedCheck_1374_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_v_1360_);
lean_inc(v_k_1359_);
lean_inc(v_size_1358_);
lean_dec(v___x_1257_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1374_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v_size_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
v_size_1364_ = lean_ctor_get(v_r_1357_, 0);
v___x_1365_ = lean_unsigned_to_nat(1u);
v___x_1366_ = lean_nat_add(v___x_1365_, v_size_1358_);
lean_dec(v_size_1358_);
v___x_1367_ = lean_nat_add(v___x_1365_, v_size_1364_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v_r_1252_);
lean_ctor_set(v___x_1362_, 3, v_r_1357_);
lean_ctor_set(v___x_1362_, 2, v_v_1250_);
lean_ctor_set(v___x_1362_, 1, v_k_1249_);
lean_ctor_set(v___x_1362_, 0, v___x_1367_);
v___x_1369_ = v___x_1362_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_r_1357_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_r_1252_);
v___x_1369_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1371_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v___x_1369_);
lean_ctor_set(v___x_1254_, 3, v_l_1356_);
lean_ctor_set(v___x_1254_, 2, v_v_1360_);
lean_ctor_set(v___x_1254_, 1, v_k_1359_);
lean_ctor_set(v___x_1254_, 0, v___x_1366_);
v___x_1371_ = v___x_1254_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_k_1359_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_v_1360_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v_l_1356_);
lean_ctor_set(v_reuseFailAlloc_1372_, 4, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
else
{
lean_object* v_k_1377_; lean_object* v_v_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1390_; 
v_k_1377_ = lean_ctor_get(v___x_1257_, 1);
v_v_1378_ = lean_ctor_get(v___x_1257_, 2);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; lean_object* v_unused_1392_; lean_object* v_unused_1393_; 
v_unused_1391_ = lean_ctor_get(v___x_1257_, 4);
lean_dec(v_unused_1391_);
v_unused_1392_ = lean_ctor_get(v___x_1257_, 3);
lean_dec(v_unused_1392_);
v_unused_1393_ = lean_ctor_get(v___x_1257_, 0);
lean_dec(v_unused_1393_);
v___x_1380_ = v___x_1257_;
v_isShared_1381_ = v_isSharedCheck_1390_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_v_1378_);
lean_inc(v_k_1377_);
lean_dec(v___x_1257_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1390_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1382_ = lean_unsigned_to_nat(3u);
v___x_1383_ = lean_unsigned_to_nat(1u);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 3, v_r_1357_);
lean_ctor_set(v___x_1380_, 2, v_v_1250_);
lean_ctor_set(v___x_1380_, 1, v_k_1249_);
lean_ctor_set(v___x_1380_, 0, v___x_1383_);
v___x_1385_ = v___x_1380_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1389_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1389_, 3, v_r_1357_);
lean_ctor_set(v_reuseFailAlloc_1389_, 4, v_r_1357_);
v___x_1385_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1387_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v___x_1385_);
lean_ctor_set(v___x_1254_, 3, v_l_1356_);
lean_ctor_set(v___x_1254_, 2, v_v_1378_);
lean_ctor_set(v___x_1254_, 1, v_k_1377_);
lean_ctor_set(v___x_1254_, 0, v___x_1382_);
v___x_1387_ = v___x_1254_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_k_1377_);
lean_ctor_set(v_reuseFailAlloc_1388_, 2, v_v_1378_);
lean_ctor_set(v_reuseFailAlloc_1388_, 3, v_l_1356_);
lean_ctor_set(v_reuseFailAlloc_1388_, 4, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
else
{
lean_object* v_r_1394_; 
v_r_1394_ = lean_ctor_get(v___x_1257_, 4);
lean_inc(v_r_1394_);
if (lean_obj_tag(v_r_1394_) == 0)
{
lean_object* v_k_1395_; lean_object* v_v_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1420_; 
v_k_1395_ = lean_ctor_get(v___x_1257_, 1);
v_v_1396_ = lean_ctor_get(v___x_1257_, 2);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1420_ == 0)
{
lean_object* v_unused_1421_; lean_object* v_unused_1422_; lean_object* v_unused_1423_; 
v_unused_1421_ = lean_ctor_get(v___x_1257_, 4);
lean_dec(v_unused_1421_);
v_unused_1422_ = lean_ctor_get(v___x_1257_, 3);
lean_dec(v_unused_1422_);
v_unused_1423_ = lean_ctor_get(v___x_1257_, 0);
lean_dec(v_unused_1423_);
v___x_1398_ = v___x_1257_;
v_isShared_1399_ = v_isSharedCheck_1420_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_v_1396_);
lean_inc(v_k_1395_);
lean_dec(v___x_1257_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1420_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v_k_1400_; lean_object* v_v_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1416_; 
v_k_1400_ = lean_ctor_get(v_r_1394_, 1);
v_v_1401_ = lean_ctor_get(v_r_1394_, 2);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_r_1394_);
if (v_isSharedCheck_1416_ == 0)
{
lean_object* v_unused_1417_; lean_object* v_unused_1418_; lean_object* v_unused_1419_; 
v_unused_1417_ = lean_ctor_get(v_r_1394_, 4);
lean_dec(v_unused_1417_);
v_unused_1418_ = lean_ctor_get(v_r_1394_, 3);
lean_dec(v_unused_1418_);
v_unused_1419_ = lean_ctor_get(v_r_1394_, 0);
lean_dec(v_unused_1419_);
v___x_1403_ = v_r_1394_;
v_isShared_1404_ = v_isSharedCheck_1416_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_v_1401_);
lean_inc(v_k_1400_);
lean_dec(v_r_1394_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1416_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1405_ = lean_unsigned_to_nat(3u);
v___x_1406_ = lean_unsigned_to_nat(1u);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 4, v_l_1356_);
lean_ctor_set(v___x_1403_, 3, v_l_1356_);
lean_ctor_set(v___x_1403_, 2, v_v_1396_);
lean_ctor_set(v___x_1403_, 1, v_k_1395_);
lean_ctor_set(v___x_1403_, 0, v___x_1406_);
v___x_1408_ = v___x_1403_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_k_1395_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_v_1396_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v_l_1356_);
lean_ctor_set(v_reuseFailAlloc_1415_, 4, v_l_1356_);
v___x_1408_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1410_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 4, v_l_1356_);
lean_ctor_set(v___x_1398_, 2, v_v_1250_);
lean_ctor_set(v___x_1398_, 1, v_k_1249_);
lean_ctor_set(v___x_1398_, 0, v___x_1406_);
v___x_1410_ = v___x_1398_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1414_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1414_, 3, v_l_1356_);
lean_ctor_set(v_reuseFailAlloc_1414_, 4, v_l_1356_);
v___x_1410_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1412_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v___x_1410_);
lean_ctor_set(v___x_1254_, 3, v___x_1408_);
lean_ctor_set(v___x_1254_, 2, v_v_1401_);
lean_ctor_set(v___x_1254_, 1, v_k_1400_);
lean_ctor_set(v___x_1254_, 0, v___x_1405_);
v___x_1412_ = v___x_1254_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_k_1400_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v_v_1401_);
lean_ctor_set(v_reuseFailAlloc_1413_, 3, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1413_, 4, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
}
else
{
lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1424_ = lean_unsigned_to_nat(2u);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v_r_1394_);
lean_ctor_set(v___x_1254_, 3, v___x_1257_);
lean_ctor_set(v___x_1254_, 0, v___x_1424_);
v___x_1426_ = v___x_1254_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1427_, 3, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1427_, 4, v_r_1394_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = lean_unsigned_to_nat(1u);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v___x_1257_);
lean_ctor_set(v___x_1254_, 3, v___x_1257_);
lean_ctor_set(v___x_1254_, 0, v___x_1428_);
v___x_1430_ = v___x_1254_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1431_, 4, v___x_1257_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
case 1:
{
lean_object* v___x_1433_; 
lean_dec(v_v_1250_);
lean_dec(v_k_1249_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 2, v_v_1246_);
lean_ctor_set(v___x_1254_, 1, v_k_1245_);
v___x_1433_ = v___x_1254_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_size_1248_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_k_1245_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_v_1246_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_l_1251_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v_r_1252_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
default: 
{
lean_object* v___x_1435_; 
lean_dec(v_size_1248_);
v___x_1435_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_1245_, v_v_1246_, v_r_1252_);
if (lean_obj_tag(v_l_1251_) == 0)
{
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_size_1436_; lean_object* v_size_1437_; lean_object* v_k_1438_; lean_object* v_v_1439_; lean_object* v_l_1440_; lean_object* v_r_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v_size_1436_ = lean_ctor_get(v_l_1251_, 0);
v_size_1437_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_size_1437_);
v_k_1438_ = lean_ctor_get(v___x_1435_, 1);
lean_inc(v_k_1438_);
v_v_1439_ = lean_ctor_get(v___x_1435_, 2);
lean_inc(v_v_1439_);
v_l_1440_ = lean_ctor_get(v___x_1435_, 3);
lean_inc(v_l_1440_);
v_r_1441_ = lean_ctor_get(v___x_1435_, 4);
lean_inc(v_r_1441_);
v___x_1442_ = lean_unsigned_to_nat(3u);
v___x_1443_ = lean_nat_mul(v___x_1442_, v_size_1436_);
v___x_1444_ = lean_nat_dec_lt(v___x_1443_, v_size_1437_);
lean_dec(v___x_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
lean_dec(v_r_1441_);
lean_dec(v_l_1440_);
lean_dec(v_v_1439_);
lean_dec(v_k_1438_);
v___x_1445_ = lean_unsigned_to_nat(1u);
v___x_1446_ = lean_nat_add(v___x_1445_, v_size_1436_);
v___x_1447_ = lean_nat_add(v___x_1446_, v_size_1437_);
lean_dec(v_size_1437_);
lean_dec(v___x_1446_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v___x_1435_);
lean_ctor_set(v___x_1254_, 0, v___x_1447_);
v___x_1449_ = v___x_1254_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v_l_1251_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v___x_1435_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
else
{
lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1520_; 
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; lean_object* v_unused_1522_; lean_object* v_unused_1523_; lean_object* v_unused_1524_; lean_object* v_unused_1525_; 
v_unused_1521_ = lean_ctor_get(v___x_1435_, 4);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v___x_1435_, 3);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v___x_1435_, 2);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v___x_1435_, 1);
lean_dec(v_unused_1524_);
v_unused_1525_ = lean_ctor_get(v___x_1435_, 0);
lean_dec(v_unused_1525_);
v___x_1452_ = v___x_1435_;
v_isShared_1453_ = v_isSharedCheck_1520_;
goto v_resetjp_1451_;
}
else
{
lean_dec(v___x_1435_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1520_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
if (lean_obj_tag(v_l_1440_) == 0)
{
if (lean_obj_tag(v_r_1441_) == 0)
{
lean_object* v_size_1454_; lean_object* v_k_1455_; lean_object* v_v_1456_; lean_object* v_l_1457_; lean_object* v_r_1458_; lean_object* v_size_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v_size_1454_ = lean_ctor_get(v_l_1440_, 0);
v_k_1455_ = lean_ctor_get(v_l_1440_, 1);
v_v_1456_ = lean_ctor_get(v_l_1440_, 2);
v_l_1457_ = lean_ctor_get(v_l_1440_, 3);
v_r_1458_ = lean_ctor_get(v_l_1440_, 4);
v_size_1459_ = lean_ctor_get(v_r_1441_, 0);
v___x_1460_ = lean_unsigned_to_nat(2u);
v___x_1461_ = lean_nat_mul(v___x_1460_, v_size_1459_);
v___x_1462_ = lean_nat_dec_lt(v_size_1454_, v___x_1461_);
lean_dec(v___x_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1491_; 
lean_inc(v_r_1458_);
lean_inc(v_l_1457_);
lean_inc(v_v_1456_);
lean_inc(v_k_1455_);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_l_1440_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; lean_object* v_unused_1493_; lean_object* v_unused_1494_; lean_object* v_unused_1495_; lean_object* v_unused_1496_; 
v_unused_1492_ = lean_ctor_get(v_l_1440_, 4);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_l_1440_, 3);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_l_1440_, 2);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_l_1440_, 1);
lean_dec(v_unused_1495_);
v_unused_1496_ = lean_ctor_get(v_l_1440_, 0);
lean_dec(v_unused_1496_);
v___x_1464_ = v_l_1440_;
v_isShared_1465_ = v_isSharedCheck_1491_;
goto v_resetjp_1463_;
}
else
{
lean_dec(v_l_1440_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1491_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1481_; 
v___x_1466_ = lean_unsigned_to_nat(1u);
v___x_1467_ = lean_nat_add(v___x_1466_, v_size_1436_);
v___x_1468_ = lean_nat_add(v___x_1467_, v_size_1437_);
lean_dec(v_size_1437_);
if (lean_obj_tag(v_l_1457_) == 0)
{
lean_object* v_size_1489_; 
v_size_1489_ = lean_ctor_get(v_l_1457_, 0);
lean_inc(v_size_1489_);
v___y_1481_ = v_size_1489_;
goto v___jp_1480_;
}
else
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_unsigned_to_nat(0u);
v___y_1481_ = v___x_1490_;
goto v___jp_1480_;
}
v___jp_1469_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1473_ = lean_nat_add(v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec(v___y_1471_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 4, v_r_1441_);
lean_ctor_set(v___x_1464_, 3, v_r_1458_);
lean_ctor_set(v___x_1464_, 2, v_v_1439_);
lean_ctor_set(v___x_1464_, 1, v_k_1438_);
lean_ctor_set(v___x_1464_, 0, v___x_1473_);
v___x_1475_ = v___x_1464_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1479_, 3, v_r_1458_);
lean_ctor_set(v_reuseFailAlloc_1479_, 4, v_r_1441_);
v___x_1475_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1477_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 4, v___x_1475_);
lean_ctor_set(v___x_1452_, 3, v___y_1470_);
lean_ctor_set(v___x_1452_, 2, v_v_1456_);
lean_ctor_set(v___x_1452_, 1, v_k_1455_);
lean_ctor_set(v___x_1452_, 0, v___x_1468_);
v___x_1477_ = v___x_1452_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_k_1455_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v_v_1456_);
lean_ctor_set(v_reuseFailAlloc_1478_, 3, v___y_1470_);
lean_ctor_set(v_reuseFailAlloc_1478_, 4, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
v___jp_1480_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = lean_nat_add(v___x_1467_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec(v___x_1467_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v_l_1457_);
lean_ctor_set(v___x_1254_, 0, v___x_1482_);
v___x_1484_ = v___x_1254_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1488_, 3, v_l_1251_);
lean_ctor_set(v_reuseFailAlloc_1488_, 4, v_l_1457_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_nat_add(v___x_1466_, v_size_1459_);
if (lean_obj_tag(v_r_1458_) == 0)
{
lean_object* v_size_1486_; 
v_size_1486_ = lean_ctor_get(v_r_1458_, 0);
lean_inc(v_size_1486_);
v___y_1470_ = v___x_1484_;
v___y_1471_ = v___x_1485_;
v___y_1472_ = v_size_1486_;
goto v___jp_1469_;
}
else
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_unsigned_to_nat(0u);
v___y_1470_ = v___x_1484_;
v___y_1471_ = v___x_1485_;
v___y_1472_ = v___x_1487_;
goto v___jp_1469_;
}
}
}
}
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
lean_del_object(v___x_1254_);
v___x_1497_ = lean_unsigned_to_nat(1u);
v___x_1498_ = lean_nat_add(v___x_1497_, v_size_1436_);
v___x_1499_ = lean_nat_add(v___x_1498_, v_size_1437_);
lean_dec(v_size_1437_);
v___x_1500_ = lean_nat_add(v___x_1498_, v_size_1454_);
lean_dec(v___x_1498_);
lean_inc_ref(v_l_1251_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 4, v_l_1440_);
lean_ctor_set(v___x_1452_, 3, v_l_1251_);
lean_ctor_set(v___x_1452_, 2, v_v_1250_);
lean_ctor_set(v___x_1452_, 1, v_k_1249_);
lean_ctor_set(v___x_1452_, 0, v___x_1500_);
v___x_1502_ = v___x_1452_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1515_, 3, v_l_1251_);
lean_ctor_set(v_reuseFailAlloc_1515_, 4, v_l_1440_);
v___x_1502_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
v_isSharedCheck_1509_ = !lean_is_exclusive(v_l_1251_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; lean_object* v_unused_1511_; lean_object* v_unused_1512_; lean_object* v_unused_1513_; lean_object* v_unused_1514_; 
v_unused_1510_ = lean_ctor_get(v_l_1251_, 4);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v_l_1251_, 3);
lean_dec(v_unused_1511_);
v_unused_1512_ = lean_ctor_get(v_l_1251_, 2);
lean_dec(v_unused_1512_);
v_unused_1513_ = lean_ctor_get(v_l_1251_, 1);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v_l_1251_, 0);
lean_dec(v_unused_1514_);
v___x_1504_ = v_l_1251_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_dec(v_l_1251_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 4, v_r_1441_);
lean_ctor_set(v___x_1504_, 3, v___x_1502_);
lean_ctor_set(v___x_1504_, 2, v_v_1439_);
lean_ctor_set(v___x_1504_, 1, v_k_1438_);
lean_ctor_set(v___x_1504_, 0, v___x_1499_);
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_r_1441_);
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
lean_dec_ref_known(v_l_1440_, 5);
lean_del_object(v___x_1452_);
lean_dec(v_v_1439_);
lean_dec(v_k_1438_);
lean_dec(v_size_1437_);
lean_dec_ref_known(v_l_1251_, 5);
lean_del_object(v___x_1254_);
lean_dec(v_v_1250_);
lean_dec(v_k_1249_);
v___x_1516_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7);
v___x_1517_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1516_);
return v___x_1517_;
}
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_del_object(v___x_1452_);
lean_dec(v_r_1441_);
lean_dec(v_v_1439_);
lean_dec(v_k_1438_);
lean_dec(v_size_1437_);
lean_dec_ref_known(v_l_1251_, 5);
lean_del_object(v___x_1254_);
lean_dec(v_v_1250_);
lean_dec(v_k_1249_);
v___x_1518_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8);
v___x_1519_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1518_);
return v___x_1519_;
}
}
}
}
else
{
lean_object* v_size_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
v_size_1526_ = lean_ctor_get(v_l_1251_, 0);
v___x_1527_ = lean_unsigned_to_nat(1u);
v___x_1528_ = lean_nat_add(v___x_1527_, v_size_1526_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v___x_1435_);
lean_ctor_set(v___x_1254_, 0, v___x_1528_);
v___x_1530_ = v___x_1254_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_l_1251_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v___x_1435_);
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
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_l_1532_; 
v_l_1532_ = lean_ctor_get(v___x_1435_, 3);
lean_inc(v_l_1532_);
if (lean_obj_tag(v_l_1532_) == 0)
{
lean_object* v_r_1533_; 
v_r_1533_ = lean_ctor_get(v___x_1435_, 4);
lean_inc(v_r_1533_);
if (lean_obj_tag(v_r_1533_) == 0)
{
lean_object* v_size_1534_; lean_object* v_k_1535_; lean_object* v_v_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1550_; 
v_size_1534_ = lean_ctor_get(v___x_1435_, 0);
v_k_1535_ = lean_ctor_get(v___x_1435_, 1);
v_v_1536_ = lean_ctor_get(v___x_1435_, 2);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; lean_object* v_unused_1552_; 
v_unused_1551_ = lean_ctor_get(v___x_1435_, 4);
lean_dec(v_unused_1551_);
v_unused_1552_ = lean_ctor_get(v___x_1435_, 3);
lean_dec(v_unused_1552_);
v___x_1538_ = v___x_1435_;
v_isShared_1539_ = v_isSharedCheck_1550_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_v_1536_);
lean_inc(v_k_1535_);
lean_inc(v_size_1534_);
lean_dec(v___x_1435_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1550_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v_size_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
v_size_1540_ = lean_ctor_get(v_l_1532_, 0);
v___x_1541_ = lean_unsigned_to_nat(1u);
v___x_1542_ = lean_nat_add(v___x_1541_, v_size_1534_);
lean_dec(v_size_1534_);
v___x_1543_ = lean_nat_add(v___x_1541_, v_size_1540_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v_l_1532_);
lean_ctor_set(v___x_1538_, 3, v_l_1251_);
lean_ctor_set(v___x_1538_, 2, v_v_1250_);
lean_ctor_set(v___x_1538_, 1, v_k_1249_);
lean_ctor_set(v___x_1538_, 0, v___x_1543_);
v___x_1545_ = v___x_1538_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v_l_1251_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v_l_1532_);
v___x_1545_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1547_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v_r_1533_);
lean_ctor_set(v___x_1254_, 3, v___x_1545_);
lean_ctor_set(v___x_1254_, 2, v_v_1536_);
lean_ctor_set(v___x_1254_, 1, v_k_1535_);
lean_ctor_set(v___x_1254_, 0, v___x_1542_);
v___x_1547_ = v___x_1254_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_k_1535_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_v_1536_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_r_1533_);
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
lean_object* v_k_1553_; lean_object* v_v_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1578_; 
v_k_1553_ = lean_ctor_get(v___x_1435_, 1);
v_v_1554_ = lean_ctor_get(v___x_1435_, 2);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; lean_object* v_unused_1580_; lean_object* v_unused_1581_; 
v_unused_1579_ = lean_ctor_get(v___x_1435_, 4);
lean_dec(v_unused_1579_);
v_unused_1580_ = lean_ctor_get(v___x_1435_, 3);
lean_dec(v_unused_1580_);
v_unused_1581_ = lean_ctor_get(v___x_1435_, 0);
lean_dec(v_unused_1581_);
v___x_1556_ = v___x_1435_;
v_isShared_1557_ = v_isSharedCheck_1578_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_v_1554_);
lean_inc(v_k_1553_);
lean_dec(v___x_1435_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1578_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v_k_1558_; lean_object* v_v_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1574_; 
v_k_1558_ = lean_ctor_get(v_l_1532_, 1);
v_v_1559_ = lean_ctor_get(v_l_1532_, 2);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_l_1532_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; lean_object* v_unused_1576_; lean_object* v_unused_1577_; 
v_unused_1575_ = lean_ctor_get(v_l_1532_, 4);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_l_1532_, 3);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v_l_1532_, 0);
lean_dec(v_unused_1577_);
v___x_1561_ = v_l_1532_;
v_isShared_1562_ = v_isSharedCheck_1574_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_v_1559_);
lean_inc(v_k_1558_);
lean_dec(v_l_1532_);
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
lean_ctor_set(v___x_1561_, 4, v_r_1533_);
lean_ctor_set(v___x_1561_, 3, v_r_1533_);
lean_ctor_set(v___x_1561_, 2, v_v_1250_);
lean_ctor_set(v___x_1561_, 1, v_k_1249_);
lean_ctor_set(v___x_1561_, 0, v___x_1564_);
v___x_1566_ = v___x_1561_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1573_, 3, v_r_1533_);
lean_ctor_set(v_reuseFailAlloc_1573_, 4, v_r_1533_);
v___x_1566_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1568_; 
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 3, v_r_1533_);
lean_ctor_set(v___x_1556_, 0, v___x_1564_);
v___x_1568_ = v___x_1556_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_k_1553_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_v_1554_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v_r_1533_);
lean_ctor_set(v_reuseFailAlloc_1572_, 4, v_r_1533_);
v___x_1568_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1570_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v___x_1568_);
lean_ctor_set(v___x_1254_, 3, v___x_1566_);
lean_ctor_set(v___x_1254_, 2, v_v_1559_);
lean_ctor_set(v___x_1254_, 1, v_k_1558_);
lean_ctor_set(v___x_1254_, 0, v___x_1563_);
v___x_1570_ = v___x_1254_;
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
}
else
{
lean_object* v_r_1582_; 
v_r_1582_ = lean_ctor_get(v___x_1435_, 4);
lean_inc(v_r_1582_);
if (lean_obj_tag(v_r_1582_) == 0)
{
lean_object* v_k_1583_; lean_object* v_v_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1596_; 
v_k_1583_ = lean_ctor_get(v___x_1435_, 1);
v_v_1584_ = lean_ctor_get(v___x_1435_, 2);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; lean_object* v_unused_1598_; lean_object* v_unused_1599_; 
v_unused_1597_ = lean_ctor_get(v___x_1435_, 4);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v___x_1435_, 3);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v___x_1435_, 0);
lean_dec(v_unused_1599_);
v___x_1586_ = v___x_1435_;
v_isShared_1587_ = v_isSharedCheck_1596_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_v_1584_);
lean_inc(v_k_1583_);
lean_dec(v___x_1435_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1596_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1588_ = lean_unsigned_to_nat(3u);
v___x_1589_ = lean_unsigned_to_nat(1u);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 4, v_l_1532_);
lean_ctor_set(v___x_1586_, 2, v_v_1250_);
lean_ctor_set(v___x_1586_, 1, v_k_1249_);
lean_ctor_set(v___x_1586_, 0, v___x_1589_);
v___x_1591_ = v___x_1586_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v_l_1532_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v_l_1532_);
v___x_1591_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1593_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v_r_1582_);
lean_ctor_set(v___x_1254_, 3, v___x_1591_);
lean_ctor_set(v___x_1254_, 2, v_v_1584_);
lean_ctor_set(v___x_1254_, 1, v_k_1583_);
lean_ctor_set(v___x_1254_, 0, v___x_1588_);
v___x_1593_ = v___x_1254_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_k_1583_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_v_1584_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1594_, 4, v_r_1582_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1600_ = lean_unsigned_to_nat(2u);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v___x_1435_);
lean_ctor_set(v___x_1254_, 3, v_r_1582_);
lean_ctor_set(v___x_1254_, 0, v___x_1600_);
v___x_1602_ = v___x_1254_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_r_1582_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v___x_1435_);
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
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v___x_1435_);
lean_ctor_set(v___x_1254_, 3, v___x_1435_);
lean_ctor_set(v___x_1254_, 0, v___x_1604_);
v___x_1606_ = v___x_1254_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v___x_1435_);
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
}
}
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_unsigned_to_nat(1u);
v___x_1610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v_k_1245_);
lean_ctor_set(v___x_1610_, 2, v_v_1246_);
lean_ctor_set(v___x_1610_, 3, v_t_1247_);
lean_ctor_set(v___x_1610_, 4, v_t_1247_);
return v___x_1610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore(lean_object* v_kvs_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v_fst_1631_; lean_object* v_snd_1632_; lean_object* v___x_1633_; uint8_t v_decide_1634_; 
v_fst_1631_ = lean_ctor_get(v_a_1630_, 0);
v_snd_1632_ = lean_ctor_get(v_a_1630_, 1);
v___x_1633_ = lean_string_utf8_byte_size(v_fst_1631_);
v_decide_1634_ = lean_nat_dec_eq(v_snd_1632_, v___x_1633_);
if (v_decide_1634_ == 0)
{
uint32_t v___x_1635_; uint32_t v___x_1636_; uint8_t v___x_1637_; 
v___x_1635_ = lean_string_utf8_get_fast(v_fst_1631_, v_snd_1632_);
v___x_1636_ = 34;
v___x_1637_ = lean_uint32_dec_eq(v___x_1635_, v___x_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec(v_kvs_1629_);
v___x_1638_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__1));
v___x_1639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1639_, 0, v_a_1630_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
return v___x_1639_;
}
else
{
lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1743_; 
lean_inc(v_snd_1632_);
lean_inc(v_fst_1631_);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_a_1630_);
if (v_isSharedCheck_1743_ == 0)
{
lean_object* v_unused_1744_; lean_object* v_unused_1745_; 
v_unused_1744_ = lean_ctor_get(v_a_1630_, 1);
lean_dec(v_unused_1744_);
v_unused_1745_ = lean_ctor_get(v_a_1630_, 0);
lean_dec(v_unused_1745_);
v___x_1641_ = v_a_1630_;
v_isShared_1642_ = v_isSharedCheck_1743_;
goto v_resetjp_1640_;
}
else
{
lean_dec(v_a_1630_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1743_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1643_ = lean_string_utf8_next_fast(v_fst_1631_, v_snd_1632_);
lean_dec(v_snd_1632_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 1, v___x_1643_);
v___x_1645_ = v___x_1641_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_fst_1631_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_1647_ = l_Lean_Json_Parser_strCore(v___x_1646_, v___x_1645_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_pos_1648_; lean_object* v_res_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1732_; 
v_pos_1648_ = lean_ctor_get(v___x_1647_, 0);
v_res_1649_ = lean_ctor_get(v___x_1647_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1651_ = v___x_1647_;
v_isShared_1652_ = v_isSharedCheck_1732_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_res_1649_);
lean_inc(v_pos_1648_);
lean_dec(v___x_1647_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1732_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v_fst_1653_; lean_object* v_snd_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1731_; 
v_fst_1653_ = lean_ctor_get(v_pos_1648_, 0);
v_snd_1654_ = lean_ctor_get(v_pos_1648_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_pos_1648_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1656_ = v_pos_1648_;
v_isShared_1657_ = v_isSharedCheck_1731_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_snd_1654_);
lean_inc(v_fst_1653_);
lean_dec(v_pos_1648_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1731_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1658_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1653_, v_snd_1654_);
lean_inc(v___x_1658_);
lean_inc(v_fst_1653_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 1, v___x_1658_);
v___x_1660_ = v___x_1656_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_fst_1653_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1666_; uint8_t v_decide_1667_; 
v___x_1666_ = lean_string_utf8_byte_size(v_fst_1653_);
v_decide_1667_ = lean_nat_dec_eq(v___x_1658_, v___x_1666_);
if (v_decide_1667_ == 0)
{
if (v___x_1637_ == 0)
{
lean_dec(v___x_1658_);
lean_dec(v_fst_1653_);
lean_dec(v_res_1649_);
lean_dec(v_kvs_1629_);
goto v___jp_1661_;
}
else
{
uint32_t v___x_1668_; uint32_t v___x_1669_; uint8_t v___x_1670_; 
lean_del_object(v___x_1651_);
v___x_1668_ = lean_string_utf8_get_fast(v_fst_1653_, v___x_1658_);
v___x_1669_ = 58;
v___x_1670_ = lean_uint32_dec_eq(v___x_1668_, v___x_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_dec(v___x_1658_);
lean_dec(v_fst_1653_);
lean_dec(v_res_1649_);
lean_dec(v_kvs_1629_);
v___x_1671_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__3));
v___x_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1660_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
return v___x_1672_;
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
lean_dec_ref(v___x_1660_);
v___x_1673_ = lean_string_utf8_next_fast(v_fst_1653_, v___x_1658_);
lean_dec(v___x_1658_);
v___x_1674_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1653_, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_fst_1653_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = l_Lean_Json_Parser_anyCore(v___x_1675_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_pos_1677_; lean_object* v_res_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1720_; 
v_pos_1677_ = lean_ctor_get(v___x_1676_, 0);
v_res_1678_ = lean_ctor_get(v___x_1676_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1680_ = v___x_1676_;
v_isShared_1681_ = v_isSharedCheck_1720_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_res_1678_);
lean_inc(v_pos_1677_);
lean_dec(v___x_1676_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1720_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v_fst_1687_; lean_object* v_snd_1688_; lean_object* v___x_1689_; uint8_t v_decide_1690_; 
v_fst_1687_ = lean_ctor_get(v_pos_1677_, 0);
v_snd_1688_ = lean_ctor_get(v_pos_1677_, 1);
v___x_1689_ = lean_string_utf8_byte_size(v_fst_1687_);
v_decide_1690_ = lean_nat_dec_eq(v_snd_1688_, v___x_1689_);
if (v_decide_1690_ == 0)
{
if (v___x_1670_ == 0)
{
lean_dec(v_res_1678_);
lean_dec(v_res_1649_);
lean_dec(v_kvs_1629_);
goto v___jp_1682_;
}
else
{
lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1717_; 
lean_inc(v_snd_1688_);
lean_inc(v_fst_1687_);
lean_del_object(v___x_1680_);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_pos_1677_);
if (v_isSharedCheck_1717_ == 0)
{
lean_object* v_unused_1718_; lean_object* v_unused_1719_; 
v_unused_1718_ = lean_ctor_get(v_pos_1677_, 1);
lean_dec(v_unused_1718_);
v_unused_1719_ = lean_ctor_get(v_pos_1677_, 0);
lean_dec(v_unused_1719_);
v___x_1692_ = v_pos_1677_;
v_isShared_1693_ = v_isSharedCheck_1717_;
goto v_resetjp_1691_;
}
else
{
lean_dec(v_pos_1677_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1717_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
uint32_t v___x_1694_; lean_object* v___x_1695_; uint32_t v___x_1696_; uint8_t v___x_1697_; 
v___x_1694_ = lean_string_utf8_get_fast(v_fst_1687_, v_snd_1688_);
v___x_1695_ = lean_string_utf8_next_fast(v_fst_1687_, v_snd_1688_);
lean_dec(v_snd_1688_);
v___x_1696_ = 125;
v___x_1697_ = lean_uint32_dec_eq(v___x_1694_, v___x_1696_);
if (v___x_1697_ == 0)
{
uint32_t v___x_1698_; uint8_t v___x_1699_; 
v___x_1698_ = 44;
v___x_1699_ = lean_uint32_dec_eq(v___x_1694_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1701_; 
lean_dec(v_res_1678_);
lean_dec(v_res_1649_);
lean_dec(v_kvs_1629_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 1, v___x_1695_);
v___x_1701_ = v___x_1692_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_fst_1687_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v___x_1695_);
v___x_1701_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__5));
v___x_1703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
return v___x_1703_;
}
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1705_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1687_, v___x_1695_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 1, v___x_1705_);
v___x_1707_ = v___x_1692_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_fst_1687_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_res_1649_, v_res_1678_, v_kvs_1629_);
v_kvs_1629_ = v___x_1708_;
v_a_1630_ = v___x_1707_;
goto _start;
}
}
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1711_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1687_, v___x_1695_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 1, v___x_1711_);
v___x_1713_ = v___x_1692_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_fst_1687_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_res_1649_, v_res_1678_, v_kvs_1629_);
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
return v___x_1715_;
}
}
}
}
}
else
{
lean_dec(v_res_1678_);
lean_dec(v_res_1649_);
lean_dec(v_kvs_1629_);
goto v___jp_1682_;
}
v___jp_1682_:
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1683_ = lean_box(0);
if (v_isShared_1681_ == 0)
{
lean_ctor_set_tag(v___x_1680_, 1);
lean_ctor_set(v___x_1680_, 1, v___x_1683_);
v___x_1685_ = v___x_1680_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_pos_1677_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v___x_1683_);
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
lean_object* v_pos_1721_; lean_object* v_err_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec(v_res_1649_);
lean_dec(v_kvs_1629_);
v_pos_1721_ = lean_ctor_get(v___x_1676_, 0);
v_err_1722_ = lean_ctor_get(v___x_1676_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1676_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_err_1722_);
lean_inc(v_pos_1721_);
lean_dec(v___x_1676_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_pos_1721_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_err_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1658_);
lean_dec(v_fst_1653_);
lean_dec(v_res_1649_);
lean_dec(v_kvs_1629_);
goto v___jp_1661_;
}
v___jp_1661_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1662_ = lean_box(0);
if (v_isShared_1652_ == 0)
{
lean_ctor_set_tag(v___x_1651_, 1);
lean_ctor_set(v___x_1651_, 1, v___x_1662_);
lean_ctor_set(v___x_1651_, 0, v___x_1660_);
v___x_1664_ = v___x_1651_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1733_; lean_object* v_err_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_dec(v_kvs_1629_);
v_pos_1733_ = lean_ctor_get(v___x_1647_, 0);
v_err_1734_ = lean_ctor_get(v___x_1647_, 1);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1647_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_err_1734_);
lean_inc(v_pos_1733_);
lean_dec(v___x_1647_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_pos_1733_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_err_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec(v_kvs_1629_);
v___x_1746_ = lean_box(0);
v___x_1747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1747_, 0, v_a_1630_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
return v___x_1747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object* v_a_1754_){
_start:
{
lean_object* v_fst_1789_; lean_object* v_snd_1790_; lean_object* v___x_1791_; uint8_t v_decide_1792_; 
v_fst_1789_ = lean_ctor_get(v_a_1754_, 0);
v_snd_1790_ = lean_ctor_get(v_a_1754_, 1);
v___x_1791_ = lean_string_utf8_byte_size(v_fst_1789_);
v_decide_1792_ = lean_nat_dec_eq(v_snd_1790_, v___x_1791_);
if (v_decide_1792_ == 0)
{
uint32_t v___x_1793_; uint32_t v___x_1794_; uint8_t v___x_1795_; 
v___x_1793_ = lean_string_utf8_get_fast(v_fst_1789_, v_snd_1790_);
v___x_1794_ = 91;
v___x_1795_ = lean_uint32_dec_eq(v___x_1793_, v___x_1794_);
if (v___x_1795_ == 0)
{
uint32_t v___x_1796_; uint8_t v___x_1797_; 
v___x_1796_ = 123;
v___x_1797_ = lean_uint32_dec_eq(v___x_1793_, v___x_1796_);
if (v___x_1797_ == 0)
{
uint32_t v___x_1798_; uint8_t v___x_1799_; 
v___x_1798_ = 34;
v___x_1799_ = lean_uint32_dec_eq(v___x_1793_, v___x_1798_);
if (v___x_1799_ == 0)
{
uint32_t v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = 102;
v___x_1801_ = lean_uint32_dec_eq(v___x_1793_, v___x_1800_);
if (v___x_1801_ == 0)
{
uint32_t v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = 116;
v___x_1803_ = lean_uint32_dec_eq(v___x_1793_, v___x_1802_);
if (v___x_1803_ == 0)
{
uint32_t v___x_1804_; uint8_t v___x_1805_; 
v___x_1804_ = 110;
v___x_1805_ = lean_uint32_dec_eq(v___x_1793_, v___x_1804_);
if (v___x_1805_ == 0)
{
uint32_t v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = 45;
v___x_1807_ = lean_uint32_dec_eq(v___x_1793_, v___x_1806_);
if (v___x_1807_ == 0)
{
uint32_t v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = 48;
v___x_1809_ = lean_uint32_dec_le(v___x_1808_, v___x_1793_);
if (v___x_1809_ == 0)
{
goto v___jp_1786_;
}
else
{
uint32_t v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = 57;
v___x_1811_ = lean_uint32_dec_le(v___x_1793_, v___x_1810_);
if (v___x_1811_ == 0)
{
goto v___jp_1786_;
}
else
{
goto v___jp_1755_;
}
}
}
else
{
goto v___jp_1755_;
}
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__2));
v___x_1813_ = l_Std_Internal_Parsec_String_pstring(v___x_1812_, v_a_1754_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_pos_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1832_; 
v_pos_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1832_ == 0)
{
lean_object* v_unused_1833_; 
v_unused_1833_ = lean_ctor_get(v___x_1813_, 1);
lean_dec(v_unused_1833_);
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1832_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_pos_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1832_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v_fst_1818_; lean_object* v_snd_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1831_; 
v_fst_1818_ = lean_ctor_get(v_pos_1814_, 0);
v_snd_1819_ = lean_ctor_get(v_pos_1814_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_pos_1814_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1821_ = v_pos_1814_;
v_isShared_1822_ = v_isSharedCheck_1831_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_snd_1819_);
lean_inc(v_fst_1818_);
lean_dec(v_pos_1814_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1831_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1823_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1818_, v_snd_1819_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 1, v___x_1823_);
v___x_1825_ = v___x_1821_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_fst_1818_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1826_ = lean_box(0);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 1, v___x_1826_);
lean_ctor_set(v___x_1816_, 0, v___x_1825_);
v___x_1828_ = v___x_1816_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
else
{
lean_object* v_pos_1834_; lean_object* v_err_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
v_pos_1834_ = lean_ctor_get(v___x_1813_, 0);
v_err_1835_ = lean_ctor_get(v___x_1813_, 1);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1813_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_err_1835_);
lean_inc(v_pos_1834_);
lean_dec(v___x_1813_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_pos_1834_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_err_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__3));
v___x_1844_ = l_Std_Internal_Parsec_String_pstring(v___x_1843_, v_a_1754_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_pos_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1863_; 
v_pos_1845_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; 
v_unused_1864_ = lean_ctor_get(v___x_1844_, 1);
lean_dec(v_unused_1864_);
v___x_1847_ = v___x_1844_;
v_isShared_1848_ = v_isSharedCheck_1863_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_pos_1845_);
lean_dec(v___x_1844_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1863_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v_fst_1849_; lean_object* v_snd_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1862_; 
v_fst_1849_ = lean_ctor_get(v_pos_1845_, 0);
v_snd_1850_ = lean_ctor_get(v_pos_1845_, 1);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_pos_1845_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1852_ = v_pos_1845_;
v_isShared_1853_ = v_isSharedCheck_1862_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_snd_1850_);
lean_inc(v_fst_1849_);
lean_dec(v_pos_1845_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1862_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1854_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1849_, v_snd_1850_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 1, v___x_1854_);
v___x_1856_ = v___x_1852_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_fst_1849_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1857_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1857_, 0, v___x_1803_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 1, v___x_1857_);
lean_ctor_set(v___x_1847_, 0, v___x_1856_);
v___x_1859_ = v___x_1847_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1856_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
else
{
lean_object* v_pos_1865_; lean_object* v_err_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
v_pos_1865_ = lean_ctor_get(v___x_1844_, 0);
v_err_1866_ = lean_ctor_get(v___x_1844_, 1);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1844_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_err_1866_);
lean_inc(v_pos_1865_);
lean_dec(v___x_1844_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_pos_1865_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_err_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__4));
v___x_1875_ = l_Std_Internal_Parsec_String_pstring(v___x_1874_, v_a_1754_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_pos_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1894_; 
v_pos_1876_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1894_ == 0)
{
lean_object* v_unused_1895_; 
v_unused_1895_ = lean_ctor_get(v___x_1875_, 1);
lean_dec(v_unused_1895_);
v___x_1878_ = v___x_1875_;
v_isShared_1879_ = v_isSharedCheck_1894_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_pos_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1894_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v_fst_1880_; lean_object* v_snd_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1893_; 
v_fst_1880_ = lean_ctor_get(v_pos_1876_, 0);
v_snd_1881_ = lean_ctor_get(v_pos_1876_, 1);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_pos_1876_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1883_ = v_pos_1876_;
v_isShared_1884_ = v_isSharedCheck_1893_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_snd_1881_);
lean_inc(v_fst_1880_);
lean_dec(v_pos_1876_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1893_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1885_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1880_, v_snd_1881_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 1, v___x_1885_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_fst_1880_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1888_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1888_, 0, v___x_1799_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v___x_1888_);
lean_ctor_set(v___x_1878_, 0, v___x_1887_);
v___x_1890_ = v___x_1878_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
else
{
lean_object* v_pos_1896_; lean_object* v_err_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
v_pos_1896_ = lean_ctor_get(v___x_1875_, 0);
v_err_1897_ = lean_ctor_get(v___x_1875_, 1);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1875_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_err_1897_);
lean_inc(v_pos_1896_);
lean_dec(v___x_1875_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_pos_1896_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_err_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
else
{
lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1943_; 
lean_inc(v_snd_1790_);
lean_inc(v_fst_1789_);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_a_1754_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; lean_object* v_unused_1945_; 
v_unused_1944_ = lean_ctor_get(v_a_1754_, 1);
lean_dec(v_unused_1944_);
v_unused_1945_ = lean_ctor_get(v_a_1754_, 0);
lean_dec(v_unused_1945_);
v___x_1906_ = v_a_1754_;
v_isShared_1907_ = v_isSharedCheck_1943_;
goto v_resetjp_1905_;
}
else
{
lean_dec(v_a_1754_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1943_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1908_ = lean_string_utf8_next_fast(v_fst_1789_, v_snd_1790_);
lean_dec(v_snd_1790_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 1, v___x_1908_);
v___x_1910_ = v___x_1906_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_fst_1789_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_1912_ = l_Lean_Json_Parser_strCore(v___x_1911_, v___x_1910_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_pos_1913_; lean_object* v_res_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1932_; 
v_pos_1913_ = lean_ctor_get(v___x_1912_, 0);
v_res_1914_ = lean_ctor_get(v___x_1912_, 1);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1916_ = v___x_1912_;
v_isShared_1917_ = v_isSharedCheck_1932_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_res_1914_);
lean_inc(v_pos_1913_);
lean_dec(v___x_1912_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1932_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v_fst_1918_; lean_object* v_snd_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1931_; 
v_fst_1918_ = lean_ctor_get(v_pos_1913_, 0);
v_snd_1919_ = lean_ctor_get(v_pos_1913_, 1);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_pos_1913_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1921_ = v_pos_1913_;
v_isShared_1922_ = v_isSharedCheck_1931_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_snd_1919_);
lean_inc(v_fst_1918_);
lean_dec(v_pos_1913_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1931_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1923_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1918_, v_snd_1919_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 1, v___x_1923_);
v___x_1925_ = v___x_1921_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_fst_1918_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1926_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_res_1914_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 1, v___x_1926_);
lean_ctor_set(v___x_1916_, 0, v___x_1925_);
v___x_1928_ = v___x_1916_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___x_1926_);
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
else
{
lean_object* v_pos_1933_; lean_object* v_err_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
v_pos_1933_ = lean_ctor_get(v___x_1912_, 0);
v_err_1934_ = lean_ctor_get(v___x_1912_, 1);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1912_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_err_1934_);
lean_inc(v_pos_1933_);
lean_dec(v___x_1912_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_pos_1933_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_err_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1988_; 
lean_inc(v_snd_1790_);
lean_inc(v_fst_1789_);
v_isSharedCheck_1988_ = !lean_is_exclusive(v_a_1754_);
if (v_isSharedCheck_1988_ == 0)
{
lean_object* v_unused_1989_; lean_object* v_unused_1990_; 
v_unused_1989_ = lean_ctor_get(v_a_1754_, 1);
lean_dec(v_unused_1989_);
v_unused_1990_ = lean_ctor_get(v_a_1754_, 0);
lean_dec(v_unused_1990_);
v___x_1947_ = v_a_1754_;
v_isShared_1948_ = v_isSharedCheck_1988_;
goto v_resetjp_1946_;
}
else
{
lean_dec(v_a_1754_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1988_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1949_ = lean_string_utf8_next_fast(v_fst_1789_, v_snd_1790_);
lean_dec(v_snd_1790_);
v___x_1950_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1789_, v___x_1949_);
lean_inc(v___x_1950_);
lean_inc(v_fst_1789_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 1, v___x_1950_);
v___x_1952_ = v___x_1947_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_fst_1789_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
uint8_t v___y_1954_; uint8_t v_decide_1986_; 
v_decide_1986_ = lean_nat_dec_eq(v___x_1950_, v___x_1791_);
if (v_decide_1986_ == 0)
{
v___y_1954_ = v___x_1797_;
goto v___jp_1953_;
}
else
{
v___y_1954_ = v___x_1795_;
goto v___jp_1953_;
}
v___jp_1953_:
{
if (v___y_1954_ == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_dec(v___x_1950_);
lean_dec(v_fst_1789_);
v___x_1955_ = lean_box(0);
v___x_1956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1952_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
return v___x_1956_;
}
else
{
uint32_t v___x_1957_; uint32_t v___x_1958_; uint8_t v___x_1959_; 
v___x_1957_ = lean_string_utf8_get_fast(v_fst_1789_, v___x_1950_);
v___x_1958_ = 125;
v___x_1959_ = lean_uint32_dec_eq(v___x_1957_, v___x_1958_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_dec(v___x_1950_);
lean_dec(v_fst_1789_);
v___x_1960_ = lean_box(1);
v___x_1961_ = l_Lean_Json_Parser_objectCore(v___x_1960_, v___x_1952_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_pos_1962_; lean_object* v_res_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1971_; 
v_pos_1962_ = lean_ctor_get(v___x_1961_, 0);
v_res_1963_ = lean_ctor_get(v___x_1961_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1965_ = v___x_1961_;
v_isShared_1966_ = v_isSharedCheck_1971_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_res_1963_);
lean_inc(v_pos_1962_);
lean_dec(v___x_1961_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1971_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1967_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_res_1963_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 1, v___x_1967_);
v___x_1969_ = v___x_1965_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_pos_1962_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
else
{
lean_object* v_pos_1972_; lean_object* v_err_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
v_pos_1972_ = lean_ctor_get(v___x_1961_, 0);
v_err_1973_ = lean_ctor_get(v___x_1961_, 1);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1961_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_err_1973_);
lean_inc(v_pos_1972_);
lean_dec(v___x_1961_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_pos_1972_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v_err_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_dec_ref(v___x_1952_);
v___x_1981_ = lean_string_utf8_next_fast(v_fst_1789_, v___x_1950_);
lean_dec(v___x_1950_);
v___x_1982_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1789_, v___x_1981_);
v___x_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1983_, 0, v_fst_1789_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
v___x_1984_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__5));
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
return v___x_1985_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2033_; 
lean_inc(v_snd_1790_);
lean_inc(v_fst_1789_);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_a_1754_);
if (v_isSharedCheck_2033_ == 0)
{
lean_object* v_unused_2034_; lean_object* v_unused_2035_; 
v_unused_2034_ = lean_ctor_get(v_a_1754_, 1);
lean_dec(v_unused_2034_);
v_unused_2035_ = lean_ctor_get(v_a_1754_, 0);
lean_dec(v_unused_2035_);
v___x_1992_ = v_a_1754_;
v_isShared_1993_ = v_isSharedCheck_2033_;
goto v_resetjp_1991_;
}
else
{
lean_dec(v_a_1754_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2033_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1994_ = lean_string_utf8_next_fast(v_fst_1789_, v_snd_1790_);
lean_dec(v_snd_1790_);
v___x_1995_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1789_, v___x_1994_);
lean_inc(v___x_1995_);
lean_inc(v_fst_1789_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 1, v___x_1995_);
v___x_1997_ = v___x_1992_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_fst_1789_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_2032_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
uint8_t v_decide_2001_; 
v_decide_2001_ = lean_nat_dec_eq(v___x_1995_, v___x_1791_);
if (v_decide_2001_ == 0)
{
if (v___x_1795_ == 0)
{
lean_dec(v___x_1995_);
lean_dec(v_fst_1789_);
goto v___jp_1998_;
}
else
{
uint32_t v___x_2002_; uint32_t v___x_2003_; uint8_t v___x_2004_; 
v___x_2002_ = lean_string_utf8_get_fast(v_fst_1789_, v___x_1995_);
v___x_2003_ = 93;
v___x_2004_ = lean_uint32_dec_eq(v___x_2002_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
lean_dec(v___x_1995_);
lean_dec(v_fst_1789_);
v___x_2005_ = lean_unsigned_to_nat(4u);
v___x_2006_ = lean_mk_empty_array_with_capacity(v___x_2005_);
v___x_2007_ = l_Lean_Json_Parser_arrayCore(v___x_2006_, v___x_1997_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_pos_2008_; lean_object* v_res_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2017_; 
v_pos_2008_ = lean_ctor_get(v___x_2007_, 0);
v_res_2009_ = lean_ctor_get(v___x_2007_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2011_ = v___x_2007_;
v_isShared_2012_ = v_isSharedCheck_2017_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_res_2009_);
lean_inc(v_pos_2008_);
lean_dec(v___x_2007_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2017_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; lean_object* v___x_2015_; 
v___x_2013_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2013_, 0, v_res_2009_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 1, v___x_2013_);
v___x_2015_ = v___x_2011_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_pos_2008_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
else
{
lean_object* v_pos_2018_; lean_object* v_err_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
v_pos_2018_ = lean_ctor_get(v___x_2007_, 0);
v_err_2019_ = lean_ctor_get(v___x_2007_, 1);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_2007_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_err_2019_);
lean_inc(v_pos_2018_);
lean_dec(v___x_2007_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_pos_2018_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_err_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
lean_dec_ref(v___x_1997_);
v___x_2027_ = lean_string_utf8_next_fast(v_fst_1789_, v___x_1995_);
lean_dec(v___x_1995_);
v___x_2028_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1789_, v___x_2027_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v_fst_1789_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__7));
v___x_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2029_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
return v___x_2031_;
}
}
}
else
{
lean_dec(v___x_1995_);
lean_dec(v_fst_1789_);
goto v___jp_1998_;
}
v___jp_1998_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_box(0);
v___x_2000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1997_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
return v___x_2000_;
}
}
}
}
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = lean_box(0);
v___x_2037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2037_, 0, v_a_1754_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
return v___x_2037_;
}
v___jp_1755_:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_Json_Parser_num(v_a_1754_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_pos_1757_; lean_object* v_res_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1776_; 
v_pos_1757_ = lean_ctor_get(v___x_1756_, 0);
v_res_1758_ = lean_ctor_get(v___x_1756_, 1);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1760_ = v___x_1756_;
v_isShared_1761_ = v_isSharedCheck_1776_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_res_1758_);
lean_inc(v_pos_1757_);
lean_dec(v___x_1756_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1776_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v_fst_1762_; lean_object* v_snd_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1775_; 
v_fst_1762_ = lean_ctor_get(v_pos_1757_, 0);
v_snd_1763_ = lean_ctor_get(v_pos_1757_, 1);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_pos_1757_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1765_ = v_pos_1757_;
v_isShared_1766_ = v_isSharedCheck_1775_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_snd_1763_);
lean_inc(v_fst_1762_);
lean_dec(v_pos_1757_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1775_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1767_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1762_, v_snd_1763_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 1, v___x_1767_);
v___x_1769_ = v___x_1765_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_fst_1762_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1770_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_res_1758_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 1, v___x_1770_);
lean_ctor_set(v___x_1760_, 0, v___x_1769_);
v___x_1772_ = v___x_1760_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v___x_1770_);
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
}
else
{
lean_object* v_pos_1777_; lean_object* v_err_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
v_pos_1777_ = lean_ctor_get(v___x_1756_, 0);
v_err_1778_ = lean_ctor_get(v___x_1756_, 1);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1756_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_err_1778_);
lean_inc(v_pos_1777_);
lean_dec(v___x_1756_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_pos_1777_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_err_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
v___jp_1786_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__1));
v___x_1788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1788_, 0, v_a_1754_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
return v___x_1788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore(lean_object* v_acc_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Lean_Json_Parser_anyCore(v_a_2039_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_pos_2041_; lean_object* v_res_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2086_; 
v_pos_2041_ = lean_ctor_get(v___x_2040_, 0);
v_res_2042_ = lean_ctor_get(v___x_2040_, 1);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2044_ = v___x_2040_;
v_isShared_2045_ = v_isSharedCheck_2086_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_res_2042_);
lean_inc(v_pos_2041_);
lean_dec(v___x_2040_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2086_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v_fst_2046_; lean_object* v_snd_2047_; lean_object* v___x_2048_; uint8_t v_decide_2049_; 
v_fst_2046_ = lean_ctor_get(v_pos_2041_, 0);
v_snd_2047_ = lean_ctor_get(v_pos_2041_, 1);
v___x_2048_ = lean_string_utf8_byte_size(v_fst_2046_);
v_decide_2049_ = lean_nat_dec_eq(v_snd_2047_, v___x_2048_);
if (v_decide_2049_ == 0)
{
lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2079_; 
lean_inc(v_snd_2047_);
lean_inc(v_fst_2046_);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_pos_2041_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; lean_object* v_unused_2081_; 
v_unused_2080_ = lean_ctor_get(v_pos_2041_, 1);
lean_dec(v_unused_2080_);
v_unused_2081_ = lean_ctor_get(v_pos_2041_, 0);
lean_dec(v_unused_2081_);
v___x_2051_ = v_pos_2041_;
v_isShared_2052_ = v_isSharedCheck_2079_;
goto v_resetjp_2050_;
}
else
{
lean_dec(v_pos_2041_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2079_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; uint32_t v___x_2054_; lean_object* v___x_2055_; uint32_t v___x_2056_; uint8_t v___x_2057_; 
v___x_2053_ = lean_array_push(v_acc_2038_, v_res_2042_);
v___x_2054_ = lean_string_utf8_get_fast(v_fst_2046_, v_snd_2047_);
v___x_2055_ = lean_string_utf8_next_fast(v_fst_2046_, v_snd_2047_);
lean_dec(v_snd_2047_);
v___x_2056_ = 93;
v___x_2057_ = lean_uint32_dec_eq(v___x_2054_, v___x_2056_);
if (v___x_2057_ == 0)
{
uint32_t v___x_2058_; uint8_t v___x_2059_; 
v___x_2058_ = 44;
v___x_2059_ = lean_uint32_dec_eq(v___x_2054_, v___x_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2061_; 
lean_dec_ref(v___x_2053_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v___x_2055_);
v___x_2061_ = v___x_2051_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_fst_2046_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v___x_2055_);
v___x_2061_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2062_; lean_object* v___x_2064_; 
v___x_2062_ = ((lean_object*)(l_Lean_Json_Parser_arrayCore___closed__1));
if (v_isShared_2045_ == 0)
{
lean_ctor_set_tag(v___x_2044_, 1);
lean_ctor_set(v___x_2044_, 1, v___x_2062_);
lean_ctor_set(v___x_2044_, 0, v___x_2061_);
v___x_2064_ = v___x_2044_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
else
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
lean_del_object(v___x_2044_);
v___x_2067_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2046_, v___x_2055_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v___x_2067_);
v___x_2069_ = v___x_2051_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_fst_2046_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
v_acc_2038_ = v___x_2053_;
v_a_2039_ = v___x_2069_;
goto _start;
}
}
}
else
{
lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2072_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2046_, v___x_2055_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v___x_2072_);
v___x_2074_ = v___x_2051_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_fst_2046_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2076_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 1, v___x_2053_);
lean_ctor_set(v___x_2044_, 0, v___x_2074_);
v___x_2076_ = v___x_2044_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___x_2053_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2084_; 
lean_dec(v_res_2042_);
lean_dec_ref(v_acc_2038_);
v___x_2082_ = lean_box(0);
if (v_isShared_2045_ == 0)
{
lean_ctor_set_tag(v___x_2044_, 1);
lean_ctor_set(v___x_2044_, 1, v___x_2082_);
v___x_2084_ = v___x_2044_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_pos_2041_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___x_2082_);
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
else
{
lean_object* v_pos_2087_; lean_object* v_err_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec_ref(v_acc_2038_);
v_pos_2087_ = lean_ctor_get(v___x_2040_, 0);
v_err_2088_ = lean_ctor_get(v___x_2040_, 1);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2040_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_err_2088_);
lean_inc(v_pos_2087_);
lean_dec(v___x_2040_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_pos_2087_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_err_2088_);
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
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2(lean_object* v_00_u03b2_2096_, lean_object* v_msg_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v_msg_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2(lean_object* v_00_u03b2_2099_, lean_object* v_k_2100_, lean_object* v_v_2101_, lean_object* v_t_2102_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_2100_, v_v_2101_, v_t_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_any(lean_object* v_a_2107_){
_start:
{
lean_object* v_fst_2108_; lean_object* v_snd_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2133_; 
v_fst_2108_ = lean_ctor_get(v_a_2107_, 0);
v_snd_2109_ = lean_ctor_get(v_a_2107_, 1);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_a_2107_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2111_ = v_a_2107_;
v_isShared_2112_ = v_isSharedCheck_2133_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_snd_2109_);
lean_inc(v_fst_2108_);
lean_dec(v_a_2107_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2133_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2113_; lean_object* v___x_2115_; 
v___x_2113_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2108_, v_snd_2109_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v___x_2113_);
v___x_2115_ = v___x_2111_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_fst_2108_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Lean_Json_Parser_anyCore(v___x_2115_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_pos_2117_; lean_object* v_fst_2118_; lean_object* v_snd_2119_; lean_object* v___x_2120_; uint8_t v_decide_2121_; 
v_pos_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_pos_2117_);
v_fst_2118_ = lean_ctor_get(v_pos_2117_, 0);
v_snd_2119_ = lean_ctor_get(v_pos_2117_, 1);
v___x_2120_ = lean_string_utf8_byte_size(v_fst_2118_);
v_decide_2121_ = lean_nat_dec_eq(v_snd_2119_, v___x_2120_);
if (v_decide_2121_ == 0)
{
lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2129_; 
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; lean_object* v_unused_2131_; 
v_unused_2130_ = lean_ctor_get(v___x_2116_, 1);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v___x_2116_, 0);
lean_dec(v_unused_2131_);
v___x_2123_ = v___x_2116_;
v_isShared_2124_ = v_isSharedCheck_2129_;
goto v_resetjp_2122_;
}
else
{
lean_dec(v___x_2116_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2129_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
v___x_2125_ = ((lean_object*)(l_Lean_Json_Parser_any___closed__1));
if (v_isShared_2124_ == 0)
{
lean_ctor_set_tag(v___x_2123_, 1);
lean_ctor_set(v___x_2123_, 1, v___x_2125_);
v___x_2127_ = v___x_2123_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_pos_2117_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
else
{
lean_dec(v_pos_2117_);
return v___x_2116_;
}
}
else
{
return v___x_2116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parse(lean_object* v_s_2134_){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
v___x_2136_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_2135_, v_s_2134_);
return v___x_2136_;
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
