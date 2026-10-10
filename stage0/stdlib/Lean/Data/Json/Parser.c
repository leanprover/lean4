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
lean_object* l_Lean_Json_Parser_finishSurrogatePair(uint16_t v_low_58_, lean_object* v_a_59_){
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
LEAN_EXPORT void l_Lean_Json_Parser_finishSurrogatePair_0interp(lean_interpreter_value* stack)
{
uint16_t v_low_58_ = stack[0].m_num;
lean_object* v_a_59_ = stack[1].m_obj;
lean_object* v_res_190_;
v_res_190_ = l_Lean_Json_Parser_finishSurrogatePair(v_low_58_, v_a_59_);
stack->m_obj
 = v_res_190_;
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair___boxed(lean_object* v_low_191_, lean_object* v_a_192_){
_start:
{
uint16_t v_low_boxed_193_; lean_object* v_res_194_; 
v_low_boxed_193_ = lean_unbox(v_low_191_);
v_res_194_ = l_Lean_Json_Parser_finishSurrogatePair(v_low_boxed_193_, v_a_192_);
return v_res_194_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_198_; lean_object* v___x_199_; 
v___x_198_ = 65533;
v___x_199_ = lean_box_uint32(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_200_; lean_object* v___x_201_; 
v___x_200_ = 9;
v___x_201_ = lean_box_uint32(v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_202_; lean_object* v___x_203_; 
v___x_202_ = 13;
v___x_203_ = lean_box_uint32(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_204_; lean_object* v___x_205_; 
v___x_204_ = 10;
v___x_205_ = lean_box_uint32(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_206_; lean_object* v___x_207_; 
v___x_206_ = 12;
v___x_207_ = lean_box_uint32(v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_208_; lean_object* v___x_209_; 
v___x_208_ = 8;
v___x_209_ = lean_box_uint32(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__7(void){
_start:
{
uint32_t v___x_210_; lean_object* v___x_211_; 
v___x_210_ = 47;
v___x_211_ = lean_box_uint32(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__8(void){
_start:
{
uint32_t v___x_212_; lean_object* v___x_213_; 
v___x_212_ = 34;
v___x_213_ = lean_box_uint32(v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__9(void){
_start:
{
uint32_t v___x_214_; lean_object* v___x_215_; 
v___x_214_ = 92;
v___x_215_ = lean_box_uint32(v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar(lean_object* v_a_216_){
_start:
{
lean_object* v_fst_217_; lean_object* v_snd_218_; lean_object* v___x_219_; uint8_t v_decide_220_; 
v_fst_217_ = lean_ctor_get(v_a_216_, 0);
v_snd_218_ = lean_ctor_get(v_a_216_, 1);
v___x_219_ = lean_string_utf8_byte_size(v_fst_217_);
v_decide_220_ = lean_nat_dec_eq(v_snd_218_, v___x_219_);
if (v_decide_220_ == 0)
{
lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_375_; 
lean_inc(v_snd_218_);
lean_inc(v_fst_217_);
v_isSharedCheck_375_ = !lean_is_exclusive(v_a_216_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; lean_object* v_unused_377_; 
v_unused_376_ = lean_ctor_get(v_a_216_, 1);
lean_dec(v_unused_376_);
v_unused_377_ = lean_ctor_get(v_a_216_, 0);
lean_dec(v_unused_377_);
v___x_222_ = v_a_216_;
v_isShared_223_ = v_isSharedCheck_375_;
goto v_resetjp_221_;
}
else
{
lean_dec(v_a_216_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_375_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
uint32_t v_c_224_; lean_object* v___x_225_; lean_object* v_it_x27_227_; 
v_c_224_ = lean_string_utf8_get_fast(v_fst_217_, v_snd_218_);
v___x_225_ = lean_string_utf8_next_fast(v_fst_217_, v_snd_218_);
lean_dec(v_snd_218_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 1, v___x_225_);
v_it_x27_227_ = v___x_222_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_fst_217_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v___x_225_);
v_it_x27_227_ = v_reuseFailAlloc_374_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
uint32_t v___x_228_; uint8_t v___x_229_; 
v___x_228_ = 92;
v___x_229_ = lean_uint32_dec_eq(v_c_224_, v___x_228_);
if (v___x_229_ == 0)
{
uint32_t v___x_230_; uint8_t v___x_231_; 
v___x_230_ = 34;
v___x_231_ = lean_uint32_dec_eq(v_c_224_, v___x_230_);
if (v___x_231_ == 0)
{
uint32_t v___x_232_; uint8_t v___x_233_; 
v___x_232_ = 47;
v___x_233_ = lean_uint32_dec_eq(v_c_224_, v___x_232_);
if (v___x_233_ == 0)
{
uint32_t v___x_234_; uint8_t v___x_235_; 
v___x_234_ = 98;
v___x_235_ = lean_uint32_dec_eq(v_c_224_, v___x_234_);
if (v___x_235_ == 0)
{
uint32_t v___x_236_; uint8_t v___x_237_; 
v___x_236_ = 102;
v___x_237_ = lean_uint32_dec_eq(v_c_224_, v___x_236_);
if (v___x_237_ == 0)
{
uint32_t v___x_238_; uint8_t v___x_239_; 
v___x_238_ = 110;
v___x_239_ = lean_uint32_dec_eq(v_c_224_, v___x_238_);
if (v___x_239_ == 0)
{
uint32_t v___x_240_; uint8_t v___x_241_; 
v___x_240_ = 114;
v___x_241_ = lean_uint32_dec_eq(v_c_224_, v___x_240_);
if (v___x_241_ == 0)
{
uint32_t v___x_242_; uint8_t v___x_243_; 
v___x_242_ = 116;
v___x_243_ = lean_uint32_dec_eq(v_c_224_, v___x_242_);
if (v___x_243_ == 0)
{
uint32_t v___x_244_; uint8_t v___x_245_; 
v___x_244_ = 117;
v___x_245_ = lean_uint32_dec_eq(v_c_224_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = ((lean_object*)(l_Lean_Json_Parser_escapedChar___closed__1));
v___x_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_247_, 0, v_it_x27_227_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
return v___x_247_;
}
else
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Json_Parser_hexChar(v_it_x27_227_);
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
lean_object* v_pos_255_; lean_object* v_res_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_330_; 
v_pos_255_ = lean_ctor_get(v___x_254_, 0);
v_res_256_ = lean_ctor_get(v___x_254_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_330_ == 0)
{
v___x_258_ = v___x_254_;
v_isShared_259_ = v_isSharedCheck_330_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_res_256_);
lean_inc(v_pos_255_);
lean_dec(v___x_254_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_330_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Json_Parser_hexChar(v_pos_255_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_pos_261_; lean_object* v_res_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_320_; 
v_pos_261_ = lean_ctor_get(v___x_260_, 0);
v_res_262_ = lean_ctor_get(v___x_260_, 1);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_320_ == 0)
{
v___x_264_ = v___x_260_;
v_isShared_265_ = v_isSharedCheck_320_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_res_262_);
lean_inc(v_pos_261_);
lean_dec(v___x_260_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_320_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___y_267_; lean_object* v_pos_268_; uint16_t v___x_276_; uint16_t v___x_277_; uint16_t v___x_278_; uint16_t v___x_279_; uint16_t v___x_280_; uint16_t v___x_281_; uint16_t v___x_282_; uint16_t v___x_283_; uint16_t v___x_284_; uint16_t v___x_285_; uint16_t v___x_286_; uint16_t v___x_287_; uint16_t v___x_288_; uint16_t v___x_289_; uint8_t v___x_290_; 
v___x_276_ = 12;
v___x_277_ = lean_unbox(v_res_250_);
lean_dec(v_res_250_);
v___x_278_ = lean_uint16_shift_left(v___x_277_, v___x_276_);
v___x_279_ = 8;
v___x_280_ = lean_unbox(v_res_253_);
lean_dec(v_res_253_);
v___x_281_ = lean_uint16_shift_left(v___x_280_, v___x_279_);
v___x_282_ = lean_uint16_lor(v___x_278_, v___x_281_);
v___x_283_ = 4;
v___x_284_ = lean_unbox(v_res_256_);
lean_dec(v_res_256_);
v___x_285_ = lean_uint16_shift_left(v___x_284_, v___x_283_);
v___x_286_ = lean_uint16_lor(v___x_282_, v___x_285_);
v___x_287_ = lean_unbox(v_res_262_);
lean_dec(v_res_262_);
v___x_288_ = lean_uint16_lor(v___x_286_, v___x_287_);
v___x_289_ = 55296;
v___x_290_ = lean_uint16_dec_lt(v___x_288_, v___x_289_);
if (v___x_290_ == 0)
{
uint16_t v___x_291_; uint8_t v___x_292_; 
v___x_291_ = 57344;
v___x_292_ = lean_uint16_dec_lt(v___x_288_, v___x_291_);
if (v___x_292_ == 0)
{
uint32_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
lean_del_object(v___x_264_);
v___x_293_ = lean_uint16_to_uint32(v___x_288_);
v___x_294_ = lean_box_uint32(v___x_293_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v___x_294_);
lean_ctor_set(v___x_258_, 0, v_pos_261_);
v___x_296_ = v___x_258_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_pos_261_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_294_);
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
uint16_t v___x_298_; uint8_t v___x_299_; 
v___x_298_ = 56320;
v___x_299_ = lean_uint16_dec_lt(v___x_288_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_302_; 
lean_del_object(v___x_264_);
v___x_300_ = l_Lean_Json_Parser_escapedChar___boxed__const__1;
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v___x_300_);
lean_ctor_set(v___x_258_, 0, v_pos_261_);
v___x_302_ = v___x_258_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_pos_261_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v___x_300_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
else
{
lean_object* v___x_304_; 
lean_del_object(v___x_258_);
lean_inc(v_pos_261_);
v___x_304_ = l_Lean_Json_Parser_finishSurrogatePair(v___x_288_, v_pos_261_);
if (lean_obj_tag(v___x_304_) == 0)
{
if (lean_obj_tag(v___x_304_) == 0)
{
lean_del_object(v___x_264_);
lean_dec(v_pos_261_);
return v___x_304_;
}
else
{
lean_object* v_pos_305_; 
v_pos_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_pos_305_);
v___y_267_ = v___x_304_;
v_pos_268_ = v_pos_305_;
goto v___jp_266_;
}
}
else
{
lean_object* v_err_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
v_err_306_ = lean_ctor_get(v___x_304_, 1);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; 
v_unused_314_ = lean_ctor_get(v___x_304_, 0);
lean_dec(v_unused_314_);
v___x_308_ = v___x_304_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_err_306_);
lean_dec(v___x_304_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
lean_inc(v_pos_261_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v_pos_261_);
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_pos_261_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_err_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_inc(v_pos_261_);
v___y_267_ = v___x_311_;
v_pos_268_ = v_pos_261_;
goto v___jp_266_;
}
}
}
}
}
}
else
{
uint32_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
lean_del_object(v___x_264_);
v___x_315_ = lean_uint16_to_uint32(v___x_288_);
v___x_316_ = lean_box_uint32(v___x_315_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v___x_316_);
lean_ctor_set(v___x_258_, 0, v_pos_261_);
v___x_318_ = v___x_258_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_pos_261_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
v___jp_266_:
{
lean_object* v_snd_269_; lean_object* v_snd_270_; uint8_t v_decide_271_; 
v_snd_269_ = lean_ctor_get(v_pos_261_, 1);
lean_inc(v_snd_269_);
lean_dec(v_pos_261_);
v_snd_270_ = lean_ctor_get(v_pos_268_, 1);
v_decide_271_ = lean_nat_dec_eq(v_snd_269_, v_snd_270_);
lean_dec(v_snd_269_);
if (v_decide_271_ == 0)
{
lean_dec_ref(v_pos_268_);
lean_del_object(v___x_264_);
return v___y_267_;
}
else
{
lean_object* v___x_272_; lean_object* v___x_274_; 
lean_dec_ref(v___y_267_);
v___x_272_ = l_Lean_Json_Parser_escapedChar___boxed__const__1;
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 1, v___x_272_);
lean_ctor_set(v___x_264_, 0, v_pos_268_);
v___x_274_ = v___x_264_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_pos_268_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
else
{
lean_object* v_pos_321_; lean_object* v_err_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_del_object(v___x_258_);
lean_dec(v_res_256_);
lean_dec(v_res_253_);
lean_dec(v_res_250_);
v_pos_321_ = lean_ctor_get(v___x_260_, 0);
v_err_322_ = lean_ctor_get(v___x_260_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_260_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_err_322_);
lean_inc(v_pos_321_);
lean_dec(v___x_260_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_pos_321_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_err_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
else
{
lean_object* v_pos_331_; lean_object* v_err_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec(v_res_253_);
lean_dec(v_res_250_);
v_pos_331_ = lean_ctor_get(v___x_254_, 0);
v_err_332_ = lean_ctor_get(v___x_254_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_254_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_err_332_);
lean_inc(v_pos_331_);
lean_dec(v___x_254_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_pos_331_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_err_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
else
{
lean_object* v_pos_340_; lean_object* v_err_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec(v_res_250_);
v_pos_340_ = lean_ctor_get(v___x_251_, 0);
v_err_341_ = lean_ctor_get(v___x_251_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_251_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_err_341_);
lean_inc(v_pos_340_);
lean_dec(v___x_251_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_pos_340_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_err_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
else
{
lean_object* v_pos_349_; lean_object* v_err_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
v_pos_349_ = lean_ctor_get(v___x_248_, 0);
v_err_350_ = lean_ctor_get(v___x_248_, 1);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_248_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_err_350_);
lean_inc(v_pos_349_);
lean_dec(v___x_248_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_pos_349_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_err_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = l_Lean_Json_Parser_escapedChar___boxed__const__2;
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_it_x27_227_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
return v___x_359_;
}
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = l_Lean_Json_Parser_escapedChar___boxed__const__3;
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_it_x27_227_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
return v___x_361_;
}
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = l_Lean_Json_Parser_escapedChar___boxed__const__4;
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_it_x27_227_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
return v___x_363_;
}
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = l_Lean_Json_Parser_escapedChar___boxed__const__5;
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_it_x27_227_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
return v___x_365_;
}
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = l_Lean_Json_Parser_escapedChar___boxed__const__6;
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v_it_x27_227_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
return v___x_367_;
}
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = l_Lean_Json_Parser_escapedChar___boxed__const__7;
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v_it_x27_227_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
return v___x_369_;
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = l_Lean_Json_Parser_escapedChar___boxed__const__8;
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v_it_x27_227_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
return v___x_371_;
}
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = l_Lean_Json_Parser_escapedChar___boxed__const__9;
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v_it_x27_227_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
return v___x_373_;
}
}
}
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_box(0);
v___x_379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_379_, 0, v_a_216_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
return v___x_379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_strCore(lean_object* v_acc_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_fst_385_; lean_object* v_snd_386_; lean_object* v___x_387_; uint8_t v_decide_388_; 
v_fst_385_ = lean_ctor_get(v_a_384_, 0);
v_snd_386_ = lean_ctor_get(v_a_384_, 1);
v___x_387_ = lean_string_utf8_byte_size(v_fst_385_);
v_decide_388_ = lean_nat_dec_eq(v_snd_386_, v___x_387_);
if (v_decide_388_ == 0)
{
lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_430_; 
lean_inc(v_snd_386_);
lean_inc(v_fst_385_);
v_isSharedCheck_430_ = !lean_is_exclusive(v_a_384_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; lean_object* v_unused_432_; 
v_unused_431_ = lean_ctor_get(v_a_384_, 1);
lean_dec(v_unused_431_);
v_unused_432_ = lean_ctor_get(v_a_384_, 0);
lean_dec(v_unused_432_);
v___x_390_ = v_a_384_;
v_isShared_391_ = v_isSharedCheck_430_;
goto v_resetjp_389_;
}
else
{
lean_dec(v_a_384_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_430_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
uint32_t v___x_392_; uint32_t v___x_393_; uint8_t v___x_394_; 
v___x_392_ = lean_string_utf8_get_fast(v_fst_385_, v_snd_386_);
v___x_393_ = 34;
v___x_394_ = lean_uint32_dec_eq(v___x_392_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_395_ = lean_string_utf8_next_fast(v_fst_385_, v_snd_386_);
lean_dec(v_snd_386_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 1, v___x_395_);
v___x_397_ = v___x_390_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_fst_385_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_395_);
v___x_397_ = v_reuseFailAlloc_424_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
uint32_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = 92;
v___x_402_ = lean_uint32_dec_eq(v___x_392_, v___x_401_);
if (v___x_402_ == 0)
{
uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 32;
v___x_404_ = lean_uint32_dec_le(v___x_403_, v___x_392_);
if (v___x_404_ == 0)
{
lean_dec_ref(v_acc_383_);
goto v___jp_398_;
}
else
{
uint32_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 1114111;
v___x_406_ = lean_uint32_dec_le(v___x_392_, v___x_405_);
if (v___x_406_ == 0)
{
lean_dec_ref(v_acc_383_);
goto v___jp_398_;
}
else
{
lean_object* v___x_407_; 
v___x_407_ = lean_string_push(v_acc_383_, v___x_392_);
v_acc_383_ = v___x_407_;
v_a_384_ = v___x_397_;
goto _start;
}
}
}
else
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Json_Parser_escapedChar(v___x_397_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_pos_410_; lean_object* v_res_411_; uint32_t v___x_412_; lean_object* v___x_413_; 
v_pos_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_pos_410_);
v_res_411_ = lean_ctor_get(v___x_409_, 1);
lean_inc(v_res_411_);
lean_dec_ref_known(v___x_409_, 2);
v___x_412_ = lean_unbox_uint32(v_res_411_);
lean_dec(v_res_411_);
v___x_413_ = lean_string_push(v_acc_383_, v___x_412_);
v_acc_383_ = v___x_413_;
v_a_384_ = v_pos_410_;
goto _start;
}
else
{
lean_object* v_pos_415_; lean_object* v_err_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_dec_ref(v_acc_383_);
v_pos_415_ = lean_ctor_get(v___x_409_, 0);
v_err_416_ = lean_ctor_get(v___x_409_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_409_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_err_416_);
lean_inc(v_pos_415_);
lean_dec(v___x_409_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_pos_415_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_err_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
v___jp_398_:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_Json_Parser_strCore___closed__1));
v___x_400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_397_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
return v___x_400_;
}
}
}
else
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = lean_string_utf8_next_fast(v_fst_385_, v_snd_386_);
lean_dec(v_snd_386_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 1, v___x_425_);
v___x_427_ = v___x_390_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_fst_385_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v___x_425_);
v___x_427_ = v_reuseFailAlloc_429_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_428_; 
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v_acc_383_);
return v___x_428_;
}
}
}
}
else
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec_ref(v_acc_383_);
v___x_433_ = lean_box(0);
v___x_434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_434_, 0, v_a_384_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_str(lean_object* v_a_435_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_437_ = l_Lean_Json_Parser_strCore(v___x_436_, v_a_435_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCore(lean_object* v_acc_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_fst_440_; lean_object* v_snd_441_; lean_object* v___x_442_; uint8_t v_decide_443_; 
v_fst_440_ = lean_ctor_get(v_a_439_, 0);
v_snd_441_ = lean_ctor_get(v_a_439_, 1);
v___x_442_ = lean_string_utf8_byte_size(v_fst_440_);
v_decide_443_ = lean_nat_dec_eq(v_snd_441_, v___x_442_);
if (v_decide_443_ == 0)
{
uint32_t v___x_444_; uint32_t v___x_445_; uint8_t v___x_446_; 
v___x_444_ = lean_string_utf8_get_fast(v_fst_440_, v_snd_441_);
v___x_445_ = 48;
v___x_446_ = lean_uint32_dec_le(v___x_445_, v___x_444_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v_a_439_);
lean_ctor_set(v___x_447_, 1, v_acc_438_);
return v___x_447_;
}
else
{
uint32_t v___x_448_; uint8_t v___x_449_; 
v___x_448_ = 57;
v___x_449_ = lean_uint32_dec_le(v___x_444_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_450_, 0, v_a_439_);
lean_ctor_set(v___x_450_, 1, v_acc_438_);
return v___x_450_;
}
else
{
lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_464_; 
lean_inc(v_snd_441_);
lean_inc(v_fst_440_);
v_isSharedCheck_464_ = !lean_is_exclusive(v_a_439_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; lean_object* v_unused_466_; 
v_unused_465_ = lean_ctor_get(v_a_439_, 1);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_a_439_, 0);
lean_dec(v_unused_466_);
v___x_452_ = v_a_439_;
v_isShared_453_ = v_isSharedCheck_464_;
goto v_resetjp_451_;
}
else
{
lean_dec(v_a_439_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_464_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_454_ = lean_string_utf8_next_fast(v_fst_440_, v_snd_441_);
lean_dec(v_snd_441_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v___x_454_);
v___x_456_ = v___x_452_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_fst_440_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_454_);
v___x_456_ = v_reuseFailAlloc_463_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; lean_object* v___x_458_; uint32_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_457_ = lean_unsigned_to_nat(10u);
v___x_458_ = lean_nat_mul(v___x_457_, v_acc_438_);
lean_dec(v_acc_438_);
v___x_459_ = lean_uint32_sub(v___x_444_, v___x_445_);
v___x_460_ = lean_uint32_to_nat(v___x_459_);
v___x_461_ = lean_nat_add(v___x_458_, v___x_460_);
lean_dec(v___x_460_);
lean_dec(v___x_458_);
v_acc_438_ = v___x_461_;
v_a_439_ = v___x_456_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_467_; 
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v_a_439_);
lean_ctor_set(v___x_467_, 1, v_acc_438_);
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCoreNumDigits(lean_object* v_acc_468_, lean_object* v_digits_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_fst_474_; lean_object* v_snd_475_; lean_object* v___x_476_; uint8_t v_decide_477_; 
v_fst_474_ = lean_ctor_get(v_a_470_, 0);
v_snd_475_ = lean_ctor_get(v_a_470_, 1);
v___x_476_ = lean_string_utf8_byte_size(v_fst_474_);
v_decide_477_ = lean_nat_dec_eq(v_snd_475_, v___x_476_);
if (v_decide_477_ == 0)
{
uint32_t v___x_478_; uint32_t v___x_479_; uint8_t v___x_480_; 
v___x_478_ = lean_string_utf8_get_fast(v_fst_474_, v_snd_475_);
v___x_479_ = 48;
v___x_480_ = lean_uint32_dec_le(v___x_479_, v___x_478_);
if (v___x_480_ == 0)
{
goto v___jp_471_;
}
else
{
uint32_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = 57;
v___x_482_ = lean_uint32_dec_le(v___x_478_, v___x_481_);
if (v___x_482_ == 0)
{
goto v___jp_471_;
}
else
{
lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_498_; 
lean_inc(v_snd_475_);
lean_inc(v_fst_474_);
v_isSharedCheck_498_ = !lean_is_exclusive(v_a_470_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; lean_object* v_unused_500_; 
v_unused_499_ = lean_ctor_get(v_a_470_, 1);
lean_dec(v_unused_499_);
v_unused_500_ = lean_ctor_get(v_a_470_, 0);
lean_dec(v_unused_500_);
v___x_484_ = v_a_470_;
v_isShared_485_ = v_isSharedCheck_498_;
goto v_resetjp_483_;
}
else
{
lean_dec(v_a_470_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_498_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = lean_string_utf8_next_fast(v_fst_474_, v_snd_475_);
lean_dec(v_snd_475_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 1, v___x_486_);
v___x_488_ = v___x_484_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_fst_474_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v___x_486_);
v___x_488_ = v_reuseFailAlloc_497_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; lean_object* v___x_490_; uint32_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_489_ = lean_unsigned_to_nat(10u);
v___x_490_ = lean_nat_mul(v___x_489_, v_acc_468_);
lean_dec(v_acc_468_);
v___x_491_ = lean_uint32_sub(v___x_478_, v___x_479_);
v___x_492_ = lean_uint32_to_nat(v___x_491_);
v___x_493_ = lean_nat_add(v___x_490_, v___x_492_);
lean_dec(v___x_492_);
lean_dec(v___x_490_);
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_nat_add(v_digits_469_, v___x_494_);
lean_dec(v_digits_469_);
v_acc_468_ = v___x_493_;
v_digits_469_ = v___x_495_;
v_a_470_ = v___x_488_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v_acc_468_);
lean_ctor_set(v___x_501_, 1, v_digits_469_);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v_a_470_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
return v___x_502_;
}
v___jp_471_:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v_acc_468_);
lean_ctor_set(v___x_472_, 1, v_digits_469_);
v___x_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_473_, 0, v_a_470_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg(lean_object* v_desc_504_, lean_object* v_inst_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_fst_507_; lean_object* v_snd_508_; lean_object* v___x_509_; uint8_t v_decide_510_; 
v_fst_507_ = lean_ctor_get(v_a_506_, 0);
v_snd_508_ = lean_ctor_get(v_a_506_, 1);
v___x_509_ = lean_string_utf8_byte_size(v_fst_507_);
v_decide_510_ = lean_nat_dec_eq(v_snd_508_, v___x_509_);
if (v_decide_510_ == 0)
{
uint32_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_511_ = lean_string_utf8_get_fast(v_fst_507_, v_snd_508_);
v___x_512_ = lean_box_uint32(v___x_511_);
v___x_513_ = lean_apply_1(v_inst_505_, v___x_512_);
v___x_514_ = lean_unbox(v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_515_ = ((lean_object*)(l_Lean_Json_Parser_lookahead___redArg___closed__0));
v___x_516_ = lean_string_append(v___x_515_, v_desc_504_);
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
v___x_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_518_, 0, v_a_506_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_box(0);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v_a_506_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
return v___x_520_;
}
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec_ref(v_inst_505_);
v___x_521_ = lean_box(0);
v___x_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_522_, 0, v_a_506_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg___boxed(lean_object* v_desc_523_, lean_object* v_inst_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_Json_Parser_lookahead___redArg(v_desc_523_, v_inst_524_, v_a_525_);
lean_dec_ref(v_desc_523_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead(lean_object* v_p_527_, lean_object* v_desc_528_, lean_object* v_inst_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_fst_531_; lean_object* v_snd_532_; lean_object* v___x_533_; uint8_t v_decide_534_; 
v_fst_531_ = lean_ctor_get(v_a_530_, 0);
v_snd_532_ = lean_ctor_get(v_a_530_, 1);
v___x_533_ = lean_string_utf8_byte_size(v_fst_531_);
v_decide_534_ = lean_nat_dec_eq(v_snd_532_, v___x_533_);
if (v_decide_534_ == 0)
{
uint32_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_535_ = lean_string_utf8_get_fast(v_fst_531_, v_snd_532_);
v___x_536_ = lean_box_uint32(v___x_535_);
v___x_537_ = lean_apply_1(v_inst_529_, v___x_536_);
v___x_538_ = lean_unbox(v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_539_ = ((lean_object*)(l_Lean_Json_Parser_lookahead___redArg___closed__0));
v___x_540_ = lean_string_append(v___x_539_, v_desc_528_);
v___x_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
v___x_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_542_, 0, v_a_530_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
return v___x_542_;
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_box(0);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v_a_530_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
return v___x_544_;
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec_ref(v_inst_529_);
v___x_545_ = lean_box(0);
v___x_546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_546_, 0, v_a_530_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___boxed(lean_object* v_p_547_, lean_object* v_desc_548_, lean_object* v_inst_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Json_Parser_lookahead(v_p_547_, v_desc_548_, v_inst_549_, v_a_550_);
lean_dec_ref(v_desc_548_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNonZero(lean_object* v_a_555_){
_start:
{
uint8_t v___y_557_; lean_object* v_fst_562_; lean_object* v_snd_563_; lean_object* v___x_564_; uint8_t v_decide_565_; 
v_fst_562_ = lean_ctor_get(v_a_555_, 0);
v_snd_563_ = lean_ctor_get(v_a_555_, 1);
v___x_564_ = lean_string_utf8_byte_size(v_fst_562_);
v_decide_565_ = lean_nat_dec_eq(v_snd_563_, v___x_564_);
if (v_decide_565_ == 0)
{
uint32_t v___x_566_; uint32_t v___x_567_; uint8_t v___x_568_; 
v___x_566_ = lean_string_utf8_get_fast(v_fst_562_, v_snd_563_);
v___x_567_ = 49;
v___x_568_ = lean_uint32_dec_le(v___x_567_, v___x_566_);
if (v___x_568_ == 0)
{
v___y_557_ = v___x_568_;
goto v___jp_556_;
}
else
{
uint32_t v___x_569_; uint8_t v___x_570_; 
v___x_569_ = 57;
v___x_570_ = lean_uint32_dec_le(v___x_566_, v___x_569_);
v___y_557_ = v___x_570_;
goto v___jp_556_;
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_box(0);
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v_a_555_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
return v___x_572_;
}
v___jp_556_:
{
if (v___y_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_559_, 0, v_a_555_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = l_Lean_Json_Parser_natCore(v___x_560_, v_a_555_);
return v___x_561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNumDigits(lean_object* v_a_576_){
_start:
{
uint8_t v___y_578_; lean_object* v_fst_583_; lean_object* v_snd_584_; lean_object* v___x_585_; uint8_t v_decide_586_; 
v_fst_583_ = lean_ctor_get(v_a_576_, 0);
v_snd_584_ = lean_ctor_get(v_a_576_, 1);
v___x_585_ = lean_string_utf8_byte_size(v_fst_583_);
v_decide_586_ = lean_nat_dec_eq(v_snd_584_, v___x_585_);
if (v_decide_586_ == 0)
{
uint32_t v___x_587_; uint32_t v___x_588_; uint8_t v___x_589_; 
v___x_587_ = lean_string_utf8_get_fast(v_fst_583_, v_snd_584_);
v___x_588_ = 48;
v___x_589_ = lean_uint32_dec_le(v___x_588_, v___x_587_);
if (v___x_589_ == 0)
{
v___y_578_ = v___x_589_;
goto v___jp_577_;
}
else
{
uint32_t v___x_590_; uint8_t v___x_591_; 
v___x_590_ = 57;
v___x_591_ = lean_uint32_dec_le(v___x_587_, v___x_590_);
v___y_578_ = v___x_591_;
goto v___jp_577_;
}
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_box(0);
v___x_593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_593_, 0, v_a_576_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
return v___x_593_;
}
v___jp_577_:
{
if (v___y_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_580_, 0, v_a_576_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
return v___x_580_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_581_, v___x_581_, v_a_576_);
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natMaybeZero(lean_object* v_a_597_){
_start:
{
uint8_t v___y_599_; lean_object* v_fst_604_; lean_object* v_snd_605_; lean_object* v___x_606_; uint8_t v_decide_607_; 
v_fst_604_ = lean_ctor_get(v_a_597_, 0);
v_snd_605_ = lean_ctor_get(v_a_597_, 1);
v___x_606_ = lean_string_utf8_byte_size(v_fst_604_);
v_decide_607_ = lean_nat_dec_eq(v_snd_605_, v___x_606_);
if (v_decide_607_ == 0)
{
uint32_t v___x_608_; uint32_t v___x_609_; uint8_t v___x_610_; 
v___x_608_ = lean_string_utf8_get_fast(v_fst_604_, v_snd_605_);
v___x_609_ = 48;
v___x_610_ = lean_uint32_dec_le(v___x_609_, v___x_608_);
if (v___x_610_ == 0)
{
v___y_599_ = v___x_610_;
goto v___jp_598_;
}
else
{
uint32_t v___x_611_; uint8_t v___x_612_; 
v___x_611_ = 57;
v___x_612_ = lean_uint32_dec_le(v___x_608_, v___x_611_);
v___y_599_ = v___x_612_;
goto v___jp_598_;
}
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_box(0);
v___x_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_614_, 0, v_a_597_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
return v___x_614_;
}
v___jp_598_:
{
if (v___y_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_601_, 0, v_a_597_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
return v___x_601_;
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_unsigned_to_nat(0u);
v___x_603_ = l_Lean_Json_Parser_natCore(v___x_602_, v_a_597_);
return v___x_603_;
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_numSign___closed__0(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_nat_to_int(v___x_615_);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_Json_Parser_numSign___closed__1(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v___x_618_ = lean_int_neg(v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numSign(lean_object* v_a_619_){
_start:
{
lean_object* v_fst_620_; lean_object* v_snd_621_; lean_object* v___x_622_; uint8_t v_decide_623_; 
v_fst_620_ = lean_ctor_get(v_a_619_, 0);
v_snd_621_ = lean_ctor_get(v_a_619_, 1);
v___x_622_ = lean_string_utf8_byte_size(v_fst_620_);
v_decide_623_ = lean_nat_dec_eq(v_snd_621_, v___x_622_);
if (v_decide_623_ == 0)
{
uint32_t v___x_624_; uint32_t v___x_625_; uint8_t v___x_626_; 
v___x_624_ = lean_string_utf8_get_fast(v_fst_620_, v_snd_621_);
v___x_625_ = 45;
v___x_626_ = lean_uint32_dec_eq(v___x_624_, v___x_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v_a_619_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
return v___x_628_;
}
else
{
lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_638_; 
lean_inc(v_snd_621_);
lean_inc(v_fst_620_);
v_isSharedCheck_638_ = !lean_is_exclusive(v_a_619_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; lean_object* v_unused_640_; 
v_unused_639_ = lean_ctor_get(v_a_619_, 1);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_a_619_, 0);
lean_dec(v_unused_640_);
v___x_630_ = v_a_619_;
v_isShared_631_ = v_isSharedCheck_638_;
goto v_resetjp_629_;
}
else
{
lean_dec(v_a_619_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_638_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_632_ = lean_string_utf8_next_fast(v_fst_620_, v_snd_621_);
lean_dec(v_snd_621_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_632_);
v___x_634_ = v___x_630_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_fst_620_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v___x_632_);
v___x_634_ = v_reuseFailAlloc_637_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
return v___x_636_;
}
}
}
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_box(0);
v___x_642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_642_, 0, v_a_619_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_nat(lean_object* v_a_643_){
_start:
{
uint8_t v___y_645_; lean_object* v_fst_650_; lean_object* v_snd_651_; lean_object* v___x_652_; uint8_t v_decide_653_; 
v_fst_650_ = lean_ctor_get(v_a_643_, 0);
v_snd_651_ = lean_ctor_get(v_a_643_, 1);
v___x_652_ = lean_string_utf8_byte_size(v_fst_650_);
v_decide_653_ = lean_nat_dec_eq(v_snd_651_, v___x_652_);
if (v_decide_653_ == 0)
{
uint32_t v___x_654_; uint32_t v___x_655_; uint8_t v___x_656_; 
v___x_654_ = lean_string_utf8_get_fast(v_fst_650_, v_snd_651_);
v___x_655_ = 48;
v___x_656_ = lean_uint32_dec_eq(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
uint32_t v___x_657_; uint8_t v___x_658_; 
v___x_657_ = 49;
v___x_658_ = lean_uint32_dec_le(v___x_657_, v___x_654_);
if (v___x_658_ == 0)
{
v___y_645_ = v___x_658_;
goto v___jp_644_;
}
else
{
uint32_t v___x_659_; uint8_t v___x_660_; 
v___x_659_ = 57;
v___x_660_ = lean_uint32_dec_le(v___x_654_, v___x_659_);
v___y_645_ = v___x_660_;
goto v___jp_644_;
}
}
else
{
lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_670_; 
lean_inc(v_snd_651_);
lean_inc(v_fst_650_);
v_isSharedCheck_670_ = !lean_is_exclusive(v_a_643_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; lean_object* v_unused_672_; 
v_unused_671_ = lean_ctor_get(v_a_643_, 1);
lean_dec(v_unused_671_);
v_unused_672_ = lean_ctor_get(v_a_643_, 0);
lean_dec(v_unused_672_);
v___x_662_ = v_a_643_;
v_isShared_663_ = v_isSharedCheck_670_;
goto v_resetjp_661_;
}
else
{
lean_dec(v_a_643_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_670_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_664_ = lean_string_utf8_next_fast(v_fst_650_, v_snd_651_);
lean_dec(v_snd_651_);
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
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_fst_650_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_664_);
v___x_666_ = v_reuseFailAlloc_669_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(0u);
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
lean_ctor_set(v___x_674_, 0, v_a_643_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
return v___x_674_;
}
v___jp_644_:
{
if (v___y_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_647_, 0, v_a_643_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
return v___x_647_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = l_Lean_Json_Parser_natCore(v___x_648_, v_a_643_);
return v___x_649_;
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_numWithDecimals___closed__0(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = l_System_Platform_numBits;
v___x_676_ = lean_unsigned_to_nat(2u);
v___x_677_ = lean_nat_pow(v___x_676_, v___x_675_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numWithDecimals(lean_object* v_a_681_){
_start:
{
lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; uint8_t v___y_686_; lean_object* v___y_733_; lean_object* v___y_737_; lean_object* v_pos_738_; lean_object* v_fst_739_; lean_object* v_snd_740_; lean_object* v_res_741_; lean_object* v___y_764_; lean_object* v___y_765_; uint8_t v___y_766_; lean_object* v_pos_785_; lean_object* v_fst_786_; lean_object* v_snd_787_; lean_object* v_res_788_; lean_object* v_fst_803_; lean_object* v_snd_804_; lean_object* v___x_805_; uint8_t v_decide_806_; 
v_fst_803_ = lean_ctor_get(v_a_681_, 0);
v_snd_804_ = lean_ctor_get(v_a_681_, 1);
v___x_805_ = lean_string_utf8_byte_size(v_fst_803_);
v_decide_806_ = lean_nat_dec_eq(v_snd_804_, v___x_805_);
if (v_decide_806_ == 0)
{
uint32_t v___x_807_; uint32_t v___x_808_; uint8_t v___x_809_; 
lean_inc(v_snd_804_);
lean_inc(v_fst_803_);
v___x_807_ = lean_string_utf8_get_fast(v_fst_803_, v_snd_804_);
v___x_808_ = 45;
v___x_809_ = lean_uint32_dec_eq(v___x_807_, v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; 
v___x_810_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v_pos_785_ = v_a_681_;
v_fst_786_ = v_fst_803_;
v_snd_787_ = v_snd_804_;
v_res_788_ = v___x_810_;
goto v___jp_784_;
}
else
{
lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_819_; 
v_isSharedCheck_819_ = !lean_is_exclusive(v_a_681_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; lean_object* v_unused_821_; 
v_unused_820_ = lean_ctor_get(v_a_681_, 1);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v_a_681_, 0);
lean_dec(v_unused_821_);
v___x_812_ = v_a_681_;
v_isShared_813_ = v_isSharedCheck_819_;
goto v_resetjp_811_;
}
else
{
lean_dec(v_a_681_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_819_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = lean_string_utf8_next_fast(v_fst_803_, v_snd_804_);
lean_dec(v_snd_804_);
lean_inc(v_fst_803_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 1, v___x_814_);
v___x_816_ = v___x_812_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_fst_803_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_814_);
v___x_816_ = v_reuseFailAlloc_818_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; 
v___x_817_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v_pos_785_ = v___x_816_;
v_fst_786_ = v_fst_803_;
v_snd_787_ = v___x_814_;
v_res_788_ = v___x_817_;
goto v___jp_784_;
}
}
}
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_box(0);
v___x_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_823_, 0, v_a_681_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
return v___x_823_;
}
v___jp_682_:
{
if (v___y_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec(v___y_685_);
v___x_687_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_688_, 0, v___y_684_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
return v___x_688_;
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_689_, v___x_689_, v___y_684_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_res_691_; lean_object* v_pos_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_722_; 
v_res_691_ = lean_ctor_get(v___x_690_, 1);
v_pos_692_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_722_ == 0)
{
v___x_694_ = v___x_690_;
v_isShared_695_ = v_isSharedCheck_722_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_res_691_);
lean_inc(v_pos_692_);
lean_dec(v___x_690_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_722_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_fst_696_; lean_object* v_snd_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_721_; 
v_fst_696_ = lean_ctor_get(v_res_691_, 0);
v_snd_697_ = lean_ctor_get(v_res_691_, 1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_res_691_);
if (v_isSharedCheck_721_ == 0)
{
v___x_699_ = v_res_691_;
v_isShared_700_ = v_isSharedCheck_721_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_snd_697_);
lean_inc(v_fst_696_);
lean_dec(v_res_691_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_721_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_701_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_702_ = lean_nat_dec_lt(v___x_701_, v_snd_697_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_703_ = lean_nat_to_int(v___y_685_);
v___x_704_ = lean_unsigned_to_nat(10u);
v___x_705_ = lean_nat_pow(v___x_704_, v_snd_697_);
v___x_706_ = lean_nat_to_int(v___x_705_);
v___x_707_ = lean_int_mul(v___x_703_, v___x_706_);
lean_dec(v___x_706_);
lean_dec(v___x_703_);
v___x_708_ = lean_nat_to_int(v_fst_696_);
v___x_709_ = lean_int_add(v___x_707_, v___x_708_);
lean_dec(v___x_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_int_mul(v___y_683_, v___x_709_);
lean_dec(v___x_709_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_710_);
v___x_712_ = v___x_699_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_snd_697_);
v___x_712_ = v_reuseFailAlloc_716_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v___x_712_);
v___x_714_ = v___x_694_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_pos_692_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
else
{
lean_object* v___x_717_; lean_object* v___x_719_; 
lean_del_object(v___x_699_);
lean_dec(v_snd_697_);
lean_dec(v_fst_696_);
lean_dec(v___y_685_);
v___x_717_ = ((lean_object*)(l_Lean_Json_Parser_numWithDecimals___closed__2));
if (v_isShared_695_ == 0)
{
lean_ctor_set_tag(v___x_694_, 1);
lean_ctor_set(v___x_694_, 1, v___x_717_);
v___x_719_ = v___x_694_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_pos_692_);
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
}
}
else
{
lean_object* v_pos_723_; lean_object* v_err_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v___y_685_);
v_pos_723_ = lean_ctor_get(v___x_690_, 0);
v_err_724_ = lean_ctor_get(v___x_690_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_690_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_err_724_);
lean_inc(v_pos_723_);
lean_dec(v___x_690_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_pos_723_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_err_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
v___jp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_box(0);
v___x_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_735_, 0, v___y_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
return v___x_735_;
}
v___jp_736_:
{
lean_object* v___x_742_; uint8_t v_decide_743_; 
v___x_742_ = lean_string_utf8_byte_size(v_fst_739_);
v_decide_743_ = lean_nat_dec_eq(v_snd_740_, v___x_742_);
if (v_decide_743_ == 0)
{
uint32_t v___x_744_; uint32_t v___x_745_; uint8_t v___x_746_; 
v___x_744_ = lean_string_utf8_get_fast(v_fst_739_, v_snd_740_);
v___x_745_ = 46;
v___x_746_ = lean_uint32_dec_eq(v___x_744_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
lean_dec(v_snd_740_);
lean_dec(v_fst_739_);
v___x_747_ = lean_nat_to_int(v_res_741_);
v___x_748_ = lean_int_mul(v___y_737_, v___x_747_);
lean_dec(v___x_747_);
v___x_749_ = l_Lean_JsonNumber_fromInt(v___x_748_);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v_pos_738_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
return v___x_750_;
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v_decide_753_; 
lean_dec_ref(v_pos_738_);
v___x_751_ = lean_string_utf8_next_fast(v_fst_739_, v_snd_740_);
lean_dec(v_snd_740_);
lean_inc(v_fst_739_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_fst_739_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v_decide_753_ = lean_nat_dec_eq(v___x_751_, v___x_742_);
if (v_decide_753_ == 0)
{
if (v___x_746_ == 0)
{
lean_dec(v_res_741_);
lean_dec(v_fst_739_);
v___y_733_ = v___x_752_;
goto v___jp_732_;
}
else
{
uint32_t v___x_754_; uint32_t v___x_755_; uint8_t v___x_756_; 
v___x_754_ = lean_string_utf8_get_fast(v_fst_739_, v___x_751_);
lean_dec(v_fst_739_);
v___x_755_ = 48;
v___x_756_ = lean_uint32_dec_le(v___x_755_, v___x_754_);
if (v___x_756_ == 0)
{
v___y_683_ = v___y_737_;
v___y_684_ = v___x_752_;
v___y_685_ = v_res_741_;
v___y_686_ = v___x_756_;
goto v___jp_682_;
}
else
{
uint32_t v___x_757_; uint8_t v___x_758_; 
v___x_757_ = 57;
v___x_758_ = lean_uint32_dec_le(v___x_754_, v___x_757_);
v___y_683_ = v___y_737_;
v___y_684_ = v___x_752_;
v___y_685_ = v_res_741_;
v___y_686_ = v___x_758_;
goto v___jp_682_;
}
}
}
else
{
lean_dec(v_res_741_);
lean_dec(v_fst_739_);
v___y_733_ = v___x_752_;
goto v___jp_732_;
}
}
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
lean_dec(v_snd_740_);
lean_dec(v_fst_739_);
v___x_759_ = lean_nat_to_int(v_res_741_);
v___x_760_ = lean_int_mul(v___y_737_, v___x_759_);
lean_dec(v___x_759_);
v___x_761_ = l_Lean_JsonNumber_fromInt(v___x_760_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v_pos_738_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
return v___x_762_;
}
}
v___jp_763_:
{
if (v___y_766_ == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_768_, 0, v___y_765_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
return v___x_768_;
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = l_Lean_Json_Parser_natCore(v___x_769_, v___y_765_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_pos_771_; lean_object* v_res_772_; lean_object* v_fst_773_; lean_object* v_snd_774_; 
v_pos_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_pos_771_);
v_res_772_ = lean_ctor_get(v___x_770_, 1);
lean_inc(v_res_772_);
lean_dec_ref_known(v___x_770_, 2);
v_fst_773_ = lean_ctor_get(v_pos_771_, 0);
lean_inc(v_fst_773_);
v_snd_774_ = lean_ctor_get(v_pos_771_, 1);
lean_inc(v_snd_774_);
v___y_737_ = v___y_764_;
v_pos_738_ = v_pos_771_;
v_fst_739_ = v_fst_773_;
v_snd_740_ = v_snd_774_;
v_res_741_ = v_res_772_;
goto v___jp_736_;
}
else
{
lean_object* v_pos_775_; lean_object* v_err_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
v_pos_775_ = lean_ctor_get(v___x_770_, 0);
v_err_776_ = lean_ctor_get(v___x_770_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_770_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_err_776_);
lean_inc(v_pos_775_);
lean_dec(v___x_770_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_pos_775_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_err_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
v___jp_784_:
{
lean_object* v___x_789_; uint8_t v_decide_790_; 
v___x_789_ = lean_string_utf8_byte_size(v_fst_786_);
v_decide_790_ = lean_nat_dec_eq(v_snd_787_, v___x_789_);
if (v_decide_790_ == 0)
{
uint32_t v___x_791_; uint32_t v___x_792_; uint8_t v___x_793_; 
v___x_791_ = lean_string_utf8_get_fast(v_fst_786_, v_snd_787_);
v___x_792_ = 48;
v___x_793_ = lean_uint32_dec_eq(v___x_791_, v___x_792_);
if (v___x_793_ == 0)
{
uint32_t v___x_794_; uint8_t v___x_795_; 
lean_dec(v_snd_787_);
lean_dec(v_fst_786_);
v___x_794_ = 49;
v___x_795_ = lean_uint32_dec_le(v___x_794_, v___x_791_);
if (v___x_795_ == 0)
{
v___y_764_ = v_res_788_;
v___y_765_ = v_pos_785_;
v___y_766_ = v___x_795_;
goto v___jp_763_;
}
else
{
uint32_t v___x_796_; uint8_t v___x_797_; 
v___x_796_ = 57;
v___x_797_ = lean_uint32_dec_le(v___x_791_, v___x_796_);
v___y_764_ = v_res_788_;
v___y_765_ = v_pos_785_;
v___y_766_ = v___x_797_;
goto v___jp_763_;
}
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec_ref(v_pos_785_);
v___x_798_ = lean_string_utf8_next_fast(v_fst_786_, v_snd_787_);
lean_dec(v_snd_787_);
lean_inc(v_fst_786_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v_fst_786_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = lean_unsigned_to_nat(0u);
v___y_737_ = v_res_788_;
v_pos_738_ = v___x_799_;
v_fst_739_ = v_fst_786_;
v_snd_740_ = v___x_798_;
v_res_741_ = v___x_800_;
goto v___jp_736_;
}
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec(v_snd_787_);
lean_dec(v_fst_786_);
v___x_801_ = lean_box(0);
v___x_802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_802_, 0, v_pos_785_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent(lean_object* v_value_827_, lean_object* v_a_828_){
_start:
{
lean_object* v___y_830_; lean_object* v___y_834_; uint8_t v___y_835_; lean_object* v___y_860_; uint8_t v___y_861_; lean_object* v___y_892_; lean_object* v_fst_893_; lean_object* v_snd_894_; lean_object* v_fst_904_; lean_object* v_snd_905_; lean_object* v___x_939_; uint8_t v_decide_940_; 
v_fst_904_ = lean_ctor_get(v_a_828_, 0);
v_snd_905_ = lean_ctor_get(v_a_828_, 1);
v___x_939_ = lean_string_utf8_byte_size(v_fst_904_);
v_decide_940_ = lean_nat_dec_eq(v_snd_905_, v___x_939_);
if (v_decide_940_ == 0)
{
uint32_t v___x_941_; uint32_t v___x_942_; uint8_t v___x_943_; 
v___x_941_ = lean_string_utf8_get_fast(v_fst_904_, v_snd_905_);
v___x_942_ = 101;
v___x_943_ = lean_uint32_dec_eq(v___x_941_, v___x_942_);
if (v___x_943_ == 0)
{
uint32_t v___x_944_; uint8_t v___x_945_; 
v___x_944_ = 69;
v___x_945_ = lean_uint32_dec_eq(v___x_941_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; 
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v_a_828_);
lean_ctor_set(v___x_946_, 1, v_value_827_);
return v___x_946_;
}
else
{
goto v___jp_906_;
}
}
else
{
goto v___jp_906_;
}
}
else
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v_a_828_);
lean_ctor_set(v___x_947_, 1, v_value_827_);
return v___x_947_;
}
v___jp_829_:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_box(0);
v___x_832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_832_, 0, v___y_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
return v___x_832_;
}
v___jp_833_:
{
if (v___y_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec_ref(v_value_827_);
v___x_836_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_837_, 0, v___y_834_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
return v___x_837_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = l_Lean_Json_Parser_natCore(v___x_838_, v___y_834_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_pos_840_; lean_object* v_res_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_849_; 
v_pos_840_ = lean_ctor_get(v___x_839_, 0);
v_res_841_ = lean_ctor_get(v___x_839_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_849_ == 0)
{
v___x_843_ = v___x_839_;
v_isShared_844_ = v_isSharedCheck_849_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_res_841_);
lean_inc(v_pos_840_);
lean_dec(v___x_839_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_849_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = l_Lean_JsonNumber_shiftr(v_value_827_, v_res_841_);
lean_dec(v_res_841_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 1, v___x_845_);
v___x_847_ = v___x_843_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_pos_840_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
lean_object* v_pos_850_; lean_object* v_err_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec_ref(v_value_827_);
v_pos_850_ = lean_ctor_get(v___x_839_, 0);
v_err_851_ = lean_ctor_get(v___x_839_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_839_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_err_851_);
lean_inc(v_pos_850_);
lean_dec(v___x_839_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_pos_850_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_err_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
v___jp_859_:
{
if (v___y_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec_ref(v_value_827_);
v___x_862_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_863_, 0, v___y_860_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
return v___x_863_;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_unsigned_to_nat(0u);
v___x_865_ = l_Lean_Json_Parser_natCore(v___x_864_, v___y_860_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_pos_866_; lean_object* v_res_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_881_; 
v_pos_866_ = lean_ctor_get(v___x_865_, 0);
v_res_867_ = lean_ctor_get(v___x_865_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_881_ == 0)
{
v___x_869_ = v___x_865_;
v_isShared_870_ = v_isSharedCheck_881_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_res_867_);
lean_inc(v_pos_866_);
lean_dec(v___x_865_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_881_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_871_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_872_ = lean_nat_dec_lt(v___x_871_, v_res_867_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = l_Lean_JsonNumber_shiftl(v_value_827_, v_res_867_);
lean_dec(v_res_867_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 1, v___x_873_);
v___x_875_ = v___x_869_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_pos_866_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
else
{
lean_object* v___x_877_; lean_object* v___x_879_; 
lean_dec(v_res_867_);
lean_dec_ref(v_value_827_);
v___x_877_ = ((lean_object*)(l_Lean_Json_Parser_exponent___closed__1));
if (v_isShared_870_ == 0)
{
lean_ctor_set_tag(v___x_869_, 1);
lean_ctor_set(v___x_869_, 1, v___x_877_);
v___x_879_ = v___x_869_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_pos_866_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_object* v_pos_882_; lean_object* v_err_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec_ref(v_value_827_);
v_pos_882_ = lean_ctor_get(v___x_865_, 0);
v_err_883_ = lean_ctor_get(v___x_865_, 1);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_865_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_err_883_);
lean_inc(v_pos_882_);
lean_dec(v___x_865_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_pos_882_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_err_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
v___jp_891_:
{
lean_object* v___x_895_; uint8_t v_decide_896_; 
v___x_895_ = lean_string_utf8_byte_size(v_fst_893_);
v_decide_896_ = lean_nat_dec_eq(v_snd_894_, v___x_895_);
if (v_decide_896_ == 0)
{
uint32_t v___x_897_; uint32_t v___x_898_; uint8_t v___x_899_; 
v___x_897_ = lean_string_utf8_get_fast(v_fst_893_, v_snd_894_);
lean_dec(v_snd_894_);
lean_dec(v_fst_893_);
v___x_898_ = 48;
v___x_899_ = lean_uint32_dec_le(v___x_898_, v___x_897_);
if (v___x_899_ == 0)
{
v___y_860_ = v___y_892_;
v___y_861_ = v___x_899_;
goto v___jp_859_;
}
else
{
uint32_t v___x_900_; uint8_t v___x_901_; 
v___x_900_ = 57;
v___x_901_ = lean_uint32_dec_le(v___x_897_, v___x_900_);
v___y_860_ = v___y_892_;
v___y_861_ = v___x_901_;
goto v___jp_859_;
}
}
else
{
lean_object* v___x_902_; lean_object* v___x_903_; 
lean_dec(v_snd_894_);
lean_dec(v_fst_893_);
lean_dec_ref(v_value_827_);
v___x_902_ = lean_box(0);
v___x_903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_903_, 0, v___y_892_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
return v___x_903_;
}
}
v___jp_906_:
{
lean_object* v___x_907_; uint8_t v_decide_908_; 
v___x_907_ = lean_string_utf8_byte_size(v_fst_904_);
v_decide_908_ = lean_nat_dec_eq(v_snd_905_, v___x_907_);
if (v_decide_908_ == 0)
{
lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_934_; 
lean_inc(v_snd_905_);
lean_inc(v_fst_904_);
v_isSharedCheck_934_ = !lean_is_exclusive(v_a_828_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; lean_object* v_unused_936_; 
v_unused_935_ = lean_ctor_get(v_a_828_, 1);
lean_dec(v_unused_935_);
v_unused_936_ = lean_ctor_get(v_a_828_, 0);
lean_dec(v_unused_936_);
v___x_910_ = v_a_828_;
v_isShared_911_ = v_isSharedCheck_934_;
goto v_resetjp_909_;
}
else
{
lean_dec(v_a_828_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_934_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_912_ = lean_string_utf8_next_fast(v_fst_904_, v_snd_905_);
lean_dec(v_snd_905_);
lean_inc(v_fst_904_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 1, v___x_912_);
v___x_914_ = v___x_910_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_fst_904_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v___x_912_);
v___x_914_ = v_reuseFailAlloc_933_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
uint8_t v_decide_915_; 
v_decide_915_ = lean_nat_dec_eq(v___x_912_, v___x_907_);
if (v_decide_915_ == 0)
{
uint32_t v___x_916_; uint32_t v___x_917_; uint8_t v___x_918_; 
v___x_916_ = lean_string_utf8_get_fast(v_fst_904_, v___x_912_);
v___x_917_ = 45;
v___x_918_ = lean_uint32_dec_eq(v___x_916_, v___x_917_);
if (v___x_918_ == 0)
{
uint32_t v___x_919_; uint8_t v___x_920_; 
v___x_919_ = 43;
v___x_920_ = lean_uint32_dec_eq(v___x_916_, v___x_919_);
if (v___x_920_ == 0)
{
v___y_892_ = v___x_914_;
v_fst_893_ = v_fst_904_;
v_snd_894_ = v___x_912_;
goto v___jp_891_;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; 
lean_dec_ref(v___x_914_);
v___x_921_ = lean_string_utf8_next_fast(v_fst_904_, v___x_912_);
lean_inc(v_fst_904_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_fst_904_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___y_892_ = v___x_922_;
v_fst_893_ = v_fst_904_;
v_snd_894_ = v___x_921_;
goto v___jp_891_;
}
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v_decide_925_; 
lean_dec_ref(v___x_914_);
v___x_923_ = lean_string_utf8_next_fast(v_fst_904_, v___x_912_);
lean_inc(v_fst_904_);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v_fst_904_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v_decide_925_ = lean_nat_dec_eq(v___x_923_, v___x_907_);
if (v_decide_925_ == 0)
{
if (v___x_918_ == 0)
{
lean_dec(v_fst_904_);
lean_dec_ref(v_value_827_);
v___y_830_ = v___x_924_;
goto v___jp_829_;
}
else
{
uint32_t v___x_926_; uint32_t v___x_927_; uint8_t v___x_928_; 
v___x_926_ = lean_string_utf8_get_fast(v_fst_904_, v___x_923_);
lean_dec(v_fst_904_);
v___x_927_ = 48;
v___x_928_ = lean_uint32_dec_le(v___x_927_, v___x_926_);
if (v___x_928_ == 0)
{
v___y_834_ = v___x_924_;
v___y_835_ = v___x_928_;
goto v___jp_833_;
}
else
{
uint32_t v___x_929_; uint8_t v___x_930_; 
v___x_929_ = 57;
v___x_930_ = lean_uint32_dec_le(v___x_926_, v___x_929_);
v___y_834_ = v___x_924_;
v___y_835_ = v___x_930_;
goto v___jp_833_;
}
}
}
else
{
lean_dec(v_fst_904_);
lean_dec_ref(v_value_827_);
v___y_830_ = v___x_924_;
goto v___jp_829_;
}
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v_fst_904_);
lean_dec_ref(v_value_827_);
v___x_931_ = lean_box(0);
v___x_932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_914_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
return v___x_932_;
}
}
}
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec_ref(v_value_827_);
v___x_937_ = lean_box(0);
v___x_938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_938_, 0, v_a_828_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
return v___x_938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Json_Parser_num_spec__0(lean_object* v_a_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = lean_nat_to_int(v_a_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_num(lean_object* v_a_950_){
_start:
{
lean_object* v___y_952_; lean_object* v___y_953_; uint8_t v___y_954_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v_fst_987_; lean_object* v_snd_988_; lean_object* v___y_999_; lean_object* v___y_1000_; uint8_t v___y_1001_; lean_object* v___y_1026_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v_fst_1032_; lean_object* v_snd_1033_; lean_object* v___y_1059_; lean_object* v_pos_1060_; lean_object* v_fst_1061_; lean_object* v_snd_1062_; lean_object* v_res_1063_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; uint8_t v___y_1075_; lean_object* v___y_1124_; lean_object* v___y_1128_; lean_object* v_pos_1129_; lean_object* v_fst_1130_; lean_object* v_snd_1131_; lean_object* v_res_1132_; lean_object* v___y_1155_; lean_object* v___y_1156_; uint8_t v___y_1157_; lean_object* v_pos_1176_; lean_object* v_fst_1177_; lean_object* v_snd_1178_; lean_object* v_res_1179_; lean_object* v_fst_1194_; lean_object* v_snd_1195_; lean_object* v___x_1196_; uint8_t v_decide_1197_; 
v_fst_1194_ = lean_ctor_get(v_a_950_, 0);
v_snd_1195_ = lean_ctor_get(v_a_950_, 1);
v___x_1196_ = lean_string_utf8_byte_size(v_fst_1194_);
v_decide_1197_ = lean_nat_dec_eq(v_snd_1195_, v___x_1196_);
if (v_decide_1197_ == 0)
{
uint32_t v___x_1198_; uint32_t v___x_1199_; uint8_t v___x_1200_; 
lean_inc(v_snd_1195_);
lean_inc(v_fst_1194_);
v___x_1198_ = lean_string_utf8_get_fast(v_fst_1194_, v_snd_1195_);
v___x_1199_ = 45;
v___x_1200_ = lean_uint32_dec_eq(v___x_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__0, &l_Lean_Json_Parser_numSign___closed__0_once, _init_l_Lean_Json_Parser_numSign___closed__0);
v_pos_1176_ = v_a_950_;
v_fst_1177_ = v_fst_1194_;
v_snd_1178_ = v_snd_1195_;
v_res_1179_ = v___x_1201_;
goto v___jp_1175_;
}
else
{
lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1210_; 
v_isSharedCheck_1210_ = !lean_is_exclusive(v_a_950_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; lean_object* v_unused_1212_; 
v_unused_1211_ = lean_ctor_get(v_a_950_, 1);
lean_dec(v_unused_1211_);
v_unused_1212_ = lean_ctor_get(v_a_950_, 0);
lean_dec(v_unused_1212_);
v___x_1203_ = v_a_950_;
v_isShared_1204_ = v_isSharedCheck_1210_;
goto v_resetjp_1202_;
}
else
{
lean_dec(v_a_950_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1210_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1205_ = lean_string_utf8_next_fast(v_fst_1194_, v_snd_1195_);
lean_dec(v_snd_1195_);
lean_inc(v_fst_1194_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v___x_1205_);
v___x_1207_ = v___x_1203_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_fst_1194_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_obj_once(&l_Lean_Json_Parser_numSign___closed__1, &l_Lean_Json_Parser_numSign___closed__1_once, _init_l_Lean_Json_Parser_numSign___closed__1);
v_pos_1176_ = v___x_1207_;
v_fst_1177_ = v_fst_1194_;
v_snd_1178_ = v___x_1205_;
v_res_1179_ = v___x_1208_;
goto v___jp_1175_;
}
}
}
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_box(0);
v___x_1214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1214_, 0, v_a_950_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
return v___x_1214_;
}
v___jp_951_:
{
if (v___y_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec_ref(v___y_953_);
v___x_955_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_956_, 0, v___y_952_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_unsigned_to_nat(0u);
v___x_958_ = l_Lean_Json_Parser_natCore(v___x_957_, v___y_952_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_pos_959_; lean_object* v_res_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_974_; 
v_pos_959_ = lean_ctor_get(v___x_958_, 0);
v_res_960_ = lean_ctor_get(v___x_958_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_974_ == 0)
{
v___x_962_ = v___x_958_;
v_isShared_963_ = v_isSharedCheck_974_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_res_960_);
lean_inc(v_pos_959_);
lean_dec(v___x_958_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_974_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_964_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_965_ = lean_nat_dec_lt(v___x_964_, v_res_960_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = l_Lean_JsonNumber_shiftl(v___y_953_, v_res_960_);
lean_dec(v_res_960_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v___x_966_);
v___x_968_ = v___x_962_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_pos_959_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
else
{
lean_object* v___x_970_; lean_object* v___x_972_; 
lean_dec(v_res_960_);
lean_dec_ref(v___y_953_);
v___x_970_ = ((lean_object*)(l_Lean_Json_Parser_exponent___closed__1));
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 1);
lean_ctor_set(v___x_962_, 1, v___x_970_);
v___x_972_ = v___x_962_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_pos_959_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
else
{
lean_object* v_pos_975_; lean_object* v_err_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec_ref(v___y_953_);
v_pos_975_ = lean_ctor_get(v___x_958_, 0);
v_err_976_ = lean_ctor_get(v___x_958_, 1);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_958_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_err_976_);
lean_inc(v_pos_975_);
lean_dec(v___x_958_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_pos_975_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_err_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
v___jp_984_:
{
lean_object* v___x_989_; uint8_t v_decide_990_; 
v___x_989_ = lean_string_utf8_byte_size(v_fst_987_);
v_decide_990_ = lean_nat_dec_eq(v_snd_988_, v___x_989_);
if (v_decide_990_ == 0)
{
uint32_t v___x_991_; uint32_t v___x_992_; uint8_t v___x_993_; 
v___x_991_ = lean_string_utf8_get_fast(v_fst_987_, v_snd_988_);
lean_dec(v_snd_988_);
lean_dec(v_fst_987_);
v___x_992_ = 48;
v___x_993_ = lean_uint32_dec_le(v___x_992_, v___x_991_);
if (v___x_993_ == 0)
{
v___y_952_ = v___y_986_;
v___y_953_ = v___y_985_;
v___y_954_ = v___x_993_;
goto v___jp_951_;
}
else
{
uint32_t v___x_994_; uint8_t v___x_995_; 
v___x_994_ = 57;
v___x_995_ = lean_uint32_dec_le(v___x_991_, v___x_994_);
v___y_952_ = v___y_986_;
v___y_953_ = v___y_985_;
v___y_954_ = v___x_995_;
goto v___jp_951_;
}
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec(v_snd_988_);
lean_dec(v_fst_987_);
lean_dec_ref(v___y_985_);
v___x_996_ = lean_box(0);
v___x_997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_997_, 0, v___y_986_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
return v___x_997_;
}
}
v___jp_998_:
{
if (v___y_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec_ref(v___y_1000_);
v___x_1002_ = ((lean_object*)(l_Lean_Json_Parser_natMaybeZero___closed__1));
v___x_1003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___y_999_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
return v___x_1003_;
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = l_Lean_Json_Parser_natCore(v___x_1004_, v___y_999_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_pos_1006_; lean_object* v_res_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1015_; 
v_pos_1006_ = lean_ctor_get(v___x_1005_, 0);
v_res_1007_ = lean_ctor_get(v___x_1005_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1009_ = v___x_1005_;
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_res_1007_);
lean_inc(v_pos_1006_);
lean_dec(v___x_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1011_ = l_Lean_JsonNumber_shiftr(v___y_1000_, v_res_1007_);
lean_dec(v_res_1007_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v___x_1011_);
v___x_1013_ = v___x_1009_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_pos_1006_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
else
{
lean_object* v_pos_1016_; lean_object* v_err_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref(v___y_1000_);
v_pos_1016_ = lean_ctor_get(v___x_1005_, 0);
v_err_1017_ = lean_ctor_get(v___x_1005_, 1);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1005_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_err_1017_);
lean_inc(v_pos_1016_);
lean_dec(v___x_1005_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_pos_1016_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_err_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
v___jp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___y_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
return v___x_1028_;
}
v___jp_1029_:
{
lean_object* v___x_1034_; uint8_t v_decide_1035_; 
v___x_1034_ = lean_string_utf8_byte_size(v_fst_1032_);
v_decide_1035_ = lean_nat_dec_eq(v_snd_1033_, v___x_1034_);
if (v_decide_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v_decide_1038_; 
lean_dec_ref(v___y_1031_);
v___x_1036_ = lean_string_utf8_next_fast(v_fst_1032_, v_snd_1033_);
lean_dec(v_snd_1033_);
lean_inc(v_fst_1032_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v_fst_1032_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v_decide_1038_ = lean_nat_dec_eq(v___x_1036_, v___x_1034_);
if (v_decide_1038_ == 0)
{
uint32_t v___x_1039_; uint32_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1039_ = lean_string_utf8_get_fast(v_fst_1032_, v___x_1036_);
v___x_1040_ = 45;
v___x_1041_ = lean_uint32_dec_eq(v___x_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
uint32_t v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = 43;
v___x_1043_ = lean_uint32_dec_eq(v___x_1039_, v___x_1042_);
if (v___x_1043_ == 0)
{
v___y_985_ = v___y_1030_;
v___y_986_ = v___x_1037_;
v_fst_987_ = v_fst_1032_;
v_snd_988_ = v___x_1036_;
goto v___jp_984_;
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec_ref_known(v___x_1037_, 2);
v___x_1044_ = lean_string_utf8_next_fast(v_fst_1032_, v___x_1036_);
lean_inc(v_fst_1032_);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v_fst_1032_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___y_985_ = v___y_1030_;
v___y_986_ = v___x_1045_;
v_fst_987_ = v_fst_1032_;
v_snd_988_ = v___x_1044_;
goto v___jp_984_;
}
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v_decide_1048_; 
lean_dec_ref_known(v___x_1037_, 2);
v___x_1046_ = lean_string_utf8_next_fast(v_fst_1032_, v___x_1036_);
lean_inc(v_fst_1032_);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v_fst_1032_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v_decide_1048_ = lean_nat_dec_eq(v___x_1046_, v___x_1034_);
if (v_decide_1048_ == 0)
{
if (v___x_1041_ == 0)
{
lean_dec(v_fst_1032_);
lean_dec_ref(v___y_1030_);
v___y_1026_ = v___x_1047_;
goto v___jp_1025_;
}
else
{
uint32_t v___x_1049_; uint32_t v___x_1050_; uint8_t v___x_1051_; 
v___x_1049_ = lean_string_utf8_get_fast(v_fst_1032_, v___x_1046_);
lean_dec(v_fst_1032_);
v___x_1050_ = 48;
v___x_1051_ = lean_uint32_dec_le(v___x_1050_, v___x_1049_);
if (v___x_1051_ == 0)
{
v___y_999_ = v___x_1047_;
v___y_1000_ = v___y_1030_;
v___y_1001_ = v___x_1051_;
goto v___jp_998_;
}
else
{
uint32_t v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = 57;
v___x_1053_ = lean_uint32_dec_le(v___x_1049_, v___x_1052_);
v___y_999_ = v___x_1047_;
v___y_1000_ = v___y_1030_;
v___y_1001_ = v___x_1053_;
goto v___jp_998_;
}
}
}
else
{
lean_dec(v_fst_1032_);
lean_dec_ref(v___y_1030_);
v___y_1026_ = v___x_1047_;
goto v___jp_1025_;
}
}
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec(v_fst_1032_);
lean_dec_ref(v___y_1030_);
v___x_1054_ = lean_box(0);
v___x_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1037_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
return v___x_1055_;
}
}
else
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_dec(v_snd_1033_);
lean_dec(v_fst_1032_);
lean_dec_ref(v___y_1030_);
v___x_1056_ = lean_box(0);
v___x_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___y_1031_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
return v___x_1057_;
}
}
v___jp_1058_:
{
lean_object* v___x_1064_; uint8_t v_decide_1065_; 
v___x_1064_ = lean_string_utf8_byte_size(v_fst_1061_);
v_decide_1065_ = lean_nat_dec_eq(v_snd_1062_, v___x_1064_);
if (v_decide_1065_ == 0)
{
uint32_t v___x_1066_; uint32_t v___x_1067_; uint8_t v___x_1068_; 
v___x_1066_ = lean_string_utf8_get_fast(v_fst_1061_, v_snd_1062_);
v___x_1067_ = 101;
v___x_1068_ = lean_uint32_dec_eq(v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
uint32_t v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = 69;
v___x_1070_ = lean_uint32_dec_eq(v___x_1066_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_dec_ref(v_res_1063_);
lean_dec(v_snd_1062_);
lean_dec(v_fst_1061_);
lean_dec_ref(v_pos_1060_);
return v___y_1059_;
}
else
{
lean_dec_ref(v___y_1059_);
v___y_1030_ = v_res_1063_;
v___y_1031_ = v_pos_1060_;
v_fst_1032_ = v_fst_1061_;
v_snd_1033_ = v_snd_1062_;
goto v___jp_1029_;
}
}
else
{
lean_dec_ref(v___y_1059_);
v___y_1030_ = v_res_1063_;
v___y_1031_ = v_pos_1060_;
v_fst_1032_ = v_fst_1061_;
v_snd_1033_ = v_snd_1062_;
goto v___jp_1029_;
}
}
else
{
lean_dec_ref(v_res_1063_);
lean_dec(v_snd_1062_);
lean_dec(v_fst_1061_);
lean_dec_ref(v_pos_1060_);
return v___y_1059_;
}
}
v___jp_1071_:
{
if (v___y_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec(v___y_1073_);
v___x_1076_ = ((lean_object*)(l_Lean_Json_Parser_natNumDigits___closed__1));
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___y_1072_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
return v___x_1077_;
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = l_Lean_Json_Parser_natCoreNumDigits(v___x_1078_, v___x_1078_, v___y_1072_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_res_1080_; lean_object* v_pos_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1113_; 
v_res_1080_ = lean_ctor_get(v___x_1079_, 1);
v_pos_1081_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1083_ = v___x_1079_;
v_isShared_1084_ = v_isSharedCheck_1113_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_res_1080_);
lean_inc(v_pos_1081_);
lean_dec(v___x_1079_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1113_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v_fst_1085_; lean_object* v_snd_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1112_; 
v_fst_1085_ = lean_ctor_get(v_res_1080_, 0);
v_snd_1086_ = lean_ctor_get(v_res_1080_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_res_1080_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1088_ = v_res_1080_;
v_isShared_1089_ = v_isSharedCheck_1112_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_snd_1086_);
lean_inc(v_fst_1085_);
lean_dec(v_res_1080_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1112_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = lean_obj_once(&l_Lean_Json_Parser_numWithDecimals___closed__0, &l_Lean_Json_Parser_numWithDecimals___closed__0_once, _init_l_Lean_Json_Parser_numWithDecimals___closed__0);
v___x_1091_ = lean_nat_dec_lt(v___x_1090_, v_snd_1086_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v_fst_1094_; lean_object* v_snd_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1092_ = lean_unsigned_to_nat(10u);
v___x_1093_ = lean_nat_pow(v___x_1092_, v_snd_1086_);
v_fst_1094_ = lean_ctor_get(v_pos_1081_, 0);
lean_inc(v_fst_1094_);
v_snd_1095_ = lean_ctor_get(v_pos_1081_, 1);
lean_inc(v_snd_1095_);
v___x_1096_ = lean_nat_to_int(v___y_1073_);
v___x_1097_ = lean_nat_to_int(v___x_1093_);
v___x_1098_ = lean_int_mul(v___x_1096_, v___x_1097_);
lean_dec(v___x_1097_);
lean_dec(v___x_1096_);
v___x_1099_ = lean_nat_to_int(v_fst_1085_);
v___x_1100_ = lean_int_add(v___x_1098_, v___x_1099_);
lean_dec(v___x_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_int_mul(v___y_1074_, v___x_1100_);
lean_dec(v___x_1100_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1101_);
v___x_1103_ = v___x_1088_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_snd_1086_);
v___x_1103_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1105_; 
lean_inc_ref(v___x_1103_);
lean_inc(v_pos_1081_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v___x_1103_);
v___x_1105_ = v___x_1083_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_pos_1081_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
v___y_1059_ = v___x_1105_;
v_pos_1060_ = v_pos_1081_;
v_fst_1061_ = v_fst_1094_;
v_snd_1062_ = v_snd_1095_;
v_res_1063_ = v___x_1103_;
goto v___jp_1058_;
}
}
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
lean_del_object(v___x_1088_);
lean_dec(v_snd_1086_);
lean_dec(v_fst_1085_);
lean_dec(v___y_1073_);
v___x_1108_ = ((lean_object*)(l_Lean_Json_Parser_numWithDecimals___closed__2));
if (v_isShared_1084_ == 0)
{
lean_ctor_set_tag(v___x_1083_, 1);
lean_ctor_set(v___x_1083_, 1, v___x_1108_);
v___x_1110_ = v___x_1083_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_pos_1081_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v___x_1108_);
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
else
{
lean_object* v_pos_1114_; lean_object* v_err_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec(v___y_1073_);
v_pos_1114_ = lean_ctor_get(v___x_1079_, 0);
v_err_1115_ = lean_ctor_get(v___x_1079_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1079_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_err_1115_);
lean_inc(v_pos_1114_);
lean_dec(v___x_1079_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_pos_1114_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_err_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
v___jp_1123_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___y_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
return v___x_1126_;
}
v___jp_1127_:
{
lean_object* v___x_1133_; uint8_t v_decide_1134_; 
v___x_1133_ = lean_string_utf8_byte_size(v_fst_1130_);
v_decide_1134_ = lean_nat_dec_eq(v_snd_1131_, v___x_1133_);
if (v_decide_1134_ == 0)
{
uint32_t v___x_1135_; uint32_t v___x_1136_; uint8_t v___x_1137_; 
v___x_1135_ = lean_string_utf8_get_fast(v_fst_1130_, v_snd_1131_);
v___x_1136_ = 46;
v___x_1137_ = lean_uint32_dec_eq(v___x_1135_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1138_ = lean_nat_to_int(v_res_1132_);
v___x_1139_ = lean_int_mul(v___y_1128_, v___x_1138_);
lean_dec(v___x_1138_);
v___x_1140_ = l_Lean_JsonNumber_fromInt(v___x_1139_);
lean_inc_ref(v___x_1140_);
lean_inc_ref(v_pos_1129_);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v_pos_1129_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___y_1059_ = v___x_1141_;
v_pos_1060_ = v_pos_1129_;
v_fst_1061_ = v_fst_1130_;
v_snd_1062_ = v_snd_1131_;
v_res_1063_ = v___x_1140_;
goto v___jp_1058_;
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v_decide_1144_; 
lean_dec_ref(v_pos_1129_);
v___x_1142_ = lean_string_utf8_next_fast(v_fst_1130_, v_snd_1131_);
lean_dec(v_snd_1131_);
lean_inc(v_fst_1130_);
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v_fst_1130_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v_decide_1144_ = lean_nat_dec_eq(v___x_1142_, v___x_1133_);
if (v_decide_1144_ == 0)
{
if (v___x_1137_ == 0)
{
lean_dec(v_res_1132_);
lean_dec(v_fst_1130_);
v___y_1124_ = v___x_1143_;
goto v___jp_1123_;
}
else
{
uint32_t v___x_1145_; uint32_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = lean_string_utf8_get_fast(v_fst_1130_, v___x_1142_);
lean_dec(v_fst_1130_);
v___x_1146_ = 48;
v___x_1147_ = lean_uint32_dec_le(v___x_1146_, v___x_1145_);
if (v___x_1147_ == 0)
{
v___y_1072_ = v___x_1143_;
v___y_1073_ = v_res_1132_;
v___y_1074_ = v___y_1128_;
v___y_1075_ = v___x_1147_;
goto v___jp_1071_;
}
else
{
uint32_t v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = 57;
v___x_1149_ = lean_uint32_dec_le(v___x_1145_, v___x_1148_);
v___y_1072_ = v___x_1143_;
v___y_1073_ = v_res_1132_;
v___y_1074_ = v___y_1128_;
v___y_1075_ = v___x_1149_;
goto v___jp_1071_;
}
}
}
else
{
lean_dec(v_res_1132_);
lean_dec(v_fst_1130_);
v___y_1124_ = v___x_1143_;
goto v___jp_1123_;
}
}
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1150_ = lean_nat_to_int(v_res_1132_);
v___x_1151_ = lean_int_mul(v___y_1128_, v___x_1150_);
lean_dec(v___x_1150_);
v___x_1152_ = l_Lean_JsonNumber_fromInt(v___x_1151_);
lean_inc_ref(v___x_1152_);
lean_inc_ref(v_pos_1129_);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_pos_1129_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___y_1059_ = v___x_1153_;
v_pos_1060_ = v_pos_1129_;
v_fst_1061_ = v_fst_1130_;
v_snd_1062_ = v_snd_1131_;
v_res_1063_ = v___x_1152_;
goto v___jp_1058_;
}
}
v___jp_1154_:
{
if (v___y_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = ((lean_object*)(l_Lean_Json_Parser_natNonZero___closed__1));
v___x_1159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___y_1155_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_unsigned_to_nat(0u);
v___x_1161_ = l_Lean_Json_Parser_natCore(v___x_1160_, v___y_1155_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_pos_1162_; lean_object* v_res_1163_; lean_object* v_fst_1164_; lean_object* v_snd_1165_; 
v_pos_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_pos_1162_);
v_res_1163_ = lean_ctor_get(v___x_1161_, 1);
lean_inc(v_res_1163_);
lean_dec_ref_known(v___x_1161_, 2);
v_fst_1164_ = lean_ctor_get(v_pos_1162_, 0);
lean_inc(v_fst_1164_);
v_snd_1165_ = lean_ctor_get(v_pos_1162_, 1);
lean_inc(v_snd_1165_);
v___y_1128_ = v___y_1156_;
v_pos_1129_ = v_pos_1162_;
v_fst_1130_ = v_fst_1164_;
v_snd_1131_ = v_snd_1165_;
v_res_1132_ = v_res_1163_;
goto v___jp_1127_;
}
else
{
lean_object* v_pos_1166_; lean_object* v_err_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_pos_1166_ = lean_ctor_get(v___x_1161_, 0);
v_err_1167_ = lean_ctor_get(v___x_1161_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1161_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_err_1167_);
lean_inc(v_pos_1166_);
lean_dec(v___x_1161_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_pos_1166_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_err_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
v___jp_1175_:
{
lean_object* v___x_1180_; uint8_t v_decide_1181_; 
v___x_1180_ = lean_string_utf8_byte_size(v_fst_1177_);
v_decide_1181_ = lean_nat_dec_eq(v_snd_1178_, v___x_1180_);
if (v_decide_1181_ == 0)
{
uint32_t v___x_1182_; uint32_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1182_ = lean_string_utf8_get_fast(v_fst_1177_, v_snd_1178_);
v___x_1183_ = 48;
v___x_1184_ = lean_uint32_dec_eq(v___x_1182_, v___x_1183_);
if (v___x_1184_ == 0)
{
uint32_t v___x_1185_; uint8_t v___x_1186_; 
lean_dec(v_snd_1178_);
lean_dec(v_fst_1177_);
v___x_1185_ = 49;
v___x_1186_ = lean_uint32_dec_le(v___x_1185_, v___x_1182_);
if (v___x_1186_ == 0)
{
v___y_1155_ = v_pos_1176_;
v___y_1156_ = v_res_1179_;
v___y_1157_ = v___x_1186_;
goto v___jp_1154_;
}
else
{
uint32_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = 57;
v___x_1188_ = lean_uint32_dec_le(v___x_1182_, v___x_1187_);
v___y_1155_ = v_pos_1176_;
v___y_1156_ = v_res_1179_;
v___y_1157_ = v___x_1188_;
goto v___jp_1154_;
}
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec_ref(v_pos_1176_);
v___x_1189_ = lean_string_utf8_next_fast(v_fst_1177_, v_snd_1178_);
lean_dec(v_snd_1178_);
lean_inc(v_fst_1177_);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v_fst_1177_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___x_1191_ = lean_unsigned_to_nat(0u);
v___y_1128_ = v_res_1179_;
v_pos_1129_ = v___x_1190_;
v_fst_1130_ = v_fst_1177_;
v_snd_1131_ = v___x_1189_;
v_res_1132_ = v___x_1191_;
goto v___jp_1127_;
}
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec(v_snd_1178_);
lean_dec(v_fst_1177_);
v___x_1192_ = lean_box(0);
v___x_1193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1193_, 0, v_pos_1176_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
return v___x_1193_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(lean_object* v_msg_1215_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_box(1);
v___x_1217_ = lean_panic_fn_borrowed(v___x_1216_, v_msg_1215_);
return v___x_1217_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1221_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2));
v___x_1222_ = lean_unsigned_to_nat(35u);
v___x_1223_ = lean_unsigned_to_nat(182u);
v___x_1224_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1));
v___x_1225_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1226_ = l_mkPanicMessageWithDecl(v___x_1225_, v___x_1224_, v___x_1223_, v___x_1222_, v___x_1221_);
return v___x_1226_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1227_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__2));
v___x_1228_ = lean_unsigned_to_nat(21u);
v___x_1229_ = lean_unsigned_to_nat(183u);
v___x_1230_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__1));
v___x_1231_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1232_ = l_mkPanicMessageWithDecl(v___x_1231_, v___x_1230_, v___x_1229_, v___x_1228_, v___x_1227_);
return v___x_1232_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1235_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6));
v___x_1236_ = lean_unsigned_to_nat(35u);
v___x_1237_ = lean_unsigned_to_nat(276u);
v___x_1238_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5));
v___x_1239_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1240_ = l_mkPanicMessageWithDecl(v___x_1239_, v___x_1238_, v___x_1237_, v___x_1236_, v___x_1235_);
return v___x_1240_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1241_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__6));
v___x_1242_ = lean_unsigned_to_nat(21u);
v___x_1243_ = lean_unsigned_to_nat(277u);
v___x_1244_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__5));
v___x_1245_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__0));
v___x_1246_ = l_mkPanicMessageWithDecl(v___x_1245_, v___x_1244_, v___x_1243_, v___x_1242_, v___x_1241_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(lean_object* v_k_1247_, lean_object* v_v_1248_, lean_object* v_t_1249_){
_start:
{
if (lean_obj_tag(v_t_1249_) == 0)
{
lean_object* v_size_1250_; lean_object* v_k_1251_; lean_object* v_v_1252_; lean_object* v_l_1253_; lean_object* v_r_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1610_; 
v_size_1250_ = lean_ctor_get(v_t_1249_, 0);
v_k_1251_ = lean_ctor_get(v_t_1249_, 1);
v_v_1252_ = lean_ctor_get(v_t_1249_, 2);
v_l_1253_ = lean_ctor_get(v_t_1249_, 3);
v_r_1254_ = lean_ctor_get(v_t_1249_, 4);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_t_1249_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1256_ = v_t_1249_;
v_isShared_1257_ = v_isSharedCheck_1610_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_r_1254_);
lean_inc(v_l_1253_);
lean_inc(v_v_1252_);
lean_inc(v_k_1251_);
lean_inc(v_size_1250_);
lean_dec(v_t_1249_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1610_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
uint8_t v___x_1258_; 
v___x_1258_ = lean_string_compare(v_k_1247_, v_k_1251_);
switch(v___x_1258_)
{
case 0:
{
lean_object* v___x_1259_; 
lean_dec(v_size_1250_);
v___x_1259_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_1247_, v_v_1248_, v_l_1253_);
if (lean_obj_tag(v_r_1254_) == 0)
{
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_size_1260_; lean_object* v_size_1261_; lean_object* v_k_1262_; lean_object* v_v_1263_; lean_object* v_l_1264_; lean_object* v_r_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v_size_1260_ = lean_ctor_get(v_r_1254_, 0);
v_size_1261_ = lean_ctor_get(v___x_1259_, 0);
v_k_1262_ = lean_ctor_get(v___x_1259_, 1);
v_v_1263_ = lean_ctor_get(v___x_1259_, 2);
v_l_1264_ = lean_ctor_get(v___x_1259_, 3);
v_r_1265_ = lean_ctor_get(v___x_1259_, 4);
lean_inc(v_r_1265_);
v___x_1266_ = lean_unsigned_to_nat(3u);
v___x_1267_ = lean_nat_mul(v___x_1266_, v_size_1260_);
v___x_1268_ = lean_nat_dec_lt(v___x_1267_, v_size_1261_);
lean_dec(v___x_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
lean_dec(v_r_1265_);
v___x_1269_ = lean_unsigned_to_nat(1u);
v___x_1270_ = lean_nat_add(v___x_1269_, v_size_1261_);
v___x_1271_ = lean_nat_add(v___x_1270_, v_size_1260_);
lean_dec(v___x_1270_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 3, v___x_1259_);
lean_ctor_set(v___x_1256_, 0, v___x_1271_);
v___x_1273_ = v___x_1256_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v_r_1254_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
else
{
lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1346_; 
lean_inc(v_l_1264_);
lean_inc(v_v_1263_);
lean_inc(v_k_1262_);
lean_inc(v_size_1261_);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; lean_object* v_unused_1348_; lean_object* v_unused_1349_; lean_object* v_unused_1350_; lean_object* v_unused_1351_; 
v_unused_1347_ = lean_ctor_get(v___x_1259_, 4);
lean_dec(v_unused_1347_);
v_unused_1348_ = lean_ctor_get(v___x_1259_, 3);
lean_dec(v_unused_1348_);
v_unused_1349_ = lean_ctor_get(v___x_1259_, 2);
lean_dec(v_unused_1349_);
v_unused_1350_ = lean_ctor_get(v___x_1259_, 1);
lean_dec(v_unused_1350_);
v_unused_1351_ = lean_ctor_get(v___x_1259_, 0);
lean_dec(v_unused_1351_);
v___x_1276_ = v___x_1259_;
v_isShared_1277_ = v_isSharedCheck_1346_;
goto v_resetjp_1275_;
}
else
{
lean_dec(v___x_1259_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1346_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
if (lean_obj_tag(v_l_1264_) == 0)
{
if (lean_obj_tag(v_r_1265_) == 0)
{
lean_object* v_size_1278_; lean_object* v_size_1279_; lean_object* v_k_1280_; lean_object* v_v_1281_; lean_object* v_l_1282_; lean_object* v_r_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v_size_1278_ = lean_ctor_get(v_l_1264_, 0);
v_size_1279_ = lean_ctor_get(v_r_1265_, 0);
v_k_1280_ = lean_ctor_get(v_r_1265_, 1);
v_v_1281_ = lean_ctor_get(v_r_1265_, 2);
v_l_1282_ = lean_ctor_get(v_r_1265_, 3);
v_r_1283_ = lean_ctor_get(v_r_1265_, 4);
v___x_1284_ = lean_unsigned_to_nat(2u);
v___x_1285_ = lean_nat_mul(v___x_1284_, v_size_1278_);
v___x_1286_ = lean_nat_dec_lt(v_size_1279_, v___x_1285_);
lean_dec(v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1316_; 
lean_inc(v_r_1283_);
lean_inc(v_l_1282_);
lean_inc(v_v_1281_);
lean_inc(v_k_1280_);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_r_1265_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; lean_object* v_unused_1318_; lean_object* v_unused_1319_; lean_object* v_unused_1320_; lean_object* v_unused_1321_; 
v_unused_1317_ = lean_ctor_get(v_r_1265_, 4);
lean_dec(v_unused_1317_);
v_unused_1318_ = lean_ctor_get(v_r_1265_, 3);
lean_dec(v_unused_1318_);
v_unused_1319_ = lean_ctor_get(v_r_1265_, 2);
lean_dec(v_unused_1319_);
v_unused_1320_ = lean_ctor_get(v_r_1265_, 1);
lean_dec(v_unused_1320_);
v_unused_1321_ = lean_ctor_get(v_r_1265_, 0);
lean_dec(v_unused_1321_);
v___x_1288_ = v_r_1265_;
v_isShared_1289_ = v_isSharedCheck_1316_;
goto v_resetjp_1287_;
}
else
{
lean_dec(v_r_1265_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1316_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___x_1304_; lean_object* v___y_1306_; 
v___x_1290_ = lean_unsigned_to_nat(1u);
v___x_1291_ = lean_nat_add(v___x_1290_, v_size_1261_);
lean_dec(v_size_1261_);
v___x_1292_ = lean_nat_add(v___x_1291_, v_size_1260_);
lean_dec(v___x_1291_);
v___x_1304_ = lean_nat_add(v___x_1290_, v_size_1278_);
if (lean_obj_tag(v_l_1282_) == 0)
{
lean_object* v_size_1314_; 
v_size_1314_ = lean_ctor_get(v_l_1282_, 0);
lean_inc(v_size_1314_);
v___y_1306_ = v_size_1314_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_unsigned_to_nat(0u);
v___y_1306_ = v___x_1315_;
goto v___jp_1305_;
}
v___jp_1293_:
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1297_ = lean_nat_add(v___y_1295_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec(v___y_1295_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 4, v_r_1254_);
lean_ctor_set(v___x_1288_, 3, v_r_1283_);
lean_ctor_set(v___x_1288_, 2, v_v_1252_);
lean_ctor_set(v___x_1288_, 1, v_k_1251_);
lean_ctor_set(v___x_1288_, 0, v___x_1297_);
v___x_1299_ = v___x_1288_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v_r_1283_);
lean_ctor_set(v_reuseFailAlloc_1303_, 4, v_r_1254_);
v___x_1299_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1301_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 4, v___x_1299_);
lean_ctor_set(v___x_1276_, 3, v___y_1294_);
lean_ctor_set(v___x_1276_, 2, v_v_1281_);
lean_ctor_set(v___x_1276_, 1, v_k_1280_);
lean_ctor_set(v___x_1276_, 0, v___x_1292_);
v___x_1301_ = v___x_1276_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1302_, 3, v___y_1294_);
lean_ctor_set(v_reuseFailAlloc_1302_, 4, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
v___jp_1305_:
{
lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1307_ = lean_nat_add(v___x_1304_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec(v___x_1304_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v_l_1282_);
lean_ctor_set(v___x_1256_, 3, v_l_1264_);
lean_ctor_set(v___x_1256_, 2, v_v_1263_);
lean_ctor_set(v___x_1256_, 1, v_k_1262_);
lean_ctor_set(v___x_1256_, 0, v___x_1307_);
v___x_1309_ = v___x_1256_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_k_1262_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_v_1263_);
lean_ctor_set(v_reuseFailAlloc_1313_, 3, v_l_1264_);
lean_ctor_set(v_reuseFailAlloc_1313_, 4, v_l_1282_);
v___x_1309_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_nat_add(v___x_1290_, v_size_1260_);
if (lean_obj_tag(v_r_1283_) == 0)
{
lean_object* v_size_1311_; 
v_size_1311_ = lean_ctor_get(v_r_1283_, 0);
lean_inc(v_size_1311_);
v___y_1294_ = v___x_1309_;
v___y_1295_ = v___x_1310_;
v___y_1296_ = v_size_1311_;
goto v___jp_1293_;
}
else
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_unsigned_to_nat(0u);
v___y_1294_ = v___x_1309_;
v___y_1295_ = v___x_1310_;
v___y_1296_ = v___x_1312_;
goto v___jp_1293_;
}
}
}
}
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
lean_del_object(v___x_1256_);
v___x_1322_ = lean_unsigned_to_nat(1u);
v___x_1323_ = lean_nat_add(v___x_1322_, v_size_1261_);
lean_dec(v_size_1261_);
v___x_1324_ = lean_nat_add(v___x_1323_, v_size_1260_);
lean_dec(v___x_1323_);
v___x_1325_ = lean_nat_add(v___x_1322_, v_size_1260_);
v___x_1326_ = lean_nat_add(v___x_1325_, v_size_1279_);
lean_dec(v___x_1325_);
lean_inc_ref(v_r_1254_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 4, v_r_1254_);
lean_ctor_set(v___x_1276_, 3, v_r_1265_);
lean_ctor_set(v___x_1276_, 2, v_v_1252_);
lean_ctor_set(v___x_1276_, 1, v_k_1251_);
lean_ctor_set(v___x_1276_, 0, v___x_1326_);
v___x_1328_ = v___x_1276_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1341_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1341_, 3, v_r_1265_);
lean_ctor_set(v_reuseFailAlloc_1341_, 4, v_r_1254_);
v___x_1328_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
v_isSharedCheck_1335_ = !lean_is_exclusive(v_r_1254_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; lean_object* v_unused_1337_; lean_object* v_unused_1338_; lean_object* v_unused_1339_; lean_object* v_unused_1340_; 
v_unused_1336_ = lean_ctor_get(v_r_1254_, 4);
lean_dec(v_unused_1336_);
v_unused_1337_ = lean_ctor_get(v_r_1254_, 3);
lean_dec(v_unused_1337_);
v_unused_1338_ = lean_ctor_get(v_r_1254_, 2);
lean_dec(v_unused_1338_);
v_unused_1339_ = lean_ctor_get(v_r_1254_, 1);
lean_dec(v_unused_1339_);
v_unused_1340_ = lean_ctor_get(v_r_1254_, 0);
lean_dec(v_unused_1340_);
v___x_1330_ = v_r_1254_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_dec(v_r_1254_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 4, v___x_1328_);
lean_ctor_set(v___x_1330_, 3, v_l_1264_);
lean_ctor_set(v___x_1330_, 2, v_v_1263_);
lean_ctor_set(v___x_1330_, 1, v_k_1262_);
lean_ctor_set(v___x_1330_, 0, v___x_1324_);
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_k_1262_);
lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_v_1263_);
lean_ctor_set(v_reuseFailAlloc_1334_, 3, v_l_1264_);
lean_ctor_set(v_reuseFailAlloc_1334_, 4, v___x_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec_ref_known(v_l_1264_, 5);
lean_del_object(v___x_1276_);
lean_dec(v_v_1263_);
lean_dec(v_k_1262_);
lean_dec(v_size_1261_);
lean_dec_ref_known(v_r_1254_, 5);
lean_del_object(v___x_1256_);
lean_dec(v_v_1252_);
lean_dec(v_k_1251_);
v___x_1342_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__3);
v___x_1343_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1342_);
return v___x_1343_;
}
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_del_object(v___x_1276_);
lean_dec(v_r_1265_);
lean_dec(v_v_1263_);
lean_dec(v_k_1262_);
lean_dec(v_size_1261_);
lean_dec_ref_known(v_r_1254_, 5);
lean_del_object(v___x_1256_);
lean_dec(v_v_1252_);
lean_dec(v_k_1251_);
v___x_1344_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__4);
v___x_1345_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1344_);
return v___x_1345_;
}
}
}
}
else
{
lean_object* v_size_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
v_size_1352_ = lean_ctor_get(v_r_1254_, 0);
v___x_1353_ = lean_unsigned_to_nat(1u);
v___x_1354_ = lean_nat_add(v___x_1353_, v_size_1352_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 3, v___x_1259_);
lean_ctor_set(v___x_1256_, 0, v___x_1354_);
v___x_1356_ = v___x_1256_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v_r_1254_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
else
{
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_l_1358_; 
v_l_1358_ = lean_ctor_get(v___x_1259_, 3);
if (lean_obj_tag(v_l_1358_) == 0)
{
lean_object* v_r_1359_; 
lean_inc_ref(v_l_1358_);
v_r_1359_ = lean_ctor_get(v___x_1259_, 4);
lean_inc(v_r_1359_);
if (lean_obj_tag(v_r_1359_) == 0)
{
lean_object* v_size_1360_; lean_object* v_k_1361_; lean_object* v_v_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1376_; 
v_size_1360_ = lean_ctor_get(v___x_1259_, 0);
v_k_1361_ = lean_ctor_get(v___x_1259_, 1);
v_v_1362_ = lean_ctor_get(v___x_1259_, 2);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; lean_object* v_unused_1378_; 
v_unused_1377_ = lean_ctor_get(v___x_1259_, 4);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v___x_1259_, 3);
lean_dec(v_unused_1378_);
v___x_1364_ = v___x_1259_;
v_isShared_1365_ = v_isSharedCheck_1376_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_v_1362_);
lean_inc(v_k_1361_);
lean_inc(v_size_1360_);
lean_dec(v___x_1259_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1376_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_size_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v_size_1366_ = lean_ctor_get(v_r_1359_, 0);
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = lean_nat_add(v___x_1367_, v_size_1360_);
lean_dec(v_size_1360_);
v___x_1369_ = lean_nat_add(v___x_1367_, v_size_1366_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 4, v_r_1254_);
lean_ctor_set(v___x_1364_, 3, v_r_1359_);
lean_ctor_set(v___x_1364_, 2, v_v_1252_);
lean_ctor_set(v___x_1364_, 1, v_k_1251_);
lean_ctor_set(v___x_1364_, 0, v___x_1369_);
v___x_1371_ = v___x_1364_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1375_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1375_, 3, v_r_1359_);
lean_ctor_set(v_reuseFailAlloc_1375_, 4, v_r_1254_);
v___x_1371_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1373_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v___x_1371_);
lean_ctor_set(v___x_1256_, 3, v_l_1358_);
lean_ctor_set(v___x_1256_, 2, v_v_1362_);
lean_ctor_set(v___x_1256_, 1, v_k_1361_);
lean_ctor_set(v___x_1256_, 0, v___x_1368_);
v___x_1373_ = v___x_1256_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v_l_1358_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
else
{
lean_object* v_k_1379_; lean_object* v_v_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1392_; 
v_k_1379_ = lean_ctor_get(v___x_1259_, 1);
v_v_1380_ = lean_ctor_get(v___x_1259_, 2);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; lean_object* v_unused_1394_; lean_object* v_unused_1395_; 
v_unused_1393_ = lean_ctor_get(v___x_1259_, 4);
lean_dec(v_unused_1393_);
v_unused_1394_ = lean_ctor_get(v___x_1259_, 3);
lean_dec(v_unused_1394_);
v_unused_1395_ = lean_ctor_get(v___x_1259_, 0);
lean_dec(v_unused_1395_);
v___x_1382_ = v___x_1259_;
v_isShared_1383_ = v_isSharedCheck_1392_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_v_1380_);
lean_inc(v_k_1379_);
lean_dec(v___x_1259_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1392_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1384_ = lean_unsigned_to_nat(3u);
v___x_1385_ = lean_unsigned_to_nat(1u);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 3, v_r_1359_);
lean_ctor_set(v___x_1382_, 2, v_v_1252_);
lean_ctor_set(v___x_1382_, 1, v_k_1251_);
lean_ctor_set(v___x_1382_, 0, v___x_1385_);
v___x_1387_ = v___x_1382_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_r_1359_);
lean_ctor_set(v_reuseFailAlloc_1391_, 4, v_r_1359_);
v___x_1387_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1389_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v___x_1387_);
lean_ctor_set(v___x_1256_, 3, v_l_1358_);
lean_ctor_set(v___x_1256_, 2, v_v_1380_);
lean_ctor_set(v___x_1256_, 1, v_k_1379_);
lean_ctor_set(v___x_1256_, 0, v___x_1384_);
v___x_1389_ = v___x_1256_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_k_1379_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_v_1380_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_l_1358_);
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
else
{
lean_object* v_r_1396_; 
v_r_1396_ = lean_ctor_get(v___x_1259_, 4);
lean_inc(v_r_1396_);
if (lean_obj_tag(v_r_1396_) == 0)
{
lean_object* v_k_1397_; lean_object* v_v_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1422_; 
lean_inc(v_l_1358_);
v_k_1397_ = lean_ctor_get(v___x_1259_, 1);
v_v_1398_ = lean_ctor_get(v___x_1259_, 2);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; lean_object* v_unused_1424_; lean_object* v_unused_1425_; 
v_unused_1423_ = lean_ctor_get(v___x_1259_, 4);
lean_dec(v_unused_1423_);
v_unused_1424_ = lean_ctor_get(v___x_1259_, 3);
lean_dec(v_unused_1424_);
v_unused_1425_ = lean_ctor_get(v___x_1259_, 0);
lean_dec(v_unused_1425_);
v___x_1400_ = v___x_1259_;
v_isShared_1401_ = v_isSharedCheck_1422_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_v_1398_);
lean_inc(v_k_1397_);
lean_dec(v___x_1259_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1422_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v_k_1402_; lean_object* v_v_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1418_; 
v_k_1402_ = lean_ctor_get(v_r_1396_, 1);
v_v_1403_ = lean_ctor_get(v_r_1396_, 2);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_r_1396_);
if (v_isSharedCheck_1418_ == 0)
{
lean_object* v_unused_1419_; lean_object* v_unused_1420_; lean_object* v_unused_1421_; 
v_unused_1419_ = lean_ctor_get(v_r_1396_, 4);
lean_dec(v_unused_1419_);
v_unused_1420_ = lean_ctor_get(v_r_1396_, 3);
lean_dec(v_unused_1420_);
v_unused_1421_ = lean_ctor_get(v_r_1396_, 0);
lean_dec(v_unused_1421_);
v___x_1405_ = v_r_1396_;
v_isShared_1406_ = v_isSharedCheck_1418_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_v_1403_);
lean_inc(v_k_1402_);
lean_dec(v_r_1396_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1418_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1407_ = lean_unsigned_to_nat(3u);
v___x_1408_ = lean_unsigned_to_nat(1u);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 4, v_l_1358_);
lean_ctor_set(v___x_1405_, 3, v_l_1358_);
lean_ctor_set(v___x_1405_, 2, v_v_1398_);
lean_ctor_set(v___x_1405_, 1, v_k_1397_);
lean_ctor_set(v___x_1405_, 0, v___x_1408_);
v___x_1410_ = v___x_1405_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1397_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1398_);
lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_l_1358_);
lean_ctor_set(v_reuseFailAlloc_1417_, 4, v_l_1358_);
v___x_1410_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1412_; 
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 4, v_l_1358_);
lean_ctor_set(v___x_1400_, 2, v_v_1252_);
lean_ctor_set(v___x_1400_, 1, v_k_1251_);
lean_ctor_set(v___x_1400_, 0, v___x_1408_);
v___x_1412_ = v___x_1400_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1416_, 3, v_l_1358_);
lean_ctor_set(v_reuseFailAlloc_1416_, 4, v_l_1358_);
v___x_1412_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1414_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v___x_1412_);
lean_ctor_set(v___x_1256_, 3, v___x_1410_);
lean_ctor_set(v___x_1256_, 2, v_v_1403_);
lean_ctor_set(v___x_1256_, 1, v_k_1402_);
lean_ctor_set(v___x_1256_, 0, v___x_1407_);
v___x_1414_ = v___x_1256_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_k_1402_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_v_1403_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1415_, 4, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1426_ = lean_unsigned_to_nat(2u);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v_r_1396_);
lean_ctor_set(v___x_1256_, 3, v___x_1259_);
lean_ctor_set(v___x_1256_, 0, v___x_1426_);
v___x_1428_ = v___x_1256_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1429_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1429_, 3, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1429_, 4, v_r_1396_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = lean_unsigned_to_nat(1u);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v___x_1259_);
lean_ctor_set(v___x_1256_, 3, v___x_1259_);
lean_ctor_set(v___x_1256_, 0, v___x_1430_);
v___x_1432_ = v___x_1256_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1433_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1433_, 3, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1433_, 4, v___x_1259_);
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
case 1:
{
lean_object* v___x_1435_; 
lean_dec(v_v_1252_);
lean_dec(v_k_1251_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 2, v_v_1248_);
lean_ctor_set(v___x_1256_, 1, v_k_1247_);
v___x_1435_ = v___x_1256_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_size_1250_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_k_1247_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_v_1248_);
lean_ctor_set(v_reuseFailAlloc_1436_, 3, v_l_1253_);
lean_ctor_set(v_reuseFailAlloc_1436_, 4, v_r_1254_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
default: 
{
lean_object* v___x_1437_; 
lean_dec(v_size_1250_);
v___x_1437_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_1247_, v_v_1248_, v_r_1254_);
if (lean_obj_tag(v_l_1253_) == 0)
{
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_size_1438_; lean_object* v_size_1439_; lean_object* v_k_1440_; lean_object* v_v_1441_; lean_object* v_l_1442_; lean_object* v_r_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v_size_1438_ = lean_ctor_get(v_l_1253_, 0);
v_size_1439_ = lean_ctor_get(v___x_1437_, 0);
v_k_1440_ = lean_ctor_get(v___x_1437_, 1);
v_v_1441_ = lean_ctor_get(v___x_1437_, 2);
v_l_1442_ = lean_ctor_get(v___x_1437_, 3);
lean_inc(v_l_1442_);
v_r_1443_ = lean_ctor_get(v___x_1437_, 4);
v___x_1444_ = lean_unsigned_to_nat(3u);
v___x_1445_ = lean_nat_mul(v___x_1444_, v_size_1438_);
v___x_1446_ = lean_nat_dec_lt(v___x_1445_, v_size_1439_);
lean_dec(v___x_1445_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
lean_dec(v_l_1442_);
v___x_1447_ = lean_unsigned_to_nat(1u);
v___x_1448_ = lean_nat_add(v___x_1447_, v_size_1438_);
v___x_1449_ = lean_nat_add(v___x_1448_, v_size_1439_);
lean_dec(v___x_1448_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v___x_1437_);
lean_ctor_set(v___x_1256_, 0, v___x_1449_);
v___x_1451_ = v___x_1256_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_l_1253_);
lean_ctor_set(v_reuseFailAlloc_1452_, 4, v___x_1437_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
else
{
lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1522_; 
lean_inc(v_r_1443_);
lean_inc(v_v_1441_);
lean_inc(v_k_1440_);
lean_inc(v_size_1439_);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; lean_object* v_unused_1524_; lean_object* v_unused_1525_; lean_object* v_unused_1526_; lean_object* v_unused_1527_; 
v_unused_1523_ = lean_ctor_get(v___x_1437_, 4);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v___x_1437_, 3);
lean_dec(v_unused_1524_);
v_unused_1525_ = lean_ctor_get(v___x_1437_, 2);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v___x_1437_, 1);
lean_dec(v_unused_1526_);
v_unused_1527_ = lean_ctor_get(v___x_1437_, 0);
lean_dec(v_unused_1527_);
v___x_1454_ = v___x_1437_;
v_isShared_1455_ = v_isSharedCheck_1522_;
goto v_resetjp_1453_;
}
else
{
lean_dec(v___x_1437_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1522_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
if (lean_obj_tag(v_l_1442_) == 0)
{
if (lean_obj_tag(v_r_1443_) == 0)
{
lean_object* v_size_1456_; lean_object* v_k_1457_; lean_object* v_v_1458_; lean_object* v_l_1459_; lean_object* v_r_1460_; lean_object* v_size_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v_size_1456_ = lean_ctor_get(v_l_1442_, 0);
v_k_1457_ = lean_ctor_get(v_l_1442_, 1);
v_v_1458_ = lean_ctor_get(v_l_1442_, 2);
v_l_1459_ = lean_ctor_get(v_l_1442_, 3);
v_r_1460_ = lean_ctor_get(v_l_1442_, 4);
v_size_1461_ = lean_ctor_get(v_r_1443_, 0);
v___x_1462_ = lean_unsigned_to_nat(2u);
v___x_1463_ = lean_nat_mul(v___x_1462_, v_size_1461_);
v___x_1464_ = lean_nat_dec_lt(v_size_1456_, v___x_1463_);
lean_dec(v___x_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1493_; 
lean_inc(v_r_1460_);
lean_inc(v_l_1459_);
lean_inc(v_v_1458_);
lean_inc(v_k_1457_);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_l_1442_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; lean_object* v_unused_1495_; lean_object* v_unused_1496_; lean_object* v_unused_1497_; lean_object* v_unused_1498_; 
v_unused_1494_ = lean_ctor_get(v_l_1442_, 4);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_l_1442_, 3);
lean_dec(v_unused_1495_);
v_unused_1496_ = lean_ctor_get(v_l_1442_, 2);
lean_dec(v_unused_1496_);
v_unused_1497_ = lean_ctor_get(v_l_1442_, 1);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v_l_1442_, 0);
lean_dec(v_unused_1498_);
v___x_1466_ = v_l_1442_;
v_isShared_1467_ = v_isSharedCheck_1493_;
goto v_resetjp_1465_;
}
else
{
lean_dec(v_l_1442_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1493_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1483_; 
v___x_1468_ = lean_unsigned_to_nat(1u);
v___x_1469_ = lean_nat_add(v___x_1468_, v_size_1438_);
v___x_1470_ = lean_nat_add(v___x_1469_, v_size_1439_);
lean_dec(v_size_1439_);
if (lean_obj_tag(v_l_1459_) == 0)
{
lean_object* v_size_1491_; 
v_size_1491_ = lean_ctor_get(v_l_1459_, 0);
lean_inc(v_size_1491_);
v___y_1483_ = v_size_1491_;
goto v___jp_1482_;
}
else
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_unsigned_to_nat(0u);
v___y_1483_ = v___x_1492_;
goto v___jp_1482_;
}
v___jp_1471_:
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1475_ = lean_nat_add(v___y_1472_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec(v___y_1472_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 4, v_r_1443_);
lean_ctor_set(v___x_1466_, 3, v_r_1460_);
lean_ctor_set(v___x_1466_, 2, v_v_1441_);
lean_ctor_set(v___x_1466_, 1, v_k_1440_);
lean_ctor_set(v___x_1466_, 0, v___x_1475_);
v___x_1477_ = v___x_1466_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_r_1460_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v_r_1443_);
v___x_1477_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1479_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 4, v___x_1477_);
lean_ctor_set(v___x_1454_, 3, v___y_1473_);
lean_ctor_set(v___x_1454_, 2, v_v_1458_);
lean_ctor_set(v___x_1454_, 1, v_k_1457_);
lean_ctor_set(v___x_1454_, 0, v___x_1470_);
v___x_1479_ = v___x_1454_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1470_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_k_1457_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_v_1458_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v___y_1473_);
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
v___jp_1482_:
{
lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1484_ = lean_nat_add(v___x_1469_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec(v___x_1469_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v_l_1459_);
lean_ctor_set(v___x_1256_, 0, v___x_1484_);
v___x_1486_ = v___x_1256_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_l_1253_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_l_1459_);
v___x_1486_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_nat_add(v___x_1468_, v_size_1461_);
if (lean_obj_tag(v_r_1460_) == 0)
{
lean_object* v_size_1488_; 
v_size_1488_ = lean_ctor_get(v_r_1460_, 0);
lean_inc(v_size_1488_);
v___y_1472_ = v___x_1487_;
v___y_1473_ = v___x_1486_;
v___y_1474_ = v_size_1488_;
goto v___jp_1471_;
}
else
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_unsigned_to_nat(0u);
v___y_1472_ = v___x_1487_;
v___y_1473_ = v___x_1486_;
v___y_1474_ = v___x_1489_;
goto v___jp_1471_;
}
}
}
}
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
lean_del_object(v___x_1256_);
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = lean_nat_add(v___x_1499_, v_size_1438_);
v___x_1501_ = lean_nat_add(v___x_1500_, v_size_1439_);
lean_dec(v_size_1439_);
v___x_1502_ = lean_nat_add(v___x_1500_, v_size_1456_);
lean_dec(v___x_1500_);
lean_inc_ref(v_l_1253_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 4, v_l_1442_);
lean_ctor_set(v___x_1454_, 3, v_l_1253_);
lean_ctor_set(v___x_1454_, 2, v_v_1252_);
lean_ctor_set(v___x_1454_, 1, v_k_1251_);
lean_ctor_set(v___x_1454_, 0, v___x_1502_);
v___x_1504_ = v___x_1454_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_l_1253_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v_l_1442_);
v___x_1504_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
v_isSharedCheck_1511_ = !lean_is_exclusive(v_l_1253_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; lean_object* v_unused_1513_; lean_object* v_unused_1514_; lean_object* v_unused_1515_; lean_object* v_unused_1516_; 
v_unused_1512_ = lean_ctor_get(v_l_1253_, 4);
lean_dec(v_unused_1512_);
v_unused_1513_ = lean_ctor_get(v_l_1253_, 3);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v_l_1253_, 2);
lean_dec(v_unused_1514_);
v_unused_1515_ = lean_ctor_get(v_l_1253_, 1);
lean_dec(v_unused_1515_);
v_unused_1516_ = lean_ctor_get(v_l_1253_, 0);
lean_dec(v_unused_1516_);
v___x_1506_ = v_l_1253_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_dec(v_l_1253_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 4, v_r_1443_);
lean_ctor_set(v___x_1506_, 3, v___x_1504_);
lean_ctor_set(v___x_1506_, 2, v_v_1441_);
lean_ctor_set(v___x_1506_, 1, v_k_1440_);
lean_ctor_set(v___x_1506_, 0, v___x_1501_);
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1510_, 3, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1510_, 4, v_r_1443_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec_ref_known(v_l_1442_, 5);
lean_del_object(v___x_1454_);
lean_dec(v_v_1441_);
lean_dec(v_k_1440_);
lean_dec(v_size_1439_);
lean_dec_ref_known(v_l_1253_, 5);
lean_del_object(v___x_1256_);
lean_dec(v_v_1252_);
lean_dec(v_k_1251_);
v___x_1518_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__7);
v___x_1519_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1518_);
return v___x_1519_;
}
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_del_object(v___x_1454_);
lean_dec(v_r_1443_);
lean_dec(v_v_1441_);
lean_dec(v_k_1440_);
lean_dec(v_size_1439_);
lean_dec_ref_known(v_l_1253_, 5);
lean_del_object(v___x_1256_);
lean_dec(v_v_1252_);
lean_dec(v_k_1251_);
v___x_1520_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg___closed__8);
v___x_1521_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v___x_1520_);
return v___x_1521_;
}
}
}
}
else
{
lean_object* v_size_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
v_size_1528_ = lean_ctor_get(v_l_1253_, 0);
v___x_1529_ = lean_unsigned_to_nat(1u);
v___x_1530_ = lean_nat_add(v___x_1529_, v_size_1528_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v___x_1437_);
lean_ctor_set(v___x_1256_, 0, v___x_1530_);
v___x_1532_ = v___x_1256_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_l_1253_);
lean_ctor_set(v_reuseFailAlloc_1533_, 4, v___x_1437_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
else
{
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_l_1534_; 
v_l_1534_ = lean_ctor_get(v___x_1437_, 3);
lean_inc(v_l_1534_);
if (lean_obj_tag(v_l_1534_) == 0)
{
lean_object* v_r_1535_; 
v_r_1535_ = lean_ctor_get(v___x_1437_, 4);
lean_inc(v_r_1535_);
if (lean_obj_tag(v_r_1535_) == 0)
{
lean_object* v_size_1536_; lean_object* v_k_1537_; lean_object* v_v_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1552_; 
v_size_1536_ = lean_ctor_get(v___x_1437_, 0);
v_k_1537_ = lean_ctor_get(v___x_1437_, 1);
v_v_1538_ = lean_ctor_get(v___x_1437_, 2);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1552_ == 0)
{
lean_object* v_unused_1553_; lean_object* v_unused_1554_; 
v_unused_1553_ = lean_ctor_get(v___x_1437_, 4);
lean_dec(v_unused_1553_);
v_unused_1554_ = lean_ctor_get(v___x_1437_, 3);
lean_dec(v_unused_1554_);
v___x_1540_ = v___x_1437_;
v_isShared_1541_ = v_isSharedCheck_1552_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_v_1538_);
lean_inc(v_k_1537_);
lean_inc(v_size_1536_);
lean_dec(v___x_1437_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1552_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v_size_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1547_; 
v_size_1542_ = lean_ctor_get(v_l_1534_, 0);
v___x_1543_ = lean_unsigned_to_nat(1u);
v___x_1544_ = lean_nat_add(v___x_1543_, v_size_1536_);
lean_dec(v_size_1536_);
v___x_1545_ = lean_nat_add(v___x_1543_, v_size_1542_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 4, v_l_1534_);
lean_ctor_set(v___x_1540_, 3, v_l_1253_);
lean_ctor_set(v___x_1540_, 2, v_v_1252_);
lean_ctor_set(v___x_1540_, 1, v_k_1251_);
lean_ctor_set(v___x_1540_, 0, v___x_1545_);
v___x_1547_ = v___x_1540_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1551_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1551_, 3, v_l_1253_);
lean_ctor_set(v_reuseFailAlloc_1551_, 4, v_l_1534_);
v___x_1547_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1549_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v_r_1535_);
lean_ctor_set(v___x_1256_, 3, v___x_1547_);
lean_ctor_set(v___x_1256_, 2, v_v_1538_);
lean_ctor_set(v___x_1256_, 1, v_k_1537_);
lean_ctor_set(v___x_1256_, 0, v___x_1544_);
v___x_1549_ = v___x_1256_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_k_1537_);
lean_ctor_set(v_reuseFailAlloc_1550_, 2, v_v_1538_);
lean_ctor_set(v_reuseFailAlloc_1550_, 3, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1550_, 4, v_r_1535_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
else
{
lean_object* v_k_1555_; lean_object* v_v_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1580_; 
v_k_1555_ = lean_ctor_get(v___x_1437_, 1);
v_v_1556_ = lean_ctor_get(v___x_1437_, 2);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; lean_object* v_unused_1582_; lean_object* v_unused_1583_; 
v_unused_1581_ = lean_ctor_get(v___x_1437_, 4);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v___x_1437_, 3);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v___x_1437_, 0);
lean_dec(v_unused_1583_);
v___x_1558_ = v___x_1437_;
v_isShared_1559_ = v_isSharedCheck_1580_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_v_1556_);
lean_inc(v_k_1555_);
lean_dec(v___x_1437_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1580_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v_k_1560_; lean_object* v_v_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1576_; 
v_k_1560_ = lean_ctor_get(v_l_1534_, 1);
v_v_1561_ = lean_ctor_get(v_l_1534_, 2);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_l_1534_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; lean_object* v_unused_1578_; lean_object* v_unused_1579_; 
v_unused_1577_ = lean_ctor_get(v_l_1534_, 4);
lean_dec(v_unused_1577_);
v_unused_1578_ = lean_ctor_get(v_l_1534_, 3);
lean_dec(v_unused_1578_);
v_unused_1579_ = lean_ctor_get(v_l_1534_, 0);
lean_dec(v_unused_1579_);
v___x_1563_ = v_l_1534_;
v_isShared_1564_ = v_isSharedCheck_1576_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_v_1561_);
lean_inc(v_k_1560_);
lean_dec(v_l_1534_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1576_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1565_ = lean_unsigned_to_nat(3u);
v___x_1566_ = lean_unsigned_to_nat(1u);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 4, v_r_1535_);
lean_ctor_set(v___x_1563_, 3, v_r_1535_);
lean_ctor_set(v___x_1563_, 2, v_v_1252_);
lean_ctor_set(v___x_1563_, 1, v_k_1251_);
lean_ctor_set(v___x_1563_, 0, v___x_1566_);
v___x_1568_ = v___x_1563_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1575_, 3, v_r_1535_);
lean_ctor_set(v_reuseFailAlloc_1575_, 4, v_r_1535_);
v___x_1568_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1570_; 
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 3, v_r_1535_);
lean_ctor_set(v___x_1558_, 0, v___x_1566_);
v___x_1570_ = v___x_1558_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_k_1555_);
lean_ctor_set(v_reuseFailAlloc_1574_, 2, v_v_1556_);
lean_ctor_set(v_reuseFailAlloc_1574_, 3, v_r_1535_);
lean_ctor_set(v_reuseFailAlloc_1574_, 4, v_r_1535_);
v___x_1570_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1572_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v___x_1570_);
lean_ctor_set(v___x_1256_, 3, v___x_1568_);
lean_ctor_set(v___x_1256_, 2, v_v_1561_);
lean_ctor_set(v___x_1256_, 1, v_k_1560_);
lean_ctor_set(v___x_1256_, 0, v___x_1565_);
v___x_1572_ = v___x_1256_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_k_1560_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v_v_1561_);
lean_ctor_set(v_reuseFailAlloc_1573_, 3, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1573_, 4, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1584_; 
v_r_1584_ = lean_ctor_get(v___x_1437_, 4);
lean_inc(v_r_1584_);
if (lean_obj_tag(v_r_1584_) == 0)
{
lean_object* v_k_1585_; lean_object* v_v_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1598_; 
v_k_1585_ = lean_ctor_get(v___x_1437_, 1);
v_v_1586_ = lean_ctor_get(v___x_1437_, 2);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; lean_object* v_unused_1600_; lean_object* v_unused_1601_; 
v_unused_1599_ = lean_ctor_get(v___x_1437_, 4);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v___x_1437_, 3);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v___x_1437_, 0);
lean_dec(v_unused_1601_);
v___x_1588_ = v___x_1437_;
v_isShared_1589_ = v_isSharedCheck_1598_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_v_1586_);
lean_inc(v_k_1585_);
lean_dec(v___x_1437_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1598_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1590_ = lean_unsigned_to_nat(3u);
v___x_1591_ = lean_unsigned_to_nat(1u);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 4, v_l_1534_);
lean_ctor_set(v___x_1588_, 2, v_v_1252_);
lean_ctor_set(v___x_1588_, 1, v_k_1251_);
lean_ctor_set(v___x_1588_, 0, v___x_1591_);
v___x_1593_ = v___x_1588_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1597_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1597_, 3, v_l_1534_);
lean_ctor_set(v_reuseFailAlloc_1597_, 4, v_l_1534_);
v___x_1593_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1595_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v_r_1584_);
lean_ctor_set(v___x_1256_, 3, v___x_1593_);
lean_ctor_set(v___x_1256_, 2, v_v_1586_);
lean_ctor_set(v___x_1256_, 1, v_k_1585_);
lean_ctor_set(v___x_1256_, 0, v___x_1590_);
v___x_1595_ = v___x_1256_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_k_1585_);
lean_ctor_set(v_reuseFailAlloc_1596_, 2, v_v_1586_);
lean_ctor_set(v_reuseFailAlloc_1596_, 3, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1596_, 4, v_r_1584_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1602_ = lean_unsigned_to_nat(2u);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v___x_1437_);
lean_ctor_set(v___x_1256_, 3, v_r_1584_);
lean_ctor_set(v___x_1256_, 0, v___x_1602_);
v___x_1604_ = v___x_1256_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1605_, 3, v_r_1584_);
lean_ctor_set(v_reuseFailAlloc_1605_, 4, v___x_1437_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1606_ = lean_unsigned_to_nat(1u);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v___x_1437_);
lean_ctor_set(v___x_1256_, 3, v___x_1437_);
lean_ctor_set(v___x_1256_, 0, v___x_1606_);
v___x_1608_ = v___x_1256_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1609_, 3, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1609_, 4, v___x_1437_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_unsigned_to_nat(1u);
v___x_1612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
lean_ctor_set(v___x_1612_, 1, v_k_1247_);
lean_ctor_set(v___x_1612_, 2, v_v_1248_);
lean_ctor_set(v___x_1612_, 3, v_t_1249_);
lean_ctor_set(v___x_1612_, 4, v_t_1249_);
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore(lean_object* v_kvs_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_fst_1633_; lean_object* v_snd_1634_; lean_object* v___x_1635_; uint8_t v_decide_1636_; 
v_fst_1633_ = lean_ctor_get(v_a_1632_, 0);
v_snd_1634_ = lean_ctor_get(v_a_1632_, 1);
v___x_1635_ = lean_string_utf8_byte_size(v_fst_1633_);
v_decide_1636_ = lean_nat_dec_eq(v_snd_1634_, v___x_1635_);
if (v_decide_1636_ == 0)
{
uint32_t v___x_1637_; uint32_t v___x_1638_; uint8_t v___x_1639_; 
v___x_1637_ = lean_string_utf8_get_fast(v_fst_1633_, v_snd_1634_);
v___x_1638_ = 34;
v___x_1639_ = lean_uint32_dec_eq(v___x_1637_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_dec(v_kvs_1631_);
v___x_1640_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__1));
v___x_1641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1641_, 0, v_a_1632_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
return v___x_1641_;
}
else
{
lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1745_; 
lean_inc(v_snd_1634_);
lean_inc(v_fst_1633_);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_a_1632_);
if (v_isSharedCheck_1745_ == 0)
{
lean_object* v_unused_1746_; lean_object* v_unused_1747_; 
v_unused_1746_ = lean_ctor_get(v_a_1632_, 1);
lean_dec(v_unused_1746_);
v_unused_1747_ = lean_ctor_get(v_a_1632_, 0);
lean_dec(v_unused_1747_);
v___x_1643_ = v_a_1632_;
v_isShared_1644_ = v_isSharedCheck_1745_;
goto v_resetjp_1642_;
}
else
{
lean_dec(v_a_1632_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1745_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1645_ = lean_string_utf8_next_fast(v_fst_1633_, v_snd_1634_);
lean_dec(v_snd_1634_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 1, v___x_1645_);
v___x_1647_ = v___x_1643_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_fst_1633_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_1649_ = l_Lean_Json_Parser_strCore(v___x_1648_, v___x_1647_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_pos_1650_; lean_object* v_res_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1734_; 
v_pos_1650_ = lean_ctor_get(v___x_1649_, 0);
v_res_1651_ = lean_ctor_get(v___x_1649_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1653_ = v___x_1649_;
v_isShared_1654_ = v_isSharedCheck_1734_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_res_1651_);
lean_inc(v_pos_1650_);
lean_dec(v___x_1649_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1734_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v_fst_1655_; lean_object* v_snd_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1733_; 
v_fst_1655_ = lean_ctor_get(v_pos_1650_, 0);
v_snd_1656_ = lean_ctor_get(v_pos_1650_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_pos_1650_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1658_ = v_pos_1650_;
v_isShared_1659_ = v_isSharedCheck_1733_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_snd_1656_);
lean_inc(v_fst_1655_);
lean_dec(v_pos_1650_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1733_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1655_, v_snd_1656_);
lean_inc(v___x_1660_);
lean_inc(v_fst_1655_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 1, v___x_1660_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_fst_1655_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1668_; uint8_t v_decide_1669_; 
v___x_1668_ = lean_string_utf8_byte_size(v_fst_1655_);
v_decide_1669_ = lean_nat_dec_eq(v___x_1660_, v___x_1668_);
if (v_decide_1669_ == 0)
{
if (v___x_1639_ == 0)
{
lean_dec(v___x_1660_);
lean_dec(v_fst_1655_);
lean_dec(v_res_1651_);
lean_dec(v_kvs_1631_);
goto v___jp_1663_;
}
else
{
uint32_t v___x_1670_; uint32_t v___x_1671_; uint8_t v___x_1672_; 
lean_del_object(v___x_1653_);
v___x_1670_ = lean_string_utf8_get_fast(v_fst_1655_, v___x_1660_);
v___x_1671_ = 58;
v___x_1672_ = lean_uint32_dec_eq(v___x_1670_, v___x_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_dec(v___x_1660_);
lean_dec(v_fst_1655_);
lean_dec(v_res_1651_);
lean_dec(v_kvs_1631_);
v___x_1673_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__3));
v___x_1674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1662_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
return v___x_1674_;
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec_ref(v___x_1662_);
v___x_1675_ = lean_string_utf8_next_fast(v_fst_1655_, v___x_1660_);
lean_dec(v___x_1660_);
v___x_1676_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1655_, v___x_1675_);
v___x_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1677_, 0, v_fst_1655_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = l_Lean_Json_Parser_anyCore(v___x_1677_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_pos_1679_; lean_object* v_res_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1722_; 
v_pos_1679_ = lean_ctor_get(v___x_1678_, 0);
v_res_1680_ = lean_ctor_get(v___x_1678_, 1);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1682_ = v___x_1678_;
v_isShared_1683_ = v_isSharedCheck_1722_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_res_1680_);
lean_inc(v_pos_1679_);
lean_dec(v___x_1678_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1722_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v_fst_1689_; lean_object* v_snd_1690_; lean_object* v___x_1691_; uint8_t v_decide_1692_; 
v_fst_1689_ = lean_ctor_get(v_pos_1679_, 0);
v_snd_1690_ = lean_ctor_get(v_pos_1679_, 1);
v___x_1691_ = lean_string_utf8_byte_size(v_fst_1689_);
v_decide_1692_ = lean_nat_dec_eq(v_snd_1690_, v___x_1691_);
if (v_decide_1692_ == 0)
{
if (v___x_1672_ == 0)
{
lean_dec(v_res_1680_);
lean_dec(v_res_1651_);
lean_dec(v_kvs_1631_);
goto v___jp_1684_;
}
else
{
lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1719_; 
lean_inc(v_snd_1690_);
lean_inc(v_fst_1689_);
lean_del_object(v___x_1682_);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_pos_1679_);
if (v_isSharedCheck_1719_ == 0)
{
lean_object* v_unused_1720_; lean_object* v_unused_1721_; 
v_unused_1720_ = lean_ctor_get(v_pos_1679_, 1);
lean_dec(v_unused_1720_);
v_unused_1721_ = lean_ctor_get(v_pos_1679_, 0);
lean_dec(v_unused_1721_);
v___x_1694_ = v_pos_1679_;
v_isShared_1695_ = v_isSharedCheck_1719_;
goto v_resetjp_1693_;
}
else
{
lean_dec(v_pos_1679_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1719_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
uint32_t v___x_1696_; lean_object* v___x_1697_; uint32_t v___x_1698_; uint8_t v___x_1699_; 
v___x_1696_ = lean_string_utf8_get_fast(v_fst_1689_, v_snd_1690_);
v___x_1697_ = lean_string_utf8_next_fast(v_fst_1689_, v_snd_1690_);
lean_dec(v_snd_1690_);
v___x_1698_ = 125;
v___x_1699_ = lean_uint32_dec_eq(v___x_1696_, v___x_1698_);
if (v___x_1699_ == 0)
{
uint32_t v___x_1700_; uint8_t v___x_1701_; 
v___x_1700_ = 44;
v___x_1701_ = lean_uint32_dec_eq(v___x_1696_, v___x_1700_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1703_; 
lean_dec(v_res_1680_);
lean_dec(v_res_1651_);
lean_dec(v_kvs_1631_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 1, v___x_1697_);
v___x_1703_ = v___x_1694_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_fst_1689_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___x_1697_);
v___x_1703_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = ((lean_object*)(l_Lean_Json_Parser_objectCore___closed__5));
v___x_1705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
return v___x_1705_;
}
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1707_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1689_, v___x_1697_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 1, v___x_1707_);
v___x_1709_ = v___x_1694_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_fst_1689_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_res_1651_, v_res_1680_, v_kvs_1631_);
v_kvs_1631_ = v___x_1710_;
v_a_1632_ = v___x_1709_;
goto _start;
}
}
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1713_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1689_, v___x_1697_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 1, v___x_1713_);
v___x_1715_ = v___x_1694_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_fst_1689_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_res_1651_, v_res_1680_, v_kvs_1631_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
return v___x_1717_;
}
}
}
}
}
else
{
lean_dec(v_res_1680_);
lean_dec(v_res_1651_);
lean_dec(v_kvs_1631_);
goto v___jp_1684_;
}
v___jp_1684_:
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1685_ = lean_box(0);
if (v_isShared_1683_ == 0)
{
lean_ctor_set_tag(v___x_1682_, 1);
lean_ctor_set(v___x_1682_, 1, v___x_1685_);
v___x_1687_ = v___x_1682_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_pos_1679_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
else
{
lean_object* v_pos_1723_; lean_object* v_err_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec(v_res_1651_);
lean_dec(v_kvs_1631_);
v_pos_1723_ = lean_ctor_get(v___x_1678_, 0);
v_err_1724_ = lean_ctor_get(v___x_1678_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1678_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_err_1724_);
lean_inc(v_pos_1723_);
lean_dec(v___x_1678_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_pos_1723_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_err_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1660_);
lean_dec(v_fst_1655_);
lean_dec(v_res_1651_);
lean_dec(v_kvs_1631_);
goto v___jp_1663_;
}
v___jp_1663_:
{
lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1664_ = lean_box(0);
if (v_isShared_1654_ == 0)
{
lean_ctor_set_tag(v___x_1653_, 1);
lean_ctor_set(v___x_1653_, 1, v___x_1664_);
lean_ctor_set(v___x_1653_, 0, v___x_1662_);
v___x_1666_ = v___x_1653_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1735_; lean_object* v_err_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec(v_kvs_1631_);
v_pos_1735_ = lean_ctor_get(v___x_1649_, 0);
v_err_1736_ = lean_ctor_get(v___x_1649_, 1);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1649_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_err_1736_);
lean_inc(v_pos_1735_);
lean_dec(v___x_1649_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_pos_1735_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_err_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec(v_kvs_1631_);
v___x_1748_ = lean_box(0);
v___x_1749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1749_, 0, v_a_1632_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object* v_a_1756_){
_start:
{
lean_object* v_fst_1791_; lean_object* v_snd_1792_; lean_object* v___x_1793_; uint8_t v_decide_1794_; 
v_fst_1791_ = lean_ctor_get(v_a_1756_, 0);
v_snd_1792_ = lean_ctor_get(v_a_1756_, 1);
v___x_1793_ = lean_string_utf8_byte_size(v_fst_1791_);
v_decide_1794_ = lean_nat_dec_eq(v_snd_1792_, v___x_1793_);
if (v_decide_1794_ == 0)
{
uint32_t v___x_1795_; uint32_t v___x_1796_; uint8_t v___x_1797_; 
v___x_1795_ = lean_string_utf8_get_fast(v_fst_1791_, v_snd_1792_);
v___x_1796_ = 91;
v___x_1797_ = lean_uint32_dec_eq(v___x_1795_, v___x_1796_);
if (v___x_1797_ == 0)
{
uint32_t v___x_1798_; uint8_t v___x_1799_; 
v___x_1798_ = 123;
v___x_1799_ = lean_uint32_dec_eq(v___x_1795_, v___x_1798_);
if (v___x_1799_ == 0)
{
uint32_t v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = 34;
v___x_1801_ = lean_uint32_dec_eq(v___x_1795_, v___x_1800_);
if (v___x_1801_ == 0)
{
uint32_t v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = 102;
v___x_1803_ = lean_uint32_dec_eq(v___x_1795_, v___x_1802_);
if (v___x_1803_ == 0)
{
uint32_t v___x_1804_; uint8_t v___x_1805_; 
v___x_1804_ = 116;
v___x_1805_ = lean_uint32_dec_eq(v___x_1795_, v___x_1804_);
if (v___x_1805_ == 0)
{
uint32_t v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = 110;
v___x_1807_ = lean_uint32_dec_eq(v___x_1795_, v___x_1806_);
if (v___x_1807_ == 0)
{
uint32_t v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = 45;
v___x_1809_ = lean_uint32_dec_eq(v___x_1795_, v___x_1808_);
if (v___x_1809_ == 0)
{
uint32_t v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = 48;
v___x_1811_ = lean_uint32_dec_le(v___x_1810_, v___x_1795_);
if (v___x_1811_ == 0)
{
goto v___jp_1788_;
}
else
{
uint32_t v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = 57;
v___x_1813_ = lean_uint32_dec_le(v___x_1795_, v___x_1812_);
if (v___x_1813_ == 0)
{
goto v___jp_1788_;
}
else
{
goto v___jp_1757_;
}
}
}
else
{
goto v___jp_1757_;
}
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__2));
v___x_1815_ = l_Std_Internal_Parsec_String_pstring(v___x_1814_, v_a_1756_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_pos_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1834_; 
v_pos_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1834_ == 0)
{
lean_object* v_unused_1835_; 
v_unused_1835_ = lean_ctor_get(v___x_1815_, 1);
lean_dec(v_unused_1835_);
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1834_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_pos_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1834_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v_fst_1820_; lean_object* v_snd_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1833_; 
v_fst_1820_ = lean_ctor_get(v_pos_1816_, 0);
v_snd_1821_ = lean_ctor_get(v_pos_1816_, 1);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_pos_1816_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1823_ = v_pos_1816_;
v_isShared_1824_ = v_isSharedCheck_1833_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_snd_1821_);
lean_inc(v_fst_1820_);
lean_dec(v_pos_1816_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1833_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1825_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1820_, v_snd_1821_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 1, v___x_1825_);
v___x_1827_ = v___x_1823_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_fst_1820_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1828_ = lean_box(0);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 1, v___x_1828_);
lean_ctor_set(v___x_1818_, 0, v___x_1827_);
v___x_1830_ = v___x_1818_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
else
{
lean_object* v_pos_1836_; lean_object* v_err_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
v_pos_1836_ = lean_ctor_get(v___x_1815_, 0);
v_err_1837_ = lean_ctor_get(v___x_1815_, 1);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1815_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_err_1837_);
lean_inc(v_pos_1836_);
lean_dec(v___x_1815_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_pos_1836_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_err_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__3));
v___x_1846_ = l_Std_Internal_Parsec_String_pstring(v___x_1845_, v_a_1756_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_pos_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1865_; 
v_pos_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1865_ == 0)
{
lean_object* v_unused_1866_; 
v_unused_1866_ = lean_ctor_get(v___x_1846_, 1);
lean_dec(v_unused_1866_);
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1865_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_pos_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1865_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v_fst_1851_; lean_object* v_snd_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1864_; 
v_fst_1851_ = lean_ctor_get(v_pos_1847_, 0);
v_snd_1852_ = lean_ctor_get(v_pos_1847_, 1);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_pos_1847_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1854_ = v_pos_1847_;
v_isShared_1855_ = v_isSharedCheck_1864_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_snd_1852_);
lean_inc(v_fst_1851_);
lean_dec(v_pos_1847_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1864_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1856_; lean_object* v___x_1858_; 
v___x_1856_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1851_, v_snd_1852_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 1, v___x_1856_);
v___x_1858_ = v___x_1854_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_fst_1851_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1859_, 0, v___x_1805_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 1, v___x_1859_);
lean_ctor_set(v___x_1849_, 0, v___x_1858_);
v___x_1861_ = v___x_1849_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1858_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
}
else
{
lean_object* v_pos_1867_; lean_object* v_err_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_pos_1867_ = lean_ctor_get(v___x_1846_, 0);
v_err_1868_ = lean_ctor_get(v___x_1846_, 1);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1846_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_err_1868_);
lean_inc(v_pos_1867_);
lean_dec(v___x_1846_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_pos_1867_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_err_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__4));
v___x_1877_ = l_Std_Internal_Parsec_String_pstring(v___x_1876_, v_a_1756_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_pos_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1896_; 
v_pos_1878_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; 
v_unused_1897_ = lean_ctor_get(v___x_1877_, 1);
lean_dec(v_unused_1897_);
v___x_1880_ = v___x_1877_;
v_isShared_1881_ = v_isSharedCheck_1896_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_pos_1878_);
lean_dec(v___x_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1896_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v_fst_1882_; lean_object* v_snd_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1895_; 
v_fst_1882_ = lean_ctor_get(v_pos_1878_, 0);
v_snd_1883_ = lean_ctor_get(v_pos_1878_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_pos_1878_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1885_ = v_pos_1878_;
v_isShared_1886_ = v_isSharedCheck_1895_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_snd_1883_);
lean_inc(v_fst_1882_);
lean_dec(v_pos_1878_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1895_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1887_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1882_, v_snd_1883_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v___x_1887_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_fst_1882_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1890_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1890_, 0, v___x_1801_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 1, v___x_1890_);
lean_ctor_set(v___x_1880_, 0, v___x_1889_);
v___x_1892_ = v___x_1880_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
else
{
lean_object* v_pos_1898_; lean_object* v_err_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
v_pos_1898_ = lean_ctor_get(v___x_1877_, 0);
v_err_1899_ = lean_ctor_get(v___x_1877_, 1);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1877_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_err_1899_);
lean_inc(v_pos_1898_);
lean_dec(v___x_1877_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_pos_1898_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_err_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
else
{
lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1945_; 
lean_inc(v_snd_1792_);
lean_inc(v_fst_1791_);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_a_1756_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; lean_object* v_unused_1947_; 
v_unused_1946_ = lean_ctor_get(v_a_1756_, 1);
lean_dec(v_unused_1946_);
v_unused_1947_ = lean_ctor_get(v_a_1756_, 0);
lean_dec(v_unused_1947_);
v___x_1908_ = v_a_1756_;
v_isShared_1909_ = v_isSharedCheck_1945_;
goto v_resetjp_1907_;
}
else
{
lean_dec(v_a_1756_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1945_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1910_ = lean_string_utf8_next_fast(v_fst_1791_, v_snd_1792_);
lean_dec(v_snd_1792_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 1, v___x_1910_);
v___x_1912_ = v___x_1908_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_fst_1791_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = ((lean_object*)(l_Lean_Json_Parser_finishSurrogatePair___closed__0));
v___x_1914_ = l_Lean_Json_Parser_strCore(v___x_1913_, v___x_1912_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_pos_1915_; lean_object* v_res_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1934_; 
v_pos_1915_ = lean_ctor_get(v___x_1914_, 0);
v_res_1916_ = lean_ctor_get(v___x_1914_, 1);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1918_ = v___x_1914_;
v_isShared_1919_ = v_isSharedCheck_1934_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_res_1916_);
lean_inc(v_pos_1915_);
lean_dec(v___x_1914_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1934_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v_fst_1920_; lean_object* v_snd_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1933_; 
v_fst_1920_ = lean_ctor_get(v_pos_1915_, 0);
v_snd_1921_ = lean_ctor_get(v_pos_1915_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_pos_1915_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1923_ = v_pos_1915_;
v_isShared_1924_ = v_isSharedCheck_1933_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_snd_1921_);
lean_inc(v_fst_1920_);
lean_dec(v_pos_1915_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1933_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1920_, v_snd_1921_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 1, v___x_1925_);
v___x_1927_ = v___x_1923_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_fst_1920_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1928_, 0, v_res_1916_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v___x_1928_);
lean_ctor_set(v___x_1918_, 0, v___x_1927_);
v___x_1930_ = v___x_1918_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1927_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
else
{
lean_object* v_pos_1935_; lean_object* v_err_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
v_pos_1935_ = lean_ctor_get(v___x_1914_, 0);
v_err_1936_ = lean_ctor_get(v___x_1914_, 1);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1914_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_err_1936_);
lean_inc(v_pos_1935_);
lean_dec(v___x_1914_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_pos_1935_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_err_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1990_; 
lean_inc(v_snd_1792_);
lean_inc(v_fst_1791_);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_a_1756_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; lean_object* v_unused_1992_; 
v_unused_1991_ = lean_ctor_get(v_a_1756_, 1);
lean_dec(v_unused_1991_);
v_unused_1992_ = lean_ctor_get(v_a_1756_, 0);
lean_dec(v_unused_1992_);
v___x_1949_ = v_a_1756_;
v_isShared_1950_ = v_isSharedCheck_1990_;
goto v_resetjp_1948_;
}
else
{
lean_dec(v_a_1756_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1990_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1954_; 
v___x_1951_ = lean_string_utf8_next_fast(v_fst_1791_, v_snd_1792_);
lean_dec(v_snd_1792_);
v___x_1952_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1791_, v___x_1951_);
lean_inc(v___x_1952_);
lean_inc(v_fst_1791_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 1, v___x_1952_);
v___x_1954_ = v___x_1949_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_fst_1791_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
uint8_t v___y_1956_; uint8_t v_decide_1988_; 
v_decide_1988_ = lean_nat_dec_eq(v___x_1952_, v___x_1793_);
if (v_decide_1988_ == 0)
{
v___y_1956_ = v___x_1799_;
goto v___jp_1955_;
}
else
{
v___y_1956_ = v___x_1797_;
goto v___jp_1955_;
}
v___jp_1955_:
{
if (v___y_1956_ == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_dec(v___x_1952_);
lean_dec(v_fst_1791_);
v___x_1957_ = lean_box(0);
v___x_1958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1954_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
return v___x_1958_;
}
else
{
uint32_t v___x_1959_; uint32_t v___x_1960_; uint8_t v___x_1961_; 
v___x_1959_ = lean_string_utf8_get_fast(v_fst_1791_, v___x_1952_);
v___x_1960_ = 125;
v___x_1961_ = lean_uint32_dec_eq(v___x_1959_, v___x_1960_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_dec(v___x_1952_);
lean_dec(v_fst_1791_);
v___x_1962_ = lean_box(1);
v___x_1963_ = l_Lean_Json_Parser_objectCore(v___x_1962_, v___x_1954_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_pos_1964_; lean_object* v_res_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1973_; 
v_pos_1964_ = lean_ctor_get(v___x_1963_, 0);
v_res_1965_ = lean_ctor_get(v___x_1963_, 1);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1967_ = v___x_1963_;
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_res_1965_);
lean_inc(v_pos_1964_);
lean_dec(v___x_1963_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1969_, 0, v_res_1965_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 1, v___x_1969_);
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_pos_1964_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
else
{
lean_object* v_pos_1974_; lean_object* v_err_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
v_pos_1974_ = lean_ctor_get(v___x_1963_, 0);
v_err_1975_ = lean_ctor_get(v___x_1963_, 1);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1963_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_err_1975_);
lean_inc(v_pos_1974_);
lean_dec(v___x_1963_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_pos_1974_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_err_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
lean_dec_ref(v___x_1954_);
v___x_1983_ = lean_string_utf8_next_fast(v_fst_1791_, v___x_1952_);
lean_dec(v___x_1952_);
v___x_1984_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1791_, v___x_1983_);
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v_fst_1791_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__5));
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1985_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
return v___x_1987_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2035_; 
lean_inc(v_snd_1792_);
lean_inc(v_fst_1791_);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_a_1756_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; lean_object* v_unused_2037_; 
v_unused_2036_ = lean_ctor_get(v_a_1756_, 1);
lean_dec(v_unused_2036_);
v_unused_2037_ = lean_ctor_get(v_a_1756_, 0);
lean_dec(v_unused_2037_);
v___x_1994_ = v_a_1756_;
v_isShared_1995_ = v_isSharedCheck_2035_;
goto v_resetjp_1993_;
}
else
{
lean_dec(v_a_1756_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2035_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1996_ = lean_string_utf8_next_fast(v_fst_1791_, v_snd_1792_);
lean_dec(v_snd_1792_);
v___x_1997_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1791_, v___x_1996_);
lean_inc(v___x_1997_);
lean_inc(v_fst_1791_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 1, v___x_1997_);
v___x_1999_ = v___x_1994_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_fst_1791_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2034_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
uint8_t v_decide_2003_; 
v_decide_2003_ = lean_nat_dec_eq(v___x_1997_, v___x_1793_);
if (v_decide_2003_ == 0)
{
if (v___x_1797_ == 0)
{
lean_dec(v___x_1997_);
lean_dec(v_fst_1791_);
goto v___jp_2000_;
}
else
{
uint32_t v___x_2004_; uint32_t v___x_2005_; uint8_t v___x_2006_; 
v___x_2004_ = lean_string_utf8_get_fast(v_fst_1791_, v___x_1997_);
v___x_2005_ = 93;
v___x_2006_ = lean_uint32_dec_eq(v___x_2004_, v___x_2005_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_dec(v___x_1997_);
lean_dec(v_fst_1791_);
v___x_2007_ = lean_unsigned_to_nat(4u);
v___x_2008_ = lean_mk_empty_array_with_capacity(v___x_2007_);
v___x_2009_ = l_Lean_Json_Parser_arrayCore(v___x_2008_, v___x_1999_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_pos_2010_; lean_object* v_res_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2019_; 
v_pos_2010_ = lean_ctor_get(v___x_2009_, 0);
v_res_2011_ = lean_ctor_get(v___x_2009_, 1);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2013_ = v___x_2009_;
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_res_2011_);
lean_inc(v_pos_2010_);
lean_dec(v___x_2009_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2015_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2015_, 0, v_res_2011_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 1, v___x_2015_);
v___x_2017_ = v___x_2013_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_pos_2010_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
else
{
lean_object* v_pos_2020_; lean_object* v_err_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
v_pos_2020_ = lean_ctor_get(v___x_2009_, 0);
v_err_2021_ = lean_ctor_get(v___x_2009_, 1);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2009_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_err_2021_);
lean_inc(v_pos_2020_);
lean_dec(v___x_2009_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_pos_2020_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_err_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_dec_ref(v___x_1999_);
v___x_2029_ = lean_string_utf8_next_fast(v_fst_1791_, v___x_1997_);
lean_dec(v___x_1997_);
v___x_2030_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1791_, v___x_2029_);
v___x_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2031_, 0, v_fst_1791_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
v___x_2032_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__7));
v___x_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2031_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
return v___x_2033_;
}
}
}
else
{
lean_dec(v___x_1997_);
lean_dec(v_fst_1791_);
goto v___jp_2000_;
}
v___jp_2000_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = lean_box(0);
v___x_2002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_1999_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
return v___x_2002_;
}
}
}
}
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = lean_box(0);
v___x_2039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2039_, 0, v_a_1756_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
return v___x_2039_;
}
v___jp_1757_:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Json_Parser_num(v_a_1756_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_pos_1759_; lean_object* v_res_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1778_; 
v_pos_1759_ = lean_ctor_get(v___x_1758_, 0);
v_res_1760_ = lean_ctor_get(v___x_1758_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1762_ = v___x_1758_;
v_isShared_1763_ = v_isSharedCheck_1778_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_res_1760_);
lean_inc(v_pos_1759_);
lean_dec(v___x_1758_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1778_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v_fst_1764_; lean_object* v_snd_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1777_; 
v_fst_1764_ = lean_ctor_get(v_pos_1759_, 0);
v_snd_1765_ = lean_ctor_get(v_pos_1759_, 1);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_pos_1759_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1767_ = v_pos_1759_;
v_isShared_1768_ = v_isSharedCheck_1777_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_snd_1765_);
lean_inc(v_fst_1764_);
lean_dec(v_pos_1759_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1777_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1769_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_1764_, v_snd_1765_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 1, v___x_1769_);
v___x_1771_ = v___x_1767_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_fst_1764_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1772_, 0, v_res_1760_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 1, v___x_1772_);
lean_ctor_set(v___x_1762_, 0, v___x_1771_);
v___x_1774_ = v___x_1762_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
else
{
lean_object* v_pos_1779_; lean_object* v_err_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
v_pos_1779_ = lean_ctor_get(v___x_1758_, 0);
v_err_1780_ = lean_ctor_get(v___x_1758_, 1);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1758_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_err_1780_);
lean_inc(v_pos_1779_);
lean_dec(v___x_1758_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_pos_1779_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_err_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
v___jp_1788_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = ((lean_object*)(l_Lean_Json_Parser_anyCore___closed__1));
v___x_1790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1790_, 0, v_a_1756_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
return v___x_1790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore(lean_object* v_acc_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_Json_Parser_anyCore(v_a_2041_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_pos_2043_; lean_object* v_res_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2088_; 
v_pos_2043_ = lean_ctor_get(v___x_2042_, 0);
v_res_2044_ = lean_ctor_get(v___x_2042_, 1);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2046_ = v___x_2042_;
v_isShared_2047_ = v_isSharedCheck_2088_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_res_2044_);
lean_inc(v_pos_2043_);
lean_dec(v___x_2042_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2088_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v_fst_2048_; lean_object* v_snd_2049_; lean_object* v___x_2050_; uint8_t v_decide_2051_; 
v_fst_2048_ = lean_ctor_get(v_pos_2043_, 0);
v_snd_2049_ = lean_ctor_get(v_pos_2043_, 1);
v___x_2050_ = lean_string_utf8_byte_size(v_fst_2048_);
v_decide_2051_ = lean_nat_dec_eq(v_snd_2049_, v___x_2050_);
if (v_decide_2051_ == 0)
{
lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2081_; 
lean_inc(v_snd_2049_);
lean_inc(v_fst_2048_);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_pos_2043_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; lean_object* v_unused_2083_; 
v_unused_2082_ = lean_ctor_get(v_pos_2043_, 1);
lean_dec(v_unused_2082_);
v_unused_2083_ = lean_ctor_get(v_pos_2043_, 0);
lean_dec(v_unused_2083_);
v___x_2053_ = v_pos_2043_;
v_isShared_2054_ = v_isSharedCheck_2081_;
goto v_resetjp_2052_;
}
else
{
lean_dec(v_pos_2043_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2081_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; uint32_t v___x_2056_; lean_object* v___x_2057_; uint32_t v___x_2058_; uint8_t v___x_2059_; 
v___x_2055_ = lean_array_push(v_acc_2040_, v_res_2044_);
v___x_2056_ = lean_string_utf8_get_fast(v_fst_2048_, v_snd_2049_);
v___x_2057_ = lean_string_utf8_next_fast(v_fst_2048_, v_snd_2049_);
lean_dec(v_snd_2049_);
v___x_2058_ = 93;
v___x_2059_ = lean_uint32_dec_eq(v___x_2056_, v___x_2058_);
if (v___x_2059_ == 0)
{
uint32_t v___x_2060_; uint8_t v___x_2061_; 
v___x_2060_ = 44;
v___x_2061_ = lean_uint32_dec_eq(v___x_2056_, v___x_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2063_; 
lean_dec_ref(v___x_2055_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v___x_2057_);
v___x_2063_ = v___x_2053_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_fst_2048_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v___x_2057_);
v___x_2063_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2064_ = ((lean_object*)(l_Lean_Json_Parser_arrayCore___closed__1));
if (v_isShared_2047_ == 0)
{
lean_ctor_set_tag(v___x_2046_, 1);
lean_ctor_set(v___x_2046_, 1, v___x_2064_);
lean_ctor_set(v___x_2046_, 0, v___x_2063_);
v___x_2066_ = v___x_2046_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
else
{
lean_object* v___x_2069_; lean_object* v___x_2071_; 
lean_del_object(v___x_2046_);
v___x_2069_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2048_, v___x_2057_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v___x_2069_);
v___x_2071_ = v___x_2053_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_fst_2048_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
v_acc_2040_ = v___x_2055_;
v_a_2041_ = v___x_2071_;
goto _start;
}
}
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
v___x_2074_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2048_, v___x_2057_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v___x_2074_);
v___x_2076_ = v___x_2053_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_fst_2048_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2078_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 1, v___x_2055_);
lean_ctor_set(v___x_2046_, 0, v___x_2076_);
v___x_2078_ = v___x_2046_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2055_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
lean_dec(v_res_2044_);
lean_dec_ref(v_acc_2040_);
v___x_2084_ = lean_box(0);
if (v_isShared_2047_ == 0)
{
lean_ctor_set_tag(v___x_2046_, 1);
lean_ctor_set(v___x_2046_, 1, v___x_2084_);
v___x_2086_ = v___x_2046_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_pos_2043_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_pos_2089_; lean_object* v_err_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec_ref(v_acc_2040_);
v_pos_2089_ = lean_ctor_get(v___x_2042_, 0);
v_err_2090_ = lean_ctor_get(v___x_2042_, 1);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2042_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_err_2090_);
lean_inc(v_pos_2089_);
lean_dec(v___x_2042_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_pos_2089_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_err_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2(lean_object* v_00_u03b2_2098_, lean_object* v_msg_2099_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2_spec__2___redArg(v_msg_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2(lean_object* v_00_u03b2_2101_, lean_object* v_k_2102_, lean_object* v_v_2103_, lean_object* v_t_2104_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_Parser_objectCore_spec__2___redArg(v_k_2102_, v_v_2103_, v_t_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_any(lean_object* v_a_2109_){
_start:
{
lean_object* v_fst_2110_; lean_object* v_snd_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2135_; 
v_fst_2110_ = lean_ctor_get(v_a_2109_, 0);
v_snd_2111_ = lean_ctor_get(v_a_2109_, 1);
v_isSharedCheck_2135_ = !lean_is_exclusive(v_a_2109_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2113_ = v_a_2109_;
v_isShared_2114_ = v_isSharedCheck_2135_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_snd_2111_);
lean_inc(v_fst_2110_);
lean_dec(v_a_2109_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2135_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2115_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_2110_, v_snd_2111_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 1, v___x_2115_);
v___x_2117_ = v___x_2113_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_fst_2110_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_Json_Parser_anyCore(v___x_2117_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_pos_2119_; lean_object* v_fst_2120_; lean_object* v_snd_2121_; lean_object* v___x_2122_; uint8_t v_decide_2123_; 
v_pos_2119_ = lean_ctor_get(v___x_2118_, 0);
v_fst_2120_ = lean_ctor_get(v_pos_2119_, 0);
v_snd_2121_ = lean_ctor_get(v_pos_2119_, 1);
v___x_2122_ = lean_string_utf8_byte_size(v_fst_2120_);
v_decide_2123_ = lean_nat_dec_eq(v_snd_2121_, v___x_2122_);
if (v_decide_2123_ == 0)
{
lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2131_; 
lean_inc(v_pos_2119_);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2131_ == 0)
{
lean_object* v_unused_2132_; lean_object* v_unused_2133_; 
v_unused_2132_ = lean_ctor_get(v___x_2118_, 1);
lean_dec(v_unused_2132_);
v_unused_2133_ = lean_ctor_get(v___x_2118_, 0);
lean_dec(v_unused_2133_);
v___x_2125_ = v___x_2118_;
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
else
{
lean_dec(v___x_2118_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = ((lean_object*)(l_Lean_Json_Parser_any___closed__1));
if (v_isShared_2126_ == 0)
{
lean_ctor_set_tag(v___x_2125_, 1);
lean_ctor_set(v___x_2125_, 1, v___x_2127_);
v___x_2129_ = v___x_2125_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_pos_2119_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
else
{
return v___x_2118_;
}
}
else
{
return v___x_2118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parse(lean_object* v_s_2136_){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
v___x_2138_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_2137_, v_s_2136_);
return v___x_2138_;
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
