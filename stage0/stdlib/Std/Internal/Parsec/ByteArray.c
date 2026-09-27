// Lean compiler output
// Module: Std.Internal.Parsec.ByteArray
// Imports: public import Std.Internal.Parsec.Basic public import Init.Data.String.Basic public import Std.Data.ByteSlice import Init.Omega
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
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* l_ByteArray_toByteSlice(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_ByteArray_Iterator_remainingBytes(lean_object*);
lean_object* l_ByteArray_mkIterator(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__1(lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__4(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__0_value;
static const lean_closure_object l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__1_value;
static const lean_closure_object l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__2 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__2_value;
static const lean_closure_object l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__3 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__3_value;
static const lean_closure_object l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__4, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__4 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__4_value;
static const lean_closure_object l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__5 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__5_value;
static const lean_ctor_object l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__0_value),((lean_object*)&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__1_value),((lean_object*)&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__2_value),((lean_object*)&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__3_value),((lean_object*)&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__4_value),((lean_object*)&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__5_value)}};
static const lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__6 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___closed__6_value;
static const lean_string_object l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "offset "};
static const lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__0_value;
static const lean_string_object l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__1_value;
static const lean_string_object l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "unexpected end of input"};
static const lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__2 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_ByteArray_pbyte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expected: '"};
static const lean_object* l_Std_Internal_Parsec_ByteArray_pbyte___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_pbyte___closed__0_value;
static const lean_string_object l_Std_Internal_Parsec_ByteArray_pbyte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Std_Internal_Parsec_ByteArray_pbyte___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_pbyte___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pbyte(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pbyte___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByte(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByte___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected byte "};
static const lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__0 = (const lean_object*)&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__0_value;
static const lean_string_object l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", got "};
static const lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__1 = (const lean_object*)&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pstring(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipString___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pByteChar(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pByteChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByteChar(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByteChar___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_ByteArray_digit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "digit expected"};
static const lean_object* l_Std_Internal_Parsec_ByteArray_digit___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_digit___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_ByteArray_digit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_ByteArray_digit___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_ByteArray_digit___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_digit___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digit(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digits(lean_object*);
static const lean_string_object l_Std_Internal_Parsec_ByteArray_hexDigit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "hex digit expected"};
static const lean_object* l_Std_Internal_Parsec_ByteArray_hexDigit___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_hexDigit(lean_object*);
static const lean_string_object l_Std_Internal_Parsec_ByteArray_octDigit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "octal digit expected"};
static const lean_object* l_Std_Internal_Parsec_ByteArray_octDigit___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_octDigit___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_ByteArray_octDigit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_ByteArray_octDigit___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_ByteArray_octDigit___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_octDigit___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_octDigit(lean_object*);
static const lean_string_object l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ASCII letter expected"};
static const lean_object* l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_asciiLetter(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_ws(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntil(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected at least one char"};
static const lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileAtMost(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileAtMost___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhileUpTo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntilUpTo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0(lean_object* v_it_1_){
_start:
{
lean_object* v_idx_2_; 
v_idx_2_ = lean_ctor_get(v_it_1_, 1);
lean_inc(v_idx_2_);
return v_idx_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0___boxed(lean_object* v_it_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0(v_it_3_);
lean_dec_ref(v_it_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__1(lean_object* v_it_5_){
_start:
{
lean_object* v_array_6_; lean_object* v_idx_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_16_; 
v_array_6_ = lean_ctor_get(v_it_5_, 0);
v_idx_7_ = lean_ctor_get(v_it_5_, 1);
v_isSharedCheck_16_ = !lean_is_exclusive(v_it_5_);
if (v_isSharedCheck_16_ == 0)
{
v___x_9_ = v_it_5_;
v_isShared_10_ = v_isSharedCheck_16_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_idx_7_);
lean_inc(v_array_6_);
lean_dec(v_it_5_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_16_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_14_; 
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = lean_nat_add(v_idx_7_, v___x_11_);
lean_dec(v_idx_7_);
if (v_isShared_10_ == 0)
{
lean_ctor_set(v___x_9_, 1, v___x_12_);
v___x_14_ = v___x_9_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_array_6_);
lean_ctor_set(v_reuseFailAlloc_15_, 1, v___x_12_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2(lean_object* v_it_17_){
_start:
{
lean_object* v_array_18_; lean_object* v_idx_19_; lean_object* v___x_20_; uint8_t v___x_21_; 
v_array_18_ = lean_ctor_get(v_it_17_, 0);
v_idx_19_ = lean_ctor_get(v_it_17_, 1);
v___x_20_ = lean_byte_array_size(v_array_18_);
v___x_21_ = lean_nat_dec_lt(v_idx_19_, v___x_20_);
if (v___x_21_ == 0)
{
uint8_t v___x_22_; 
v___x_22_ = 0;
return v___x_22_;
}
else
{
uint8_t v___x_23_; 
v___x_23_ = lean_byte_array_fget(v_array_18_, v_idx_19_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___boxed(lean_object* v_it_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2(v_it_24_);
lean_dec_ref(v_it_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3(lean_object* v_it_27_){
_start:
{
lean_object* v_array_28_; lean_object* v_idx_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v_array_28_ = lean_ctor_get(v_it_27_, 0);
v_idx_29_ = lean_ctor_get(v_it_27_, 1);
v___x_30_ = lean_byte_array_size(v_array_28_);
v___x_31_ = lean_nat_dec_lt(v_idx_29_, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3___boxed(lean_object* v_it_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3(v_it_32_);
lean_dec_ref(v_it_32_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__4(lean_object* v_it_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_array_37_; lean_object* v_idx_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_47_; 
v_array_37_ = lean_ctor_get(v_it_35_, 0);
v_idx_38_ = lean_ctor_get(v_it_35_, 1);
v_isSharedCheck_47_ = !lean_is_exclusive(v_it_35_);
if (v_isSharedCheck_47_ == 0)
{
v___x_40_ = v_it_35_;
v_isShared_41_ = v_isSharedCheck_47_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_idx_38_);
lean_inc(v_array_37_);
lean_dec(v_it_35_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_47_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_45_; 
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_add(v_idx_38_, v___x_42_);
lean_dec(v_idx_38_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 1, v___x_43_);
v___x_45_ = v___x_40_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_array_37_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v___x_43_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5(lean_object* v_it_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_array_50_; lean_object* v_idx_51_; uint8_t v___x_52_; 
v_array_50_ = lean_ctor_get(v_it_48_, 0);
v_idx_51_ = lean_ctor_get(v_it_48_, 1);
v___x_52_ = lean_byte_array_fget(v_array_50_, v_idx_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5___boxed(lean_object* v_it_53_, lean_object* v___y_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5(v_it_53_, v___y_54_);
lean_dec_ref(v_it_53_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object* v_p_74_, lean_object* v_arr_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = l_ByteArray_mkIterator(v_arr_75_);
v___x_77_ = lean_apply_1(v_p_74_, v___x_76_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_res_78_; lean_object* v___x_79_; 
v_res_78_ = lean_ctor_get(v___x_77_, 1);
lean_inc(v_res_78_);
lean_dec_ref_known(v___x_77_, 2);
v___x_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_79_, 0, v_res_78_);
return v___x_79_;
}
else
{
lean_object* v_pos_80_; lean_object* v_err_81_; lean_object* v_idx_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___y_93_; 
v_pos_80_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_pos_80_);
v_err_81_ = lean_ctor_get(v___x_77_, 1);
lean_inc(v_err_81_);
lean_dec_ref_known(v___x_77_, 2);
v_idx_82_ = lean_ctor_get(v_pos_80_, 1);
lean_inc(v_idx_82_);
lean_dec(v_pos_80_);
v___x_83_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__0));
v___x_84_ = l_Nat_reprFast(v_idx_82_);
v___x_85_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
v___x_86_ = l_Std_Format_defWidth;
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = l_Std_Format_pretty(v___x_85_, v___x_86_, v___x_87_, v___x_87_);
v___x_89_ = lean_string_append(v___x_83_, v___x_88_);
lean_dec_ref(v___x_88_);
v___x_90_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__1));
v___x_91_ = lean_string_append(v___x_89_, v___x_90_);
if (lean_obj_tag(v_err_81_) == 0)
{
lean_object* v___x_96_; 
v___x_96_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__2));
v___y_93_ = v___x_96_;
goto v___jp_92_;
}
else
{
lean_object* v_s_97_; 
v_s_97_ = lean_ctor_get(v_err_81_, 0);
lean_inc_ref(v_s_97_);
lean_dec_ref_known(v_err_81_, 1);
v___y_93_ = v_s_97_;
goto v___jp_92_;
}
v___jp_92_:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_string_append(v___x_91_, v___y_93_);
lean_dec_ref(v___y_93_);
v___x_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run(lean_object* v_00_u03b1_98_, lean_object* v_p_99_, lean_object* v_arr_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v_p_99_, v_arr_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pbyte(uint8_t v_b_104_, lean_object* v_it_105_){
_start:
{
lean_object* v_array_106_; lean_object* v_idx_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v_array_106_ = lean_ctor_get(v_it_105_, 0);
v_idx_107_ = lean_ctor_get(v_it_105_, 1);
v___x_108_ = lean_byte_array_size(v_array_106_);
v___x_109_ = lean_nat_dec_lt(v_idx_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_box(0);
v___x_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_111_, 0, v_it_105_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
return v___x_111_;
}
else
{
uint8_t v_got_112_; uint8_t v___x_113_; 
v_got_112_ = lean_byte_array_fget(v_array_106_, v_idx_107_);
v___x_113_ = lean_uint8_dec_eq(v_got_112_, v_b_104_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_114_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0));
v___x_115_ = lean_uint8_to_nat(v_b_104_);
v___x_116_ = l_Nat_reprFast(v___x_115_);
v___x_117_ = lean_string_append(v___x_114_, v___x_116_);
lean_dec_ref(v___x_116_);
v___x_118_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1));
v___x_119_ = lean_string_append(v___x_117_, v___x_118_);
v___x_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
v___x_121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_121_, 0, v_it_105_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
return v___x_121_;
}
else
{
lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_132_; 
lean_inc(v_idx_107_);
lean_inc_ref(v_array_106_);
v_isSharedCheck_132_ = !lean_is_exclusive(v_it_105_);
if (v_isSharedCheck_132_ == 0)
{
lean_object* v_unused_133_; lean_object* v_unused_134_; 
v_unused_133_ = lean_ctor_get(v_it_105_, 1);
lean_dec(v_unused_133_);
v_unused_134_ = lean_ctor_get(v_it_105_, 0);
lean_dec(v_unused_134_);
v___x_123_ = v_it_105_;
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
else
{
lean_dec(v_it_105_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_125_ = lean_unsigned_to_nat(1u);
v___x_126_ = lean_nat_add(v_idx_107_, v___x_125_);
lean_dec(v_idx_107_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v___x_126_);
v___x_128_ = v___x_123_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_array_106_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v___x_126_);
v___x_128_ = v_reuseFailAlloc_131_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_box(v_got_112_);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_128_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
return v___x_130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pbyte___boxed(lean_object* v_b_135_, lean_object* v_it_136_){
_start:
{
uint8_t v_b_boxed_137_; lean_object* v_res_138_; 
v_b_boxed_137_ = lean_unbox(v_b_135_);
v_res_138_ = l_Std_Internal_Parsec_ByteArray_pbyte(v_b_boxed_137_, v_it_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByte(uint8_t v_b_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_array_141_; lean_object* v_idx_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v_array_141_ = lean_ctor_get(v_a_140_, 0);
v_idx_142_ = lean_ctor_get(v_a_140_, 1);
v___x_143_ = lean_byte_array_size(v_array_141_);
v___x_144_ = lean_nat_dec_lt(v_idx_142_, v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_box(0);
v___x_146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_146_, 0, v_a_140_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
return v___x_146_;
}
else
{
uint8_t v_got_147_; uint8_t v___x_148_; 
v_got_147_ = lean_byte_array_fget(v_array_141_, v_idx_142_);
v___x_148_ = lean_uint8_dec_eq(v_got_147_, v_b_139_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_149_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0));
v___x_150_ = lean_uint8_to_nat(v_b_139_);
v___x_151_ = l_Nat_reprFast(v___x_150_);
v___x_152_ = lean_string_append(v___x_149_, v___x_151_);
lean_dec_ref(v___x_151_);
v___x_153_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1));
v___x_154_ = lean_string_append(v___x_152_, v___x_153_);
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
v___x_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_156_, 0, v_a_140_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
return v___x_156_;
}
else
{
lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_167_; 
lean_inc(v_idx_142_);
lean_inc_ref(v_array_141_);
v_isSharedCheck_167_ = !lean_is_exclusive(v_a_140_);
if (v_isSharedCheck_167_ == 0)
{
lean_object* v_unused_168_; lean_object* v_unused_169_; 
v_unused_168_ = lean_ctor_get(v_a_140_, 1);
lean_dec(v_unused_168_);
v_unused_169_ = lean_ctor_get(v_a_140_, 0);
lean_dec(v_unused_169_);
v___x_158_ = v_a_140_;
v_isShared_159_ = v_isSharedCheck_167_;
goto v_resetjp_157_;
}
else
{
lean_dec(v_a_140_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_167_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_160_ = lean_unsigned_to_nat(1u);
v___x_161_ = lean_nat_add(v_idx_142_, v___x_160_);
lean_dec(v_idx_142_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v___x_161_);
v___x_163_ = v___x_158_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_array_141_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v___x_161_);
v___x_163_ = v_reuseFailAlloc_166_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_box(0);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
return v___x_165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByte___boxed(lean_object* v_b_170_, lean_object* v_a_171_){
_start:
{
uint8_t v_b_boxed_172_; lean_object* v_res_173_; 
v_b_boxed_172_ = lean_unbox(v_b_170_);
v_res_173_ = l_Std_Internal_Parsec_ByteArray_skipByte(v_b_boxed_172_, v_a_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go(lean_object* v_arr_176_, lean_object* v_idx_177_, lean_object* v_it_178_){
_start:
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_byte_array_size(v_arr_176_);
v___x_180_ = lean_nat_dec_lt(v_idx_177_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_idx_177_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v_it_178_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
return v___x_182_;
}
else
{
lean_object* v_array_183_; lean_object* v_idx_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_array_183_ = lean_ctor_get(v_it_178_, 0);
v_idx_184_ = lean_ctor_get(v_it_178_, 1);
v___x_185_ = lean_byte_array_size(v_array_183_);
v___x_186_ = lean_nat_dec_lt(v_idx_184_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec(v_idx_177_);
v___x_187_ = lean_box(0);
v___x_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_188_, 0, v_it_178_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
return v___x_188_;
}
else
{
uint8_t v_got_189_; uint8_t v_want_190_; uint8_t v___x_191_; 
v_got_189_ = lean_byte_array_fget(v_array_183_, v_idx_184_);
v_want_190_ = lean_byte_array_fget(v_arr_176_, v_idx_177_);
v___x_191_ = lean_uint8_dec_eq(v_got_189_, v_want_190_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v_idx_177_);
v___x_192_ = ((lean_object*)(l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__0));
v___x_193_ = lean_uint8_to_nat(v_want_190_);
v___x_194_ = l_Nat_reprFast(v___x_193_);
v___x_195_ = lean_string_append(v___x_192_, v___x_194_);
lean_dec_ref(v___x_194_);
v___x_196_ = ((lean_object*)(l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__1));
v___x_197_ = lean_string_append(v___x_195_, v___x_196_);
v___x_198_ = lean_uint8_to_nat(v_got_189_);
v___x_199_ = l_Nat_reprFast(v___x_198_);
v___x_200_ = lean_string_append(v___x_197_, v___x_199_);
lean_dec_ref(v___x_199_);
v___x_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
v___x_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_202_, 0, v_it_178_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
return v___x_202_;
}
else
{
lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_213_; 
lean_inc(v_idx_184_);
lean_inc_ref(v_array_183_);
v_isSharedCheck_213_ = !lean_is_exclusive(v_it_178_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; lean_object* v_unused_215_; 
v_unused_214_ = lean_ctor_get(v_it_178_, 1);
lean_dec(v_unused_214_);
v_unused_215_ = lean_ctor_get(v_it_178_, 0);
lean_dec(v_unused_215_);
v___x_204_ = v_it_178_;
v_isShared_205_ = v_isSharedCheck_213_;
goto v_resetjp_203_;
}
else
{
lean_dec(v_it_178_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_213_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_206_ = lean_unsigned_to_nat(1u);
v___x_207_ = lean_nat_add(v_idx_177_, v___x_206_);
lean_dec(v_idx_177_);
v___x_208_ = lean_nat_add(v_idx_184_, v___x_206_);
lean_dec(v_idx_184_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_208_);
v___x_210_ = v___x_204_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_array_183_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_208_);
v___x_210_ = v_reuseFailAlloc_212_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
v_idx_177_ = v___x_207_;
v_it_178_ = v___x_210_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___boxed(lean_object* v_arr_216_, lean_object* v_idx_217_, lean_object* v_it_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go(v_arr_216_, v_idx_217_, v_it_218_);
lean_dec_ref(v_arr_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object* v_arr_220_, lean_object* v_it_221_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go(v_arr_220_, v___x_222_, v_it_221_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes___boxed(lean_object* v_arr_224_, lean_object* v_it_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_arr_224_, v_it_225_);
lean_dec_ref(v_arr_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pstring(lean_object* v_s_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_utf8_229_; lean_object* v___x_230_; 
v_utf8_229_ = lean_string_to_utf8(v_s_227_);
v___x_230_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_229_, v_a_228_);
lean_dec_ref(v_utf8_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_pos_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
v_pos_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; 
v_unused_239_ = lean_ctor_get(v___x_230_, 1);
lean_dec(v_unused_239_);
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_pos_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v_s_227_);
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_pos_231_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_s_227_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
else
{
lean_object* v_pos_240_; lean_object* v_err_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
lean_dec_ref(v_s_227_);
v_pos_240_ = lean_ctor_get(v___x_230_, 0);
v_err_241_ = lean_ctor_get(v___x_230_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_230_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_err_241_);
lean_inc(v_pos_240_);
lean_dec(v___x_230_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_pos_240_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_err_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipString(lean_object* v_s_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_utf8_251_; lean_object* v___x_252_; 
v_utf8_251_ = lean_string_to_utf8(v_s_249_);
v___x_252_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_251_, v_a_250_);
lean_dec_ref(v_utf8_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_pos_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_261_; 
v_pos_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_261_ == 0)
{
lean_object* v_unused_262_; 
v_unused_262_ = lean_ctor_get(v___x_252_, 1);
lean_dec(v_unused_262_);
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_pos_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_257_ = lean_box(0);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v___x_257_);
v___x_259_ = v___x_255_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_pos_253_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
else
{
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipString___boxed(lean_object* v_s_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_Internal_Parsec_ByteArray_skipString(v_s_263_, v_a_264_);
lean_dec_ref(v_s_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pByteChar(uint32_t v_c_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_array_269_; lean_object* v_idx_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_array_269_ = lean_ctor_get(v_a_268_, 0);
v_idx_270_ = lean_ctor_get(v_a_268_, 1);
v___x_271_ = lean_byte_array_size(v_array_269_);
v___x_272_ = lean_nat_dec_lt(v_idx_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_box(0);
v___x_274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_274_, 0, v_a_268_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
return v___x_274_;
}
else
{
uint8_t v_c_275_; uint8_t v___x_276_; uint8_t v___x_277_; 
v_c_275_ = lean_byte_array_fget(v_array_269_, v_idx_270_);
v___x_276_ = lean_uint32_to_uint8(v_c_267_);
v___x_277_ = lean_uint8_dec_eq(v_c_275_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_278_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0));
v___x_279_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0));
v___x_280_ = lean_string_push(v___x_279_, v_c_267_);
v___x_281_ = lean_string_append(v___x_278_, v___x_280_);
lean_dec_ref(v___x_280_);
v___x_282_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1));
v___x_283_ = lean_string_append(v___x_281_, v___x_282_);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
v___x_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_285_, 0, v_a_268_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
return v___x_285_;
}
else
{
lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_296_; 
lean_inc(v_idx_270_);
lean_inc_ref(v_array_269_);
v_isSharedCheck_296_ = !lean_is_exclusive(v_a_268_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; lean_object* v_unused_298_; 
v_unused_297_ = lean_ctor_get(v_a_268_, 1);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_a_268_, 0);
lean_dec(v_unused_298_);
v___x_287_ = v_a_268_;
v_isShared_288_ = v_isSharedCheck_296_;
goto v_resetjp_286_;
}
else
{
lean_dec(v_a_268_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_296_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_it_x27_292_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_nat_add(v_idx_270_, v___x_289_);
lean_dec(v_idx_270_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v___x_290_);
v_it_x27_292_ = v___x_287_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_array_269_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v___x_290_);
v_it_x27_292_ = v_reuseFailAlloc_295_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_box_uint32(v_c_267_);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v_it_x27_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
return v___x_294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pByteChar___boxed(lean_object* v_c_299_, lean_object* v_a_300_){
_start:
{
uint32_t v_c_boxed_301_; lean_object* v_res_302_; 
v_c_boxed_301_ = lean_unbox_uint32(v_c_299_);
lean_dec(v_c_299_);
v_res_302_ = l_Std_Internal_Parsec_ByteArray_pByteChar(v_c_boxed_301_, v_a_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByteChar(uint32_t v_c_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_array_305_; lean_object* v_idx_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_array_305_ = lean_ctor_get(v_a_304_, 0);
v_idx_306_ = lean_ctor_get(v_a_304_, 1);
v___x_307_ = lean_byte_array_size(v_array_305_);
v___x_308_ = lean_nat_dec_lt(v_idx_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_box(0);
v___x_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_310_, 0, v_a_304_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
return v___x_310_;
}
else
{
uint8_t v___x_311_; uint8_t v_got_312_; uint8_t v___x_313_; 
v___x_311_ = lean_uint32_to_uint8(v_c_303_);
v_got_312_ = lean_byte_array_fget(v_array_305_, v_idx_306_);
v___x_313_ = lean_uint8_dec_eq(v_got_312_, v___x_311_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_314_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0));
v___x_315_ = lean_uint8_to_nat(v___x_311_);
v___x_316_ = l_Nat_reprFast(v___x_315_);
v___x_317_ = lean_string_append(v___x_314_, v___x_316_);
lean_dec_ref(v___x_316_);
v___x_318_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1));
v___x_319_ = lean_string_append(v___x_317_, v___x_318_);
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
v___x_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_321_, 0, v_a_304_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
return v___x_321_;
}
else
{
lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_332_; 
lean_inc(v_idx_306_);
lean_inc_ref(v_array_305_);
v_isSharedCheck_332_ = !lean_is_exclusive(v_a_304_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; lean_object* v_unused_334_; 
v_unused_333_ = lean_ctor_get(v_a_304_, 1);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_a_304_, 0);
lean_dec(v_unused_334_);
v___x_323_ = v_a_304_;
v_isShared_324_ = v_isSharedCheck_332_;
goto v_resetjp_322_;
}
else
{
lean_dec(v_a_304_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_332_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_325_ = lean_unsigned_to_nat(1u);
v___x_326_ = lean_nat_add(v_idx_306_, v___x_325_);
lean_dec(v_idx_306_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v___x_326_);
v___x_328_ = v___x_323_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_array_305_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_326_);
v___x_328_ = v_reuseFailAlloc_331_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_box(0);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
return v___x_330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByteChar___boxed(lean_object* v_c_335_, lean_object* v_a_336_){
_start:
{
uint32_t v_c_boxed_337_; lean_object* v_res_338_; 
v_c_boxed_337_ = lean_unbox_uint32(v_c_335_);
lean_dec(v_c_335_);
v_res_338_ = l_Std_Internal_Parsec_ByteArray_skipByteChar(v_c_boxed_337_, v_a_336_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digit(lean_object* v_a_342_){
_start:
{
lean_object* v_array_343_; lean_object* v_idx_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_array_343_ = lean_ctor_get(v_a_342_, 0);
v_idx_344_ = lean_ctor_get(v_a_342_, 1);
v___x_345_ = lean_byte_array_size(v_array_343_);
v___x_346_ = lean_nat_dec_lt(v_idx_344_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_box(0);
v___x_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_348_, 0, v_a_342_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
return v___x_348_;
}
else
{
uint8_t v_c_349_; uint8_t v___y_351_; uint8_t v___x_368_; uint8_t v___x_369_; 
v_c_349_ = lean_byte_array_fget(v_array_343_, v_idx_344_);
v___x_368_ = 48;
v___x_369_ = lean_uint8_dec_le(v___x_368_, v_c_349_);
if (v___x_369_ == 0)
{
v___y_351_ = v___x_369_;
goto v___jp_350_;
}
else
{
uint8_t v___x_370_; uint8_t v___x_371_; 
v___x_370_ = 57;
v___x_371_ = lean_uint8_dec_le(v_c_349_, v___x_370_);
v___y_351_ = v___x_371_;
goto v___jp_350_;
}
v___jp_350_:
{
if (v___y_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_digit___closed__1));
v___x_353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_353_, 0, v_a_342_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
return v___x_353_;
}
else
{
lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_365_; 
lean_inc(v_idx_344_);
lean_inc_ref(v_array_343_);
v_isSharedCheck_365_ = !lean_is_exclusive(v_a_342_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; lean_object* v_unused_367_; 
v_unused_366_ = lean_ctor_get(v_a_342_, 1);
lean_dec(v_unused_366_);
v_unused_367_ = lean_ctor_get(v_a_342_, 0);
lean_dec(v_unused_367_);
v___x_355_ = v_a_342_;
v_isShared_356_ = v_isSharedCheck_365_;
goto v_resetjp_354_;
}
else
{
lean_dec(v_a_342_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_365_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_it_x27_360_; 
v___x_357_ = lean_unsigned_to_nat(1u);
v___x_358_ = lean_nat_add(v_idx_344_, v___x_357_);
lean_dec(v_idx_344_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 1, v___x_358_);
v_it_x27_360_ = v___x_355_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_array_343_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v___x_358_);
v_it_x27_360_ = v_reuseFailAlloc_364_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
uint32_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = lean_uint8_to_uint32(v_c_349_);
v___x_362_ = lean_box_uint32(v___x_361_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_it_x27_360_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
return v___x_363_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(uint8_t v_b_372_){
_start:
{
uint8_t v___x_373_; uint8_t v___x_374_; lean_object* v___x_375_; 
v___x_373_ = 48;
v___x_374_ = lean_uint8_sub(v_b_372_, v___x_373_);
v___x_375_ = lean_uint8_to_nat(v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat___boxed(lean_object* v_b_376_){
_start:
{
uint8_t v_b_boxed_377_; lean_object* v_res_378_; 
v_b_boxed_377_ = lean_unbox(v_b_376_);
v_res_378_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(v_b_boxed_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object* v_it_379_, lean_object* v_acc_380_){
_start:
{
lean_object* v_array_381_; lean_object* v_idx_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v_array_381_ = lean_ctor_get(v_it_379_, 0);
v_idx_382_ = lean_ctor_get(v_it_379_, 1);
v___x_383_ = lean_byte_array_size(v_array_381_);
v___x_384_ = lean_nat_dec_lt(v_idx_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; 
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_acc_380_);
lean_ctor_set(v___x_385_, 1, v_it_379_);
return v___x_385_;
}
else
{
uint8_t v_candidate_386_; uint8_t v___x_387_; uint8_t v___y_389_; uint8_t v___x_408_; 
v_candidate_386_ = lean_byte_array_fget(v_array_381_, v_idx_382_);
v___x_387_ = 48;
v___x_408_ = lean_uint8_dec_le(v___x_387_, v_candidate_386_);
if (v___x_408_ == 0)
{
v___y_389_ = v___x_408_;
goto v___jp_388_;
}
else
{
uint8_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = 57;
v___x_410_ = lean_uint8_dec_le(v_candidate_386_, v___x_409_);
v___y_389_ = v___x_410_;
goto v___jp_388_;
}
v___jp_388_:
{
if (v___y_389_ == 0)
{
lean_object* v___x_390_; 
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_acc_380_);
lean_ctor_set(v___x_390_, 1, v_it_379_);
return v___x_390_;
}
else
{
lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_405_; 
lean_inc(v_idx_382_);
lean_inc_ref(v_array_381_);
v_isSharedCheck_405_ = !lean_is_exclusive(v_it_379_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; lean_object* v_unused_407_; 
v_unused_406_ = lean_ctor_get(v_it_379_, 1);
lean_dec(v_unused_406_);
v_unused_407_ = lean_ctor_get(v_it_379_, 0);
lean_dec(v_unused_407_);
v___x_392_ = v_it_379_;
v_isShared_393_ = v_isSharedCheck_405_;
goto v_resetjp_391_;
}
else
{
lean_dec(v_it_379_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_405_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
uint8_t v___x_394_; lean_object* v_digit_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v_acc_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_394_ = lean_uint8_sub(v_candidate_386_, v___x_387_);
v_digit_395_ = lean_uint8_to_nat(v___x_394_);
v___x_396_ = lean_unsigned_to_nat(10u);
v___x_397_ = lean_nat_mul(v_acc_380_, v___x_396_);
lean_dec(v_acc_380_);
v_acc_398_ = lean_nat_add(v___x_397_, v_digit_395_);
lean_dec(v___x_397_);
v___x_399_ = lean_unsigned_to_nat(1u);
v___x_400_ = lean_nat_add(v_idx_382_, v___x_399_);
lean_dec(v_idx_382_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v___x_400_);
v___x_402_ = v___x_392_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_array_381_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_400_);
v___x_402_ = v_reuseFailAlloc_404_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
v_it_379_ = v___x_402_;
v_acc_380_ = v_acc_398_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore(lean_object* v_acc_411_, lean_object* v_it_412_){
_start:
{
lean_object* v___x_413_; lean_object* v_fst_414_; lean_object* v_snd_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
v___x_413_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_412_, v_acc_411_);
v_fst_414_ = lean_ctor_get(v___x_413_, 0);
v_snd_415_ = lean_ctor_get(v___x_413_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_413_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_snd_415_);
lean_inc(v_fst_414_);
lean_dec(v___x_413_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v_fst_414_);
lean_ctor_set(v___x_417_, 0, v_snd_415_);
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_snd_415_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_fst_414_);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digits(lean_object* v_a_423_){
_start:
{
lean_object* v_array_424_; lean_object* v_idx_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v_array_424_ = lean_ctor_get(v_a_423_, 0);
v_idx_425_ = lean_ctor_get(v_a_423_, 1);
v___x_426_ = lean_byte_array_size(v_array_424_);
v___x_427_ = lean_nat_dec_lt(v_idx_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_box(0);
v___x_429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_429_, 0, v_a_423_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
return v___x_429_;
}
else
{
uint8_t v_c_430_; uint8_t v___x_431_; uint8_t v___y_433_; uint8_t v___x_461_; 
v_c_430_ = lean_byte_array_fget(v_array_424_, v_idx_425_);
v___x_431_ = 48;
v___x_461_ = lean_uint8_dec_le(v___x_431_, v_c_430_);
if (v___x_461_ == 0)
{
v___y_433_ = v___x_461_;
goto v___jp_432_;
}
else
{
uint8_t v___x_462_; uint8_t v___x_463_; 
v___x_462_ = 57;
v___x_463_ = lean_uint8_dec_le(v_c_430_, v___x_462_);
v___y_433_ = v___x_463_;
goto v___jp_432_;
}
v___jp_432_:
{
if (v___y_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_digit___closed__1));
v___x_435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_435_, 0, v_a_423_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
return v___x_435_;
}
else
{
lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_458_; 
lean_inc(v_idx_425_);
lean_inc_ref(v_array_424_);
v_isSharedCheck_458_ = !lean_is_exclusive(v_a_423_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; lean_object* v_unused_460_; 
v_unused_459_ = lean_ctor_get(v_a_423_, 1);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_a_423_, 0);
lean_dec(v_unused_460_);
v___x_437_ = v_a_423_;
v_isShared_438_ = v_isSharedCheck_458_;
goto v_resetjp_436_;
}
else
{
lean_dec(v_a_423_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_458_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_it_x27_442_; 
v___x_439_ = lean_unsigned_to_nat(1u);
v___x_440_ = lean_nat_add(v_idx_425_, v___x_439_);
lean_dec(v_idx_425_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 1, v___x_440_);
v_it_x27_442_ = v___x_437_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_array_424_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_440_);
v_it_x27_442_ = v_reuseFailAlloc_457_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
uint32_t v___x_443_; uint8_t v___x_444_; uint8_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v_fst_448_; lean_object* v_snd_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v___x_443_ = lean_uint8_to_uint32(v_c_430_);
v___x_444_ = lean_uint32_to_uint8(v___x_443_);
v___x_445_ = lean_uint8_sub(v___x_444_, v___x_431_);
v___x_446_ = lean_uint8_to_nat(v___x_445_);
v___x_447_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_442_, v___x_446_);
v_fst_448_ = lean_ctor_get(v___x_447_, 0);
v_snd_449_ = lean_ctor_get(v___x_447_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_447_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_snd_449_);
lean_inc(v_fst_448_);
lean_dec(v___x_447_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v_fst_448_);
lean_ctor_set(v___x_451_, 0, v_snd_449_);
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_snd_449_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_fst_448_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_hexDigit(lean_object* v_a_467_){
_start:
{
lean_object* v_array_468_; lean_object* v_idx_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v_array_468_ = lean_ctor_get(v_a_467_, 0);
v_idx_469_ = lean_ctor_get(v_a_467_, 1);
v___x_470_ = lean_byte_array_size(v_array_468_);
v___x_471_ = lean_nat_dec_lt(v_idx_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_box(0);
v___x_473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_473_, 0, v_a_467_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
return v___x_473_;
}
else
{
uint8_t v_c_474_; uint8_t v___y_483_; uint8_t v___y_484_; uint8_t v___y_488_; uint8_t v___y_489_; uint8_t v___y_490_; uint8_t v___y_492_; uint8_t v___y_493_; uint8_t v___y_499_; uint8_t v___x_504_; uint8_t v___x_505_; 
v_c_474_ = lean_byte_array_fget(v_array_468_, v_idx_469_);
v___x_504_ = 48;
v___x_505_ = lean_uint8_dec_le(v___x_504_, v_c_474_);
if (v___x_505_ == 0)
{
v___y_499_ = v___x_505_;
goto v___jp_498_;
}
else
{
uint8_t v___x_506_; uint8_t v___x_507_; 
v___x_506_ = 57;
v___x_507_ = lean_uint8_dec_le(v_c_474_, v___x_506_);
v___y_499_ = v___x_507_;
goto v___jp_498_;
}
v___jp_475_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v_it_x27_478_; uint32_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_add(v_idx_469_, v___x_476_);
lean_dec(v_idx_469_);
v_it_x27_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_478_, 0, v_array_468_);
lean_ctor_set(v_it_x27_478_, 1, v___x_477_);
v___x_479_ = lean_uint8_to_uint32(v_c_474_);
v___x_480_ = lean_box_uint32(v___x_479_);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v_it_x27_478_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
return v___x_481_;
}
v___jp_482_:
{
if (v___y_483_ == 0)
{
if (v___y_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1));
v___x_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_486_, 0, v_a_467_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
return v___x_486_;
}
else
{
lean_inc(v_idx_469_);
lean_inc_ref(v_array_468_);
lean_dec_ref(v_a_467_);
goto v___jp_475_;
}
}
else
{
lean_inc(v_idx_469_);
lean_inc_ref(v_array_468_);
lean_dec_ref(v_a_467_);
goto v___jp_475_;
}
}
v___jp_487_:
{
if (v___y_488_ == 0)
{
v___y_483_ = v___y_489_;
v___y_484_ = v___y_490_;
goto v___jp_482_;
}
else
{
v___y_483_ = v___y_489_;
v___y_484_ = v___y_488_;
goto v___jp_482_;
}
}
v___jp_491_:
{
uint8_t v___x_494_; uint8_t v___x_495_; 
v___x_494_ = 65;
v___x_495_ = lean_uint8_dec_le(v___x_494_, v_c_474_);
if (v___x_495_ == 0)
{
v___y_488_ = v___y_493_;
v___y_489_ = v___y_492_;
v___y_490_ = v___x_495_;
goto v___jp_487_;
}
else
{
uint8_t v___x_496_; uint8_t v___x_497_; 
v___x_496_ = 70;
v___x_497_ = lean_uint8_dec_le(v_c_474_, v___x_496_);
v___y_488_ = v___y_493_;
v___y_489_ = v___y_492_;
v___y_490_ = v___x_497_;
goto v___jp_487_;
}
}
v___jp_498_:
{
uint8_t v___x_500_; uint8_t v___x_501_; 
v___x_500_ = 97;
v___x_501_ = lean_uint8_dec_le(v___x_500_, v_c_474_);
if (v___x_501_ == 0)
{
v___y_492_ = v___y_499_;
v___y_493_ = v___x_501_;
goto v___jp_491_;
}
else
{
uint8_t v___x_502_; uint8_t v___x_503_; 
v___x_502_ = 102;
v___x_503_ = lean_uint8_dec_le(v_c_474_, v___x_502_);
v___y_492_ = v___y_499_;
v___y_493_ = v___x_503_;
goto v___jp_491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_octDigit(lean_object* v_a_511_){
_start:
{
lean_object* v_array_512_; lean_object* v_idx_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_array_512_ = lean_ctor_get(v_a_511_, 0);
v_idx_513_ = lean_ctor_get(v_a_511_, 1);
v___x_514_ = lean_byte_array_size(v_array_512_);
v___x_515_ = lean_nat_dec_lt(v_idx_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_box(0);
v___x_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_517_, 0, v_a_511_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
return v___x_517_;
}
else
{
uint8_t v_c_518_; uint8_t v___y_520_; uint8_t v___x_537_; uint8_t v___x_538_; 
v_c_518_ = lean_byte_array_fget(v_array_512_, v_idx_513_);
v___x_537_ = 48;
v___x_538_ = lean_uint8_dec_le(v___x_537_, v_c_518_);
if (v___x_538_ == 0)
{
v___y_520_ = v___x_538_;
goto v___jp_519_;
}
else
{
uint8_t v___x_539_; uint8_t v___x_540_; 
v___x_539_ = 55;
v___x_540_ = lean_uint8_dec_le(v_c_518_, v___x_539_);
v___y_520_ = v___x_540_;
goto v___jp_519_;
}
v___jp_519_:
{
if (v___y_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_octDigit___closed__1));
v___x_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_522_, 0, v_a_511_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
return v___x_522_;
}
else
{
lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_534_; 
lean_inc(v_idx_513_);
lean_inc_ref(v_array_512_);
v_isSharedCheck_534_ = !lean_is_exclusive(v_a_511_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; lean_object* v_unused_536_; 
v_unused_535_ = lean_ctor_get(v_a_511_, 1);
lean_dec(v_unused_535_);
v_unused_536_ = lean_ctor_get(v_a_511_, 0);
lean_dec(v_unused_536_);
v___x_524_ = v_a_511_;
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
else
{
lean_dec(v_a_511_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v_it_x27_529_; 
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = lean_nat_add(v_idx_513_, v___x_526_);
lean_dec(v_idx_513_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 1, v___x_527_);
v_it_x27_529_ = v___x_524_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_array_512_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_527_);
v_it_x27_529_ = v_reuseFailAlloc_533_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
uint32_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = lean_uint8_to_uint32(v_c_518_);
v___x_531_ = lean_box_uint32(v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v_it_x27_529_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
return v___x_532_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_asciiLetter(lean_object* v_a_544_){
_start:
{
lean_object* v_array_545_; lean_object* v_idx_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_array_545_ = lean_ctor_get(v_a_544_, 0);
v_idx_546_ = lean_ctor_get(v_a_544_, 1);
v___x_547_ = lean_byte_array_size(v_array_545_);
v___x_548_ = lean_nat_dec_lt(v_idx_546_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_box(0);
v___x_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_550_, 0, v_a_544_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
return v___x_550_;
}
else
{
uint8_t v_c_551_; uint8_t v___y_560_; uint8_t v___y_561_; uint8_t v___y_565_; uint8_t v___x_570_; uint8_t v___x_571_; 
v_c_551_ = lean_byte_array_fget(v_array_545_, v_idx_546_);
v___x_570_ = 65;
v___x_571_ = lean_uint8_dec_le(v___x_570_, v_c_551_);
if (v___x_571_ == 0)
{
v___y_565_ = v___x_571_;
goto v___jp_564_;
}
else
{
uint8_t v___x_572_; uint8_t v___x_573_; 
v___x_572_ = 90;
v___x_573_ = lean_uint8_dec_le(v_c_551_, v___x_572_);
v___y_565_ = v___x_573_;
goto v___jp_564_;
}
v___jp_552_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v_it_x27_555_; uint32_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = lean_nat_add(v_idx_546_, v___x_553_);
lean_dec(v_idx_546_);
v_it_x27_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_555_, 0, v_array_545_);
lean_ctor_set(v_it_x27_555_, 1, v___x_554_);
v___x_556_ = lean_uint8_to_uint32(v_c_551_);
v___x_557_ = lean_box_uint32(v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v_it_x27_555_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
return v___x_558_;
}
v___jp_559_:
{
if (v___y_560_ == 0)
{
if (v___y_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1));
v___x_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_563_, 0, v_a_544_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
return v___x_563_;
}
else
{
lean_inc(v_idx_546_);
lean_inc_ref(v_array_545_);
lean_dec_ref(v_a_544_);
goto v___jp_552_;
}
}
else
{
lean_inc(v_idx_546_);
lean_inc_ref(v_array_545_);
lean_dec_ref(v_a_544_);
goto v___jp_552_;
}
}
v___jp_564_:
{
uint8_t v___x_566_; uint8_t v___x_567_; 
v___x_566_ = 97;
v___x_567_ = lean_uint8_dec_le(v___x_566_, v_c_551_);
if (v___x_567_ == 0)
{
v___y_560_ = v___y_565_;
v___y_561_ = v___x_567_;
goto v___jp_559_;
}
else
{
uint8_t v___x_568_; uint8_t v___x_569_; 
v___x_568_ = 122;
v___x_569_ = lean_uint8_dec_le(v_c_551_, v___x_568_);
v___y_560_ = v___y_565_;
v___y_561_ = v___x_569_;
goto v___jp_559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(lean_object* v_it_574_){
_start:
{
lean_object* v_array_575_; lean_object* v_idx_576_; uint8_t v___y_578_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_array_575_ = lean_ctor_get(v_it_574_, 0);
v_idx_576_ = lean_ctor_get(v_it_574_, 1);
v___x_591_ = lean_byte_array_size(v_array_575_);
v___x_592_ = lean_nat_dec_lt(v_idx_576_, v___x_591_);
if (v___x_592_ == 0)
{
return v_it_574_;
}
else
{
uint8_t v_b_593_; uint8_t v___x_594_; uint8_t v___x_595_; uint8_t v___y_597_; uint8_t v___x_598_; uint8_t v___x_599_; uint8_t v___y_601_; uint8_t v___x_602_; uint8_t v___x_603_; 
v_b_593_ = lean_byte_array_fget(v_array_575_, v_idx_576_);
v___x_594_ = 9;
v___x_595_ = lean_uint8_dec_eq(v_b_593_, v___x_594_);
v___x_598_ = 10;
v___x_599_ = lean_uint8_dec_eq(v_b_593_, v___x_598_);
v___x_602_ = 13;
v___x_603_ = lean_uint8_dec_eq(v_b_593_, v___x_602_);
if (v___x_603_ == 0)
{
uint8_t v___x_604_; uint8_t v___x_605_; 
v___x_604_ = 32;
v___x_605_ = lean_uint8_dec_eq(v_b_593_, v___x_604_);
v___y_601_ = v___x_605_;
goto v___jp_600_;
}
else
{
v___y_601_ = v___x_603_;
goto v___jp_600_;
}
v___jp_596_:
{
if (v___x_595_ == 0)
{
v___y_578_ = v___y_597_;
goto v___jp_577_;
}
else
{
v___y_578_ = v___x_595_;
goto v___jp_577_;
}
}
v___jp_600_:
{
if (v___x_599_ == 0)
{
v___y_597_ = v___y_601_;
goto v___jp_596_;
}
else
{
v___y_597_ = v___x_599_;
goto v___jp_596_;
}
}
}
v___jp_577_:
{
if (v___y_578_ == 0)
{
return v_it_574_;
}
else
{
lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_588_; 
lean_inc(v_idx_576_);
lean_inc_ref(v_array_575_);
v_isSharedCheck_588_ = !lean_is_exclusive(v_it_574_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; lean_object* v_unused_590_; 
v_unused_589_ = lean_ctor_get(v_it_574_, 1);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_it_574_, 0);
lean_dec(v_unused_590_);
v___x_580_ = v_it_574_;
v_isShared_581_ = v_isSharedCheck_588_;
goto v_resetjp_579_;
}
else
{
lean_dec(v_it_574_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_588_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = lean_nat_add(v_idx_576_, v___x_582_);
lean_dec(v_idx_576_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_583_);
v___x_585_ = v___x_580_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_array_575_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v___x_583_);
v___x_585_ = v_reuseFailAlloc_587_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
v_it_574_ = v___x_585_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_ws(lean_object* v_it_606_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(v_it_606_);
v___x_608_ = lean_box(0);
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take(lean_object* v_n_610_, lean_object* v_it_611_){
_start:
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = l_ByteArray_Iterator_remainingBytes(v_it_611_);
v___x_613_ = lean_nat_dec_lt(v___x_612_, v_n_610_);
lean_dec(v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v_array_614_; lean_object* v_idx_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_634_; 
v_array_614_ = lean_ctor_get(v_it_611_, 0);
v_idx_615_ = lean_ctor_get(v_it_611_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_it_611_);
if (v_isSharedCheck_634_ == 0)
{
v___x_617_ = v_it_611_;
v_isShared_618_ = v_isSharedCheck_634_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_idx_615_);
lean_inc(v_array_614_);
lean_dec(v_it_611_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_634_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_619_ = lean_nat_add(v_idx_615_, v_n_610_);
lean_inc(v___x_619_);
lean_inc_ref(v_array_614_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_619_);
v___x_621_ = v___x_617_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_array_614_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_619_);
v___x_621_ = v_reuseFailAlloc_633_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v_lower_623_; lean_object* v_upper_624_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___y_630_; uint8_t v___x_632_; 
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_byte_array_size(v_array_614_);
v___x_632_ = lean_nat_dec_le(v_idx_615_, v___x_627_);
if (v___x_632_ == 0)
{
v___y_630_ = v_idx_615_;
goto v___jp_629_;
}
else
{
lean_dec(v_idx_615_);
v___y_630_ = v___x_627_;
goto v___jp_629_;
}
v___jp_622_:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = l_ByteArray_toByteSlice(v_array_614_, v_lower_623_, v_upper_624_);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_621_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
return v___x_626_;
}
v___jp_629_:
{
uint8_t v___x_631_; 
v___x_631_ = lean_nat_dec_le(v___x_619_, v___x_628_);
if (v___x_631_ == 0)
{
lean_dec(v___x_619_);
v_lower_623_ = v___y_630_;
v_upper_624_ = v___x_628_;
goto v___jp_622_;
}
else
{
v_lower_623_ = v___y_630_;
v_upper_624_ = v___x_619_;
goto v___jp_622_;
}
}
}
}
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_box(0);
v___x_636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_636_, 0, v_it_611_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take___boxed(lean_object* v_n_637_, lean_object* v_it_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Std_Internal_Parsec_ByteArray_take(v_n_637_, v_it_638_);
lean_dec(v_n_637_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(lean_object* v_pred_640_, lean_object* v_count_641_, lean_object* v_iter_642_){
_start:
{
lean_object* v_array_643_; lean_object* v_idx_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_array_643_ = lean_ctor_get(v_iter_642_, 0);
v_idx_644_ = lean_ctor_get(v_iter_642_, 1);
v___x_645_ = lean_byte_array_size(v_array_643_);
v___x_646_ = lean_nat_dec_lt(v_idx_644_, v___x_645_);
if (v___x_646_ == 0)
{
uint8_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
lean_dec_ref(v_pred_640_);
v___x_647_ = 1;
v___x_648_ = lean_box(v___x_647_);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v_iter_642_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v_count_641_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
return v___x_650_;
}
else
{
uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_651_ = lean_byte_array_fget(v_array_643_, v_idx_644_);
v___x_652_ = lean_box(v___x_651_);
lean_inc_ref(v_pred_640_);
v___x_653_ = lean_apply_1(v_pred_640_, v___x_652_);
v___x_654_ = lean_unbox(v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; 
lean_dec_ref(v_pred_640_);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v_iter_642_);
lean_ctor_set(v___x_655_, 1, v___x_653_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v_count_641_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
return v___x_656_;
}
else
{
lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_667_; 
lean_inc(v_idx_644_);
lean_inc_ref(v_array_643_);
v_isSharedCheck_667_ = !lean_is_exclusive(v_iter_642_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; lean_object* v_unused_669_; 
v_unused_668_ = lean_ctor_get(v_iter_642_, 1);
lean_dec(v_unused_668_);
v_unused_669_ = lean_ctor_get(v_iter_642_, 0);
lean_dec(v_unused_669_);
v___x_658_ = v_iter_642_;
v_isShared_659_ = v_isSharedCheck_667_;
goto v_resetjp_657_;
}
else
{
lean_dec(v_iter_642_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_667_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_660_ = lean_unsigned_to_nat(1u);
v___x_661_ = lean_nat_add(v_count_641_, v___x_660_);
lean_dec(v_count_641_);
v___x_662_ = lean_nat_add(v_idx_644_, v___x_660_);
lean_dec(v_idx_644_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_662_);
v___x_664_ = v___x_658_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_array_643_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v___x_662_);
v___x_664_ = v_reuseFailAlloc_666_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
v_count_641_ = v___x_661_;
v_iter_642_ = v___x_664_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object* v_pred_670_, lean_object* v_limit_671_, lean_object* v_count_672_, lean_object* v_iter_673_){
_start:
{
uint8_t v___x_674_; 
v___x_674_ = lean_nat_dec_le(v_limit_671_, v_count_672_);
if (v___x_674_ == 0)
{
lean_object* v_array_675_; lean_object* v_idx_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v_array_675_ = lean_ctor_get(v_iter_673_, 0);
v_idx_676_ = lean_ctor_get(v_iter_673_, 1);
v___x_677_ = lean_byte_array_size(v_array_675_);
v___x_678_ = lean_nat_dec_lt(v_idx_676_, v___x_677_);
if (v___x_678_ == 0)
{
uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec_ref(v_pred_670_);
v___x_679_ = 1;
v___x_680_ = lean_box(v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v_iter_673_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v_count_672_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
return v___x_682_;
}
else
{
uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_683_ = lean_byte_array_fget(v_array_675_, v_idx_676_);
v___x_684_ = lean_box(v___x_683_);
lean_inc_ref(v_pred_670_);
v___x_685_ = lean_apply_1(v_pred_670_, v___x_684_);
v___x_686_ = lean_unbox(v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec_ref(v_pred_670_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v_iter_673_);
lean_ctor_set(v___x_687_, 1, v___x_685_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v_count_672_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
return v___x_688_;
}
else
{
lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_699_; 
lean_inc(v_idx_676_);
lean_inc_ref(v_array_675_);
v_isSharedCheck_699_ = !lean_is_exclusive(v_iter_673_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; lean_object* v_unused_701_; 
v_unused_700_ = lean_ctor_get(v_iter_673_, 1);
lean_dec(v_unused_700_);
v_unused_701_ = lean_ctor_get(v_iter_673_, 0);
lean_dec(v_unused_701_);
v___x_690_ = v_iter_673_;
v_isShared_691_ = v_isSharedCheck_699_;
goto v_resetjp_689_;
}
else
{
lean_dec(v_iter_673_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_699_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_692_ = lean_unsigned_to_nat(1u);
v___x_693_ = lean_nat_add(v_count_672_, v___x_692_);
lean_dec(v_count_672_);
v___x_694_ = lean_nat_add(v_idx_676_, v___x_692_);
lean_dec(v_idx_676_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_694_);
v___x_696_ = v___x_690_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_array_675_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_694_);
v___x_696_ = v_reuseFailAlloc_698_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
v_count_672_ = v___x_693_;
v_iter_673_ = v___x_696_;
goto _start;
}
}
}
}
}
else
{
uint8_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
lean_dec_ref(v_pred_670_);
v___x_702_ = 0;
v___x_703_ = lean_box(v___x_702_);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v_iter_673_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v_count_672_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo___boxed(lean_object* v_pred_706_, lean_object* v_limit_707_, lean_object* v_count_708_, lean_object* v_iter_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_706_, v_limit_707_, v_count_708_, v_iter_709_);
lean_dec(v_limit_707_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile(lean_object* v_pred_711_, lean_object* v_it_712_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_snd_715_; lean_object* v_snd_716_; uint8_t v___x_717_; 
v___x_713_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_712_);
v___x_714_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v_pred_711_, v___x_713_, v_it_712_);
v_snd_715_ = lean_ctor_get(v___x_714_, 1);
lean_inc(v_snd_715_);
v_snd_716_ = lean_ctor_get(v_snd_715_, 1);
v___x_717_ = lean_unbox(v_snd_716_);
if (v___x_717_ == 0)
{
lean_object* v_fst_718_; lean_object* v_fst_719_; lean_object* v_array_720_; lean_object* v_idx_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_738_; 
v_fst_718_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_fst_718_);
lean_dec_ref(v___x_714_);
v_fst_719_ = lean_ctor_get(v_snd_715_, 0);
lean_inc(v_fst_719_);
lean_dec(v_snd_715_);
v_array_720_ = lean_ctor_get(v_it_712_, 0);
v_idx_721_ = lean_ctor_get(v_it_712_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_it_712_);
if (v_isSharedCheck_738_ == 0)
{
v___x_723_ = v_it_712_;
v_isShared_724_ = v_isSharedCheck_738_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_idx_721_);
lean_inc(v_array_720_);
lean_dec(v_it_712_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_738_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_lower_726_; lean_object* v_upper_727_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___y_735_; uint8_t v___x_737_; 
v___x_732_ = lean_nat_add(v_idx_721_, v_fst_718_);
lean_dec(v_fst_718_);
v___x_733_ = lean_byte_array_size(v_array_720_);
v___x_737_ = lean_nat_dec_le(v_idx_721_, v___x_713_);
if (v___x_737_ == 0)
{
v___y_735_ = v_idx_721_;
goto v___jp_734_;
}
else
{
lean_dec(v_idx_721_);
v___y_735_ = v___x_713_;
goto v___jp_734_;
}
v___jp_725_:
{
lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_728_ = l_ByteArray_toByteSlice(v_array_720_, v_lower_726_, v_upper_727_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_728_);
lean_ctor_set(v___x_723_, 0, v_fst_719_);
v___x_730_ = v___x_723_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_fst_719_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
v___jp_734_:
{
uint8_t v___x_736_; 
v___x_736_ = lean_nat_dec_le(v___x_732_, v___x_733_);
if (v___x_736_ == 0)
{
lean_dec(v___x_732_);
v_lower_726_ = v___y_735_;
v_upper_727_ = v___x_733_;
goto v___jp_725_;
}
else
{
v_lower_726_ = v___y_735_;
v_upper_727_ = v___x_732_;
goto v___jp_725_;
}
}
}
}
else
{
lean_object* v_fst_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref(v___x_714_);
lean_dec_ref(v_it_712_);
v_fst_739_ = lean_ctor_get(v_snd_715_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v_snd_715_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v_snd_715_, 1);
lean_dec(v_unused_748_);
v___x_741_ = v_snd_715_;
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_fst_739_);
lean_dec(v_snd_715_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = lean_box(0);
if (v_isShared_742_ == 0)
{
lean_ctor_set_tag(v___x_741_, 1);
lean_ctor_set(v___x_741_, 1, v___x_743_);
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_fst_739_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(lean_object* v_pred_749_, uint8_t v_b_750_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_751_ = lean_box(v_b_750_);
v___x_752_ = lean_apply_1(v_pred_749_, v___x_751_);
v___x_753_ = lean_unbox(v___x_752_);
if (v___x_753_ == 0)
{
uint8_t v___x_754_; 
v___x_754_ = 1;
return v___x_754_;
}
else
{
uint8_t v___x_755_; 
v___x_755_ = 0;
return v___x_755_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed(lean_object* v_pred_756_, lean_object* v_b_757_){
_start:
{
uint8_t v_b_boxed_758_; uint8_t v_res_759_; lean_object* v_r_760_; 
v_b_boxed_758_ = lean_unbox(v_b_757_);
v_res_759_ = l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(v_pred_756_, v_b_boxed_758_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil(lean_object* v_pred_761_, lean_object* v_a_762_){
_start:
{
lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v_snd_766_; lean_object* v_snd_767_; uint8_t v___x_768_; 
v___f_763_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_763_, 0, v_pred_761_);
v___x_764_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_762_);
v___x_765_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v___f_763_, v___x_764_, v_a_762_);
v_snd_766_ = lean_ctor_get(v___x_765_, 1);
lean_inc(v_snd_766_);
v_snd_767_ = lean_ctor_get(v_snd_766_, 1);
v___x_768_ = lean_unbox(v_snd_767_);
if (v___x_768_ == 0)
{
lean_object* v_fst_769_; lean_object* v_fst_770_; lean_object* v_array_771_; lean_object* v_idx_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_789_; 
v_fst_769_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_fst_769_);
lean_dec_ref(v___x_765_);
v_fst_770_ = lean_ctor_get(v_snd_766_, 0);
lean_inc(v_fst_770_);
lean_dec(v_snd_766_);
v_array_771_ = lean_ctor_get(v_a_762_, 0);
v_idx_772_ = lean_ctor_get(v_a_762_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_a_762_);
if (v_isSharedCheck_789_ == 0)
{
v___x_774_ = v_a_762_;
v_isShared_775_ = v_isSharedCheck_789_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_idx_772_);
lean_inc(v_array_771_);
lean_dec(v_a_762_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_789_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_lower_777_; lean_object* v_upper_778_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___y_786_; uint8_t v___x_788_; 
v___x_783_ = lean_nat_add(v_idx_772_, v_fst_769_);
lean_dec(v_fst_769_);
v___x_784_ = lean_byte_array_size(v_array_771_);
v___x_788_ = lean_nat_dec_le(v_idx_772_, v___x_764_);
if (v___x_788_ == 0)
{
v___y_786_ = v_idx_772_;
goto v___jp_785_;
}
else
{
lean_dec(v_idx_772_);
v___y_786_ = v___x_764_;
goto v___jp_785_;
}
v___jp_776_:
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = l_ByteArray_toByteSlice(v_array_771_, v_lower_777_, v_upper_778_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v___x_779_);
lean_ctor_set(v___x_774_, 0, v_fst_770_);
v___x_781_ = v___x_774_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_fst_770_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
v___jp_785_:
{
uint8_t v___x_787_; 
v___x_787_ = lean_nat_dec_le(v___x_783_, v___x_784_);
if (v___x_787_ == 0)
{
lean_dec(v___x_783_);
v_lower_777_ = v___y_786_;
v_upper_778_ = v___x_784_;
goto v___jp_776_;
}
else
{
v_lower_777_ = v___y_786_;
v_upper_778_ = v___x_783_;
goto v___jp_776_;
}
}
}
}
else
{
lean_object* v_fst_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref(v___x_765_);
lean_dec_ref(v_a_762_);
v_fst_790_ = lean_ctor_get(v_snd_766_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v_snd_766_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v_snd_766_, 1);
lean_dec(v_unused_799_);
v___x_792_ = v_snd_766_;
v_isShared_793_ = v_isSharedCheck_798_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_fst_790_);
lean_dec(v_snd_766_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_798_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_794_ = lean_box(0);
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 1);
lean_ctor_set(v___x_792_, 1, v___x_794_);
v___x_796_ = v___x_792_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_fst_790_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhile(lean_object* v_pred_800_, lean_object* v_it_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_snd_804_; lean_object* v_snd_805_; uint8_t v___x_806_; 
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v_pred_800_, v___x_802_, v_it_801_);
v_snd_804_ = lean_ctor_get(v___x_803_, 1);
lean_inc(v_snd_804_);
lean_dec_ref(v___x_803_);
v_snd_805_ = lean_ctor_get(v_snd_804_, 1);
v___x_806_ = lean_unbox(v_snd_805_);
if (v___x_806_ == 0)
{
lean_object* v_fst_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_815_; 
v_fst_807_ = lean_ctor_get(v_snd_804_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v_snd_804_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v_snd_804_, 1);
lean_dec(v_unused_816_);
v___x_809_ = v_snd_804_;
v_isShared_810_ = v_isSharedCheck_815_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_fst_807_);
lean_dec(v_snd_804_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_815_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_811_ = lean_box(0);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 1, v___x_811_);
v___x_813_ = v___x_809_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_fst_807_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
else
{
lean_object* v_fst_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_825_; 
v_fst_817_ = lean_ctor_get(v_snd_804_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v_snd_804_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; 
v_unused_826_ = lean_ctor_get(v_snd_804_, 1);
lean_dec(v_unused_826_);
v___x_819_ = v_snd_804_;
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_fst_817_);
lean_dec(v_snd_804_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_821_ = lean_box(0);
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 1);
lean_ctor_set(v___x_819_, 1, v___x_821_);
v___x_823_ = v___x_819_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_fst_817_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntil(lean_object* v_pred_827_, lean_object* v_a_828_){
_start:
{
lean_object* v___f_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v_snd_832_; lean_object* v_snd_833_; uint8_t v___x_834_; 
v___f_829_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_829_, 0, v_pred_827_);
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v___f_829_, v___x_830_, v_a_828_);
v_snd_832_ = lean_ctor_get(v___x_831_, 1);
lean_inc(v_snd_832_);
lean_dec_ref(v___x_831_);
v_snd_833_ = lean_ctor_get(v_snd_832_, 1);
v___x_834_ = lean_unbox(v_snd_833_);
if (v___x_834_ == 0)
{
lean_object* v_fst_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_843_; 
v_fst_835_ = lean_ctor_get(v_snd_832_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v_snd_832_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; 
v_unused_844_ = lean_ctor_get(v_snd_832_, 1);
lean_dec(v_unused_844_);
v___x_837_ = v_snd_832_;
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_fst_835_);
lean_dec(v_snd_832_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_839_ = lean_box(0);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v___x_839_);
v___x_841_ = v___x_837_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_fst_835_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
else
{
lean_object* v_fst_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_853_; 
v_fst_845_ = lean_ctor_get(v_snd_832_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v_snd_832_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v_snd_832_, 1);
lean_dec(v_unused_854_);
v___x_847_ = v_snd_832_;
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_fst_845_);
lean_dec(v_snd_832_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = lean_box(0);
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 1);
lean_ctor_set(v___x_847_, 1, v___x_849_);
v___x_851_ = v___x_847_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_fst_845_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(lean_object* v_pred_855_, lean_object* v_limit_856_, lean_object* v_it_857_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v_snd_860_; lean_object* v_snd_861_; uint8_t v___x_862_; 
v___x_858_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_857_);
v___x_859_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_855_, v_limit_856_, v___x_858_, v_it_857_);
v_snd_860_ = lean_ctor_get(v___x_859_, 1);
lean_inc(v_snd_860_);
v_snd_861_ = lean_ctor_get(v_snd_860_, 1);
v___x_862_ = lean_unbox(v_snd_861_);
if (v___x_862_ == 0)
{
lean_object* v_fst_863_; lean_object* v_fst_864_; lean_object* v_array_865_; lean_object* v_idx_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_883_; 
v_fst_863_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_fst_863_);
lean_dec_ref(v___x_859_);
v_fst_864_ = lean_ctor_get(v_snd_860_, 0);
lean_inc(v_fst_864_);
lean_dec(v_snd_860_);
v_array_865_ = lean_ctor_get(v_it_857_, 0);
v_idx_866_ = lean_ctor_get(v_it_857_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v_it_857_);
if (v_isSharedCheck_883_ == 0)
{
v___x_868_ = v_it_857_;
v_isShared_869_ = v_isSharedCheck_883_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_idx_866_);
lean_inc(v_array_865_);
lean_dec(v_it_857_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_883_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_lower_871_; lean_object* v_upper_872_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___y_880_; uint8_t v___x_882_; 
v___x_877_ = lean_nat_add(v_idx_866_, v_fst_863_);
lean_dec(v_fst_863_);
v___x_878_ = lean_byte_array_size(v_array_865_);
v___x_882_ = lean_nat_dec_le(v_idx_866_, v___x_858_);
if (v___x_882_ == 0)
{
v___y_880_ = v_idx_866_;
goto v___jp_879_;
}
else
{
lean_dec(v_idx_866_);
v___y_880_ = v___x_858_;
goto v___jp_879_;
}
v___jp_870_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = l_ByteArray_toByteSlice(v_array_865_, v_lower_871_, v_upper_872_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v___x_873_);
lean_ctor_set(v___x_868_, 0, v_fst_864_);
v___x_875_ = v___x_868_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_fst_864_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
v___jp_879_:
{
uint8_t v___x_881_; 
v___x_881_ = lean_nat_dec_le(v___x_877_, v___x_878_);
if (v___x_881_ == 0)
{
lean_dec(v___x_877_);
v_lower_871_ = v___y_880_;
v_upper_872_ = v___x_878_;
goto v___jp_870_;
}
else
{
v_lower_871_ = v___y_880_;
v_upper_872_ = v___x_877_;
goto v___jp_870_;
}
}
}
}
else
{
lean_object* v_fst_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_892_; 
lean_dec_ref(v___x_859_);
lean_dec_ref(v_it_857_);
v_fst_884_ = lean_ctor_get(v_snd_860_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v_snd_860_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_snd_860_, 1);
lean_dec(v_unused_893_);
v___x_886_ = v_snd_860_;
v_isShared_887_ = v_isSharedCheck_892_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_fst_884_);
lean_dec(v_snd_860_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_892_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_888_ = lean_box(0);
if (v_isShared_887_ == 0)
{
lean_ctor_set_tag(v___x_886_, 1);
lean_ctor_set(v___x_886_, 1, v___x_888_);
v___x_890_ = v___x_886_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_fst_884_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo___boxed(lean_object* v_pred_894_, lean_object* v_limit_895_, lean_object* v_it_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(v_pred_894_, v_limit_895_, v_it_896_);
lean_dec(v_limit_895_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(lean_object* v_pred_901_, lean_object* v_limit_902_, lean_object* v_it_903_){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v_snd_906_; lean_object* v_snd_907_; uint8_t v___x_908_; 
v___x_904_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_903_);
v___x_905_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_901_, v_limit_902_, v___x_904_, v_it_903_);
v_snd_906_ = lean_ctor_get(v___x_905_, 1);
lean_inc(v_snd_906_);
v_snd_907_ = lean_ctor_get(v_snd_906_, 1);
v___x_908_ = lean_unbox(v_snd_907_);
if (v___x_908_ == 0)
{
lean_object* v_fst_909_; lean_object* v_fst_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_938_; 
v_fst_909_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_fst_909_);
lean_dec_ref(v___x_905_);
v_fst_910_ = lean_ctor_get(v_snd_906_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v_snd_906_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v_snd_906_, 1);
lean_dec(v_unused_939_);
v___x_912_ = v_snd_906_;
v_isShared_913_ = v_isSharedCheck_938_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_fst_910_);
lean_dec(v_snd_906_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_938_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
uint8_t v___x_914_; 
v___x_914_ = lean_nat_dec_eq(v_fst_909_, v___x_904_);
if (v___x_914_ == 0)
{
lean_object* v_array_915_; lean_object* v_idx_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_933_; 
lean_del_object(v___x_912_);
v_array_915_ = lean_ctor_get(v_it_903_, 0);
v_idx_916_ = lean_ctor_get(v_it_903_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_it_903_);
if (v_isSharedCheck_933_ == 0)
{
v___x_918_ = v_it_903_;
v_isShared_919_ = v_isSharedCheck_933_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_idx_916_);
lean_inc(v_array_915_);
lean_dec(v_it_903_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_933_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v_lower_921_; lean_object* v_upper_922_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___y_930_; uint8_t v___x_932_; 
v___x_927_ = lean_nat_add(v_idx_916_, v_fst_909_);
lean_dec(v_fst_909_);
v___x_928_ = lean_byte_array_size(v_array_915_);
v___x_932_ = lean_nat_dec_le(v_idx_916_, v___x_904_);
if (v___x_932_ == 0)
{
v___y_930_ = v_idx_916_;
goto v___jp_929_;
}
else
{
lean_dec(v_idx_916_);
v___y_930_ = v___x_904_;
goto v___jp_929_;
}
v___jp_920_:
{
lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_923_ = l_ByteArray_toByteSlice(v_array_915_, v_lower_921_, v_upper_922_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v___x_923_);
lean_ctor_set(v___x_918_, 0, v_fst_910_);
v___x_925_ = v___x_918_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_fst_910_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
v___jp_929_:
{
uint8_t v___x_931_; 
v___x_931_ = lean_nat_dec_le(v___x_927_, v___x_928_);
if (v___x_931_ == 0)
{
lean_dec(v___x_927_);
v_lower_921_ = v___y_930_;
v_upper_922_ = v___x_928_;
goto v___jp_920_;
}
else
{
v_lower_921_ = v___y_930_;
v_upper_922_ = v___x_927_;
goto v___jp_920_;
}
}
}
}
else
{
lean_object* v___x_934_; lean_object* v___x_936_; 
lean_dec(v_fst_910_);
lean_dec(v_fst_909_);
v___x_934_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1));
if (v_isShared_913_ == 0)
{
lean_ctor_set_tag(v___x_912_, 1);
lean_ctor_set(v___x_912_, 1, v___x_934_);
lean_ctor_set(v___x_912_, 0, v_it_903_);
v___x_936_ = v___x_912_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_it_903_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
else
{
lean_object* v_fst_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v___x_905_);
lean_dec_ref(v_it_903_);
v_fst_940_ = lean_ctor_get(v_snd_906_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_snd_906_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_snd_906_, 1);
lean_dec(v_unused_949_);
v___x_942_ = v_snd_906_;
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_fst_940_);
lean_dec(v_snd_906_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_944_ = lean_box(0);
if (v_isShared_943_ == 0)
{
lean_ctor_set_tag(v___x_942_, 1);
lean_ctor_set(v___x_942_, 1, v___x_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_fst_940_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v___x_944_);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___boxed(lean_object* v_pred_950_, lean_object* v_limit_951_, lean_object* v_it_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(v_pred_950_, v_limit_951_, v_it_952_);
lean_dec(v_limit_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(lean_object* v_pred_954_, lean_object* v_limit_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___f_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v_snd_960_; lean_object* v_snd_961_; uint8_t v___x_962_; 
v___f_957_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_957_, 0, v_pred_954_);
v___x_958_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_956_);
v___x_959_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_957_, v_limit_955_, v___x_958_, v_a_956_);
v_snd_960_ = lean_ctor_get(v___x_959_, 1);
lean_inc(v_snd_960_);
v_snd_961_ = lean_ctor_get(v_snd_960_, 1);
v___x_962_ = lean_unbox(v_snd_961_);
if (v___x_962_ == 0)
{
lean_object* v_fst_963_; lean_object* v_fst_964_; lean_object* v_array_965_; lean_object* v_idx_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_983_; 
v_fst_963_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_fst_963_);
lean_dec_ref(v___x_959_);
v_fst_964_ = lean_ctor_get(v_snd_960_, 0);
lean_inc(v_fst_964_);
lean_dec(v_snd_960_);
v_array_965_ = lean_ctor_get(v_a_956_, 0);
v_idx_966_ = lean_ctor_get(v_a_956_, 1);
v_isSharedCheck_983_ = !lean_is_exclusive(v_a_956_);
if (v_isSharedCheck_983_ == 0)
{
v___x_968_ = v_a_956_;
v_isShared_969_ = v_isSharedCheck_983_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_idx_966_);
lean_inc(v_array_965_);
lean_dec(v_a_956_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_983_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v_lower_971_; lean_object* v_upper_972_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___y_980_; uint8_t v___x_982_; 
v___x_977_ = lean_nat_add(v_idx_966_, v_fst_963_);
lean_dec(v_fst_963_);
v___x_978_ = lean_byte_array_size(v_array_965_);
v___x_982_ = lean_nat_dec_le(v_idx_966_, v___x_958_);
if (v___x_982_ == 0)
{
v___y_980_ = v_idx_966_;
goto v___jp_979_;
}
else
{
lean_dec(v_idx_966_);
v___y_980_ = v___x_958_;
goto v___jp_979_;
}
v___jp_970_:
{
lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_973_ = l_ByteArray_toByteSlice(v_array_965_, v_lower_971_, v_upper_972_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 1, v___x_973_);
lean_ctor_set(v___x_968_, 0, v_fst_964_);
v___x_975_ = v___x_968_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_fst_964_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
v___jp_979_:
{
uint8_t v___x_981_; 
v___x_981_ = lean_nat_dec_le(v___x_977_, v___x_978_);
if (v___x_981_ == 0)
{
lean_dec(v___x_977_);
v_lower_971_ = v___y_980_;
v_upper_972_ = v___x_978_;
goto v___jp_970_;
}
else
{
v_lower_971_ = v___y_980_;
v_upper_972_ = v___x_977_;
goto v___jp_970_;
}
}
}
}
else
{
lean_object* v_fst_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_992_; 
lean_dec_ref(v___x_959_);
lean_dec_ref(v_a_956_);
v_fst_984_ = lean_ctor_get(v_snd_960_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v_snd_960_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; 
v_unused_993_ = lean_ctor_get(v_snd_960_, 1);
lean_dec(v_unused_993_);
v___x_986_ = v_snd_960_;
v_isShared_987_ = v_isSharedCheck_992_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_fst_984_);
lean_dec(v_snd_960_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_992_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_988_ = lean_box(0);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 1);
lean_ctor_set(v___x_986_, 1, v___x_988_);
v___x_990_ = v___x_986_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_fst_984_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo___boxed(lean_object* v_pred_994_, lean_object* v_limit_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(v_pred_994_, v_limit_995_, v_a_996_);
lean_dec(v_limit_995_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileAtMost(lean_object* v_pred_998_, lean_object* v_limit_999_, lean_object* v_it_1000_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v_snd_1003_; lean_object* v_fst_1004_; lean_object* v_fst_1005_; lean_object* v_array_1006_; lean_object* v_idx_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1024_; 
v___x_1001_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_1000_);
v___x_1002_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_998_, v_limit_999_, v___x_1001_, v_it_1000_);
v_snd_1003_ = lean_ctor_get(v___x_1002_, 1);
lean_inc(v_snd_1003_);
v_fst_1004_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_fst_1004_);
lean_dec_ref(v___x_1002_);
v_fst_1005_ = lean_ctor_get(v_snd_1003_, 0);
lean_inc(v_fst_1005_);
lean_dec(v_snd_1003_);
v_array_1006_ = lean_ctor_get(v_it_1000_, 0);
v_idx_1007_ = lean_ctor_get(v_it_1000_, 1);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_it_1000_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1009_ = v_it_1000_;
v_isShared_1010_ = v_isSharedCheck_1024_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_idx_1007_);
lean_inc(v_array_1006_);
lean_dec(v_it_1000_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1024_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v_lower_1012_; lean_object* v_upper_1013_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___y_1021_; uint8_t v___x_1023_; 
v___x_1018_ = lean_nat_add(v_idx_1007_, v_fst_1004_);
lean_dec(v_fst_1004_);
v___x_1019_ = lean_byte_array_size(v_array_1006_);
v___x_1023_ = lean_nat_dec_le(v_idx_1007_, v___x_1001_);
if (v___x_1023_ == 0)
{
v___y_1021_ = v_idx_1007_;
goto v___jp_1020_;
}
else
{
lean_dec(v_idx_1007_);
v___y_1021_ = v___x_1001_;
goto v___jp_1020_;
}
v___jp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1014_ = l_ByteArray_toByteSlice(v_array_1006_, v_lower_1012_, v_upper_1013_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v___x_1014_);
lean_ctor_set(v___x_1009_, 0, v_fst_1005_);
v___x_1016_ = v___x_1009_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_fst_1005_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
v___jp_1020_:
{
uint8_t v___x_1022_; 
v___x_1022_ = lean_nat_dec_le(v___x_1018_, v___x_1019_);
if (v___x_1022_ == 0)
{
lean_dec(v___x_1018_);
v_lower_1012_ = v___y_1021_;
v_upper_1013_ = v___x_1019_;
goto v___jp_1011_;
}
else
{
v_lower_1012_ = v___y_1021_;
v_upper_1013_ = v___x_1018_;
goto v___jp_1011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileAtMost___boxed(lean_object* v_pred_1025_, lean_object* v_limit_1026_, lean_object* v_it_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Std_Internal_Parsec_ByteArray_takeWhileAtMost(v_pred_1025_, v_limit_1026_, v_it_1027_);
lean_dec(v_limit_1026_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost(lean_object* v_pred_1029_, lean_object* v_limit_1030_, lean_object* v_it_1031_){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v_snd_1034_; lean_object* v_fst_1035_; lean_object* v_fst_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1064_; 
v___x_1032_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_1031_);
v___x_1033_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_1029_, v_limit_1030_, v___x_1032_, v_it_1031_);
v_snd_1034_ = lean_ctor_get(v___x_1033_, 1);
lean_inc(v_snd_1034_);
v_fst_1035_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_fst_1035_);
lean_dec_ref(v___x_1033_);
v_fst_1036_ = lean_ctor_get(v_snd_1034_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_snd_1034_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v_snd_1034_, 1);
lean_dec(v_unused_1065_);
v___x_1038_ = v_snd_1034_;
v_isShared_1039_ = v_isSharedCheck_1064_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_fst_1036_);
lean_dec(v_snd_1034_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1064_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
uint8_t v___x_1040_; 
v___x_1040_ = lean_nat_dec_eq(v_fst_1035_, v___x_1032_);
if (v___x_1040_ == 0)
{
lean_object* v_array_1041_; lean_object* v_idx_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1059_; 
lean_del_object(v___x_1038_);
v_array_1041_ = lean_ctor_get(v_it_1031_, 0);
v_idx_1042_ = lean_ctor_get(v_it_1031_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_it_1031_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1044_ = v_it_1031_;
v_isShared_1045_ = v_isSharedCheck_1059_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_idx_1042_);
lean_inc(v_array_1041_);
lean_dec(v_it_1031_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1059_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v_lower_1047_; lean_object* v_upper_1048_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___y_1056_; uint8_t v___x_1058_; 
v___x_1053_ = lean_nat_add(v_idx_1042_, v_fst_1035_);
lean_dec(v_fst_1035_);
v___x_1054_ = lean_byte_array_size(v_array_1041_);
v___x_1058_ = lean_nat_dec_le(v_idx_1042_, v___x_1032_);
if (v___x_1058_ == 0)
{
v___y_1056_ = v_idx_1042_;
goto v___jp_1055_;
}
else
{
lean_dec(v_idx_1042_);
v___y_1056_ = v___x_1032_;
goto v___jp_1055_;
}
v___jp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1049_ = l_ByteArray_toByteSlice(v_array_1041_, v_lower_1047_, v_upper_1048_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 1, v___x_1049_);
lean_ctor_set(v___x_1044_, 0, v_fst_1036_);
v___x_1051_ = v___x_1044_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_fst_1036_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
v___jp_1055_:
{
uint8_t v___x_1057_; 
v___x_1057_ = lean_nat_dec_le(v___x_1053_, v___x_1054_);
if (v___x_1057_ == 0)
{
lean_dec(v___x_1053_);
v_lower_1047_ = v___y_1056_;
v_upper_1048_ = v___x_1054_;
goto v___jp_1046_;
}
else
{
v_lower_1047_ = v___y_1056_;
v_upper_1048_ = v___x_1053_;
goto v___jp_1046_;
}
}
}
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
lean_dec(v_fst_1036_);
lean_dec(v_fst_1035_);
v___x_1060_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1));
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 1);
lean_ctor_set(v___x_1038_, 1, v___x_1060_);
lean_ctor_set(v___x_1038_, 0, v_it_1031_);
v___x_1062_ = v___x_1038_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_it_1031_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost___boxed(lean_object* v_pred_1066_, lean_object* v_limit_1067_, lean_object* v_it_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost(v_pred_1066_, v_limit_1067_, v_it_1068_);
lean_dec(v_limit_1067_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(lean_object* v_pred_1070_, lean_object* v_limit_1071_, lean_object* v_it_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v_snd_1075_; lean_object* v_snd_1076_; uint8_t v___x_1077_; 
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_1070_, v_limit_1071_, v___x_1073_, v_it_1072_);
v_snd_1075_ = lean_ctor_get(v___x_1074_, 1);
lean_inc(v_snd_1075_);
lean_dec_ref(v___x_1074_);
v_snd_1076_ = lean_ctor_get(v_snd_1075_, 1);
v___x_1077_ = lean_unbox(v_snd_1076_);
if (v___x_1077_ == 0)
{
lean_object* v_fst_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1086_; 
v_fst_1078_ = lean_ctor_get(v_snd_1075_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_snd_1075_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; 
v_unused_1087_ = lean_ctor_get(v_snd_1075_, 1);
lean_dec(v_unused_1087_);
v___x_1080_ = v_snd_1075_;
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_fst_1078_);
lean_dec(v_snd_1075_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = lean_box(0);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v___x_1082_);
v___x_1084_ = v___x_1080_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_fst_1078_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
else
{
lean_object* v_fst_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1096_; 
v_fst_1088_ = lean_ctor_get(v_snd_1075_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_snd_1075_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v_snd_1075_, 1);
lean_dec(v_unused_1097_);
v___x_1090_ = v_snd_1075_;
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_fst_1088_);
lean_dec(v_snd_1075_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = lean_box(0);
if (v_isShared_1091_ == 0)
{
lean_ctor_set_tag(v___x_1090_, 1);
lean_ctor_set(v___x_1090_, 1, v___x_1092_);
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_fst_1088_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhileUpTo___boxed(lean_object* v_pred_1098_, lean_object* v_limit_1099_, lean_object* v_it_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(v_pred_1098_, v_limit_1099_, v_it_1100_);
lean_dec(v_limit_1099_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(lean_object* v_pred_1102_, lean_object* v_limit_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v___f_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v_snd_1108_; lean_object* v_snd_1109_; uint8_t v___x_1110_; 
v___f_1105_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1105_, 0, v_pred_1102_);
v___x_1106_ = lean_unsigned_to_nat(0u);
v___x_1107_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1105_, v_limit_1103_, v___x_1106_, v_a_1104_);
v_snd_1108_ = lean_ctor_get(v___x_1107_, 1);
lean_inc(v_snd_1108_);
lean_dec_ref(v___x_1107_);
v_snd_1109_ = lean_ctor_get(v_snd_1108_, 1);
v___x_1110_ = lean_unbox(v_snd_1109_);
if (v___x_1110_ == 0)
{
lean_object* v_fst_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1119_; 
v_fst_1111_ = lean_ctor_get(v_snd_1108_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_snd_1108_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; 
v_unused_1120_ = lean_ctor_get(v_snd_1108_, 1);
lean_dec(v_unused_1120_);
v___x_1113_ = v_snd_1108_;
v_isShared_1114_ = v_isSharedCheck_1119_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_fst_1111_);
lean_dec(v_snd_1108_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1119_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1115_ = lean_box(0);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 1, v___x_1115_);
v___x_1117_ = v___x_1113_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_fst_1111_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
else
{
lean_object* v_fst_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1129_; 
v_fst_1121_ = lean_ctor_get(v_snd_1108_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_snd_1108_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; 
v_unused_1130_ = lean_ctor_get(v_snd_1108_, 1);
lean_dec(v_unused_1130_);
v___x_1123_ = v_snd_1108_;
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_fst_1121_);
lean_dec(v_snd_1108_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1125_ = lean_box(0);
if (v_isShared_1124_ == 0)
{
lean_ctor_set_tag(v___x_1123_, 1);
lean_ctor_set(v___x_1123_, 1, v___x_1125_);
v___x_1127_ = v___x_1123_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_fst_1121_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntilUpTo___boxed(lean_object* v_pred_1131_, lean_object* v_limit_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(v_pred_1131_, v_limit_1132_, v_a_1133_);
lean_dec(v_limit_1132_);
return v_res_1134_;
}
}
lean_object* runtime_initialize_Std_Internal_Parsec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_ByteSlice(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Internal_Parsec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_ByteSlice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Parsec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_ByteSlice(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Parsec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_ByteSlice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Parsec_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Parsec_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Parsec_ByteArray(builtin);
}
#ifdef __cplusplus
}
#endif
