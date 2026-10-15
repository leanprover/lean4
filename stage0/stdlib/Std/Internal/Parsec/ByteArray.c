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
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
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
lean_object* v_array_346_; lean_object* v_idx_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_array_346_ = lean_ctor_get(v_a_342_, 0);
v_idx_347_ = lean_ctor_get(v_a_342_, 1);
v___x_348_ = lean_byte_array_size(v_array_346_);
v___x_349_ = lean_nat_dec_lt(v_idx_347_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_box(0);
v___x_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_351_, 0, v_a_342_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
return v___x_351_;
}
else
{
uint8_t v_c_352_; uint8_t v___x_353_; uint8_t v___x_354_; 
v_c_352_ = lean_byte_array_fget(v_array_346_, v_idx_347_);
v___x_353_ = 48;
v___x_354_ = lean_uint8_dec_le(v___x_353_, v_c_352_);
if (v___x_354_ == 0)
{
goto v___jp_343_;
}
else
{
uint8_t v___x_355_; uint8_t v___x_356_; 
v___x_355_ = 57;
v___x_356_ = lean_uint8_dec_le(v_c_352_, v___x_355_);
if (v___x_356_ == 0)
{
goto v___jp_343_;
}
else
{
lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_368_; 
lean_inc(v_idx_347_);
lean_inc_ref(v_array_346_);
v_isSharedCheck_368_ = !lean_is_exclusive(v_a_342_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; lean_object* v_unused_370_; 
v_unused_369_ = lean_ctor_get(v_a_342_, 1);
lean_dec(v_unused_369_);
v_unused_370_ = lean_ctor_get(v_a_342_, 0);
lean_dec(v_unused_370_);
v___x_358_ = v_a_342_;
v_isShared_359_ = v_isSharedCheck_368_;
goto v_resetjp_357_;
}
else
{
lean_dec(v_a_342_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_368_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_it_x27_363_; 
v___x_360_ = lean_unsigned_to_nat(1u);
v___x_361_ = lean_nat_add(v_idx_347_, v___x_360_);
lean_dec(v_idx_347_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 1, v___x_361_);
v_it_x27_363_ = v___x_358_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_array_346_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_361_);
v_it_x27_363_ = v_reuseFailAlloc_367_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
uint32_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_364_ = lean_uint8_to_uint32(v_c_352_);
v___x_365_ = lean_box_uint32(v___x_364_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_it_x27_363_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
return v___x_366_;
}
}
}
}
}
v___jp_343_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_digit___closed__1));
v___x_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_345_, 0, v_a_342_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(uint8_t v_b_371_){
_start:
{
uint8_t v___x_372_; uint8_t v___x_373_; lean_object* v___x_374_; 
v___x_372_ = 48;
v___x_373_ = lean_uint8_sub(v_b_371_, v___x_372_);
v___x_374_ = lean_uint8_to_nat(v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat___boxed(lean_object* v_b_375_){
_start:
{
uint8_t v_b_boxed_376_; lean_object* v_res_377_; 
v_b_boxed_376_ = lean_unbox(v_b_375_);
v_res_377_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(v_b_boxed_376_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object* v_it_378_, lean_object* v_acc_379_){
_start:
{
lean_object* v_array_380_; lean_object* v_idx_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v_array_380_ = lean_ctor_get(v_it_378_, 0);
v_idx_381_ = lean_ctor_get(v_it_378_, 1);
v___x_382_ = lean_byte_array_size(v_array_380_);
v___x_383_ = lean_nat_dec_lt(v_idx_381_, v___x_382_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; 
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_acc_379_);
lean_ctor_set(v___x_384_, 1, v_it_378_);
return v___x_384_;
}
else
{
uint8_t v_candidate_385_; uint8_t v___x_386_; uint8_t v___x_387_; 
v_candidate_385_ = lean_byte_array_fget(v_array_380_, v_idx_381_);
v___x_386_ = 48;
v___x_387_ = lean_uint8_dec_le(v___x_386_, v_candidate_385_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v_acc_379_);
lean_ctor_set(v___x_388_, 1, v_it_378_);
return v___x_388_;
}
else
{
uint8_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 57;
v___x_390_ = lean_uint8_dec_le(v_candidate_385_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v_acc_379_);
lean_ctor_set(v___x_391_, 1, v_it_378_);
return v___x_391_;
}
else
{
lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_406_; 
lean_inc(v_idx_381_);
lean_inc_ref(v_array_380_);
v_isSharedCheck_406_ = !lean_is_exclusive(v_it_378_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; lean_object* v_unused_408_; 
v_unused_407_ = lean_ctor_get(v_it_378_, 1);
lean_dec(v_unused_407_);
v_unused_408_ = lean_ctor_get(v_it_378_, 0);
lean_dec(v_unused_408_);
v___x_393_ = v_it_378_;
v_isShared_394_ = v_isSharedCheck_406_;
goto v_resetjp_392_;
}
else
{
lean_dec(v_it_378_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_406_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
uint8_t v___x_395_; lean_object* v_digit_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v_acc_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_395_ = lean_uint8_sub(v_candidate_385_, v___x_386_);
v_digit_396_ = lean_uint8_to_nat(v___x_395_);
v___x_397_ = lean_unsigned_to_nat(10u);
v___x_398_ = lean_nat_mul(v_acc_379_, v___x_397_);
lean_dec(v_acc_379_);
v_acc_399_ = lean_nat_add(v___x_398_, v_digit_396_);
lean_dec(v___x_398_);
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = lean_nat_add(v_idx_381_, v___x_400_);
lean_dec(v_idx_381_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 1, v___x_401_);
v___x_403_ = v___x_393_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_array_380_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v___x_401_);
v___x_403_ = v_reuseFailAlloc_405_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
v_it_378_ = v___x_403_;
v_acc_379_ = v_acc_399_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore(lean_object* v_acc_409_, lean_object* v_it_410_){
_start:
{
lean_object* v___x_411_; lean_object* v_fst_412_; lean_object* v_snd_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
v___x_411_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_410_, v_acc_409_);
v_fst_412_ = lean_ctor_get(v___x_411_, 0);
v_snd_413_ = lean_ctor_get(v___x_411_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_411_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_snd_413_);
lean_inc(v_fst_412_);
lean_dec(v___x_411_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v_fst_412_);
lean_ctor_set(v___x_415_, 0, v_snd_413_);
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_snd_413_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_fst_412_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digits(lean_object* v_a_421_){
_start:
{
lean_object* v_array_425_; lean_object* v_idx_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v_array_425_ = lean_ctor_get(v_a_421_, 0);
v_idx_426_ = lean_ctor_get(v_a_421_, 1);
v___x_427_ = lean_byte_array_size(v_array_425_);
v___x_428_ = lean_nat_dec_lt(v_idx_426_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_box(0);
v___x_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_430_, 0, v_a_421_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
return v___x_430_;
}
else
{
uint8_t v_c_431_; uint8_t v___x_432_; uint8_t v___x_433_; 
v_c_431_ = lean_byte_array_fget(v_array_425_, v_idx_426_);
v___x_432_ = 48;
v___x_433_ = lean_uint8_dec_le(v___x_432_, v_c_431_);
if (v___x_433_ == 0)
{
goto v___jp_422_;
}
else
{
uint8_t v___x_434_; uint8_t v___x_435_; 
v___x_434_ = 57;
v___x_435_ = lean_uint8_dec_le(v_c_431_, v___x_434_);
if (v___x_435_ == 0)
{
goto v___jp_422_;
}
else
{
lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_458_; 
lean_inc(v_idx_426_);
lean_inc_ref(v_array_425_);
v_isSharedCheck_458_ = !lean_is_exclusive(v_a_421_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; lean_object* v_unused_460_; 
v_unused_459_ = lean_ctor_get(v_a_421_, 1);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_a_421_, 0);
lean_dec(v_unused_460_);
v___x_437_ = v_a_421_;
v_isShared_438_ = v_isSharedCheck_458_;
goto v_resetjp_436_;
}
else
{
lean_dec(v_a_421_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_458_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_it_x27_442_; 
v___x_439_ = lean_unsigned_to_nat(1u);
v___x_440_ = lean_nat_add(v_idx_426_, v___x_439_);
lean_dec(v_idx_426_);
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
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_array_425_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_440_);
v_it_x27_442_ = v_reuseFailAlloc_457_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
uint32_t v___x_443_; uint8_t v___x_444_; uint8_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v_fst_448_; lean_object* v_snd_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v___x_443_ = lean_uint8_to_uint32(v_c_431_);
v___x_444_ = lean_uint32_to_uint8(v___x_443_);
v___x_445_ = lean_uint8_sub(v___x_444_, v___x_432_);
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
v___jp_422_:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_digit___closed__1));
v___x_424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_424_, 0, v_a_421_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_hexDigit(lean_object* v_a_464_){
_start:
{
lean_object* v_array_468_; lean_object* v_idx_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v_array_468_ = lean_ctor_get(v_a_464_, 0);
v_idx_469_ = lean_ctor_get(v_a_464_, 1);
v___x_470_ = lean_byte_array_size(v_array_468_);
v___x_471_ = lean_nat_dec_lt(v_idx_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_box(0);
v___x_473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_473_, 0, v_a_464_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
return v___x_473_;
}
else
{
uint8_t v_c_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v_it_x27_477_; uint8_t v___x_492_; uint8_t v___x_493_; 
v_c_474_ = lean_byte_array_fget(v_array_468_, v_idx_469_);
v___x_475_ = lean_unsigned_to_nat(1u);
v___x_476_ = lean_nat_add(v_idx_469_, v___x_475_);
lean_inc_ref(v_array_468_);
v_it_x27_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_477_, 0, v_array_468_);
lean_ctor_set(v_it_x27_477_, 1, v___x_476_);
v___x_492_ = 48;
v___x_493_ = lean_uint8_dec_le(v___x_492_, v_c_474_);
if (v___x_493_ == 0)
{
goto v___jp_487_;
}
else
{
uint8_t v___x_494_; uint8_t v___x_495_; 
v___x_494_ = 57;
v___x_495_ = lean_uint8_dec_le(v_c_474_, v___x_494_);
if (v___x_495_ == 0)
{
goto v___jp_487_;
}
else
{
lean_dec_ref(v_a_464_);
goto v___jp_478_;
}
}
v___jp_478_:
{
uint32_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_uint8_to_uint32(v_c_474_);
v___x_480_ = lean_box_uint32(v___x_479_);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v_it_x27_477_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
return v___x_481_;
}
v___jp_482_:
{
uint8_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = 65;
v___x_484_ = lean_uint8_dec_le(v___x_483_, v_c_474_);
if (v___x_484_ == 0)
{
lean_dec_ref_known(v_it_x27_477_, 2);
goto v___jp_465_;
}
else
{
uint8_t v___x_485_; uint8_t v___x_486_; 
v___x_485_ = 70;
v___x_486_ = lean_uint8_dec_le(v_c_474_, v___x_485_);
if (v___x_486_ == 0)
{
lean_dec_ref_known(v_it_x27_477_, 2);
goto v___jp_465_;
}
else
{
lean_dec_ref(v_a_464_);
goto v___jp_478_;
}
}
}
v___jp_487_:
{
uint8_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = 97;
v___x_489_ = lean_uint8_dec_le(v___x_488_, v_c_474_);
if (v___x_489_ == 0)
{
goto v___jp_482_;
}
else
{
uint8_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = 102;
v___x_491_ = lean_uint8_dec_le(v_c_474_, v___x_490_);
if (v___x_491_ == 0)
{
goto v___jp_482_;
}
else
{
lean_dec_ref(v_a_464_);
goto v___jp_478_;
}
}
}
}
v___jp_465_:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1));
v___x_467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_467_, 0, v_a_464_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_octDigit(lean_object* v_a_499_){
_start:
{
lean_object* v_array_503_; lean_object* v_idx_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_array_503_ = lean_ctor_get(v_a_499_, 0);
v_idx_504_ = lean_ctor_get(v_a_499_, 1);
v___x_505_ = lean_byte_array_size(v_array_503_);
v___x_506_ = lean_nat_dec_lt(v_idx_504_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_box(0);
v___x_508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_508_, 0, v_a_499_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
return v___x_508_;
}
else
{
uint8_t v_c_509_; uint8_t v___x_510_; uint8_t v___x_511_; 
v_c_509_ = lean_byte_array_fget(v_array_503_, v_idx_504_);
v___x_510_ = 48;
v___x_511_ = lean_uint8_dec_le(v___x_510_, v_c_509_);
if (v___x_511_ == 0)
{
goto v___jp_500_;
}
else
{
uint8_t v___x_512_; uint8_t v___x_513_; 
v___x_512_ = 55;
v___x_513_ = lean_uint8_dec_le(v_c_509_, v___x_512_);
if (v___x_513_ == 0)
{
goto v___jp_500_;
}
else
{
lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_525_; 
lean_inc(v_idx_504_);
lean_inc_ref(v_array_503_);
v_isSharedCheck_525_ = !lean_is_exclusive(v_a_499_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; lean_object* v_unused_527_; 
v_unused_526_ = lean_ctor_get(v_a_499_, 1);
lean_dec(v_unused_526_);
v_unused_527_ = lean_ctor_get(v_a_499_, 0);
lean_dec(v_unused_527_);
v___x_515_ = v_a_499_;
v_isShared_516_ = v_isSharedCheck_525_;
goto v_resetjp_514_;
}
else
{
lean_dec(v_a_499_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_525_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v_it_x27_520_; 
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_518_ = lean_nat_add(v_idx_504_, v___x_517_);
lean_dec(v_idx_504_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 1, v___x_518_);
v_it_x27_520_ = v___x_515_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_array_503_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_518_);
v_it_x27_520_ = v_reuseFailAlloc_524_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
uint32_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = lean_uint8_to_uint32(v_c_509_);
v___x_522_ = lean_box_uint32(v___x_521_);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v_it_x27_520_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
return v___x_523_;
}
}
}
}
}
v___jp_500_:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_octDigit___closed__1));
v___x_502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_502_, 0, v_a_499_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_asciiLetter(lean_object* v_a_531_){
_start:
{
lean_object* v_array_535_; lean_object* v_idx_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_array_535_ = lean_ctor_get(v_a_531_, 0);
v_idx_536_ = lean_ctor_get(v_a_531_, 1);
v___x_537_ = lean_byte_array_size(v_array_535_);
v___x_538_ = lean_nat_dec_lt(v_idx_536_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_box(0);
v___x_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_540_, 0, v_a_531_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
return v___x_540_;
}
else
{
uint8_t v_c_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v_it_x27_544_; uint8_t v___x_554_; uint8_t v___x_555_; 
v_c_541_ = lean_byte_array_fget(v_array_535_, v_idx_536_);
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_add(v_idx_536_, v___x_542_);
lean_inc_ref(v_array_535_);
v_it_x27_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_544_, 0, v_array_535_);
lean_ctor_set(v_it_x27_544_, 1, v___x_543_);
v___x_554_ = 65;
v___x_555_ = lean_uint8_dec_le(v___x_554_, v_c_541_);
if (v___x_555_ == 0)
{
goto v___jp_549_;
}
else
{
uint8_t v___x_556_; uint8_t v___x_557_; 
v___x_556_ = 90;
v___x_557_ = lean_uint8_dec_le(v_c_541_, v___x_556_);
if (v___x_557_ == 0)
{
goto v___jp_549_;
}
else
{
lean_dec_ref(v_a_531_);
goto v___jp_545_;
}
}
v___jp_545_:
{
uint32_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = lean_uint8_to_uint32(v_c_541_);
v___x_547_ = lean_box_uint32(v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v_it_x27_544_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
return v___x_548_;
}
v___jp_549_:
{
uint8_t v___x_550_; uint8_t v___x_551_; 
v___x_550_ = 97;
v___x_551_ = lean_uint8_dec_le(v___x_550_, v_c_541_);
if (v___x_551_ == 0)
{
lean_dec_ref_known(v_it_x27_544_, 2);
goto v___jp_532_;
}
else
{
uint8_t v___x_552_; uint8_t v___x_553_; 
v___x_552_ = 122;
v___x_553_ = lean_uint8_dec_le(v_c_541_, v___x_552_);
if (v___x_553_ == 0)
{
lean_dec_ref_known(v_it_x27_544_, 2);
goto v___jp_532_;
}
else
{
lean_dec_ref(v_a_531_);
goto v___jp_545_;
}
}
}
}
v___jp_532_:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1));
v___x_534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_534_, 0, v_a_531_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(lean_object* v_it_558_){
_start:
{
lean_object* v_array_559_; lean_object* v_idx_560_; lean_object* v___x_566_; uint8_t v___x_567_; 
v_array_559_ = lean_ctor_get(v_it_558_, 0);
v_idx_560_ = lean_ctor_get(v_it_558_, 1);
v___x_566_ = lean_byte_array_size(v_array_559_);
v___x_567_ = lean_nat_dec_lt(v_idx_560_, v___x_566_);
if (v___x_567_ == 0)
{
return v_it_558_;
}
else
{
uint8_t v_b_568_; uint8_t v___x_569_; uint8_t v___x_570_; 
v_b_568_ = lean_byte_array_fget(v_array_559_, v_idx_560_);
v___x_569_ = 9;
v___x_570_ = lean_uint8_dec_eq(v_b_568_, v___x_569_);
if (v___x_570_ == 0)
{
uint8_t v___x_571_; uint8_t v___x_572_; 
v___x_571_ = 10;
v___x_572_ = lean_uint8_dec_eq(v_b_568_, v___x_571_);
if (v___x_572_ == 0)
{
uint8_t v___x_573_; uint8_t v___x_574_; 
v___x_573_ = 13;
v___x_574_ = lean_uint8_dec_eq(v_b_568_, v___x_573_);
if (v___x_574_ == 0)
{
uint8_t v___x_575_; uint8_t v___x_576_; 
v___x_575_ = 32;
v___x_576_ = lean_uint8_dec_eq(v_b_568_, v___x_575_);
if (v___x_576_ == 0)
{
return v_it_558_;
}
else
{
lean_inc(v_idx_560_);
lean_inc_ref(v_array_559_);
lean_dec_ref(v_it_558_);
goto v___jp_561_;
}
}
else
{
lean_inc(v_idx_560_);
lean_inc_ref(v_array_559_);
lean_dec_ref(v_it_558_);
goto v___jp_561_;
}
}
else
{
lean_inc(v_idx_560_);
lean_inc_ref(v_array_559_);
lean_dec_ref(v_it_558_);
goto v___jp_561_;
}
}
else
{
lean_inc(v_idx_560_);
lean_inc_ref(v_array_559_);
lean_dec_ref(v_it_558_);
goto v___jp_561_;
}
}
v___jp_561_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_idx_560_, v___x_562_);
lean_dec(v_idx_560_);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v_array_559_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v_it_558_ = v___x_564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_ws(lean_object* v_it_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(v_it_577_);
v___x_579_ = lean_box(0);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take(lean_object* v_n_581_, lean_object* v_it_582_){
_start:
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = l_ByteArray_Iterator_remainingBytes(v_it_582_);
v___x_584_ = lean_nat_dec_lt(v___x_583_, v_n_581_);
lean_dec(v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v_array_585_; lean_object* v_idx_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_605_; 
v_array_585_ = lean_ctor_get(v_it_582_, 0);
v_idx_586_ = lean_ctor_get(v_it_582_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v_it_582_);
if (v_isSharedCheck_605_ == 0)
{
v___x_588_ = v_it_582_;
v_isShared_589_ = v_isSharedCheck_605_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_idx_586_);
lean_inc(v_array_585_);
lean_dec(v_it_582_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_605_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = lean_nat_add(v_idx_586_, v_n_581_);
lean_inc(v___x_590_);
lean_inc_ref(v_array_585_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 1, v___x_590_);
v___x_592_ = v___x_588_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_array_585_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v___x_590_);
v___x_592_ = v_reuseFailAlloc_604_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v_lower_594_; lean_object* v_upper_595_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___y_601_; uint8_t v___x_603_; 
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = lean_byte_array_size(v_array_585_);
v___x_603_ = lean_nat_dec_le(v_idx_586_, v___x_598_);
if (v___x_603_ == 0)
{
v___y_601_ = v_idx_586_;
goto v___jp_600_;
}
else
{
lean_dec(v_idx_586_);
v___y_601_ = v___x_598_;
goto v___jp_600_;
}
v___jp_593_:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = l_ByteArray_toByteSlice(v_array_585_, v_lower_594_, v_upper_595_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_592_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
return v___x_597_;
}
v___jp_600_:
{
uint8_t v___x_602_; 
v___x_602_ = lean_nat_dec_le(v___x_590_, v___x_599_);
if (v___x_602_ == 0)
{
lean_dec(v___x_590_);
v_lower_594_ = v___y_601_;
v_upper_595_ = v___x_599_;
goto v___jp_593_;
}
else
{
v_lower_594_ = v___y_601_;
v_upper_595_ = v___x_590_;
goto v___jp_593_;
}
}
}
}
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_box(0);
v___x_607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_607_, 0, v_it_582_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take___boxed(lean_object* v_n_608_, lean_object* v_it_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Std_Internal_Parsec_ByteArray_take(v_n_608_, v_it_609_);
lean_dec(v_n_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(lean_object* v_pred_611_, lean_object* v_count_612_, lean_object* v_iter_613_){
_start:
{
lean_object* v_array_614_; lean_object* v_idx_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v_array_614_ = lean_ctor_get(v_iter_613_, 0);
v_idx_615_ = lean_ctor_get(v_iter_613_, 1);
v___x_616_ = lean_byte_array_size(v_array_614_);
v___x_617_ = lean_nat_dec_lt(v_idx_615_, v___x_616_);
if (v___x_617_ == 0)
{
uint8_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec_ref(v_pred_611_);
v___x_618_ = 1;
v___x_619_ = lean_box(v___x_618_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v_iter_613_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v_count_612_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
return v___x_621_;
}
else
{
uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_622_ = lean_byte_array_fget(v_array_614_, v_idx_615_);
v___x_623_ = lean_box(v___x_622_);
lean_inc_ref(v_pred_611_);
v___x_624_ = lean_apply_1(v_pred_611_, v___x_623_);
v___x_625_ = lean_unbox(v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec_ref(v_pred_611_);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v_iter_613_);
lean_ctor_set(v___x_626_, 1, v___x_624_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v_count_612_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
return v___x_627_;
}
else
{
lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_638_; 
lean_inc(v_idx_615_);
lean_inc_ref(v_array_614_);
v_isSharedCheck_638_ = !lean_is_exclusive(v_iter_613_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; lean_object* v_unused_640_; 
v_unused_639_ = lean_ctor_get(v_iter_613_, 1);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_iter_613_, 0);
lean_dec(v_unused_640_);
v___x_629_ = v_iter_613_;
v_isShared_630_ = v_isSharedCheck_638_;
goto v_resetjp_628_;
}
else
{
lean_dec(v_iter_613_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_638_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_add(v_count_612_, v___x_631_);
lean_dec(v_count_612_);
v___x_633_ = lean_nat_add(v_idx_615_, v___x_631_);
lean_dec(v_idx_615_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v___x_633_);
v___x_635_ = v___x_629_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_array_614_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v___x_633_);
v___x_635_ = v_reuseFailAlloc_637_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
v_count_612_ = v___x_632_;
v_iter_613_ = v___x_635_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object* v_pred_641_, lean_object* v_limit_642_, lean_object* v_count_643_, lean_object* v_iter_644_){
_start:
{
uint8_t v___x_645_; 
v___x_645_ = lean_nat_dec_le(v_limit_642_, v_count_643_);
if (v___x_645_ == 0)
{
lean_object* v_array_646_; lean_object* v_idx_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_array_646_ = lean_ctor_get(v_iter_644_, 0);
v_idx_647_ = lean_ctor_get(v_iter_644_, 1);
v___x_648_ = lean_byte_array_size(v_array_646_);
v___x_649_ = lean_nat_dec_lt(v_idx_647_, v___x_648_);
if (v___x_649_ == 0)
{
uint8_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec_ref(v_pred_641_);
v___x_650_ = 1;
v___x_651_ = lean_box(v___x_650_);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v_iter_644_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v_count_643_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
return v___x_653_;
}
else
{
uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_654_ = lean_byte_array_fget(v_array_646_, v_idx_647_);
v___x_655_ = lean_box(v___x_654_);
lean_inc_ref(v_pred_641_);
v___x_656_ = lean_apply_1(v_pred_641_, v___x_655_);
v___x_657_ = lean_unbox(v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec_ref(v_pred_641_);
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v_iter_644_);
lean_ctor_set(v___x_658_, 1, v___x_656_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v_count_643_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
return v___x_659_;
}
else
{
lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_670_; 
lean_inc(v_idx_647_);
lean_inc_ref(v_array_646_);
v_isSharedCheck_670_ = !lean_is_exclusive(v_iter_644_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; lean_object* v_unused_672_; 
v_unused_671_ = lean_ctor_get(v_iter_644_, 1);
lean_dec(v_unused_671_);
v_unused_672_ = lean_ctor_get(v_iter_644_, 0);
lean_dec(v_unused_672_);
v___x_661_ = v_iter_644_;
v_isShared_662_ = v_isSharedCheck_670_;
goto v_resetjp_660_;
}
else
{
lean_dec(v_iter_644_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_670_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = lean_nat_add(v_count_643_, v___x_663_);
lean_dec(v_count_643_);
v___x_665_ = lean_nat_add(v_idx_647_, v___x_663_);
lean_dec(v_idx_647_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v___x_665_);
v___x_667_ = v___x_661_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_array_646_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_669_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
v_count_643_ = v___x_664_;
v_iter_644_ = v___x_667_;
goto _start;
}
}
}
}
}
else
{
uint8_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec_ref(v_pred_641_);
v___x_673_ = 0;
v___x_674_ = lean_box(v___x_673_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_iter_644_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_count_643_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo___boxed(lean_object* v_pred_677_, lean_object* v_limit_678_, lean_object* v_count_679_, lean_object* v_iter_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_677_, v_limit_678_, v_count_679_, v_iter_680_);
lean_dec(v_limit_678_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile(lean_object* v_pred_682_, lean_object* v_it_683_){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v_snd_686_; lean_object* v_snd_687_; uint8_t v___x_688_; 
v___x_684_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_683_);
v___x_685_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v_pred_682_, v___x_684_, v_it_683_);
v_snd_686_ = lean_ctor_get(v___x_685_, 1);
lean_inc(v_snd_686_);
v_snd_687_ = lean_ctor_get(v_snd_686_, 1);
v___x_688_ = lean_unbox(v_snd_687_);
if (v___x_688_ == 0)
{
lean_object* v_fst_689_; lean_object* v_fst_690_; lean_object* v_array_691_; lean_object* v_idx_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_709_; 
v_fst_689_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_fst_689_);
lean_dec_ref(v___x_685_);
v_fst_690_ = lean_ctor_get(v_snd_686_, 0);
lean_inc(v_fst_690_);
lean_dec(v_snd_686_);
v_array_691_ = lean_ctor_get(v_it_683_, 0);
v_idx_692_ = lean_ctor_get(v_it_683_, 1);
v_isSharedCheck_709_ = !lean_is_exclusive(v_it_683_);
if (v_isSharedCheck_709_ == 0)
{
v___x_694_ = v_it_683_;
v_isShared_695_ = v_isSharedCheck_709_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_idx_692_);
lean_inc(v_array_691_);
lean_dec(v_it_683_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_709_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_lower_697_; lean_object* v_upper_698_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___y_706_; uint8_t v___x_708_; 
v___x_703_ = lean_nat_add(v_idx_692_, v_fst_689_);
lean_dec(v_fst_689_);
v___x_704_ = lean_byte_array_size(v_array_691_);
v___x_708_ = lean_nat_dec_le(v_idx_692_, v___x_684_);
if (v___x_708_ == 0)
{
v___y_706_ = v_idx_692_;
goto v___jp_705_;
}
else
{
lean_dec(v_idx_692_);
v___y_706_ = v___x_684_;
goto v___jp_705_;
}
v___jp_696_:
{
lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_699_ = l_ByteArray_toByteSlice(v_array_691_, v_lower_697_, v_upper_698_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v___x_699_);
lean_ctor_set(v___x_694_, 0, v_fst_690_);
v___x_701_ = v___x_694_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_fst_690_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
v___jp_705_:
{
uint8_t v___x_707_; 
v___x_707_ = lean_nat_dec_le(v___x_703_, v___x_704_);
if (v___x_707_ == 0)
{
lean_dec(v___x_703_);
v_lower_697_ = v___y_706_;
v_upper_698_ = v___x_704_;
goto v___jp_696_;
}
else
{
v_lower_697_ = v___y_706_;
v_upper_698_ = v___x_703_;
goto v___jp_696_;
}
}
}
}
else
{
lean_object* v_fst_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v___x_685_);
lean_dec_ref(v_it_683_);
v_fst_710_ = lean_ctor_get(v_snd_686_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v_snd_686_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v_snd_686_, 1);
lean_dec(v_unused_719_);
v___x_712_ = v_snd_686_;
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_fst_710_);
lean_dec(v_snd_686_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = lean_box(0);
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 1);
lean_ctor_set(v___x_712_, 1, v___x_714_);
v___x_716_ = v___x_712_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_fst_710_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(lean_object* v_pred_720_, uint8_t v_b_721_){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_722_ = lean_box(v_b_721_);
v___x_723_ = lean_apply_1(v_pred_720_, v___x_722_);
v___x_724_ = lean_unbox(v___x_723_);
if (v___x_724_ == 0)
{
uint8_t v___x_725_; 
v___x_725_ = 1;
return v___x_725_;
}
else
{
uint8_t v___x_726_; 
v___x_726_ = 0;
return v___x_726_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed(lean_object* v_pred_727_, lean_object* v_b_728_){
_start:
{
uint8_t v_b_boxed_729_; uint8_t v_res_730_; lean_object* v_r_731_; 
v_b_boxed_729_ = lean_unbox(v_b_728_);
v_res_730_ = l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(v_pred_727_, v_b_boxed_729_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil(lean_object* v_pred_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v_snd_737_; lean_object* v_snd_738_; uint8_t v___x_739_; 
v___f_734_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_734_, 0, v_pred_732_);
v___x_735_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_733_);
v___x_736_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v___f_734_, v___x_735_, v_a_733_);
v_snd_737_ = lean_ctor_get(v___x_736_, 1);
lean_inc(v_snd_737_);
v_snd_738_ = lean_ctor_get(v_snd_737_, 1);
v___x_739_ = lean_unbox(v_snd_738_);
if (v___x_739_ == 0)
{
lean_object* v_fst_740_; lean_object* v_fst_741_; lean_object* v_array_742_; lean_object* v_idx_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_760_; 
v_fst_740_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_fst_740_);
lean_dec_ref(v___x_736_);
v_fst_741_ = lean_ctor_get(v_snd_737_, 0);
lean_inc(v_fst_741_);
lean_dec(v_snd_737_);
v_array_742_ = lean_ctor_get(v_a_733_, 0);
v_idx_743_ = lean_ctor_get(v_a_733_, 1);
v_isSharedCheck_760_ = !lean_is_exclusive(v_a_733_);
if (v_isSharedCheck_760_ == 0)
{
v___x_745_ = v_a_733_;
v_isShared_746_ = v_isSharedCheck_760_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_idx_743_);
lean_inc(v_array_742_);
lean_dec(v_a_733_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_760_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v_lower_748_; lean_object* v_upper_749_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___y_757_; uint8_t v___x_759_; 
v___x_754_ = lean_nat_add(v_idx_743_, v_fst_740_);
lean_dec(v_fst_740_);
v___x_755_ = lean_byte_array_size(v_array_742_);
v___x_759_ = lean_nat_dec_le(v_idx_743_, v___x_735_);
if (v___x_759_ == 0)
{
v___y_757_ = v_idx_743_;
goto v___jp_756_;
}
else
{
lean_dec(v_idx_743_);
v___y_757_ = v___x_735_;
goto v___jp_756_;
}
v___jp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = l_ByteArray_toByteSlice(v_array_742_, v_lower_748_, v_upper_749_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 1, v___x_750_);
lean_ctor_set(v___x_745_, 0, v_fst_741_);
v___x_752_ = v___x_745_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_fst_741_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
v___jp_756_:
{
uint8_t v___x_758_; 
v___x_758_ = lean_nat_dec_le(v___x_754_, v___x_755_);
if (v___x_758_ == 0)
{
lean_dec(v___x_754_);
v_lower_748_ = v___y_757_;
v_upper_749_ = v___x_755_;
goto v___jp_747_;
}
else
{
v_lower_748_ = v___y_757_;
v_upper_749_ = v___x_754_;
goto v___jp_747_;
}
}
}
}
else
{
lean_object* v_fst_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_769_; 
lean_dec_ref(v___x_736_);
lean_dec_ref(v_a_733_);
v_fst_761_ = lean_ctor_get(v_snd_737_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v_snd_737_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; 
v_unused_770_ = lean_ctor_get(v_snd_737_, 1);
lean_dec(v_unused_770_);
v___x_763_ = v_snd_737_;
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_fst_761_);
lean_dec(v_snd_737_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_765_ = lean_box(0);
if (v_isShared_764_ == 0)
{
lean_ctor_set_tag(v___x_763_, 1);
lean_ctor_set(v___x_763_, 1, v___x_765_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_fst_761_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhile(lean_object* v_pred_771_, lean_object* v_it_772_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v_snd_775_; lean_object* v_snd_776_; uint8_t v___x_777_; 
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v_pred_771_, v___x_773_, v_it_772_);
v_snd_775_ = lean_ctor_get(v___x_774_, 1);
lean_inc(v_snd_775_);
lean_dec_ref(v___x_774_);
v_snd_776_ = lean_ctor_get(v_snd_775_, 1);
v___x_777_ = lean_unbox(v_snd_776_);
if (v___x_777_ == 0)
{
lean_object* v_fst_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_786_; 
v_fst_778_ = lean_ctor_get(v_snd_775_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v_snd_775_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v_snd_775_, 1);
lean_dec(v_unused_787_);
v___x_780_ = v_snd_775_;
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_fst_778_);
lean_dec(v_snd_775_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_box(0);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 1, v___x_782_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_fst_778_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_fst_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_796_; 
v_fst_788_ = lean_ctor_get(v_snd_775_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_snd_775_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v_snd_775_, 1);
lean_dec(v_unused_797_);
v___x_790_ = v_snd_775_;
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_fst_788_);
lean_dec(v_snd_775_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = lean_box(0);
if (v_isShared_791_ == 0)
{
lean_ctor_set_tag(v___x_790_, 1);
lean_ctor_set(v___x_790_, 1, v___x_792_);
v___x_794_ = v___x_790_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_fst_788_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntil(lean_object* v_pred_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___f_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v_snd_803_; lean_object* v_snd_804_; uint8_t v___x_805_; 
v___f_800_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_800_, 0, v_pred_798_);
v___x_801_ = lean_unsigned_to_nat(0u);
v___x_802_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v___f_800_, v___x_801_, v_a_799_);
v_snd_803_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_snd_803_);
lean_dec_ref(v___x_802_);
v_snd_804_ = lean_ctor_get(v_snd_803_, 1);
v___x_805_ = lean_unbox(v_snd_804_);
if (v___x_805_ == 0)
{
lean_object* v_fst_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_814_; 
v_fst_806_ = lean_ctor_get(v_snd_803_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v_snd_803_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v_snd_803_, 1);
lean_dec(v_unused_815_);
v___x_808_ = v_snd_803_;
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_fst_806_);
lean_dec(v_snd_803_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = lean_box(0);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 1, v___x_810_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_fst_806_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
else
{
lean_object* v_fst_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_824_; 
v_fst_816_ = lean_ctor_get(v_snd_803_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_snd_803_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v_snd_803_, 1);
lean_dec(v_unused_825_);
v___x_818_ = v_snd_803_;
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_fst_816_);
lean_dec(v_snd_803_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_820_ = lean_box(0);
if (v_isShared_819_ == 0)
{
lean_ctor_set_tag(v___x_818_, 1);
lean_ctor_set(v___x_818_, 1, v___x_820_);
v___x_822_ = v___x_818_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_fst_816_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(lean_object* v_pred_826_, lean_object* v_limit_827_, lean_object* v_it_828_){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v_snd_831_; lean_object* v_snd_832_; uint8_t v___x_833_; 
v___x_829_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_828_);
v___x_830_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_826_, v_limit_827_, v___x_829_, v_it_828_);
v_snd_831_ = lean_ctor_get(v___x_830_, 1);
lean_inc(v_snd_831_);
v_snd_832_ = lean_ctor_get(v_snd_831_, 1);
v___x_833_ = lean_unbox(v_snd_832_);
if (v___x_833_ == 0)
{
lean_object* v_fst_834_; lean_object* v_fst_835_; lean_object* v_array_836_; lean_object* v_idx_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_854_; 
v_fst_834_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_fst_834_);
lean_dec_ref(v___x_830_);
v_fst_835_ = lean_ctor_get(v_snd_831_, 0);
lean_inc(v_fst_835_);
lean_dec(v_snd_831_);
v_array_836_ = lean_ctor_get(v_it_828_, 0);
v_idx_837_ = lean_ctor_get(v_it_828_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v_it_828_);
if (v_isSharedCheck_854_ == 0)
{
v___x_839_ = v_it_828_;
v_isShared_840_ = v_isSharedCheck_854_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_idx_837_);
lean_inc(v_array_836_);
lean_dec(v_it_828_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_854_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v_lower_842_; lean_object* v_upper_843_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___y_851_; uint8_t v___x_853_; 
v___x_848_ = lean_nat_add(v_idx_837_, v_fst_834_);
lean_dec(v_fst_834_);
v___x_849_ = lean_byte_array_size(v_array_836_);
v___x_853_ = lean_nat_dec_le(v_idx_837_, v___x_829_);
if (v___x_853_ == 0)
{
v___y_851_ = v_idx_837_;
goto v___jp_850_;
}
else
{
lean_dec(v_idx_837_);
v___y_851_ = v___x_829_;
goto v___jp_850_;
}
v___jp_841_:
{
lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_844_ = l_ByteArray_toByteSlice(v_array_836_, v_lower_842_, v_upper_843_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v___x_844_);
lean_ctor_set(v___x_839_, 0, v_fst_835_);
v___x_846_ = v___x_839_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_fst_835_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
v___jp_850_:
{
uint8_t v___x_852_; 
v___x_852_ = lean_nat_dec_le(v___x_848_, v___x_849_);
if (v___x_852_ == 0)
{
lean_dec(v___x_848_);
v_lower_842_ = v___y_851_;
v_upper_843_ = v___x_849_;
goto v___jp_841_;
}
else
{
v_lower_842_ = v___y_851_;
v_upper_843_ = v___x_848_;
goto v___jp_841_;
}
}
}
}
else
{
lean_object* v_fst_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_863_; 
lean_dec_ref(v___x_830_);
lean_dec_ref(v_it_828_);
v_fst_855_ = lean_ctor_get(v_snd_831_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v_snd_831_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; 
v_unused_864_ = lean_ctor_get(v_snd_831_, 1);
lean_dec(v_unused_864_);
v___x_857_ = v_snd_831_;
v_isShared_858_ = v_isSharedCheck_863_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_fst_855_);
lean_dec(v_snd_831_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_863_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = lean_box(0);
if (v_isShared_858_ == 0)
{
lean_ctor_set_tag(v___x_857_, 1);
lean_ctor_set(v___x_857_, 1, v___x_859_);
v___x_861_ = v___x_857_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_fst_855_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_859_);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo___boxed(lean_object* v_pred_865_, lean_object* v_limit_866_, lean_object* v_it_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(v_pred_865_, v_limit_866_, v_it_867_);
lean_dec(v_limit_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(lean_object* v_pred_872_, lean_object* v_limit_873_, lean_object* v_it_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v_snd_877_; lean_object* v_snd_878_; uint8_t v___x_879_; 
v___x_875_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_874_);
v___x_876_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_872_, v_limit_873_, v___x_875_, v_it_874_);
v_snd_877_ = lean_ctor_get(v___x_876_, 1);
lean_inc(v_snd_877_);
v_snd_878_ = lean_ctor_get(v_snd_877_, 1);
v___x_879_ = lean_unbox(v_snd_878_);
if (v___x_879_ == 0)
{
lean_object* v_fst_880_; lean_object* v_fst_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_909_; 
v_fst_880_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_fst_880_);
lean_dec_ref(v___x_876_);
v_fst_881_ = lean_ctor_get(v_snd_877_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v_snd_877_);
if (v_isSharedCheck_909_ == 0)
{
lean_object* v_unused_910_; 
v_unused_910_ = lean_ctor_get(v_snd_877_, 1);
lean_dec(v_unused_910_);
v___x_883_ = v_snd_877_;
v_isShared_884_ = v_isSharedCheck_909_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_fst_881_);
lean_dec(v_snd_877_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_909_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
uint8_t v___x_885_; 
v___x_885_ = lean_nat_dec_eq(v_fst_880_, v___x_875_);
if (v___x_885_ == 0)
{
lean_object* v_array_886_; lean_object* v_idx_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_904_; 
lean_del_object(v___x_883_);
v_array_886_ = lean_ctor_get(v_it_874_, 0);
v_idx_887_ = lean_ctor_get(v_it_874_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v_it_874_);
if (v_isSharedCheck_904_ == 0)
{
v___x_889_ = v_it_874_;
v_isShared_890_ = v_isSharedCheck_904_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_idx_887_);
lean_inc(v_array_886_);
lean_dec(v_it_874_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_904_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_lower_892_; lean_object* v_upper_893_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___y_901_; uint8_t v___x_903_; 
v___x_898_ = lean_nat_add(v_idx_887_, v_fst_880_);
lean_dec(v_fst_880_);
v___x_899_ = lean_byte_array_size(v_array_886_);
v___x_903_ = lean_nat_dec_le(v_idx_887_, v___x_875_);
if (v___x_903_ == 0)
{
v___y_901_ = v_idx_887_;
goto v___jp_900_;
}
else
{
lean_dec(v_idx_887_);
v___y_901_ = v___x_875_;
goto v___jp_900_;
}
v___jp_891_:
{
lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_894_ = l_ByteArray_toByteSlice(v_array_886_, v_lower_892_, v_upper_893_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 1, v___x_894_);
lean_ctor_set(v___x_889_, 0, v_fst_881_);
v___x_896_ = v___x_889_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_fst_881_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
v___jp_900_:
{
uint8_t v___x_902_; 
v___x_902_ = lean_nat_dec_le(v___x_898_, v___x_899_);
if (v___x_902_ == 0)
{
lean_dec(v___x_898_);
v_lower_892_ = v___y_901_;
v_upper_893_ = v___x_899_;
goto v___jp_891_;
}
else
{
v_lower_892_ = v___y_901_;
v_upper_893_ = v___x_898_;
goto v___jp_891_;
}
}
}
}
else
{
lean_object* v___x_905_; lean_object* v___x_907_; 
lean_dec(v_fst_881_);
lean_dec(v_fst_880_);
v___x_905_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1));
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 1);
lean_ctor_set(v___x_883_, 1, v___x_905_);
lean_ctor_set(v___x_883_, 0, v_it_874_);
v___x_907_ = v___x_883_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_it_874_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v___x_905_);
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
else
{
lean_object* v_fst_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v___x_876_);
lean_dec_ref(v_it_874_);
v_fst_911_ = lean_ctor_get(v_snd_877_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v_snd_877_);
if (v_isSharedCheck_919_ == 0)
{
lean_object* v_unused_920_; 
v_unused_920_ = lean_ctor_get(v_snd_877_, 1);
lean_dec(v_unused_920_);
v___x_913_ = v_snd_877_;
v_isShared_914_ = v_isSharedCheck_919_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_fst_911_);
lean_dec(v_snd_877_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_919_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_915_ = lean_box(0);
if (v_isShared_914_ == 0)
{
lean_ctor_set_tag(v___x_913_, 1);
lean_ctor_set(v___x_913_, 1, v___x_915_);
v___x_917_ = v___x_913_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_fst_911_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v___x_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___boxed(lean_object* v_pred_921_, lean_object* v_limit_922_, lean_object* v_it_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(v_pred_921_, v_limit_922_, v_it_923_);
lean_dec(v_limit_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(lean_object* v_pred_925_, lean_object* v_limit_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___f_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v_snd_931_; lean_object* v_snd_932_; uint8_t v___x_933_; 
v___f_928_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_928_, 0, v_pred_925_);
v___x_929_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_927_);
v___x_930_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_928_, v_limit_926_, v___x_929_, v_a_927_);
v_snd_931_ = lean_ctor_get(v___x_930_, 1);
lean_inc(v_snd_931_);
v_snd_932_ = lean_ctor_get(v_snd_931_, 1);
v___x_933_ = lean_unbox(v_snd_932_);
if (v___x_933_ == 0)
{
lean_object* v_fst_934_; lean_object* v_fst_935_; lean_object* v_array_936_; lean_object* v_idx_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_954_; 
v_fst_934_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_fst_934_);
lean_dec_ref(v___x_930_);
v_fst_935_ = lean_ctor_get(v_snd_931_, 0);
lean_inc(v_fst_935_);
lean_dec(v_snd_931_);
v_array_936_ = lean_ctor_get(v_a_927_, 0);
v_idx_937_ = lean_ctor_get(v_a_927_, 1);
v_isSharedCheck_954_ = !lean_is_exclusive(v_a_927_);
if (v_isSharedCheck_954_ == 0)
{
v___x_939_ = v_a_927_;
v_isShared_940_ = v_isSharedCheck_954_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_idx_937_);
lean_inc(v_array_936_);
lean_dec(v_a_927_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_954_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_lower_942_; lean_object* v_upper_943_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___y_951_; uint8_t v___x_953_; 
v___x_948_ = lean_nat_add(v_idx_937_, v_fst_934_);
lean_dec(v_fst_934_);
v___x_949_ = lean_byte_array_size(v_array_936_);
v___x_953_ = lean_nat_dec_le(v_idx_937_, v___x_929_);
if (v___x_953_ == 0)
{
v___y_951_ = v_idx_937_;
goto v___jp_950_;
}
else
{
lean_dec(v_idx_937_);
v___y_951_ = v___x_929_;
goto v___jp_950_;
}
v___jp_941_:
{
lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_944_ = l_ByteArray_toByteSlice(v_array_936_, v_lower_942_, v_upper_943_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_944_);
lean_ctor_set(v___x_939_, 0, v_fst_935_);
v___x_946_ = v___x_939_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_fst_935_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
v___jp_950_:
{
uint8_t v___x_952_; 
v___x_952_ = lean_nat_dec_le(v___x_948_, v___x_949_);
if (v___x_952_ == 0)
{
lean_dec(v___x_948_);
v_lower_942_ = v___y_951_;
v_upper_943_ = v___x_949_;
goto v___jp_941_;
}
else
{
v_lower_942_ = v___y_951_;
v_upper_943_ = v___x_948_;
goto v___jp_941_;
}
}
}
}
else
{
lean_object* v_fst_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref(v___x_930_);
lean_dec_ref(v_a_927_);
v_fst_955_ = lean_ctor_get(v_snd_931_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v_snd_931_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; 
v_unused_964_ = lean_ctor_get(v_snd_931_, 1);
lean_dec(v_unused_964_);
v___x_957_ = v_snd_931_;
v_isShared_958_ = v_isSharedCheck_963_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_fst_955_);
lean_dec(v_snd_931_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_963_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = lean_box(0);
if (v_isShared_958_ == 0)
{
lean_ctor_set_tag(v___x_957_, 1);
lean_ctor_set(v___x_957_, 1, v___x_959_);
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_fst_955_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo___boxed(lean_object* v_pred_965_, lean_object* v_limit_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(v_pred_965_, v_limit_966_, v_a_967_);
lean_dec(v_limit_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileAtMost(lean_object* v_pred_969_, lean_object* v_limit_970_, lean_object* v_it_971_){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v_snd_974_; lean_object* v_fst_975_; lean_object* v_fst_976_; lean_object* v_array_977_; lean_object* v_idx_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_995_; 
v___x_972_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_971_);
v___x_973_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_969_, v_limit_970_, v___x_972_, v_it_971_);
v_snd_974_ = lean_ctor_get(v___x_973_, 1);
lean_inc(v_snd_974_);
v_fst_975_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_fst_975_);
lean_dec_ref(v___x_973_);
v_fst_976_ = lean_ctor_get(v_snd_974_, 0);
lean_inc(v_fst_976_);
lean_dec(v_snd_974_);
v_array_977_ = lean_ctor_get(v_it_971_, 0);
v_idx_978_ = lean_ctor_get(v_it_971_, 1);
v_isSharedCheck_995_ = !lean_is_exclusive(v_it_971_);
if (v_isSharedCheck_995_ == 0)
{
v___x_980_ = v_it_971_;
v_isShared_981_ = v_isSharedCheck_995_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_idx_978_);
lean_inc(v_array_977_);
lean_dec(v_it_971_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_995_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v_lower_983_; lean_object* v_upper_984_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___y_992_; uint8_t v___x_994_; 
v___x_989_ = lean_nat_add(v_idx_978_, v_fst_975_);
lean_dec(v_fst_975_);
v___x_990_ = lean_byte_array_size(v_array_977_);
v___x_994_ = lean_nat_dec_le(v_idx_978_, v___x_972_);
if (v___x_994_ == 0)
{
v___y_992_ = v_idx_978_;
goto v___jp_991_;
}
else
{
lean_dec(v_idx_978_);
v___y_992_ = v___x_972_;
goto v___jp_991_;
}
v___jp_982_:
{
lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_985_ = l_ByteArray_toByteSlice(v_array_977_, v_lower_983_, v_upper_984_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v___x_985_);
lean_ctor_set(v___x_980_, 0, v_fst_976_);
v___x_987_ = v___x_980_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_fst_976_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
v___jp_991_:
{
uint8_t v___x_993_; 
v___x_993_ = lean_nat_dec_le(v___x_989_, v___x_990_);
if (v___x_993_ == 0)
{
lean_dec(v___x_989_);
v_lower_983_ = v___y_992_;
v_upper_984_ = v___x_990_;
goto v___jp_982_;
}
else
{
v_lower_983_ = v___y_992_;
v_upper_984_ = v___x_989_;
goto v___jp_982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileAtMost___boxed(lean_object* v_pred_996_, lean_object* v_limit_997_, lean_object* v_it_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Std_Internal_Parsec_ByteArray_takeWhileAtMost(v_pred_996_, v_limit_997_, v_it_998_);
lean_dec(v_limit_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost(lean_object* v_pred_1000_, lean_object* v_limit_1001_, lean_object* v_it_1002_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v_snd_1005_; lean_object* v_fst_1006_; lean_object* v_fst_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1035_; 
v___x_1003_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_1002_);
v___x_1004_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_1000_, v_limit_1001_, v___x_1003_, v_it_1002_);
v_snd_1005_ = lean_ctor_get(v___x_1004_, 1);
lean_inc(v_snd_1005_);
v_fst_1006_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_fst_1006_);
lean_dec_ref(v___x_1004_);
v_fst_1007_ = lean_ctor_get(v_snd_1005_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_snd_1005_);
if (v_isSharedCheck_1035_ == 0)
{
lean_object* v_unused_1036_; 
v_unused_1036_ = lean_ctor_get(v_snd_1005_, 1);
lean_dec(v_unused_1036_);
v___x_1009_ = v_snd_1005_;
v_isShared_1010_ = v_isSharedCheck_1035_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_fst_1007_);
lean_dec(v_snd_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1035_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
uint8_t v___x_1011_; 
v___x_1011_ = lean_nat_dec_eq(v_fst_1006_, v___x_1003_);
if (v___x_1011_ == 0)
{
lean_object* v_array_1012_; lean_object* v_idx_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1030_; 
lean_del_object(v___x_1009_);
v_array_1012_ = lean_ctor_get(v_it_1002_, 0);
v_idx_1013_ = lean_ctor_get(v_it_1002_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_it_1002_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1015_ = v_it_1002_;
v_isShared_1016_ = v_isSharedCheck_1030_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_idx_1013_);
lean_inc(v_array_1012_);
lean_dec(v_it_1002_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1030_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v_lower_1018_; lean_object* v_upper_1019_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___y_1027_; uint8_t v___x_1029_; 
v___x_1024_ = lean_nat_add(v_idx_1013_, v_fst_1006_);
lean_dec(v_fst_1006_);
v___x_1025_ = lean_byte_array_size(v_array_1012_);
v___x_1029_ = lean_nat_dec_le(v_idx_1013_, v___x_1003_);
if (v___x_1029_ == 0)
{
v___y_1027_ = v_idx_1013_;
goto v___jp_1026_;
}
else
{
lean_dec(v_idx_1013_);
v___y_1027_ = v___x_1003_;
goto v___jp_1026_;
}
v___jp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1020_ = l_ByteArray_toByteSlice(v_array_1012_, v_lower_1018_, v_upper_1019_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 1, v___x_1020_);
lean_ctor_set(v___x_1015_, 0, v_fst_1007_);
v___x_1022_ = v___x_1015_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_fst_1007_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
v___jp_1026_:
{
uint8_t v___x_1028_; 
v___x_1028_ = lean_nat_dec_le(v___x_1024_, v___x_1025_);
if (v___x_1028_ == 0)
{
lean_dec(v___x_1024_);
v_lower_1018_ = v___y_1027_;
v_upper_1019_ = v___x_1025_;
goto v___jp_1017_;
}
else
{
v_lower_1018_ = v___y_1027_;
v_upper_1019_ = v___x_1024_;
goto v___jp_1017_;
}
}
}
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
lean_dec(v_fst_1007_);
lean_dec(v_fst_1006_);
v___x_1031_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1));
if (v_isShared_1010_ == 0)
{
lean_ctor_set_tag(v___x_1009_, 1);
lean_ctor_set(v___x_1009_, 1, v___x_1031_);
lean_ctor_set(v___x_1009_, 0, v_it_1002_);
v___x_1033_ = v___x_1009_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_it_1002_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost___boxed(lean_object* v_pred_1037_, lean_object* v_limit_1038_, lean_object* v_it_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost(v_pred_1037_, v_limit_1038_, v_it_1039_);
lean_dec(v_limit_1038_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(lean_object* v_pred_1041_, lean_object* v_limit_1042_, lean_object* v_it_1043_){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v_snd_1046_; lean_object* v_snd_1047_; uint8_t v___x_1048_; 
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_1041_, v_limit_1042_, v___x_1044_, v_it_1043_);
v_snd_1046_ = lean_ctor_get(v___x_1045_, 1);
lean_inc(v_snd_1046_);
lean_dec_ref(v___x_1045_);
v_snd_1047_ = lean_ctor_get(v_snd_1046_, 1);
v___x_1048_ = lean_unbox(v_snd_1047_);
if (v___x_1048_ == 0)
{
lean_object* v_fst_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1057_; 
v_fst_1049_ = lean_ctor_get(v_snd_1046_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_snd_1046_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v_snd_1046_, 1);
lean_dec(v_unused_1058_);
v___x_1051_ = v_snd_1046_;
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_fst_1049_);
lean_dec(v_snd_1046_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1053_ = lean_box(0);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 1, v___x_1053_);
v___x_1055_ = v___x_1051_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_fst_1049_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
else
{
lean_object* v_fst_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1067_; 
v_fst_1059_ = lean_ctor_get(v_snd_1046_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_snd_1046_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v_snd_1046_, 1);
lean_dec(v_unused_1068_);
v___x_1061_ = v_snd_1046_;
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_fst_1059_);
lean_dec(v_snd_1046_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1063_ = lean_box(0);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 1);
lean_ctor_set(v___x_1061_, 1, v___x_1063_);
v___x_1065_ = v___x_1061_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_fst_1059_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhileUpTo___boxed(lean_object* v_pred_1069_, lean_object* v_limit_1070_, lean_object* v_it_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(v_pred_1069_, v_limit_1070_, v_it_1071_);
lean_dec(v_limit_1070_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(lean_object* v_pred_1073_, lean_object* v_limit_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v___f_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v_snd_1079_; lean_object* v_snd_1080_; uint8_t v___x_1081_; 
v___f_1076_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1076_, 0, v_pred_1073_);
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1078_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1076_, v_limit_1074_, v___x_1077_, v_a_1075_);
v_snd_1079_ = lean_ctor_get(v___x_1078_, 1);
lean_inc(v_snd_1079_);
lean_dec_ref(v___x_1078_);
v_snd_1080_ = lean_ctor_get(v_snd_1079_, 1);
v___x_1081_ = lean_unbox(v_snd_1080_);
if (v___x_1081_ == 0)
{
lean_object* v_fst_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1090_; 
v_fst_1082_ = lean_ctor_get(v_snd_1079_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_snd_1079_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v_snd_1079_, 1);
lean_dec(v_unused_1091_);
v___x_1084_ = v_snd_1079_;
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_fst_1082_);
lean_dec(v_snd_1079_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1086_ = lean_box(0);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 1, v___x_1086_);
v___x_1088_ = v___x_1084_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_fst_1082_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
else
{
lean_object* v_fst_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1100_; 
v_fst_1092_ = lean_ctor_get(v_snd_1079_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_snd_1079_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v_snd_1079_, 1);
lean_dec(v_unused_1101_);
v___x_1094_ = v_snd_1079_;
v_isShared_1095_ = v_isSharedCheck_1100_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_fst_1092_);
lean_dec(v_snd_1079_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1100_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1096_ = lean_box(0);
if (v_isShared_1095_ == 0)
{
lean_ctor_set_tag(v___x_1094_, 1);
lean_ctor_set(v___x_1094_, 1, v___x_1096_);
v___x_1098_ = v___x_1094_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_fst_1092_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntilUpTo___boxed(lean_object* v_pred_1102_, lean_object* v_limit_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(v_pred_1102_, v_limit_1103_, v_a_1104_);
lean_dec(v_limit_1103_);
return v_res_1105_;
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
