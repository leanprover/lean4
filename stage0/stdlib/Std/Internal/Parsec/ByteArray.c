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
uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2(lean_object* v_it_17_){
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
LEAN_EXPORT void l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_it_17_ = stack[0].m_obj;
uint8_t v_res_24_;
v_res_24_ = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2(v_it_17_);
stack->m_num = v_res_24_;
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___boxed(lean_object* v_it_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2(v_it_25_);
lean_dec_ref(v_it_25_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3(lean_object* v_it_28_){
_start:
{
lean_object* v_array_29_; lean_object* v_idx_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v_array_29_ = lean_ctor_get(v_it_28_, 0);
v_idx_30_ = lean_ctor_get(v_it_28_, 1);
v___x_31_ = lean_byte_array_size(v_array_29_);
v___x_32_ = lean_nat_dec_lt(v_idx_30_, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT void l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_it_28_ = stack[0].m_obj;
uint8_t v_res_33_;
v_res_33_ = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3(v_it_28_);
stack->m_num = v_res_33_;
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3___boxed(lean_object* v_it_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3(v_it_34_);
lean_dec_ref(v_it_34_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__4(lean_object* v_it_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_array_39_; lean_object* v_idx_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_49_; 
v_array_39_ = lean_ctor_get(v_it_37_, 0);
v_idx_40_ = lean_ctor_get(v_it_37_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v_it_37_);
if (v_isSharedCheck_49_ == 0)
{
v___x_42_ = v_it_37_;
v_isShared_43_ = v_isSharedCheck_49_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_idx_40_);
lean_inc(v_array_39_);
lean_dec(v_it_37_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_49_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_47_; 
v___x_44_ = lean_unsigned_to_nat(1u);
v___x_45_ = lean_nat_add(v_idx_40_, v___x_44_);
lean_dec(v_idx_40_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v___x_45_);
v___x_47_ = v___x_42_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_array_39_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v___x_45_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5(lean_object* v_it_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_array_52_; lean_object* v_idx_53_; uint8_t v___x_54_; 
v_array_52_ = lean_ctor_get(v_it_50_, 0);
v_idx_53_ = lean_ctor_get(v_it_50_, 1);
v___x_54_ = lean_byte_array_fget(v_array_52_, v_idx_53_);
return v___x_54_;
}
}
LEAN_EXPORT void l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_it_50_ = stack[0].m_obj;
uint8_t v_res_55_;
v_res_55_ = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5(v_it_50_, lean_box(0));
stack->m_num = v_res_55_;
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5___boxed(lean_object* v_it_56_, lean_object* v___y_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5(v_it_56_, v___y_57_);
lean_dec_ref(v_it_56_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object* v_p_77_, lean_object* v_arr_78_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = l_ByteArray_mkIterator(v_arr_78_);
v___x_80_ = lean_apply_1(v_p_77_, v___x_79_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v_res_81_; lean_object* v___x_82_; 
v_res_81_ = lean_ctor_get(v___x_80_, 1);
lean_inc(v_res_81_);
lean_dec_ref_known(v___x_80_, 2);
v___x_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_82_, 0, v_res_81_);
return v___x_82_;
}
else
{
lean_object* v_pos_83_; lean_object* v_err_84_; lean_object* v_idx_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___y_96_; 
v_pos_83_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_pos_83_);
v_err_84_ = lean_ctor_get(v___x_80_, 1);
lean_inc(v_err_84_);
lean_dec_ref_known(v___x_80_, 2);
v_idx_85_ = lean_ctor_get(v_pos_83_, 1);
lean_inc(v_idx_85_);
lean_dec(v_pos_83_);
v___x_86_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__0));
v___x_87_ = l_Nat_reprFast(v_idx_85_);
v___x_88_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
v___x_89_ = l_Std_Format_defWidth;
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = l_Std_Format_pretty(v___x_88_, v___x_89_, v___x_90_, v___x_90_);
v___x_92_ = lean_string_append(v___x_86_, v___x_91_);
lean_dec_ref(v___x_91_);
v___x_93_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__1));
v___x_94_ = lean_string_append(v___x_92_, v___x_93_);
if (lean_obj_tag(v_err_84_) == 0)
{
lean_object* v___x_99_; 
v___x_99_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__2));
v___y_96_ = v___x_99_;
goto v___jp_95_;
}
else
{
lean_object* v_s_100_; 
v_s_100_ = lean_ctor_get(v_err_84_, 0);
lean_inc_ref(v_s_100_);
lean_dec_ref_known(v_err_84_, 1);
v___y_96_ = v_s_100_;
goto v___jp_95_;
}
v___jp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_string_append(v___x_94_, v___y_96_);
lean_dec_ref(v___y_96_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run(lean_object* v_00_u03b1_101_, lean_object* v_p_102_, lean_object* v_arr_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v_p_102_, v_arr_103_);
return v___x_104_;
}
}
lean_object* l_Std_Internal_Parsec_ByteArray_pbyte(uint8_t v_b_107_, lean_object* v_it_108_){
_start:
{
lean_object* v_array_109_; lean_object* v_idx_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_array_109_ = lean_ctor_get(v_it_108_, 0);
v_idx_110_ = lean_ctor_get(v_it_108_, 1);
v___x_111_ = lean_byte_array_size(v_array_109_);
v___x_112_ = lean_nat_dec_lt(v_idx_110_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_box(0);
v___x_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_114_, 0, v_it_108_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
return v___x_114_;
}
else
{
uint8_t v_got_115_; uint8_t v___x_116_; 
v_got_115_ = lean_byte_array_fget(v_array_109_, v_idx_110_);
v___x_116_ = lean_uint8_dec_eq(v_got_115_, v_b_107_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_117_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0));
v___x_118_ = lean_uint8_to_nat(v_b_107_);
v___x_119_ = l_Nat_reprFast(v___x_118_);
v___x_120_ = lean_string_append(v___x_117_, v___x_119_);
lean_dec_ref(v___x_119_);
v___x_121_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1));
v___x_122_ = lean_string_append(v___x_120_, v___x_121_);
v___x_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
v___x_124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_124_, 0, v_it_108_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
return v___x_124_;
}
else
{
lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_135_; 
lean_inc(v_idx_110_);
lean_inc_ref(v_array_109_);
v_isSharedCheck_135_ = !lean_is_exclusive(v_it_108_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; lean_object* v_unused_137_; 
v_unused_136_ = lean_ctor_get(v_it_108_, 1);
lean_dec(v_unused_136_);
v_unused_137_ = lean_ctor_get(v_it_108_, 0);
lean_dec(v_unused_137_);
v___x_126_ = v_it_108_;
v_isShared_127_ = v_isSharedCheck_135_;
goto v_resetjp_125_;
}
else
{
lean_dec(v_it_108_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_135_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = lean_nat_add(v_idx_110_, v___x_128_);
lean_dec(v_idx_110_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v___x_129_);
v___x_131_ = v___x_126_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_array_109_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v___x_129_);
v___x_131_ = v_reuseFailAlloc_134_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_box(v_got_115_);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
return v___x_133_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Internal_Parsec_ByteArray_pbyte_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_107_ = stack[0].m_num;
lean_object* v_it_108_ = stack[1].m_obj;
lean_object* v_res_138_;
v_res_138_ = l_Std_Internal_Parsec_ByteArray_pbyte(v_b_107_, v_it_108_);
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pbyte___boxed(lean_object* v_b_139_, lean_object* v_it_140_){
_start:
{
uint8_t v_b_boxed_141_; lean_object* v_res_142_; 
v_b_boxed_141_ = lean_unbox(v_b_139_);
v_res_142_ = l_Std_Internal_Parsec_ByteArray_pbyte(v_b_boxed_141_, v_it_140_);
return v_res_142_;
}
}
lean_object* l_Std_Internal_Parsec_ByteArray_skipByte(uint8_t v_b_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_array_145_; lean_object* v_idx_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v_array_145_ = lean_ctor_get(v_a_144_, 0);
v_idx_146_ = lean_ctor_get(v_a_144_, 1);
v___x_147_ = lean_byte_array_size(v_array_145_);
v___x_148_ = lean_nat_dec_lt(v_idx_146_, v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_box(0);
v___x_150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_150_, 0, v_a_144_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
return v___x_150_;
}
else
{
uint8_t v_got_151_; uint8_t v___x_152_; 
v_got_151_ = lean_byte_array_fget(v_array_145_, v_idx_146_);
v___x_152_ = lean_uint8_dec_eq(v_got_151_, v_b_143_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_153_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0));
v___x_154_ = lean_uint8_to_nat(v_b_143_);
v___x_155_ = l_Nat_reprFast(v___x_154_);
v___x_156_ = lean_string_append(v___x_153_, v___x_155_);
lean_dec_ref(v___x_155_);
v___x_157_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1));
v___x_158_ = lean_string_append(v___x_156_, v___x_157_);
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
v___x_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_160_, 0, v_a_144_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
return v___x_160_;
}
else
{
lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_171_; 
lean_inc(v_idx_146_);
lean_inc_ref(v_array_145_);
v_isSharedCheck_171_ = !lean_is_exclusive(v_a_144_);
if (v_isSharedCheck_171_ == 0)
{
lean_object* v_unused_172_; lean_object* v_unused_173_; 
v_unused_172_ = lean_ctor_get(v_a_144_, 1);
lean_dec(v_unused_172_);
v_unused_173_ = lean_ctor_get(v_a_144_, 0);
lean_dec(v_unused_173_);
v___x_162_ = v_a_144_;
v_isShared_163_ = v_isSharedCheck_171_;
goto v_resetjp_161_;
}
else
{
lean_dec(v_a_144_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_171_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_164_ = lean_unsigned_to_nat(1u);
v___x_165_ = lean_nat_add(v_idx_146_, v___x_164_);
lean_dec(v_idx_146_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 1, v___x_165_);
v___x_167_ = v___x_162_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_array_145_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___x_165_);
v___x_167_ = v_reuseFailAlloc_170_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_box(0);
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
return v___x_169_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Internal_Parsec_ByteArray_skipByte_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_143_ = stack[0].m_num;
lean_object* v_a_144_ = stack[1].m_obj;
lean_object* v_res_174_;
v_res_174_ = l_Std_Internal_Parsec_ByteArray_skipByte(v_b_143_, v_a_144_);
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByte___boxed(lean_object* v_b_175_, lean_object* v_a_176_){
_start:
{
uint8_t v_b_boxed_177_; lean_object* v_res_178_; 
v_b_boxed_177_ = lean_unbox(v_b_175_);
v_res_178_ = l_Std_Internal_Parsec_ByteArray_skipByte(v_b_boxed_177_, v_a_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go(lean_object* v_arr_181_, lean_object* v_idx_182_, lean_object* v_it_183_){
_start:
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_byte_array_size(v_arr_181_);
v___x_185_ = lean_nat_dec_lt(v_idx_182_, v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec(v_idx_182_);
v___x_186_ = lean_box(0);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v_it_183_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
return v___x_187_;
}
else
{
lean_object* v_array_188_; lean_object* v_idx_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v_array_188_ = lean_ctor_get(v_it_183_, 0);
v_idx_189_ = lean_ctor_get(v_it_183_, 1);
v___x_190_ = lean_byte_array_size(v_array_188_);
v___x_191_ = lean_nat_dec_lt(v_idx_189_, v___x_190_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; 
lean_dec(v_idx_182_);
v___x_192_ = lean_box(0);
v___x_193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_193_, 0, v_it_183_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
return v___x_193_;
}
else
{
uint8_t v_got_194_; uint8_t v_want_195_; uint8_t v___x_196_; 
v_got_194_ = lean_byte_array_fget(v_array_188_, v_idx_189_);
v_want_195_ = lean_byte_array_fget(v_arr_181_, v_idx_182_);
v___x_196_ = lean_uint8_dec_eq(v_got_194_, v_want_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec(v_idx_182_);
v___x_197_ = ((lean_object*)(l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__0));
v___x_198_ = lean_uint8_to_nat(v_want_195_);
v___x_199_ = l_Nat_reprFast(v___x_198_);
v___x_200_ = lean_string_append(v___x_197_, v___x_199_);
lean_dec_ref(v___x_199_);
v___x_201_ = ((lean_object*)(l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__1));
v___x_202_ = lean_string_append(v___x_200_, v___x_201_);
v___x_203_ = lean_uint8_to_nat(v_got_194_);
v___x_204_ = l_Nat_reprFast(v___x_203_);
v___x_205_ = lean_string_append(v___x_202_, v___x_204_);
lean_dec_ref(v___x_204_);
v___x_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
v___x_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_207_, 0, v_it_183_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
return v___x_207_;
}
else
{
lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_218_; 
lean_inc(v_idx_189_);
lean_inc_ref(v_array_188_);
v_isSharedCheck_218_ = !lean_is_exclusive(v_it_183_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; lean_object* v_unused_220_; 
v_unused_219_ = lean_ctor_get(v_it_183_, 1);
lean_dec(v_unused_219_);
v_unused_220_ = lean_ctor_get(v_it_183_, 0);
lean_dec(v_unused_220_);
v___x_209_ = v_it_183_;
v_isShared_210_ = v_isSharedCheck_218_;
goto v_resetjp_208_;
}
else
{
lean_dec(v_it_183_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_218_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_add(v_idx_182_, v___x_211_);
lean_dec(v_idx_182_);
v___x_213_ = lean_nat_add(v_idx_189_, v___x_211_);
lean_dec(v_idx_189_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v___x_213_);
v___x_215_ = v___x_209_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_array_188_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___x_213_);
v___x_215_ = v_reuseFailAlloc_217_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
v_idx_182_ = v___x_212_;
v_it_183_ = v___x_215_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___boxed(lean_object* v_arr_221_, lean_object* v_idx_222_, lean_object* v_it_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go(v_arr_221_, v_idx_222_, v_it_223_);
lean_dec_ref(v_arr_221_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object* v_arr_225_, lean_object* v_it_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go(v_arr_225_, v___x_227_, v_it_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes___boxed(lean_object* v_arr_229_, lean_object* v_it_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_arr_229_, v_it_230_);
lean_dec_ref(v_arr_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pstring(lean_object* v_s_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_utf8_234_; lean_object* v___x_235_; 
v_utf8_234_ = lean_string_to_utf8(v_s_232_);
v___x_235_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_234_, v_a_233_);
lean_dec_ref(v_utf8_234_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_pos_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
v_pos_236_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; 
v_unused_244_ = lean_ctor_get(v___x_235_, 1);
lean_dec(v_unused_244_);
v___x_238_ = v___x_235_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_pos_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v_s_232_);
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_pos_236_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_s_232_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
else
{
lean_object* v_pos_245_; lean_object* v_err_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec_ref(v_s_232_);
v_pos_245_ = lean_ctor_get(v___x_235_, 0);
v_err_246_ = lean_ctor_get(v___x_235_, 1);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_235_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_err_246_);
lean_inc(v_pos_245_);
lean_dec(v___x_235_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_pos_245_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_err_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipString(lean_object* v_s_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_utf8_256_; lean_object* v___x_257_; 
v_utf8_256_ = lean_string_to_utf8(v_s_254_);
v___x_257_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_256_, v_a_255_);
lean_dec_ref(v_utf8_256_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_pos_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_266_; 
v_pos_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; 
v_unused_267_ = lean_ctor_get(v___x_257_, 1);
lean_dec(v_unused_267_);
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_pos_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_box(0);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 1, v___x_262_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_pos_258_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
else
{
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipString___boxed(lean_object* v_s_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Std_Internal_Parsec_ByteArray_skipString(v_s_268_, v_a_269_);
lean_dec_ref(v_s_268_);
return v_res_270_;
}
}
lean_object* l_Std_Internal_Parsec_ByteArray_pByteChar(uint32_t v_c_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_array_274_; lean_object* v_idx_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v_array_274_ = lean_ctor_get(v_a_273_, 0);
v_idx_275_ = lean_ctor_get(v_a_273_, 1);
v___x_276_ = lean_byte_array_size(v_array_274_);
v___x_277_ = lean_nat_dec_lt(v_idx_275_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_box(0);
v___x_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_279_, 0, v_a_273_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
return v___x_279_;
}
else
{
uint8_t v_c_280_; uint8_t v___x_281_; uint8_t v___x_282_; 
v_c_280_ = lean_byte_array_fget(v_array_274_, v_idx_275_);
v___x_281_ = lean_uint32_to_uint8(v_c_272_);
v___x_282_ = lean_uint8_dec_eq(v_c_280_, v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_283_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0));
v___x_284_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0));
v___x_285_ = lean_string_push(v___x_284_, v_c_272_);
v___x_286_ = lean_string_append(v___x_283_, v___x_285_);
lean_dec_ref(v___x_285_);
v___x_287_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1));
v___x_288_ = lean_string_append(v___x_286_, v___x_287_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
v___x_290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_290_, 0, v_a_273_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
return v___x_290_;
}
else
{
lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_301_; 
lean_inc(v_idx_275_);
lean_inc_ref(v_array_274_);
v_isSharedCheck_301_ = !lean_is_exclusive(v_a_273_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; lean_object* v_unused_303_; 
v_unused_302_ = lean_ctor_get(v_a_273_, 1);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_a_273_, 0);
lean_dec(v_unused_303_);
v___x_292_ = v_a_273_;
v_isShared_293_ = v_isSharedCheck_301_;
goto v_resetjp_291_;
}
else
{
lean_dec(v_a_273_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_301_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v_it_x27_297_; 
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = lean_nat_add(v_idx_275_, v___x_294_);
lean_dec(v_idx_275_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v___x_295_);
v_it_x27_297_ = v___x_292_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_array_274_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v___x_295_);
v_it_x27_297_ = v_reuseFailAlloc_300_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_box_uint32(v_c_272_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_it_x27_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
return v___x_299_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Internal_Parsec_ByteArray_pByteChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_272_ = stack[0].m_num;
lean_object* v_a_273_ = stack[1].m_obj;
lean_object* v_res_304_;
v_res_304_ = l_Std_Internal_Parsec_ByteArray_pByteChar(v_c_272_, v_a_273_);
stack->m_obj
 = v_res_304_;
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pByteChar___boxed(lean_object* v_c_305_, lean_object* v_a_306_){
_start:
{
uint32_t v_c_boxed_307_; lean_object* v_res_308_; 
v_c_boxed_307_ = lean_unbox_uint32(v_c_305_);
lean_dec(v_c_305_);
v_res_308_ = l_Std_Internal_Parsec_ByteArray_pByteChar(v_c_boxed_307_, v_a_306_);
return v_res_308_;
}
}
lean_object* l_Std_Internal_Parsec_ByteArray_skipByteChar(uint32_t v_c_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_array_311_; lean_object* v_idx_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v_array_311_ = lean_ctor_get(v_a_310_, 0);
v_idx_312_ = lean_ctor_get(v_a_310_, 1);
v___x_313_ = lean_byte_array_size(v_array_311_);
v___x_314_ = lean_nat_dec_lt(v_idx_312_, v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_box(0);
v___x_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_316_, 0, v_a_310_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
return v___x_316_;
}
else
{
uint8_t v___x_317_; uint8_t v_got_318_; uint8_t v___x_319_; 
v___x_317_ = lean_uint32_to_uint8(v_c_309_);
v_got_318_ = lean_byte_array_fget(v_array_311_, v_idx_312_);
v___x_319_ = lean_uint8_dec_eq(v_got_318_, v___x_317_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_320_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0));
v___x_321_ = lean_uint8_to_nat(v___x_317_);
v___x_322_ = l_Nat_reprFast(v___x_321_);
v___x_323_ = lean_string_append(v___x_320_, v___x_322_);
lean_dec_ref(v___x_322_);
v___x_324_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1));
v___x_325_ = lean_string_append(v___x_323_, v___x_324_);
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
v___x_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_327_, 0, v_a_310_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
return v___x_327_;
}
else
{
lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_338_; 
lean_inc(v_idx_312_);
lean_inc_ref(v_array_311_);
v_isSharedCheck_338_ = !lean_is_exclusive(v_a_310_);
if (v_isSharedCheck_338_ == 0)
{
lean_object* v_unused_339_; lean_object* v_unused_340_; 
v_unused_339_ = lean_ctor_get(v_a_310_, 1);
lean_dec(v_unused_339_);
v_unused_340_ = lean_ctor_get(v_a_310_, 0);
lean_dec(v_unused_340_);
v___x_329_ = v_a_310_;
v_isShared_330_ = v_isSharedCheck_338_;
goto v_resetjp_328_;
}
else
{
lean_dec(v_a_310_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_338_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = lean_nat_add(v_idx_312_, v___x_331_);
lean_dec(v_idx_312_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v___x_332_);
v___x_334_ = v___x_329_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_array_311_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v___x_332_);
v___x_334_ = v_reuseFailAlloc_337_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_box(0);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
return v___x_336_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Internal_Parsec_ByteArray_skipByteChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_309_ = stack[0].m_num;
lean_object* v_a_310_ = stack[1].m_obj;
lean_object* v_res_341_;
v_res_341_ = l_Std_Internal_Parsec_ByteArray_skipByteChar(v_c_309_, v_a_310_);
stack->m_obj
 = v_res_341_;
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByteChar___boxed(lean_object* v_c_342_, lean_object* v_a_343_){
_start:
{
uint32_t v_c_boxed_344_; lean_object* v_res_345_; 
v_c_boxed_344_ = lean_unbox_uint32(v_c_342_);
lean_dec(v_c_342_);
v_res_345_ = l_Std_Internal_Parsec_ByteArray_skipByteChar(v_c_boxed_344_, v_a_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digit(lean_object* v_a_349_){
_start:
{
lean_object* v_array_353_; lean_object* v_idx_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v_array_353_ = lean_ctor_get(v_a_349_, 0);
v_idx_354_ = lean_ctor_get(v_a_349_, 1);
v___x_355_ = lean_byte_array_size(v_array_353_);
v___x_356_ = lean_nat_dec_lt(v_idx_354_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_box(0);
v___x_358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_358_, 0, v_a_349_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
return v___x_358_;
}
else
{
uint8_t v_c_359_; uint8_t v___x_360_; uint8_t v___x_361_; 
v_c_359_ = lean_byte_array_fget(v_array_353_, v_idx_354_);
v___x_360_ = 48;
v___x_361_ = lean_uint8_dec_le(v___x_360_, v_c_359_);
if (v___x_361_ == 0)
{
goto v___jp_350_;
}
else
{
uint8_t v___x_362_; uint8_t v___x_363_; 
v___x_362_ = 57;
v___x_363_ = lean_uint8_dec_le(v_c_359_, v___x_362_);
if (v___x_363_ == 0)
{
goto v___jp_350_;
}
else
{
lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_375_; 
lean_inc(v_idx_354_);
lean_inc_ref(v_array_353_);
v_isSharedCheck_375_ = !lean_is_exclusive(v_a_349_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; lean_object* v_unused_377_; 
v_unused_376_ = lean_ctor_get(v_a_349_, 1);
lean_dec(v_unused_376_);
v_unused_377_ = lean_ctor_get(v_a_349_, 0);
lean_dec(v_unused_377_);
v___x_365_ = v_a_349_;
v_isShared_366_ = v_isSharedCheck_375_;
goto v_resetjp_364_;
}
else
{
lean_dec(v_a_349_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_375_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v_it_x27_370_; 
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_nat_add(v_idx_354_, v___x_367_);
lean_dec(v_idx_354_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 1, v___x_368_);
v_it_x27_370_ = v___x_365_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_array_353_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v___x_368_);
v_it_x27_370_ = v_reuseFailAlloc_374_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
uint32_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = lean_uint8_to_uint32(v_c_359_);
v___x_372_ = lean_box_uint32(v___x_371_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v_it_x27_370_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
return v___x_373_;
}
}
}
}
}
v___jp_350_:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_digit___closed__1));
v___x_352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_352_, 0, v_a_349_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
return v___x_352_;
}
}
}
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(uint8_t v_b_378_){
_start:
{
uint8_t v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; 
v___x_379_ = 48;
v___x_380_ = lean_uint8_sub(v_b_378_, v___x_379_);
v___x_381_ = lean_uint8_to_nat(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT void l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_378_ = stack[0].m_num;
lean_object* v_res_382_;
v_res_382_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(v_b_378_);
stack->m_obj
 = v_res_382_;
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat___boxed(lean_object* v_b_383_){
_start:
{
uint8_t v_b_boxed_384_; lean_object* v_res_385_; 
v_b_boxed_384_ = lean_unbox(v_b_383_);
v_res_385_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(v_b_boxed_384_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object* v_it_386_, lean_object* v_acc_387_){
_start:
{
lean_object* v_array_388_; lean_object* v_idx_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v_array_388_ = lean_ctor_get(v_it_386_, 0);
v_idx_389_ = lean_ctor_get(v_it_386_, 1);
v___x_390_ = lean_byte_array_size(v_array_388_);
v___x_391_ = lean_nat_dec_lt(v_idx_389_, v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v_acc_387_);
lean_ctor_set(v___x_392_, 1, v_it_386_);
return v___x_392_;
}
else
{
uint8_t v_candidate_393_; uint8_t v___x_394_; uint8_t v___x_395_; 
v_candidate_393_ = lean_byte_array_fget(v_array_388_, v_idx_389_);
v___x_394_ = 48;
v___x_395_ = lean_uint8_dec_le(v___x_394_, v_candidate_393_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; 
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v_acc_387_);
lean_ctor_set(v___x_396_, 1, v_it_386_);
return v___x_396_;
}
else
{
uint8_t v___x_397_; uint8_t v___x_398_; 
v___x_397_ = 57;
v___x_398_ = lean_uint8_dec_le(v_candidate_393_, v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_acc_387_);
lean_ctor_set(v___x_399_, 1, v_it_386_);
return v___x_399_;
}
else
{
lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_414_; 
lean_inc(v_idx_389_);
lean_inc_ref(v_array_388_);
v_isSharedCheck_414_ = !lean_is_exclusive(v_it_386_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; lean_object* v_unused_416_; 
v_unused_415_ = lean_ctor_get(v_it_386_, 1);
lean_dec(v_unused_415_);
v_unused_416_ = lean_ctor_get(v_it_386_, 0);
lean_dec(v_unused_416_);
v___x_401_ = v_it_386_;
v_isShared_402_ = v_isSharedCheck_414_;
goto v_resetjp_400_;
}
else
{
lean_dec(v_it_386_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_414_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
uint8_t v___x_403_; lean_object* v_digit_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v_acc_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_403_ = lean_uint8_sub(v_candidate_393_, v___x_394_);
v_digit_404_ = lean_uint8_to_nat(v___x_403_);
v___x_405_ = lean_unsigned_to_nat(10u);
v___x_406_ = lean_nat_mul(v_acc_387_, v___x_405_);
lean_dec(v_acc_387_);
v_acc_407_ = lean_nat_add(v___x_406_, v_digit_404_);
lean_dec(v___x_406_);
v___x_408_ = lean_unsigned_to_nat(1u);
v___x_409_ = lean_nat_add(v_idx_389_, v___x_408_);
lean_dec(v_idx_389_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 1, v___x_409_);
v___x_411_ = v___x_401_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_array_388_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v___x_409_);
v___x_411_ = v_reuseFailAlloc_413_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
v_it_386_ = v___x_411_;
v_acc_387_ = v_acc_407_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore(lean_object* v_acc_417_, lean_object* v_it_418_){
_start:
{
lean_object* v___x_419_; lean_object* v_fst_420_; lean_object* v_snd_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
v___x_419_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_418_, v_acc_417_);
v_fst_420_ = lean_ctor_get(v___x_419_, 0);
v_snd_421_ = lean_ctor_get(v___x_419_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_419_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_snd_421_);
lean_inc(v_fst_420_);
lean_dec(v___x_419_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v_fst_420_);
lean_ctor_set(v___x_423_, 0, v_snd_421_);
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_snd_421_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_fst_420_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digits(lean_object* v_a_429_){
_start:
{
lean_object* v_array_433_; lean_object* v_idx_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_array_433_ = lean_ctor_get(v_a_429_, 0);
v_idx_434_ = lean_ctor_get(v_a_429_, 1);
v___x_435_ = lean_byte_array_size(v_array_433_);
v___x_436_ = lean_nat_dec_lt(v_idx_434_, v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_box(0);
v___x_438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_438_, 0, v_a_429_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
return v___x_438_;
}
else
{
uint8_t v_c_439_; uint8_t v___x_440_; uint8_t v___x_441_; 
v_c_439_ = lean_byte_array_fget(v_array_433_, v_idx_434_);
v___x_440_ = 48;
v___x_441_ = lean_uint8_dec_le(v___x_440_, v_c_439_);
if (v___x_441_ == 0)
{
goto v___jp_430_;
}
else
{
uint8_t v___x_442_; uint8_t v___x_443_; 
v___x_442_ = 57;
v___x_443_ = lean_uint8_dec_le(v_c_439_, v___x_442_);
if (v___x_443_ == 0)
{
goto v___jp_430_;
}
else
{
lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_466_; 
lean_inc(v_idx_434_);
lean_inc_ref(v_array_433_);
v_isSharedCheck_466_ = !lean_is_exclusive(v_a_429_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; lean_object* v_unused_468_; 
v_unused_467_ = lean_ctor_get(v_a_429_, 1);
lean_dec(v_unused_467_);
v_unused_468_ = lean_ctor_get(v_a_429_, 0);
lean_dec(v_unused_468_);
v___x_445_ = v_a_429_;
v_isShared_446_ = v_isSharedCheck_466_;
goto v_resetjp_444_;
}
else
{
lean_dec(v_a_429_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_466_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_it_x27_450_; 
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_add(v_idx_434_, v___x_447_);
lean_dec(v_idx_434_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v___x_448_);
v_it_x27_450_ = v___x_445_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_array_433_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_448_);
v_it_x27_450_ = v_reuseFailAlloc_465_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
uint32_t v___x_451_; uint8_t v___x_452_; uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v_fst_456_; lean_object* v_snd_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v___x_451_ = lean_uint8_to_uint32(v_c_439_);
v___x_452_ = lean_uint32_to_uint8(v___x_451_);
v___x_453_ = lean_uint8_sub(v___x_452_, v___x_440_);
v___x_454_ = lean_uint8_to_nat(v___x_453_);
v___x_455_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_450_, v___x_454_);
v_fst_456_ = lean_ctor_get(v___x_455_, 0);
v_snd_457_ = lean_ctor_get(v___x_455_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_455_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_snd_457_);
lean_inc(v_fst_456_);
lean_dec(v___x_455_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v_fst_456_);
lean_ctor_set(v___x_459_, 0, v_snd_457_);
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_snd_457_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_fst_456_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
}
}
v___jp_430_:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_digit___closed__1));
v___x_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_432_, 0, v_a_429_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_hexDigit(lean_object* v_a_472_){
_start:
{
lean_object* v_array_476_; lean_object* v_idx_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v_array_476_ = lean_ctor_get(v_a_472_, 0);
v_idx_477_ = lean_ctor_get(v_a_472_, 1);
v___x_478_ = lean_byte_array_size(v_array_476_);
v___x_479_ = lean_nat_dec_lt(v_idx_477_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_box(0);
v___x_481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_481_, 0, v_a_472_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
return v___x_481_;
}
else
{
uint8_t v_c_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v_it_x27_485_; uint8_t v___x_500_; uint8_t v___x_501_; 
v_c_482_ = lean_byte_array_fget(v_array_476_, v_idx_477_);
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_nat_add(v_idx_477_, v___x_483_);
lean_inc_ref(v_array_476_);
v_it_x27_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_485_, 0, v_array_476_);
lean_ctor_set(v_it_x27_485_, 1, v___x_484_);
v___x_500_ = 48;
v___x_501_ = lean_uint8_dec_le(v___x_500_, v_c_482_);
if (v___x_501_ == 0)
{
goto v___jp_495_;
}
else
{
uint8_t v___x_502_; uint8_t v___x_503_; 
v___x_502_ = 57;
v___x_503_ = lean_uint8_dec_le(v_c_482_, v___x_502_);
if (v___x_503_ == 0)
{
goto v___jp_495_;
}
else
{
lean_dec_ref(v_a_472_);
goto v___jp_486_;
}
}
v___jp_486_:
{
uint32_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_uint8_to_uint32(v_c_482_);
v___x_488_ = lean_box_uint32(v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v_it_x27_485_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
return v___x_489_;
}
v___jp_490_:
{
uint8_t v___x_491_; uint8_t v___x_492_; 
v___x_491_ = 65;
v___x_492_ = lean_uint8_dec_le(v___x_491_, v_c_482_);
if (v___x_492_ == 0)
{
lean_dec_ref_known(v_it_x27_485_, 2);
goto v___jp_473_;
}
else
{
uint8_t v___x_493_; uint8_t v___x_494_; 
v___x_493_ = 70;
v___x_494_ = lean_uint8_dec_le(v_c_482_, v___x_493_);
if (v___x_494_ == 0)
{
lean_dec_ref_known(v_it_x27_485_, 2);
goto v___jp_473_;
}
else
{
lean_dec_ref(v_a_472_);
goto v___jp_486_;
}
}
}
v___jp_495_:
{
uint8_t v___x_496_; uint8_t v___x_497_; 
v___x_496_ = 97;
v___x_497_ = lean_uint8_dec_le(v___x_496_, v_c_482_);
if (v___x_497_ == 0)
{
goto v___jp_490_;
}
else
{
uint8_t v___x_498_; uint8_t v___x_499_; 
v___x_498_ = 102;
v___x_499_ = lean_uint8_dec_le(v_c_482_, v___x_498_);
if (v___x_499_ == 0)
{
goto v___jp_490_;
}
else
{
lean_dec_ref(v_a_472_);
goto v___jp_486_;
}
}
}
}
v___jp_473_:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1));
v___x_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_475_, 0, v_a_472_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_octDigit(lean_object* v_a_507_){
_start:
{
lean_object* v_array_511_; lean_object* v_idx_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_array_511_ = lean_ctor_get(v_a_507_, 0);
v_idx_512_ = lean_ctor_get(v_a_507_, 1);
v___x_513_ = lean_byte_array_size(v_array_511_);
v___x_514_ = lean_nat_dec_lt(v_idx_512_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_box(0);
v___x_516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_516_, 0, v_a_507_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
return v___x_516_;
}
else
{
uint8_t v_c_517_; uint8_t v___x_518_; uint8_t v___x_519_; 
v_c_517_ = lean_byte_array_fget(v_array_511_, v_idx_512_);
v___x_518_ = 48;
v___x_519_ = lean_uint8_dec_le(v___x_518_, v_c_517_);
if (v___x_519_ == 0)
{
goto v___jp_508_;
}
else
{
uint8_t v___x_520_; uint8_t v___x_521_; 
v___x_520_ = 55;
v___x_521_ = lean_uint8_dec_le(v_c_517_, v___x_520_);
if (v___x_521_ == 0)
{
goto v___jp_508_;
}
else
{
lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_533_; 
lean_inc(v_idx_512_);
lean_inc_ref(v_array_511_);
v_isSharedCheck_533_ = !lean_is_exclusive(v_a_507_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; lean_object* v_unused_535_; 
v_unused_534_ = lean_ctor_get(v_a_507_, 1);
lean_dec(v_unused_534_);
v_unused_535_ = lean_ctor_get(v_a_507_, 0);
lean_dec(v_unused_535_);
v___x_523_ = v_a_507_;
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
else
{
lean_dec(v_a_507_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v_it_x27_528_; 
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_add(v_idx_512_, v___x_525_);
lean_dec(v_idx_512_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v___x_526_);
v_it_x27_528_ = v___x_523_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_array_511_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v___x_526_);
v_it_x27_528_ = v_reuseFailAlloc_532_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
uint32_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_uint8_to_uint32(v_c_517_);
v___x_530_ = lean_box_uint32(v___x_529_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v_it_x27_528_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
return v___x_531_;
}
}
}
}
}
v___jp_508_:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_octDigit___closed__1));
v___x_510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_510_, 0, v_a_507_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_asciiLetter(lean_object* v_a_539_){
_start:
{
lean_object* v_array_543_; lean_object* v_idx_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v_array_543_ = lean_ctor_get(v_a_539_, 0);
v_idx_544_ = lean_ctor_get(v_a_539_, 1);
v___x_545_ = lean_byte_array_size(v_array_543_);
v___x_546_ = lean_nat_dec_lt(v_idx_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_box(0);
v___x_548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_548_, 0, v_a_539_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
return v___x_548_;
}
else
{
uint8_t v_c_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v_it_x27_552_; uint8_t v___x_562_; uint8_t v___x_563_; 
v_c_549_ = lean_byte_array_fget(v_array_543_, v_idx_544_);
v___x_550_ = lean_unsigned_to_nat(1u);
v___x_551_ = lean_nat_add(v_idx_544_, v___x_550_);
lean_inc_ref(v_array_543_);
v_it_x27_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_552_, 0, v_array_543_);
lean_ctor_set(v_it_x27_552_, 1, v___x_551_);
v___x_562_ = 65;
v___x_563_ = lean_uint8_dec_le(v___x_562_, v_c_549_);
if (v___x_563_ == 0)
{
goto v___jp_557_;
}
else
{
uint8_t v___x_564_; uint8_t v___x_565_; 
v___x_564_ = 90;
v___x_565_ = lean_uint8_dec_le(v_c_549_, v___x_564_);
if (v___x_565_ == 0)
{
goto v___jp_557_;
}
else
{
lean_dec_ref(v_a_539_);
goto v___jp_553_;
}
}
v___jp_553_:
{
uint32_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_uint8_to_uint32(v_c_549_);
v___x_555_ = lean_box_uint32(v___x_554_);
v___x_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_556_, 0, v_it_x27_552_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
return v___x_556_;
}
v___jp_557_:
{
uint8_t v___x_558_; uint8_t v___x_559_; 
v___x_558_ = 97;
v___x_559_ = lean_uint8_dec_le(v___x_558_, v_c_549_);
if (v___x_559_ == 0)
{
lean_dec_ref_known(v_it_x27_552_, 2);
goto v___jp_540_;
}
else
{
uint8_t v___x_560_; uint8_t v___x_561_; 
v___x_560_ = 122;
v___x_561_ = lean_uint8_dec_le(v_c_549_, v___x_560_);
if (v___x_561_ == 0)
{
lean_dec_ref_known(v_it_x27_552_, 2);
goto v___jp_540_;
}
else
{
lean_dec_ref(v_a_539_);
goto v___jp_553_;
}
}
}
}
v___jp_540_:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1));
v___x_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_542_, 0, v_a_539_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
return v___x_542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(lean_object* v_it_566_){
_start:
{
lean_object* v_array_567_; lean_object* v_idx_568_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_array_567_ = lean_ctor_get(v_it_566_, 0);
v_idx_568_ = lean_ctor_get(v_it_566_, 1);
v___x_574_ = lean_byte_array_size(v_array_567_);
v___x_575_ = lean_nat_dec_lt(v_idx_568_, v___x_574_);
if (v___x_575_ == 0)
{
return v_it_566_;
}
else
{
uint8_t v_b_576_; uint8_t v___x_577_; uint8_t v___x_578_; 
v_b_576_ = lean_byte_array_fget(v_array_567_, v_idx_568_);
v___x_577_ = 9;
v___x_578_ = lean_uint8_dec_eq(v_b_576_, v___x_577_);
if (v___x_578_ == 0)
{
uint8_t v___x_579_; uint8_t v___x_580_; 
v___x_579_ = 10;
v___x_580_ = lean_uint8_dec_eq(v_b_576_, v___x_579_);
if (v___x_580_ == 0)
{
uint8_t v___x_581_; uint8_t v___x_582_; 
v___x_581_ = 13;
v___x_582_ = lean_uint8_dec_eq(v_b_576_, v___x_581_);
if (v___x_582_ == 0)
{
uint8_t v___x_583_; uint8_t v___x_584_; 
v___x_583_ = 32;
v___x_584_ = lean_uint8_dec_eq(v_b_576_, v___x_583_);
if (v___x_584_ == 0)
{
return v_it_566_;
}
else
{
lean_inc(v_idx_568_);
lean_inc_ref(v_array_567_);
lean_dec_ref(v_it_566_);
goto v___jp_569_;
}
}
else
{
lean_inc(v_idx_568_);
lean_inc_ref(v_array_567_);
lean_dec_ref(v_it_566_);
goto v___jp_569_;
}
}
else
{
lean_inc(v_idx_568_);
lean_inc_ref(v_array_567_);
lean_dec_ref(v_it_566_);
goto v___jp_569_;
}
}
else
{
lean_inc(v_idx_568_);
lean_inc_ref(v_array_567_);
lean_dec_ref(v_it_566_);
goto v___jp_569_;
}
}
v___jp_569_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = lean_nat_add(v_idx_568_, v___x_570_);
lean_dec(v_idx_568_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v_array_567_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v_it_566_ = v___x_572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_ws(lean_object* v_it_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(v_it_585_);
v___x_587_ = lean_box(0);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take(lean_object* v_n_589_, lean_object* v_it_590_){
_start:
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = l_ByteArray_Iterator_remainingBytes(v_it_590_);
v___x_592_ = lean_nat_dec_lt(v___x_591_, v_n_589_);
lean_dec(v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v_array_593_; lean_object* v_idx_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_613_; 
v_array_593_ = lean_ctor_get(v_it_590_, 0);
v_idx_594_ = lean_ctor_get(v_it_590_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_it_590_);
if (v_isSharedCheck_613_ == 0)
{
v___x_596_ = v_it_590_;
v_isShared_597_ = v_isSharedCheck_613_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_idx_594_);
lean_inc(v_array_593_);
lean_dec(v_it_590_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_613_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = lean_nat_add(v_idx_594_, v_n_589_);
lean_inc(v___x_598_);
lean_inc_ref(v_array_593_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v___x_598_);
v___x_600_ = v___x_596_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_array_593_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v___x_598_);
v___x_600_ = v_reuseFailAlloc_612_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v_lower_602_; lean_object* v_upper_603_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___y_609_; uint8_t v___x_611_; 
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = lean_byte_array_size(v_array_593_);
v___x_611_ = lean_nat_dec_le(v_idx_594_, v___x_606_);
if (v___x_611_ == 0)
{
v___y_609_ = v_idx_594_;
goto v___jp_608_;
}
else
{
lean_dec(v_idx_594_);
v___y_609_ = v___x_606_;
goto v___jp_608_;
}
v___jp_601_:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = l_ByteArray_toByteSlice(v_array_593_, v_lower_602_, v_upper_603_);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_600_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
return v___x_605_;
}
v___jp_608_:
{
uint8_t v___x_610_; 
v___x_610_ = lean_nat_dec_le(v___x_598_, v___x_607_);
if (v___x_610_ == 0)
{
lean_dec(v___x_598_);
v_lower_602_ = v___y_609_;
v_upper_603_ = v___x_607_;
goto v___jp_601_;
}
else
{
v_lower_602_ = v___y_609_;
v_upper_603_ = v___x_598_;
goto v___jp_601_;
}
}
}
}
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_box(0);
v___x_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_615_, 0, v_it_590_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take___boxed(lean_object* v_n_616_, lean_object* v_it_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Std_Internal_Parsec_ByteArray_take(v_n_616_, v_it_617_);
lean_dec(v_n_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(lean_object* v_pred_619_, lean_object* v_count_620_, lean_object* v_iter_621_){
_start:
{
lean_object* v_array_622_; lean_object* v_idx_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v_array_622_ = lean_ctor_get(v_iter_621_, 0);
v_idx_623_ = lean_ctor_get(v_iter_621_, 1);
v___x_624_ = lean_byte_array_size(v_array_622_);
v___x_625_ = lean_nat_dec_lt(v_idx_623_, v___x_624_);
if (v___x_625_ == 0)
{
uint8_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec_ref(v_pred_619_);
v___x_626_ = 1;
v___x_627_ = lean_box(v___x_626_);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v_iter_621_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v_count_620_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
return v___x_629_;
}
else
{
uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_630_ = lean_byte_array_fget(v_array_622_, v_idx_623_);
v___x_631_ = lean_box(v___x_630_);
lean_inc_ref(v_pred_619_);
v___x_632_ = lean_apply_1(v_pred_619_, v___x_631_);
v___x_633_ = lean_unbox(v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec_ref(v_pred_619_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v_iter_621_);
lean_ctor_set(v___x_634_, 1, v___x_632_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v_count_620_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
return v___x_635_;
}
else
{
lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_646_; 
lean_inc(v_idx_623_);
lean_inc_ref(v_array_622_);
v_isSharedCheck_646_ = !lean_is_exclusive(v_iter_621_);
if (v_isSharedCheck_646_ == 0)
{
lean_object* v_unused_647_; lean_object* v_unused_648_; 
v_unused_647_ = lean_ctor_get(v_iter_621_, 1);
lean_dec(v_unused_647_);
v_unused_648_ = lean_ctor_get(v_iter_621_, 0);
lean_dec(v_unused_648_);
v___x_637_ = v_iter_621_;
v_isShared_638_ = v_isSharedCheck_646_;
goto v_resetjp_636_;
}
else
{
lean_dec(v_iter_621_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_646_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_639_ = lean_unsigned_to_nat(1u);
v___x_640_ = lean_nat_add(v_count_620_, v___x_639_);
lean_dec(v_count_620_);
v___x_641_ = lean_nat_add(v_idx_623_, v___x_639_);
lean_dec(v_idx_623_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v___x_641_);
v___x_643_ = v___x_637_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_array_622_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v___x_641_);
v___x_643_ = v_reuseFailAlloc_645_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
v_count_620_ = v___x_640_;
v_iter_621_ = v___x_643_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object* v_pred_649_, lean_object* v_limit_650_, lean_object* v_count_651_, lean_object* v_iter_652_){
_start:
{
uint8_t v___x_653_; 
v___x_653_ = lean_nat_dec_le(v_limit_650_, v_count_651_);
if (v___x_653_ == 0)
{
lean_object* v_array_654_; lean_object* v_idx_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_array_654_ = lean_ctor_get(v_iter_652_, 0);
v_idx_655_ = lean_ctor_get(v_iter_652_, 1);
v___x_656_ = lean_byte_array_size(v_array_654_);
v___x_657_ = lean_nat_dec_lt(v_idx_655_, v___x_656_);
if (v___x_657_ == 0)
{
uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec_ref(v_pred_649_);
v___x_658_ = 1;
v___x_659_ = lean_box(v___x_658_);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v_iter_652_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v_count_651_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
return v___x_661_;
}
else
{
uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_662_ = lean_byte_array_fget(v_array_654_, v_idx_655_);
v___x_663_ = lean_box(v___x_662_);
lean_inc_ref(v_pred_649_);
v___x_664_ = lean_apply_1(v_pred_649_, v___x_663_);
v___x_665_ = lean_unbox(v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec_ref(v_pred_649_);
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v_iter_652_);
lean_ctor_set(v___x_666_, 1, v___x_664_);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v_count_651_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
return v___x_667_;
}
else
{
lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_678_; 
lean_inc(v_idx_655_);
lean_inc_ref(v_array_654_);
v_isSharedCheck_678_ = !lean_is_exclusive(v_iter_652_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; lean_object* v_unused_680_; 
v_unused_679_ = lean_ctor_get(v_iter_652_, 1);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v_iter_652_, 0);
lean_dec(v_unused_680_);
v___x_669_ = v_iter_652_;
v_isShared_670_ = v_isSharedCheck_678_;
goto v_resetjp_668_;
}
else
{
lean_dec(v_iter_652_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_678_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_671_ = lean_unsigned_to_nat(1u);
v___x_672_ = lean_nat_add(v_count_651_, v___x_671_);
lean_dec(v_count_651_);
v___x_673_ = lean_nat_add(v_idx_655_, v___x_671_);
lean_dec(v_idx_655_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 1, v___x_673_);
v___x_675_ = v___x_669_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_array_654_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v___x_673_);
v___x_675_ = v_reuseFailAlloc_677_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
v_count_651_ = v___x_672_;
v_iter_652_ = v___x_675_;
goto _start;
}
}
}
}
}
else
{
uint8_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec_ref(v_pred_649_);
v___x_681_ = 0;
v___x_682_ = lean_box(v___x_681_);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v_iter_652_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v_count_651_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo___boxed(lean_object* v_pred_685_, lean_object* v_limit_686_, lean_object* v_count_687_, lean_object* v_iter_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_685_, v_limit_686_, v_count_687_, v_iter_688_);
lean_dec(v_limit_686_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile(lean_object* v_pred_690_, lean_object* v_it_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v_snd_694_; lean_object* v_snd_695_; uint8_t v___x_696_; 
v___x_692_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_691_);
v___x_693_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v_pred_690_, v___x_692_, v_it_691_);
v_snd_694_ = lean_ctor_get(v___x_693_, 1);
lean_inc(v_snd_694_);
v_snd_695_ = lean_ctor_get(v_snd_694_, 1);
v___x_696_ = lean_unbox(v_snd_695_);
if (v___x_696_ == 0)
{
lean_object* v_fst_697_; lean_object* v_fst_698_; lean_object* v_array_699_; lean_object* v_idx_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_717_; 
v_fst_697_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_fst_697_);
lean_dec_ref(v___x_693_);
v_fst_698_ = lean_ctor_get(v_snd_694_, 0);
lean_inc(v_fst_698_);
lean_dec(v_snd_694_);
v_array_699_ = lean_ctor_get(v_it_691_, 0);
v_idx_700_ = lean_ctor_get(v_it_691_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v_it_691_);
if (v_isSharedCheck_717_ == 0)
{
v___x_702_ = v_it_691_;
v_isShared_703_ = v_isSharedCheck_717_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_idx_700_);
lean_inc(v_array_699_);
lean_dec(v_it_691_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_717_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_lower_705_; lean_object* v_upper_706_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___y_714_; uint8_t v___x_716_; 
v___x_711_ = lean_nat_add(v_idx_700_, v_fst_697_);
lean_dec(v_fst_697_);
v___x_712_ = lean_byte_array_size(v_array_699_);
v___x_716_ = lean_nat_dec_le(v_idx_700_, v___x_692_);
if (v___x_716_ == 0)
{
v___y_714_ = v_idx_700_;
goto v___jp_713_;
}
else
{
lean_dec(v_idx_700_);
v___y_714_ = v___x_692_;
goto v___jp_713_;
}
v___jp_704_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = l_ByteArray_toByteSlice(v_array_699_, v_lower_705_, v_upper_706_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v___x_707_);
lean_ctor_set(v___x_702_, 0, v_fst_698_);
v___x_709_ = v___x_702_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_fst_698_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
v___jp_713_:
{
uint8_t v___x_715_; 
v___x_715_ = lean_nat_dec_le(v___x_711_, v___x_712_);
if (v___x_715_ == 0)
{
lean_dec(v___x_711_);
v_lower_705_ = v___y_714_;
v_upper_706_ = v___x_712_;
goto v___jp_704_;
}
else
{
v_lower_705_ = v___y_714_;
v_upper_706_ = v___x_711_;
goto v___jp_704_;
}
}
}
}
else
{
lean_object* v_fst_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_726_; 
lean_dec_ref(v___x_693_);
lean_dec_ref(v_it_691_);
v_fst_718_ = lean_ctor_get(v_snd_694_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v_snd_694_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v_snd_694_, 1);
lean_dec(v_unused_727_);
v___x_720_ = v_snd_694_;
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_fst_718_);
lean_dec(v_snd_694_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_722_ = lean_box(0);
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 1);
lean_ctor_set(v___x_720_, 1, v___x_722_);
v___x_724_ = v___x_720_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_fst_718_);
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
uint8_t l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(lean_object* v_pred_728_, uint8_t v_b_729_){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_730_ = lean_box(v_b_729_);
v___x_731_ = lean_apply_1(v_pred_728_, v___x_730_);
v___x_732_ = lean_unbox(v___x_731_);
if (v___x_732_ == 0)
{
uint8_t v___x_733_; 
v___x_733_ = 1;
return v___x_733_;
}
else
{
uint8_t v___x_734_; 
v___x_734_ = 0;
return v___x_734_;
}
}
}
LEAN_EXPORT void l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pred_728_ = stack[0].m_obj;
uint8_t v_b_729_ = stack[1].m_num;
uint8_t v_res_735_;
v_res_735_ = l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(v_pred_728_, v_b_729_);
stack->m_num = v_res_735_;
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed(lean_object* v_pred_736_, lean_object* v_b_737_){
_start:
{
uint8_t v_b_boxed_738_; uint8_t v_res_739_; lean_object* v_r_740_; 
v_b_boxed_738_ = lean_unbox(v_b_737_);
v_res_739_ = l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(v_pred_736_, v_b_boxed_738_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil(lean_object* v_pred_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_snd_746_; lean_object* v_snd_747_; uint8_t v___x_748_; 
v___f_743_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_743_, 0, v_pred_741_);
v___x_744_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_742_);
v___x_745_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v___f_743_, v___x_744_, v_a_742_);
v_snd_746_ = lean_ctor_get(v___x_745_, 1);
lean_inc(v_snd_746_);
v_snd_747_ = lean_ctor_get(v_snd_746_, 1);
v___x_748_ = lean_unbox(v_snd_747_);
if (v___x_748_ == 0)
{
lean_object* v_fst_749_; lean_object* v_fst_750_; lean_object* v_array_751_; lean_object* v_idx_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_769_; 
v_fst_749_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_fst_749_);
lean_dec_ref(v___x_745_);
v_fst_750_ = lean_ctor_get(v_snd_746_, 0);
lean_inc(v_fst_750_);
lean_dec(v_snd_746_);
v_array_751_ = lean_ctor_get(v_a_742_, 0);
v_idx_752_ = lean_ctor_get(v_a_742_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v_a_742_);
if (v_isSharedCheck_769_ == 0)
{
v___x_754_ = v_a_742_;
v_isShared_755_ = v_isSharedCheck_769_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_idx_752_);
lean_inc(v_array_751_);
lean_dec(v_a_742_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_769_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_lower_757_; lean_object* v_upper_758_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___y_766_; uint8_t v___x_768_; 
v___x_763_ = lean_nat_add(v_idx_752_, v_fst_749_);
lean_dec(v_fst_749_);
v___x_764_ = lean_byte_array_size(v_array_751_);
v___x_768_ = lean_nat_dec_le(v_idx_752_, v___x_744_);
if (v___x_768_ == 0)
{
v___y_766_ = v_idx_752_;
goto v___jp_765_;
}
else
{
lean_dec(v_idx_752_);
v___y_766_ = v___x_744_;
goto v___jp_765_;
}
v___jp_756_:
{
lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_759_ = l_ByteArray_toByteSlice(v_array_751_, v_lower_757_, v_upper_758_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v___x_759_);
lean_ctor_set(v___x_754_, 0, v_fst_750_);
v___x_761_ = v___x_754_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_fst_750_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
v___jp_765_:
{
uint8_t v___x_767_; 
v___x_767_ = lean_nat_dec_le(v___x_763_, v___x_764_);
if (v___x_767_ == 0)
{
lean_dec(v___x_763_);
v_lower_757_ = v___y_766_;
v_upper_758_ = v___x_764_;
goto v___jp_756_;
}
else
{
v_lower_757_ = v___y_766_;
v_upper_758_ = v___x_763_;
goto v___jp_756_;
}
}
}
}
else
{
lean_object* v_fst_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v___x_745_);
lean_dec_ref(v_a_742_);
v_fst_770_ = lean_ctor_get(v_snd_746_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v_snd_746_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_snd_746_, 1);
lean_dec(v_unused_779_);
v___x_772_ = v_snd_746_;
v_isShared_773_ = v_isSharedCheck_778_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_fst_770_);
lean_dec(v_snd_746_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_778_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = lean_box(0);
if (v_isShared_773_ == 0)
{
lean_ctor_set_tag(v___x_772_, 1);
lean_ctor_set(v___x_772_, 1, v___x_774_);
v___x_776_ = v___x_772_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_fst_770_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhile(lean_object* v_pred_780_, lean_object* v_it_781_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v_snd_784_; lean_object* v_snd_785_; uint8_t v___x_786_; 
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v_pred_780_, v___x_782_, v_it_781_);
v_snd_784_ = lean_ctor_get(v___x_783_, 1);
lean_inc(v_snd_784_);
lean_dec_ref(v___x_783_);
v_snd_785_ = lean_ctor_get(v_snd_784_, 1);
v___x_786_ = lean_unbox(v_snd_785_);
if (v___x_786_ == 0)
{
lean_object* v_fst_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_795_; 
v_fst_787_ = lean_ctor_get(v_snd_784_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v_snd_784_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v_snd_784_, 1);
lean_dec(v_unused_796_);
v___x_789_ = v_snd_784_;
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_fst_787_);
lean_dec(v_snd_784_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = lean_box(0);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 1, v___x_791_);
v___x_793_ = v___x_789_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_fst_787_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
else
{
lean_object* v_fst_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_805_; 
v_fst_797_ = lean_ctor_get(v_snd_784_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v_snd_784_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; 
v_unused_806_ = lean_ctor_get(v_snd_784_, 1);
lean_dec(v_unused_806_);
v___x_799_ = v_snd_784_;
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_fst_797_);
lean_dec(v_snd_784_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_801_ = lean_box(0);
if (v_isShared_800_ == 0)
{
lean_ctor_set_tag(v___x_799_, 1);
lean_ctor_set(v___x_799_, 1, v___x_801_);
v___x_803_ = v___x_799_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_fst_797_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntil(lean_object* v_pred_807_, lean_object* v_a_808_){
_start:
{
lean_object* v___f_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v_snd_812_; lean_object* v_snd_813_; uint8_t v___x_814_; 
v___f_809_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_809_, 0, v_pred_807_);
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v___f_809_, v___x_810_, v_a_808_);
v_snd_812_ = lean_ctor_get(v___x_811_, 1);
lean_inc(v_snd_812_);
lean_dec_ref(v___x_811_);
v_snd_813_ = lean_ctor_get(v_snd_812_, 1);
v___x_814_ = lean_unbox(v_snd_813_);
if (v___x_814_ == 0)
{
lean_object* v_fst_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_823_; 
v_fst_815_ = lean_ctor_get(v_snd_812_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v_snd_812_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v_snd_812_, 1);
lean_dec(v_unused_824_);
v___x_817_ = v_snd_812_;
v_isShared_818_ = v_isSharedCheck_823_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_fst_815_);
lean_dec(v_snd_812_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_823_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = lean_box(0);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v___x_819_);
v___x_821_ = v___x_817_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_fst_815_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
else
{
lean_object* v_fst_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_833_; 
v_fst_825_ = lean_ctor_get(v_snd_812_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v_snd_812_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; 
v_unused_834_ = lean_ctor_get(v_snd_812_, 1);
lean_dec(v_unused_834_);
v___x_827_ = v_snd_812_;
v_isShared_828_ = v_isSharedCheck_833_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_fst_825_);
lean_dec(v_snd_812_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_833_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_829_ = lean_box(0);
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 1);
lean_ctor_set(v___x_827_, 1, v___x_829_);
v___x_831_ = v___x_827_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_fst_825_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(lean_object* v_pred_835_, lean_object* v_limit_836_, lean_object* v_it_837_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v_snd_840_; lean_object* v_snd_841_; uint8_t v___x_842_; 
v___x_838_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_837_);
v___x_839_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_835_, v_limit_836_, v___x_838_, v_it_837_);
v_snd_840_ = lean_ctor_get(v___x_839_, 1);
lean_inc(v_snd_840_);
v_snd_841_ = lean_ctor_get(v_snd_840_, 1);
v___x_842_ = lean_unbox(v_snd_841_);
if (v___x_842_ == 0)
{
lean_object* v_fst_843_; lean_object* v_fst_844_; lean_object* v_array_845_; lean_object* v_idx_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_863_; 
v_fst_843_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_fst_843_);
lean_dec_ref(v___x_839_);
v_fst_844_ = lean_ctor_get(v_snd_840_, 0);
lean_inc(v_fst_844_);
lean_dec(v_snd_840_);
v_array_845_ = lean_ctor_get(v_it_837_, 0);
v_idx_846_ = lean_ctor_get(v_it_837_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v_it_837_);
if (v_isSharedCheck_863_ == 0)
{
v___x_848_ = v_it_837_;
v_isShared_849_ = v_isSharedCheck_863_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_idx_846_);
lean_inc(v_array_845_);
lean_dec(v_it_837_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_863_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v_lower_851_; lean_object* v_upper_852_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___y_860_; uint8_t v___x_862_; 
v___x_857_ = lean_nat_add(v_idx_846_, v_fst_843_);
lean_dec(v_fst_843_);
v___x_858_ = lean_byte_array_size(v_array_845_);
v___x_862_ = lean_nat_dec_le(v_idx_846_, v___x_838_);
if (v___x_862_ == 0)
{
v___y_860_ = v_idx_846_;
goto v___jp_859_;
}
else
{
lean_dec(v_idx_846_);
v___y_860_ = v___x_838_;
goto v___jp_859_;
}
v___jp_850_:
{
lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_853_ = l_ByteArray_toByteSlice(v_array_845_, v_lower_851_, v_upper_852_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v___x_853_);
lean_ctor_set(v___x_848_, 0, v_fst_844_);
v___x_855_ = v___x_848_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_fst_844_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
v___jp_859_:
{
uint8_t v___x_861_; 
v___x_861_ = lean_nat_dec_le(v___x_857_, v___x_858_);
if (v___x_861_ == 0)
{
lean_dec(v___x_857_);
v_lower_851_ = v___y_860_;
v_upper_852_ = v___x_858_;
goto v___jp_850_;
}
else
{
v_lower_851_ = v___y_860_;
v_upper_852_ = v___x_857_;
goto v___jp_850_;
}
}
}
}
else
{
lean_object* v_fst_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v___x_839_);
lean_dec_ref(v_it_837_);
v_fst_864_ = lean_ctor_get(v_snd_840_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v_snd_840_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; 
v_unused_873_ = lean_ctor_get(v_snd_840_, 1);
lean_dec(v_unused_873_);
v___x_866_ = v_snd_840_;
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_fst_864_);
lean_dec(v_snd_840_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_868_ = lean_box(0);
if (v_isShared_867_ == 0)
{
lean_ctor_set_tag(v___x_866_, 1);
lean_ctor_set(v___x_866_, 1, v___x_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_fst_864_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo___boxed(lean_object* v_pred_874_, lean_object* v_limit_875_, lean_object* v_it_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(v_pred_874_, v_limit_875_, v_it_876_);
lean_dec(v_limit_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(lean_object* v_pred_881_, lean_object* v_limit_882_, lean_object* v_it_883_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v_snd_886_; lean_object* v_snd_887_; uint8_t v___x_888_; 
v___x_884_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_883_);
v___x_885_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_881_, v_limit_882_, v___x_884_, v_it_883_);
v_snd_886_ = lean_ctor_get(v___x_885_, 1);
lean_inc(v_snd_886_);
v_snd_887_ = lean_ctor_get(v_snd_886_, 1);
v___x_888_ = lean_unbox(v_snd_887_);
if (v___x_888_ == 0)
{
lean_object* v_fst_889_; lean_object* v_fst_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_918_; 
v_fst_889_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_fst_889_);
lean_dec_ref(v___x_885_);
v_fst_890_ = lean_ctor_get(v_snd_886_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v_snd_886_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v_snd_886_, 1);
lean_dec(v_unused_919_);
v___x_892_ = v_snd_886_;
v_isShared_893_ = v_isSharedCheck_918_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_fst_890_);
lean_dec(v_snd_886_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_918_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
uint8_t v___x_894_; 
v___x_894_ = lean_nat_dec_eq(v_fst_889_, v___x_884_);
if (v___x_894_ == 0)
{
lean_object* v_array_895_; lean_object* v_idx_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_913_; 
lean_del_object(v___x_892_);
v_array_895_ = lean_ctor_get(v_it_883_, 0);
v_idx_896_ = lean_ctor_get(v_it_883_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v_it_883_);
if (v_isSharedCheck_913_ == 0)
{
v___x_898_ = v_it_883_;
v_isShared_899_ = v_isSharedCheck_913_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_idx_896_);
lean_inc(v_array_895_);
lean_dec(v_it_883_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_913_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_lower_901_; lean_object* v_upper_902_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___y_910_; uint8_t v___x_912_; 
v___x_907_ = lean_nat_add(v_idx_896_, v_fst_889_);
lean_dec(v_fst_889_);
v___x_908_ = lean_byte_array_size(v_array_895_);
v___x_912_ = lean_nat_dec_le(v_idx_896_, v___x_884_);
if (v___x_912_ == 0)
{
v___y_910_ = v_idx_896_;
goto v___jp_909_;
}
else
{
lean_dec(v_idx_896_);
v___y_910_ = v___x_884_;
goto v___jp_909_;
}
v___jp_900_:
{
lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_903_ = l_ByteArray_toByteSlice(v_array_895_, v_lower_901_, v_upper_902_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v___x_903_);
lean_ctor_set(v___x_898_, 0, v_fst_890_);
v___x_905_ = v___x_898_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_fst_890_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
v___jp_909_:
{
uint8_t v___x_911_; 
v___x_911_ = lean_nat_dec_le(v___x_907_, v___x_908_);
if (v___x_911_ == 0)
{
lean_dec(v___x_907_);
v_lower_901_ = v___y_910_;
v_upper_902_ = v___x_908_;
goto v___jp_900_;
}
else
{
v_lower_901_ = v___y_910_;
v_upper_902_ = v___x_907_;
goto v___jp_900_;
}
}
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_916_; 
lean_dec(v_fst_890_);
lean_dec(v_fst_889_);
v___x_914_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1));
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 1);
lean_ctor_set(v___x_892_, 1, v___x_914_);
lean_ctor_set(v___x_892_, 0, v_it_883_);
v___x_916_ = v___x_892_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_it_883_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_object* v_fst_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v___x_885_);
lean_dec_ref(v_it_883_);
v_fst_920_ = lean_ctor_get(v_snd_886_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v_snd_886_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v_snd_886_, 1);
lean_dec(v_unused_929_);
v___x_922_ = v_snd_886_;
v_isShared_923_ = v_isSharedCheck_928_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_fst_920_);
lean_dec(v_snd_886_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_928_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_924_ = lean_box(0);
if (v_isShared_923_ == 0)
{
lean_ctor_set_tag(v___x_922_, 1);
lean_ctor_set(v___x_922_, 1, v___x_924_);
v___x_926_ = v___x_922_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_fst_920_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___boxed(lean_object* v_pred_930_, lean_object* v_limit_931_, lean_object* v_it_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(v_pred_930_, v_limit_931_, v_it_932_);
lean_dec(v_limit_931_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(lean_object* v_pred_934_, lean_object* v_limit_935_, lean_object* v_a_936_){
_start:
{
lean_object* v___f_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v_snd_940_; lean_object* v_snd_941_; uint8_t v___x_942_; 
v___f_937_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_937_, 0, v_pred_934_);
v___x_938_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_936_);
v___x_939_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_937_, v_limit_935_, v___x_938_, v_a_936_);
v_snd_940_ = lean_ctor_get(v___x_939_, 1);
lean_inc(v_snd_940_);
v_snd_941_ = lean_ctor_get(v_snd_940_, 1);
v___x_942_ = lean_unbox(v_snd_941_);
if (v___x_942_ == 0)
{
lean_object* v_fst_943_; lean_object* v_fst_944_; lean_object* v_array_945_; lean_object* v_idx_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_963_; 
v_fst_943_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_fst_943_);
lean_dec_ref(v___x_939_);
v_fst_944_ = lean_ctor_get(v_snd_940_, 0);
lean_inc(v_fst_944_);
lean_dec(v_snd_940_);
v_array_945_ = lean_ctor_get(v_a_936_, 0);
v_idx_946_ = lean_ctor_get(v_a_936_, 1);
v_isSharedCheck_963_ = !lean_is_exclusive(v_a_936_);
if (v_isSharedCheck_963_ == 0)
{
v___x_948_ = v_a_936_;
v_isShared_949_ = v_isSharedCheck_963_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_idx_946_);
lean_inc(v_array_945_);
lean_dec(v_a_936_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_963_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_lower_951_; lean_object* v_upper_952_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___y_960_; uint8_t v___x_962_; 
v___x_957_ = lean_nat_add(v_idx_946_, v_fst_943_);
lean_dec(v_fst_943_);
v___x_958_ = lean_byte_array_size(v_array_945_);
v___x_962_ = lean_nat_dec_le(v_idx_946_, v___x_938_);
if (v___x_962_ == 0)
{
v___y_960_ = v_idx_946_;
goto v___jp_959_;
}
else
{
lean_dec(v_idx_946_);
v___y_960_ = v___x_938_;
goto v___jp_959_;
}
v___jp_950_:
{
lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_953_ = l_ByteArray_toByteSlice(v_array_945_, v_lower_951_, v_upper_952_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_953_);
lean_ctor_set(v___x_948_, 0, v_fst_944_);
v___x_955_ = v___x_948_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_fst_944_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
v___jp_959_:
{
uint8_t v___x_961_; 
v___x_961_ = lean_nat_dec_le(v___x_957_, v___x_958_);
if (v___x_961_ == 0)
{
lean_dec(v___x_957_);
v_lower_951_ = v___y_960_;
v_upper_952_ = v___x_958_;
goto v___jp_950_;
}
else
{
v_lower_951_ = v___y_960_;
v_upper_952_ = v___x_957_;
goto v___jp_950_;
}
}
}
}
else
{
lean_object* v_fst_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_972_; 
lean_dec_ref(v___x_939_);
lean_dec_ref(v_a_936_);
v_fst_964_ = lean_ctor_get(v_snd_940_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v_snd_940_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; 
v_unused_973_ = lean_ctor_get(v_snd_940_, 1);
lean_dec(v_unused_973_);
v___x_966_ = v_snd_940_;
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_fst_964_);
lean_dec(v_snd_940_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_968_ = lean_box(0);
if (v_isShared_967_ == 0)
{
lean_ctor_set_tag(v___x_966_, 1);
lean_ctor_set(v___x_966_, 1, v___x_968_);
v___x_970_ = v___x_966_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_fst_964_);
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
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo___boxed(lean_object* v_pred_974_, lean_object* v_limit_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(v_pred_974_, v_limit_975_, v_a_976_);
lean_dec(v_limit_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileAtMost(lean_object* v_pred_978_, lean_object* v_limit_979_, lean_object* v_it_980_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_snd_983_; lean_object* v_fst_984_; lean_object* v_fst_985_; lean_object* v_array_986_; lean_object* v_idx_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1004_; 
v___x_981_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_980_);
v___x_982_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_978_, v_limit_979_, v___x_981_, v_it_980_);
v_snd_983_ = lean_ctor_get(v___x_982_, 1);
lean_inc(v_snd_983_);
v_fst_984_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_fst_984_);
lean_dec_ref(v___x_982_);
v_fst_985_ = lean_ctor_get(v_snd_983_, 0);
lean_inc(v_fst_985_);
lean_dec(v_snd_983_);
v_array_986_ = lean_ctor_get(v_it_980_, 0);
v_idx_987_ = lean_ctor_get(v_it_980_, 1);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_it_980_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_989_ = v_it_980_;
v_isShared_990_ = v_isSharedCheck_1004_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_idx_987_);
lean_inc(v_array_986_);
lean_dec(v_it_980_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1004_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v_lower_992_; lean_object* v_upper_993_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___y_1001_; uint8_t v___x_1003_; 
v___x_998_ = lean_nat_add(v_idx_987_, v_fst_984_);
lean_dec(v_fst_984_);
v___x_999_ = lean_byte_array_size(v_array_986_);
v___x_1003_ = lean_nat_dec_le(v_idx_987_, v___x_981_);
if (v___x_1003_ == 0)
{
v___y_1001_ = v_idx_987_;
goto v___jp_1000_;
}
else
{
lean_dec(v_idx_987_);
v___y_1001_ = v___x_981_;
goto v___jp_1000_;
}
v___jp_991_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = l_ByteArray_toByteSlice(v_array_986_, v_lower_992_, v_upper_993_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 1, v___x_994_);
lean_ctor_set(v___x_989_, 0, v_fst_985_);
v___x_996_ = v___x_989_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_fst_985_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
v___jp_1000_:
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_nat_dec_le(v___x_998_, v___x_999_);
if (v___x_1002_ == 0)
{
lean_dec(v___x_998_);
v_lower_992_ = v___y_1001_;
v_upper_993_ = v___x_999_;
goto v___jp_991_;
}
else
{
v_lower_992_ = v___y_1001_;
v_upper_993_ = v___x_998_;
goto v___jp_991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileAtMost___boxed(lean_object* v_pred_1005_, lean_object* v_limit_1006_, lean_object* v_it_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Std_Internal_Parsec_ByteArray_takeWhileAtMost(v_pred_1005_, v_limit_1006_, v_it_1007_);
lean_dec(v_limit_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost(lean_object* v_pred_1009_, lean_object* v_limit_1010_, lean_object* v_it_1011_){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v_snd_1014_; lean_object* v_fst_1015_; lean_object* v_fst_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1044_; 
v___x_1012_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_1011_);
v___x_1013_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_1009_, v_limit_1010_, v___x_1012_, v_it_1011_);
v_snd_1014_ = lean_ctor_get(v___x_1013_, 1);
lean_inc(v_snd_1014_);
v_fst_1015_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_fst_1015_);
lean_dec_ref(v___x_1013_);
v_fst_1016_ = lean_ctor_get(v_snd_1014_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_snd_1014_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; 
v_unused_1045_ = lean_ctor_get(v_snd_1014_, 1);
lean_dec(v_unused_1045_);
v___x_1018_ = v_snd_1014_;
v_isShared_1019_ = v_isSharedCheck_1044_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_fst_1016_);
lean_dec(v_snd_1014_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1044_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
uint8_t v___x_1020_; 
v___x_1020_ = lean_nat_dec_eq(v_fst_1015_, v___x_1012_);
if (v___x_1020_ == 0)
{
lean_object* v_array_1021_; lean_object* v_idx_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1039_; 
lean_del_object(v___x_1018_);
v_array_1021_ = lean_ctor_get(v_it_1011_, 0);
v_idx_1022_ = lean_ctor_get(v_it_1011_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_it_1011_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1024_ = v_it_1011_;
v_isShared_1025_ = v_isSharedCheck_1039_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_idx_1022_);
lean_inc(v_array_1021_);
lean_dec(v_it_1011_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1039_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v_lower_1027_; lean_object* v_upper_1028_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___y_1036_; uint8_t v___x_1038_; 
v___x_1033_ = lean_nat_add(v_idx_1022_, v_fst_1015_);
lean_dec(v_fst_1015_);
v___x_1034_ = lean_byte_array_size(v_array_1021_);
v___x_1038_ = lean_nat_dec_le(v_idx_1022_, v___x_1012_);
if (v___x_1038_ == 0)
{
v___y_1036_ = v_idx_1022_;
goto v___jp_1035_;
}
else
{
lean_dec(v_idx_1022_);
v___y_1036_ = v___x_1012_;
goto v___jp_1035_;
}
v___jp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = l_ByteArray_toByteSlice(v_array_1021_, v_lower_1027_, v_upper_1028_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v___x_1029_);
lean_ctor_set(v___x_1024_, 0, v_fst_1016_);
v___x_1031_ = v___x_1024_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_fst_1016_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
v___jp_1035_:
{
uint8_t v___x_1037_; 
v___x_1037_ = lean_nat_dec_le(v___x_1033_, v___x_1034_);
if (v___x_1037_ == 0)
{
lean_dec(v___x_1033_);
v_lower_1027_ = v___y_1036_;
v_upper_1028_ = v___x_1034_;
goto v___jp_1026_;
}
else
{
v_lower_1027_ = v___y_1036_;
v_upper_1028_ = v___x_1033_;
goto v___jp_1026_;
}
}
}
}
else
{
lean_object* v___x_1040_; lean_object* v___x_1042_; 
lean_dec(v_fst_1016_);
lean_dec(v_fst_1015_);
v___x_1040_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1));
if (v_isShared_1019_ == 0)
{
lean_ctor_set_tag(v___x_1018_, 1);
lean_ctor_set(v___x_1018_, 1, v___x_1040_);
lean_ctor_set(v___x_1018_, 0, v_it_1011_);
v___x_1042_ = v___x_1018_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_it_1011_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost___boxed(lean_object* v_pred_1046_, lean_object* v_limit_1047_, lean_object* v_it_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost(v_pred_1046_, v_limit_1047_, v_it_1048_);
lean_dec(v_limit_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(lean_object* v_pred_1050_, lean_object* v_limit_1051_, lean_object* v_it_1052_){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v_snd_1055_; lean_object* v_snd_1056_; uint8_t v___x_1057_; 
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_1050_, v_limit_1051_, v___x_1053_, v_it_1052_);
v_snd_1055_ = lean_ctor_get(v___x_1054_, 1);
lean_inc(v_snd_1055_);
lean_dec_ref(v___x_1054_);
v_snd_1056_ = lean_ctor_get(v_snd_1055_, 1);
v___x_1057_ = lean_unbox(v_snd_1056_);
if (v___x_1057_ == 0)
{
lean_object* v_fst_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1066_; 
v_fst_1058_ = lean_ctor_get(v_snd_1055_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_snd_1055_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; 
v_unused_1067_ = lean_ctor_get(v_snd_1055_, 1);
lean_dec(v_unused_1067_);
v___x_1060_ = v_snd_1055_;
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_fst_1058_);
lean_dec(v_snd_1055_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1062_ = lean_box(0);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 1, v___x_1062_);
v___x_1064_ = v___x_1060_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_fst_1058_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
else
{
lean_object* v_fst_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1076_; 
v_fst_1068_ = lean_ctor_get(v_snd_1055_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_snd_1055_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v_snd_1055_, 1);
lean_dec(v_unused_1077_);
v___x_1070_ = v_snd_1055_;
v_isShared_1071_ = v_isSharedCheck_1076_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_fst_1068_);
lean_dec(v_snd_1055_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1076_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = lean_box(0);
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 1);
lean_ctor_set(v___x_1070_, 1, v___x_1072_);
v___x_1074_ = v___x_1070_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_fst_1068_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhileUpTo___boxed(lean_object* v_pred_1078_, lean_object* v_limit_1079_, lean_object* v_it_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(v_pred_1078_, v_limit_1079_, v_it_1080_);
lean_dec(v_limit_1079_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(lean_object* v_pred_1082_, lean_object* v_limit_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v___f_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v_snd_1088_; lean_object* v_snd_1089_; uint8_t v___x_1090_; 
v___f_1085_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1085_, 0, v_pred_1082_);
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1085_, v_limit_1083_, v___x_1086_, v_a_1084_);
v_snd_1088_ = lean_ctor_get(v___x_1087_, 1);
lean_inc(v_snd_1088_);
lean_dec_ref(v___x_1087_);
v_snd_1089_ = lean_ctor_get(v_snd_1088_, 1);
v___x_1090_ = lean_unbox(v_snd_1089_);
if (v___x_1090_ == 0)
{
lean_object* v_fst_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1099_; 
v_fst_1091_ = lean_ctor_get(v_snd_1088_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_snd_1088_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v_snd_1088_, 1);
lean_dec(v_unused_1100_);
v___x_1093_ = v_snd_1088_;
v_isShared_1094_ = v_isSharedCheck_1099_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_fst_1091_);
lean_dec(v_snd_1088_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1099_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1095_ = lean_box(0);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v___x_1095_);
v___x_1097_ = v___x_1093_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_fst_1091_);
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
else
{
lean_object* v_fst_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1109_; 
v_fst_1101_ = lean_ctor_get(v_snd_1088_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_snd_1088_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; 
v_unused_1110_ = lean_ctor_get(v_snd_1088_, 1);
lean_dec(v_unused_1110_);
v___x_1103_ = v_snd_1088_;
v_isShared_1104_ = v_isSharedCheck_1109_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_fst_1101_);
lean_dec(v_snd_1088_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1109_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1105_ = lean_box(0);
if (v_isShared_1104_ == 0)
{
lean_ctor_set_tag(v___x_1103_, 1);
lean_ctor_set(v___x_1103_, 1, v___x_1105_);
v___x_1107_ = v___x_1103_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_fst_1101_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v___x_1105_);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntilUpTo___boxed(lean_object* v_pred_1111_, lean_object* v_limit_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(v_pred_1111_, v_limit_1112_, v_a_1113_);
lean_dec(v_limit_1112_);
return v_res_1114_;
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
