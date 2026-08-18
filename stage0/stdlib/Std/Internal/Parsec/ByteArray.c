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
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_ByteArray_toByteSlice(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Internal_Parsec_ByteArray_digit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Internal_Parsec_ByteArray_digit___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_ByteArray_digit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Internal_Parsec_ByteArray_digit___closed__3;
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
static lean_once_cell_t l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3;
static lean_once_cell_t l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4;
static lean_once_cell_t l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_hexDigit(lean_object*);
static const lean_string_object l_Std_Internal_Parsec_ByteArray_octDigit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "octal digit expected"};
static const lean_object* l_Std_Internal_Parsec_ByteArray_octDigit___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_octDigit___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_ByteArray_octDigit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_ByteArray_octDigit___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_ByteArray_octDigit___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_octDigit___closed__1_value;
static lean_once_cell_t l_Std_Internal_Parsec_ByteArray_octDigit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Internal_Parsec_ByteArray_octDigit___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_octDigit(lean_object*);
static const lean_string_object l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ASCII letter expected"};
static const lean_object* l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1_value;
static lean_once_cell_t l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_asciiLetter(lean_object*);
static lean_once_cell_t l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0;
static lean_once_cell_t l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1;
static lean_once_cell_t l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2;
static lean_once_cell_t l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3;
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
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2(void){
_start:
{
uint32_t v___x_342_; uint8_t v___x_343_; 
v___x_342_ = 48;
v___x_343_ = lean_uint32_to_uint8(v___x_342_);
return v___x_343_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3(void){
_start:
{
uint32_t v___x_344_; uint8_t v___x_345_; 
v___x_344_ = 57;
v___x_345_ = lean_uint32_to_uint8(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digit(lean_object* v_a_346_){
_start:
{
lean_object* v_array_350_; lean_object* v_idx_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v_array_350_ = lean_ctor_get(v_a_346_, 0);
v_idx_351_ = lean_ctor_get(v_a_346_, 1);
v___x_352_ = lean_byte_array_size(v_array_350_);
v___x_353_ = lean_nat_dec_lt(v_idx_351_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_box(0);
v___x_355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_355_, 0, v_a_346_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
return v___x_355_;
}
else
{
uint8_t v_c_356_; uint8_t v___x_357_; uint8_t v___x_358_; 
v_c_356_ = lean_byte_array_fget(v_array_350_, v_idx_351_);
v___x_357_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_358_ = lean_uint8_dec_le(v___x_357_, v_c_356_);
if (v___x_358_ == 0)
{
goto v___jp_347_;
}
else
{
uint8_t v___x_359_; uint8_t v___x_360_; 
v___x_359_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__3, &l_Std_Internal_Parsec_ByteArray_digit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3);
v___x_360_ = lean_uint8_dec_le(v_c_356_, v___x_359_);
if (v___x_360_ == 0)
{
goto v___jp_347_;
}
else
{
lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_372_; 
lean_inc(v_idx_351_);
lean_inc_ref(v_array_350_);
v_isSharedCheck_372_ = !lean_is_exclusive(v_a_346_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; lean_object* v_unused_374_; 
v_unused_373_ = lean_ctor_get(v_a_346_, 1);
lean_dec(v_unused_373_);
v_unused_374_ = lean_ctor_get(v_a_346_, 0);
lean_dec(v_unused_374_);
v___x_362_ = v_a_346_;
v_isShared_363_ = v_isSharedCheck_372_;
goto v_resetjp_361_;
}
else
{
lean_dec(v_a_346_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_372_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v_it_x27_367_; 
v___x_364_ = lean_unsigned_to_nat(1u);
v___x_365_ = lean_nat_add(v_idx_351_, v___x_364_);
lean_dec(v_idx_351_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 1, v___x_365_);
v_it_x27_367_ = v___x_362_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_array_350_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v___x_365_);
v_it_x27_367_ = v_reuseFailAlloc_371_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
uint32_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = lean_uint8_to_uint32(v_c_356_);
v___x_369_ = lean_box_uint32(v___x_368_);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v_it_x27_367_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
return v___x_370_;
}
}
}
}
}
v___jp_347_:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_digit___closed__1));
v___x_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_349_, 0, v_a_346_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(uint8_t v_b_375_){
_start:
{
uint8_t v___x_376_; uint8_t v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_377_ = lean_uint8_sub(v_b_375_, v___x_376_);
v___x_378_ = lean_uint8_to_nat(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat___boxed(lean_object* v_b_379_){
_start:
{
uint8_t v_b_boxed_380_; lean_object* v_res_381_; 
v_b_boxed_380_ = lean_unbox(v_b_379_);
v_res_381_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(v_b_boxed_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object* v_it_382_, lean_object* v_acc_383_){
_start:
{
lean_object* v_array_384_; lean_object* v_idx_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v_array_384_ = lean_ctor_get(v_it_382_, 0);
v_idx_385_ = lean_ctor_get(v_it_382_, 1);
v___x_386_ = lean_byte_array_size(v_array_384_);
v___x_387_ = lean_nat_dec_lt(v_idx_385_, v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v_acc_383_);
lean_ctor_set(v___x_388_, 1, v_it_382_);
return v___x_388_;
}
else
{
uint8_t v_candidate_389_; uint8_t v___x_390_; uint8_t v___x_391_; 
v_candidate_389_ = lean_byte_array_fget(v_array_384_, v_idx_385_);
v___x_390_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_391_ = lean_uint8_dec_le(v___x_390_, v_candidate_389_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v_acc_383_);
lean_ctor_set(v___x_392_, 1, v_it_382_);
return v___x_392_;
}
else
{
uint8_t v___x_393_; uint8_t v___x_394_; 
v___x_393_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__3, &l_Std_Internal_Parsec_ByteArray_digit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3);
v___x_394_ = lean_uint8_dec_le(v_candidate_389_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v_acc_383_);
lean_ctor_set(v___x_395_, 1, v_it_382_);
return v___x_395_;
}
else
{
lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_410_; 
lean_inc(v_idx_385_);
lean_inc_ref(v_array_384_);
v_isSharedCheck_410_ = !lean_is_exclusive(v_it_382_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; lean_object* v_unused_412_; 
v_unused_411_ = lean_ctor_get(v_it_382_, 1);
lean_dec(v_unused_411_);
v_unused_412_ = lean_ctor_get(v_it_382_, 0);
lean_dec(v_unused_412_);
v___x_397_ = v_it_382_;
v_isShared_398_ = v_isSharedCheck_410_;
goto v_resetjp_396_;
}
else
{
lean_dec(v_it_382_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_410_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
uint8_t v___x_399_; lean_object* v_digit_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v_acc_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_399_ = lean_uint8_sub(v_candidate_389_, v___x_390_);
v_digit_400_ = lean_uint8_to_nat(v___x_399_);
v___x_401_ = lean_unsigned_to_nat(10u);
v___x_402_ = lean_nat_mul(v_acc_383_, v___x_401_);
lean_dec(v_acc_383_);
v_acc_403_ = lean_nat_add(v___x_402_, v_digit_400_);
lean_dec(v___x_402_);
v___x_404_ = lean_unsigned_to_nat(1u);
v___x_405_ = lean_nat_add(v_idx_385_, v___x_404_);
lean_dec(v_idx_385_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 1, v___x_405_);
v___x_407_ = v___x_397_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_array_384_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v___x_405_);
v___x_407_ = v_reuseFailAlloc_409_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
v_it_382_ = v___x_407_;
v_acc_383_ = v_acc_403_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore(lean_object* v_acc_413_, lean_object* v_it_414_){
_start:
{
lean_object* v___x_415_; lean_object* v_fst_416_; lean_object* v_snd_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
v___x_415_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_414_, v_acc_413_);
v_fst_416_ = lean_ctor_get(v___x_415_, 0);
v_snd_417_ = lean_ctor_get(v___x_415_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_415_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_snd_417_);
lean_inc(v_fst_416_);
lean_dec(v___x_415_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 1, v_fst_416_);
lean_ctor_set(v___x_419_, 0, v_snd_417_);
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_snd_417_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_fst_416_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digits(lean_object* v_a_425_){
_start:
{
lean_object* v_array_429_; lean_object* v_idx_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_array_429_ = lean_ctor_get(v_a_425_, 0);
v_idx_430_ = lean_ctor_get(v_a_425_, 1);
v___x_431_ = lean_byte_array_size(v_array_429_);
v___x_432_ = lean_nat_dec_lt(v_idx_430_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_box(0);
v___x_434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_434_, 0, v_a_425_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
return v___x_434_;
}
else
{
uint8_t v_c_435_; uint8_t v___x_436_; uint8_t v___x_437_; 
v_c_435_ = lean_byte_array_fget(v_array_429_, v_idx_430_);
v___x_436_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_437_ = lean_uint8_dec_le(v___x_436_, v_c_435_);
if (v___x_437_ == 0)
{
goto v___jp_426_;
}
else
{
uint8_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__3, &l_Std_Internal_Parsec_ByteArray_digit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3);
v___x_439_ = lean_uint8_dec_le(v_c_435_, v___x_438_);
if (v___x_439_ == 0)
{
goto v___jp_426_;
}
else
{
lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_462_; 
lean_inc(v_idx_430_);
lean_inc_ref(v_array_429_);
v_isSharedCheck_462_ = !lean_is_exclusive(v_a_425_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; lean_object* v_unused_464_; 
v_unused_463_ = lean_ctor_get(v_a_425_, 1);
lean_dec(v_unused_463_);
v_unused_464_ = lean_ctor_get(v_a_425_, 0);
lean_dec(v_unused_464_);
v___x_441_ = v_a_425_;
v_isShared_442_ = v_isSharedCheck_462_;
goto v_resetjp_440_;
}
else
{
lean_dec(v_a_425_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_462_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_it_x27_446_; 
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_add(v_idx_430_, v___x_443_);
lean_dec(v_idx_430_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v___x_444_);
v_it_x27_446_ = v___x_441_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_array_429_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_444_);
v_it_x27_446_ = v_reuseFailAlloc_461_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
uint32_t v___x_447_; uint8_t v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v_fst_452_; lean_object* v_snd_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
v___x_447_ = lean_uint8_to_uint32(v_c_435_);
v___x_448_ = lean_uint32_to_uint8(v___x_447_);
v___x_449_ = lean_uint8_sub(v___x_448_, v___x_436_);
v___x_450_ = lean_uint8_to_nat(v___x_449_);
v___x_451_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_446_, v___x_450_);
v_fst_452_ = lean_ctor_get(v___x_451_, 0);
v_snd_453_ = lean_ctor_get(v___x_451_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_451_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_snd_453_);
lean_inc(v_fst_452_);
lean_dec(v___x_451_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v_fst_452_);
lean_ctor_set(v___x_455_, 0, v_snd_453_);
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_snd_453_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_fst_452_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
}
}
v___jp_426_:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_digit___closed__1));
v___x_428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_428_, 0, v_a_425_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
return v___x_428_;
}
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2(void){
_start:
{
uint32_t v___x_468_; uint8_t v___x_469_; 
v___x_468_ = 65;
v___x_469_ = lean_uint32_to_uint8(v___x_468_);
return v___x_469_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3(void){
_start:
{
uint32_t v___x_470_; uint8_t v___x_471_; 
v___x_470_ = 70;
v___x_471_ = lean_uint32_to_uint8(v___x_470_);
return v___x_471_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4(void){
_start:
{
uint32_t v___x_472_; uint8_t v___x_473_; 
v___x_472_ = 97;
v___x_473_ = lean_uint32_to_uint8(v___x_472_);
return v___x_473_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5(void){
_start:
{
uint32_t v___x_474_; uint8_t v___x_475_; 
v___x_474_ = 102;
v___x_475_ = lean_uint32_to_uint8(v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_hexDigit(lean_object* v_a_476_){
_start:
{
lean_object* v_array_480_; lean_object* v_idx_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_array_480_ = lean_ctor_get(v_a_476_, 0);
v_idx_481_ = lean_ctor_get(v_a_476_, 1);
v___x_482_ = lean_byte_array_size(v_array_480_);
v___x_483_ = lean_nat_dec_lt(v_idx_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_box(0);
v___x_485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_485_, 0, v_a_476_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
return v___x_485_;
}
else
{
uint8_t v_c_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v_it_x27_489_; uint8_t v___x_504_; uint8_t v___x_505_; 
v_c_486_ = lean_byte_array_fget(v_array_480_, v_idx_481_);
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_nat_add(v_idx_481_, v___x_487_);
lean_inc_ref(v_array_480_);
v_it_x27_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_489_, 0, v_array_480_);
lean_ctor_set(v_it_x27_489_, 1, v___x_488_);
v___x_504_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_505_ = lean_uint8_dec_le(v___x_504_, v_c_486_);
if (v___x_505_ == 0)
{
goto v___jp_499_;
}
else
{
uint8_t v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__3, &l_Std_Internal_Parsec_ByteArray_digit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3);
v___x_507_ = lean_uint8_dec_le(v_c_486_, v___x_506_);
if (v___x_507_ == 0)
{
goto v___jp_499_;
}
else
{
lean_dec_ref(v_a_476_);
goto v___jp_490_;
}
}
v___jp_490_:
{
uint32_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_uint8_to_uint32(v_c_486_);
v___x_492_ = lean_box_uint32(v___x_491_);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v_it_x27_489_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
return v___x_493_;
}
v___jp_494_:
{
uint8_t v___x_495_; uint8_t v___x_496_; 
v___x_495_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2);
v___x_496_ = lean_uint8_dec_le(v___x_495_, v_c_486_);
if (v___x_496_ == 0)
{
lean_dec_ref_known(v_it_x27_489_, 2);
goto v___jp_477_;
}
else
{
uint8_t v___x_497_; uint8_t v___x_498_; 
v___x_497_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3);
v___x_498_ = lean_uint8_dec_le(v_c_486_, v___x_497_);
if (v___x_498_ == 0)
{
lean_dec_ref_known(v_it_x27_489_, 2);
goto v___jp_477_;
}
else
{
lean_dec_ref(v_a_476_);
goto v___jp_490_;
}
}
}
v___jp_499_:
{
uint8_t v___x_500_; uint8_t v___x_501_; 
v___x_500_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4);
v___x_501_ = lean_uint8_dec_le(v___x_500_, v_c_486_);
if (v___x_501_ == 0)
{
goto v___jp_494_;
}
else
{
uint8_t v___x_502_; uint8_t v___x_503_; 
v___x_502_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5);
v___x_503_ = lean_uint8_dec_le(v_c_486_, v___x_502_);
if (v___x_503_ == 0)
{
goto v___jp_494_;
}
else
{
lean_dec_ref(v_a_476_);
goto v___jp_490_;
}
}
}
}
v___jp_477_:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1));
v___x_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_479_, 0, v_a_476_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
return v___x_479_;
}
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_octDigit___closed__2(void){
_start:
{
uint32_t v___x_511_; uint8_t v___x_512_; 
v___x_511_ = 55;
v___x_512_ = lean_uint32_to_uint8(v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_octDigit(lean_object* v_a_513_){
_start:
{
lean_object* v_array_517_; lean_object* v_idx_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_array_517_ = lean_ctor_get(v_a_513_, 0);
v_idx_518_ = lean_ctor_get(v_a_513_, 1);
v___x_519_ = lean_byte_array_size(v_array_517_);
v___x_520_ = lean_nat_dec_lt(v_idx_518_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_box(0);
v___x_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_522_, 0, v_a_513_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
return v___x_522_;
}
else
{
uint8_t v_c_523_; uint8_t v___x_524_; uint8_t v___x_525_; 
v_c_523_ = lean_byte_array_fget(v_array_517_, v_idx_518_);
v___x_524_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_525_ = lean_uint8_dec_le(v___x_524_, v_c_523_);
if (v___x_525_ == 0)
{
goto v___jp_514_;
}
else
{
uint8_t v___x_526_; uint8_t v___x_527_; 
v___x_526_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_octDigit___closed__2, &l_Std_Internal_Parsec_ByteArray_octDigit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_octDigit___closed__2);
v___x_527_ = lean_uint8_dec_le(v_c_523_, v___x_526_);
if (v___x_527_ == 0)
{
goto v___jp_514_;
}
else
{
lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_539_; 
lean_inc(v_idx_518_);
lean_inc_ref(v_array_517_);
v_isSharedCheck_539_ = !lean_is_exclusive(v_a_513_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; lean_object* v_unused_541_; 
v_unused_540_ = lean_ctor_get(v_a_513_, 1);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_a_513_, 0);
lean_dec(v_unused_541_);
v___x_529_ = v_a_513_;
v_isShared_530_ = v_isSharedCheck_539_;
goto v_resetjp_528_;
}
else
{
lean_dec(v_a_513_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_539_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v_it_x27_534_; 
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_nat_add(v_idx_518_, v___x_531_);
lean_dec(v_idx_518_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 1, v___x_532_);
v_it_x27_534_ = v___x_529_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_array_517_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v___x_532_);
v_it_x27_534_ = v_reuseFailAlloc_538_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
uint32_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = lean_uint8_to_uint32(v_c_523_);
v___x_536_ = lean_box_uint32(v___x_535_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v_it_x27_534_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
return v___x_537_;
}
}
}
}
}
v___jp_514_:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_octDigit___closed__1));
v___x_516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_516_, 0, v_a_513_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
return v___x_516_;
}
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2(void){
_start:
{
uint32_t v___x_545_; uint8_t v___x_546_; 
v___x_545_ = 122;
v___x_546_ = lean_uint32_to_uint8(v___x_545_);
return v___x_546_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3(void){
_start:
{
uint32_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = 90;
v___x_548_ = lean_uint32_to_uint8(v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_asciiLetter(lean_object* v_a_549_){
_start:
{
lean_object* v_array_553_; lean_object* v_idx_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v_array_553_ = lean_ctor_get(v_a_549_, 0);
v_idx_554_ = lean_ctor_get(v_a_549_, 1);
v___x_555_ = lean_byte_array_size(v_array_553_);
v___x_556_ = lean_nat_dec_lt(v_idx_554_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_box(0);
v___x_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_558_, 0, v_a_549_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
return v___x_558_;
}
else
{
uint8_t v_c_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v_it_x27_562_; uint8_t v___x_572_; uint8_t v___x_573_; 
v_c_559_ = lean_byte_array_fget(v_array_553_, v_idx_554_);
v___x_560_ = lean_unsigned_to_nat(1u);
v___x_561_ = lean_nat_add(v_idx_554_, v___x_560_);
lean_inc_ref(v_array_553_);
v_it_x27_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_562_, 0, v_array_553_);
lean_ctor_set(v_it_x27_562_, 1, v___x_561_);
v___x_572_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2);
v___x_573_ = lean_uint8_dec_le(v___x_572_, v_c_559_);
if (v___x_573_ == 0)
{
goto v___jp_567_;
}
else
{
uint8_t v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3, &l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3);
v___x_575_ = lean_uint8_dec_le(v_c_559_, v___x_574_);
if (v___x_575_ == 0)
{
goto v___jp_567_;
}
else
{
lean_dec_ref(v_a_549_);
goto v___jp_563_;
}
}
v___jp_563_:
{
uint32_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = lean_uint8_to_uint32(v_c_559_);
v___x_565_ = lean_box_uint32(v___x_564_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v_it_x27_562_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
return v___x_566_;
}
v___jp_567_:
{
uint8_t v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4);
v___x_569_ = lean_uint8_dec_le(v___x_568_, v_c_559_);
if (v___x_569_ == 0)
{
lean_dec_ref_known(v_it_x27_562_, 2);
goto v___jp_550_;
}
else
{
uint8_t v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2, &l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2);
v___x_571_ = lean_uint8_dec_le(v_c_559_, v___x_570_);
if (v___x_571_ == 0)
{
lean_dec_ref_known(v_it_x27_562_, 2);
goto v___jp_550_;
}
else
{
lean_dec_ref(v_a_549_);
goto v___jp_563_;
}
}
}
}
v___jp_550_:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1));
v___x_552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_552_, 0, v_a_549_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
return v___x_552_;
}
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0(void){
_start:
{
uint32_t v___x_576_; uint8_t v___x_577_; 
v___x_576_ = 9;
v___x_577_ = lean_uint32_to_uint8(v___x_576_);
return v___x_577_;
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1(void){
_start:
{
uint32_t v___x_578_; uint8_t v___x_579_; 
v___x_578_ = 10;
v___x_579_ = lean_uint32_to_uint8(v___x_578_);
return v___x_579_;
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2(void){
_start:
{
uint32_t v___x_580_; uint8_t v___x_581_; 
v___x_580_ = 13;
v___x_581_ = lean_uint32_to_uint8(v___x_580_);
return v___x_581_;
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3(void){
_start:
{
uint32_t v___x_582_; uint8_t v___x_583_; 
v___x_582_ = 32;
v___x_583_ = lean_uint32_to_uint8(v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(lean_object* v_it_584_){
_start:
{
lean_object* v_array_585_; lean_object* v_idx_586_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_array_585_ = lean_ctor_get(v_it_584_, 0);
v_idx_586_ = lean_ctor_get(v_it_584_, 1);
v___x_592_ = lean_byte_array_size(v_array_585_);
v___x_593_ = lean_nat_dec_lt(v_idx_586_, v___x_592_);
if (v___x_593_ == 0)
{
return v_it_584_;
}
else
{
uint8_t v_b_594_; uint8_t v___x_595_; uint8_t v___x_596_; 
v_b_594_ = lean_byte_array_fget(v_array_585_, v_idx_586_);
v___x_595_ = lean_uint8_once(&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0, &l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0_once, _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0);
v___x_596_ = lean_uint8_dec_eq(v_b_594_, v___x_595_);
if (v___x_596_ == 0)
{
uint8_t v___x_597_; uint8_t v___x_598_; 
v___x_597_ = lean_uint8_once(&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1, &l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1_once, _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1);
v___x_598_ = lean_uint8_dec_eq(v_b_594_, v___x_597_);
if (v___x_598_ == 0)
{
uint8_t v___x_599_; uint8_t v___x_600_; 
v___x_599_ = lean_uint8_once(&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2, &l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2_once, _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2);
v___x_600_ = lean_uint8_dec_eq(v_b_594_, v___x_599_);
if (v___x_600_ == 0)
{
uint8_t v___x_601_; uint8_t v___x_602_; 
v___x_601_ = lean_uint8_once(&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3, &l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3_once, _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3);
v___x_602_ = lean_uint8_dec_eq(v_b_594_, v___x_601_);
if (v___x_602_ == 0)
{
return v_it_584_;
}
else
{
lean_inc(v_idx_586_);
lean_inc_ref(v_array_585_);
lean_dec_ref(v_it_584_);
goto v___jp_587_;
}
}
else
{
lean_inc(v_idx_586_);
lean_inc_ref(v_array_585_);
lean_dec_ref(v_it_584_);
goto v___jp_587_;
}
}
else
{
lean_inc(v_idx_586_);
lean_inc_ref(v_array_585_);
lean_dec_ref(v_it_584_);
goto v___jp_587_;
}
}
else
{
lean_inc(v_idx_586_);
lean_inc_ref(v_array_585_);
lean_dec_ref(v_it_584_);
goto v___jp_587_;
}
}
v___jp_587_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = lean_nat_add(v_idx_586_, v___x_588_);
lean_dec(v_idx_586_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v_array_585_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v_it_584_ = v___x_590_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_ws(lean_object* v_it_603_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(v_it_603_);
v___x_605_ = lean_box(0);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take(lean_object* v_n_607_, lean_object* v_it_608_){
_start:
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = l_ByteArray_Iterator_remainingBytes(v_it_608_);
v___x_610_ = lean_nat_dec_lt(v___x_609_, v_n_607_);
lean_dec(v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v_array_611_; lean_object* v_idx_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_631_; 
v_array_611_ = lean_ctor_get(v_it_608_, 0);
v_idx_612_ = lean_ctor_get(v_it_608_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_it_608_);
if (v_isSharedCheck_631_ == 0)
{
v___x_614_ = v_it_608_;
v_isShared_615_ = v_isSharedCheck_631_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_idx_612_);
lean_inc(v_array_611_);
lean_dec(v_it_608_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_631_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = lean_nat_add(v_idx_612_, v_n_607_);
lean_inc(v___x_616_);
lean_inc_ref(v_array_611_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v___x_616_);
v___x_618_ = v___x_614_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_array_611_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v___x_616_);
v___x_618_ = v_reuseFailAlloc_630_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v_lower_620_; lean_object* v_upper_621_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___y_627_; uint8_t v___x_629_; 
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = lean_byte_array_size(v_array_611_);
v___x_629_ = lean_nat_dec_le(v_idx_612_, v___x_624_);
if (v___x_629_ == 0)
{
v___y_627_ = v_idx_612_;
goto v___jp_626_;
}
else
{
lean_dec(v_idx_612_);
v___y_627_ = v___x_624_;
goto v___jp_626_;
}
v___jp_619_:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = l_ByteArray_toByteSlice(v_array_611_, v_lower_620_, v_upper_621_);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_618_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
return v___x_623_;
}
v___jp_626_:
{
uint8_t v___x_628_; 
v___x_628_ = lean_nat_dec_le(v___x_616_, v___x_625_);
if (v___x_628_ == 0)
{
lean_dec(v___x_616_);
v_lower_620_ = v___y_627_;
v_upper_621_ = v___x_625_;
goto v___jp_619_;
}
else
{
v_lower_620_ = v___y_627_;
v_upper_621_ = v___x_616_;
goto v___jp_619_;
}
}
}
}
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_box(0);
v___x_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_633_, 0, v_it_608_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take___boxed(lean_object* v_n_634_, lean_object* v_it_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Std_Internal_Parsec_ByteArray_take(v_n_634_, v_it_635_);
lean_dec(v_n_634_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(lean_object* v_pred_637_, lean_object* v_count_638_, lean_object* v_iter_639_){
_start:
{
lean_object* v_array_640_; lean_object* v_idx_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_array_640_ = lean_ctor_get(v_iter_639_, 0);
v_idx_641_ = lean_ctor_get(v_iter_639_, 1);
v___x_642_ = lean_byte_array_size(v_array_640_);
v___x_643_ = lean_nat_dec_lt(v_idx_641_, v___x_642_);
if (v___x_643_ == 0)
{
uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
lean_dec_ref(v_pred_637_);
v___x_644_ = 1;
v___x_645_ = lean_box(v___x_644_);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v_iter_639_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v_count_638_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
return v___x_647_;
}
else
{
uint8_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_648_ = lean_byte_array_fget(v_array_640_, v_idx_641_);
v___x_649_ = lean_box(v___x_648_);
lean_inc_ref(v_pred_637_);
v___x_650_ = lean_apply_1(v_pred_637_, v___x_649_);
v___x_651_ = lean_unbox(v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec_ref(v_pred_637_);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v_iter_639_);
lean_ctor_set(v___x_652_, 1, v___x_650_);
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v_count_638_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
return v___x_653_;
}
else
{
lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_664_; 
lean_inc(v_idx_641_);
lean_inc_ref(v_array_640_);
v_isSharedCheck_664_ = !lean_is_exclusive(v_iter_639_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; lean_object* v_unused_666_; 
v_unused_665_ = lean_ctor_get(v_iter_639_, 1);
lean_dec(v_unused_665_);
v_unused_666_ = lean_ctor_get(v_iter_639_, 0);
lean_dec(v_unused_666_);
v___x_655_ = v_iter_639_;
v_isShared_656_ = v_isSharedCheck_664_;
goto v_resetjp_654_;
}
else
{
lean_dec(v_iter_639_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_664_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_nat_add(v_count_638_, v___x_657_);
lean_dec(v_count_638_);
v___x_659_ = lean_nat_add(v_idx_641_, v___x_657_);
lean_dec(v_idx_641_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v___x_659_);
v___x_661_ = v___x_655_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_array_640_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_659_);
v___x_661_ = v_reuseFailAlloc_663_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
v_count_638_ = v___x_658_;
v_iter_639_ = v___x_661_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object* v_pred_667_, lean_object* v_limit_668_, lean_object* v_count_669_, lean_object* v_iter_670_){
_start:
{
uint8_t v___x_671_; 
v___x_671_ = lean_nat_dec_le(v_limit_668_, v_count_669_);
if (v___x_671_ == 0)
{
lean_object* v_array_672_; lean_object* v_idx_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v_array_672_ = lean_ctor_get(v_iter_670_, 0);
v_idx_673_ = lean_ctor_get(v_iter_670_, 1);
v___x_674_ = lean_byte_array_size(v_array_672_);
v___x_675_ = lean_nat_dec_lt(v_idx_673_, v___x_674_);
if (v___x_675_ == 0)
{
uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec_ref(v_pred_667_);
v___x_676_ = 1;
v___x_677_ = lean_box(v___x_676_);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v_iter_670_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v_count_669_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
return v___x_679_;
}
else
{
uint8_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_680_ = lean_byte_array_fget(v_array_672_, v_idx_673_);
v___x_681_ = lean_box(v___x_680_);
lean_inc_ref(v_pred_667_);
v___x_682_ = lean_apply_1(v_pred_667_, v___x_681_);
v___x_683_ = lean_unbox(v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; 
lean_dec_ref(v_pred_667_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v_iter_670_);
lean_ctor_set(v___x_684_, 1, v___x_682_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v_count_669_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
return v___x_685_;
}
else
{
lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_696_; 
lean_inc(v_idx_673_);
lean_inc_ref(v_array_672_);
v_isSharedCheck_696_ = !lean_is_exclusive(v_iter_670_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; lean_object* v_unused_698_; 
v_unused_697_ = lean_ctor_get(v_iter_670_, 1);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_iter_670_, 0);
lean_dec(v_unused_698_);
v___x_687_ = v_iter_670_;
v_isShared_688_ = v_isSharedCheck_696_;
goto v_resetjp_686_;
}
else
{
lean_dec(v_iter_670_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_696_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_689_ = lean_unsigned_to_nat(1u);
v___x_690_ = lean_nat_add(v_count_669_, v___x_689_);
lean_dec(v_count_669_);
v___x_691_ = lean_nat_add(v_idx_673_, v___x_689_);
lean_dec(v_idx_673_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_691_);
v___x_693_ = v___x_687_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_array_672_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_691_);
v___x_693_ = v_reuseFailAlloc_695_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
v_count_669_ = v___x_690_;
v_iter_670_ = v___x_693_;
goto _start;
}
}
}
}
}
else
{
uint8_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
lean_dec_ref(v_pred_667_);
v___x_699_ = 0;
v___x_700_ = lean_box(v___x_699_);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v_iter_670_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v_count_669_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo___boxed(lean_object* v_pred_703_, lean_object* v_limit_704_, lean_object* v_count_705_, lean_object* v_iter_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_703_, v_limit_704_, v_count_705_, v_iter_706_);
lean_dec(v_limit_704_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile(lean_object* v_pred_708_, lean_object* v_it_709_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_snd_712_; lean_object* v_snd_713_; uint8_t v___x_714_; 
v___x_710_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_709_);
v___x_711_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v_pred_708_, v___x_710_, v_it_709_);
v_snd_712_ = lean_ctor_get(v___x_711_, 1);
lean_inc(v_snd_712_);
v_snd_713_ = lean_ctor_get(v_snd_712_, 1);
v___x_714_ = lean_unbox(v_snd_713_);
if (v___x_714_ == 0)
{
lean_object* v_fst_715_; lean_object* v_fst_716_; lean_object* v_array_717_; lean_object* v_idx_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_735_; 
v_fst_715_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_fst_715_);
lean_dec_ref(v___x_711_);
v_fst_716_ = lean_ctor_get(v_snd_712_, 0);
lean_inc(v_fst_716_);
lean_dec(v_snd_712_);
v_array_717_ = lean_ctor_get(v_it_709_, 0);
v_idx_718_ = lean_ctor_get(v_it_709_, 1);
v_isSharedCheck_735_ = !lean_is_exclusive(v_it_709_);
if (v_isSharedCheck_735_ == 0)
{
v___x_720_ = v_it_709_;
v_isShared_721_ = v_isSharedCheck_735_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_idx_718_);
lean_inc(v_array_717_);
lean_dec(v_it_709_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_735_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v_lower_723_; lean_object* v_upper_724_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___y_732_; uint8_t v___x_734_; 
v___x_729_ = lean_nat_add(v_idx_718_, v_fst_715_);
lean_dec(v_fst_715_);
v___x_730_ = lean_byte_array_size(v_array_717_);
v___x_734_ = lean_nat_dec_le(v_idx_718_, v___x_710_);
if (v___x_734_ == 0)
{
v___y_732_ = v_idx_718_;
goto v___jp_731_;
}
else
{
lean_dec(v_idx_718_);
v___y_732_ = v___x_710_;
goto v___jp_731_;
}
v___jp_722_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = l_ByteArray_toByteSlice(v_array_717_, v_lower_723_, v_upper_724_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v___x_725_);
lean_ctor_set(v___x_720_, 0, v_fst_716_);
v___x_727_ = v___x_720_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_fst_716_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
v___jp_731_:
{
uint8_t v___x_733_; 
v___x_733_ = lean_nat_dec_le(v___x_729_, v___x_730_);
if (v___x_733_ == 0)
{
lean_dec(v___x_729_);
v_lower_723_ = v___y_732_;
v_upper_724_ = v___x_730_;
goto v___jp_722_;
}
else
{
v_lower_723_ = v___y_732_;
v_upper_724_ = v___x_729_;
goto v___jp_722_;
}
}
}
}
else
{
lean_object* v_fst_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_744_; 
lean_dec_ref(v___x_711_);
lean_dec_ref(v_it_709_);
v_fst_736_ = lean_ctor_get(v_snd_712_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_snd_712_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v_snd_712_, 1);
lean_dec(v_unused_745_);
v___x_738_ = v_snd_712_;
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_fst_736_);
lean_dec(v_snd_712_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_740_ = lean_box(0);
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 1);
lean_ctor_set(v___x_738_, 1, v___x_740_);
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_fst_736_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(lean_object* v_pred_746_, uint8_t v_b_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_748_ = lean_box(v_b_747_);
v___x_749_ = lean_apply_1(v_pred_746_, v___x_748_);
v___x_750_ = lean_unbox(v___x_749_);
if (v___x_750_ == 0)
{
uint8_t v___x_751_; 
v___x_751_ = 1;
return v___x_751_;
}
else
{
uint8_t v___x_752_; 
v___x_752_ = 0;
return v___x_752_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed(lean_object* v_pred_753_, lean_object* v_b_754_){
_start:
{
uint8_t v_b_boxed_755_; uint8_t v_res_756_; lean_object* v_r_757_; 
v_b_boxed_755_ = lean_unbox(v_b_754_);
v_res_756_ = l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(v_pred_753_, v_b_boxed_755_);
v_r_757_ = lean_box(v_res_756_);
return v_r_757_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil(lean_object* v_pred_758_, lean_object* v_a_759_){
_start:
{
lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v_snd_763_; lean_object* v_snd_764_; uint8_t v___x_765_; 
v___f_760_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_760_, 0, v_pred_758_);
v___x_761_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_759_);
v___x_762_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v___f_760_, v___x_761_, v_a_759_);
v_snd_763_ = lean_ctor_get(v___x_762_, 1);
lean_inc(v_snd_763_);
v_snd_764_ = lean_ctor_get(v_snd_763_, 1);
v___x_765_ = lean_unbox(v_snd_764_);
if (v___x_765_ == 0)
{
lean_object* v_fst_766_; lean_object* v_fst_767_; lean_object* v_array_768_; lean_object* v_idx_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_786_; 
v_fst_766_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_fst_766_);
lean_dec_ref(v___x_762_);
v_fst_767_ = lean_ctor_get(v_snd_763_, 0);
lean_inc(v_fst_767_);
lean_dec(v_snd_763_);
v_array_768_ = lean_ctor_get(v_a_759_, 0);
v_idx_769_ = lean_ctor_get(v_a_759_, 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v_a_759_);
if (v_isSharedCheck_786_ == 0)
{
v___x_771_ = v_a_759_;
v_isShared_772_ = v_isSharedCheck_786_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_idx_769_);
lean_inc(v_array_768_);
lean_dec(v_a_759_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_786_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v_lower_774_; lean_object* v_upper_775_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___y_783_; uint8_t v___x_785_; 
v___x_780_ = lean_nat_add(v_idx_769_, v_fst_766_);
lean_dec(v_fst_766_);
v___x_781_ = lean_byte_array_size(v_array_768_);
v___x_785_ = lean_nat_dec_le(v_idx_769_, v___x_761_);
if (v___x_785_ == 0)
{
v___y_783_ = v_idx_769_;
goto v___jp_782_;
}
else
{
lean_dec(v_idx_769_);
v___y_783_ = v___x_761_;
goto v___jp_782_;
}
v___jp_773_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = l_ByteArray_toByteSlice(v_array_768_, v_lower_774_, v_upper_775_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___x_776_);
lean_ctor_set(v___x_771_, 0, v_fst_767_);
v___x_778_ = v___x_771_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_fst_767_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
v___jp_782_:
{
uint8_t v___x_784_; 
v___x_784_ = lean_nat_dec_le(v___x_780_, v___x_781_);
if (v___x_784_ == 0)
{
lean_dec(v___x_780_);
v_lower_774_ = v___y_783_;
v_upper_775_ = v___x_781_;
goto v___jp_773_;
}
else
{
v_lower_774_ = v___y_783_;
v_upper_775_ = v___x_780_;
goto v___jp_773_;
}
}
}
}
else
{
lean_object* v_fst_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_795_; 
lean_dec_ref(v___x_762_);
lean_dec_ref(v_a_759_);
v_fst_787_ = lean_ctor_get(v_snd_763_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v_snd_763_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v_snd_763_, 1);
lean_dec(v_unused_796_);
v___x_789_ = v_snd_763_;
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_fst_787_);
lean_dec(v_snd_763_);
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
lean_ctor_set_tag(v___x_789_, 1);
lean_ctor_set(v___x_789_, 1, v___x_791_);
v___x_793_ = v___x_789_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 2, 0);
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
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhile(lean_object* v_pred_797_, lean_object* v_it_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v_snd_801_; lean_object* v_snd_802_; uint8_t v___x_803_; 
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v_pred_797_, v___x_799_, v_it_798_);
v_snd_801_ = lean_ctor_get(v___x_800_, 1);
lean_inc(v_snd_801_);
lean_dec_ref(v___x_800_);
v_snd_802_ = lean_ctor_get(v_snd_801_, 1);
v___x_803_ = lean_unbox(v_snd_802_);
if (v___x_803_ == 0)
{
lean_object* v_fst_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_812_; 
v_fst_804_ = lean_ctor_get(v_snd_801_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v_snd_801_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v_snd_801_, 1);
lean_dec(v_unused_813_);
v___x_806_ = v_snd_801_;
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_fst_804_);
lean_dec(v_snd_801_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = lean_box(0);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 1, v___x_808_);
v___x_810_ = v___x_806_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_fst_804_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
else
{
lean_object* v_fst_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_822_; 
v_fst_814_ = lean_ctor_get(v_snd_801_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v_snd_801_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_snd_801_, 1);
lean_dec(v_unused_823_);
v___x_816_ = v_snd_801_;
v_isShared_817_ = v_isSharedCheck_822_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_fst_814_);
lean_dec(v_snd_801_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_822_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = lean_box(0);
if (v_isShared_817_ == 0)
{
lean_ctor_set_tag(v___x_816_, 1);
lean_ctor_set(v___x_816_, 1, v___x_818_);
v___x_820_ = v___x_816_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_fst_814_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntil(lean_object* v_pred_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___f_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v_snd_829_; lean_object* v_snd_830_; uint8_t v___x_831_; 
v___f_826_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_826_, 0, v_pred_824_);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v___f_826_, v___x_827_, v_a_825_);
v_snd_829_ = lean_ctor_get(v___x_828_, 1);
lean_inc(v_snd_829_);
lean_dec_ref(v___x_828_);
v_snd_830_ = lean_ctor_get(v_snd_829_, 1);
v___x_831_ = lean_unbox(v_snd_830_);
if (v___x_831_ == 0)
{
lean_object* v_fst_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_840_; 
v_fst_832_ = lean_ctor_get(v_snd_829_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v_snd_829_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v_snd_829_, 1);
lean_dec(v_unused_841_);
v___x_834_ = v_snd_829_;
v_isShared_835_ = v_isSharedCheck_840_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_fst_832_);
lean_dec(v_snd_829_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_840_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_box(0);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v___x_836_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_fst_832_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
else
{
lean_object* v_fst_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_850_; 
v_fst_842_ = lean_ctor_get(v_snd_829_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v_snd_829_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v_snd_829_, 1);
lean_dec(v_unused_851_);
v___x_844_ = v_snd_829_;
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_fst_842_);
lean_dec(v_snd_829_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = lean_box(0);
if (v_isShared_845_ == 0)
{
lean_ctor_set_tag(v___x_844_, 1);
lean_ctor_set(v___x_844_, 1, v___x_846_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_fst_842_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(lean_object* v_pred_852_, lean_object* v_limit_853_, lean_object* v_it_854_){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v_snd_857_; lean_object* v_snd_858_; uint8_t v___x_859_; 
v___x_855_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_854_);
v___x_856_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_852_, v_limit_853_, v___x_855_, v_it_854_);
v_snd_857_ = lean_ctor_get(v___x_856_, 1);
lean_inc(v_snd_857_);
v_snd_858_ = lean_ctor_get(v_snd_857_, 1);
v___x_859_ = lean_unbox(v_snd_858_);
if (v___x_859_ == 0)
{
lean_object* v_fst_860_; lean_object* v_fst_861_; lean_object* v_array_862_; lean_object* v_idx_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_880_; 
v_fst_860_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_fst_860_);
lean_dec_ref(v___x_856_);
v_fst_861_ = lean_ctor_get(v_snd_857_, 0);
lean_inc(v_fst_861_);
lean_dec(v_snd_857_);
v_array_862_ = lean_ctor_get(v_it_854_, 0);
v_idx_863_ = lean_ctor_get(v_it_854_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v_it_854_);
if (v_isSharedCheck_880_ == 0)
{
v___x_865_ = v_it_854_;
v_isShared_866_ = v_isSharedCheck_880_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_idx_863_);
lean_inc(v_array_862_);
lean_dec(v_it_854_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_880_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_lower_868_; lean_object* v_upper_869_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___y_877_; uint8_t v___x_879_; 
v___x_874_ = lean_nat_add(v_idx_863_, v_fst_860_);
lean_dec(v_fst_860_);
v___x_875_ = lean_byte_array_size(v_array_862_);
v___x_879_ = lean_nat_dec_le(v_idx_863_, v___x_855_);
if (v___x_879_ == 0)
{
v___y_877_ = v_idx_863_;
goto v___jp_876_;
}
else
{
lean_dec(v_idx_863_);
v___y_877_ = v___x_855_;
goto v___jp_876_;
}
v___jp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = l_ByteArray_toByteSlice(v_array_862_, v_lower_868_, v_upper_869_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 1, v___x_870_);
lean_ctor_set(v___x_865_, 0, v_fst_861_);
v___x_872_ = v___x_865_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_fst_861_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
v___jp_876_:
{
uint8_t v___x_878_; 
v___x_878_ = lean_nat_dec_le(v___x_874_, v___x_875_);
if (v___x_878_ == 0)
{
lean_dec(v___x_874_);
v_lower_868_ = v___y_877_;
v_upper_869_ = v___x_875_;
goto v___jp_867_;
}
else
{
v_lower_868_ = v___y_877_;
v_upper_869_ = v___x_874_;
goto v___jp_867_;
}
}
}
}
else
{
lean_object* v_fst_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_889_; 
lean_dec_ref(v___x_856_);
lean_dec_ref(v_it_854_);
v_fst_881_ = lean_ctor_get(v_snd_857_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v_snd_857_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v_snd_857_, 1);
lean_dec(v_unused_890_);
v___x_883_ = v_snd_857_;
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_fst_881_);
lean_dec(v_snd_857_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = lean_box(0);
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 1);
lean_ctor_set(v___x_883_, 1, v___x_885_);
v___x_887_ = v___x_883_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_fst_881_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_885_);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo___boxed(lean_object* v_pred_891_, lean_object* v_limit_892_, lean_object* v_it_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(v_pred_891_, v_limit_892_, v_it_893_);
lean_dec(v_limit_892_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(lean_object* v_pred_898_, lean_object* v_limit_899_, lean_object* v_it_900_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v_snd_903_; lean_object* v_snd_904_; uint8_t v___x_905_; 
v___x_901_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_900_);
v___x_902_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_898_, v_limit_899_, v___x_901_, v_it_900_);
v_snd_903_ = lean_ctor_get(v___x_902_, 1);
lean_inc(v_snd_903_);
v_snd_904_ = lean_ctor_get(v_snd_903_, 1);
v___x_905_ = lean_unbox(v_snd_904_);
if (v___x_905_ == 0)
{
lean_object* v_fst_906_; lean_object* v_fst_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_935_; 
v_fst_906_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_fst_906_);
lean_dec_ref(v___x_902_);
v_fst_907_ = lean_ctor_get(v_snd_903_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v_snd_903_);
if (v_isSharedCheck_935_ == 0)
{
lean_object* v_unused_936_; 
v_unused_936_ = lean_ctor_get(v_snd_903_, 1);
lean_dec(v_unused_936_);
v___x_909_ = v_snd_903_;
v_isShared_910_ = v_isSharedCheck_935_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_fst_907_);
lean_dec(v_snd_903_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_935_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
uint8_t v___x_911_; 
v___x_911_ = lean_nat_dec_eq(v_fst_906_, v___x_901_);
if (v___x_911_ == 0)
{
lean_object* v_array_912_; lean_object* v_idx_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_930_; 
lean_del_object(v___x_909_);
v_array_912_ = lean_ctor_get(v_it_900_, 0);
v_idx_913_ = lean_ctor_get(v_it_900_, 1);
v_isSharedCheck_930_ = !lean_is_exclusive(v_it_900_);
if (v_isSharedCheck_930_ == 0)
{
v___x_915_ = v_it_900_;
v_isShared_916_ = v_isSharedCheck_930_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_idx_913_);
lean_inc(v_array_912_);
lean_dec(v_it_900_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_930_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v_lower_918_; lean_object* v_upper_919_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___y_927_; uint8_t v___x_929_; 
v___x_924_ = lean_nat_add(v_idx_913_, v_fst_906_);
lean_dec(v_fst_906_);
v___x_925_ = lean_byte_array_size(v_array_912_);
v___x_929_ = lean_nat_dec_le(v_idx_913_, v___x_901_);
if (v___x_929_ == 0)
{
v___y_927_ = v_idx_913_;
goto v___jp_926_;
}
else
{
lean_dec(v_idx_913_);
v___y_927_ = v___x_901_;
goto v___jp_926_;
}
v___jp_917_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_920_ = l_ByteArray_toByteSlice(v_array_912_, v_lower_918_, v_upper_919_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 1, v___x_920_);
lean_ctor_set(v___x_915_, 0, v_fst_907_);
v___x_922_ = v___x_915_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_fst_907_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
v___jp_926_:
{
uint8_t v___x_928_; 
v___x_928_ = lean_nat_dec_le(v___x_924_, v___x_925_);
if (v___x_928_ == 0)
{
lean_dec(v___x_924_);
v_lower_918_ = v___y_927_;
v_upper_919_ = v___x_925_;
goto v___jp_917_;
}
else
{
v_lower_918_ = v___y_927_;
v_upper_919_ = v___x_924_;
goto v___jp_917_;
}
}
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_933_; 
lean_dec(v_fst_907_);
lean_dec(v_fst_906_);
v___x_931_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1));
if (v_isShared_910_ == 0)
{
lean_ctor_set_tag(v___x_909_, 1);
lean_ctor_set(v___x_909_, 1, v___x_931_);
lean_ctor_set(v___x_909_, 0, v_it_900_);
v___x_933_ = v___x_909_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_it_900_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v_fst_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_945_; 
lean_dec_ref(v___x_902_);
lean_dec_ref(v_it_900_);
v_fst_937_ = lean_ctor_get(v_snd_903_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v_snd_903_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v_snd_903_, 1);
lean_dec(v_unused_946_);
v___x_939_ = v_snd_903_;
v_isShared_940_ = v_isSharedCheck_945_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_fst_937_);
lean_dec(v_snd_903_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_945_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_941_ = lean_box(0);
if (v_isShared_940_ == 0)
{
lean_ctor_set_tag(v___x_939_, 1);
lean_ctor_set(v___x_939_, 1, v___x_941_);
v___x_943_ = v___x_939_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_fst_937_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___boxed(lean_object* v_pred_947_, lean_object* v_limit_948_, lean_object* v_it_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(v_pred_947_, v_limit_948_, v_it_949_);
lean_dec(v_limit_948_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(lean_object* v_pred_951_, lean_object* v_limit_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___f_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v_snd_957_; lean_object* v_snd_958_; uint8_t v___x_959_; 
v___f_954_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_954_, 0, v_pred_951_);
v___x_955_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_953_);
v___x_956_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_954_, v_limit_952_, v___x_955_, v_a_953_);
v_snd_957_ = lean_ctor_get(v___x_956_, 1);
lean_inc(v_snd_957_);
v_snd_958_ = lean_ctor_get(v_snd_957_, 1);
v___x_959_ = lean_unbox(v_snd_958_);
if (v___x_959_ == 0)
{
lean_object* v_fst_960_; lean_object* v_fst_961_; lean_object* v_array_962_; lean_object* v_idx_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_980_; 
v_fst_960_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_fst_960_);
lean_dec_ref(v___x_956_);
v_fst_961_ = lean_ctor_get(v_snd_957_, 0);
lean_inc(v_fst_961_);
lean_dec(v_snd_957_);
v_array_962_ = lean_ctor_get(v_a_953_, 0);
v_idx_963_ = lean_ctor_get(v_a_953_, 1);
v_isSharedCheck_980_ = !lean_is_exclusive(v_a_953_);
if (v_isSharedCheck_980_ == 0)
{
v___x_965_ = v_a_953_;
v_isShared_966_ = v_isSharedCheck_980_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_idx_963_);
lean_inc(v_array_962_);
lean_dec(v_a_953_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_980_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v_lower_968_; lean_object* v_upper_969_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___y_977_; uint8_t v___x_979_; 
v___x_974_ = lean_nat_add(v_idx_963_, v_fst_960_);
lean_dec(v_fst_960_);
v___x_975_ = lean_byte_array_size(v_array_962_);
v___x_979_ = lean_nat_dec_le(v_idx_963_, v___x_955_);
if (v___x_979_ == 0)
{
v___y_977_ = v_idx_963_;
goto v___jp_976_;
}
else
{
lean_dec(v_idx_963_);
v___y_977_ = v___x_955_;
goto v___jp_976_;
}
v___jp_967_:
{
lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_970_ = l_ByteArray_toByteSlice(v_array_962_, v_lower_968_, v_upper_969_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 1, v___x_970_);
lean_ctor_set(v___x_965_, 0, v_fst_961_);
v___x_972_ = v___x_965_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_fst_961_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
v___jp_976_:
{
uint8_t v___x_978_; 
v___x_978_ = lean_nat_dec_le(v___x_974_, v___x_975_);
if (v___x_978_ == 0)
{
lean_dec(v___x_974_);
v_lower_968_ = v___y_977_;
v_upper_969_ = v___x_975_;
goto v___jp_967_;
}
else
{
v_lower_968_ = v___y_977_;
v_upper_969_ = v___x_974_;
goto v___jp_967_;
}
}
}
}
else
{
lean_object* v_fst_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_989_; 
lean_dec_ref(v___x_956_);
lean_dec_ref(v_a_953_);
v_fst_981_ = lean_ctor_get(v_snd_957_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v_snd_957_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; 
v_unused_990_ = lean_ctor_get(v_snd_957_, 1);
lean_dec(v_unused_990_);
v___x_983_ = v_snd_957_;
v_isShared_984_ = v_isSharedCheck_989_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_fst_981_);
lean_dec(v_snd_957_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_989_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_985_ = lean_box(0);
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 1);
lean_ctor_set(v___x_983_, 1, v___x_985_);
v___x_987_ = v___x_983_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_fst_981_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo___boxed(lean_object* v_pred_991_, lean_object* v_limit_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(v_pred_991_, v_limit_992_, v_a_993_);
lean_dec(v_limit_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileAtMost(lean_object* v_pred_995_, lean_object* v_limit_996_, lean_object* v_it_997_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v_snd_1000_; lean_object* v_fst_1001_; lean_object* v_fst_1002_; lean_object* v_array_1003_; lean_object* v_idx_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1021_; 
v___x_998_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_997_);
v___x_999_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_995_, v_limit_996_, v___x_998_, v_it_997_);
v_snd_1000_ = lean_ctor_get(v___x_999_, 1);
lean_inc(v_snd_1000_);
v_fst_1001_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_fst_1001_);
lean_dec_ref(v___x_999_);
v_fst_1002_ = lean_ctor_get(v_snd_1000_, 0);
lean_inc(v_fst_1002_);
lean_dec(v_snd_1000_);
v_array_1003_ = lean_ctor_get(v_it_997_, 0);
v_idx_1004_ = lean_ctor_get(v_it_997_, 1);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_it_997_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1006_ = v_it_997_;
v_isShared_1007_ = v_isSharedCheck_1021_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_idx_1004_);
lean_inc(v_array_1003_);
lean_dec(v_it_997_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1021_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_lower_1009_; lean_object* v_upper_1010_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___y_1018_; uint8_t v___x_1020_; 
v___x_1015_ = lean_nat_add(v_idx_1004_, v_fst_1001_);
lean_dec(v_fst_1001_);
v___x_1016_ = lean_byte_array_size(v_array_1003_);
v___x_1020_ = lean_nat_dec_le(v_idx_1004_, v___x_998_);
if (v___x_1020_ == 0)
{
v___y_1018_ = v_idx_1004_;
goto v___jp_1017_;
}
else
{
lean_dec(v_idx_1004_);
v___y_1018_ = v___x_998_;
goto v___jp_1017_;
}
v___jp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1011_ = l_ByteArray_toByteSlice(v_array_1003_, v_lower_1009_, v_upper_1010_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 1, v___x_1011_);
lean_ctor_set(v___x_1006_, 0, v_fst_1002_);
v___x_1013_ = v___x_1006_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_fst_1002_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
v___jp_1017_:
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_nat_dec_le(v___x_1015_, v___x_1016_);
if (v___x_1019_ == 0)
{
lean_dec(v___x_1015_);
v_lower_1009_ = v___y_1018_;
v_upper_1010_ = v___x_1016_;
goto v___jp_1008_;
}
else
{
v_lower_1009_ = v___y_1018_;
v_upper_1010_ = v___x_1015_;
goto v___jp_1008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileAtMost___boxed(lean_object* v_pred_1022_, lean_object* v_limit_1023_, lean_object* v_it_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Std_Internal_Parsec_ByteArray_takeWhileAtMost(v_pred_1022_, v_limit_1023_, v_it_1024_);
lean_dec(v_limit_1023_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost(lean_object* v_pred_1026_, lean_object* v_limit_1027_, lean_object* v_it_1028_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v_snd_1031_; lean_object* v_fst_1032_; lean_object* v_fst_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1061_; 
v___x_1029_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_1028_);
v___x_1030_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_1026_, v_limit_1027_, v___x_1029_, v_it_1028_);
v_snd_1031_ = lean_ctor_get(v___x_1030_, 1);
lean_inc(v_snd_1031_);
v_fst_1032_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_fst_1032_);
lean_dec_ref(v___x_1030_);
v_fst_1033_ = lean_ctor_get(v_snd_1031_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_snd_1031_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v_snd_1031_, 1);
lean_dec(v_unused_1062_);
v___x_1035_ = v_snd_1031_;
v_isShared_1036_ = v_isSharedCheck_1061_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_fst_1033_);
lean_dec(v_snd_1031_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1061_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
uint8_t v___x_1037_; 
v___x_1037_ = lean_nat_dec_eq(v_fst_1032_, v___x_1029_);
if (v___x_1037_ == 0)
{
lean_object* v_array_1038_; lean_object* v_idx_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1056_; 
lean_del_object(v___x_1035_);
v_array_1038_ = lean_ctor_get(v_it_1028_, 0);
v_idx_1039_ = lean_ctor_get(v_it_1028_, 1);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_it_1028_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1041_ = v_it_1028_;
v_isShared_1042_ = v_isSharedCheck_1056_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_idx_1039_);
lean_inc(v_array_1038_);
lean_dec(v_it_1028_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1056_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_lower_1044_; lean_object* v_upper_1045_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___y_1053_; uint8_t v___x_1055_; 
v___x_1050_ = lean_nat_add(v_idx_1039_, v_fst_1032_);
lean_dec(v_fst_1032_);
v___x_1051_ = lean_byte_array_size(v_array_1038_);
v___x_1055_ = lean_nat_dec_le(v_idx_1039_, v___x_1029_);
if (v___x_1055_ == 0)
{
v___y_1053_ = v_idx_1039_;
goto v___jp_1052_;
}
else
{
lean_dec(v_idx_1039_);
v___y_1053_ = v___x_1029_;
goto v___jp_1052_;
}
v___jp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1046_ = l_ByteArray_toByteSlice(v_array_1038_, v_lower_1044_, v_upper_1045_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 1, v___x_1046_);
lean_ctor_set(v___x_1041_, 0, v_fst_1033_);
v___x_1048_ = v___x_1041_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_fst_1033_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
v___jp_1052_:
{
uint8_t v___x_1054_; 
v___x_1054_ = lean_nat_dec_le(v___x_1050_, v___x_1051_);
if (v___x_1054_ == 0)
{
lean_dec(v___x_1050_);
v_lower_1044_ = v___y_1053_;
v_upper_1045_ = v___x_1051_;
goto v___jp_1043_;
}
else
{
v_lower_1044_ = v___y_1053_;
v_upper_1045_ = v___x_1050_;
goto v___jp_1043_;
}
}
}
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
lean_dec(v_fst_1033_);
lean_dec(v_fst_1032_);
v___x_1057_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1));
if (v_isShared_1036_ == 0)
{
lean_ctor_set_tag(v___x_1035_, 1);
lean_ctor_set(v___x_1035_, 1, v___x_1057_);
lean_ctor_set(v___x_1035_, 0, v_it_1028_);
v___x_1059_ = v___x_1035_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_it_1028_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost___boxed(lean_object* v_pred_1063_, lean_object* v_limit_1064_, lean_object* v_it_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost(v_pred_1063_, v_limit_1064_, v_it_1065_);
lean_dec(v_limit_1064_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(lean_object* v_pred_1067_, lean_object* v_limit_1068_, lean_object* v_it_1069_){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_snd_1072_; lean_object* v_snd_1073_; uint8_t v___x_1074_; 
v___x_1070_ = lean_unsigned_to_nat(0u);
v___x_1071_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_1067_, v_limit_1068_, v___x_1070_, v_it_1069_);
v_snd_1072_ = lean_ctor_get(v___x_1071_, 1);
lean_inc(v_snd_1072_);
lean_dec_ref(v___x_1071_);
v_snd_1073_ = lean_ctor_get(v_snd_1072_, 1);
v___x_1074_ = lean_unbox(v_snd_1073_);
if (v___x_1074_ == 0)
{
lean_object* v_fst_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1083_; 
v_fst_1075_ = lean_ctor_get(v_snd_1072_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_snd_1072_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v_snd_1072_, 1);
lean_dec(v_unused_1084_);
v___x_1077_ = v_snd_1072_;
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_fst_1075_);
lean_dec(v_snd_1072_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = lean_box(0);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_fst_1075_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
else
{
lean_object* v_fst_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1093_; 
v_fst_1085_ = lean_ctor_get(v_snd_1072_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_snd_1072_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; 
v_unused_1094_ = lean_ctor_get(v_snd_1072_, 1);
lean_dec(v_unused_1094_);
v___x_1087_ = v_snd_1072_;
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_fst_1085_);
lean_dec(v_snd_1072_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1089_ = lean_box(0);
if (v_isShared_1088_ == 0)
{
lean_ctor_set_tag(v___x_1087_, 1);
lean_ctor_set(v___x_1087_, 1, v___x_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_fst_1085_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhileUpTo___boxed(lean_object* v_pred_1095_, lean_object* v_limit_1096_, lean_object* v_it_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(v_pred_1095_, v_limit_1096_, v_it_1097_);
lean_dec(v_limit_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(lean_object* v_pred_1099_, lean_object* v_limit_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v___f_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v_snd_1105_; lean_object* v_snd_1106_; uint8_t v___x_1107_; 
v___f_1102_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1102_, 0, v_pred_1099_);
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1102_, v_limit_1100_, v___x_1103_, v_a_1101_);
v_snd_1105_ = lean_ctor_get(v___x_1104_, 1);
lean_inc(v_snd_1105_);
lean_dec_ref(v___x_1104_);
v_snd_1106_ = lean_ctor_get(v_snd_1105_, 1);
v___x_1107_ = lean_unbox(v_snd_1106_);
if (v___x_1107_ == 0)
{
lean_object* v_fst_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1116_; 
v_fst_1108_ = lean_ctor_get(v_snd_1105_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_snd_1105_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; 
v_unused_1117_ = lean_ctor_get(v_snd_1105_, 1);
lean_dec(v_unused_1117_);
v___x_1110_ = v_snd_1105_;
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_fst_1108_);
lean_dec(v_snd_1105_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1112_ = lean_box(0);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 1, v___x_1112_);
v___x_1114_ = v___x_1110_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_fst_1108_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
else
{
lean_object* v_fst_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1126_; 
v_fst_1118_ = lean_ctor_get(v_snd_1105_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_snd_1105_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v_snd_1105_, 1);
lean_dec(v_unused_1127_);
v___x_1120_ = v_snd_1105_;
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_fst_1118_);
lean_dec(v_snd_1105_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1122_ = lean_box(0);
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 1);
lean_ctor_set(v___x_1120_, 1, v___x_1122_);
v___x_1124_ = v___x_1120_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_fst_1118_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntilUpTo___boxed(lean_object* v_pred_1128_, lean_object* v_limit_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(v_pred_1128_, v_limit_1129_, v_a_1130_);
lean_dec(v_limit_1129_);
return v_res_1131_;
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
