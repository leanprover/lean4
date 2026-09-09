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
uint8_t lean_uint8_sub(uint8_t, uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
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
lean_object* v_array_347_; lean_object* v_idx_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v_array_347_ = lean_ctor_get(v_a_346_, 0);
v_idx_348_ = lean_ctor_get(v_a_346_, 1);
v___x_349_ = lean_byte_array_size(v_array_347_);
v___x_350_ = lean_nat_dec_lt(v_idx_348_, v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_box(0);
v___x_352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_352_, 0, v_a_346_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
return v___x_352_;
}
else
{
uint8_t v_c_353_; uint8_t v___y_355_; uint8_t v___x_372_; uint8_t v___x_373_; 
v_c_353_ = lean_byte_array_fget(v_array_347_, v_idx_348_);
v___x_372_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_373_ = lean_uint8_dec_le(v___x_372_, v_c_353_);
if (v___x_373_ == 0)
{
v___y_355_ = v___x_373_;
goto v___jp_354_;
}
else
{
uint8_t v___x_374_; uint8_t v___x_375_; 
v___x_374_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__3, &l_Std_Internal_Parsec_ByteArray_digit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3);
v___x_375_ = lean_uint8_dec_le(v_c_353_, v___x_374_);
v___y_355_ = v___x_375_;
goto v___jp_354_;
}
v___jp_354_:
{
if (v___y_355_ == 0)
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_digit___closed__1));
v___x_357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_357_, 0, v_a_346_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
return v___x_357_;
}
else
{
lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_369_; 
lean_inc(v_idx_348_);
lean_inc_ref(v_array_347_);
v_isSharedCheck_369_ = !lean_is_exclusive(v_a_346_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; lean_object* v_unused_371_; 
v_unused_370_ = lean_ctor_get(v_a_346_, 1);
lean_dec(v_unused_370_);
v_unused_371_ = lean_ctor_get(v_a_346_, 0);
lean_dec(v_unused_371_);
v___x_359_ = v_a_346_;
v_isShared_360_ = v_isSharedCheck_369_;
goto v_resetjp_358_;
}
else
{
lean_dec(v_a_346_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_369_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_it_x27_364_; 
v___x_361_ = lean_unsigned_to_nat(1u);
v___x_362_ = lean_nat_add(v_idx_348_, v___x_361_);
lean_dec(v_idx_348_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v___x_362_);
v_it_x27_364_ = v___x_359_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_array_347_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v___x_362_);
v_it_x27_364_ = v_reuseFailAlloc_368_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
uint32_t v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = lean_uint8_to_uint32(v_c_353_);
v___x_366_ = lean_box_uint32(v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v_it_x27_364_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
return v___x_367_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(uint8_t v_b_376_){
_start:
{
uint8_t v___x_377_; uint8_t v___x_378_; lean_object* v___x_379_; 
v___x_377_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_378_ = lean_uint8_sub(v_b_376_, v___x_377_);
v___x_379_ = lean_uint8_to_nat(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat___boxed(lean_object* v_b_380_){
_start:
{
uint8_t v_b_boxed_381_; lean_object* v_res_382_; 
v_b_boxed_381_ = lean_unbox(v_b_380_);
v_res_382_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(v_b_boxed_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object* v_it_383_, lean_object* v_acc_384_){
_start:
{
lean_object* v_array_385_; lean_object* v_idx_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v_array_385_ = lean_ctor_get(v_it_383_, 0);
v_idx_386_ = lean_ctor_get(v_it_383_, 1);
v___x_387_ = lean_byte_array_size(v_array_385_);
v___x_388_ = lean_nat_dec_lt(v_idx_386_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v_acc_384_);
lean_ctor_set(v___x_389_, 1, v_it_383_);
return v___x_389_;
}
else
{
uint8_t v_candidate_390_; uint8_t v___x_391_; uint8_t v___y_393_; uint8_t v___x_412_; 
v_candidate_390_ = lean_byte_array_fget(v_array_385_, v_idx_386_);
v___x_391_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_412_ = lean_uint8_dec_le(v___x_391_, v_candidate_390_);
if (v___x_412_ == 0)
{
v___y_393_ = v___x_412_;
goto v___jp_392_;
}
else
{
uint8_t v___x_413_; uint8_t v___x_414_; 
v___x_413_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__3, &l_Std_Internal_Parsec_ByteArray_digit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3);
v___x_414_ = lean_uint8_dec_le(v_candidate_390_, v___x_413_);
v___y_393_ = v___x_414_;
goto v___jp_392_;
}
v___jp_392_:
{
if (v___y_393_ == 0)
{
lean_object* v___x_394_; 
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v_acc_384_);
lean_ctor_set(v___x_394_, 1, v_it_383_);
return v___x_394_;
}
else
{
lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_409_; 
lean_inc(v_idx_386_);
lean_inc_ref(v_array_385_);
v_isSharedCheck_409_ = !lean_is_exclusive(v_it_383_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; lean_object* v_unused_411_; 
v_unused_410_ = lean_ctor_get(v_it_383_, 1);
lean_dec(v_unused_410_);
v_unused_411_ = lean_ctor_get(v_it_383_, 0);
lean_dec(v_unused_411_);
v___x_396_ = v_it_383_;
v_isShared_397_ = v_isSharedCheck_409_;
goto v_resetjp_395_;
}
else
{
lean_dec(v_it_383_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_409_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
uint8_t v___x_398_; lean_object* v_digit_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_acc_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_398_ = lean_uint8_sub(v_candidate_390_, v___x_391_);
v_digit_399_ = lean_uint8_to_nat(v___x_398_);
v___x_400_ = lean_unsigned_to_nat(10u);
v___x_401_ = lean_nat_mul(v_acc_384_, v___x_400_);
lean_dec(v_acc_384_);
v_acc_402_ = lean_nat_add(v___x_401_, v_digit_399_);
lean_dec(v___x_401_);
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_nat_add(v_idx_386_, v___x_403_);
lean_dec(v_idx_386_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v___x_404_);
v___x_406_ = v___x_396_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_array_385_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_404_);
v___x_406_ = v_reuseFailAlloc_408_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
v_it_383_ = v___x_406_;
v_acc_384_ = v_acc_402_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore(lean_object* v_acc_415_, lean_object* v_it_416_){
_start:
{
lean_object* v___x_417_; lean_object* v_fst_418_; lean_object* v_snd_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
v___x_417_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_416_, v_acc_415_);
v_fst_418_ = lean_ctor_get(v___x_417_, 0);
v_snd_419_ = lean_ctor_get(v___x_417_, 1);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_417_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_snd_419_);
lean_inc(v_fst_418_);
lean_dec(v___x_417_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 1, v_fst_418_);
lean_ctor_set(v___x_421_, 0, v_snd_419_);
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_snd_419_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_fst_418_);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digits(lean_object* v_a_427_){
_start:
{
lean_object* v_array_428_; lean_object* v_idx_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v_array_428_ = lean_ctor_get(v_a_427_, 0);
v_idx_429_ = lean_ctor_get(v_a_427_, 1);
v___x_430_ = lean_byte_array_size(v_array_428_);
v___x_431_ = lean_nat_dec_lt(v_idx_429_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_box(0);
v___x_433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_433_, 0, v_a_427_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
return v___x_433_;
}
else
{
uint8_t v_c_434_; uint8_t v___x_435_; uint8_t v___y_437_; uint8_t v___x_465_; 
v_c_434_ = lean_byte_array_fget(v_array_428_, v_idx_429_);
v___x_435_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_465_ = lean_uint8_dec_le(v___x_435_, v_c_434_);
if (v___x_465_ == 0)
{
v___y_437_ = v___x_465_;
goto v___jp_436_;
}
else
{
uint8_t v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__3, &l_Std_Internal_Parsec_ByteArray_digit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3);
v___x_467_ = lean_uint8_dec_le(v_c_434_, v___x_466_);
v___y_437_ = v___x_467_;
goto v___jp_436_;
}
v___jp_436_:
{
if (v___y_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_digit___closed__1));
v___x_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_439_, 0, v_a_427_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
return v___x_439_;
}
else
{
lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_462_; 
lean_inc(v_idx_429_);
lean_inc_ref(v_array_428_);
v_isSharedCheck_462_ = !lean_is_exclusive(v_a_427_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; lean_object* v_unused_464_; 
v_unused_463_ = lean_ctor_get(v_a_427_, 1);
lean_dec(v_unused_463_);
v_unused_464_ = lean_ctor_get(v_a_427_, 0);
lean_dec(v_unused_464_);
v___x_441_ = v_a_427_;
v_isShared_442_ = v_isSharedCheck_462_;
goto v_resetjp_440_;
}
else
{
lean_dec(v_a_427_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_462_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_it_x27_446_; 
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_add(v_idx_429_, v___x_443_);
lean_dec(v_idx_429_);
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
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_array_428_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_444_);
v_it_x27_446_ = v_reuseFailAlloc_461_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
uint32_t v___x_447_; uint8_t v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v_fst_452_; lean_object* v_snd_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
v___x_447_ = lean_uint8_to_uint32(v_c_434_);
v___x_448_ = lean_uint32_to_uint8(v___x_447_);
v___x_449_ = lean_uint8_sub(v___x_448_, v___x_435_);
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
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2(void){
_start:
{
uint32_t v___x_471_; uint8_t v___x_472_; 
v___x_471_ = 65;
v___x_472_ = lean_uint32_to_uint8(v___x_471_);
return v___x_472_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3(void){
_start:
{
uint32_t v___x_473_; uint8_t v___x_474_; 
v___x_473_ = 70;
v___x_474_ = lean_uint32_to_uint8(v___x_473_);
return v___x_474_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4(void){
_start:
{
uint32_t v___x_475_; uint8_t v___x_476_; 
v___x_475_ = 97;
v___x_476_ = lean_uint32_to_uint8(v___x_475_);
return v___x_476_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5(void){
_start:
{
uint32_t v___x_477_; uint8_t v___x_478_; 
v___x_477_ = 102;
v___x_478_ = lean_uint32_to_uint8(v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_hexDigit(lean_object* v_a_479_){
_start:
{
lean_object* v_array_480_; lean_object* v_idx_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_array_480_ = lean_ctor_get(v_a_479_, 0);
v_idx_481_ = lean_ctor_get(v_a_479_, 1);
v___x_482_ = lean_byte_array_size(v_array_480_);
v___x_483_ = lean_nat_dec_lt(v_idx_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_box(0);
v___x_485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_485_, 0, v_a_479_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
return v___x_485_;
}
else
{
uint8_t v_c_486_; uint8_t v___y_495_; uint8_t v___y_496_; uint8_t v___y_500_; uint8_t v___y_501_; uint8_t v___y_502_; uint8_t v___y_504_; uint8_t v___y_505_; uint8_t v___y_511_; uint8_t v___x_516_; uint8_t v___x_517_; 
v_c_486_ = lean_byte_array_fget(v_array_480_, v_idx_481_);
v___x_516_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_517_ = lean_uint8_dec_le(v___x_516_, v_c_486_);
if (v___x_517_ == 0)
{
v___y_511_ = v___x_517_;
goto v___jp_510_;
}
else
{
uint8_t v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__3, &l_Std_Internal_Parsec_ByteArray_digit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3);
v___x_519_ = lean_uint8_dec_le(v_c_486_, v___x_518_);
v___y_511_ = v___x_519_;
goto v___jp_510_;
}
v___jp_487_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v_it_x27_490_; uint32_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_nat_add(v_idx_481_, v___x_488_);
lean_dec(v_idx_481_);
v_it_x27_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_490_, 0, v_array_480_);
lean_ctor_set(v_it_x27_490_, 1, v___x_489_);
v___x_491_ = lean_uint8_to_uint32(v_c_486_);
v___x_492_ = lean_box_uint32(v___x_491_);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v_it_x27_490_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
return v___x_493_;
}
v___jp_494_:
{
if (v___y_495_ == 0)
{
if (v___y_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1));
v___x_498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_498_, 0, v_a_479_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
return v___x_498_;
}
else
{
lean_inc(v_idx_481_);
lean_inc_ref(v_array_480_);
lean_dec_ref(v_a_479_);
goto v___jp_487_;
}
}
else
{
lean_inc(v_idx_481_);
lean_inc_ref(v_array_480_);
lean_dec_ref(v_a_479_);
goto v___jp_487_;
}
}
v___jp_499_:
{
if (v___y_500_ == 0)
{
v___y_495_ = v___y_501_;
v___y_496_ = v___y_502_;
goto v___jp_494_;
}
else
{
v___y_495_ = v___y_501_;
v___y_496_ = v___y_500_;
goto v___jp_494_;
}
}
v___jp_503_:
{
uint8_t v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2);
v___x_507_ = lean_uint8_dec_le(v___x_506_, v_c_486_);
if (v___x_507_ == 0)
{
v___y_500_ = v___y_505_;
v___y_501_ = v___y_504_;
v___y_502_ = v___x_507_;
goto v___jp_499_;
}
else
{
uint8_t v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3);
v___x_509_ = lean_uint8_dec_le(v_c_486_, v___x_508_);
v___y_500_ = v___y_505_;
v___y_501_ = v___y_504_;
v___y_502_ = v___x_509_;
goto v___jp_499_;
}
}
v___jp_510_:
{
uint8_t v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4);
v___x_513_ = lean_uint8_dec_le(v___x_512_, v_c_486_);
if (v___x_513_ == 0)
{
v___y_504_ = v___y_511_;
v___y_505_ = v___x_513_;
goto v___jp_503_;
}
else
{
uint8_t v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5);
v___x_515_ = lean_uint8_dec_le(v_c_486_, v___x_514_);
v___y_504_ = v___y_511_;
v___y_505_ = v___x_515_;
goto v___jp_503_;
}
}
}
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_octDigit___closed__2(void){
_start:
{
uint32_t v___x_523_; uint8_t v___x_524_; 
v___x_523_ = 55;
v___x_524_ = lean_uint32_to_uint8(v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_octDigit(lean_object* v_a_525_){
_start:
{
lean_object* v_array_526_; lean_object* v_idx_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v_array_526_ = lean_ctor_get(v_a_525_, 0);
v_idx_527_ = lean_ctor_get(v_a_525_, 1);
v___x_528_ = lean_byte_array_size(v_array_526_);
v___x_529_ = lean_nat_dec_lt(v_idx_527_, v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_box(0);
v___x_531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_531_, 0, v_a_525_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
return v___x_531_;
}
else
{
uint8_t v_c_532_; uint8_t v___y_534_; uint8_t v___x_551_; uint8_t v___x_552_; 
v_c_532_ = lean_byte_array_fget(v_array_526_, v_idx_527_);
v___x_551_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_552_ = lean_uint8_dec_le(v___x_551_, v_c_532_);
if (v___x_552_ == 0)
{
v___y_534_ = v___x_552_;
goto v___jp_533_;
}
else
{
uint8_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_octDigit___closed__2, &l_Std_Internal_Parsec_ByteArray_octDigit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_octDigit___closed__2);
v___x_554_ = lean_uint8_dec_le(v_c_532_, v___x_553_);
v___y_534_ = v___x_554_;
goto v___jp_533_;
}
v___jp_533_:
{
if (v___y_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_octDigit___closed__1));
v___x_536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_536_, 0, v_a_525_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
return v___x_536_;
}
else
{
lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_548_; 
lean_inc(v_idx_527_);
lean_inc_ref(v_array_526_);
v_isSharedCheck_548_ = !lean_is_exclusive(v_a_525_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; lean_object* v_unused_550_; 
v_unused_549_ = lean_ctor_get(v_a_525_, 1);
lean_dec(v_unused_549_);
v_unused_550_ = lean_ctor_get(v_a_525_, 0);
lean_dec(v_unused_550_);
v___x_538_ = v_a_525_;
v_isShared_539_ = v_isSharedCheck_548_;
goto v_resetjp_537_;
}
else
{
lean_dec(v_a_525_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_548_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v_it_x27_543_; 
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_nat_add(v_idx_527_, v___x_540_);
lean_dec(v_idx_527_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v___x_541_);
v_it_x27_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_array_526_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_541_);
v_it_x27_543_ = v_reuseFailAlloc_547_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
uint32_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_uint8_to_uint32(v_c_532_);
v___x_545_ = lean_box_uint32(v___x_544_);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v_it_x27_543_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
return v___x_546_;
}
}
}
}
}
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2(void){
_start:
{
uint32_t v___x_558_; uint8_t v___x_559_; 
v___x_558_ = 122;
v___x_559_ = lean_uint32_to_uint8(v___x_558_);
return v___x_559_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3(void){
_start:
{
uint32_t v___x_560_; uint8_t v___x_561_; 
v___x_560_ = 90;
v___x_561_ = lean_uint32_to_uint8(v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_asciiLetter(lean_object* v_a_562_){
_start:
{
lean_object* v_array_563_; lean_object* v_idx_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_array_563_ = lean_ctor_get(v_a_562_, 0);
v_idx_564_ = lean_ctor_get(v_a_562_, 1);
v___x_565_ = lean_byte_array_size(v_array_563_);
v___x_566_ = lean_nat_dec_lt(v_idx_564_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_box(0);
v___x_568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_568_, 0, v_a_562_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
return v___x_568_;
}
else
{
uint8_t v_c_569_; uint8_t v___y_578_; uint8_t v___y_579_; uint8_t v___y_583_; uint8_t v___x_588_; uint8_t v___x_589_; 
v_c_569_ = lean_byte_array_fget(v_array_563_, v_idx_564_);
v___x_588_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2);
v___x_589_ = lean_uint8_dec_le(v___x_588_, v_c_569_);
if (v___x_589_ == 0)
{
v___y_583_ = v___x_589_;
goto v___jp_582_;
}
else
{
uint8_t v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3, &l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3);
v___x_591_ = lean_uint8_dec_le(v_c_569_, v___x_590_);
v___y_583_ = v___x_591_;
goto v___jp_582_;
}
v___jp_570_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v_it_x27_573_; uint32_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = lean_nat_add(v_idx_564_, v___x_571_);
lean_dec(v_idx_564_);
v_it_x27_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_573_, 0, v_array_563_);
lean_ctor_set(v_it_x27_573_, 1, v___x_572_);
v___x_574_ = lean_uint8_to_uint32(v_c_569_);
v___x_575_ = lean_box_uint32(v___x_574_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v_it_x27_573_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
return v___x_576_;
}
v___jp_577_:
{
if (v___y_578_ == 0)
{
if (v___y_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1));
v___x_581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_581_, 0, v_a_562_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
return v___x_581_;
}
else
{
lean_inc(v_idx_564_);
lean_inc_ref(v_array_563_);
lean_dec_ref(v_a_562_);
goto v___jp_570_;
}
}
else
{
lean_inc(v_idx_564_);
lean_inc_ref(v_array_563_);
lean_dec_ref(v_a_562_);
goto v___jp_570_;
}
}
v___jp_582_:
{
uint8_t v___x_584_; uint8_t v___x_585_; 
v___x_584_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4);
v___x_585_ = lean_uint8_dec_le(v___x_584_, v_c_569_);
if (v___x_585_ == 0)
{
v___y_578_ = v___y_583_;
v___y_579_ = v___x_585_;
goto v___jp_577_;
}
else
{
uint8_t v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2, &l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2);
v___x_587_ = lean_uint8_dec_le(v_c_569_, v___x_586_);
v___y_578_ = v___y_583_;
v___y_579_ = v___x_587_;
goto v___jp_577_;
}
}
}
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0(void){
_start:
{
uint32_t v___x_592_; uint8_t v___x_593_; 
v___x_592_ = 9;
v___x_593_ = lean_uint32_to_uint8(v___x_592_);
return v___x_593_;
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1(void){
_start:
{
uint32_t v___x_594_; uint8_t v___x_595_; 
v___x_594_ = 10;
v___x_595_ = lean_uint32_to_uint8(v___x_594_);
return v___x_595_;
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2(void){
_start:
{
uint32_t v___x_596_; uint8_t v___x_597_; 
v___x_596_ = 13;
v___x_597_ = lean_uint32_to_uint8(v___x_596_);
return v___x_597_;
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3(void){
_start:
{
uint32_t v___x_598_; uint8_t v___x_599_; 
v___x_598_ = 32;
v___x_599_ = lean_uint32_to_uint8(v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(lean_object* v_it_600_){
_start:
{
lean_object* v_array_601_; lean_object* v_idx_602_; uint8_t v___y_604_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_array_601_ = lean_ctor_get(v_it_600_, 0);
v_idx_602_ = lean_ctor_get(v_it_600_, 1);
v___x_617_ = lean_byte_array_size(v_array_601_);
v___x_618_ = lean_nat_dec_lt(v_idx_602_, v___x_617_);
if (v___x_618_ == 0)
{
return v_it_600_;
}
else
{
uint8_t v_b_619_; uint8_t v___x_620_; uint8_t v___x_621_; uint8_t v___y_623_; uint8_t v___x_624_; uint8_t v___x_625_; uint8_t v___y_627_; uint8_t v___x_628_; uint8_t v___x_629_; 
v_b_619_ = lean_byte_array_fget(v_array_601_, v_idx_602_);
v___x_620_ = lean_uint8_once(&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0, &l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0_once, _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0);
v___x_621_ = lean_uint8_dec_eq(v_b_619_, v___x_620_);
v___x_624_ = lean_uint8_once(&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1, &l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1_once, _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1);
v___x_625_ = lean_uint8_dec_eq(v_b_619_, v___x_624_);
v___x_628_ = lean_uint8_once(&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2, &l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2_once, _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2);
v___x_629_ = lean_uint8_dec_eq(v_b_619_, v___x_628_);
if (v___x_629_ == 0)
{
uint8_t v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_uint8_once(&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3, &l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3_once, _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3);
v___x_631_ = lean_uint8_dec_eq(v_b_619_, v___x_630_);
v___y_627_ = v___x_631_;
goto v___jp_626_;
}
else
{
v___y_627_ = v___x_629_;
goto v___jp_626_;
}
v___jp_622_:
{
if (v___x_621_ == 0)
{
v___y_604_ = v___y_623_;
goto v___jp_603_;
}
else
{
v___y_604_ = v___x_621_;
goto v___jp_603_;
}
}
v___jp_626_:
{
if (v___x_625_ == 0)
{
v___y_623_ = v___y_627_;
goto v___jp_622_;
}
else
{
v___y_623_ = v___x_625_;
goto v___jp_622_;
}
}
}
v___jp_603_:
{
if (v___y_604_ == 0)
{
return v_it_600_;
}
else
{
lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_614_; 
lean_inc(v_idx_602_);
lean_inc_ref(v_array_601_);
v_isSharedCheck_614_ = !lean_is_exclusive(v_it_600_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; lean_object* v_unused_616_; 
v_unused_615_ = lean_ctor_get(v_it_600_, 1);
lean_dec(v_unused_615_);
v_unused_616_ = lean_ctor_get(v_it_600_, 0);
lean_dec(v_unused_616_);
v___x_606_ = v_it_600_;
v_isShared_607_ = v_isSharedCheck_614_;
goto v_resetjp_605_;
}
else
{
lean_dec(v_it_600_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_614_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_nat_add(v_idx_602_, v___x_608_);
lean_dec(v_idx_602_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v___x_609_);
v___x_611_ = v___x_606_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_array_601_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___x_609_);
v___x_611_ = v_reuseFailAlloc_613_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
v_it_600_ = v___x_611_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_ws(lean_object* v_it_632_){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(v_it_632_);
v___x_634_ = lean_box(0);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take(lean_object* v_n_636_, lean_object* v_it_637_){
_start:
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = l_ByteArray_Iterator_remainingBytes(v_it_637_);
v___x_639_ = lean_nat_dec_lt(v___x_638_, v_n_636_);
lean_dec(v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v_array_640_; lean_object* v_idx_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_660_; 
v_array_640_ = lean_ctor_get(v_it_637_, 0);
v_idx_641_ = lean_ctor_get(v_it_637_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v_it_637_);
if (v_isSharedCheck_660_ == 0)
{
v___x_643_ = v_it_637_;
v_isShared_644_ = v_isSharedCheck_660_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_idx_641_);
lean_inc(v_array_640_);
lean_dec(v_it_637_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_660_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = lean_nat_add(v_idx_641_, v_n_636_);
lean_inc(v___x_645_);
lean_inc_ref(v_array_640_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v___x_645_);
v___x_647_ = v___x_643_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_array_640_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v___x_645_);
v___x_647_ = v_reuseFailAlloc_659_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v_lower_649_; lean_object* v_upper_650_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___y_656_; uint8_t v___x_658_; 
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_byte_array_size(v_array_640_);
v___x_658_ = lean_nat_dec_le(v_idx_641_, v___x_653_);
if (v___x_658_ == 0)
{
v___y_656_ = v_idx_641_;
goto v___jp_655_;
}
else
{
lean_dec(v_idx_641_);
v___y_656_ = v___x_653_;
goto v___jp_655_;
}
v___jp_648_:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = l_ByteArray_toByteSlice(v_array_640_, v_lower_649_, v_upper_650_);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_647_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
return v___x_652_;
}
v___jp_655_:
{
uint8_t v___x_657_; 
v___x_657_ = lean_nat_dec_le(v___x_645_, v___x_654_);
if (v___x_657_ == 0)
{
lean_dec(v___x_645_);
v_lower_649_ = v___y_656_;
v_upper_650_ = v___x_654_;
goto v___jp_648_;
}
else
{
v_lower_649_ = v___y_656_;
v_upper_650_ = v___x_645_;
goto v___jp_648_;
}
}
}
}
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_box(0);
v___x_662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_662_, 0, v_it_637_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
return v___x_662_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take___boxed(lean_object* v_n_663_, lean_object* v_it_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Std_Internal_Parsec_ByteArray_take(v_n_663_, v_it_664_);
lean_dec(v_n_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(lean_object* v_pred_666_, lean_object* v_count_667_, lean_object* v_iter_668_){
_start:
{
lean_object* v_array_669_; lean_object* v_idx_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_array_669_ = lean_ctor_get(v_iter_668_, 0);
v_idx_670_ = lean_ctor_get(v_iter_668_, 1);
v___x_671_ = lean_byte_array_size(v_array_669_);
v___x_672_ = lean_nat_dec_lt(v_idx_670_, v___x_671_);
if (v___x_672_ == 0)
{
uint8_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec_ref(v_pred_666_);
v___x_673_ = 1;
v___x_674_ = lean_box(v___x_673_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_iter_668_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_count_667_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
return v___x_676_;
}
else
{
uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_677_ = lean_byte_array_fget(v_array_669_, v_idx_670_);
v___x_678_ = lean_box(v___x_677_);
lean_inc_ref(v_pred_666_);
v___x_679_ = lean_apply_1(v_pred_666_, v___x_678_);
v___x_680_ = lean_unbox(v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec_ref(v_pred_666_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v_iter_668_);
lean_ctor_set(v___x_681_, 1, v___x_679_);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v_count_667_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
return v___x_682_;
}
else
{
lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_693_; 
lean_inc(v_idx_670_);
lean_inc_ref(v_array_669_);
v_isSharedCheck_693_ = !lean_is_exclusive(v_iter_668_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; lean_object* v_unused_695_; 
v_unused_694_ = lean_ctor_get(v_iter_668_, 1);
lean_dec(v_unused_694_);
v_unused_695_ = lean_ctor_get(v_iter_668_, 0);
lean_dec(v_unused_695_);
v___x_684_ = v_iter_668_;
v_isShared_685_ = v_isSharedCheck_693_;
goto v_resetjp_683_;
}
else
{
lean_dec(v_iter_668_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_693_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = lean_nat_add(v_count_667_, v___x_686_);
lean_dec(v_count_667_);
v___x_688_ = lean_nat_add(v_idx_670_, v___x_686_);
lean_dec(v_idx_670_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_688_);
v___x_690_ = v___x_684_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_array_669_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_688_);
v___x_690_ = v_reuseFailAlloc_692_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
v_count_667_ = v___x_687_;
v_iter_668_ = v___x_690_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object* v_pred_696_, lean_object* v_limit_697_, lean_object* v_count_698_, lean_object* v_iter_699_){
_start:
{
uint8_t v___x_700_; 
v___x_700_ = lean_nat_dec_le(v_limit_697_, v_count_698_);
if (v___x_700_ == 0)
{
lean_object* v_array_701_; lean_object* v_idx_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v_array_701_ = lean_ctor_get(v_iter_699_, 0);
v_idx_702_ = lean_ctor_get(v_iter_699_, 1);
v___x_703_ = lean_byte_array_size(v_array_701_);
v___x_704_ = lean_nat_dec_lt(v_idx_702_, v___x_703_);
if (v___x_704_ == 0)
{
uint8_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec_ref(v_pred_696_);
v___x_705_ = 1;
v___x_706_ = lean_box(v___x_705_);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v_iter_699_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v_count_698_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
return v___x_708_;
}
else
{
uint8_t v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_709_ = lean_byte_array_fget(v_array_701_, v_idx_702_);
v___x_710_ = lean_box(v___x_709_);
lean_inc_ref(v_pred_696_);
v___x_711_ = lean_apply_1(v_pred_696_, v___x_710_);
v___x_712_ = lean_unbox(v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec_ref(v_pred_696_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_iter_699_);
lean_ctor_set(v___x_713_, 1, v___x_711_);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v_count_698_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
return v___x_714_;
}
else
{
lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_725_; 
lean_inc(v_idx_702_);
lean_inc_ref(v_array_701_);
v_isSharedCheck_725_ = !lean_is_exclusive(v_iter_699_);
if (v_isSharedCheck_725_ == 0)
{
lean_object* v_unused_726_; lean_object* v_unused_727_; 
v_unused_726_ = lean_ctor_get(v_iter_699_, 1);
lean_dec(v_unused_726_);
v_unused_727_ = lean_ctor_get(v_iter_699_, 0);
lean_dec(v_unused_727_);
v___x_716_ = v_iter_699_;
v_isShared_717_ = v_isSharedCheck_725_;
goto v_resetjp_715_;
}
else
{
lean_dec(v_iter_699_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_725_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_nat_add(v_count_698_, v___x_718_);
lean_dec(v_count_698_);
v___x_720_ = lean_nat_add(v_idx_702_, v___x_718_);
lean_dec(v_idx_702_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v___x_720_);
v___x_722_ = v___x_716_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_array_701_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_720_);
v___x_722_ = v_reuseFailAlloc_724_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
v_count_698_ = v___x_719_;
v_iter_699_ = v___x_722_;
goto _start;
}
}
}
}
}
else
{
uint8_t v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec_ref(v_pred_696_);
v___x_728_ = 0;
v___x_729_ = lean_box(v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v_iter_699_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v_count_698_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
return v___x_731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo___boxed(lean_object* v_pred_732_, lean_object* v_limit_733_, lean_object* v_count_734_, lean_object* v_iter_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_732_, v_limit_733_, v_count_734_, v_iter_735_);
lean_dec(v_limit_733_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile(lean_object* v_pred_737_, lean_object* v_it_738_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v_snd_741_; lean_object* v_snd_742_; uint8_t v___x_743_; 
v___x_739_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_738_);
v___x_740_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v_pred_737_, v___x_739_, v_it_738_);
v_snd_741_ = lean_ctor_get(v___x_740_, 1);
lean_inc(v_snd_741_);
v_snd_742_ = lean_ctor_get(v_snd_741_, 1);
v___x_743_ = lean_unbox(v_snd_742_);
if (v___x_743_ == 0)
{
lean_object* v_fst_744_; lean_object* v_fst_745_; lean_object* v_array_746_; lean_object* v_idx_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_764_; 
v_fst_744_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_fst_744_);
lean_dec_ref(v___x_740_);
v_fst_745_ = lean_ctor_get(v_snd_741_, 0);
lean_inc(v_fst_745_);
lean_dec(v_snd_741_);
v_array_746_ = lean_ctor_get(v_it_738_, 0);
v_idx_747_ = lean_ctor_get(v_it_738_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_it_738_);
if (v_isSharedCheck_764_ == 0)
{
v___x_749_ = v_it_738_;
v_isShared_750_ = v_isSharedCheck_764_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_idx_747_);
lean_inc(v_array_746_);
lean_dec(v_it_738_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_764_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v_lower_752_; lean_object* v_upper_753_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___y_761_; uint8_t v___x_763_; 
v___x_758_ = lean_nat_add(v_idx_747_, v_fst_744_);
lean_dec(v_fst_744_);
v___x_759_ = lean_byte_array_size(v_array_746_);
v___x_763_ = lean_nat_dec_le(v_idx_747_, v___x_739_);
if (v___x_763_ == 0)
{
v___y_761_ = v_idx_747_;
goto v___jp_760_;
}
else
{
lean_dec(v_idx_747_);
v___y_761_ = v___x_739_;
goto v___jp_760_;
}
v___jp_751_:
{
lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_754_ = l_ByteArray_toByteSlice(v_array_746_, v_lower_752_, v_upper_753_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_754_);
lean_ctor_set(v___x_749_, 0, v_fst_745_);
v___x_756_ = v___x_749_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_fst_745_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
v___jp_760_:
{
uint8_t v___x_762_; 
v___x_762_ = lean_nat_dec_le(v___x_758_, v___x_759_);
if (v___x_762_ == 0)
{
lean_dec(v___x_758_);
v_lower_752_ = v___y_761_;
v_upper_753_ = v___x_759_;
goto v___jp_751_;
}
else
{
v_lower_752_ = v___y_761_;
v_upper_753_ = v___x_758_;
goto v___jp_751_;
}
}
}
}
else
{
lean_object* v_fst_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref(v___x_740_);
lean_dec_ref(v_it_738_);
v_fst_765_ = lean_ctor_get(v_snd_741_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v_snd_741_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_snd_741_, 1);
lean_dec(v_unused_774_);
v___x_767_ = v_snd_741_;
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_fst_765_);
lean_dec(v_snd_741_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = lean_box(0);
if (v_isShared_768_ == 0)
{
lean_ctor_set_tag(v___x_767_, 1);
lean_ctor_set(v___x_767_, 1, v___x_769_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_fst_765_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(lean_object* v_pred_775_, uint8_t v_b_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_777_ = lean_box(v_b_776_);
v___x_778_ = lean_apply_1(v_pred_775_, v___x_777_);
v___x_779_ = lean_unbox(v___x_778_);
if (v___x_779_ == 0)
{
uint8_t v___x_780_; 
v___x_780_ = 1;
return v___x_780_;
}
else
{
uint8_t v___x_781_; 
v___x_781_ = 0;
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed(lean_object* v_pred_782_, lean_object* v_b_783_){
_start:
{
uint8_t v_b_boxed_784_; uint8_t v_res_785_; lean_object* v_r_786_; 
v_b_boxed_784_ = lean_unbox(v_b_783_);
v_res_785_ = l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(v_pred_782_, v_b_boxed_784_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil(lean_object* v_pred_787_, lean_object* v_a_788_){
_start:
{
lean_object* v___f_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v_snd_792_; lean_object* v_snd_793_; uint8_t v___x_794_; 
v___f_789_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_789_, 0, v_pred_787_);
v___x_790_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_788_);
v___x_791_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v___f_789_, v___x_790_, v_a_788_);
v_snd_792_ = lean_ctor_get(v___x_791_, 1);
lean_inc(v_snd_792_);
v_snd_793_ = lean_ctor_get(v_snd_792_, 1);
v___x_794_ = lean_unbox(v_snd_793_);
if (v___x_794_ == 0)
{
lean_object* v_fst_795_; lean_object* v_fst_796_; lean_object* v_array_797_; lean_object* v_idx_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_815_; 
v_fst_795_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_fst_795_);
lean_dec_ref(v___x_791_);
v_fst_796_ = lean_ctor_get(v_snd_792_, 0);
lean_inc(v_fst_796_);
lean_dec(v_snd_792_);
v_array_797_ = lean_ctor_get(v_a_788_, 0);
v_idx_798_ = lean_ctor_get(v_a_788_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v_a_788_);
if (v_isSharedCheck_815_ == 0)
{
v___x_800_ = v_a_788_;
v_isShared_801_ = v_isSharedCheck_815_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_idx_798_);
lean_inc(v_array_797_);
lean_dec(v_a_788_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_815_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_lower_803_; lean_object* v_upper_804_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___y_812_; uint8_t v___x_814_; 
v___x_809_ = lean_nat_add(v_idx_798_, v_fst_795_);
lean_dec(v_fst_795_);
v___x_810_ = lean_byte_array_size(v_array_797_);
v___x_814_ = lean_nat_dec_le(v_idx_798_, v___x_790_);
if (v___x_814_ == 0)
{
v___y_812_ = v_idx_798_;
goto v___jp_811_;
}
else
{
lean_dec(v_idx_798_);
v___y_812_ = v___x_790_;
goto v___jp_811_;
}
v___jp_802_:
{
lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_805_ = l_ByteArray_toByteSlice(v_array_797_, v_lower_803_, v_upper_804_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v___x_805_);
lean_ctor_set(v___x_800_, 0, v_fst_796_);
v___x_807_ = v___x_800_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_fst_796_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
v___jp_811_:
{
uint8_t v___x_813_; 
v___x_813_ = lean_nat_dec_le(v___x_809_, v___x_810_);
if (v___x_813_ == 0)
{
lean_dec(v___x_809_);
v_lower_803_ = v___y_812_;
v_upper_804_ = v___x_810_;
goto v___jp_802_;
}
else
{
v_lower_803_ = v___y_812_;
v_upper_804_ = v___x_809_;
goto v___jp_802_;
}
}
}
}
else
{
lean_object* v_fst_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v___x_791_);
lean_dec_ref(v_a_788_);
v_fst_816_ = lean_ctor_get(v_snd_792_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_snd_792_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v_snd_792_, 1);
lean_dec(v_unused_825_);
v___x_818_ = v_snd_792_;
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_fst_816_);
lean_dec(v_snd_792_);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhile(lean_object* v_pred_826_, lean_object* v_it_827_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v_snd_830_; lean_object* v_snd_831_; uint8_t v___x_832_; 
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v_pred_826_, v___x_828_, v_it_827_);
v_snd_830_ = lean_ctor_get(v___x_829_, 1);
lean_inc(v_snd_830_);
lean_dec_ref(v___x_829_);
v_snd_831_ = lean_ctor_get(v_snd_830_, 1);
v___x_832_ = lean_unbox(v_snd_831_);
if (v___x_832_ == 0)
{
lean_object* v_fst_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_841_; 
v_fst_833_ = lean_ctor_get(v_snd_830_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v_snd_830_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v_snd_830_, 1);
lean_dec(v_unused_842_);
v___x_835_ = v_snd_830_;
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_fst_833_);
lean_dec(v_snd_830_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = lean_box(0);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v___x_837_);
v___x_839_ = v___x_835_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_fst_833_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
else
{
lean_object* v_fst_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_851_; 
v_fst_843_ = lean_ctor_get(v_snd_830_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v_snd_830_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; 
v_unused_852_ = lean_ctor_get(v_snd_830_, 1);
lean_dec(v_unused_852_);
v___x_845_ = v_snd_830_;
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_fst_843_);
lean_dec(v_snd_830_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_847_ = lean_box(0);
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 1);
lean_ctor_set(v___x_845_, 1, v___x_847_);
v___x_849_ = v___x_845_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_fst_843_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntil(lean_object* v_pred_853_, lean_object* v_a_854_){
_start:
{
lean_object* v___f_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v_snd_858_; lean_object* v_snd_859_; uint8_t v___x_860_; 
v___f_855_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_855_, 0, v_pred_853_);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v___f_855_, v___x_856_, v_a_854_);
v_snd_858_ = lean_ctor_get(v___x_857_, 1);
lean_inc(v_snd_858_);
lean_dec_ref(v___x_857_);
v_snd_859_ = lean_ctor_get(v_snd_858_, 1);
v___x_860_ = lean_unbox(v_snd_859_);
if (v___x_860_ == 0)
{
lean_object* v_fst_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_869_; 
v_fst_861_ = lean_ctor_get(v_snd_858_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v_snd_858_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; 
v_unused_870_ = lean_ctor_get(v_snd_858_, 1);
lean_dec(v_unused_870_);
v___x_863_ = v_snd_858_;
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_fst_861_);
lean_dec(v_snd_858_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = lean_box(0);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v___x_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_fst_861_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
else
{
lean_object* v_fst_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_879_; 
v_fst_871_ = lean_ctor_get(v_snd_858_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v_snd_858_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; 
v_unused_880_ = lean_ctor_get(v_snd_858_, 1);
lean_dec(v_unused_880_);
v___x_873_ = v_snd_858_;
v_isShared_874_ = v_isSharedCheck_879_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_fst_871_);
lean_dec(v_snd_858_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_879_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_875_ = lean_box(0);
if (v_isShared_874_ == 0)
{
lean_ctor_set_tag(v___x_873_, 1);
lean_ctor_set(v___x_873_, 1, v___x_875_);
v___x_877_ = v___x_873_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_fst_871_);
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
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(lean_object* v_pred_881_, lean_object* v_limit_882_, lean_object* v_it_883_){
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
lean_object* v_fst_889_; lean_object* v_fst_890_; lean_object* v_array_891_; lean_object* v_idx_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_909_; 
v_fst_889_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_fst_889_);
lean_dec_ref(v___x_885_);
v_fst_890_ = lean_ctor_get(v_snd_886_, 0);
lean_inc(v_fst_890_);
lean_dec(v_snd_886_);
v_array_891_ = lean_ctor_get(v_it_883_, 0);
v_idx_892_ = lean_ctor_get(v_it_883_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v_it_883_);
if (v_isSharedCheck_909_ == 0)
{
v___x_894_ = v_it_883_;
v_isShared_895_ = v_isSharedCheck_909_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_idx_892_);
lean_inc(v_array_891_);
lean_dec(v_it_883_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_909_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v_lower_897_; lean_object* v_upper_898_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___y_906_; uint8_t v___x_908_; 
v___x_903_ = lean_nat_add(v_idx_892_, v_fst_889_);
lean_dec(v_fst_889_);
v___x_904_ = lean_byte_array_size(v_array_891_);
v___x_908_ = lean_nat_dec_le(v_idx_892_, v___x_884_);
if (v___x_908_ == 0)
{
v___y_906_ = v_idx_892_;
goto v___jp_905_;
}
else
{
lean_dec(v_idx_892_);
v___y_906_ = v___x_884_;
goto v___jp_905_;
}
v___jp_896_:
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = l_ByteArray_toByteSlice(v_array_891_, v_lower_897_, v_upper_898_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 1, v___x_899_);
lean_ctor_set(v___x_894_, 0, v_fst_890_);
v___x_901_ = v___x_894_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_fst_890_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
v___jp_905_:
{
uint8_t v___x_907_; 
v___x_907_ = lean_nat_dec_le(v___x_903_, v___x_904_);
if (v___x_907_ == 0)
{
lean_dec(v___x_903_);
v_lower_897_ = v___y_906_;
v_upper_898_ = v___x_904_;
goto v___jp_896_;
}
else
{
v_lower_897_ = v___y_906_;
v_upper_898_ = v___x_903_;
goto v___jp_896_;
}
}
}
}
else
{
lean_object* v_fst_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v___x_885_);
lean_dec_ref(v_it_883_);
v_fst_910_ = lean_ctor_get(v_snd_886_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v_snd_886_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v_snd_886_, 1);
lean_dec(v_unused_919_);
v___x_912_ = v_snd_886_;
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_fst_910_);
lean_dec(v_snd_886_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = lean_box(0);
if (v_isShared_913_ == 0)
{
lean_ctor_set_tag(v___x_912_, 1);
lean_ctor_set(v___x_912_, 1, v___x_914_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_fst_910_);
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
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo___boxed(lean_object* v_pred_920_, lean_object* v_limit_921_, lean_object* v_it_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(v_pred_920_, v_limit_921_, v_it_922_);
lean_dec(v_limit_921_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(lean_object* v_pred_927_, lean_object* v_limit_928_, lean_object* v_it_929_){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_snd_932_; lean_object* v_snd_933_; uint8_t v___x_934_; 
v___x_930_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_929_);
v___x_931_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_927_, v_limit_928_, v___x_930_, v_it_929_);
v_snd_932_ = lean_ctor_get(v___x_931_, 1);
lean_inc(v_snd_932_);
v_snd_933_ = lean_ctor_get(v_snd_932_, 1);
v___x_934_ = lean_unbox(v_snd_933_);
if (v___x_934_ == 0)
{
lean_object* v_fst_935_; lean_object* v_fst_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_964_; 
v_fst_935_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_fst_935_);
lean_dec_ref(v___x_931_);
v_fst_936_ = lean_ctor_get(v_snd_932_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_snd_932_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v_snd_932_, 1);
lean_dec(v_unused_965_);
v___x_938_ = v_snd_932_;
v_isShared_939_ = v_isSharedCheck_964_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_fst_936_);
lean_dec(v_snd_932_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_964_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
uint8_t v___x_940_; 
v___x_940_ = lean_nat_dec_eq(v_fst_935_, v___x_930_);
if (v___x_940_ == 0)
{
lean_object* v_array_941_; lean_object* v_idx_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_959_; 
lean_del_object(v___x_938_);
v_array_941_ = lean_ctor_get(v_it_929_, 0);
v_idx_942_ = lean_ctor_get(v_it_929_, 1);
v_isSharedCheck_959_ = !lean_is_exclusive(v_it_929_);
if (v_isSharedCheck_959_ == 0)
{
v___x_944_ = v_it_929_;
v_isShared_945_ = v_isSharedCheck_959_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_idx_942_);
lean_inc(v_array_941_);
lean_dec(v_it_929_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_959_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_lower_947_; lean_object* v_upper_948_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___y_956_; uint8_t v___x_958_; 
v___x_953_ = lean_nat_add(v_idx_942_, v_fst_935_);
lean_dec(v_fst_935_);
v___x_954_ = lean_byte_array_size(v_array_941_);
v___x_958_ = lean_nat_dec_le(v_idx_942_, v___x_930_);
if (v___x_958_ == 0)
{
v___y_956_ = v_idx_942_;
goto v___jp_955_;
}
else
{
lean_dec(v_idx_942_);
v___y_956_ = v___x_930_;
goto v___jp_955_;
}
v___jp_946_:
{
lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_949_ = l_ByteArray_toByteSlice(v_array_941_, v_lower_947_, v_upper_948_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v___x_949_);
lean_ctor_set(v___x_944_, 0, v_fst_936_);
v___x_951_ = v___x_944_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_fst_936_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
v___jp_955_:
{
uint8_t v___x_957_; 
v___x_957_ = lean_nat_dec_le(v___x_953_, v___x_954_);
if (v___x_957_ == 0)
{
lean_dec(v___x_953_);
v_lower_947_ = v___y_956_;
v_upper_948_ = v___x_954_;
goto v___jp_946_;
}
else
{
v_lower_947_ = v___y_956_;
v_upper_948_ = v___x_953_;
goto v___jp_946_;
}
}
}
}
else
{
lean_object* v___x_960_; lean_object* v___x_962_; 
lean_dec(v_fst_936_);
lean_dec(v_fst_935_);
v___x_960_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1));
if (v_isShared_939_ == 0)
{
lean_ctor_set_tag(v___x_938_, 1);
lean_ctor_set(v___x_938_, 1, v___x_960_);
lean_ctor_set(v___x_938_, 0, v_it_929_);
v___x_962_ = v___x_938_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_it_929_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v___x_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
else
{
lean_object* v_fst_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_974_; 
lean_dec_ref(v___x_931_);
lean_dec_ref(v_it_929_);
v_fst_966_ = lean_ctor_get(v_snd_932_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v_snd_932_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; 
v_unused_975_ = lean_ctor_get(v_snd_932_, 1);
lean_dec(v_unused_975_);
v___x_968_ = v_snd_932_;
v_isShared_969_ = v_isSharedCheck_974_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_fst_966_);
lean_dec(v_snd_932_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_974_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_970_ = lean_box(0);
if (v_isShared_969_ == 0)
{
lean_ctor_set_tag(v___x_968_, 1);
lean_ctor_set(v___x_968_, 1, v___x_970_);
v___x_972_ = v___x_968_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_fst_966_);
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
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___boxed(lean_object* v_pred_976_, lean_object* v_limit_977_, lean_object* v_it_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(v_pred_976_, v_limit_977_, v_it_978_);
lean_dec(v_limit_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(lean_object* v_pred_980_, lean_object* v_limit_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___f_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v_snd_986_; lean_object* v_snd_987_; uint8_t v___x_988_; 
v___f_983_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_983_, 0, v_pred_980_);
v___x_984_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_982_);
v___x_985_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_983_, v_limit_981_, v___x_984_, v_a_982_);
v_snd_986_ = lean_ctor_get(v___x_985_, 1);
lean_inc(v_snd_986_);
v_snd_987_ = lean_ctor_get(v_snd_986_, 1);
v___x_988_ = lean_unbox(v_snd_987_);
if (v___x_988_ == 0)
{
lean_object* v_fst_989_; lean_object* v_fst_990_; lean_object* v_array_991_; lean_object* v_idx_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1009_; 
v_fst_989_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_fst_989_);
lean_dec_ref(v___x_985_);
v_fst_990_ = lean_ctor_get(v_snd_986_, 0);
lean_inc(v_fst_990_);
lean_dec(v_snd_986_);
v_array_991_ = lean_ctor_get(v_a_982_, 0);
v_idx_992_ = lean_ctor_get(v_a_982_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_a_982_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_994_ = v_a_982_;
v_isShared_995_ = v_isSharedCheck_1009_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_idx_992_);
lean_inc(v_array_991_);
lean_dec(v_a_982_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1009_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v_lower_997_; lean_object* v_upper_998_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___y_1006_; uint8_t v___x_1008_; 
v___x_1003_ = lean_nat_add(v_idx_992_, v_fst_989_);
lean_dec(v_fst_989_);
v___x_1004_ = lean_byte_array_size(v_array_991_);
v___x_1008_ = lean_nat_dec_le(v_idx_992_, v___x_984_);
if (v___x_1008_ == 0)
{
v___y_1006_ = v_idx_992_;
goto v___jp_1005_;
}
else
{
lean_dec(v_idx_992_);
v___y_1006_ = v___x_984_;
goto v___jp_1005_;
}
v___jp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_999_ = l_ByteArray_toByteSlice(v_array_991_, v_lower_997_, v_upper_998_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v___x_999_);
lean_ctor_set(v___x_994_, 0, v_fst_990_);
v___x_1001_ = v___x_994_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_fst_990_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
v___jp_1005_:
{
uint8_t v___x_1007_; 
v___x_1007_ = lean_nat_dec_le(v___x_1003_, v___x_1004_);
if (v___x_1007_ == 0)
{
lean_dec(v___x_1003_);
v_lower_997_ = v___y_1006_;
v_upper_998_ = v___x_1004_;
goto v___jp_996_;
}
else
{
v_lower_997_ = v___y_1006_;
v_upper_998_ = v___x_1003_;
goto v___jp_996_;
}
}
}
}
else
{
lean_object* v_fst_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1018_; 
lean_dec_ref(v___x_985_);
lean_dec_ref(v_a_982_);
v_fst_1010_ = lean_ctor_get(v_snd_986_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_snd_986_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v_snd_986_, 1);
lean_dec(v_unused_1019_);
v___x_1012_ = v_snd_986_;
v_isShared_1013_ = v_isSharedCheck_1018_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_fst_1010_);
lean_dec(v_snd_986_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1018_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1014_ = lean_box(0);
if (v_isShared_1013_ == 0)
{
lean_ctor_set_tag(v___x_1012_, 1);
lean_ctor_set(v___x_1012_, 1, v___x_1014_);
v___x_1016_ = v___x_1012_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_fst_1010_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo___boxed(lean_object* v_pred_1020_, lean_object* v_limit_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(v_pred_1020_, v_limit_1021_, v_a_1022_);
lean_dec(v_limit_1021_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileAtMost(lean_object* v_pred_1024_, lean_object* v_limit_1025_, lean_object* v_it_1026_){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v_snd_1029_; lean_object* v_fst_1030_; lean_object* v_fst_1031_; lean_object* v_array_1032_; lean_object* v_idx_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1050_; 
v___x_1027_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_1026_);
v___x_1028_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_1024_, v_limit_1025_, v___x_1027_, v_it_1026_);
v_snd_1029_ = lean_ctor_get(v___x_1028_, 1);
lean_inc(v_snd_1029_);
v_fst_1030_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_fst_1030_);
lean_dec_ref(v___x_1028_);
v_fst_1031_ = lean_ctor_get(v_snd_1029_, 0);
lean_inc(v_fst_1031_);
lean_dec(v_snd_1029_);
v_array_1032_ = lean_ctor_get(v_it_1026_, 0);
v_idx_1033_ = lean_ctor_get(v_it_1026_, 1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_it_1026_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1035_ = v_it_1026_;
v_isShared_1036_ = v_isSharedCheck_1050_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_idx_1033_);
lean_inc(v_array_1032_);
lean_dec(v_it_1026_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1050_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_lower_1038_; lean_object* v_upper_1039_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___y_1047_; uint8_t v___x_1049_; 
v___x_1044_ = lean_nat_add(v_idx_1033_, v_fst_1030_);
lean_dec(v_fst_1030_);
v___x_1045_ = lean_byte_array_size(v_array_1032_);
v___x_1049_ = lean_nat_dec_le(v_idx_1033_, v___x_1027_);
if (v___x_1049_ == 0)
{
v___y_1047_ = v_idx_1033_;
goto v___jp_1046_;
}
else
{
lean_dec(v_idx_1033_);
v___y_1047_ = v___x_1027_;
goto v___jp_1046_;
}
v___jp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1040_ = l_ByteArray_toByteSlice(v_array_1032_, v_lower_1038_, v_upper_1039_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 1, v___x_1040_);
lean_ctor_set(v___x_1035_, 0, v_fst_1031_);
v___x_1042_ = v___x_1035_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_fst_1031_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
v___jp_1046_:
{
uint8_t v___x_1048_; 
v___x_1048_ = lean_nat_dec_le(v___x_1044_, v___x_1045_);
if (v___x_1048_ == 0)
{
lean_dec(v___x_1044_);
v_lower_1038_ = v___y_1047_;
v_upper_1039_ = v___x_1045_;
goto v___jp_1037_;
}
else
{
v_lower_1038_ = v___y_1047_;
v_upper_1039_ = v___x_1044_;
goto v___jp_1037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileAtMost___boxed(lean_object* v_pred_1051_, lean_object* v_limit_1052_, lean_object* v_it_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Std_Internal_Parsec_ByteArray_takeWhileAtMost(v_pred_1051_, v_limit_1052_, v_it_1053_);
lean_dec(v_limit_1052_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost(lean_object* v_pred_1055_, lean_object* v_limit_1056_, lean_object* v_it_1057_){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v_snd_1060_; lean_object* v_fst_1061_; lean_object* v_fst_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1090_; 
v___x_1058_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_1057_);
v___x_1059_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_1055_, v_limit_1056_, v___x_1058_, v_it_1057_);
v_snd_1060_ = lean_ctor_get(v___x_1059_, 1);
lean_inc(v_snd_1060_);
v_fst_1061_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_fst_1061_);
lean_dec_ref(v___x_1059_);
v_fst_1062_ = lean_ctor_get(v_snd_1060_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_snd_1060_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v_snd_1060_, 1);
lean_dec(v_unused_1091_);
v___x_1064_ = v_snd_1060_;
v_isShared_1065_ = v_isSharedCheck_1090_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_fst_1062_);
lean_dec(v_snd_1060_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1090_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
uint8_t v___x_1066_; 
v___x_1066_ = lean_nat_dec_eq(v_fst_1061_, v___x_1058_);
if (v___x_1066_ == 0)
{
lean_object* v_array_1067_; lean_object* v_idx_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1085_; 
lean_del_object(v___x_1064_);
v_array_1067_ = lean_ctor_get(v_it_1057_, 0);
v_idx_1068_ = lean_ctor_get(v_it_1057_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_it_1057_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1070_ = v_it_1057_;
v_isShared_1071_ = v_isSharedCheck_1085_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_idx_1068_);
lean_inc(v_array_1067_);
lean_dec(v_it_1057_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1085_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v_lower_1073_; lean_object* v_upper_1074_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___y_1082_; uint8_t v___x_1084_; 
v___x_1079_ = lean_nat_add(v_idx_1068_, v_fst_1061_);
lean_dec(v_fst_1061_);
v___x_1080_ = lean_byte_array_size(v_array_1067_);
v___x_1084_ = lean_nat_dec_le(v_idx_1068_, v___x_1058_);
if (v___x_1084_ == 0)
{
v___y_1082_ = v_idx_1068_;
goto v___jp_1081_;
}
else
{
lean_dec(v_idx_1068_);
v___y_1082_ = v___x_1058_;
goto v___jp_1081_;
}
v___jp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1075_ = l_ByteArray_toByteSlice(v_array_1067_, v_lower_1073_, v_upper_1074_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 1, v___x_1075_);
lean_ctor_set(v___x_1070_, 0, v_fst_1062_);
v___x_1077_ = v___x_1070_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_fst_1062_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
v___jp_1081_:
{
uint8_t v___x_1083_; 
v___x_1083_ = lean_nat_dec_le(v___x_1079_, v___x_1080_);
if (v___x_1083_ == 0)
{
lean_dec(v___x_1079_);
v_lower_1073_ = v___y_1082_;
v_upper_1074_ = v___x_1080_;
goto v___jp_1072_;
}
else
{
v_lower_1073_ = v___y_1082_;
v_upper_1074_ = v___x_1079_;
goto v___jp_1072_;
}
}
}
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
lean_dec(v_fst_1062_);
lean_dec(v_fst_1061_);
v___x_1086_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1));
if (v_isShared_1065_ == 0)
{
lean_ctor_set_tag(v___x_1064_, 1);
lean_ctor_set(v___x_1064_, 1, v___x_1086_);
lean_ctor_set(v___x_1064_, 0, v_it_1057_);
v___x_1088_ = v___x_1064_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_it_1057_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost___boxed(lean_object* v_pred_1092_, lean_object* v_limit_1093_, lean_object* v_it_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost(v_pred_1092_, v_limit_1093_, v_it_1094_);
lean_dec(v_limit_1093_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(lean_object* v_pred_1096_, lean_object* v_limit_1097_, lean_object* v_it_1098_){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v_snd_1101_; lean_object* v_snd_1102_; uint8_t v___x_1103_; 
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_1096_, v_limit_1097_, v___x_1099_, v_it_1098_);
v_snd_1101_ = lean_ctor_get(v___x_1100_, 1);
lean_inc(v_snd_1101_);
lean_dec_ref(v___x_1100_);
v_snd_1102_ = lean_ctor_get(v_snd_1101_, 1);
v___x_1103_ = lean_unbox(v_snd_1102_);
if (v___x_1103_ == 0)
{
lean_object* v_fst_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1112_; 
v_fst_1104_ = lean_ctor_get(v_snd_1101_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_snd_1101_);
if (v_isSharedCheck_1112_ == 0)
{
lean_object* v_unused_1113_; 
v_unused_1113_ = lean_ctor_get(v_snd_1101_, 1);
lean_dec(v_unused_1113_);
v___x_1106_ = v_snd_1101_;
v_isShared_1107_ = v_isSharedCheck_1112_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_fst_1104_);
lean_dec(v_snd_1101_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1112_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1108_ = lean_box(0);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 1, v___x_1108_);
v___x_1110_ = v___x_1106_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_fst_1104_);
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
else
{
lean_object* v_fst_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1122_; 
v_fst_1114_ = lean_ctor_get(v_snd_1101_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_snd_1101_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v_snd_1101_, 1);
lean_dec(v_unused_1123_);
v___x_1116_ = v_snd_1101_;
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_fst_1114_);
lean_dec(v_snd_1101_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1118_ = lean_box(0);
if (v_isShared_1117_ == 0)
{
lean_ctor_set_tag(v___x_1116_, 1);
lean_ctor_set(v___x_1116_, 1, v___x_1118_);
v___x_1120_ = v___x_1116_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_fst_1114_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v___x_1118_);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhileUpTo___boxed(lean_object* v_pred_1124_, lean_object* v_limit_1125_, lean_object* v_it_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(v_pred_1124_, v_limit_1125_, v_it_1126_);
lean_dec(v_limit_1125_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(lean_object* v_pred_1128_, lean_object* v_limit_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___f_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v_snd_1134_; lean_object* v_snd_1135_; uint8_t v___x_1136_; 
v___f_1131_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1131_, 0, v_pred_1128_);
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1131_, v_limit_1129_, v___x_1132_, v_a_1130_);
v_snd_1134_ = lean_ctor_get(v___x_1133_, 1);
lean_inc(v_snd_1134_);
lean_dec_ref(v___x_1133_);
v_snd_1135_ = lean_ctor_get(v_snd_1134_, 1);
v___x_1136_ = lean_unbox(v_snd_1135_);
if (v___x_1136_ == 0)
{
lean_object* v_fst_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1145_; 
v_fst_1137_ = lean_ctor_get(v_snd_1134_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_snd_1134_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; 
v_unused_1146_ = lean_ctor_get(v_snd_1134_, 1);
lean_dec(v_unused_1146_);
v___x_1139_ = v_snd_1134_;
v_isShared_1140_ = v_isSharedCheck_1145_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_fst_1137_);
lean_dec(v_snd_1134_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1145_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1141_ = lean_box(0);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v___x_1141_);
v___x_1143_ = v___x_1139_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_fst_1137_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
else
{
lean_object* v_fst_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1155_; 
v_fst_1147_ = lean_ctor_get(v_snd_1134_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_snd_1134_);
if (v_isSharedCheck_1155_ == 0)
{
lean_object* v_unused_1156_; 
v_unused_1156_ = lean_ctor_get(v_snd_1134_, 1);
lean_dec(v_unused_1156_);
v___x_1149_ = v_snd_1134_;
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_fst_1147_);
lean_dec(v_snd_1134_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = lean_box(0);
if (v_isShared_1150_ == 0)
{
lean_ctor_set_tag(v___x_1149_, 1);
lean_ctor_set(v___x_1149_, 1, v___x_1151_);
v___x_1153_ = v___x_1149_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_fst_1147_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntilUpTo___boxed(lean_object* v_pred_1157_, lean_object* v_limit_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(v_pred_1157_, v_limit_1158_, v_a_1159_);
lean_dec(v_limit_1158_);
return v_res_1160_;
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
