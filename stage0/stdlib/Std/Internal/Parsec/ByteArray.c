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
uint8_t lean_uint8_of_nat(lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__1(lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0;
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
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0(void){
_start:
{
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = lean_uint8_of_nat(v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2(lean_object* v_it_19_){
_start:
{
lean_object* v_array_20_; lean_object* v_idx_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v_array_20_ = lean_ctor_get(v_it_19_, 0);
v_idx_21_ = lean_ctor_get(v_it_19_, 1);
v___x_22_ = lean_byte_array_size(v_array_20_);
v___x_23_ = lean_nat_dec_lt(v_idx_21_, v___x_22_);
if (v___x_23_ == 0)
{
uint8_t v___x_24_; 
v___x_24_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0, &l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0_once, _init_l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0);
return v___x_24_;
}
else
{
uint8_t v___x_25_; 
v___x_25_ = lean_byte_array_fget(v_array_20_, v_idx_21_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___boxed(lean_object* v_it_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2(v_it_26_);
lean_dec_ref(v_it_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3(lean_object* v_it_29_){
_start:
{
lean_object* v_array_30_; lean_object* v_idx_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v_array_30_ = lean_ctor_get(v_it_29_, 0);
v_idx_31_ = lean_ctor_get(v_it_29_, 1);
v___x_32_ = lean_byte_array_size(v_array_30_);
v___x_33_ = lean_nat_dec_lt(v_idx_31_, v___x_32_);
return v___x_33_;
}
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
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5(lean_object* v_it_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_array_52_; lean_object* v_idx_53_; uint8_t v___x_54_; 
v_array_52_ = lean_ctor_get(v_it_50_, 0);
v_idx_53_ = lean_ctor_get(v_it_50_, 1);
v___x_54_ = lean_byte_array_fget(v_array_52_, v_idx_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5___boxed(lean_object* v_it_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_res_57_; lean_object* v_r_58_; 
v_res_57_ = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5(v_it_55_, v___y_56_);
lean_dec_ref(v_it_55_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object* v_p_76_, lean_object* v_arr_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = l_ByteArray_mkIterator(v_arr_77_);
v___x_79_ = lean_apply_1(v_p_76_, v___x_78_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_res_80_; lean_object* v___x_81_; 
v_res_80_ = lean_ctor_get(v___x_79_, 1);
lean_inc(v_res_80_);
lean_dec_ref(v___x_79_);
v___x_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_81_, 0, v_res_80_);
return v___x_81_;
}
else
{
lean_object* v_pos_82_; lean_object* v_err_83_; lean_object* v_idx_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___y_95_; 
v_pos_82_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_pos_82_);
v_err_83_ = lean_ctor_get(v___x_79_, 1);
lean_inc(v_err_83_);
lean_dec_ref(v___x_79_);
v_idx_84_ = lean_ctor_get(v_pos_82_, 1);
lean_inc(v_idx_84_);
lean_dec(v_pos_82_);
v___x_85_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__0));
v___x_86_ = l_Nat_reprFast(v_idx_84_);
v___x_87_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
v___x_88_ = l_Std_Format_defWidth;
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = l_Std_Format_pretty(v___x_87_, v___x_88_, v___x_89_, v___x_89_);
v___x_91_ = lean_string_append(v___x_85_, v___x_90_);
lean_dec_ref(v___x_90_);
v___x_92_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__1));
v___x_93_ = lean_string_append(v___x_91_, v___x_92_);
if (lean_obj_tag(v_err_83_) == 0)
{
lean_object* v___x_98_; 
v___x_98_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__2));
v___y_95_ = v___x_98_;
goto v___jp_94_;
}
else
{
lean_object* v_s_99_; 
v_s_99_ = lean_ctor_get(v_err_83_, 0);
lean_inc_ref(v_s_99_);
lean_dec_ref(v_err_83_);
v___y_95_ = v_s_99_;
goto v___jp_94_;
}
v___jp_94_:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_string_append(v___x_93_, v___y_95_);
lean_dec_ref(v___y_95_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run(lean_object* v_00_u03b1_100_, lean_object* v_p_101_, lean_object* v_arr_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v_p_101_, v_arr_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pbyte(uint8_t v_b_106_, lean_object* v_it_107_){
_start:
{
lean_object* v_array_108_; lean_object* v_idx_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_array_108_ = lean_ctor_get(v_it_107_, 0);
v_idx_109_ = lean_ctor_get(v_it_107_, 1);
v___x_110_ = lean_byte_array_size(v_array_108_);
v___x_111_ = lean_nat_dec_lt(v_idx_109_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_box(0);
v___x_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_113_, 0, v_it_107_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
return v___x_113_;
}
else
{
uint8_t v_got_114_; uint8_t v___x_115_; 
v_got_114_ = lean_byte_array_fget(v_array_108_, v_idx_109_);
v___x_115_ = lean_uint8_dec_eq(v_got_114_, v_b_106_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_116_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0));
v___x_117_ = lean_uint8_to_nat(v_b_106_);
v___x_118_ = l_Nat_reprFast(v___x_117_);
v___x_119_ = lean_string_append(v___x_116_, v___x_118_);
lean_dec_ref(v___x_118_);
v___x_120_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1));
v___x_121_ = lean_string_append(v___x_119_, v___x_120_);
v___x_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
v___x_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_123_, 0, v_it_107_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
return v___x_123_;
}
else
{
lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_134_; 
lean_inc(v_idx_109_);
lean_inc_ref(v_array_108_);
v_isSharedCheck_134_ = !lean_is_exclusive(v_it_107_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; lean_object* v_unused_136_; 
v_unused_135_ = lean_ctor_get(v_it_107_, 1);
lean_dec(v_unused_135_);
v_unused_136_ = lean_ctor_get(v_it_107_, 0);
lean_dec(v_unused_136_);
v___x_125_ = v_it_107_;
v_isShared_126_ = v_isSharedCheck_134_;
goto v_resetjp_124_;
}
else
{
lean_dec(v_it_107_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_134_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_nat_add(v_idx_109_, v___x_127_);
lean_dec(v_idx_109_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_128_);
v___x_130_ = v___x_125_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_array_108_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_128_);
v___x_130_ = v_reuseFailAlloc_133_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_box(v_got_114_);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
return v___x_132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pbyte___boxed(lean_object* v_b_137_, lean_object* v_it_138_){
_start:
{
uint8_t v_b_boxed_139_; lean_object* v_res_140_; 
v_b_boxed_139_ = lean_unbox(v_b_137_);
v_res_140_ = l_Std_Internal_Parsec_ByteArray_pbyte(v_b_boxed_139_, v_it_138_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByte(uint8_t v_b_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_array_143_; lean_object* v_idx_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v_array_143_ = lean_ctor_get(v_a_142_, 0);
v_idx_144_ = lean_ctor_get(v_a_142_, 1);
v___x_145_ = lean_byte_array_size(v_array_143_);
v___x_146_ = lean_nat_dec_lt(v_idx_144_, v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_box(0);
v___x_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_148_, 0, v_a_142_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
return v___x_148_;
}
else
{
uint8_t v_got_149_; uint8_t v___x_150_; 
v_got_149_ = lean_byte_array_fget(v_array_143_, v_idx_144_);
v___x_150_ = lean_uint8_dec_eq(v_got_149_, v_b_141_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_151_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0));
v___x_152_ = lean_uint8_to_nat(v_b_141_);
v___x_153_ = l_Nat_reprFast(v___x_152_);
v___x_154_ = lean_string_append(v___x_151_, v___x_153_);
lean_dec_ref(v___x_153_);
v___x_155_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1));
v___x_156_ = lean_string_append(v___x_154_, v___x_155_);
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
v___x_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_158_, 0, v_a_142_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
return v___x_158_;
}
else
{
lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_169_; 
lean_inc(v_idx_144_);
lean_inc_ref(v_array_143_);
v_isSharedCheck_169_ = !lean_is_exclusive(v_a_142_);
if (v_isSharedCheck_169_ == 0)
{
lean_object* v_unused_170_; lean_object* v_unused_171_; 
v_unused_170_ = lean_ctor_get(v_a_142_, 1);
lean_dec(v_unused_170_);
v_unused_171_ = lean_ctor_get(v_a_142_, 0);
lean_dec(v_unused_171_);
v___x_160_ = v_a_142_;
v_isShared_161_ = v_isSharedCheck_169_;
goto v_resetjp_159_;
}
else
{
lean_dec(v_a_142_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_169_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_162_ = lean_unsigned_to_nat(1u);
v___x_163_ = lean_nat_add(v_idx_144_, v___x_162_);
lean_dec(v_idx_144_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_163_);
v___x_165_ = v___x_160_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_array_143_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___x_163_);
v___x_165_ = v_reuseFailAlloc_168_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_box(0);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
return v___x_167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByte___boxed(lean_object* v_b_172_, lean_object* v_a_173_){
_start:
{
uint8_t v_b_boxed_174_; lean_object* v_res_175_; 
v_b_boxed_174_ = lean_unbox(v_b_172_);
v_res_175_ = l_Std_Internal_Parsec_ByteArray_skipByte(v_b_boxed_174_, v_a_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go(lean_object* v_arr_178_, lean_object* v_idx_179_, lean_object* v_it_180_){
_start:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_byte_array_size(v_arr_178_);
v___x_182_ = lean_nat_dec_lt(v_idx_179_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_idx_179_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v_it_180_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
return v___x_184_;
}
else
{
lean_object* v_array_185_; lean_object* v_idx_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_array_185_ = lean_ctor_get(v_it_180_, 0);
v_idx_186_ = lean_ctor_get(v_it_180_, 1);
v___x_187_ = lean_byte_array_size(v_array_185_);
v___x_188_ = lean_nat_dec_lt(v_idx_186_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec(v_idx_179_);
v___x_189_ = lean_box(0);
v___x_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_190_, 0, v_it_180_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
return v___x_190_;
}
else
{
uint8_t v_got_191_; uint8_t v_want_192_; uint8_t v___x_193_; 
v_got_191_ = lean_byte_array_fget(v_array_185_, v_idx_186_);
v_want_192_ = lean_byte_array_fget(v_arr_178_, v_idx_179_);
v___x_193_ = lean_uint8_dec_eq(v_got_191_, v_want_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v_idx_179_);
v___x_194_ = ((lean_object*)(l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__0));
v___x_195_ = lean_uint8_to_nat(v_want_192_);
v___x_196_ = l_Nat_reprFast(v___x_195_);
v___x_197_ = lean_string_append(v___x_194_, v___x_196_);
lean_dec_ref(v___x_196_);
v___x_198_ = ((lean_object*)(l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___closed__1));
v___x_199_ = lean_string_append(v___x_197_, v___x_198_);
v___x_200_ = lean_uint8_to_nat(v_got_191_);
v___x_201_ = l_Nat_reprFast(v___x_200_);
v___x_202_ = lean_string_append(v___x_199_, v___x_201_);
lean_dec_ref(v___x_201_);
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
v___x_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_204_, 0, v_it_180_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
return v___x_204_;
}
else
{
lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_215_; 
lean_inc(v_idx_186_);
lean_inc_ref(v_array_185_);
v_isSharedCheck_215_ = !lean_is_exclusive(v_it_180_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; lean_object* v_unused_217_; 
v_unused_216_ = lean_ctor_get(v_it_180_, 1);
lean_dec(v_unused_216_);
v_unused_217_ = lean_ctor_get(v_it_180_, 0);
lean_dec(v_unused_217_);
v___x_206_ = v_it_180_;
v_isShared_207_ = v_isSharedCheck_215_;
goto v_resetjp_205_;
}
else
{
lean_dec(v_it_180_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_215_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_208_ = lean_unsigned_to_nat(1u);
v___x_209_ = lean_nat_add(v_idx_179_, v___x_208_);
lean_dec(v_idx_179_);
v___x_210_ = lean_nat_add(v_idx_186_, v___x_208_);
lean_dec(v_idx_186_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v___x_210_);
v___x_212_ = v___x_206_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_array_185_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_210_);
v___x_212_ = v_reuseFailAlloc_214_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
v_idx_179_ = v___x_209_;
v_it_180_ = v___x_212_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go___boxed(lean_object* v_arr_218_, lean_object* v_idx_219_, lean_object* v_it_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go(v_arr_218_, v_idx_219_, v_it_220_);
lean_dec_ref(v_arr_218_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object* v_arr_222_, lean_object* v_it_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipBytes_go(v_arr_222_, v___x_224_, v_it_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes___boxed(lean_object* v_arr_226_, lean_object* v_it_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_arr_226_, v_it_227_);
lean_dec_ref(v_arr_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pstring(lean_object* v_s_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_utf8_231_; lean_object* v___x_232_; 
v_utf8_231_ = lean_string_to_utf8(v_s_229_);
v___x_232_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_231_, v_a_230_);
lean_dec_ref(v_utf8_231_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_pos_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
v_pos_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; 
v_unused_241_ = lean_ctor_get(v___x_232_, 1);
lean_dec(v_unused_241_);
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_pos_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v_s_229_);
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_pos_233_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_s_229_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
else
{
lean_object* v_pos_242_; lean_object* v_err_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec_ref(v_s_229_);
v_pos_242_ = lean_ctor_get(v___x_232_, 0);
v_err_243_ = lean_ctor_get(v___x_232_, 1);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_232_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_err_243_);
lean_inc(v_pos_242_);
lean_dec(v___x_232_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_pos_242_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_err_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipString(lean_object* v_s_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_utf8_253_; lean_object* v___x_254_; 
v_utf8_253_ = lean_string_to_utf8(v_s_251_);
v___x_254_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_253_, v_a_252_);
lean_dec_ref(v_utf8_253_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_pos_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_263_; 
v_pos_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; 
v_unused_264_ = lean_ctor_get(v___x_254_, 1);
lean_dec(v_unused_264_);
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_pos_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_259_ = lean_box(0);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v___x_259_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_pos_255_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
else
{
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipString___boxed(lean_object* v_s_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Std_Internal_Parsec_ByteArray_skipString(v_s_265_, v_a_266_);
lean_dec_ref(v_s_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pByteChar(uint32_t v_c_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_array_271_; lean_object* v_idx_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v_array_271_ = lean_ctor_get(v_a_270_, 0);
v_idx_272_ = lean_ctor_get(v_a_270_, 1);
v___x_273_ = lean_byte_array_size(v_array_271_);
v___x_274_ = lean_nat_dec_lt(v_idx_272_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_box(0);
v___x_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_276_, 0, v_a_270_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
return v___x_276_;
}
else
{
uint8_t v_c_277_; uint8_t v___x_278_; uint8_t v___x_279_; 
v_c_277_ = lean_byte_array_fget(v_array_271_, v_idx_272_);
v___x_278_ = lean_uint32_to_uint8(v_c_269_);
v___x_279_ = lean_uint8_dec_eq(v_c_277_, v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_280_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0));
v___x_281_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0));
v___x_282_ = lean_string_push(v___x_281_, v_c_269_);
v___x_283_ = lean_string_append(v___x_280_, v___x_282_);
lean_dec_ref(v___x_282_);
v___x_284_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1));
v___x_285_ = lean_string_append(v___x_283_, v___x_284_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
v___x_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_287_, 0, v_a_270_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
return v___x_287_;
}
else
{
lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_298_; 
lean_inc(v_idx_272_);
lean_inc_ref(v_array_271_);
v_isSharedCheck_298_ = !lean_is_exclusive(v_a_270_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; lean_object* v_unused_300_; 
v_unused_299_ = lean_ctor_get(v_a_270_, 1);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_a_270_, 0);
lean_dec(v_unused_300_);
v___x_289_ = v_a_270_;
v_isShared_290_ = v_isSharedCheck_298_;
goto v_resetjp_288_;
}
else
{
lean_dec(v_a_270_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_298_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v_it_x27_294_; 
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_add(v_idx_272_, v___x_291_);
lean_dec(v_idx_272_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 1, v___x_292_);
v_it_x27_294_ = v___x_289_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_array_271_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_292_);
v_it_x27_294_ = v_reuseFailAlloc_297_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_box_uint32(v_c_269_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_it_x27_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
return v___x_296_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pByteChar___boxed(lean_object* v_c_301_, lean_object* v_a_302_){
_start:
{
uint32_t v_c_boxed_303_; lean_object* v_res_304_; 
v_c_boxed_303_ = lean_unbox_uint32(v_c_301_);
lean_dec(v_c_301_);
v_res_304_ = l_Std_Internal_Parsec_ByteArray_pByteChar(v_c_boxed_303_, v_a_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByteChar(uint32_t v_c_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_array_307_; lean_object* v_idx_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_array_307_ = lean_ctor_get(v_a_306_, 0);
v_idx_308_ = lean_ctor_get(v_a_306_, 1);
v___x_309_ = lean_byte_array_size(v_array_307_);
v___x_310_ = lean_nat_dec_lt(v_idx_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_box(0);
v___x_312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_312_, 0, v_a_306_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
return v___x_312_;
}
else
{
uint8_t v___x_313_; uint8_t v_got_314_; uint8_t v___x_315_; 
v___x_313_ = lean_uint32_to_uint8(v_c_305_);
v_got_314_ = lean_byte_array_fget(v_array_307_, v_idx_308_);
v___x_315_ = lean_uint8_dec_eq(v_got_314_, v___x_313_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_316_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0));
v___x_317_ = lean_uint8_to_nat(v___x_313_);
v___x_318_ = l_Nat_reprFast(v___x_317_);
v___x_319_ = lean_string_append(v___x_316_, v___x_318_);
lean_dec_ref(v___x_318_);
v___x_320_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1));
v___x_321_ = lean_string_append(v___x_319_, v___x_320_);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
v___x_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_323_, 0, v_a_306_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
return v___x_323_;
}
else
{
lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_334_; 
lean_inc(v_idx_308_);
lean_inc_ref(v_array_307_);
v_isSharedCheck_334_ = !lean_is_exclusive(v_a_306_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; lean_object* v_unused_336_; 
v_unused_335_ = lean_ctor_get(v_a_306_, 1);
lean_dec(v_unused_335_);
v_unused_336_ = lean_ctor_get(v_a_306_, 0);
lean_dec(v_unused_336_);
v___x_325_ = v_a_306_;
v_isShared_326_ = v_isSharedCheck_334_;
goto v_resetjp_324_;
}
else
{
lean_dec(v_a_306_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_334_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_327_ = lean_unsigned_to_nat(1u);
v___x_328_ = lean_nat_add(v_idx_308_, v___x_327_);
lean_dec(v_idx_308_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v___x_328_);
v___x_330_ = v___x_325_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_array_307_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_328_);
v___x_330_ = v_reuseFailAlloc_333_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_box(0);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
return v___x_332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByteChar___boxed(lean_object* v_c_337_, lean_object* v_a_338_){
_start:
{
uint32_t v_c_boxed_339_; lean_object* v_res_340_; 
v_c_boxed_339_ = lean_unbox_uint32(v_c_337_);
lean_dec(v_c_337_);
v_res_340_ = l_Std_Internal_Parsec_ByteArray_skipByteChar(v_c_boxed_339_, v_a_338_);
return v_res_340_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2(void){
_start:
{
uint32_t v___x_344_; uint8_t v___x_345_; 
v___x_344_ = 48;
v___x_345_ = lean_uint32_to_uint8(v___x_344_);
return v___x_345_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3(void){
_start:
{
uint32_t v___x_346_; uint8_t v___x_347_; 
v___x_346_ = 57;
v___x_347_ = lean_uint32_to_uint8(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digit(lean_object* v_a_348_){
_start:
{
lean_object* v_array_352_; lean_object* v_idx_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_array_352_ = lean_ctor_get(v_a_348_, 0);
v_idx_353_ = lean_ctor_get(v_a_348_, 1);
v___x_354_ = lean_byte_array_size(v_array_352_);
v___x_355_ = lean_nat_dec_lt(v_idx_353_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_box(0);
v___x_357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_357_, 0, v_a_348_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
return v___x_357_;
}
else
{
uint8_t v_c_358_; uint8_t v___x_359_; uint8_t v___x_360_; 
v_c_358_ = lean_byte_array_fget(v_array_352_, v_idx_353_);
v___x_359_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_360_ = lean_uint8_dec_le(v___x_359_, v_c_358_);
if (v___x_360_ == 0)
{
goto v___jp_349_;
}
else
{
uint8_t v___x_361_; uint8_t v___x_362_; 
v___x_361_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__3, &l_Std_Internal_Parsec_ByteArray_digit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3);
v___x_362_ = lean_uint8_dec_le(v_c_358_, v___x_361_);
if (v___x_362_ == 0)
{
goto v___jp_349_;
}
else
{
lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_374_; 
lean_inc(v_idx_353_);
lean_inc_ref(v_array_352_);
v_isSharedCheck_374_ = !lean_is_exclusive(v_a_348_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; lean_object* v_unused_376_; 
v_unused_375_ = lean_ctor_get(v_a_348_, 1);
lean_dec(v_unused_375_);
v_unused_376_ = lean_ctor_get(v_a_348_, 0);
lean_dec(v_unused_376_);
v___x_364_ = v_a_348_;
v_isShared_365_ = v_isSharedCheck_374_;
goto v_resetjp_363_;
}
else
{
lean_dec(v_a_348_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_374_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_it_x27_369_; 
v___x_366_ = lean_unsigned_to_nat(1u);
v___x_367_ = lean_nat_add(v_idx_353_, v___x_366_);
lean_dec(v_idx_353_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v___x_367_);
v_it_x27_369_ = v___x_364_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_array_352_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_367_);
v_it_x27_369_ = v_reuseFailAlloc_373_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
uint32_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = lean_uint8_to_uint32(v_c_358_);
v___x_371_ = lean_box_uint32(v___x_370_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v_it_x27_369_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
return v___x_372_;
}
}
}
}
}
v___jp_349_:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_digit___closed__1));
v___x_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_351_, 0, v_a_348_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(uint8_t v_b_377_){
_start:
{
uint8_t v___x_378_; uint8_t v___x_379_; lean_object* v___x_380_; 
v___x_378_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_379_ = lean_uint8_sub(v_b_377_, v___x_378_);
v___x_380_ = lean_uint8_to_nat(v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat___boxed(lean_object* v_b_381_){
_start:
{
uint8_t v_b_boxed_382_; lean_object* v_res_383_; 
v_b_boxed_382_ = lean_unbox(v_b_381_);
v_res_383_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(v_b_boxed_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object* v_it_384_, lean_object* v_acc_385_){
_start:
{
lean_object* v_array_386_; lean_object* v_idx_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v_array_386_ = lean_ctor_get(v_it_384_, 0);
v_idx_387_ = lean_ctor_get(v_it_384_, 1);
v___x_388_ = lean_byte_array_size(v_array_386_);
v___x_389_ = lean_nat_dec_lt(v_idx_387_, v___x_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_acc_385_);
lean_ctor_set(v___x_390_, 1, v_it_384_);
return v___x_390_;
}
else
{
uint8_t v_candidate_391_; uint8_t v___x_392_; uint8_t v___x_393_; 
v_candidate_391_ = lean_byte_array_fget(v_array_386_, v_idx_387_);
v___x_392_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_393_ = lean_uint8_dec_le(v___x_392_, v_candidate_391_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v_acc_385_);
lean_ctor_set(v___x_394_, 1, v_it_384_);
return v___x_394_;
}
else
{
uint8_t v___x_395_; uint8_t v___x_396_; 
v___x_395_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__3, &l_Std_Internal_Parsec_ByteArray_digit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3);
v___x_396_ = lean_uint8_dec_le(v_candidate_391_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; 
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_acc_385_);
lean_ctor_set(v___x_397_, 1, v_it_384_);
return v___x_397_;
}
else
{
lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_412_; 
lean_inc(v_idx_387_);
lean_inc_ref(v_array_386_);
v_isSharedCheck_412_ = !lean_is_exclusive(v_it_384_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; lean_object* v_unused_414_; 
v_unused_413_ = lean_ctor_get(v_it_384_, 1);
lean_dec(v_unused_413_);
v_unused_414_ = lean_ctor_get(v_it_384_, 0);
lean_dec(v_unused_414_);
v___x_399_ = v_it_384_;
v_isShared_400_ = v_isSharedCheck_412_;
goto v_resetjp_398_;
}
else
{
lean_dec(v_it_384_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_412_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
uint8_t v___x_401_; lean_object* v_digit_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v_acc_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_401_ = lean_uint8_sub(v_candidate_391_, v___x_392_);
v_digit_402_ = lean_uint8_to_nat(v___x_401_);
v___x_403_ = lean_unsigned_to_nat(10u);
v___x_404_ = lean_nat_mul(v_acc_385_, v___x_403_);
lean_dec(v_acc_385_);
v_acc_405_ = lean_nat_add(v___x_404_, v_digit_402_);
lean_dec(v___x_404_);
v___x_406_ = lean_unsigned_to_nat(1u);
v___x_407_ = lean_nat_add(v_idx_387_, v___x_406_);
lean_dec(v_idx_387_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 1, v___x_407_);
v___x_409_ = v___x_399_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_array_386_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v___x_407_);
v___x_409_ = v_reuseFailAlloc_411_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
v_it_384_ = v___x_409_;
v_acc_385_ = v_acc_405_;
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
lean_object* v_array_431_; lean_object* v_idx_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_array_431_ = lean_ctor_get(v_a_427_, 0);
v_idx_432_ = lean_ctor_get(v_a_427_, 1);
v___x_433_ = lean_byte_array_size(v_array_431_);
v___x_434_ = lean_nat_dec_lt(v_idx_432_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_box(0);
v___x_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_436_, 0, v_a_427_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
return v___x_436_;
}
else
{
uint8_t v_c_437_; uint8_t v___x_438_; uint8_t v___x_439_; 
v_c_437_ = lean_byte_array_fget(v_array_431_, v_idx_432_);
v___x_438_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_439_ = lean_uint8_dec_le(v___x_438_, v_c_437_);
if (v___x_439_ == 0)
{
goto v___jp_428_;
}
else
{
uint8_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__3, &l_Std_Internal_Parsec_ByteArray_digit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3);
v___x_441_ = lean_uint8_dec_le(v_c_437_, v___x_440_);
if (v___x_441_ == 0)
{
goto v___jp_428_;
}
else
{
lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_464_; 
lean_inc(v_idx_432_);
lean_inc_ref(v_array_431_);
v_isSharedCheck_464_ = !lean_is_exclusive(v_a_427_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; lean_object* v_unused_466_; 
v_unused_465_ = lean_ctor_get(v_a_427_, 1);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_a_427_, 0);
lean_dec(v_unused_466_);
v___x_443_ = v_a_427_;
v_isShared_444_ = v_isSharedCheck_464_;
goto v_resetjp_442_;
}
else
{
lean_dec(v_a_427_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_464_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v_it_x27_448_; 
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_add(v_idx_432_, v___x_445_);
lean_dec(v_idx_432_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 1, v___x_446_);
v_it_x27_448_ = v___x_443_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_array_431_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_446_);
v_it_x27_448_ = v_reuseFailAlloc_463_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
uint32_t v___x_449_; uint8_t v___x_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v_fst_454_; lean_object* v_snd_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
v___x_449_ = lean_uint8_to_uint32(v_c_437_);
v___x_450_ = lean_uint32_to_uint8(v___x_449_);
v___x_451_ = lean_uint8_sub(v___x_450_, v___x_438_);
v___x_452_ = lean_uint8_to_nat(v___x_451_);
v___x_453_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_448_, v___x_452_);
v_fst_454_ = lean_ctor_get(v___x_453_, 0);
v_snd_455_ = lean_ctor_get(v___x_453_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_453_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_snd_455_);
lean_inc(v_fst_454_);
lean_dec(v___x_453_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v_fst_454_);
lean_ctor_set(v___x_457_, 0, v_snd_455_);
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_snd_455_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_fst_454_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
}
}
v___jp_428_:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_digit___closed__1));
v___x_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_430_, 0, v_a_427_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
return v___x_430_;
}
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2(void){
_start:
{
uint32_t v___x_470_; uint8_t v___x_471_; 
v___x_470_ = 65;
v___x_471_ = lean_uint32_to_uint8(v___x_470_);
return v___x_471_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3(void){
_start:
{
uint32_t v___x_472_; uint8_t v___x_473_; 
v___x_472_ = 70;
v___x_473_ = lean_uint32_to_uint8(v___x_472_);
return v___x_473_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4(void){
_start:
{
uint32_t v___x_474_; uint8_t v___x_475_; 
v___x_474_ = 97;
v___x_475_ = lean_uint32_to_uint8(v___x_474_);
return v___x_475_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5(void){
_start:
{
uint32_t v___x_476_; uint8_t v___x_477_; 
v___x_476_ = 102;
v___x_477_ = lean_uint32_to_uint8(v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_hexDigit(lean_object* v_a_478_){
_start:
{
lean_object* v_array_482_; lean_object* v_idx_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v_array_482_ = lean_ctor_get(v_a_478_, 0);
v_idx_483_ = lean_ctor_get(v_a_478_, 1);
v___x_484_ = lean_byte_array_size(v_array_482_);
v___x_485_ = lean_nat_dec_lt(v_idx_483_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_box(0);
v___x_487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_487_, 0, v_a_478_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
return v___x_487_;
}
else
{
uint8_t v_c_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_it_x27_491_; uint8_t v___x_506_; uint8_t v___x_507_; 
v_c_488_ = lean_byte_array_fget(v_array_482_, v_idx_483_);
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_nat_add(v_idx_483_, v___x_489_);
lean_inc_ref(v_array_482_);
v_it_x27_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_491_, 0, v_array_482_);
lean_ctor_set(v_it_x27_491_, 1, v___x_490_);
v___x_506_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_507_ = lean_uint8_dec_le(v___x_506_, v_c_488_);
if (v___x_507_ == 0)
{
goto v___jp_501_;
}
else
{
uint8_t v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__3, &l_Std_Internal_Parsec_ByteArray_digit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3);
v___x_509_ = lean_uint8_dec_le(v_c_488_, v___x_508_);
if (v___x_509_ == 0)
{
goto v___jp_501_;
}
else
{
lean_dec_ref(v_a_478_);
goto v___jp_492_;
}
}
v___jp_492_:
{
uint32_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_uint8_to_uint32(v_c_488_);
v___x_494_ = lean_box_uint32(v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v_it_x27_491_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
return v___x_495_;
}
v___jp_496_:
{
uint8_t v___x_497_; uint8_t v___x_498_; 
v___x_497_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2);
v___x_498_ = lean_uint8_dec_le(v___x_497_, v_c_488_);
if (v___x_498_ == 0)
{
lean_dec_ref(v_it_x27_491_);
goto v___jp_479_;
}
else
{
uint8_t v___x_499_; uint8_t v___x_500_; 
v___x_499_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3);
v___x_500_ = lean_uint8_dec_le(v_c_488_, v___x_499_);
if (v___x_500_ == 0)
{
lean_dec_ref(v_it_x27_491_);
goto v___jp_479_;
}
else
{
lean_dec_ref(v_a_478_);
goto v___jp_492_;
}
}
}
v___jp_501_:
{
uint8_t v___x_502_; uint8_t v___x_503_; 
v___x_502_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4);
v___x_503_ = lean_uint8_dec_le(v___x_502_, v_c_488_);
if (v___x_503_ == 0)
{
goto v___jp_496_;
}
else
{
uint8_t v___x_504_; uint8_t v___x_505_; 
v___x_504_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5);
v___x_505_ = lean_uint8_dec_le(v_c_488_, v___x_504_);
if (v___x_505_ == 0)
{
goto v___jp_496_;
}
else
{
lean_dec_ref(v_a_478_);
goto v___jp_492_;
}
}
}
}
v___jp_479_:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1));
v___x_481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_481_, 0, v_a_478_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
return v___x_481_;
}
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_octDigit___closed__2(void){
_start:
{
uint32_t v___x_513_; uint8_t v___x_514_; 
v___x_513_ = 55;
v___x_514_ = lean_uint32_to_uint8(v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_octDigit(lean_object* v_a_515_){
_start:
{
lean_object* v_array_519_; lean_object* v_idx_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v_array_519_ = lean_ctor_get(v_a_515_, 0);
v_idx_520_ = lean_ctor_get(v_a_515_, 1);
v___x_521_ = lean_byte_array_size(v_array_519_);
v___x_522_ = lean_nat_dec_lt(v_idx_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_box(0);
v___x_524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_524_, 0, v_a_515_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
return v___x_524_;
}
else
{
uint8_t v_c_525_; uint8_t v___x_526_; uint8_t v___x_527_; 
v_c_525_ = lean_byte_array_fget(v_array_519_, v_idx_520_);
v___x_526_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_527_ = lean_uint8_dec_le(v___x_526_, v_c_525_);
if (v___x_527_ == 0)
{
goto v___jp_516_;
}
else
{
uint8_t v___x_528_; uint8_t v___x_529_; 
v___x_528_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_octDigit___closed__2, &l_Std_Internal_Parsec_ByteArray_octDigit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_octDigit___closed__2);
v___x_529_ = lean_uint8_dec_le(v_c_525_, v___x_528_);
if (v___x_529_ == 0)
{
goto v___jp_516_;
}
else
{
lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_541_; 
lean_inc(v_idx_520_);
lean_inc_ref(v_array_519_);
v_isSharedCheck_541_ = !lean_is_exclusive(v_a_515_);
if (v_isSharedCheck_541_ == 0)
{
lean_object* v_unused_542_; lean_object* v_unused_543_; 
v_unused_542_ = lean_ctor_get(v_a_515_, 1);
lean_dec(v_unused_542_);
v_unused_543_ = lean_ctor_get(v_a_515_, 0);
lean_dec(v_unused_543_);
v___x_531_ = v_a_515_;
v_isShared_532_ = v_isSharedCheck_541_;
goto v_resetjp_530_;
}
else
{
lean_dec(v_a_515_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_541_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v_it_x27_536_; 
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_add(v_idx_520_, v___x_533_);
lean_dec(v_idx_520_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 1, v___x_534_);
v_it_x27_536_ = v___x_531_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_array_519_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v___x_534_);
v_it_x27_536_ = v_reuseFailAlloc_540_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
uint32_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = lean_uint8_to_uint32(v_c_525_);
v___x_538_ = lean_box_uint32(v___x_537_);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v_it_x27_536_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
return v___x_539_;
}
}
}
}
}
v___jp_516_:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_octDigit___closed__1));
v___x_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_518_, 0, v_a_515_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
return v___x_518_;
}
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2(void){
_start:
{
uint32_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = 122;
v___x_548_ = lean_uint32_to_uint8(v___x_547_);
return v___x_548_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3(void){
_start:
{
uint32_t v___x_549_; uint8_t v___x_550_; 
v___x_549_ = 90;
v___x_550_ = lean_uint32_to_uint8(v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_asciiLetter(lean_object* v_a_551_){
_start:
{
lean_object* v_array_555_; lean_object* v_idx_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_array_555_ = lean_ctor_get(v_a_551_, 0);
v_idx_556_ = lean_ctor_get(v_a_551_, 1);
v___x_557_ = lean_byte_array_size(v_array_555_);
v___x_558_ = lean_nat_dec_lt(v_idx_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_box(0);
v___x_560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_560_, 0, v_a_551_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
return v___x_560_;
}
else
{
uint8_t v_c_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v_it_x27_564_; uint8_t v___x_574_; uint8_t v___x_575_; 
v_c_561_ = lean_byte_array_fget(v_array_555_, v_idx_556_);
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_idx_556_, v___x_562_);
lean_inc_ref(v_array_555_);
v_it_x27_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_564_, 0, v_array_555_);
lean_ctor_set(v_it_x27_564_, 1, v___x_563_);
v___x_574_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2);
v___x_575_ = lean_uint8_dec_le(v___x_574_, v_c_561_);
if (v___x_575_ == 0)
{
goto v___jp_569_;
}
else
{
uint8_t v___x_576_; uint8_t v___x_577_; 
v___x_576_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3, &l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3);
v___x_577_ = lean_uint8_dec_le(v_c_561_, v___x_576_);
if (v___x_577_ == 0)
{
goto v___jp_569_;
}
else
{
lean_dec_ref(v_a_551_);
goto v___jp_565_;
}
}
v___jp_565_:
{
uint32_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = lean_uint8_to_uint32(v_c_561_);
v___x_567_ = lean_box_uint32(v___x_566_);
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v_it_x27_564_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
return v___x_568_;
}
v___jp_569_:
{
uint8_t v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4);
v___x_571_ = lean_uint8_dec_le(v___x_570_, v_c_561_);
if (v___x_571_ == 0)
{
lean_dec_ref(v_it_x27_564_);
goto v___jp_552_;
}
else
{
uint8_t v___x_572_; uint8_t v___x_573_; 
v___x_572_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2, &l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2);
v___x_573_ = lean_uint8_dec_le(v_c_561_, v___x_572_);
if (v___x_573_ == 0)
{
lean_dec_ref(v_it_x27_564_);
goto v___jp_552_;
}
else
{
lean_dec_ref(v_a_551_);
goto v___jp_565_;
}
}
}
}
v___jp_552_:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1));
v___x_554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_554_, 0, v_a_551_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
return v___x_554_;
}
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0(void){
_start:
{
uint32_t v___x_578_; uint8_t v___x_579_; 
v___x_578_ = 9;
v___x_579_ = lean_uint32_to_uint8(v___x_578_);
return v___x_579_;
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1(void){
_start:
{
uint32_t v___x_580_; uint8_t v___x_581_; 
v___x_580_ = 10;
v___x_581_ = lean_uint32_to_uint8(v___x_580_);
return v___x_581_;
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2(void){
_start:
{
uint32_t v___x_582_; uint8_t v___x_583_; 
v___x_582_ = 13;
v___x_583_ = lean_uint32_to_uint8(v___x_582_);
return v___x_583_;
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3(void){
_start:
{
uint32_t v___x_584_; uint8_t v___x_585_; 
v___x_584_ = 32;
v___x_585_ = lean_uint32_to_uint8(v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(lean_object* v_it_586_){
_start:
{
lean_object* v_array_587_; lean_object* v_idx_588_; lean_object* v___x_594_; uint8_t v___x_595_; 
v_array_587_ = lean_ctor_get(v_it_586_, 0);
v_idx_588_ = lean_ctor_get(v_it_586_, 1);
v___x_594_ = lean_byte_array_size(v_array_587_);
v___x_595_ = lean_nat_dec_lt(v_idx_588_, v___x_594_);
if (v___x_595_ == 0)
{
return v_it_586_;
}
else
{
uint8_t v_b_596_; uint8_t v___x_597_; uint8_t v___x_598_; 
v_b_596_ = lean_byte_array_fget(v_array_587_, v_idx_588_);
v___x_597_ = lean_uint8_once(&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0, &l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0_once, _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0);
v___x_598_ = lean_uint8_dec_eq(v_b_596_, v___x_597_);
if (v___x_598_ == 0)
{
uint8_t v___x_599_; uint8_t v___x_600_; 
v___x_599_ = lean_uint8_once(&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1, &l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1_once, _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1);
v___x_600_ = lean_uint8_dec_eq(v_b_596_, v___x_599_);
if (v___x_600_ == 0)
{
uint8_t v___x_601_; uint8_t v___x_602_; 
v___x_601_ = lean_uint8_once(&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2, &l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2_once, _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2);
v___x_602_ = lean_uint8_dec_eq(v_b_596_, v___x_601_);
if (v___x_602_ == 0)
{
uint8_t v___x_603_; uint8_t v___x_604_; 
v___x_603_ = lean_uint8_once(&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3, &l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3_once, _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3);
v___x_604_ = lean_uint8_dec_eq(v_b_596_, v___x_603_);
if (v___x_604_ == 0)
{
return v_it_586_;
}
else
{
lean_inc(v_idx_588_);
lean_inc_ref(v_array_587_);
lean_dec_ref(v_it_586_);
goto v___jp_589_;
}
}
else
{
lean_inc(v_idx_588_);
lean_inc_ref(v_array_587_);
lean_dec_ref(v_it_586_);
goto v___jp_589_;
}
}
else
{
lean_inc(v_idx_588_);
lean_inc_ref(v_array_587_);
lean_dec_ref(v_it_586_);
goto v___jp_589_;
}
}
else
{
lean_inc(v_idx_588_);
lean_inc_ref(v_array_587_);
lean_dec_ref(v_it_586_);
goto v___jp_589_;
}
}
v___jp_589_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = lean_nat_add(v_idx_588_, v___x_590_);
lean_dec(v_idx_588_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v_array_587_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v_it_586_ = v___x_592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_ws(lean_object* v_it_605_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(v_it_605_);
v___x_607_ = lean_box(0);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take(lean_object* v_n_609_, lean_object* v_it_610_){
_start:
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = l_ByteArray_Iterator_remainingBytes(v_it_610_);
v___x_612_ = lean_nat_dec_lt(v___x_611_, v_n_609_);
lean_dec(v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v_array_613_; lean_object* v_idx_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_633_; 
v_array_613_ = lean_ctor_get(v_it_610_, 0);
v_idx_614_ = lean_ctor_get(v_it_610_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_it_610_);
if (v_isSharedCheck_633_ == 0)
{
v___x_616_ = v_it_610_;
v_isShared_617_ = v_isSharedCheck_633_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_idx_614_);
lean_inc(v_array_613_);
lean_dec(v_it_610_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_633_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_618_ = lean_nat_add(v_idx_614_, v_n_609_);
lean_inc(v___x_618_);
lean_inc_ref(v_array_613_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v___x_618_);
v___x_620_ = v___x_616_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_array_613_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___x_618_);
v___x_620_ = v_reuseFailAlloc_632_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v_lower_622_; lean_object* v_upper_623_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___y_629_; uint8_t v___x_631_; 
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = lean_byte_array_size(v_array_613_);
v___x_631_ = lean_nat_dec_le(v_idx_614_, v___x_626_);
if (v___x_631_ == 0)
{
v___y_629_ = v_idx_614_;
goto v___jp_628_;
}
else
{
lean_dec(v_idx_614_);
v___y_629_ = v___x_626_;
goto v___jp_628_;
}
v___jp_621_:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = l_ByteArray_toByteSlice(v_array_613_, v_lower_622_, v_upper_623_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_620_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
return v___x_625_;
}
v___jp_628_:
{
uint8_t v___x_630_; 
v___x_630_ = lean_nat_dec_le(v___x_618_, v___x_627_);
if (v___x_630_ == 0)
{
lean_dec(v___x_618_);
v_lower_622_ = v___y_629_;
v_upper_623_ = v___x_627_;
goto v___jp_621_;
}
else
{
v_lower_622_ = v___y_629_;
v_upper_623_ = v___x_618_;
goto v___jp_621_;
}
}
}
}
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_box(0);
v___x_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_635_, 0, v_it_610_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take___boxed(lean_object* v_n_636_, lean_object* v_it_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_Internal_Parsec_ByteArray_take(v_n_636_, v_it_637_);
lean_dec(v_n_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(lean_object* v_pred_639_, lean_object* v_count_640_, lean_object* v_iter_641_){
_start:
{
lean_object* v_array_642_; lean_object* v_idx_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_array_642_ = lean_ctor_get(v_iter_641_, 0);
v_idx_643_ = lean_ctor_get(v_iter_641_, 1);
v___x_644_ = lean_byte_array_size(v_array_642_);
v___x_645_ = lean_nat_dec_lt(v_idx_643_, v___x_644_);
if (v___x_645_ == 0)
{
uint8_t v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec_ref(v_pred_639_);
v___x_646_ = 1;
v___x_647_ = lean_box(v___x_646_);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v_iter_641_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v_count_640_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
return v___x_649_;
}
else
{
uint8_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_650_ = lean_byte_array_fget(v_array_642_, v_idx_643_);
v___x_651_ = lean_box(v___x_650_);
lean_inc_ref(v_pred_639_);
v___x_652_ = lean_apply_1(v_pred_639_, v___x_651_);
v___x_653_ = lean_unbox(v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec_ref(v_pred_639_);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v_iter_641_);
lean_ctor_set(v___x_654_, 1, v___x_652_);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v_count_640_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
return v___x_655_;
}
else
{
lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_666_; 
lean_inc(v_idx_643_);
lean_inc_ref(v_array_642_);
v_isSharedCheck_666_ = !lean_is_exclusive(v_iter_641_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; lean_object* v_unused_668_; 
v_unused_667_ = lean_ctor_get(v_iter_641_, 1);
lean_dec(v_unused_667_);
v_unused_668_ = lean_ctor_get(v_iter_641_, 0);
lean_dec(v_unused_668_);
v___x_657_ = v_iter_641_;
v_isShared_658_ = v_isSharedCheck_666_;
goto v_resetjp_656_;
}
else
{
lean_dec(v_iter_641_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_666_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_nat_add(v_count_640_, v___x_659_);
lean_dec(v_count_640_);
v___x_661_ = lean_nat_add(v_idx_643_, v___x_659_);
lean_dec(v_idx_643_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___x_661_);
v___x_663_ = v___x_657_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_array_642_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_661_);
v___x_663_ = v_reuseFailAlloc_665_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
v_count_640_ = v___x_660_;
v_iter_641_ = v___x_663_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object* v_pred_669_, lean_object* v_limit_670_, lean_object* v_count_671_, lean_object* v_iter_672_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = lean_nat_dec_le(v_limit_670_, v_count_671_);
if (v___x_673_ == 0)
{
lean_object* v_array_674_; lean_object* v_idx_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_array_674_ = lean_ctor_get(v_iter_672_, 0);
v_idx_675_ = lean_ctor_get(v_iter_672_, 1);
v___x_676_ = lean_byte_array_size(v_array_674_);
v___x_677_ = lean_nat_dec_lt(v_idx_675_, v___x_676_);
if (v___x_677_ == 0)
{
uint8_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
lean_dec_ref(v_pred_669_);
v___x_678_ = 1;
v___x_679_ = lean_box(v___x_678_);
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v_iter_672_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v_count_671_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
return v___x_681_;
}
else
{
uint8_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_682_ = lean_byte_array_fget(v_array_674_, v_idx_675_);
v___x_683_ = lean_box(v___x_682_);
lean_inc_ref(v_pred_669_);
v___x_684_ = lean_apply_1(v_pred_669_, v___x_683_);
v___x_685_ = lean_unbox(v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec_ref(v_pred_669_);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v_iter_672_);
lean_ctor_set(v___x_686_, 1, v___x_684_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v_count_671_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
return v___x_687_;
}
else
{
lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_698_; 
lean_inc(v_idx_675_);
lean_inc_ref(v_array_674_);
v_isSharedCheck_698_ = !lean_is_exclusive(v_iter_672_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; lean_object* v_unused_700_; 
v_unused_699_ = lean_ctor_get(v_iter_672_, 1);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_iter_672_, 0);
lean_dec(v_unused_700_);
v___x_689_ = v_iter_672_;
v_isShared_690_ = v_isSharedCheck_698_;
goto v_resetjp_688_;
}
else
{
lean_dec(v_iter_672_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_698_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_691_ = lean_unsigned_to_nat(1u);
v___x_692_ = lean_nat_add(v_count_671_, v___x_691_);
lean_dec(v_count_671_);
v___x_693_ = lean_nat_add(v_idx_675_, v___x_691_);
lean_dec(v_idx_675_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_693_);
v___x_695_ = v___x_689_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_array_674_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_693_);
v___x_695_ = v_reuseFailAlloc_697_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
v_count_671_ = v___x_692_;
v_iter_672_ = v___x_695_;
goto _start;
}
}
}
}
}
else
{
uint8_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec_ref(v_pred_669_);
v___x_701_ = 0;
v___x_702_ = lean_box(v___x_701_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v_iter_672_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v_count_671_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo___boxed(lean_object* v_pred_705_, lean_object* v_limit_706_, lean_object* v_count_707_, lean_object* v_iter_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_705_, v_limit_706_, v_count_707_, v_iter_708_);
lean_dec(v_limit_706_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile(lean_object* v_pred_710_, lean_object* v_it_711_){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_snd_714_; lean_object* v_snd_715_; uint8_t v___x_716_; 
v___x_712_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_711_);
v___x_713_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v_pred_710_, v___x_712_, v_it_711_);
v_snd_714_ = lean_ctor_get(v___x_713_, 1);
lean_inc(v_snd_714_);
v_snd_715_ = lean_ctor_get(v_snd_714_, 1);
v___x_716_ = lean_unbox(v_snd_715_);
if (v___x_716_ == 0)
{
lean_object* v_fst_717_; lean_object* v_fst_718_; lean_object* v_array_719_; lean_object* v_idx_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_737_; 
v_fst_717_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_fst_717_);
lean_dec_ref(v___x_713_);
v_fst_718_ = lean_ctor_get(v_snd_714_, 0);
lean_inc(v_fst_718_);
lean_dec(v_snd_714_);
v_array_719_ = lean_ctor_get(v_it_711_, 0);
v_idx_720_ = lean_ctor_get(v_it_711_, 1);
v_isSharedCheck_737_ = !lean_is_exclusive(v_it_711_);
if (v_isSharedCheck_737_ == 0)
{
v___x_722_ = v_it_711_;
v_isShared_723_ = v_isSharedCheck_737_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_idx_720_);
lean_inc(v_array_719_);
lean_dec(v_it_711_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_737_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_lower_725_; lean_object* v_upper_726_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___y_734_; uint8_t v___x_736_; 
v___x_731_ = lean_nat_add(v_idx_720_, v_fst_717_);
lean_dec(v_fst_717_);
v___x_732_ = lean_byte_array_size(v_array_719_);
v___x_736_ = lean_nat_dec_le(v_idx_720_, v___x_712_);
if (v___x_736_ == 0)
{
v___y_734_ = v_idx_720_;
goto v___jp_733_;
}
else
{
lean_dec(v_idx_720_);
v___y_734_ = v___x_712_;
goto v___jp_733_;
}
v___jp_724_:
{
lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_727_ = l_ByteArray_toByteSlice(v_array_719_, v_lower_725_, v_upper_726_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v___x_727_);
lean_ctor_set(v___x_722_, 0, v_fst_718_);
v___x_729_ = v___x_722_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_fst_718_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
v___jp_733_:
{
uint8_t v___x_735_; 
v___x_735_ = lean_nat_dec_le(v___x_731_, v___x_732_);
if (v___x_735_ == 0)
{
lean_dec(v___x_731_);
v_lower_725_ = v___y_734_;
v_upper_726_ = v___x_732_;
goto v___jp_724_;
}
else
{
v_lower_725_ = v___y_734_;
v_upper_726_ = v___x_731_;
goto v___jp_724_;
}
}
}
}
else
{
lean_object* v_fst_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_746_; 
lean_dec_ref(v___x_713_);
lean_dec_ref(v_it_711_);
v_fst_738_ = lean_ctor_get(v_snd_714_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v_snd_714_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; 
v_unused_747_ = lean_ctor_get(v_snd_714_, 1);
lean_dec(v_unused_747_);
v___x_740_ = v_snd_714_;
v_isShared_741_ = v_isSharedCheck_746_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_fst_738_);
lean_dec(v_snd_714_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_746_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = lean_box(0);
if (v_isShared_741_ == 0)
{
lean_ctor_set_tag(v___x_740_, 1);
lean_ctor_set(v___x_740_, 1, v___x_742_);
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_fst_738_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(lean_object* v_pred_748_, uint8_t v_b_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_750_ = lean_box(v_b_749_);
v___x_751_ = lean_apply_1(v_pred_748_, v___x_750_);
v___x_752_ = lean_unbox(v___x_751_);
if (v___x_752_ == 0)
{
uint8_t v___x_753_; 
v___x_753_ = 1;
return v___x_753_;
}
else
{
uint8_t v___x_754_; 
v___x_754_ = 0;
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed(lean_object* v_pred_755_, lean_object* v_b_756_){
_start:
{
uint8_t v_b_boxed_757_; uint8_t v_res_758_; lean_object* v_r_759_; 
v_b_boxed_757_ = lean_unbox(v_b_756_);
v_res_758_ = l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(v_pred_755_, v_b_boxed_757_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil(lean_object* v_pred_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___f_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v_snd_765_; lean_object* v_snd_766_; uint8_t v___x_767_; 
v___f_762_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_762_, 0, v_pred_760_);
v___x_763_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_761_);
v___x_764_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v___f_762_, v___x_763_, v_a_761_);
v_snd_765_ = lean_ctor_get(v___x_764_, 1);
lean_inc(v_snd_765_);
v_snd_766_ = lean_ctor_get(v_snd_765_, 1);
v___x_767_ = lean_unbox(v_snd_766_);
if (v___x_767_ == 0)
{
lean_object* v_fst_768_; lean_object* v_fst_769_; lean_object* v_array_770_; lean_object* v_idx_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_788_; 
v_fst_768_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_fst_768_);
lean_dec_ref(v___x_764_);
v_fst_769_ = lean_ctor_get(v_snd_765_, 0);
lean_inc(v_fst_769_);
lean_dec(v_snd_765_);
v_array_770_ = lean_ctor_get(v_a_761_, 0);
v_idx_771_ = lean_ctor_get(v_a_761_, 1);
v_isSharedCheck_788_ = !lean_is_exclusive(v_a_761_);
if (v_isSharedCheck_788_ == 0)
{
v___x_773_ = v_a_761_;
v_isShared_774_ = v_isSharedCheck_788_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_idx_771_);
lean_inc(v_array_770_);
lean_dec(v_a_761_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_788_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_lower_776_; lean_object* v_upper_777_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___y_785_; uint8_t v___x_787_; 
v___x_782_ = lean_nat_add(v_idx_771_, v_fst_768_);
lean_dec(v_fst_768_);
v___x_783_ = lean_byte_array_size(v_array_770_);
v___x_787_ = lean_nat_dec_le(v_idx_771_, v___x_763_);
if (v___x_787_ == 0)
{
v___y_785_ = v_idx_771_;
goto v___jp_784_;
}
else
{
lean_dec(v_idx_771_);
v___y_785_ = v___x_763_;
goto v___jp_784_;
}
v___jp_775_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = l_ByteArray_toByteSlice(v_array_770_, v_lower_776_, v_upper_777_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_778_);
lean_ctor_set(v___x_773_, 0, v_fst_769_);
v___x_780_ = v___x_773_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_fst_769_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
v___jp_784_:
{
uint8_t v___x_786_; 
v___x_786_ = lean_nat_dec_le(v___x_782_, v___x_783_);
if (v___x_786_ == 0)
{
lean_dec(v___x_782_);
v_lower_776_ = v___y_785_;
v_upper_777_ = v___x_783_;
goto v___jp_775_;
}
else
{
v_lower_776_ = v___y_785_;
v_upper_777_ = v___x_782_;
goto v___jp_775_;
}
}
}
}
else
{
lean_object* v_fst_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
lean_dec_ref(v___x_764_);
lean_dec_ref(v_a_761_);
v_fst_789_ = lean_ctor_get(v_snd_765_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v_snd_765_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; 
v_unused_798_ = lean_ctor_get(v_snd_765_, 1);
lean_dec(v_unused_798_);
v___x_791_ = v_snd_765_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_fst_789_);
lean_dec(v_snd_765_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = lean_box(0);
if (v_isShared_792_ == 0)
{
lean_ctor_set_tag(v___x_791_, 1);
lean_ctor_set(v___x_791_, 1, v___x_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_fst_789_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhile(lean_object* v_pred_799_, lean_object* v_it_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v_snd_803_; lean_object* v_snd_804_; uint8_t v___x_805_; 
v___x_801_ = lean_unsigned_to_nat(0u);
v___x_802_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v_pred_799_, v___x_801_, v_it_800_);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntil(lean_object* v_pred_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___f_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v_snd_831_; lean_object* v_snd_832_; uint8_t v___x_833_; 
v___f_828_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_828_, 0, v_pred_826_);
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v___f_828_, v___x_829_, v_a_827_);
v_snd_831_ = lean_ctor_get(v___x_830_, 1);
lean_inc(v_snd_831_);
lean_dec_ref(v___x_830_);
v_snd_832_ = lean_ctor_get(v_snd_831_, 1);
v___x_833_ = lean_unbox(v_snd_832_);
if (v___x_833_ == 0)
{
lean_object* v_fst_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_842_; 
v_fst_834_ = lean_ctor_get(v_snd_831_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v_snd_831_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v_snd_831_, 1);
lean_dec(v_unused_843_);
v___x_836_ = v_snd_831_;
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_fst_834_);
lean_dec(v_snd_831_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_838_ = lean_box(0);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_838_);
v___x_840_ = v___x_836_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_fst_834_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
else
{
lean_object* v_fst_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_852_; 
v_fst_844_ = lean_ctor_get(v_snd_831_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v_snd_831_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v_snd_831_, 1);
lean_dec(v_unused_853_);
v___x_846_ = v_snd_831_;
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_fst_844_);
lean_dec(v_snd_831_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_848_ = lean_box(0);
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 1);
lean_ctor_set(v___x_846_, 1, v___x_848_);
v___x_850_ = v___x_846_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_fst_844_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(lean_object* v_pred_854_, lean_object* v_limit_855_, lean_object* v_it_856_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v_snd_859_; lean_object* v_snd_860_; uint8_t v___x_861_; 
v___x_857_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_856_);
v___x_858_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_854_, v_limit_855_, v___x_857_, v_it_856_);
v_snd_859_ = lean_ctor_get(v___x_858_, 1);
lean_inc(v_snd_859_);
v_snd_860_ = lean_ctor_get(v_snd_859_, 1);
v___x_861_ = lean_unbox(v_snd_860_);
if (v___x_861_ == 0)
{
lean_object* v_fst_862_; lean_object* v_fst_863_; lean_object* v_array_864_; lean_object* v_idx_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_882_; 
v_fst_862_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_fst_862_);
lean_dec_ref(v___x_858_);
v_fst_863_ = lean_ctor_get(v_snd_859_, 0);
lean_inc(v_fst_863_);
lean_dec(v_snd_859_);
v_array_864_ = lean_ctor_get(v_it_856_, 0);
v_idx_865_ = lean_ctor_get(v_it_856_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v_it_856_);
if (v_isSharedCheck_882_ == 0)
{
v___x_867_ = v_it_856_;
v_isShared_868_ = v_isSharedCheck_882_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_idx_865_);
lean_inc(v_array_864_);
lean_dec(v_it_856_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_882_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_lower_870_; lean_object* v_upper_871_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___y_879_; uint8_t v___x_881_; 
v___x_876_ = lean_nat_add(v_idx_865_, v_fst_862_);
lean_dec(v_fst_862_);
v___x_877_ = lean_byte_array_size(v_array_864_);
v___x_881_ = lean_nat_dec_le(v_idx_865_, v___x_857_);
if (v___x_881_ == 0)
{
v___y_879_ = v_idx_865_;
goto v___jp_878_;
}
else
{
lean_dec(v_idx_865_);
v___y_879_ = v___x_857_;
goto v___jp_878_;
}
v___jp_869_:
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = l_ByteArray_toByteSlice(v_array_864_, v_lower_870_, v_upper_871_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_872_);
lean_ctor_set(v___x_867_, 0, v_fst_863_);
v___x_874_ = v___x_867_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_fst_863_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
v___jp_878_:
{
uint8_t v___x_880_; 
v___x_880_ = lean_nat_dec_le(v___x_876_, v___x_877_);
if (v___x_880_ == 0)
{
lean_dec(v___x_876_);
v_lower_870_ = v___y_879_;
v_upper_871_ = v___x_877_;
goto v___jp_869_;
}
else
{
v_lower_870_ = v___y_879_;
v_upper_871_ = v___x_876_;
goto v___jp_869_;
}
}
}
}
else
{
lean_object* v_fst_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref(v___x_858_);
lean_dec_ref(v_it_856_);
v_fst_883_ = lean_ctor_get(v_snd_859_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v_snd_859_);
if (v_isSharedCheck_891_ == 0)
{
lean_object* v_unused_892_; 
v_unused_892_ = lean_ctor_get(v_snd_859_, 1);
lean_dec(v_unused_892_);
v___x_885_ = v_snd_859_;
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_fst_883_);
lean_dec(v_snd_859_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = lean_box(0);
if (v_isShared_886_ == 0)
{
lean_ctor_set_tag(v___x_885_, 1);
lean_ctor_set(v___x_885_, 1, v___x_887_);
v___x_889_ = v___x_885_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_fst_883_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo___boxed(lean_object* v_pred_893_, lean_object* v_limit_894_, lean_object* v_it_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(v_pred_893_, v_limit_894_, v_it_895_);
lean_dec(v_limit_894_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(lean_object* v_pred_900_, lean_object* v_limit_901_, lean_object* v_it_902_){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v_snd_905_; lean_object* v_snd_906_; uint8_t v___x_907_; 
v___x_903_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_902_);
v___x_904_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_900_, v_limit_901_, v___x_903_, v_it_902_);
v_snd_905_ = lean_ctor_get(v___x_904_, 1);
lean_inc(v_snd_905_);
v_snd_906_ = lean_ctor_get(v_snd_905_, 1);
v___x_907_ = lean_unbox(v_snd_906_);
if (v___x_907_ == 0)
{
lean_object* v_fst_908_; lean_object* v_fst_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_937_; 
v_fst_908_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_fst_908_);
lean_dec_ref(v___x_904_);
v_fst_909_ = lean_ctor_get(v_snd_905_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v_snd_905_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v_snd_905_, 1);
lean_dec(v_unused_938_);
v___x_911_ = v_snd_905_;
v_isShared_912_ = v_isSharedCheck_937_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_fst_909_);
lean_dec(v_snd_905_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_937_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
uint8_t v___x_913_; 
v___x_913_ = lean_nat_dec_eq(v_fst_908_, v___x_903_);
if (v___x_913_ == 0)
{
lean_object* v_array_914_; lean_object* v_idx_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_932_; 
lean_del_object(v___x_911_);
v_array_914_ = lean_ctor_get(v_it_902_, 0);
v_idx_915_ = lean_ctor_get(v_it_902_, 1);
v_isSharedCheck_932_ = !lean_is_exclusive(v_it_902_);
if (v_isSharedCheck_932_ == 0)
{
v___x_917_ = v_it_902_;
v_isShared_918_ = v_isSharedCheck_932_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_idx_915_);
lean_inc(v_array_914_);
lean_dec(v_it_902_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_932_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v_lower_920_; lean_object* v_upper_921_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___y_929_; uint8_t v___x_931_; 
v___x_926_ = lean_nat_add(v_idx_915_, v_fst_908_);
lean_dec(v_fst_908_);
v___x_927_ = lean_byte_array_size(v_array_914_);
v___x_931_ = lean_nat_dec_le(v_idx_915_, v___x_903_);
if (v___x_931_ == 0)
{
v___y_929_ = v_idx_915_;
goto v___jp_928_;
}
else
{
lean_dec(v_idx_915_);
v___y_929_ = v___x_903_;
goto v___jp_928_;
}
v___jp_919_:
{
lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_922_ = l_ByteArray_toByteSlice(v_array_914_, v_lower_920_, v_upper_921_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 1, v___x_922_);
lean_ctor_set(v___x_917_, 0, v_fst_909_);
v___x_924_ = v___x_917_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_fst_909_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
v___jp_928_:
{
uint8_t v___x_930_; 
v___x_930_ = lean_nat_dec_le(v___x_926_, v___x_927_);
if (v___x_930_ == 0)
{
lean_dec(v___x_926_);
v_lower_920_ = v___y_929_;
v_upper_921_ = v___x_927_;
goto v___jp_919_;
}
else
{
v_lower_920_ = v___y_929_;
v_upper_921_ = v___x_926_;
goto v___jp_919_;
}
}
}
}
else
{
lean_object* v___x_933_; lean_object* v___x_935_; 
lean_dec(v_fst_909_);
lean_dec(v_fst_908_);
v___x_933_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1));
if (v_isShared_912_ == 0)
{
lean_ctor_set_tag(v___x_911_, 1);
lean_ctor_set(v___x_911_, 1, v___x_933_);
lean_ctor_set(v___x_911_, 0, v_it_902_);
v___x_935_ = v___x_911_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_it_902_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
else
{
lean_object* v_fst_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v___x_904_);
lean_dec_ref(v_it_902_);
v_fst_939_ = lean_ctor_get(v_snd_905_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v_snd_905_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; 
v_unused_948_ = lean_ctor_get(v_snd_905_, 1);
lean_dec(v_unused_948_);
v___x_941_ = v_snd_905_;
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_fst_939_);
lean_dec(v_snd_905_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = lean_box(0);
if (v_isShared_942_ == 0)
{
lean_ctor_set_tag(v___x_941_, 1);
lean_ctor_set(v___x_941_, 1, v___x_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_fst_939_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___boxed(lean_object* v_pred_949_, lean_object* v_limit_950_, lean_object* v_it_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(v_pred_949_, v_limit_950_, v_it_951_);
lean_dec(v_limit_950_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(lean_object* v_pred_953_, lean_object* v_limit_954_, lean_object* v_a_955_){
_start:
{
lean_object* v___f_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v_snd_959_; lean_object* v_snd_960_; uint8_t v___x_961_; 
v___f_956_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_956_, 0, v_pred_953_);
v___x_957_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_955_);
v___x_958_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_956_, v_limit_954_, v___x_957_, v_a_955_);
v_snd_959_ = lean_ctor_get(v___x_958_, 1);
lean_inc(v_snd_959_);
v_snd_960_ = lean_ctor_get(v_snd_959_, 1);
v___x_961_ = lean_unbox(v_snd_960_);
if (v___x_961_ == 0)
{
lean_object* v_fst_962_; lean_object* v_fst_963_; lean_object* v_array_964_; lean_object* v_idx_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_982_; 
v_fst_962_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_fst_962_);
lean_dec_ref(v___x_958_);
v_fst_963_ = lean_ctor_get(v_snd_959_, 0);
lean_inc(v_fst_963_);
lean_dec(v_snd_959_);
v_array_964_ = lean_ctor_get(v_a_955_, 0);
v_idx_965_ = lean_ctor_get(v_a_955_, 1);
v_isSharedCheck_982_ = !lean_is_exclusive(v_a_955_);
if (v_isSharedCheck_982_ == 0)
{
v___x_967_ = v_a_955_;
v_isShared_968_ = v_isSharedCheck_982_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_idx_965_);
lean_inc(v_array_964_);
lean_dec(v_a_955_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_982_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v_lower_970_; lean_object* v_upper_971_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___y_979_; uint8_t v___x_981_; 
v___x_976_ = lean_nat_add(v_idx_965_, v_fst_962_);
lean_dec(v_fst_962_);
v___x_977_ = lean_byte_array_size(v_array_964_);
v___x_981_ = lean_nat_dec_le(v_idx_965_, v___x_957_);
if (v___x_981_ == 0)
{
v___y_979_ = v_idx_965_;
goto v___jp_978_;
}
else
{
lean_dec(v_idx_965_);
v___y_979_ = v___x_957_;
goto v___jp_978_;
}
v___jp_969_:
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = l_ByteArray_toByteSlice(v_array_964_, v_lower_970_, v_upper_971_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 1, v___x_972_);
lean_ctor_set(v___x_967_, 0, v_fst_963_);
v___x_974_ = v___x_967_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_fst_963_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
v___jp_978_:
{
uint8_t v___x_980_; 
v___x_980_ = lean_nat_dec_le(v___x_976_, v___x_977_);
if (v___x_980_ == 0)
{
lean_dec(v___x_976_);
v_lower_970_ = v___y_979_;
v_upper_971_ = v___x_977_;
goto v___jp_969_;
}
else
{
v_lower_970_ = v___y_979_;
v_upper_971_ = v___x_976_;
goto v___jp_969_;
}
}
}
}
else
{
lean_object* v_fst_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v___x_958_);
lean_dec_ref(v_a_955_);
v_fst_983_ = lean_ctor_get(v_snd_959_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v_snd_959_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v_snd_959_, 1);
lean_dec(v_unused_992_);
v___x_985_ = v_snd_959_;
v_isShared_986_ = v_isSharedCheck_991_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_fst_983_);
lean_dec(v_snd_959_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_991_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = lean_box(0);
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 1);
lean_ctor_set(v___x_985_, 1, v___x_987_);
v___x_989_ = v___x_985_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_fst_983_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v___x_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo___boxed(lean_object* v_pred_993_, lean_object* v_limit_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(v_pred_993_, v_limit_994_, v_a_995_);
lean_dec(v_limit_994_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileAtMost(lean_object* v_pred_997_, lean_object* v_limit_998_, lean_object* v_it_999_){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_snd_1002_; lean_object* v_fst_1003_; lean_object* v_fst_1004_; lean_object* v_array_1005_; lean_object* v_idx_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1023_; 
v___x_1000_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_999_);
v___x_1001_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_997_, v_limit_998_, v___x_1000_, v_it_999_);
v_snd_1002_ = lean_ctor_get(v___x_1001_, 1);
lean_inc(v_snd_1002_);
v_fst_1003_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_fst_1003_);
lean_dec_ref(v___x_1001_);
v_fst_1004_ = lean_ctor_get(v_snd_1002_, 0);
lean_inc(v_fst_1004_);
lean_dec(v_snd_1002_);
v_array_1005_ = lean_ctor_get(v_it_999_, 0);
v_idx_1006_ = lean_ctor_get(v_it_999_, 1);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_it_999_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1008_ = v_it_999_;
v_isShared_1009_ = v_isSharedCheck_1023_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_idx_1006_);
lean_inc(v_array_1005_);
lean_dec(v_it_999_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1023_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v_lower_1011_; lean_object* v_upper_1012_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___y_1020_; uint8_t v___x_1022_; 
v___x_1017_ = lean_nat_add(v_idx_1006_, v_fst_1003_);
lean_dec(v_fst_1003_);
v___x_1018_ = lean_byte_array_size(v_array_1005_);
v___x_1022_ = lean_nat_dec_le(v_idx_1006_, v___x_1000_);
if (v___x_1022_ == 0)
{
v___y_1020_ = v_idx_1006_;
goto v___jp_1019_;
}
else
{
lean_dec(v_idx_1006_);
v___y_1020_ = v___x_1000_;
goto v___jp_1019_;
}
v___jp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = l_ByteArray_toByteSlice(v_array_1005_, v_lower_1011_, v_upper_1012_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v___x_1013_);
lean_ctor_set(v___x_1008_, 0, v_fst_1004_);
v___x_1015_ = v___x_1008_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_fst_1004_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
v___jp_1019_:
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_nat_dec_le(v___x_1017_, v___x_1018_);
if (v___x_1021_ == 0)
{
lean_dec(v___x_1017_);
v_lower_1011_ = v___y_1020_;
v_upper_1012_ = v___x_1018_;
goto v___jp_1010_;
}
else
{
v_lower_1011_ = v___y_1020_;
v_upper_1012_ = v___x_1017_;
goto v___jp_1010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileAtMost___boxed(lean_object* v_pred_1024_, lean_object* v_limit_1025_, lean_object* v_it_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Std_Internal_Parsec_ByteArray_takeWhileAtMost(v_pred_1024_, v_limit_1025_, v_it_1026_);
lean_dec(v_limit_1025_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost(lean_object* v_pred_1028_, lean_object* v_limit_1029_, lean_object* v_it_1030_){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v_snd_1033_; lean_object* v_fst_1034_; lean_object* v_fst_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1063_; 
v___x_1031_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_1030_);
v___x_1032_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_1028_, v_limit_1029_, v___x_1031_, v_it_1030_);
v_snd_1033_ = lean_ctor_get(v___x_1032_, 1);
lean_inc(v_snd_1033_);
v_fst_1034_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_fst_1034_);
lean_dec_ref(v___x_1032_);
v_fst_1035_ = lean_ctor_get(v_snd_1033_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_snd_1033_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v_snd_1033_, 1);
lean_dec(v_unused_1064_);
v___x_1037_ = v_snd_1033_;
v_isShared_1038_ = v_isSharedCheck_1063_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_fst_1035_);
lean_dec(v_snd_1033_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1063_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
uint8_t v___x_1039_; 
v___x_1039_ = lean_nat_dec_eq(v_fst_1034_, v___x_1031_);
if (v___x_1039_ == 0)
{
lean_object* v_array_1040_; lean_object* v_idx_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1058_; 
lean_del_object(v___x_1037_);
v_array_1040_ = lean_ctor_get(v_it_1030_, 0);
v_idx_1041_ = lean_ctor_get(v_it_1030_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_it_1030_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1043_ = v_it_1030_;
v_isShared_1044_ = v_isSharedCheck_1058_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_idx_1041_);
lean_inc(v_array_1040_);
lean_dec(v_it_1030_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1058_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v_lower_1046_; lean_object* v_upper_1047_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___y_1055_; uint8_t v___x_1057_; 
v___x_1052_ = lean_nat_add(v_idx_1041_, v_fst_1034_);
lean_dec(v_fst_1034_);
v___x_1053_ = lean_byte_array_size(v_array_1040_);
v___x_1057_ = lean_nat_dec_le(v_idx_1041_, v___x_1031_);
if (v___x_1057_ == 0)
{
v___y_1055_ = v_idx_1041_;
goto v___jp_1054_;
}
else
{
lean_dec(v_idx_1041_);
v___y_1055_ = v___x_1031_;
goto v___jp_1054_;
}
v___jp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1048_ = l_ByteArray_toByteSlice(v_array_1040_, v_lower_1046_, v_upper_1047_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 1, v___x_1048_);
lean_ctor_set(v___x_1043_, 0, v_fst_1035_);
v___x_1050_ = v___x_1043_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_fst_1035_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
v___jp_1054_:
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_nat_dec_le(v___x_1052_, v___x_1053_);
if (v___x_1056_ == 0)
{
lean_dec(v___x_1052_);
v_lower_1046_ = v___y_1055_;
v_upper_1047_ = v___x_1053_;
goto v___jp_1045_;
}
else
{
v_lower_1046_ = v___y_1055_;
v_upper_1047_ = v___x_1052_;
goto v___jp_1045_;
}
}
}
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
lean_dec(v_fst_1035_);
lean_dec(v_fst_1034_);
v___x_1059_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1));
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 1);
lean_ctor_set(v___x_1037_, 1, v___x_1059_);
lean_ctor_set(v___x_1037_, 0, v_it_1030_);
v___x_1061_ = v___x_1037_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_it_1030_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost___boxed(lean_object* v_pred_1065_, lean_object* v_limit_1066_, lean_object* v_it_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Std_Internal_Parsec_ByteArray_takeWhile1AtMost(v_pred_1065_, v_limit_1066_, v_it_1067_);
lean_dec(v_limit_1066_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(lean_object* v_pred_1069_, lean_object* v_limit_1070_, lean_object* v_it_1071_){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v_snd_1074_; lean_object* v_snd_1075_; uint8_t v___x_1076_; 
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v_pred_1069_, v_limit_1070_, v___x_1072_, v_it_1071_);
v_snd_1074_ = lean_ctor_get(v___x_1073_, 1);
lean_inc(v_snd_1074_);
lean_dec_ref(v___x_1073_);
v_snd_1075_ = lean_ctor_get(v_snd_1074_, 1);
v___x_1076_ = lean_unbox(v_snd_1075_);
if (v___x_1076_ == 0)
{
lean_object* v_fst_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1085_; 
v_fst_1077_ = lean_ctor_get(v_snd_1074_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_snd_1074_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; 
v_unused_1086_ = lean_ctor_get(v_snd_1074_, 1);
lean_dec(v_unused_1086_);
v___x_1079_ = v_snd_1074_;
v_isShared_1080_ = v_isSharedCheck_1085_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_fst_1077_);
lean_dec(v_snd_1074_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1085_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1081_ = lean_box(0);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v___x_1081_);
v___x_1083_ = v___x_1079_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_fst_1077_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
else
{
lean_object* v_fst_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1095_; 
v_fst_1087_ = lean_ctor_get(v_snd_1074_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_snd_1074_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; 
v_unused_1096_ = lean_ctor_get(v_snd_1074_, 1);
lean_dec(v_unused_1096_);
v___x_1089_ = v_snd_1074_;
v_isShared_1090_ = v_isSharedCheck_1095_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_fst_1087_);
lean_dec(v_snd_1074_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1095_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1091_ = lean_box(0);
if (v_isShared_1090_ == 0)
{
lean_ctor_set_tag(v___x_1089_, 1);
lean_ctor_set(v___x_1089_, 1, v___x_1091_);
v___x_1093_ = v___x_1089_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_fst_1087_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhileUpTo___boxed(lean_object* v_pred_1097_, lean_object* v_limit_1098_, lean_object* v_it_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(v_pred_1097_, v_limit_1098_, v_it_1099_);
lean_dec(v_limit_1098_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(lean_object* v_pred_1101_, lean_object* v_limit_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v___f_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v_snd_1107_; lean_object* v_snd_1108_; uint8_t v___x_1109_; 
v___f_1104_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1104_, 0, v_pred_1101_);
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1104_, v_limit_1102_, v___x_1105_, v_a_1103_);
v_snd_1107_ = lean_ctor_get(v___x_1106_, 1);
lean_inc(v_snd_1107_);
lean_dec_ref(v___x_1106_);
v_snd_1108_ = lean_ctor_get(v_snd_1107_, 1);
v___x_1109_ = lean_unbox(v_snd_1108_);
if (v___x_1109_ == 0)
{
lean_object* v_fst_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1118_; 
v_fst_1110_ = lean_ctor_get(v_snd_1107_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_snd_1107_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; 
v_unused_1119_ = lean_ctor_get(v_snd_1107_, 1);
lean_dec(v_unused_1119_);
v___x_1112_ = v_snd_1107_;
v_isShared_1113_ = v_isSharedCheck_1118_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_fst_1110_);
lean_dec(v_snd_1107_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1118_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1114_ = lean_box(0);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 1, v___x_1114_);
v___x_1116_ = v___x_1112_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_fst_1110_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
else
{
lean_object* v_fst_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1128_; 
v_fst_1120_ = lean_ctor_get(v_snd_1107_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_snd_1107_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v_snd_1107_, 1);
lean_dec(v_unused_1129_);
v___x_1122_ = v_snd_1107_;
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_fst_1120_);
lean_dec(v_snd_1107_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1124_ = lean_box(0);
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 1);
lean_ctor_set(v___x_1122_, 1, v___x_1124_);
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_fst_1120_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntilUpTo___boxed(lean_object* v_pred_1130_, lean_object* v_limit_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(v_pred_1130_, v_limit_1131_, v_a_1132_);
lean_dec(v_limit_1131_);
return v_res_1133_;
}
}
lean_object* runtime_initialize_Std_Internal_Parsec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_ByteSlice(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
