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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
size_t lean_sarray_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_byte_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_ByteArray_toByteSlice(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___at___00Std_Internal_Parsec_ByteArray_skipBytes_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___at___00Std_Internal_Parsec_ByteArray_skipBytes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhile_findEnd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWhile_findEnd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntil(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected at least one char"};
static const lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWhileUpTo_findEnd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWhileUpTo_findEnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pbyte(uint8_t v_b_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_array_108_; lean_object* v_idx_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_array_108_ = lean_ctor_get(v_a_107_, 0);
v_idx_109_ = lean_ctor_get(v_a_107_, 1);
v___x_110_ = lean_byte_array_size(v_array_108_);
v___x_111_ = lean_nat_dec_lt(v_idx_109_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_box(0);
v___x_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_113_, 0, v_a_107_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
return v___x_113_;
}
else
{
uint8_t v_c_114_; uint8_t v___x_115_; 
v_c_114_ = lean_byte_array_fget(v_array_108_, v_idx_109_);
v___x_115_ = lean_uint8_dec_eq(v_c_114_, v_b_106_);
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
lean_ctor_set(v___x_123_, 0, v_a_107_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
return v___x_123_;
}
else
{
lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_134_; 
lean_inc(v_idx_109_);
lean_inc_ref(v_array_108_);
v_isSharedCheck_134_ = !lean_is_exclusive(v_a_107_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; lean_object* v_unused_136_; 
v_unused_135_ = lean_ctor_get(v_a_107_, 1);
lean_dec(v_unused_135_);
v_unused_136_ = lean_ctor_get(v_a_107_, 0);
lean_dec(v_unused_136_);
v___x_125_ = v_a_107_;
v_isShared_126_ = v_isSharedCheck_134_;
goto v_resetjp_124_;
}
else
{
lean_dec(v_a_107_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_134_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v_it_x27_130_; 
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_nat_add(v_idx_109_, v___x_127_);
lean_dec(v_idx_109_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_128_);
v_it_x27_130_ = v___x_125_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_array_108_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_128_);
v_it_x27_130_ = v_reuseFailAlloc_133_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_box(v_b_106_);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v_it_x27_130_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
return v___x_132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pbyte___boxed(lean_object* v_b_137_, lean_object* v_a_138_){
_start:
{
uint8_t v_b_boxed_139_; lean_object* v_res_140_; 
v_b_boxed_139_ = lean_unbox(v_b_137_);
v_res_140_ = l_Std_Internal_Parsec_ByteArray_pbyte(v_b_boxed_139_, v_a_138_);
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
uint8_t v_c_149_; uint8_t v___x_150_; 
v_c_149_ = lean_byte_array_fget(v_array_143_, v_idx_144_);
v___x_150_ = lean_uint8_dec_eq(v_c_149_, v_b_141_);
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
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v_it_x27_165_; 
v___x_162_ = lean_unsigned_to_nat(1u);
v___x_163_ = lean_nat_add(v_idx_144_, v___x_162_);
lean_dec(v_idx_144_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_163_);
v_it_x27_165_ = v___x_160_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_array_143_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___x_163_);
v_it_x27_165_ = v_reuseFailAlloc_168_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_box(0);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v_it_x27_165_);
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
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___at___00Std_Internal_Parsec_ByteArray_skipBytes_spec__0(lean_object* v_as_176_, size_t v_sz_177_, size_t v_i_178_, lean_object* v_b_179_, lean_object* v___y_180_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = lean_usize_dec_lt(v_i_178_, v_sz_177_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___y_180_);
lean_ctor_set(v___x_182_, 1, v_b_179_);
return v___x_182_;
}
else
{
lean_object* v_array_183_; lean_object* v_idx_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_array_183_ = lean_ctor_get(v___y_180_, 0);
v_idx_184_ = lean_ctor_get(v___y_180_, 1);
v___x_185_ = lean_byte_array_size(v_array_183_);
v___x_186_ = lean_nat_dec_lt(v_idx_184_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_box(0);
v___x_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_188_, 0, v___y_180_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
return v___x_188_;
}
else
{
uint8_t v_a_189_; uint8_t v_c_190_; uint8_t v___x_191_; 
v_a_189_ = lean_byte_array_uget(v_as_176_, v_i_178_);
v_c_190_ = lean_byte_array_fget(v_array_183_, v_idx_184_);
v___x_191_ = lean_uint8_dec_eq(v_c_190_, v_a_189_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_192_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0));
v___x_193_ = lean_uint8_to_nat(v_a_189_);
v___x_194_ = l_Nat_reprFast(v___x_193_);
v___x_195_ = lean_string_append(v___x_192_, v___x_194_);
lean_dec_ref(v___x_194_);
v___x_196_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1));
v___x_197_ = lean_string_append(v___x_195_, v___x_196_);
v___x_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
v___x_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_199_, 0, v___y_180_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
return v___x_199_;
}
else
{
lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_212_; 
lean_inc(v_idx_184_);
lean_inc_ref(v_array_183_);
v_isSharedCheck_212_ = !lean_is_exclusive(v___y_180_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; lean_object* v_unused_214_; 
v_unused_213_ = lean_ctor_get(v___y_180_, 1);
lean_dec(v_unused_213_);
v_unused_214_ = lean_ctor_get(v___y_180_, 0);
lean_dec(v_unused_214_);
v___x_201_ = v___y_180_;
v_isShared_202_ = v_isSharedCheck_212_;
goto v_resetjp_200_;
}
else
{
lean_dec(v___y_180_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_212_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v_it_x27_207_; 
v___x_203_ = lean_box(0);
v___x_204_ = lean_unsigned_to_nat(1u);
v___x_205_ = lean_nat_add(v_idx_184_, v___x_204_);
lean_dec(v_idx_184_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 1, v___x_205_);
v_it_x27_207_ = v___x_201_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_array_183_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___x_205_);
v_it_x27_207_ = v_reuseFailAlloc_211_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
size_t v___x_208_; size_t v___x_209_; 
v___x_208_ = ((size_t)1ULL);
v___x_209_ = lean_usize_add(v_i_178_, v___x_208_);
v_i_178_ = v___x_209_;
v_b_179_ = v___x_203_;
v___y_180_ = v_it_x27_207_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___at___00Std_Internal_Parsec_ByteArray_skipBytes_spec__0___boxed(lean_object* v_as_215_, lean_object* v_sz_216_, lean_object* v_i_217_, lean_object* v_b_218_, lean_object* v___y_219_){
_start:
{
size_t v_sz_boxed_220_; size_t v_i_boxed_221_; lean_object* v_res_222_; 
v_sz_boxed_220_ = lean_unbox_usize(v_sz_216_);
lean_dec(v_sz_216_);
v_i_boxed_221_ = lean_unbox_usize(v_i_217_);
lean_dec(v_i_217_);
v_res_222_ = l_ByteArray_forInUnsafe_loop___at___00Std_Internal_Parsec_ByteArray_skipBytes_spec__0(v_as_215_, v_sz_boxed_220_, v_i_boxed_221_, v_b_218_, v___y_219_);
lean_dec_ref(v_as_215_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object* v_arr_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_225_; size_t v_sz_226_; size_t v___x_227_; lean_object* v___x_228_; 
v___x_225_ = lean_box(0);
v_sz_226_ = lean_sarray_size(v_arr_223_);
v___x_227_ = ((size_t)0ULL);
v___x_228_ = l_ByteArray_forInUnsafe_loop___at___00Std_Internal_Parsec_ByteArray_skipBytes_spec__0(v_arr_223_, v_sz_226_, v___x_227_, v___x_225_, v_a_224_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_pos_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
v_pos_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; 
v_unused_237_ = lean_ctor_get(v___x_228_, 1);
lean_dec(v_unused_237_);
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_pos_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 1, v___x_225_);
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_pos_229_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_225_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
else
{
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes___boxed(lean_object* v_arr_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_arr_238_, v_a_239_);
lean_dec_ref(v_arr_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pstring(lean_object* v_s_241_, lean_object* v_a_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_string_to_utf8(v_s_241_);
v___x_244_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_243_, v_a_242_);
lean_dec_ref(v___x_243_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_pos_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
v_pos_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; 
v_unused_253_ = lean_ctor_get(v___x_244_, 1);
lean_dec(v_unused_253_);
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_pos_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 1, v_s_241_);
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_pos_245_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_s_241_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
else
{
lean_object* v_pos_254_; lean_object* v_err_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec_ref(v_s_241_);
v_pos_254_ = lean_ctor_get(v___x_244_, 0);
v_err_255_ = lean_ctor_get(v___x_244_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_244_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_err_255_);
lean_inc(v_pos_254_);
lean_dec(v___x_244_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_pos_254_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_err_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipString(lean_object* v_s_263_, lean_object* v_a_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_string_to_utf8(v_s_263_);
v___x_266_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_265_, v_a_264_);
lean_dec_ref(v___x_265_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_pos_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_275_; 
v_pos_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; 
v_unused_276_ = lean_ctor_get(v___x_266_, 1);
lean_dec(v_unused_276_);
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_275_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_pos_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_275_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_271_ = lean_box(0);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___x_271_);
v___x_273_ = v___x_269_;
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
else
{
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipString___boxed(lean_object* v_s_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_Internal_Parsec_ByteArray_skipString(v_s_277_, v_a_278_);
lean_dec_ref(v_s_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pByteChar(uint32_t v_c_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_array_283_; lean_object* v_idx_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v_array_283_ = lean_ctor_get(v_a_282_, 0);
v_idx_284_ = lean_ctor_get(v_a_282_, 1);
v___x_285_ = lean_byte_array_size(v_array_283_);
v___x_286_ = lean_nat_dec_lt(v_idx_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_box(0);
v___x_288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_288_, 0, v_a_282_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
return v___x_288_;
}
else
{
uint8_t v_c_289_; uint8_t v___x_290_; uint8_t v___x_291_; 
v_c_289_ = lean_byte_array_fget(v_array_283_, v_idx_284_);
v___x_290_ = lean_uint32_to_uint8(v_c_281_);
v___x_291_ = lean_uint8_dec_eq(v_c_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_292_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0));
v___x_293_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0));
v___x_294_ = lean_string_push(v___x_293_, v_c_281_);
v___x_295_ = lean_string_append(v___x_292_, v___x_294_);
lean_dec_ref(v___x_294_);
v___x_296_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1));
v___x_297_ = lean_string_append(v___x_295_, v___x_296_);
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
v___x_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_299_, 0, v_a_282_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
return v___x_299_;
}
else
{
lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_310_; 
lean_inc(v_idx_284_);
lean_inc_ref(v_array_283_);
v_isSharedCheck_310_ = !lean_is_exclusive(v_a_282_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; lean_object* v_unused_312_; 
v_unused_311_ = lean_ctor_get(v_a_282_, 1);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v_a_282_, 0);
lean_dec(v_unused_312_);
v___x_301_ = v_a_282_;
v_isShared_302_ = v_isSharedCheck_310_;
goto v_resetjp_300_;
}
else
{
lean_dec(v_a_282_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_310_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_it_x27_306_; 
v___x_303_ = lean_unsigned_to_nat(1u);
v___x_304_ = lean_nat_add(v_idx_284_, v___x_303_);
lean_dec(v_idx_284_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v___x_304_);
v_it_x27_306_ = v___x_301_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_array_283_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v___x_304_);
v_it_x27_306_ = v_reuseFailAlloc_309_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_box_uint32(v_c_281_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v_it_x27_306_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
return v___x_308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pByteChar___boxed(lean_object* v_c_313_, lean_object* v_a_314_){
_start:
{
uint32_t v_c_boxed_315_; lean_object* v_res_316_; 
v_c_boxed_315_ = lean_unbox_uint32(v_c_313_);
lean_dec(v_c_313_);
v_res_316_ = l_Std_Internal_Parsec_ByteArray_pByteChar(v_c_boxed_315_, v_a_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByteChar(uint32_t v_c_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_array_319_; lean_object* v_idx_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_array_319_ = lean_ctor_get(v_a_318_, 0);
v_idx_320_ = lean_ctor_get(v_a_318_, 1);
v___x_321_ = lean_byte_array_size(v_array_319_);
v___x_322_ = lean_nat_dec_lt(v_idx_320_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_box(0);
v___x_324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_324_, 0, v_a_318_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
return v___x_324_;
}
else
{
uint8_t v___x_325_; uint8_t v_c_326_; uint8_t v___x_327_; 
v___x_325_ = lean_uint32_to_uint8(v_c_317_);
v_c_326_ = lean_byte_array_fget(v_array_319_, v_idx_320_);
v___x_327_ = lean_uint8_dec_eq(v_c_326_, v___x_325_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_328_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0));
v___x_329_ = lean_uint8_to_nat(v___x_325_);
v___x_330_ = l_Nat_reprFast(v___x_329_);
v___x_331_ = lean_string_append(v___x_328_, v___x_330_);
lean_dec_ref(v___x_330_);
v___x_332_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1));
v___x_333_ = lean_string_append(v___x_331_, v___x_332_);
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
v___x_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_335_, 0, v_a_318_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
return v___x_335_;
}
else
{
lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_346_; 
lean_inc(v_idx_320_);
lean_inc_ref(v_array_319_);
v_isSharedCheck_346_ = !lean_is_exclusive(v_a_318_);
if (v_isSharedCheck_346_ == 0)
{
lean_object* v_unused_347_; lean_object* v_unused_348_; 
v_unused_347_ = lean_ctor_get(v_a_318_, 1);
lean_dec(v_unused_347_);
v_unused_348_ = lean_ctor_get(v_a_318_, 0);
lean_dec(v_unused_348_);
v___x_337_ = v_a_318_;
v_isShared_338_ = v_isSharedCheck_346_;
goto v_resetjp_336_;
}
else
{
lean_dec(v_a_318_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_346_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v_it_x27_342_; 
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_nat_add(v_idx_320_, v___x_339_);
lean_dec(v_idx_320_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 1, v___x_340_);
v_it_x27_342_ = v___x_337_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_array_319_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v___x_340_);
v_it_x27_342_ = v_reuseFailAlloc_345_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_box(0);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v_it_x27_342_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
return v___x_344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByteChar___boxed(lean_object* v_c_349_, lean_object* v_a_350_){
_start:
{
uint32_t v_c_boxed_351_; lean_object* v_res_352_; 
v_c_boxed_351_ = lean_unbox_uint32(v_c_349_);
lean_dec(v_c_349_);
v_res_352_ = l_Std_Internal_Parsec_ByteArray_skipByteChar(v_c_boxed_351_, v_a_350_);
return v_res_352_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2(void){
_start:
{
uint32_t v___x_356_; uint8_t v___x_357_; 
v___x_356_ = 48;
v___x_357_ = lean_uint32_to_uint8(v___x_356_);
return v___x_357_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3(void){
_start:
{
uint32_t v___x_358_; uint8_t v___x_359_; 
v___x_358_ = 57;
v___x_359_ = lean_uint32_to_uint8(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digit(lean_object* v_a_360_){
_start:
{
lean_object* v_array_364_; lean_object* v_idx_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v_array_364_ = lean_ctor_get(v_a_360_, 0);
v_idx_365_ = lean_ctor_get(v_a_360_, 1);
v___x_366_ = lean_byte_array_size(v_array_364_);
v___x_367_ = lean_nat_dec_lt(v_idx_365_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_box(0);
v___x_369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_369_, 0, v_a_360_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
return v___x_369_;
}
else
{
uint8_t v_c_370_; uint8_t v___x_371_; uint8_t v___x_372_; 
v_c_370_ = lean_byte_array_fget(v_array_364_, v_idx_365_);
v___x_371_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_372_ = lean_uint8_dec_le(v___x_371_, v_c_370_);
if (v___x_372_ == 0)
{
goto v___jp_361_;
}
else
{
uint8_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__3, &l_Std_Internal_Parsec_ByteArray_digit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3);
v___x_374_ = lean_uint8_dec_le(v_c_370_, v___x_373_);
if (v___x_374_ == 0)
{
goto v___jp_361_;
}
else
{
lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_386_; 
lean_inc(v_idx_365_);
lean_inc_ref(v_array_364_);
v_isSharedCheck_386_ = !lean_is_exclusive(v_a_360_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; lean_object* v_unused_388_; 
v_unused_387_ = lean_ctor_get(v_a_360_, 1);
lean_dec(v_unused_387_);
v_unused_388_ = lean_ctor_get(v_a_360_, 0);
lean_dec(v_unused_388_);
v___x_376_ = v_a_360_;
v_isShared_377_ = v_isSharedCheck_386_;
goto v_resetjp_375_;
}
else
{
lean_dec(v_a_360_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_386_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_it_x27_381_; 
v___x_378_ = lean_unsigned_to_nat(1u);
v___x_379_ = lean_nat_add(v_idx_365_, v___x_378_);
lean_dec(v_idx_365_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 1, v___x_379_);
v_it_x27_381_ = v___x_376_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_array_364_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v___x_379_);
v_it_x27_381_ = v_reuseFailAlloc_385_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
uint32_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_uint8_to_uint32(v_c_370_);
v___x_383_ = lean_box_uint32(v___x_382_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_it_x27_381_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
return v___x_384_;
}
}
}
}
}
v___jp_361_:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_digit___closed__1));
v___x_363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_363_, 0, v_a_360_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(uint8_t v_b_389_){
_start:
{
uint8_t v___x_390_; uint8_t v___x_391_; lean_object* v___x_392_; 
v___x_390_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_391_ = lean_uint8_sub(v_b_389_, v___x_390_);
v___x_392_ = lean_uint8_to_nat(v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat___boxed(lean_object* v_b_393_){
_start:
{
uint8_t v_b_boxed_394_; lean_object* v_res_395_; 
v_b_boxed_394_ = lean_unbox(v_b_393_);
v_res_395_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(v_b_boxed_394_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object* v_it_396_, lean_object* v_acc_397_){
_start:
{
lean_object* v_array_398_; lean_object* v_idx_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_array_398_ = lean_ctor_get(v_it_396_, 0);
v_idx_399_ = lean_ctor_get(v_it_396_, 1);
v___x_400_ = lean_byte_array_size(v_array_398_);
v___x_401_ = lean_nat_dec_lt(v_idx_399_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_acc_397_);
lean_ctor_set(v___x_402_, 1, v_it_396_);
return v___x_402_;
}
else
{
uint8_t v_candidate_403_; uint8_t v___x_404_; uint8_t v___x_405_; 
v_candidate_403_ = lean_byte_array_fget(v_array_398_, v_idx_399_);
v___x_404_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_405_ = lean_uint8_dec_le(v___x_404_, v_candidate_403_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_acc_397_);
lean_ctor_set(v___x_406_, 1, v_it_396_);
return v___x_406_;
}
else
{
uint8_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__3, &l_Std_Internal_Parsec_ByteArray_digit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3);
v___x_408_ = lean_uint8_dec_le(v_candidate_403_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; 
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v_acc_397_);
lean_ctor_set(v___x_409_, 1, v_it_396_);
return v___x_409_;
}
else
{
lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_424_; 
lean_inc(v_idx_399_);
lean_inc_ref(v_array_398_);
v_isSharedCheck_424_ = !lean_is_exclusive(v_it_396_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; lean_object* v_unused_426_; 
v_unused_425_ = lean_ctor_get(v_it_396_, 1);
lean_dec(v_unused_425_);
v_unused_426_ = lean_ctor_get(v_it_396_, 0);
lean_dec(v_unused_426_);
v___x_411_ = v_it_396_;
v_isShared_412_ = v_isSharedCheck_424_;
goto v_resetjp_410_;
}
else
{
lean_dec(v_it_396_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_424_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
uint8_t v___x_413_; lean_object* v_digit_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v_acc_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_413_ = lean_uint8_sub(v_candidate_403_, v___x_404_);
v_digit_414_ = lean_uint8_to_nat(v___x_413_);
v___x_415_ = lean_unsigned_to_nat(10u);
v___x_416_ = lean_nat_mul(v_acc_397_, v___x_415_);
lean_dec(v_acc_397_);
v_acc_417_ = lean_nat_add(v___x_416_, v_digit_414_);
lean_dec(v___x_416_);
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = lean_nat_add(v_idx_399_, v___x_418_);
lean_dec(v_idx_399_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v___x_419_);
v___x_421_ = v___x_411_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_array_398_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___x_419_);
v___x_421_ = v_reuseFailAlloc_423_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
v_it_396_ = v___x_421_;
v_acc_397_ = v_acc_417_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore(lean_object* v_acc_427_, lean_object* v_it_428_){
_start:
{
lean_object* v___x_429_; lean_object* v_fst_430_; lean_object* v_snd_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
v___x_429_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_428_, v_acc_427_);
v_fst_430_ = lean_ctor_get(v___x_429_, 0);
v_snd_431_ = lean_ctor_get(v___x_429_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_429_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_snd_431_);
lean_inc(v_fst_430_);
lean_dec(v___x_429_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v_fst_430_);
lean_ctor_set(v___x_433_, 0, v_snd_431_);
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_snd_431_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_fst_430_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digits(lean_object* v_a_439_){
_start:
{
lean_object* v_array_443_; lean_object* v_idx_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v_array_443_ = lean_ctor_get(v_a_439_, 0);
v_idx_444_ = lean_ctor_get(v_a_439_, 1);
v___x_445_ = lean_byte_array_size(v_array_443_);
v___x_446_ = lean_nat_dec_lt(v_idx_444_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_box(0);
v___x_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_448_, 0, v_a_439_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
return v___x_448_;
}
else
{
uint8_t v_c_449_; uint8_t v___x_450_; uint8_t v___x_451_; 
v_c_449_ = lean_byte_array_fget(v_array_443_, v_idx_444_);
v___x_450_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_451_ = lean_uint8_dec_le(v___x_450_, v_c_449_);
if (v___x_451_ == 0)
{
goto v___jp_440_;
}
else
{
uint8_t v___x_452_; uint8_t v___x_453_; 
v___x_452_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__3, &l_Std_Internal_Parsec_ByteArray_digit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3);
v___x_453_ = lean_uint8_dec_le(v_c_449_, v___x_452_);
if (v___x_453_ == 0)
{
goto v___jp_440_;
}
else
{
lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_476_; 
lean_inc(v_idx_444_);
lean_inc_ref(v_array_443_);
v_isSharedCheck_476_ = !lean_is_exclusive(v_a_439_);
if (v_isSharedCheck_476_ == 0)
{
lean_object* v_unused_477_; lean_object* v_unused_478_; 
v_unused_477_ = lean_ctor_get(v_a_439_, 1);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_a_439_, 0);
lean_dec(v_unused_478_);
v___x_455_ = v_a_439_;
v_isShared_456_ = v_isSharedCheck_476_;
goto v_resetjp_454_;
}
else
{
lean_dec(v_a_439_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_476_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v_it_x27_460_; 
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_add(v_idx_444_, v___x_457_);
lean_dec(v_idx_444_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_458_);
v_it_x27_460_ = v___x_455_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_array_443_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_458_);
v_it_x27_460_ = v_reuseFailAlloc_475_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
uint32_t v___x_461_; uint8_t v___x_462_; uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v_fst_466_; lean_object* v_snd_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
v___x_461_ = lean_uint8_to_uint32(v_c_449_);
v___x_462_ = lean_uint32_to_uint8(v___x_461_);
v___x_463_ = lean_uint8_sub(v___x_462_, v___x_450_);
v___x_464_ = lean_uint8_to_nat(v___x_463_);
v___x_465_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_460_, v___x_464_);
v_fst_466_ = lean_ctor_get(v___x_465_, 0);
v_snd_467_ = lean_ctor_get(v___x_465_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_465_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_snd_467_);
lean_inc(v_fst_466_);
lean_dec(v___x_465_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 1, v_fst_466_);
lean_ctor_set(v___x_469_, 0, v_snd_467_);
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_snd_467_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_fst_466_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
}
}
v___jp_440_:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_digit___closed__1));
v___x_442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_442_, 0, v_a_439_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
return v___x_442_;
}
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2(void){
_start:
{
uint32_t v___x_482_; uint8_t v___x_483_; 
v___x_482_ = 65;
v___x_483_ = lean_uint32_to_uint8(v___x_482_);
return v___x_483_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3(void){
_start:
{
uint32_t v___x_484_; uint8_t v___x_485_; 
v___x_484_ = 70;
v___x_485_ = lean_uint32_to_uint8(v___x_484_);
return v___x_485_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4(void){
_start:
{
uint32_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = 97;
v___x_487_ = lean_uint32_to_uint8(v___x_486_);
return v___x_487_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5(void){
_start:
{
uint32_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = 102;
v___x_489_ = lean_uint32_to_uint8(v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_hexDigit(lean_object* v_a_490_){
_start:
{
lean_object* v_array_494_; lean_object* v_idx_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_array_494_ = lean_ctor_get(v_a_490_, 0);
v_idx_495_ = lean_ctor_get(v_a_490_, 1);
v___x_496_ = lean_byte_array_size(v_array_494_);
v___x_497_ = lean_nat_dec_lt(v_idx_495_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_box(0);
v___x_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_499_, 0, v_a_490_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
return v___x_499_;
}
else
{
uint8_t v_c_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_it_x27_503_; uint8_t v___x_518_; uint8_t v___x_519_; 
v_c_500_ = lean_byte_array_fget(v_array_494_, v_idx_495_);
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_add(v_idx_495_, v___x_501_);
lean_inc_ref(v_array_494_);
v_it_x27_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_503_, 0, v_array_494_);
lean_ctor_set(v_it_x27_503_, 1, v___x_502_);
v___x_518_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_519_ = lean_uint8_dec_le(v___x_518_, v_c_500_);
if (v___x_519_ == 0)
{
goto v___jp_513_;
}
else
{
uint8_t v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__3, &l_Std_Internal_Parsec_ByteArray_digit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__3);
v___x_521_ = lean_uint8_dec_le(v_c_500_, v___x_520_);
if (v___x_521_ == 0)
{
goto v___jp_513_;
}
else
{
lean_dec_ref(v_a_490_);
goto v___jp_504_;
}
}
v___jp_504_:
{
uint32_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = lean_uint8_to_uint32(v_c_500_);
v___x_506_ = lean_box_uint32(v___x_505_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v_it_x27_503_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
return v___x_507_;
}
v___jp_508_:
{
uint8_t v___x_509_; uint8_t v___x_510_; 
v___x_509_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2);
v___x_510_ = lean_uint8_dec_le(v___x_509_, v_c_500_);
if (v___x_510_ == 0)
{
lean_dec_ref(v_it_x27_503_);
goto v___jp_491_;
}
else
{
uint8_t v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3);
v___x_512_ = lean_uint8_dec_le(v_c_500_, v___x_511_);
if (v___x_512_ == 0)
{
lean_dec_ref(v_it_x27_503_);
goto v___jp_491_;
}
else
{
lean_dec_ref(v_a_490_);
goto v___jp_504_;
}
}
}
v___jp_513_:
{
uint8_t v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4);
v___x_515_ = lean_uint8_dec_le(v___x_514_, v_c_500_);
if (v___x_515_ == 0)
{
goto v___jp_508_;
}
else
{
uint8_t v___x_516_; uint8_t v___x_517_; 
v___x_516_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__5);
v___x_517_ = lean_uint8_dec_le(v_c_500_, v___x_516_);
if (v___x_517_ == 0)
{
goto v___jp_508_;
}
else
{
lean_dec_ref(v_a_490_);
goto v___jp_504_;
}
}
}
}
v___jp_491_:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1));
v___x_493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_493_, 0, v_a_490_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
return v___x_493_;
}
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_octDigit___closed__2(void){
_start:
{
uint32_t v___x_525_; uint8_t v___x_526_; 
v___x_525_ = 55;
v___x_526_ = lean_uint32_to_uint8(v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_octDigit(lean_object* v_a_527_){
_start:
{
lean_object* v_array_531_; lean_object* v_idx_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_array_531_ = lean_ctor_get(v_a_527_, 0);
v_idx_532_ = lean_ctor_get(v_a_527_, 1);
v___x_533_ = lean_byte_array_size(v_array_531_);
v___x_534_ = lean_nat_dec_lt(v_idx_532_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_box(0);
v___x_536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_536_, 0, v_a_527_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
return v___x_536_;
}
else
{
uint8_t v_c_537_; uint8_t v___x_538_; uint8_t v___x_539_; 
v_c_537_ = lean_byte_array_fget(v_array_531_, v_idx_532_);
v___x_538_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_digit___closed__2, &l_Std_Internal_Parsec_ByteArray_digit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2);
v___x_539_ = lean_uint8_dec_le(v___x_538_, v_c_537_);
if (v___x_539_ == 0)
{
goto v___jp_528_;
}
else
{
uint8_t v___x_540_; uint8_t v___x_541_; 
v___x_540_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_octDigit___closed__2, &l_Std_Internal_Parsec_ByteArray_octDigit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_octDigit___closed__2);
v___x_541_ = lean_uint8_dec_le(v_c_537_, v___x_540_);
if (v___x_541_ == 0)
{
goto v___jp_528_;
}
else
{
lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_553_; 
lean_inc(v_idx_532_);
lean_inc_ref(v_array_531_);
v_isSharedCheck_553_ = !lean_is_exclusive(v_a_527_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; lean_object* v_unused_555_; 
v_unused_554_ = lean_ctor_get(v_a_527_, 1);
lean_dec(v_unused_554_);
v_unused_555_ = lean_ctor_get(v_a_527_, 0);
lean_dec(v_unused_555_);
v___x_543_ = v_a_527_;
v_isShared_544_ = v_isSharedCheck_553_;
goto v_resetjp_542_;
}
else
{
lean_dec(v_a_527_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_553_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_it_x27_548_; 
v___x_545_ = lean_unsigned_to_nat(1u);
v___x_546_ = lean_nat_add(v_idx_532_, v___x_545_);
lean_dec(v_idx_532_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 1, v___x_546_);
v_it_x27_548_ = v___x_543_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_array_531_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___x_546_);
v_it_x27_548_ = v_reuseFailAlloc_552_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
uint32_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_549_ = lean_uint8_to_uint32(v_c_537_);
v___x_550_ = lean_box_uint32(v___x_549_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v_it_x27_548_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
return v___x_551_;
}
}
}
}
}
v___jp_528_:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_octDigit___closed__1));
v___x_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_530_, 0, v_a_527_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
return v___x_530_;
}
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2(void){
_start:
{
uint32_t v___x_559_; uint8_t v___x_560_; 
v___x_559_ = 122;
v___x_560_ = lean_uint32_to_uint8(v___x_559_);
return v___x_560_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3(void){
_start:
{
uint32_t v___x_561_; uint8_t v___x_562_; 
v___x_561_ = 90;
v___x_562_ = lean_uint32_to_uint8(v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_asciiLetter(lean_object* v_a_563_){
_start:
{
lean_object* v_array_567_; lean_object* v_idx_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_array_567_ = lean_ctor_get(v_a_563_, 0);
v_idx_568_ = lean_ctor_get(v_a_563_, 1);
v___x_569_ = lean_byte_array_size(v_array_567_);
v___x_570_ = lean_nat_dec_lt(v_idx_568_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_box(0);
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v_a_563_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
return v___x_572_;
}
else
{
uint8_t v_c_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v_it_x27_576_; uint8_t v___x_586_; uint8_t v___x_587_; 
v_c_573_ = lean_byte_array_fget(v_array_567_, v_idx_568_);
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = lean_nat_add(v_idx_568_, v___x_574_);
lean_inc_ref(v_array_567_);
v_it_x27_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_576_, 0, v_array_567_);
lean_ctor_set(v_it_x27_576_, 1, v___x_575_);
v___x_586_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2);
v___x_587_ = lean_uint8_dec_le(v___x_586_, v_c_573_);
if (v___x_587_ == 0)
{
goto v___jp_581_;
}
else
{
uint8_t v___x_588_; uint8_t v___x_589_; 
v___x_588_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3, &l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3_once, _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__3);
v___x_589_ = lean_uint8_dec_le(v_c_573_, v___x_588_);
if (v___x_589_ == 0)
{
goto v___jp_581_;
}
else
{
lean_dec_ref(v_a_563_);
goto v___jp_577_;
}
}
v___jp_577_:
{
uint32_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_uint8_to_uint32(v_c_573_);
v___x_579_ = lean_box_uint32(v___x_578_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_it_x27_576_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
return v___x_580_;
}
v___jp_581_:
{
uint8_t v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4, &l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4_once, _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4);
v___x_583_ = lean_uint8_dec_le(v___x_582_, v_c_573_);
if (v___x_583_ == 0)
{
lean_dec_ref(v_it_x27_576_);
goto v___jp_564_;
}
else
{
uint8_t v___x_584_; uint8_t v___x_585_; 
v___x_584_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2, &l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2_once, _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2);
v___x_585_ = lean_uint8_dec_le(v_c_573_, v___x_584_);
if (v___x_585_ == 0)
{
lean_dec_ref(v_it_x27_576_);
goto v___jp_564_;
}
else
{
lean_dec_ref(v_a_563_);
goto v___jp_577_;
}
}
}
}
v___jp_564_:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1));
v___x_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_566_, 0, v_a_563_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
return v___x_566_;
}
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0(void){
_start:
{
uint32_t v___x_590_; uint8_t v___x_591_; 
v___x_590_ = 9;
v___x_591_ = lean_uint32_to_uint8(v___x_590_);
return v___x_591_;
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1(void){
_start:
{
uint32_t v___x_592_; uint8_t v___x_593_; 
v___x_592_ = 10;
v___x_593_ = lean_uint32_to_uint8(v___x_592_);
return v___x_593_;
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2(void){
_start:
{
uint32_t v___x_594_; uint8_t v___x_595_; 
v___x_594_ = 13;
v___x_595_ = lean_uint32_to_uint8(v___x_594_);
return v___x_595_;
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3(void){
_start:
{
uint32_t v___x_596_; uint8_t v___x_597_; 
v___x_596_ = 32;
v___x_597_ = lean_uint32_to_uint8(v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(lean_object* v_it_598_){
_start:
{
lean_object* v_array_599_; lean_object* v_idx_600_; lean_object* v___x_606_; uint8_t v___x_607_; 
v_array_599_ = lean_ctor_get(v_it_598_, 0);
v_idx_600_ = lean_ctor_get(v_it_598_, 1);
v___x_606_ = lean_byte_array_size(v_array_599_);
v___x_607_ = lean_nat_dec_lt(v_idx_600_, v___x_606_);
if (v___x_607_ == 0)
{
return v_it_598_;
}
else
{
uint8_t v_b_608_; uint8_t v___x_609_; uint8_t v___x_610_; 
v_b_608_ = lean_byte_array_fget(v_array_599_, v_idx_600_);
v___x_609_ = lean_uint8_once(&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0, &l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0_once, _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0);
v___x_610_ = lean_uint8_dec_eq(v_b_608_, v___x_609_);
if (v___x_610_ == 0)
{
uint8_t v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_uint8_once(&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1, &l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1_once, _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1);
v___x_612_ = lean_uint8_dec_eq(v_b_608_, v___x_611_);
if (v___x_612_ == 0)
{
uint8_t v___x_613_; uint8_t v___x_614_; 
v___x_613_ = lean_uint8_once(&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2, &l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2_once, _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2);
v___x_614_ = lean_uint8_dec_eq(v_b_608_, v___x_613_);
if (v___x_614_ == 0)
{
uint8_t v___x_615_; uint8_t v___x_616_; 
v___x_615_ = lean_uint8_once(&l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3, &l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3_once, _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3);
v___x_616_ = lean_uint8_dec_eq(v_b_608_, v___x_615_);
if (v___x_616_ == 0)
{
return v_it_598_;
}
else
{
lean_inc(v_idx_600_);
lean_inc_ref(v_array_599_);
lean_dec_ref(v_it_598_);
goto v___jp_601_;
}
}
else
{
lean_inc(v_idx_600_);
lean_inc_ref(v_array_599_);
lean_dec_ref(v_it_598_);
goto v___jp_601_;
}
}
else
{
lean_inc(v_idx_600_);
lean_inc_ref(v_array_599_);
lean_dec_ref(v_it_598_);
goto v___jp_601_;
}
}
else
{
lean_inc(v_idx_600_);
lean_inc_ref(v_array_599_);
lean_dec_ref(v_it_598_);
goto v___jp_601_;
}
}
v___jp_601_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_nat_add(v_idx_600_, v___x_602_);
lean_dec(v_idx_600_);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v_array_599_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v_it_598_ = v___x_604_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_ws(lean_object* v_it_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(v_it_617_);
v___x_619_ = lean_box(0);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take(lean_object* v_n_621_, lean_object* v_it_622_){
_start:
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = l_ByteArray_Iterator_remainingBytes(v_it_622_);
v___x_624_ = lean_nat_dec_lt(v___x_623_, v_n_621_);
lean_dec(v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v_array_625_; lean_object* v_idx_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_645_; 
v_array_625_ = lean_ctor_get(v_it_622_, 0);
v_idx_626_ = lean_ctor_get(v_it_622_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_it_622_);
if (v_isSharedCheck_645_ == 0)
{
v___x_628_ = v_it_622_;
v_isShared_629_ = v_isSharedCheck_645_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_idx_626_);
lean_inc(v_array_625_);
lean_dec(v_it_622_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_645_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = lean_nat_add(v_idx_626_, v_n_621_);
lean_inc(v___x_630_);
lean_inc_ref(v_array_625_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v___x_630_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_array_625_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_630_);
v___x_632_ = v_reuseFailAlloc_644_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v_lower_634_; lean_object* v_upper_635_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___y_641_; uint8_t v___x_643_; 
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = lean_byte_array_size(v_array_625_);
v___x_643_ = lean_nat_dec_le(v_idx_626_, v___x_638_);
if (v___x_643_ == 0)
{
v___y_641_ = v_idx_626_;
goto v___jp_640_;
}
else
{
lean_dec(v_idx_626_);
v___y_641_ = v___x_638_;
goto v___jp_640_;
}
v___jp_633_:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = l_ByteArray_toByteSlice(v_array_625_, v_lower_634_, v_upper_635_);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_632_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
return v___x_637_;
}
v___jp_640_:
{
uint8_t v___x_642_; 
v___x_642_ = lean_nat_dec_le(v___x_630_, v___x_639_);
if (v___x_642_ == 0)
{
lean_dec(v___x_630_);
v_lower_634_ = v___y_641_;
v_upper_635_ = v___x_639_;
goto v___jp_633_;
}
else
{
v_lower_634_ = v___y_641_;
v_upper_635_ = v___x_630_;
goto v___jp_633_;
}
}
}
}
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_box(0);
v___x_647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_647_, 0, v_it_622_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take___boxed(lean_object* v_n_648_, lean_object* v_it_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Std_Internal_Parsec_ByteArray_take(v_n_648_, v_it_649_);
lean_dec(v_n_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhile_findEnd(lean_object* v_pred_651_, lean_object* v_count_652_, lean_object* v_iter_653_){
_start:
{
lean_object* v_array_654_; lean_object* v_idx_655_; uint8_t v___y_657_; lean_object* v___x_675_; uint8_t v___x_676_; 
v_array_654_ = lean_ctor_get(v_iter_653_, 0);
v_idx_655_ = lean_ctor_get(v_iter_653_, 1);
v___x_675_ = lean_byte_array_size(v_array_654_);
v___x_676_ = lean_nat_dec_lt(v_idx_655_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
lean_dec_ref(v_pred_651_);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v_count_652_);
lean_ctor_set(v___x_677_, 1, v_iter_653_);
return v___x_677_;
}
else
{
if (v___x_676_ == 0)
{
uint8_t v___x_678_; 
v___x_678_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0, &l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0_once, _init_l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0);
v___y_657_ = v___x_678_;
goto v___jp_656_;
}
else
{
uint8_t v___x_679_; 
v___x_679_ = lean_byte_array_fget(v_array_654_, v_idx_655_);
v___y_657_ = v___x_679_;
goto v___jp_656_;
}
}
v___jp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_box(v___y_657_);
lean_inc_ref(v_pred_651_);
v___x_659_ = lean_apply_1(v_pred_651_, v___x_658_);
v___x_660_ = lean_unbox(v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
lean_dec_ref(v_pred_651_);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v_count_652_);
lean_ctor_set(v___x_661_, 1, v_iter_653_);
return v___x_661_;
}
else
{
lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_672_; 
lean_inc(v_idx_655_);
lean_inc_ref(v_array_654_);
v_isSharedCheck_672_ = !lean_is_exclusive(v_iter_653_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; lean_object* v_unused_674_; 
v_unused_673_ = lean_ctor_get(v_iter_653_, 1);
lean_dec(v_unused_673_);
v_unused_674_ = lean_ctor_get(v_iter_653_, 0);
lean_dec(v_unused_674_);
v___x_663_ = v_iter_653_;
v_isShared_664_ = v_isSharedCheck_672_;
goto v_resetjp_662_;
}
else
{
lean_dec(v_iter_653_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_672_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = lean_nat_add(v_count_652_, v___x_665_);
lean_dec(v_count_652_);
v___x_667_ = lean_nat_add(v_idx_655_, v___x_665_);
lean_dec(v_idx_655_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_667_);
v___x_669_ = v___x_663_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_array_654_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v___x_667_);
v___x_669_ = v_reuseFailAlloc_671_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
v_count_652_ = v___x_666_;
v_iter_653_ = v___x_669_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhile(lean_object* v_pred_680_, lean_object* v_it_681_){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v_fst_684_; lean_object* v_snd_685_; lean_object* v_array_686_; lean_object* v_idx_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_704_; 
v___x_682_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_681_);
v___x_683_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhile_findEnd(v_pred_680_, v___x_682_, v_it_681_);
v_fst_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_fst_684_);
v_snd_685_ = lean_ctor_get(v___x_683_, 1);
lean_inc(v_snd_685_);
lean_dec_ref(v___x_683_);
v_array_686_ = lean_ctor_get(v_it_681_, 0);
v_idx_687_ = lean_ctor_get(v_it_681_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_it_681_);
if (v_isSharedCheck_704_ == 0)
{
v___x_689_ = v_it_681_;
v_isShared_690_ = v_isSharedCheck_704_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_idx_687_);
lean_inc(v_array_686_);
lean_dec(v_it_681_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_704_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_lower_692_; lean_object* v_upper_693_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___y_701_; uint8_t v___x_703_; 
v___x_698_ = lean_nat_add(v_idx_687_, v_fst_684_);
lean_dec(v_fst_684_);
v___x_699_ = lean_byte_array_size(v_array_686_);
v___x_703_ = lean_nat_dec_le(v_idx_687_, v___x_682_);
if (v___x_703_ == 0)
{
v___y_701_ = v_idx_687_;
goto v___jp_700_;
}
else
{
lean_dec(v_idx_687_);
v___y_701_ = v___x_682_;
goto v___jp_700_;
}
v___jp_691_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = l_ByteArray_toByteSlice(v_array_686_, v_lower_692_, v_upper_693_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_694_);
lean_ctor_set(v___x_689_, 0, v_snd_685_);
v___x_696_ = v___x_689_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_snd_685_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
v___jp_700_:
{
uint8_t v___x_702_; 
v___x_702_ = lean_nat_dec_le(v___x_698_, v___x_699_);
if (v___x_702_ == 0)
{
lean_dec(v___x_698_);
v_lower_692_ = v___y_701_;
v_upper_693_ = v___x_699_;
goto v___jp_691_;
}
else
{
v_lower_692_ = v___y_701_;
v_upper_693_ = v___x_698_;
goto v___jp_691_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(lean_object* v_pred_705_, uint8_t v_b_706_){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_707_ = lean_box(v_b_706_);
v___x_708_ = lean_apply_1(v_pred_705_, v___x_707_);
v___x_709_ = lean_unbox(v___x_708_);
if (v___x_709_ == 0)
{
uint8_t v___x_710_; 
v___x_710_ = 1;
return v___x_710_;
}
else
{
uint8_t v___x_711_; 
v___x_711_ = 0;
return v___x_711_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed(lean_object* v_pred_712_, lean_object* v_b_713_){
_start:
{
uint8_t v_b_boxed_714_; uint8_t v_res_715_; lean_object* v_r_716_; 
v_b_boxed_714_ = lean_unbox(v_b_713_);
v_res_715_ = l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0(v_pred_712_, v_b_boxed_714_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntil(lean_object* v_pred_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___f_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_fst_722_; lean_object* v_snd_723_; lean_object* v_array_724_; lean_object* v_idx_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_742_; 
v___f_719_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_719_, 0, v_pred_717_);
v___x_720_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_718_);
v___x_721_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhile_findEnd(v___f_719_, v___x_720_, v_a_718_);
v_fst_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_fst_722_);
v_snd_723_ = lean_ctor_get(v___x_721_, 1);
lean_inc(v_snd_723_);
lean_dec_ref(v___x_721_);
v_array_724_ = lean_ctor_get(v_a_718_, 0);
v_idx_725_ = lean_ctor_get(v_a_718_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_a_718_);
if (v_isSharedCheck_742_ == 0)
{
v___x_727_ = v_a_718_;
v_isShared_728_ = v_isSharedCheck_742_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_idx_725_);
lean_inc(v_array_724_);
lean_dec(v_a_718_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_742_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_lower_730_; lean_object* v_upper_731_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___y_739_; uint8_t v___x_741_; 
v___x_736_ = lean_nat_add(v_idx_725_, v_fst_722_);
lean_dec(v_fst_722_);
v___x_737_ = lean_byte_array_size(v_array_724_);
v___x_741_ = lean_nat_dec_le(v_idx_725_, v___x_720_);
if (v___x_741_ == 0)
{
v___y_739_ = v_idx_725_;
goto v___jp_738_;
}
else
{
lean_dec(v_idx_725_);
v___y_739_ = v___x_720_;
goto v___jp_738_;
}
v___jp_729_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_732_ = l_ByteArray_toByteSlice(v_array_724_, v_lower_730_, v_upper_731_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v___x_732_);
lean_ctor_set(v___x_727_, 0, v_snd_723_);
v___x_734_ = v___x_727_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_snd_723_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
v___jp_738_:
{
uint8_t v___x_740_; 
v___x_740_ = lean_nat_dec_le(v___x_736_, v___x_737_);
if (v___x_740_ == 0)
{
lean_dec(v___x_736_);
v_lower_730_ = v___y_739_;
v_upper_731_ = v___x_737_;
goto v___jp_729_;
}
else
{
v_lower_730_ = v___y_739_;
v_upper_731_ = v___x_736_;
goto v___jp_729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWhile_findEnd(lean_object* v_pred_743_, lean_object* v_count_744_, lean_object* v_iter_745_){
_start:
{
lean_object* v_array_746_; lean_object* v_idx_747_; uint8_t v___y_749_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_array_746_ = lean_ctor_get(v_iter_745_, 0);
v_idx_747_ = lean_ctor_get(v_iter_745_, 1);
v___x_766_ = lean_byte_array_size(v_array_746_);
v___x_767_ = lean_nat_dec_lt(v_idx_747_, v___x_766_);
if (v___x_767_ == 0)
{
lean_dec(v_count_744_);
lean_dec_ref(v_pred_743_);
return v_iter_745_;
}
else
{
if (v___x_767_ == 0)
{
uint8_t v___x_768_; 
v___x_768_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0, &l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0_once, _init_l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0);
v___y_749_ = v___x_768_;
goto v___jp_748_;
}
else
{
uint8_t v___x_769_; 
v___x_769_ = lean_byte_array_fget(v_array_746_, v_idx_747_);
v___y_749_ = v___x_769_;
goto v___jp_748_;
}
}
v___jp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_750_ = lean_box(v___y_749_);
lean_inc_ref(v_pred_743_);
v___x_751_ = lean_apply_1(v_pred_743_, v___x_750_);
v___x_752_ = lean_unbox(v___x_751_);
if (v___x_752_ == 0)
{
lean_dec(v_count_744_);
lean_dec_ref(v_pred_743_);
return v_iter_745_;
}
else
{
lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_763_; 
lean_inc(v_idx_747_);
lean_inc_ref(v_array_746_);
v_isSharedCheck_763_ = !lean_is_exclusive(v_iter_745_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; lean_object* v_unused_765_; 
v_unused_764_ = lean_ctor_get(v_iter_745_, 1);
lean_dec(v_unused_764_);
v_unused_765_ = lean_ctor_get(v_iter_745_, 0);
lean_dec(v_unused_765_);
v___x_754_ = v_iter_745_;
v_isShared_755_ = v_isSharedCheck_763_;
goto v_resetjp_753_;
}
else
{
lean_dec(v_iter_745_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_763_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_756_ = lean_unsigned_to_nat(1u);
v___x_757_ = lean_nat_add(v_count_744_, v___x_756_);
lean_dec(v_count_744_);
v___x_758_ = lean_nat_add(v_idx_747_, v___x_756_);
lean_dec(v_idx_747_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v___x_758_);
v___x_760_ = v___x_754_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_array_746_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___x_758_);
v___x_760_ = v_reuseFailAlloc_762_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
v_count_744_ = v___x_757_;
v_iter_745_ = v___x_760_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhile(lean_object* v_pred_770_, lean_object* v_it_771_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWhile_findEnd(v_pred_770_, v___x_772_, v_it_771_);
v___x_774_ = lean_box(0);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_773_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntil(lean_object* v_pred_776_, lean_object* v_a_777_){
_start:
{
lean_object* v___f_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___f_778_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_778_, 0, v_pred_776_);
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWhile_findEnd(v___f_778_, v___x_779_, v_a_777_);
v___x_781_ = lean_box(0);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(lean_object* v_pred_783_, lean_object* v_limit_784_, lean_object* v_count_785_, lean_object* v_iter_786_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = lean_nat_dec_le(v_limit_784_, v_count_785_);
if (v___x_787_ == 0)
{
lean_object* v_array_788_; lean_object* v_idx_789_; uint8_t v___y_791_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_array_788_ = lean_ctor_get(v_iter_786_, 0);
v_idx_789_ = lean_ctor_get(v_iter_786_, 1);
v___x_809_ = lean_byte_array_size(v_array_788_);
v___x_810_ = lean_nat_dec_lt(v_idx_789_, v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; 
lean_dec_ref(v_pred_783_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v_count_785_);
lean_ctor_set(v___x_811_, 1, v_iter_786_);
return v___x_811_;
}
else
{
if (v___x_787_ == 0)
{
if (v___x_810_ == 0)
{
uint8_t v___x_812_; 
v___x_812_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0, &l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0_once, _init_l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0);
v___y_791_ = v___x_812_;
goto v___jp_790_;
}
else
{
uint8_t v___x_813_; 
v___x_813_ = lean_byte_array_fget(v_array_788_, v_idx_789_);
v___y_791_ = v___x_813_;
goto v___jp_790_;
}
}
else
{
lean_object* v___x_814_; 
lean_dec_ref(v_pred_783_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v_count_785_);
lean_ctor_set(v___x_814_, 1, v_iter_786_);
return v___x_814_;
}
}
v___jp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_792_ = lean_box(v___y_791_);
lean_inc_ref(v_pred_783_);
v___x_793_ = lean_apply_1(v_pred_783_, v___x_792_);
v___x_794_ = lean_unbox(v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
lean_dec_ref(v_pred_783_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v_count_785_);
lean_ctor_set(v___x_795_, 1, v_iter_786_);
return v___x_795_;
}
else
{
lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_806_; 
lean_inc(v_idx_789_);
lean_inc_ref(v_array_788_);
v_isSharedCheck_806_ = !lean_is_exclusive(v_iter_786_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; lean_object* v_unused_808_; 
v_unused_807_ = lean_ctor_get(v_iter_786_, 1);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_iter_786_, 0);
lean_dec(v_unused_808_);
v___x_797_ = v_iter_786_;
v_isShared_798_ = v_isSharedCheck_806_;
goto v_resetjp_796_;
}
else
{
lean_dec(v_iter_786_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_806_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_799_ = lean_unsigned_to_nat(1u);
v___x_800_ = lean_nat_add(v_count_785_, v___x_799_);
lean_dec(v_count_785_);
v___x_801_ = lean_nat_add(v_idx_789_, v___x_799_);
lean_dec(v_idx_789_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v___x_801_);
v___x_803_ = v___x_797_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_array_788_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_801_);
v___x_803_ = v_reuseFailAlloc_805_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
v_count_785_ = v___x_800_;
v_iter_786_ = v___x_803_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_815_; 
lean_dec_ref(v_pred_783_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v_count_785_);
lean_ctor_set(v___x_815_, 1, v_iter_786_);
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd___boxed(lean_object* v_pred_816_, lean_object* v_limit_817_, lean_object* v_count_818_, lean_object* v_iter_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v_pred_816_, v_limit_817_, v_count_818_, v_iter_819_);
lean_dec(v_limit_817_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(lean_object* v_pred_821_, lean_object* v_limit_822_, lean_object* v_it_823_){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v_fst_826_; lean_object* v_snd_827_; lean_object* v_array_828_; lean_object* v_idx_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_846_; 
v___x_824_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_823_);
v___x_825_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v_pred_821_, v_limit_822_, v___x_824_, v_it_823_);
v_fst_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_fst_826_);
v_snd_827_ = lean_ctor_get(v___x_825_, 1);
lean_inc(v_snd_827_);
lean_dec_ref(v___x_825_);
v_array_828_ = lean_ctor_get(v_it_823_, 0);
v_idx_829_ = lean_ctor_get(v_it_823_, 1);
v_isSharedCheck_846_ = !lean_is_exclusive(v_it_823_);
if (v_isSharedCheck_846_ == 0)
{
v___x_831_ = v_it_823_;
v_isShared_832_ = v_isSharedCheck_846_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_idx_829_);
lean_inc(v_array_828_);
lean_dec(v_it_823_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_846_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v_lower_834_; lean_object* v_upper_835_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___y_843_; uint8_t v___x_845_; 
v___x_840_ = lean_nat_add(v_idx_829_, v_fst_826_);
lean_dec(v_fst_826_);
v___x_841_ = lean_byte_array_size(v_array_828_);
v___x_845_ = lean_nat_dec_le(v_idx_829_, v___x_824_);
if (v___x_845_ == 0)
{
v___y_843_ = v_idx_829_;
goto v___jp_842_;
}
else
{
lean_dec(v_idx_829_);
v___y_843_ = v___x_824_;
goto v___jp_842_;
}
v___jp_833_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = l_ByteArray_toByteSlice(v_array_828_, v_lower_834_, v_upper_835_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v___x_836_);
lean_ctor_set(v___x_831_, 0, v_snd_827_);
v___x_838_ = v___x_831_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_snd_827_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
v___jp_842_:
{
uint8_t v___x_844_; 
v___x_844_ = lean_nat_dec_le(v___x_840_, v___x_841_);
if (v___x_844_ == 0)
{
lean_dec(v___x_840_);
v_lower_834_ = v___y_843_;
v_upper_835_ = v___x_841_;
goto v___jp_833_;
}
else
{
v_lower_834_ = v___y_843_;
v_upper_835_ = v___x_840_;
goto v___jp_833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo___boxed(lean_object* v_pred_847_, lean_object* v_limit_848_, lean_object* v_it_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Std_Internal_Parsec_ByteArray_takeWhileUpTo(v_pred_847_, v_limit_848_, v_it_849_);
lean_dec(v_limit_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(lean_object* v_pred_851_, lean_object* v_limit_852_, lean_object* v_count_853_, lean_object* v_iter_854_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = lean_nat_dec_le(v_limit_852_, v_count_853_);
if (v___x_855_ == 0)
{
lean_object* v_array_856_; lean_object* v_idx_857_; uint8_t v___y_859_; lean_object* v___x_877_; uint8_t v___x_878_; 
v_array_856_ = lean_ctor_get(v_iter_854_, 0);
v_idx_857_ = lean_ctor_get(v_iter_854_, 1);
v___x_877_ = lean_byte_array_size(v_array_856_);
v___x_878_ = lean_nat_dec_lt(v_idx_857_, v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; 
lean_dec_ref(v_pred_851_);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v_count_853_);
lean_ctor_set(v___x_879_, 1, v_iter_854_);
return v___x_879_;
}
else
{
if (v___x_855_ == 0)
{
if (v___x_878_ == 0)
{
uint8_t v___x_880_; 
v___x_880_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0, &l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0_once, _init_l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0);
v___y_859_ = v___x_880_;
goto v___jp_858_;
}
else
{
uint8_t v___x_881_; 
v___x_881_ = lean_byte_array_fget(v_array_856_, v_idx_857_);
v___y_859_ = v___x_881_;
goto v___jp_858_;
}
}
else
{
lean_object* v___x_882_; 
lean_dec_ref(v_pred_851_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v_count_853_);
lean_ctor_set(v___x_882_, 1, v_iter_854_);
return v___x_882_;
}
}
v___jp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_860_ = lean_box(v___y_859_);
lean_inc_ref(v_pred_851_);
v___x_861_ = lean_apply_1(v_pred_851_, v___x_860_);
v___x_862_ = lean_unbox(v___x_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; 
lean_dec_ref(v_pred_851_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_count_853_);
lean_ctor_set(v___x_863_, 1, v_iter_854_);
return v___x_863_;
}
else
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_874_; 
lean_inc(v_idx_857_);
lean_inc_ref(v_array_856_);
v_isSharedCheck_874_ = !lean_is_exclusive(v_iter_854_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; lean_object* v_unused_876_; 
v_unused_875_ = lean_ctor_get(v_iter_854_, 1);
lean_dec(v_unused_875_);
v_unused_876_ = lean_ctor_get(v_iter_854_, 0);
lean_dec(v_unused_876_);
v___x_865_ = v_iter_854_;
v_isShared_866_ = v_isSharedCheck_874_;
goto v_resetjp_864_;
}
else
{
lean_dec(v_iter_854_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_874_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_nat_add(v_count_853_, v___x_867_);
lean_dec(v_count_853_);
v___x_869_ = lean_nat_add(v_idx_857_, v___x_867_);
lean_dec(v_idx_857_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 1, v___x_869_);
v___x_871_ = v___x_865_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_array_856_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_869_);
v___x_871_ = v_reuseFailAlloc_873_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
v_count_853_ = v___x_868_;
v_iter_854_ = v___x_871_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_883_; 
lean_dec_ref(v_pred_851_);
v___x_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_883_, 0, v_count_853_);
lean_ctor_set(v___x_883_, 1, v_iter_854_);
return v___x_883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd___boxed(lean_object* v_pred_884_, lean_object* v_limit_885_, lean_object* v_count_886_, lean_object* v_iter_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(v_pred_884_, v_limit_885_, v_count_886_, v_iter_887_);
lean_dec(v_limit_885_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(lean_object* v_pred_892_, lean_object* v_limit_893_, lean_object* v_it_894_){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v_fst_897_; lean_object* v_snd_898_; uint8_t v___x_899_; 
v___x_895_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_894_);
v___x_896_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(v_pred_892_, v_limit_893_, v___x_895_, v_it_894_);
v_fst_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_fst_897_);
v_snd_898_ = lean_ctor_get(v___x_896_, 1);
lean_inc(v_snd_898_);
lean_dec_ref(v___x_896_);
v___x_899_ = lean_nat_dec_eq(v_fst_897_, v___x_895_);
if (v___x_899_ == 0)
{
lean_object* v_array_900_; lean_object* v_idx_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_918_; 
v_array_900_ = lean_ctor_get(v_it_894_, 0);
v_idx_901_ = lean_ctor_get(v_it_894_, 1);
v_isSharedCheck_918_ = !lean_is_exclusive(v_it_894_);
if (v_isSharedCheck_918_ == 0)
{
v___x_903_ = v_it_894_;
v_isShared_904_ = v_isSharedCheck_918_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_idx_901_);
lean_inc(v_array_900_);
lean_dec(v_it_894_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_918_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v_lower_906_; lean_object* v_upper_907_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___y_915_; uint8_t v___x_917_; 
v___x_912_ = lean_nat_add(v_idx_901_, v_fst_897_);
lean_dec(v_fst_897_);
v___x_913_ = lean_byte_array_size(v_array_900_);
v___x_917_ = lean_nat_dec_le(v_idx_901_, v___x_895_);
if (v___x_917_ == 0)
{
v___y_915_ = v_idx_901_;
goto v___jp_914_;
}
else
{
lean_dec(v_idx_901_);
v___y_915_ = v___x_895_;
goto v___jp_914_;
}
v___jp_905_:
{
lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_908_ = l_ByteArray_toByteSlice(v_array_900_, v_lower_906_, v_upper_907_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 1, v___x_908_);
lean_ctor_set(v___x_903_, 0, v_snd_898_);
v___x_910_ = v___x_903_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_snd_898_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
v___jp_914_:
{
uint8_t v___x_916_; 
v___x_916_ = lean_nat_dec_le(v___x_912_, v___x_913_);
if (v___x_916_ == 0)
{
lean_dec(v___x_912_);
v_lower_906_ = v___y_915_;
v_upper_907_ = v___x_913_;
goto v___jp_905_;
}
else
{
v_lower_906_ = v___y_915_;
v_upper_907_ = v___x_912_;
goto v___jp_905_;
}
}
}
}
else
{
lean_object* v_array_919_; lean_object* v_idx_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_fst_897_);
v_array_919_ = lean_ctor_get(v_snd_898_, 0);
v_idx_920_ = lean_ctor_get(v_snd_898_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_snd_898_);
if (v_isSharedCheck_934_ == 0)
{
v___x_922_ = v_snd_898_;
v_isShared_923_ = v_isSharedCheck_934_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_idx_920_);
lean_inc(v_array_919_);
lean_dec(v_snd_898_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_934_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_924_ = lean_byte_array_size(v_array_919_);
lean_dec_ref(v_array_919_);
v___x_925_ = lean_nat_dec_le(v___x_924_, v_idx_920_);
lean_dec(v_idx_920_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = ((lean_object*)(l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___closed__1));
if (v_isShared_923_ == 0)
{
lean_ctor_set_tag(v___x_922_, 1);
lean_ctor_set(v___x_922_, 1, v___x_926_);
lean_ctor_set(v___x_922_, 0, v_it_894_);
v___x_928_ = v___x_922_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_it_894_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_930_ = lean_box(0);
if (v_isShared_923_ == 0)
{
lean_ctor_set_tag(v___x_922_, 1);
lean_ctor_set(v___x_922_, 1, v___x_930_);
lean_ctor_set(v___x_922_, 0, v_it_894_);
v___x_932_ = v___x_922_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_it_894_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1___boxed(lean_object* v_pred_935_, lean_object* v_limit_936_, lean_object* v_it_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Std_Internal_Parsec_ByteArray_takeWhileUpTo1(v_pred_935_, v_limit_936_, v_it_937_);
lean_dec(v_limit_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(lean_object* v_pred_939_, lean_object* v_limit_940_, lean_object* v_a_941_){
_start:
{
lean_object* v___f_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v_fst_945_; lean_object* v_snd_946_; lean_object* v_array_947_; lean_object* v_idx_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_965_; 
v___f_942_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_942_, 0, v_pred_939_);
v___x_943_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_941_);
v___x_944_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v___f_942_, v_limit_940_, v___x_943_, v_a_941_);
v_fst_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_fst_945_);
v_snd_946_ = lean_ctor_get(v___x_944_, 1);
lean_inc(v_snd_946_);
lean_dec_ref(v___x_944_);
v_array_947_ = lean_ctor_get(v_a_941_, 0);
v_idx_948_ = lean_ctor_get(v_a_941_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_a_941_);
if (v_isSharedCheck_965_ == 0)
{
v___x_950_ = v_a_941_;
v_isShared_951_ = v_isSharedCheck_965_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_idx_948_);
lean_inc(v_array_947_);
lean_dec(v_a_941_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_965_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_lower_953_; lean_object* v_upper_954_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___y_962_; uint8_t v___x_964_; 
v___x_959_ = lean_nat_add(v_idx_948_, v_fst_945_);
lean_dec(v_fst_945_);
v___x_960_ = lean_byte_array_size(v_array_947_);
v___x_964_ = lean_nat_dec_le(v_idx_948_, v___x_943_);
if (v___x_964_ == 0)
{
v___y_962_ = v_idx_948_;
goto v___jp_961_;
}
else
{
lean_dec(v_idx_948_);
v___y_962_ = v___x_943_;
goto v___jp_961_;
}
v___jp_952_:
{
lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_955_ = l_ByteArray_toByteSlice(v_array_947_, v_lower_953_, v_upper_954_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 1, v___x_955_);
lean_ctor_set(v___x_950_, 0, v_snd_946_);
v___x_957_ = v___x_950_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_snd_946_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
v___jp_961_:
{
uint8_t v___x_963_; 
v___x_963_ = lean_nat_dec_le(v___x_959_, v___x_960_);
if (v___x_963_ == 0)
{
lean_dec(v___x_959_);
v_lower_953_ = v___y_962_;
v_upper_954_ = v___x_960_;
goto v___jp_952_;
}
else
{
v_lower_953_ = v___y_962_;
v_upper_954_ = v___x_959_;
goto v___jp_952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_takeUntilUpTo___boxed(lean_object* v_pred_966_, lean_object* v_limit_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Std_Internal_Parsec_ByteArray_takeUntilUpTo(v_pred_966_, v_limit_967_, v_a_968_);
lean_dec(v_limit_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWhileUpTo_findEnd(lean_object* v_pred_970_, lean_object* v_limit_971_, lean_object* v_count_972_, lean_object* v_iter_973_){
_start:
{
uint8_t v___x_974_; 
v___x_974_ = lean_nat_dec_le(v_limit_971_, v_count_972_);
if (v___x_974_ == 0)
{
lean_object* v_array_975_; lean_object* v_idx_976_; uint8_t v___y_978_; lean_object* v___x_995_; uint8_t v___x_996_; 
v_array_975_ = lean_ctor_get(v_iter_973_, 0);
v_idx_976_ = lean_ctor_get(v_iter_973_, 1);
v___x_995_ = lean_byte_array_size(v_array_975_);
v___x_996_ = lean_nat_dec_lt(v_idx_976_, v___x_995_);
if (v___x_996_ == 0)
{
lean_dec(v_count_972_);
lean_dec_ref(v_pred_970_);
return v_iter_973_;
}
else
{
if (v___x_974_ == 0)
{
if (v___x_996_ == 0)
{
uint8_t v___x_997_; 
v___x_997_ = lean_uint8_once(&l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0, &l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0_once, _init_l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0);
v___y_978_ = v___x_997_;
goto v___jp_977_;
}
else
{
uint8_t v___x_998_; 
v___x_998_ = lean_byte_array_fget(v_array_975_, v_idx_976_);
v___y_978_ = v___x_998_;
goto v___jp_977_;
}
}
else
{
lean_dec(v_count_972_);
lean_dec_ref(v_pred_970_);
return v_iter_973_;
}
}
v___jp_977_:
{
lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_979_ = lean_box(v___y_978_);
lean_inc_ref(v_pred_970_);
v___x_980_ = lean_apply_1(v_pred_970_, v___x_979_);
v___x_981_ = lean_unbox(v___x_980_);
if (v___x_981_ == 0)
{
lean_dec(v_count_972_);
lean_dec_ref(v_pred_970_);
return v_iter_973_;
}
else
{
lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_992_; 
lean_inc(v_idx_976_);
lean_inc_ref(v_array_975_);
v_isSharedCheck_992_ = !lean_is_exclusive(v_iter_973_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; lean_object* v_unused_994_; 
v_unused_993_ = lean_ctor_get(v_iter_973_, 1);
lean_dec(v_unused_993_);
v_unused_994_ = lean_ctor_get(v_iter_973_, 0);
lean_dec(v_unused_994_);
v___x_983_ = v_iter_973_;
v_isShared_984_ = v_isSharedCheck_992_;
goto v_resetjp_982_;
}
else
{
lean_dec(v_iter_973_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_992_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_985_ = lean_unsigned_to_nat(1u);
v___x_986_ = lean_nat_add(v_count_972_, v___x_985_);
lean_dec(v_count_972_);
v___x_987_ = lean_nat_add(v_idx_976_, v___x_985_);
lean_dec(v_idx_976_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 1, v___x_987_);
v___x_989_ = v___x_983_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_array_975_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v___x_987_);
v___x_989_ = v_reuseFailAlloc_991_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
v_count_972_ = v___x_986_;
v_iter_973_ = v___x_989_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_count_972_);
lean_dec_ref(v_pred_970_);
return v_iter_973_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWhileUpTo_findEnd___boxed(lean_object* v_pred_999_, lean_object* v_limit_1000_, lean_object* v_count_1001_, lean_object* v_iter_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWhileUpTo_findEnd(v_pred_999_, v_limit_1000_, v_count_1001_, v_iter_1002_);
lean_dec(v_limit_1000_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(lean_object* v_pred_1004_, lean_object* v_limit_1005_, lean_object* v_it_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWhileUpTo_findEnd(v_pred_1004_, v_limit_1005_, v___x_1007_, v_it_1006_);
v___x_1009_ = lean_box(0);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipWhileUpTo___boxed(lean_object* v_pred_1011_, lean_object* v_limit_1012_, lean_object* v_it_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Std_Internal_Parsec_ByteArray_skipWhileUpTo(v_pred_1011_, v_limit_1012_, v_it_1013_);
lean_dec(v_limit_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(lean_object* v_pred_1015_, lean_object* v_limit_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___f_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___f_1018_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_takeUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1018_, 0, v_pred_1015_);
v___x_1019_ = lean_unsigned_to_nat(0u);
v___x_1020_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWhileUpTo_findEnd(v___f_1018_, v_limit_1016_, v___x_1019_, v_a_1017_);
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipUntilUpTo___boxed(lean_object* v_pred_1023_, lean_object* v_limit_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Std_Internal_Parsec_ByteArray_skipUntilUpTo(v_pred_1023_, v_limit_1024_, v_a_1025_);
lean_dec(v_limit_1024_);
return v_res_1026_;
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
