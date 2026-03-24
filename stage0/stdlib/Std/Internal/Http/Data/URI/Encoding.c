// Lean compiler output
// Module: Std.Internal.Http.Data.URI.Encoding
// Imports: import Init.Grind import Init.While import Init.Data.SInt.Lemmas import Init.Data.UInt.Lemmas import Init.Data.UInt.Bitwise import Init.Data.Array.Lemmas public import Init.Data.String public import Std.Internal.Http.Internal.Char
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_uint8_shift_left(uint8_t, uint8_t);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
extern lean_object* l_ByteArray_empty;
uint8_t lean_string_validate_utf8(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_byte_array_uget(lean_object*, size_t);
uint8_t lean_uint8_shift_right(uint8_t, uint8_t);
uint8_t lean_uint8_dec_lt(uint8_t, uint8_t);
uint8_t lean_uint8_land(uint8_t, uint8_t);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_data(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_ByteArray_instDecidableEq___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_String_quote(lean_object*);
lean_object* l_ByteArray_hash___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_URI_isEncodedChar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_isEncodedChar___closed__0;
static lean_once_cell_t l_Std_Http_URI_isEncodedChar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_isEncodedChar___closed__1;
static lean_once_cell_t l_Std_Http_URI_isEncodedChar___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_isEncodedChar___closed__2;
static lean_once_cell_t l_Std_Http_URI_isEncodedChar___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_isEncodedChar___closed__3;
static lean_once_cell_t l_Std_Http_URI_isEncodedChar___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_isEncodedChar___closed__4;
static lean_once_cell_t l_Std_Http_URI_isEncodedChar___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_isEncodedChar___closed__5;
static lean_once_cell_t l_Std_Http_URI_isEncodedChar___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_isEncodedChar___closed__6;
LEAN_EXPORT uint8_t l_Std_Http_URI_isEncodedChar(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_isEncodedChar___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_URI_isEncodedQueryChar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_isEncodedQueryChar___closed__0;
LEAN_EXPORT uint8_t l_Std_Http_URI_isEncodedQueryChar(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_isEncodedQueryChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__0 = (const lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__0_value;
static const lean_closure_object l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__1 = (const lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__1_value;
static const lean_closure_object l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__2 = (const lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__2_value;
static const lean_closure_object l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__3 = (const lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__3_value;
static const lean_closure_object l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__4 = (const lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__4_value;
static const lean_closure_object l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__5 = (const lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__5_value;
static const lean_closure_object l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__6 = (const lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__6_value;
static const lean_ctor_object l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__0_value),((lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__1_value)}};
static const lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__7 = (const lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__7_value;
static const lean_ctor_object l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__7_value),((lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__2_value),((lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__3_value),((lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__4_value),((lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__5_value)}};
static const lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__8 = (const lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__8_value;
static const lean_ctor_object l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__8_value),((lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__6_value)}};
static const lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9 = (const lean_object*)&l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9_value;
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidPercentEncoding(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidPercentEncoding___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_hexDigit(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Std.Internal.Http.Data.URI.Encoding"};
static const lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0_value;
static const lean_string_object l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Std.Http.URI.EncodedString.ofByteArray!"};
static const lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1 = (const lean_object*)&l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1_value;
static const lean_string_object l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid encoded string"};
static const lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2 = (const lean_object*)&l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2_value;
static lean_once_cell_t l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___lam__0(lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedString_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_EncodedString_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedString_instToString___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedString_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedString_decode_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedString_decode_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_EncodedString_decode___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedString_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedString_instRepr___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedString_instRepr___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedString_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteArray_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedString_instHashable___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedString_instHashable___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Std.Http.URI.EncodedQueryString.ofByteArray!"};
static const lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0_value;
static const lean_string_object l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "invalid encoded query string"};
static const lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1 = (const lean_object*)&l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1_value;
static lean_once_cell_t l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0;
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringEncodedQueryString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___boxed(lean_object*);
static const lean_sarray_object l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_sarray_object) + 1, .m_other = 1, .m_tag = 248}, .m_size = 1, .m_capacity = 1, .m_data = {0}};
static const lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__0 = (const lean_object*)&l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__0_value;
static lean_once_cell_t l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1;
static const lean_sarray_object l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_sarray_object) + 1, .m_other = 1, .m_tag = 248}, .m_size = 1, .m_capacity = 1, .m_data = {1}};
static const lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2 = (const lean_object*)&l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2_value;
static lean_once_cell_t l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3;
LEAN_EXPORT uint64_t l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_instHashableOptionEncodedQueryString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___closed__0 = (const lean_object*)&l_Std_Http_URI_instHashableOptionEncodedQueryString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___boxed(lean_object*);
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16;
static lean_once_cell_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17;
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedSegment_encode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_EncodedSegment_encode___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedSegment_encode___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedSegment_encode___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode___boxed(lean_object*);
static lean_once_cell_t l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0;
static lean_once_cell_t l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1;
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedFragment_encode___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedFragment_encode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedFragment_encode___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedFragment_encode___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedUserInfo_encode___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedUserInfo_encode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedUserInfo_encode___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedUserInfo_encode___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryParam_encode___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedQueryParam_encode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedQueryParam_encode___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedQueryParam_encode___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode___boxed(lean_object*);
static uint8_t _init_l_Std_Http_URI_isEncodedChar___closed__0(void){
_start:
{
uint32_t v___x_1_; uint8_t v___x_2_; 
v___x_1_ = 37;
v___x_2_ = lean_uint32_to_uint8(v___x_1_);
return v___x_2_;
}
}
static uint8_t _init_l_Std_Http_URI_isEncodedChar___closed__1(void){
_start:
{
uint32_t v___x_3_; uint8_t v___x_4_; 
v___x_3_ = 65;
v___x_4_ = lean_uint32_to_uint8(v___x_3_);
return v___x_4_;
}
}
static uint8_t _init_l_Std_Http_URI_isEncodedChar___closed__2(void){
_start:
{
uint32_t v___x_5_; uint8_t v___x_6_; 
v___x_5_ = 70;
v___x_6_ = lean_uint32_to_uint8(v___x_5_);
return v___x_6_;
}
}
static uint8_t _init_l_Std_Http_URI_isEncodedChar___closed__3(void){
_start:
{
uint32_t v___x_7_; uint8_t v___x_8_; 
v___x_7_ = 97;
v___x_8_ = lean_uint32_to_uint8(v___x_7_);
return v___x_8_;
}
}
static uint8_t _init_l_Std_Http_URI_isEncodedChar___closed__4(void){
_start:
{
uint32_t v___x_9_; uint8_t v___x_10_; 
v___x_9_ = 102;
v___x_10_ = lean_uint32_to_uint8(v___x_9_);
return v___x_10_;
}
}
static uint8_t _init_l_Std_Http_URI_isEncodedChar___closed__5(void){
_start:
{
uint32_t v___x_11_; uint8_t v___x_12_; 
v___x_11_ = 48;
v___x_12_ = lean_uint32_to_uint8(v___x_11_);
return v___x_12_;
}
}
static uint8_t _init_l_Std_Http_URI_isEncodedChar___closed__6(void){
_start:
{
uint32_t v___x_13_; uint8_t v___x_14_; 
v___x_13_ = 57;
v___x_14_ = lean_uint32_to_uint8(v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isEncodedChar(lean_object* v_rule_15_, uint8_t v_c_16_){
_start:
{
uint8_t v___x_17_; uint8_t v___x_18_; uint8_t v___y_20_; uint8_t v___y_24_; uint8_t v___y_30_; 
v___x_17_ = 128;
v___x_18_ = lean_uint8_dec_lt(v_c_16_, v___x_17_);
if (v___x_18_ == 0)
{
lean_dec_ref(v_rule_15_);
return v___x_18_;
}
else
{
lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_35_ = lean_box(v_c_16_);
v___x_36_ = lean_apply_1(v_rule_15_, v___x_35_);
v___x_37_ = lean_unbox(v___x_36_);
if (v___x_37_ == 0)
{
uint8_t v___x_38_; uint8_t v___x_39_; 
v___x_38_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_39_ = lean_uint8_dec_le(v___x_38_, v_c_16_);
if (v___x_39_ == 0)
{
v___y_30_ = v___x_39_;
goto v___jp_29_;
}
else
{
uint8_t v___x_40_; uint8_t v___x_41_; 
v___x_40_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_41_ = lean_uint8_dec_le(v_c_16_, v___x_40_);
v___y_30_ = v___x_41_;
goto v___jp_29_;
}
}
else
{
return v___x_18_;
}
}
v___jp_19_:
{
if (v___y_20_ == 0)
{
uint8_t v___x_21_; uint8_t v___x_22_; 
v___x_21_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__0, &l_Std_Http_URI_isEncodedChar___closed__0_once, _init_l_Std_Http_URI_isEncodedChar___closed__0);
v___x_22_ = lean_uint8_dec_eq(v_c_16_, v___x_21_);
if (v___x_22_ == 0)
{
return v___y_20_;
}
else
{
return v___x_18_;
}
}
else
{
return v___x_18_;
}
}
v___jp_23_:
{
if (v___y_24_ == 0)
{
uint8_t v___x_25_; uint8_t v___x_26_; 
v___x_25_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_26_ = lean_uint8_dec_le(v___x_25_, v_c_16_);
if (v___x_26_ == 0)
{
v___y_20_ = v___x_26_;
goto v___jp_19_;
}
else
{
uint8_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__2, &l_Std_Http_URI_isEncodedChar___closed__2_once, _init_l_Std_Http_URI_isEncodedChar___closed__2);
v___x_28_ = lean_uint8_dec_le(v_c_16_, v___x_27_);
v___y_20_ = v___x_28_;
goto v___jp_19_;
}
}
else
{
return v___x_18_;
}
}
v___jp_29_:
{
if (v___y_30_ == 0)
{
uint8_t v___x_31_; uint8_t v___x_32_; 
v___x_31_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_32_ = lean_uint8_dec_le(v___x_31_, v_c_16_);
if (v___x_32_ == 0)
{
v___y_24_ = v___x_32_;
goto v___jp_23_;
}
else
{
uint8_t v___x_33_; uint8_t v___x_34_; 
v___x_33_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__4, &l_Std_Http_URI_isEncodedChar___closed__4_once, _init_l_Std_Http_URI_isEncodedChar___closed__4);
v___x_34_ = lean_uint8_dec_le(v_c_16_, v___x_33_);
v___y_24_ = v___x_34_;
goto v___jp_23_;
}
}
else
{
return v___x_18_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isEncodedChar___boxed(lean_object* v_rule_42_, lean_object* v_c_43_){
_start:
{
uint8_t v_c_boxed_44_; uint8_t v_res_45_; lean_object* v_r_46_; 
v_c_boxed_44_ = lean_unbox(v_c_43_);
v_res_45_ = l_Std_Http_URI_isEncodedChar(v_rule_42_, v_c_boxed_44_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
static uint8_t _init_l_Std_Http_URI_isEncodedQueryChar___closed__0(void){
_start:
{
uint32_t v___x_47_; uint8_t v___x_48_; 
v___x_47_ = 43;
v___x_48_ = lean_uint32_to_uint8(v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isEncodedQueryChar(lean_object* v_rule_49_, uint8_t v_c_50_){
_start:
{
uint8_t v___x_51_; 
v___x_51_ = l_Std_Http_URI_isEncodedChar(v_rule_49_, v_c_50_);
if (v___x_51_ == 0)
{
uint8_t v___x_52_; uint8_t v___x_53_; 
v___x_52_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_53_ = lean_uint8_dec_eq(v_c_50_, v___x_52_);
if (v___x_53_ == 0)
{
return v___x_51_;
}
else
{
return v___x_53_;
}
}
else
{
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isEncodedQueryChar___boxed(lean_object* v_rule_54_, lean_object* v_c_55_){
_start:
{
uint8_t v_c_boxed_56_; uint8_t v_res_57_; lean_object* v_r_58_; 
v_c_boxed_56_ = lean_unbox(v_c_55_);
v_res_57_ = l_Std_Http_URI_isEncodedQueryChar(v_rule_54_, v_c_boxed_56_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(lean_object* v_r_59_, uint8_t v___x_60_, uint8_t v_v_61_){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = l_Std_Http_URI_isEncodedChar(v_r_59_, v_v_61_);
if (v___x_62_ == 0)
{
return v___x_60_;
}
else
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed(lean_object* v_r_64_, lean_object* v___x_65_, lean_object* v_v_66_){
_start:
{
uint8_t v___x_71__boxed_67_; uint8_t v_v_boxed_68_; uint8_t v_res_69_; lean_object* v_r_70_; 
v___x_71__boxed_67_ = lean_unbox(v___x_65_);
v_v_boxed_68_ = lean_unbox(v_v_66_);
v_res_69_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(v_r_64_, v___x_71__boxed_67_, v_v_boxed_68_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars(lean_object* v_r_90_, lean_object* v_s_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_92_ = lean_byte_array_data(v_s_91_);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_array_get_size(v___x_92_);
v___x_95_ = ((lean_object*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9));
v___x_96_ = lean_nat_dec_lt(v___x_93_, v___x_94_);
if (v___x_96_ == 0)
{
uint8_t v___x_97_; 
lean_dec_ref(v___x_92_);
lean_dec_ref(v_r_90_);
v___x_97_ = 1;
return v___x_97_;
}
else
{
if (v___x_96_ == 0)
{
lean_dec_ref(v___x_92_);
lean_dec_ref(v_r_90_);
return v___x_96_;
}
else
{
lean_object* v___x_98_; lean_object* v___f_99_; size_t v___x_100_; size_t v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_98_ = lean_box(v___x_96_);
v___f_99_ = lean_alloc_closure((void*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed), 3, 2);
lean_closure_set(v___f_99_, 0, v_r_90_);
lean_closure_set(v___f_99_, 1, v___x_98_);
v___x_100_ = ((size_t)0ULL);
v___x_101_ = lean_usize_of_nat(v___x_94_);
v___x_102_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_95_, v___f_99_, v___x_92_, v___x_100_, v___x_101_);
v___x_103_ = lean_unbox(v___x_102_);
lean_dec(v___x_102_);
if (v___x_103_ == 0)
{
return v___x_96_;
}
else
{
uint8_t v___x_104_; 
v___x_104_ = 0;
return v___x_104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___boxed(lean_object* v_r_105_, lean_object* v_s_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_105_, v_s_106_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(lean_object* v_r_109_, uint8_t v___x_110_, uint8_t v_v_111_){
_start:
{
uint8_t v___x_112_; 
v___x_112_ = l_Std_Http_URI_isEncodedQueryChar(v_r_109_, v_v_111_);
if (v___x_112_ == 0)
{
return v___x_110_;
}
else
{
uint8_t v___x_113_; 
v___x_113_ = 0;
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed(lean_object* v_r_114_, lean_object* v___x_115_, lean_object* v_v_116_){
_start:
{
uint8_t v___x_71__boxed_117_; uint8_t v_v_boxed_118_; uint8_t v_res_119_; lean_object* v_r_120_; 
v___x_71__boxed_117_ = lean_unbox(v___x_115_);
v_v_boxed_118_ = lean_unbox(v_v_116_);
v_res_119_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(v_r_114_, v___x_71__boxed_117_, v_v_boxed_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(lean_object* v_r_121_, lean_object* v_s_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_123_ = lean_byte_array_data(v_s_122_);
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_array_get_size(v___x_123_);
v___x_126_ = ((lean_object*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9));
v___x_127_ = lean_nat_dec_lt(v___x_124_, v___x_125_);
if (v___x_127_ == 0)
{
uint8_t v___x_128_; 
lean_dec_ref(v___x_123_);
lean_dec_ref(v_r_121_);
v___x_128_ = 1;
return v___x_128_;
}
else
{
if (v___x_127_ == 0)
{
lean_dec_ref(v___x_123_);
lean_dec_ref(v_r_121_);
return v___x_127_;
}
else
{
lean_object* v___x_129_; lean_object* v___f_130_; size_t v___x_131_; size_t v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_129_ = lean_box(v___x_127_);
v___f_130_ = lean_alloc_closure((void*)(l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed), 3, 2);
lean_closure_set(v___f_130_, 0, v_r_121_);
lean_closure_set(v___f_130_, 1, v___x_129_);
v___x_131_ = ((size_t)0ULL);
v___x_132_ = lean_usize_of_nat(v___x_125_);
v___x_133_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_126_, v___f_130_, v___x_123_, v___x_131_, v___x_132_);
v___x_134_ = lean_unbox(v___x_133_);
lean_dec(v___x_133_);
if (v___x_134_ == 0)
{
return v___x_127_;
}
else
{
uint8_t v___x_135_; 
v___x_135_ = 0;
return v___x_135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___boxed(lean_object* v_r_136_, lean_object* v_s_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_136_, v_s_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(lean_object* v_ba_140_, lean_object* v_i_141_){
_start:
{
uint8_t v___y_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = lean_byte_array_size(v_ba_140_);
v___x_149_ = lean_nat_dec_lt(v_i_141_, v___x_148_);
if (v___x_149_ == 0)
{
uint8_t v___x_150_; 
lean_dec(v_i_141_);
v___x_150_ = 1;
return v___x_150_;
}
else
{
uint8_t v_c_151_; uint8_t v___x_152_; uint8_t v___x_153_; 
v_c_151_ = lean_byte_array_fget(v_ba_140_, v_i_141_);
v___x_152_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__0, &l_Std_Http_URI_isEncodedChar___closed__0_once, _init_l_Std_Http_URI_isEncodedChar___closed__0);
v___x_153_ = lean_uint8_dec_eq(v_c_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_i_141_, v___x_154_);
lean_dec(v_i_141_);
v_i_141_ = v___x_155_;
goto _start;
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_157_ = lean_unsigned_to_nat(2u);
v___x_158_ = lean_nat_add(v_i_141_, v___x_157_);
v___x_159_ = lean_nat_dec_lt(v___x_158_, v___x_148_);
if (v___x_159_ == 0)
{
lean_dec(v___x_158_);
lean_dec(v_i_141_);
return v___x_159_;
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v_d1_162_; uint8_t v_d2_163_; uint8_t v___y_165_; uint8_t v___y_171_; uint8_t v___y_182_; uint8_t v___y_184_; uint8_t v___y_190_; uint8_t v___x_195_; uint8_t v___x_196_; 
v___x_160_ = lean_unsigned_to_nat(1u);
v___x_161_ = lean_nat_add(v_i_141_, v___x_160_);
v_d1_162_ = lean_byte_array_fget(v_ba_140_, v___x_161_);
lean_dec(v___x_161_);
v_d2_163_ = lean_byte_array_fget(v_ba_140_, v___x_158_);
lean_dec(v___x_158_);
v___x_195_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_196_ = lean_uint8_dec_le(v___x_195_, v_d1_162_);
if (v___x_196_ == 0)
{
v___y_190_ = v___x_196_;
goto v___jp_189_;
}
else
{
uint8_t v___x_197_; uint8_t v___x_198_; 
v___x_197_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_198_ = lean_uint8_dec_le(v_d1_162_, v___x_197_);
v___y_190_ = v___x_198_;
goto v___jp_189_;
}
v___jp_164_:
{
if (v___y_165_ == 0)
{
uint8_t v___x_166_; uint8_t v___x_167_; 
v___x_166_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_167_ = lean_uint8_dec_le(v___x_166_, v_d2_163_);
if (v___x_167_ == 0)
{
v___y_147_ = v___x_167_;
goto v___jp_146_;
}
else
{
uint8_t v___x_168_; uint8_t v___x_169_; 
v___x_168_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__2, &l_Std_Http_URI_isEncodedChar___closed__2_once, _init_l_Std_Http_URI_isEncodedChar___closed__2);
v___x_169_ = lean_uint8_dec_le(v_d2_163_, v___x_168_);
v___y_147_ = v___x_169_;
goto v___jp_146_;
}
}
else
{
goto v___jp_142_;
}
}
v___jp_170_:
{
if (v___y_171_ == 0)
{
uint8_t v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_173_ = lean_uint8_dec_le(v___x_172_, v_d2_163_);
if (v___x_173_ == 0)
{
v___y_165_ = v___x_173_;
goto v___jp_164_;
}
else
{
uint8_t v___x_174_; uint8_t v___x_175_; 
v___x_174_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__4, &l_Std_Http_URI_isEncodedChar___closed__4_once, _init_l_Std_Http_URI_isEncodedChar___closed__4);
v___x_175_ = lean_uint8_dec_le(v_d2_163_, v___x_174_);
v___y_165_ = v___x_175_;
goto v___jp_164_;
}
}
else
{
goto v___jp_142_;
}
}
v___jp_176_:
{
uint8_t v___x_177_; uint8_t v___x_178_; 
v___x_177_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_178_ = lean_uint8_dec_le(v___x_177_, v_d2_163_);
if (v___x_178_ == 0)
{
v___y_171_ = v___x_178_;
goto v___jp_170_;
}
else
{
uint8_t v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_180_ = lean_uint8_dec_le(v_d2_163_, v___x_179_);
v___y_171_ = v___x_180_;
goto v___jp_170_;
}
}
v___jp_181_:
{
if (v___y_182_ == 0)
{
lean_dec(v_i_141_);
return v___y_182_;
}
else
{
goto v___jp_176_;
}
}
v___jp_183_:
{
if (v___y_184_ == 0)
{
uint8_t v___x_185_; uint8_t v___x_186_; 
v___x_185_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_186_ = lean_uint8_dec_le(v___x_185_, v_d1_162_);
if (v___x_186_ == 0)
{
v___y_182_ = v___x_186_;
goto v___jp_181_;
}
else
{
uint8_t v___x_187_; uint8_t v___x_188_; 
v___x_187_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__2, &l_Std_Http_URI_isEncodedChar___closed__2_once, _init_l_Std_Http_URI_isEncodedChar___closed__2);
v___x_188_ = lean_uint8_dec_le(v_d1_162_, v___x_187_);
v___y_182_ = v___x_188_;
goto v___jp_181_;
}
}
else
{
goto v___jp_176_;
}
}
v___jp_189_:
{
if (v___y_190_ == 0)
{
uint8_t v___x_191_; uint8_t v___x_192_; 
v___x_191_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_192_ = lean_uint8_dec_le(v___x_191_, v_d1_162_);
if (v___x_192_ == 0)
{
v___y_184_ = v___x_192_;
goto v___jp_183_;
}
else
{
uint8_t v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__4, &l_Std_Http_URI_isEncodedChar___closed__4_once, _init_l_Std_Http_URI_isEncodedChar___closed__4);
v___x_194_ = lean_uint8_dec_le(v_d1_162_, v___x_193_);
v___y_184_ = v___x_194_;
goto v___jp_183_;
}
}
else
{
goto v___jp_176_;
}
}
}
}
}
v___jp_142_:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_unsigned_to_nat(3u);
v___x_144_ = lean_nat_add(v_i_141_, v___x_143_);
lean_dec(v_i_141_);
v_i_141_ = v___x_144_;
goto _start;
}
v___jp_146_:
{
if (v___y_147_ == 0)
{
lean_dec(v_i_141_);
return v___y_147_;
}
else
{
goto v___jp_142_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop___boxed(lean_object* v_ba_199_, lean_object* v_i_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_199_, v_i_200_);
lean_dec_ref(v_ba_199_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidPercentEncoding(lean_object* v_ba_203_){
_start:
{
lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_203_, v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidPercentEncoding___boxed(lean_object* v_ba_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_206_);
lean_dec_ref(v_ba_206_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_hexDigit(uint8_t v_n_209_){
_start:
{
uint8_t v___x_210_; uint8_t v___x_211_; 
v___x_210_ = 10;
v___x_211_ = lean_uint8_dec_lt(v_n_209_, v___x_210_);
if (v___x_211_ == 0)
{
uint8_t v___x_212_; uint8_t v___x_213_; uint8_t v___x_214_; 
v___x_212_ = lean_uint8_sub(v_n_209_, v___x_210_);
v___x_213_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_214_ = lean_uint8_add(v___x_212_, v___x_213_);
return v___x_214_;
}
else
{
uint8_t v___x_215_; uint8_t v___x_216_; 
v___x_215_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_216_ = lean_uint8_add(v_n_209_, v___x_215_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigit___boxed(lean_object* v_n_217_){
_start:
{
uint8_t v_n_boxed_218_; uint8_t v_res_219_; lean_object* v_r_220_; 
v_n_boxed_218_ = lean_unbox(v_n_217_);
v_res_219_ = l_Std_Http_URI_hexDigit(v_n_boxed_218_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f(uint8_t v_c_221_){
_start:
{
uint8_t v___y_223_; uint8_t v___y_224_; uint8_t v___y_232_; uint8_t v___y_233_; uint8_t v___x_243_; uint8_t v___y_245_; uint8_t v___x_253_; 
v___x_243_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_253_ = lean_uint8_dec_le(v___x_243_, v_c_221_);
if (v___x_253_ == 0)
{
v___y_245_ = v___x_253_;
goto v___jp_244_;
}
else
{
uint8_t v___x_254_; uint8_t v___x_255_; 
v___x_254_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_255_ = lean_uint8_dec_le(v_c_221_, v___x_254_);
v___y_245_ = v___x_255_;
goto v___jp_244_;
}
v___jp_222_:
{
if (v___y_224_ == 0)
{
lean_object* v___x_225_; 
v___x_225_ = lean_box(0);
return v___x_225_;
}
else
{
uint8_t v___x_226_; uint8_t v___x_227_; uint8_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_226_ = lean_uint8_sub(v_c_221_, v___y_223_);
v___x_227_ = 10;
v___x_228_ = lean_uint8_add(v___x_226_, v___x_227_);
v___x_229_ = lean_box(v___x_228_);
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
return v___x_230_;
}
}
v___jp_231_:
{
if (v___y_233_ == 0)
{
uint8_t v___x_234_; uint8_t v___x_235_; 
v___x_234_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_235_ = lean_uint8_dec_le(v___x_234_, v_c_221_);
if (v___x_235_ == 0)
{
v___y_223_ = v___x_234_;
v___y_224_ = v___x_235_;
goto v___jp_222_;
}
else
{
uint8_t v___x_236_; uint8_t v___x_237_; 
v___x_236_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__2, &l_Std_Http_URI_isEncodedChar___closed__2_once, _init_l_Std_Http_URI_isEncodedChar___closed__2);
v___x_237_ = lean_uint8_dec_le(v_c_221_, v___x_236_);
v___y_223_ = v___x_234_;
v___y_224_ = v___x_237_;
goto v___jp_222_;
}
}
else
{
uint8_t v___x_238_; uint8_t v___x_239_; uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_238_ = lean_uint8_sub(v_c_221_, v___y_232_);
v___x_239_ = 10;
v___x_240_ = lean_uint8_add(v___x_238_, v___x_239_);
v___x_241_ = lean_box(v___x_240_);
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
v___jp_244_:
{
if (v___y_245_ == 0)
{
uint8_t v___x_246_; uint8_t v___x_247_; 
v___x_246_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_247_ = lean_uint8_dec_le(v___x_246_, v_c_221_);
if (v___x_247_ == 0)
{
v___y_232_ = v___x_246_;
v___y_233_ = v___x_247_;
goto v___jp_231_;
}
else
{
uint8_t v___x_248_; uint8_t v___x_249_; 
v___x_248_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__4, &l_Std_Http_URI_isEncodedChar___closed__4_once, _init_l_Std_Http_URI_isEncodedChar___closed__4);
v___x_249_ = lean_uint8_dec_le(v_c_221_, v___x_248_);
v___y_232_ = v___x_246_;
v___y_233_ = v___x_249_;
goto v___jp_231_;
}
}
else
{
uint8_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_uint8_sub(v_c_221_, v___x_243_);
v___x_251_ = lean_box(v___x_250_);
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f___boxed(lean_object* v_c_256_){
_start:
{
uint8_t v_c_boxed_257_; lean_object* v_res_258_; 
v_c_boxed_257_ = lean_unbox(v_c_256_);
v_res_258_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_c_boxed_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(lean_object* v_x_259_, uint8_t v_x_260_, lean_object* v_h__1_261_){
_start:
{
lean_object* v_data_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_data_262_ = lean_byte_array_data(v_x_259_);
v___x_263_ = lean_box(v_x_260_);
v___x_264_ = lean_apply_2(v_h__1_261_, v_data_262_, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg___boxed(lean_object* v_x_265_, lean_object* v_x_266_, lean_object* v_h__1_267_){
_start:
{
uint8_t v_x_17__boxed_268_; lean_object* v_res_269_; 
v_x_17__boxed_268_ = lean_unbox(v_x_266_);
v_res_269_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(v_x_265_, v_x_17__boxed_268_, v_h__1_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(lean_object* v_motive_270_, lean_object* v_x_271_, uint8_t v_x_272_, lean_object* v_h__1_273_){
_start:
{
lean_object* v_data_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_data_274_ = lean_byte_array_data(v_x_271_);
v___x_275_ = lean_box(v_x_272_);
v___x_276_ = lean_apply_2(v_h__1_273_, v_data_274_, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___boxed(lean_object* v_motive_277_, lean_object* v_x_278_, lean_object* v_x_279_, lean_object* v_h__1_280_){
_start:
{
uint8_t v_x_29__boxed_281_; lean_object* v_res_282_; 
v_x_29__boxed_281_ = lean_unbox(v_x_279_);
v_res_282_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(v_motive_277_, v_x_278_, v_x_29__boxed_281_, v_h__1_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter___redArg(lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_h__1_285_, lean_object* v_h__2_286_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
lean_object* v___x_287_; 
lean_dec(v_h__2_286_);
v___x_287_ = lean_apply_1(v_h__1_285_, v_x_284_);
return v___x_287_;
}
else
{
lean_object* v_head_288_; lean_object* v_tail_289_; lean_object* v___x_290_; 
lean_dec(v_h__1_285_);
v_head_288_ = lean_ctor_get(v_x_283_, 0);
lean_inc(v_head_288_);
v_tail_289_ = lean_ctor_get(v_x_283_, 1);
lean_inc(v_tail_289_);
lean_dec_ref(v_x_283_);
v___x_290_ = lean_apply_3(v_h__2_286_, v_head_288_, v_tail_289_, v_x_284_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter(lean_object* v_motive_291_, lean_object* v_x_292_, lean_object* v_x_293_, lean_object* v_h__1_294_, lean_object* v_h__2_295_){
_start:
{
if (lean_obj_tag(v_x_292_) == 0)
{
lean_object* v___x_296_; 
lean_dec(v_h__2_295_);
v___x_296_ = lean_apply_1(v_h__1_294_, v_x_293_);
return v___x_296_;
}
else
{
lean_object* v_head_297_; lean_object* v_tail_298_; lean_object* v___x_299_; 
lean_dec(v_h__1_294_);
v_head_297_ = lean_ctor_get(v_x_292_, 0);
lean_inc(v_head_297_);
v_tail_298_ = lean_ctor_get(v_x_292_, 1);
lean_inc(v_tail_298_);
lean_dec_ref(v_x_292_);
v___x_299_ = lean_apply_3(v_h__2_295_, v_head_297_, v_tail_298_, v_x_293_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty(lean_object* v_r_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_ByteArray_empty;
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___boxed(lean_object* v_r_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Std_Http_URI_EncodedString_empty(v_r_302_);
lean_dec_ref(v_r_302_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited(lean_object* v_r_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_ByteArray_empty;
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___boxed(lean_object* v_r_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_Http_URI_EncodedString_instInhabited(v_r_306_);
lean_dec_ref(v_r_306_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(lean_object* v_s_308_, uint8_t v_c_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = lean_byte_array_push(v_s_308_, v_c_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg___boxed(lean_object* v_s_311_, lean_object* v_c_312_){
_start:
{
uint8_t v_c_boxed_313_; lean_object* v_res_314_; 
v_c_boxed_313_ = lean_unbox(v_c_312_);
v_res_314_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(v_s_311_, v_c_boxed_313_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(lean_object* v_r_315_, lean_object* v_s_316_, uint8_t v_c_317_, lean_object* v_h_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = lean_byte_array_push(v_s_316_, v_c_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___boxed(lean_object* v_r_320_, lean_object* v_s_321_, lean_object* v_c_322_, lean_object* v_h_323_){
_start:
{
uint8_t v_c_boxed_324_; lean_object* v_res_325_; 
v_c_boxed_324_ = lean_unbox(v_c_322_);
v_res_325_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(v_r_320_, v_s_321_, v_c_boxed_324_, v_h_323_);
lean_dec_ref(v_r_320_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(uint8_t v_b_326_, lean_object* v_s_327_){
_start:
{
uint8_t v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; uint8_t v___x_331_; uint8_t v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; uint8_t v___x_335_; uint8_t v___x_336_; lean_object* v_ba_337_; 
v___x_328_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__0, &l_Std_Http_URI_isEncodedChar___closed__0_once, _init_l_Std_Http_URI_isEncodedChar___closed__0);
v___x_329_ = lean_byte_array_push(v_s_327_, v___x_328_);
v___x_330_ = 4;
v___x_331_ = lean_uint8_shift_right(v_b_326_, v___x_330_);
v___x_332_ = l_Std_Http_URI_hexDigit(v___x_331_);
v___x_333_ = lean_byte_array_push(v___x_329_, v___x_332_);
v___x_334_ = 15;
v___x_335_ = lean_uint8_land(v_b_326_, v___x_334_);
v___x_336_ = l_Std_Http_URI_hexDigit(v___x_335_);
v_ba_337_ = lean_byte_array_push(v___x_333_, v___x_336_);
return v_ba_337_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg___boxed(lean_object* v_b_338_, lean_object* v_s_339_){
_start:
{
uint8_t v_b_boxed_340_; lean_object* v_res_341_; 
v_b_boxed_340_ = lean_unbox(v_b_338_);
v_res_341_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_boxed_340_, v_s_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(lean_object* v_r_342_, uint8_t v_b_343_, lean_object* v_s_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_343_, v_s_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___boxed(lean_object* v_r_346_, lean_object* v_b_347_, lean_object* v_s_348_){
_start:
{
uint8_t v_b_boxed_349_; lean_object* v_res_350_; 
v_b_boxed_349_ = lean_unbox(v_b_347_);
v_res_350_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(v_r_346_, v_b_boxed_349_, v_s_348_);
lean_dec_ref(v_r_346_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(lean_object* v_r_351_, lean_object* v_as_352_, size_t v_i_353_, size_t v_stop_354_, lean_object* v_b_355_){
_start:
{
lean_object* v___y_357_; uint8_t v___x_361_; 
v___x_361_ = lean_usize_dec_eq(v_i_353_, v_stop_354_);
if (v___x_361_ == 0)
{
uint8_t v___x_362_; uint8_t v___x_363_; uint8_t v___x_364_; 
v___x_362_ = lean_byte_array_uget(v_as_352_, v_i_353_);
v___x_363_ = 128;
v___x_364_ = lean_uint8_dec_lt(v___x_362_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
v___x_365_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_362_, v_b_355_);
v___y_357_ = v___x_365_;
goto v___jp_356_;
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_366_ = lean_box(v___x_362_);
lean_inc_ref(v_r_351_);
v___x_367_ = lean_apply_1(v_r_351_, v___x_366_);
v___x_368_ = lean_unbox(v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
v___x_369_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_362_, v_b_355_);
v___y_357_ = v___x_369_;
goto v___jp_356_;
}
else
{
lean_object* v___x_370_; 
v___x_370_ = lean_byte_array_push(v_b_355_, v___x_362_);
v___y_357_ = v___x_370_;
goto v___jp_356_;
}
}
}
else
{
lean_dec_ref(v_r_351_);
return v_b_355_;
}
v___jp_356_:
{
size_t v___x_358_; size_t v___x_359_; 
v___x_358_ = ((size_t)1ULL);
v___x_359_ = lean_usize_add(v_i_353_, v___x_358_);
v_i_353_ = v___x_359_;
v_b_355_ = v___y_357_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0___boxed(lean_object* v_r_371_, lean_object* v_as_372_, lean_object* v_i_373_, lean_object* v_stop_374_, lean_object* v_b_375_){
_start:
{
size_t v_i_boxed_376_; size_t v_stop_boxed_377_; lean_object* v_res_378_; 
v_i_boxed_376_ = lean_unbox_usize(v_i_373_);
lean_dec(v_i_373_);
v_stop_boxed_377_ = lean_unbox_usize(v_stop_374_);
lean_dec(v_stop_374_);
v_res_378_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_371_, v_as_372_, v_i_boxed_376_, v_stop_boxed_377_, v_b_375_);
lean_dec_ref(v_as_372_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode(lean_object* v_r_379_, lean_object* v_s_380_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_381_ = l_ByteArray_empty;
v___x_382_ = lean_string_to_utf8(v_s_380_);
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_byte_array_size(v___x_382_);
v___x_385_ = lean_nat_dec_lt(v___x_383_, v___x_384_);
if (v___x_385_ == 0)
{
lean_dec_ref(v___x_382_);
lean_dec_ref(v_r_379_);
return v___x_381_;
}
else
{
uint8_t v___x_386_; 
v___x_386_ = lean_nat_dec_le(v___x_384_, v___x_384_);
if (v___x_386_ == 0)
{
if (v___x_385_ == 0)
{
lean_dec_ref(v___x_382_);
lean_dec_ref(v_r_379_);
return v___x_381_;
}
else
{
size_t v___x_387_; size_t v___x_388_; lean_object* v___x_389_; 
v___x_387_ = ((size_t)0ULL);
v___x_388_ = lean_usize_of_nat(v___x_384_);
v___x_389_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_379_, v___x_382_, v___x_387_, v___x_388_, v___x_381_);
lean_dec_ref(v___x_382_);
return v___x_389_;
}
}
else
{
size_t v___x_390_; size_t v___x_391_; lean_object* v___x_392_; 
v___x_390_ = ((size_t)0ULL);
v___x_391_ = lean_usize_of_nat(v___x_384_);
v___x_392_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_379_, v___x_382_, v___x_390_, v___x_391_, v___x_381_);
lean_dec_ref(v___x_382_);
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode___boxed(lean_object* v_r_393_, lean_object* v_s_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_Http_URI_EncodedString_encode(v_r_393_, v_s_394_);
lean_dec_ref(v_s_394_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x3f(lean_object* v_r_396_, lean_object* v_ba_397_){
_start:
{
uint8_t v___x_398_; 
lean_inc_ref(v_ba_397_);
v___x_398_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_396_, v_ba_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_dec_ref(v_ba_397_);
v___x_399_ = lean_box(0);
return v___x_399_;
}
else
{
uint8_t v___x_400_; 
v___x_400_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_397_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; 
lean_dec_ref(v_ba_397_);
v___x_401_ = lean_box(0);
return v___x_401_;
}
else
{
lean_object* v___x_402_; 
v___x_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_402_, 0, v_ba_397_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = l_ByteArray_empty;
v___x_405_ = lean_panic_fn(v___x_404_, v_msg_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(lean_object* v_r_406_, lean_object* v_msg_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v_msg_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_409_, lean_object* v_msg_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(v_r_409_, v_msg_410_);
lean_dec_ref(v_r_409_);
return v_res_411_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_415_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2));
v___x_416_ = lean_unsigned_to_nat(12u);
v___x_417_ = lean_unsigned_to_nat(320u);
v___x_418_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1));
v___x_419_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_420_ = l_mkPanicMessageWithDecl(v___x_419_, v___x_418_, v___x_417_, v___x_416_, v___x_415_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x21(lean_object* v_r_421_, lean_object* v_ba_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_421_, v_ba_422_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_obj_once(&l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3, &l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3_once, _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3);
v___x_425_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v___x_424_);
return v___x_425_;
}
else
{
lean_object* v_val_426_; 
v_val_426_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_val_426_);
lean_dec_ref(v___x_423_);
return v_val_426_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f(lean_object* v_r_427_, lean_object* v_s_428_){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_string_to_utf8(v_s_428_);
v___x_430_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_427_, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f___boxed(lean_object* v_r_431_, lean_object* v_s_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_Http_URI_EncodedString_ofString_x3f(v_r_431_, v_s_432_);
lean_dec_ref(v_s_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21(lean_object* v_r_434_, lean_object* v_s_435_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_string_to_utf8(v_s_435_);
v___x_437_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v_r_434_, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21___boxed(lean_object* v_r_438_, lean_object* v_s_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Std_Http_URI_EncodedString_ofString_x21(v_r_438_, v_s_439_);
lean_dec_ref(v_s_439_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg(lean_object* v_ba_441_){
_start:
{
lean_inc_ref(v_ba_441_);
return v_ba_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg___boxed(lean_object* v_ba_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Std_Http_URI_EncodedString_new___redArg(v_ba_442_);
lean_dec_ref(v_ba_442_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new(lean_object* v_r_444_, lean_object* v_ba_445_, lean_object* v_valid_446_, lean_object* v___validEncoding_447_){
_start:
{
lean_inc_ref(v_ba_445_);
return v_ba_445_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___boxed(lean_object* v_r_448_, lean_object* v_ba_449_, lean_object* v_valid_450_, lean_object* v___validEncoding_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Std_Http_URI_EncodedString_new(v_r_448_, v_ba_449_, v_valid_450_, v___validEncoding_451_);
lean_dec_ref(v_ba_449_);
lean_dec_ref(v_r_448_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___lam__0(lean_object* v_es_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = lean_string_from_utf8_unchecked(v_es_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString(lean_object* v_r_456_){
_start:
{
lean_object* v___f_457_; 
v___f_457_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instToString___closed__0));
return v___f_457_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___boxed(lean_object* v_r_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_Http_URI_EncodedString_instToString(v_r_458_);
lean_dec_ref(v_r_458_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedString_decode_spec__0(lean_object* v_len_460_, lean_object* v_rawBytes_461_, lean_object* v_b_462_){
_start:
{
lean_object* v_fst_464_; lean_object* v_snd_465_; lean_object* v_fst_468_; lean_object* v_snd_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_515_; 
v_fst_468_ = lean_ctor_get(v_b_462_, 0);
v_snd_469_ = lean_ctor_get(v_b_462_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_b_462_);
if (v_isSharedCheck_515_ == 0)
{
v___x_471_ = v_b_462_;
v_isShared_472_ = v_isSharedCheck_515_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_snd_469_);
lean_inc(v_fst_468_);
lean_dec(v_b_462_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_515_;
goto v_resetjp_470_;
}
v___jp_463_:
{
lean_object* v___x_466_; 
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v_fst_464_);
lean_ctor_set(v___x_466_, 1, v_snd_465_);
v_b_462_ = v___x_466_;
goto _start;
}
v_resetjp_470_:
{
uint8_t v___x_473_; 
v___x_473_ = lean_nat_dec_lt(v_snd_469_, v_len_460_);
if (v___x_473_ == 0)
{
lean_object* v___x_475_; 
if (v_isShared_472_ == 0)
{
v___x_475_ = v___x_471_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_fst_468_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_snd_469_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
else
{
uint8_t v_percent_477_; uint8_t v_c_478_; uint8_t v___x_483_; 
lean_del_object(v___x_471_);
v_percent_477_ = 37;
v_c_478_ = lean_byte_array_fget(v_rawBytes_461_, v_snd_469_);
v___x_483_ = lean_uint8_dec_eq(v_c_478_, v_percent_477_);
if (v___x_483_ == 0)
{
goto v___jp_479_;
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_add(v_snd_469_, v___x_484_);
v___x_486_ = lean_nat_dec_lt(v___x_485_, v_len_460_);
if (v___x_486_ == 0)
{
lean_dec(v___x_485_);
goto v___jp_479_;
}
else
{
uint8_t v_h1_487_; lean_object* v___x_488_; 
v_h1_487_ = lean_byte_array_fget(v_rawBytes_461_, v___x_485_);
lean_dec(v___x_485_);
v___x_488_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_h1_487_);
if (lean_obj_tag(v___x_488_) == 1)
{
lean_object* v_val_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v_val_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_val_489_);
lean_dec_ref(v___x_488_);
v___x_490_ = lean_unsigned_to_nat(2u);
v___x_491_ = lean_nat_add(v_snd_469_, v___x_490_);
v___x_492_ = lean_nat_dec_lt(v___x_491_, v_len_460_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec(v_val_489_);
lean_dec(v_snd_469_);
v___x_493_ = lean_byte_array_push(v_fst_468_, v_c_478_);
v___x_494_ = lean_byte_array_push(v___x_493_, v_h1_487_);
v_fst_464_ = v___x_494_;
v_snd_465_ = v___x_491_;
goto v___jp_463_;
}
else
{
uint8_t v_h2_495_; lean_object* v___x_496_; 
v_h2_495_ = lean_byte_array_fget(v_rawBytes_461_, v___x_491_);
lean_dec(v___x_491_);
v___x_496_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_h2_495_);
if (lean_obj_tag(v___x_496_) == 1)
{
lean_object* v_val_497_; uint8_t v___x_498_; uint8_t v___x_499_; uint8_t v___x_500_; uint8_t v___x_501_; uint8_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_val_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_val_497_);
lean_dec_ref(v___x_496_);
v___x_498_ = 4;
v___x_499_ = lean_unbox(v_val_489_);
lean_dec(v_val_489_);
v___x_500_ = lean_uint8_shift_left(v___x_499_, v___x_498_);
v___x_501_ = lean_unbox(v_val_497_);
lean_dec(v_val_497_);
v___x_502_ = lean_uint8_add(v___x_500_, v___x_501_);
v___x_503_ = lean_byte_array_push(v_fst_468_, v___x_502_);
v___x_504_ = lean_unsigned_to_nat(3u);
v___x_505_ = lean_nat_add(v_snd_469_, v___x_504_);
lean_dec(v_snd_469_);
v_fst_464_ = v___x_503_;
v_snd_465_ = v___x_505_;
goto v___jp_463_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec(v___x_496_);
lean_dec(v_val_489_);
v___x_506_ = lean_byte_array_push(v_fst_468_, v_c_478_);
v___x_507_ = lean_byte_array_push(v___x_506_, v_h1_487_);
v___x_508_ = lean_byte_array_push(v___x_507_, v_h2_495_);
v___x_509_ = lean_unsigned_to_nat(3u);
v___x_510_ = lean_nat_add(v_snd_469_, v___x_509_);
lean_dec(v_snd_469_);
v_fst_464_ = v___x_508_;
v_snd_465_ = v___x_510_;
goto v___jp_463_;
}
}
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v___x_488_);
v___x_511_ = lean_byte_array_push(v_fst_468_, v_c_478_);
v___x_512_ = lean_byte_array_push(v___x_511_, v_h1_487_);
v___x_513_ = lean_unsigned_to_nat(2u);
v___x_514_ = lean_nat_add(v_snd_469_, v___x_513_);
lean_dec(v_snd_469_);
v_fst_464_ = v___x_512_;
v_snd_465_ = v___x_514_;
goto v___jp_463_;
}
}
}
v___jp_479_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = lean_byte_array_push(v_fst_468_, v_c_478_);
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = lean_nat_add(v_snd_469_, v___x_481_);
lean_dec(v_snd_469_);
v_fst_464_ = v___x_480_;
v_snd_465_ = v___x_482_;
goto v___jp_463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedString_decode_spec__0___boxed(lean_object* v_len_516_, lean_object* v_rawBytes_517_, lean_object* v_b_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedString_decode_spec__0(v_len_516_, v_rawBytes_517_, v_b_518_);
lean_dec_ref(v_rawBytes_517_);
lean_dec(v_len_516_);
return v_res_519_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0(void){
_start:
{
lean_object* v_i_520_; lean_object* v_decoded_521_; lean_object* v___x_522_; 
v_i_520_ = lean_unsigned_to_nat(0u);
v_decoded_521_ = l_ByteArray_empty;
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v_decoded_521_);
lean_ctor_set(v___x_522_, 1, v_i_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg(lean_object* v_es_523_){
_start:
{
lean_object* v_len_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v_fst_527_; uint8_t v___x_528_; 
v_len_524_ = lean_byte_array_size(v_es_523_);
v___x_525_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_526_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedString_decode_spec__0(v_len_524_, v_es_523_, v___x_525_);
v_fst_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_fst_527_);
lean_dec_ref(v___x_526_);
v___x_528_ = lean_string_validate_utf8(v_fst_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
lean_dec(v_fst_527_);
v___x_529_ = lean_box(0);
return v___x_529_;
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_string_from_utf8_unchecked(v_fst_527_);
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg___boxed(lean_object* v_es_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_532_);
lean_dec_ref(v_es_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode(lean_object* v_r_534_, lean_object* v_es_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___boxed(lean_object* v_r_537_, lean_object* v_es_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Std_Http_URI_EncodedString_decode(v_r_537_, v_es_538_);
lean_dec_ref(v_es_538_);
lean_dec_ref(v_r_537_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___lam__0(lean_object* v_es_540_, lean_object* v_n_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = lean_string_from_utf8_unchecked(v_es_540_);
v___x_543_ = l_String_quote(v___x_542_);
v___x_544_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed(lean_object* v_es_545_, lean_object* v_n_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_Http_URI_EncodedString_instRepr___lam__0(v_es_545_, v_n_546_);
lean_dec(v_n_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr(lean_object* v_r_549_){
_start:
{
lean_object* v___f_550_; 
v___f_550_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___closed__0));
return v___f_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___boxed(lean_object* v_r_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_Http_URI_EncodedString_instRepr(v_r_551_);
lean_dec_ref(v_r_551_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq(lean_object* v_r_553_){
_start:
{
lean_object* v___f_554_; 
v___f_554_ = lean_alloc_closure((void*)(l_ByteArray_instDecidableEq___boxed), 2, 0);
return v___f_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___boxed(lean_object* v_r_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_Http_URI_EncodedString_instBEq(v_r_555_);
lean_dec_ref(v_r_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable(lean_object* v_r_558_){
_start:
{
lean_object* v___f_559_; 
v___f_559_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___closed__0));
return v___f_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___boxed(lean_object* v_r_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_Http_URI_EncodedString_instHashable(v_r_560_);
lean_dec_ref(v_r_560_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty(lean_object* v_r_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_ByteArray_empty;
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___boxed(lean_object* v_r_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Std_Http_URI_EncodedQueryString_empty(v_r_564_);
lean_dec_ref(v_r_564_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited(lean_object* v_r_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_ByteArray_empty;
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___boxed(lean_object* v_r_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Std_Http_URI_EncodedQueryString_instInhabited(v_r_568_);
lean_dec_ref(v_r_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(lean_object* v_s_570_, uint8_t v_c_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = lean_byte_array_push(v_s_570_, v_c_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg___boxed(lean_object* v_s_573_, lean_object* v_c_574_){
_start:
{
uint8_t v_c_boxed_575_; lean_object* v_res_576_; 
v_c_boxed_575_ = lean_unbox(v_c_574_);
v_res_576_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(v_s_573_, v_c_boxed_575_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(lean_object* v_r_577_, lean_object* v_s_578_, uint8_t v_c_579_, lean_object* v_h_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = lean_byte_array_push(v_s_578_, v_c_579_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___boxed(lean_object* v_r_582_, lean_object* v_s_583_, lean_object* v_c_584_, lean_object* v_h_585_){
_start:
{
uint8_t v_c_boxed_586_; lean_object* v_res_587_; 
v_c_boxed_586_ = lean_unbox(v_c_584_);
v_res_587_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(v_r_582_, v_s_583_, v_c_boxed_586_, v_h_585_);
lean_dec_ref(v_r_582_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(lean_object* v_ba_588_, lean_object* v_r_589_){
_start:
{
uint8_t v___x_590_; 
lean_inc_ref(v_ba_588_);
v___x_590_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_589_, v_ba_588_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
lean_dec_ref(v_ba_588_);
v___x_591_ = lean_box(0);
return v___x_591_;
}
else
{
uint8_t v___x_592_; 
v___x_592_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_588_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
lean_dec_ref(v_ba_588_);
v___x_593_ = lean_box(0);
return v___x_593_;
}
else
{
lean_object* v___x_594_; 
v___x_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_594_, 0, v_ba_588_);
return v___x_594_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_595_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = l_ByteArray_empty;
v___x_597_ = lean_panic_fn(v___x_596_, v_msg_595_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(lean_object* v_r_598_, lean_object* v_msg_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v_msg_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_601_, lean_object* v_msg_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(v_r_601_, v_msg_602_);
lean_dec_ref(v_r_601_);
return v_res_603_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_606_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1));
v___x_607_ = lean_unsigned_to_nat(12u);
v___x_608_ = lean_unsigned_to_nat(438u);
v___x_609_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0));
v___x_610_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_611_ = l_mkPanicMessageWithDecl(v___x_610_, v___x_609_, v___x_608_, v___x_607_, v___x_606_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(lean_object* v_ba_612_, lean_object* v_r_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_612_, v_r_613_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_obj_once(&l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2, &l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2_once, _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2);
v___x_616_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v___x_615_);
return v___x_616_;
}
else
{
lean_object* v_val_617_; 
v_val_617_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_val_617_);
lean_dec_ref(v___x_614_);
return v_val_617_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f(lean_object* v_s_618_, lean_object* v_r_619_){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_string_to_utf8(v_s_618_);
v___x_621_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v___x_620_, v_r_619_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f___boxed(lean_object* v_s_622_, lean_object* v_r_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_622_, v_r_623_);
lean_dec_ref(v_s_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21(lean_object* v_s_625_, lean_object* v_r_626_){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_string_to_utf8(v_s_625_);
v___x_628_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v___x_627_, v_r_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21___boxed(lean_object* v_s_629_, lean_object* v_r_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Std_Http_URI_EncodedQueryString_ofString_x21(v_s_629_, v_r_630_);
lean_dec_ref(v_s_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg(lean_object* v_ba_632_){
_start:
{
lean_inc_ref(v_ba_632_);
return v_ba_632_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg___boxed(lean_object* v_ba_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_Http_URI_EncodedQueryString_new___redArg(v_ba_633_);
lean_dec_ref(v_ba_633_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new(lean_object* v_r_635_, lean_object* v_ba_636_, lean_object* v_valid_637_, lean_object* v___validEncoding_638_){
_start:
{
lean_inc_ref(v_ba_636_);
return v_ba_636_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___boxed(lean_object* v_r_639_, lean_object* v_ba_640_, lean_object* v_valid_641_, lean_object* v___validEncoding_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Std_Http_URI_EncodedQueryString_new(v_r_639_, v_ba_640_, v_valid_641_, v___validEncoding_642_);
lean_dec_ref(v_ba_640_);
lean_dec_ref(v_r_639_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(uint8_t v_b_644_, lean_object* v_s_645_){
_start:
{
uint8_t v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; uint8_t v___x_649_; uint8_t v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; uint8_t v___x_653_; uint8_t v___x_654_; lean_object* v_ba_655_; 
v___x_646_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__0, &l_Std_Http_URI_isEncodedChar___closed__0_once, _init_l_Std_Http_URI_isEncodedChar___closed__0);
v___x_647_ = lean_byte_array_push(v_s_645_, v___x_646_);
v___x_648_ = 4;
v___x_649_ = lean_uint8_shift_right(v_b_644_, v___x_648_);
v___x_650_ = l_Std_Http_URI_hexDigit(v___x_649_);
v___x_651_ = lean_byte_array_push(v___x_647_, v___x_650_);
v___x_652_ = 15;
v___x_653_ = lean_uint8_land(v_b_644_, v___x_652_);
v___x_654_ = l_Std_Http_URI_hexDigit(v___x_653_);
v_ba_655_ = lean_byte_array_push(v___x_651_, v___x_654_);
return v_ba_655_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg___boxed(lean_object* v_b_656_, lean_object* v_s_657_){
_start:
{
uint8_t v_b_boxed_658_; lean_object* v_res_659_; 
v_b_boxed_658_ = lean_unbox(v_b_656_);
v_res_659_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_boxed_658_, v_s_657_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(lean_object* v_r_660_, uint8_t v_b_661_, lean_object* v_s_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_661_, v_s_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___boxed(lean_object* v_r_664_, lean_object* v_b_665_, lean_object* v_s_666_){
_start:
{
uint8_t v_b_boxed_667_; lean_object* v_res_668_; 
v_b_boxed_667_ = lean_unbox(v_b_665_);
v_res_668_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(v_r_664_, v_b_boxed_667_, v_s_666_);
lean_dec_ref(v_r_664_);
return v_res_668_;
}
}
static uint8_t _init_l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0(void){
_start:
{
uint32_t v___x_669_; uint8_t v___x_670_; 
v___x_669_ = 32;
v___x_670_ = lean_uint32_to_uint8(v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(lean_object* v_r_671_, lean_object* v_as_672_, size_t v_i_673_, size_t v_stop_674_, lean_object* v_b_675_){
_start:
{
lean_object* v___y_677_; uint8_t v___x_681_; 
v___x_681_ = lean_usize_dec_eq(v_i_673_, v_stop_674_);
if (v___x_681_ == 0)
{
uint8_t v___x_682_; uint8_t v___x_689_; uint8_t v___x_690_; 
v___x_682_ = lean_byte_array_uget(v_as_672_, v_i_673_);
v___x_689_ = 128;
v___x_690_ = lean_uint8_dec_lt(v___x_682_, v___x_689_);
if (v___x_690_ == 0)
{
goto v___jp_683_;
}
else
{
lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_691_ = lean_box(v___x_682_);
lean_inc_ref(v_r_671_);
v___x_692_ = lean_apply_1(v_r_671_, v___x_691_);
v___x_693_ = lean_unbox(v___x_692_);
if (v___x_693_ == 0)
{
goto v___jp_683_;
}
else
{
lean_object* v___x_694_; 
v___x_694_ = lean_byte_array_push(v_b_675_, v___x_682_);
v___y_677_ = v___x_694_;
goto v___jp_676_;
}
}
v___jp_683_:
{
uint8_t v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_uint8_once(&l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0, &l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0_once, _init_l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0);
v___x_685_ = lean_uint8_dec_eq(v___x_682_, v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; 
v___x_686_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v___x_682_, v_b_675_);
v___y_677_ = v___x_686_;
goto v___jp_676_;
}
else
{
uint8_t v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_688_ = lean_byte_array_push(v_b_675_, v___x_687_);
v___y_677_ = v___x_688_;
goto v___jp_676_;
}
}
}
else
{
lean_dec_ref(v_r_671_);
return v_b_675_;
}
v___jp_676_:
{
size_t v___x_678_; size_t v___x_679_; 
v___x_678_ = ((size_t)1ULL);
v___x_679_ = lean_usize_add(v_i_673_, v___x_678_);
v_i_673_ = v___x_679_;
v_b_675_ = v___y_677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___boxed(lean_object* v_r_695_, lean_object* v_as_696_, lean_object* v_i_697_, lean_object* v_stop_698_, lean_object* v_b_699_){
_start:
{
size_t v_i_boxed_700_; size_t v_stop_boxed_701_; lean_object* v_res_702_; 
v_i_boxed_700_ = lean_unbox_usize(v_i_697_);
lean_dec(v_i_697_);
v_stop_boxed_701_ = lean_unbox_usize(v_stop_698_);
lean_dec(v_stop_698_);
v_res_702_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_695_, v_as_696_, v_i_boxed_700_, v_stop_boxed_701_, v_b_699_);
lean_dec_ref(v_as_696_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode(lean_object* v_s_703_, lean_object* v_r_704_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_705_ = l_ByteArray_empty;
v___x_706_ = lean_string_to_utf8(v_s_703_);
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = lean_byte_array_size(v___x_706_);
v___x_709_ = lean_nat_dec_lt(v___x_707_, v___x_708_);
if (v___x_709_ == 0)
{
lean_dec_ref(v___x_706_);
lean_dec_ref(v_r_704_);
return v___x_705_;
}
else
{
uint8_t v___x_710_; 
v___x_710_ = lean_nat_dec_le(v___x_708_, v___x_708_);
if (v___x_710_ == 0)
{
if (v___x_709_ == 0)
{
lean_dec_ref(v___x_706_);
lean_dec_ref(v_r_704_);
return v___x_705_;
}
else
{
size_t v___x_711_; size_t v___x_712_; lean_object* v___x_713_; 
v___x_711_ = ((size_t)0ULL);
v___x_712_ = lean_usize_of_nat(v___x_708_);
v___x_713_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_704_, v___x_706_, v___x_711_, v___x_712_, v___x_705_);
lean_dec_ref(v___x_706_);
return v___x_713_;
}
}
else
{
size_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; 
v___x_714_ = ((size_t)0ULL);
v___x_715_ = lean_usize_of_nat(v___x_708_);
v___x_716_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_704_, v___x_706_, v___x_714_, v___x_715_, v___x_705_);
lean_dec_ref(v___x_706_);
return v___x_716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode___boxed(lean_object* v_s_717_, lean_object* v_r_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_717_, v_r_718_);
lean_dec_ref(v_s_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___redArg(lean_object* v_es_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = lean_string_from_utf8_unchecked(v_es_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString(lean_object* v_r_722_, lean_object* v_es_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = lean_string_from_utf8_unchecked(v_es_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___boxed(lean_object* v_r_725_, lean_object* v_es_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Std_Http_URI_EncodedQueryString_toString(v_r_725_, v_es_726_);
lean_dec_ref(v_r_725_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(lean_object* v_len_728_, lean_object* v_rawBytes_729_, lean_object* v_b_730_){
_start:
{
lean_object* v_fst_732_; lean_object* v_snd_733_; lean_object* v_fst_736_; lean_object* v_snd_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_789_; 
v_fst_736_ = lean_ctor_get(v_b_730_, 0);
v_snd_737_ = lean_ctor_get(v_b_730_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_b_730_);
if (v_isSharedCheck_789_ == 0)
{
v___x_739_ = v_b_730_;
v_isShared_740_ = v_isSharedCheck_789_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_snd_737_);
lean_inc(v_fst_736_);
lean_dec(v_b_730_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_789_;
goto v_resetjp_738_;
}
v___jp_731_:
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v_fst_732_);
lean_ctor_set(v___x_734_, 1, v_snd_733_);
v_b_730_ = v___x_734_;
goto _start;
}
v_resetjp_738_:
{
uint8_t v___x_741_; 
v___x_741_ = lean_nat_dec_lt(v_snd_737_, v_len_728_);
if (v___x_741_ == 0)
{
lean_object* v___x_743_; 
if (v_isShared_740_ == 0)
{
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_fst_736_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_snd_737_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
else
{
uint8_t v_plus_745_; uint8_t v_c_746_; uint8_t v___x_751_; 
lean_del_object(v___x_739_);
v_plus_745_ = 43;
v_c_746_ = lean_byte_array_fget(v_rawBytes_729_, v_snd_737_);
v___x_751_ = lean_uint8_dec_eq(v_c_746_, v_plus_745_);
if (v___x_751_ == 0)
{
uint8_t v_percent_752_; uint8_t v___x_753_; 
v_percent_752_ = 37;
v___x_753_ = lean_uint8_dec_eq(v_c_746_, v_percent_752_);
if (v___x_753_ == 0)
{
goto v___jp_747_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_nat_add(v_snd_737_, v___x_754_);
v___x_756_ = lean_nat_dec_lt(v___x_755_, v_len_728_);
if (v___x_756_ == 0)
{
lean_dec(v___x_755_);
goto v___jp_747_;
}
else
{
uint8_t v_h1_757_; lean_object* v___x_758_; 
v_h1_757_ = lean_byte_array_fget(v_rawBytes_729_, v___x_755_);
lean_dec(v___x_755_);
v___x_758_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_h1_757_);
if (lean_obj_tag(v___x_758_) == 1)
{
lean_object* v_val_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_val_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_val_759_);
lean_dec_ref(v___x_758_);
v___x_760_ = lean_unsigned_to_nat(2u);
v___x_761_ = lean_nat_add(v_snd_737_, v___x_760_);
v___x_762_ = lean_nat_dec_lt(v___x_761_, v_len_728_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec(v_val_759_);
lean_dec(v_snd_737_);
v___x_763_ = lean_byte_array_push(v_fst_736_, v_c_746_);
v___x_764_ = lean_byte_array_push(v___x_763_, v_h1_757_);
v_fst_732_ = v___x_764_;
v_snd_733_ = v___x_761_;
goto v___jp_731_;
}
else
{
uint8_t v_h2_765_; lean_object* v___x_766_; 
v_h2_765_ = lean_byte_array_fget(v_rawBytes_729_, v___x_761_);
lean_dec(v___x_761_);
v___x_766_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_h2_765_);
if (lean_obj_tag(v___x_766_) == 1)
{
lean_object* v_val_767_; uint8_t v___x_768_; uint8_t v___x_769_; uint8_t v___x_770_; uint8_t v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_val_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_val_767_);
lean_dec_ref(v___x_766_);
v___x_768_ = 4;
v___x_769_ = lean_unbox(v_val_759_);
lean_dec(v_val_759_);
v___x_770_ = lean_uint8_shift_left(v___x_769_, v___x_768_);
v___x_771_ = lean_unbox(v_val_767_);
lean_dec(v_val_767_);
v___x_772_ = lean_uint8_add(v___x_770_, v___x_771_);
v___x_773_ = lean_byte_array_push(v_fst_736_, v___x_772_);
v___x_774_ = lean_unsigned_to_nat(3u);
v___x_775_ = lean_nat_add(v_snd_737_, v___x_774_);
lean_dec(v_snd_737_);
v_fst_732_ = v___x_773_;
v_snd_733_ = v___x_775_;
goto v___jp_731_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec(v___x_766_);
lean_dec(v_val_759_);
v___x_776_ = lean_byte_array_push(v_fst_736_, v_c_746_);
v___x_777_ = lean_byte_array_push(v___x_776_, v_h1_757_);
v___x_778_ = lean_byte_array_push(v___x_777_, v_h2_765_);
v___x_779_ = lean_unsigned_to_nat(3u);
v___x_780_ = lean_nat_add(v_snd_737_, v___x_779_);
lean_dec(v_snd_737_);
v_fst_732_ = v___x_778_;
v_snd_733_ = v___x_780_;
goto v___jp_731_;
}
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec(v___x_758_);
v___x_781_ = lean_byte_array_push(v_fst_736_, v_c_746_);
v___x_782_ = lean_byte_array_push(v___x_781_, v_h1_757_);
v___x_783_ = lean_unsigned_to_nat(2u);
v___x_784_ = lean_nat_add(v_snd_737_, v___x_783_);
lean_dec(v_snd_737_);
v_fst_732_ = v___x_782_;
v_snd_733_ = v___x_784_;
goto v___jp_731_;
}
}
}
}
else
{
uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_785_ = 32;
v___x_786_ = lean_byte_array_push(v_fst_736_, v___x_785_);
v___x_787_ = lean_unsigned_to_nat(1u);
v___x_788_ = lean_nat_add(v_snd_737_, v___x_787_);
lean_dec(v_snd_737_);
v_fst_732_ = v___x_786_;
v_snd_733_ = v___x_788_;
goto v___jp_731_;
}
v___jp_747_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = lean_byte_array_push(v_fst_736_, v_c_746_);
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_nat_add(v_snd_737_, v___x_749_);
lean_dec(v_snd_737_);
v_fst_732_ = v___x_748_;
v_snd_733_ = v___x_750_;
goto v___jp_731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___boxed(lean_object* v_len_790_, lean_object* v_rawBytes_791_, lean_object* v_b_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(v_len_790_, v_rawBytes_791_, v_b_792_);
lean_dec_ref(v_rawBytes_791_);
lean_dec(v_len_790_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg(lean_object* v_es_794_){
_start:
{
lean_object* v_len_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_fst_798_; uint8_t v___x_799_; 
v_len_795_ = lean_byte_array_size(v_es_794_);
v___x_796_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_797_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(v_len_795_, v_es_794_, v___x_796_);
v_fst_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_fst_798_);
lean_dec_ref(v___x_797_);
v___x_799_ = lean_string_validate_utf8(v_fst_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; 
lean_dec(v_fst_798_);
v___x_800_ = lean_box(0);
return v___x_800_;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_string_from_utf8_unchecked(v_fst_798_);
v___x_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg___boxed(lean_object* v_es_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_803_);
lean_dec_ref(v_es_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode(lean_object* v_r_805_, lean_object* v_es_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___boxed(lean_object* v_r_808_, lean_object* v_es_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_Http_URI_EncodedQueryString_decode(v_r_808_, v_es_809_);
lean_dec_ref(v_es_809_);
lean_dec_ref(v_r_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringEncodedQueryString(lean_object* v_r_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = lean_alloc_closure((void*)(l_Std_Http_URI_EncodedQueryString_toString___boxed), 2, 1);
lean_closure_set(v___x_812_, 0, v_r_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString(lean_object* v_r_813_){
_start:
{
lean_object* v___f_814_; 
v___f_814_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___closed__0));
return v___f_814_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___boxed(lean_object* v_r_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_Http_URI_instReprEncodedQueryString(v_r_815_);
lean_dec_ref(v_r_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString(lean_object* v_r_817_){
_start:
{
lean_object* v___f_818_; 
v___f_818_ = lean_alloc_closure((void*)(l_ByteArray_instDecidableEq___boxed), 2, 0);
return v___f_818_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___boxed(lean_object* v_r_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Std_Http_URI_instBEqEncodedQueryString(v_r_819_);
lean_dec_ref(v_r_819_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString(lean_object* v_r_821_){
_start:
{
lean_object* v___f_822_; 
v___f_822_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___closed__0));
return v___f_822_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___boxed(lean_object* v_r_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_Http_URI_instHashableEncodedQueryString(v_r_823_);
lean_dec_ref(v_r_823_);
return v_res_824_;
}
}
static uint64_t _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1(void){
_start:
{
lean_object* v___x_831_; uint64_t v___x_832_; 
v___x_831_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__0));
v___x_832_ = lean_byte_array_hash(v___x_831_);
return v___x_832_;
}
}
static lean_object* _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2));
v___x_840_ = lean_byte_array_size(v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT uint64_t l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0(lean_object* v_x_841_){
_start:
{
if (lean_obj_tag(v_x_841_) == 0)
{
uint64_t v___x_842_; 
v___x_842_ = lean_uint64_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1, &l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1);
return v___x_842_;
}
else
{
lean_object* v_val_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; lean_object* v___x_849_; uint64_t v___x_850_; 
v_val_843_ = lean_ctor_get(v_x_841_, 0);
v___x_844_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2));
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_obj_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3, &l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3);
v___x_847_ = lean_byte_array_size(v_val_843_);
v___x_848_ = 0;
v___x_849_ = lean_byte_array_copy_slice(v_val_843_, v___x_845_, v___x_844_, v___x_846_, v___x_847_, v___x_848_);
v___x_850_ = lean_byte_array_hash(v___x_849_);
lean_dec_ref(v___x_849_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___boxed(lean_object* v_x_851_){
_start:
{
uint64_t v_res_852_; lean_object* v_r_853_; 
v_res_852_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0(v_x_851_);
lean_dec(v_x_851_);
v_r_853_ = lean_box_uint64(v_res_852_);
return v_r_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString(lean_object* v_r_855_){
_start:
{
lean_object* v___f_856_; 
v___f_856_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___closed__0));
return v___f_856_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___boxed(lean_object* v_r_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Std_Http_URI_instHashableOptionEncodedQueryString(v_r_857_);
lean_dec_ref(v_r_857_);
return v_res_858_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0(void){
_start:
{
uint32_t v___x_859_; uint8_t v___x_860_; 
v___x_859_ = 58;
v___x_860_ = lean_uint32_to_uint8(v___x_859_);
return v___x_860_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1(void){
_start:
{
uint32_t v___x_861_; uint8_t v___x_862_; 
v___x_861_ = 64;
v___x_862_ = lean_uint32_to_uint8(v___x_861_);
return v___x_862_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2(void){
_start:
{
uint32_t v___x_863_; uint8_t v___x_864_; 
v___x_863_ = 38;
v___x_864_ = lean_uint32_to_uint8(v___x_863_);
return v___x_864_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3(void){
_start:
{
uint32_t v___x_865_; uint8_t v___x_866_; 
v___x_865_ = 39;
v___x_866_ = lean_uint32_to_uint8(v___x_865_);
return v___x_866_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4(void){
_start:
{
uint32_t v___x_867_; uint8_t v___x_868_; 
v___x_867_ = 40;
v___x_868_ = lean_uint32_to_uint8(v___x_867_);
return v___x_868_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5(void){
_start:
{
uint32_t v___x_869_; uint8_t v___x_870_; 
v___x_869_ = 41;
v___x_870_ = lean_uint32_to_uint8(v___x_869_);
return v___x_870_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6(void){
_start:
{
uint32_t v___x_871_; uint8_t v___x_872_; 
v___x_871_ = 42;
v___x_872_ = lean_uint32_to_uint8(v___x_871_);
return v___x_872_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7(void){
_start:
{
uint32_t v___x_873_; uint8_t v___x_874_; 
v___x_873_ = 44;
v___x_874_ = lean_uint32_to_uint8(v___x_873_);
return v___x_874_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8(void){
_start:
{
uint32_t v___x_875_; uint8_t v___x_876_; 
v___x_875_ = 59;
v___x_876_ = lean_uint32_to_uint8(v___x_875_);
return v___x_876_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9(void){
_start:
{
uint32_t v___x_877_; uint8_t v___x_878_; 
v___x_877_ = 61;
v___x_878_ = lean_uint32_to_uint8(v___x_877_);
return v___x_878_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10(void){
_start:
{
uint32_t v___x_879_; uint8_t v___x_880_; 
v___x_879_ = 33;
v___x_880_ = lean_uint32_to_uint8(v___x_879_);
return v___x_880_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11(void){
_start:
{
uint32_t v___x_881_; uint8_t v___x_882_; 
v___x_881_ = 36;
v___x_882_ = lean_uint32_to_uint8(v___x_881_);
return v___x_882_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12(void){
_start:
{
uint32_t v___x_883_; uint8_t v___x_884_; 
v___x_883_ = 95;
v___x_884_ = lean_uint32_to_uint8(v___x_883_);
return v___x_884_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13(void){
_start:
{
uint32_t v___x_885_; uint8_t v___x_886_; 
v___x_885_ = 126;
v___x_886_ = lean_uint32_to_uint8(v___x_885_);
return v___x_886_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14(void){
_start:
{
uint32_t v___x_887_; uint8_t v___x_888_; 
v___x_887_ = 45;
v___x_888_ = lean_uint32_to_uint8(v___x_887_);
return v___x_888_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15(void){
_start:
{
uint32_t v___x_889_; uint8_t v___x_890_; 
v___x_889_ = 46;
v___x_890_ = lean_uint32_to_uint8(v___x_889_);
return v___x_890_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16(void){
_start:
{
uint32_t v___x_891_; uint8_t v___x_892_; 
v___x_891_ = 90;
v___x_892_ = lean_uint32_to_uint8(v___x_891_);
return v___x_892_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17(void){
_start:
{
uint32_t v___x_893_; uint8_t v___x_894_; 
v___x_893_ = 122;
v___x_894_ = lean_uint32_to_uint8(v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0(uint8_t v___y_895_){
_start:
{
uint8_t v___y_897_; uint8_t v___y_903_; uint8_t v___y_923_; uint8_t v___y_929_; uint8_t v___y_935_; uint8_t v___y_941_; uint8_t v___y_947_; uint8_t v___x_952_; uint8_t v___x_953_; 
v___x_952_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_953_ = lean_uint8_dec_le(v___x_952_, v___y_895_);
if (v___x_953_ == 0)
{
v___y_947_ = v___x_953_;
goto v___jp_946_;
}
else
{
uint8_t v___x_954_; uint8_t v___x_955_; 
v___x_954_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_955_ = lean_uint8_dec_le(v___y_895_, v___x_954_);
v___y_947_ = v___x_955_;
goto v___jp_946_;
}
v___jp_896_:
{
if (v___y_897_ == 0)
{
uint8_t v___x_898_; uint8_t v___x_899_; 
v___x_898_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_899_ = lean_uint8_dec_eq(v___y_895_, v___x_898_);
if (v___x_899_ == 0)
{
uint8_t v___x_900_; uint8_t v___x_901_; 
v___x_900_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_901_ = lean_uint8_dec_eq(v___y_895_, v___x_900_);
return v___x_901_;
}
else
{
return v___x_899_;
}
}
else
{
return v___y_897_;
}
}
v___jp_902_:
{
if (v___y_903_ == 0)
{
uint8_t v___x_904_; uint8_t v___x_905_; 
v___x_904_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_905_ = lean_uint8_dec_eq(v___y_895_, v___x_904_);
if (v___x_905_ == 0)
{
uint8_t v___x_906_; uint8_t v___x_907_; 
v___x_906_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_907_ = lean_uint8_dec_eq(v___y_895_, v___x_906_);
if (v___x_907_ == 0)
{
uint8_t v___x_908_; uint8_t v___x_909_; 
v___x_908_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_909_ = lean_uint8_dec_eq(v___y_895_, v___x_908_);
if (v___x_909_ == 0)
{
uint8_t v___x_910_; uint8_t v___x_911_; 
v___x_910_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_911_ = lean_uint8_dec_eq(v___y_895_, v___x_910_);
if (v___x_911_ == 0)
{
uint8_t v___x_912_; uint8_t v___x_913_; 
v___x_912_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_913_ = lean_uint8_dec_eq(v___y_895_, v___x_912_);
if (v___x_913_ == 0)
{
uint8_t v___x_914_; uint8_t v___x_915_; 
v___x_914_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_915_ = lean_uint8_dec_eq(v___y_895_, v___x_914_);
if (v___x_915_ == 0)
{
uint8_t v___x_916_; uint8_t v___x_917_; 
v___x_916_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_917_ = lean_uint8_dec_eq(v___y_895_, v___x_916_);
if (v___x_917_ == 0)
{
uint8_t v___x_918_; uint8_t v___x_919_; 
v___x_918_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_919_ = lean_uint8_dec_eq(v___y_895_, v___x_918_);
if (v___x_919_ == 0)
{
uint8_t v___x_920_; uint8_t v___x_921_; 
v___x_920_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_921_ = lean_uint8_dec_eq(v___y_895_, v___x_920_);
v___y_897_ = v___x_921_;
goto v___jp_896_;
}
else
{
v___y_897_ = v___x_919_;
goto v___jp_896_;
}
}
else
{
v___y_897_ = v___x_917_;
goto v___jp_896_;
}
}
else
{
v___y_897_ = v___x_915_;
goto v___jp_896_;
}
}
else
{
v___y_897_ = v___x_913_;
goto v___jp_896_;
}
}
else
{
v___y_897_ = v___x_911_;
goto v___jp_896_;
}
}
else
{
v___y_897_ = v___x_909_;
goto v___jp_896_;
}
}
else
{
v___y_897_ = v___x_907_;
goto v___jp_896_;
}
}
else
{
v___y_897_ = v___x_905_;
goto v___jp_896_;
}
}
else
{
return v___y_903_;
}
}
v___jp_922_:
{
if (v___y_923_ == 0)
{
uint8_t v___x_924_; uint8_t v___x_925_; 
v___x_924_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_925_ = lean_uint8_dec_eq(v___y_895_, v___x_924_);
if (v___x_925_ == 0)
{
uint8_t v___x_926_; uint8_t v___x_927_; 
v___x_926_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_927_ = lean_uint8_dec_eq(v___y_895_, v___x_926_);
v___y_903_ = v___x_927_;
goto v___jp_902_;
}
else
{
v___y_903_ = v___x_925_;
goto v___jp_902_;
}
}
else
{
return v___y_923_;
}
}
v___jp_928_:
{
if (v___y_929_ == 0)
{
uint8_t v___x_930_; uint8_t v___x_931_; 
v___x_930_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_931_ = lean_uint8_dec_eq(v___y_895_, v___x_930_);
if (v___x_931_ == 0)
{
uint8_t v___x_932_; uint8_t v___x_933_; 
v___x_932_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_933_ = lean_uint8_dec_eq(v___y_895_, v___x_932_);
v___y_923_ = v___x_933_;
goto v___jp_922_;
}
else
{
v___y_923_ = v___x_931_;
goto v___jp_922_;
}
}
else
{
return v___y_929_;
}
}
v___jp_934_:
{
if (v___y_935_ == 0)
{
uint8_t v___x_936_; uint8_t v___x_937_; 
v___x_936_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_937_ = lean_uint8_dec_eq(v___y_895_, v___x_936_);
if (v___x_937_ == 0)
{
uint8_t v___x_938_; uint8_t v___x_939_; 
v___x_938_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_939_ = lean_uint8_dec_eq(v___y_895_, v___x_938_);
v___y_929_ = v___x_939_;
goto v___jp_928_;
}
else
{
v___y_929_ = v___x_937_;
goto v___jp_928_;
}
}
else
{
return v___y_935_;
}
}
v___jp_940_:
{
if (v___y_941_ == 0)
{
uint8_t v___x_942_; uint8_t v___x_943_; 
v___x_942_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_943_ = lean_uint8_dec_le(v___x_942_, v___y_895_);
if (v___x_943_ == 0)
{
v___y_935_ = v___x_943_;
goto v___jp_934_;
}
else
{
uint8_t v___x_944_; uint8_t v___x_945_; 
v___x_944_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_945_ = lean_uint8_dec_le(v___y_895_, v___x_944_);
v___y_935_ = v___x_945_;
goto v___jp_934_;
}
}
else
{
return v___y_941_;
}
}
v___jp_946_:
{
if (v___y_947_ == 0)
{
uint8_t v___x_948_; uint8_t v___x_949_; 
v___x_948_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_949_ = lean_uint8_dec_le(v___x_948_, v___y_895_);
if (v___x_949_ == 0)
{
v___y_941_ = v___x_949_;
goto v___jp_940_;
}
else
{
uint8_t v___x_950_; uint8_t v___x_951_; 
v___x_950_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_951_ = lean_uint8_dec_le(v___y_895_, v___x_950_);
v___y_941_ = v___x_951_;
goto v___jp_940_;
}
}
else
{
return v___y_947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___lam__0___boxed(lean_object* v___y_956_){
_start:
{
uint8_t v___y_318__boxed_957_; uint8_t v_res_958_; lean_object* v_r_959_; 
v___y_318__boxed_957_ = lean_unbox(v___y_956_);
v_res_958_ = l_Std_Http_URI_EncodedSegment_encode___lam__0(v___y_318__boxed_957_);
v_r_959_ = lean_box(v_res_958_);
return v_r_959_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode(lean_object* v_s_961_){
_start:
{
lean_object* v___f_962_; lean_object* v___x_963_; 
v___f_962_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_963_ = l_Std_Http_URI_EncodedString_encode(v___f_962_, v_s_961_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___boxed(lean_object* v_s_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Std_Http_URI_EncodedSegment_encode(v_s_964_);
lean_dec_ref(v_s_964_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object* v_ba_966_){
_start:
{
lean_object* v___f_967_; lean_object* v___x_968_; 
v___f_967_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_968_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_967_, v_ba_966_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x21(lean_object* v_ba_969_){
_start:
{
lean_object* v___f_970_; lean_object* v___x_971_; 
v___f_970_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_971_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_970_, v_ba_969_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object* v_segment_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Std_Http_URI_EncodedString_decode___redArg(v_segment_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode___boxed(lean_object* v_segment_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_Http_URI_EncodedSegment_decode(v_segment_974_);
lean_dec_ref(v_segment_974_);
return v_res_975_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0(void){
_start:
{
uint32_t v___x_976_; uint8_t v___x_977_; 
v___x_976_ = 47;
v___x_977_ = lean_uint32_to_uint8(v___x_976_);
return v___x_977_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1(void){
_start:
{
uint32_t v___x_978_; uint8_t v___x_979_; 
v___x_978_ = 63;
v___x_979_ = lean_uint32_to_uint8(v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedFragment_encode___lam__0(uint8_t v___y_980_){
_start:
{
uint8_t v___y_982_; uint8_t v___y_988_; uint8_t v___y_994_; uint8_t v___y_1014_; uint8_t v___y_1020_; uint8_t v___y_1026_; uint8_t v___y_1032_; uint8_t v___y_1038_; uint8_t v___x_1043_; uint8_t v___x_1044_; 
v___x_1043_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1044_ = lean_uint8_dec_le(v___x_1043_, v___y_980_);
if (v___x_1044_ == 0)
{
v___y_1038_ = v___x_1044_;
goto v___jp_1037_;
}
else
{
uint8_t v___x_1045_; uint8_t v___x_1046_; 
v___x_1045_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1046_ = lean_uint8_dec_le(v___y_980_, v___x_1045_);
v___y_1038_ = v___x_1046_;
goto v___jp_1037_;
}
v___jp_981_:
{
if (v___y_982_ == 0)
{
uint8_t v___x_983_; uint8_t v___x_984_; 
v___x_983_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0);
v___x_984_ = lean_uint8_dec_eq(v___y_980_, v___x_983_);
if (v___x_984_ == 0)
{
uint8_t v___x_985_; uint8_t v___x_986_; 
v___x_985_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1);
v___x_986_ = lean_uint8_dec_eq(v___y_980_, v___x_985_);
return v___x_986_;
}
else
{
return v___x_984_;
}
}
else
{
return v___y_982_;
}
}
v___jp_987_:
{
if (v___y_988_ == 0)
{
uint8_t v___x_989_; uint8_t v___x_990_; 
v___x_989_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_990_ = lean_uint8_dec_eq(v___y_980_, v___x_989_);
if (v___x_990_ == 0)
{
uint8_t v___x_991_; uint8_t v___x_992_; 
v___x_991_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_992_ = lean_uint8_dec_eq(v___y_980_, v___x_991_);
v___y_982_ = v___x_992_;
goto v___jp_981_;
}
else
{
v___y_982_ = v___x_990_;
goto v___jp_981_;
}
}
else
{
return v___y_988_;
}
}
v___jp_993_:
{
if (v___y_994_ == 0)
{
uint8_t v___x_995_; uint8_t v___x_996_; 
v___x_995_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_996_ = lean_uint8_dec_eq(v___y_980_, v___x_995_);
if (v___x_996_ == 0)
{
uint8_t v___x_997_; uint8_t v___x_998_; 
v___x_997_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_998_ = lean_uint8_dec_eq(v___y_980_, v___x_997_);
if (v___x_998_ == 0)
{
uint8_t v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1000_ = lean_uint8_dec_eq(v___y_980_, v___x_999_);
if (v___x_1000_ == 0)
{
uint8_t v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1002_ = lean_uint8_dec_eq(v___y_980_, v___x_1001_);
if (v___x_1002_ == 0)
{
uint8_t v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1004_ = lean_uint8_dec_eq(v___y_980_, v___x_1003_);
if (v___x_1004_ == 0)
{
uint8_t v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1006_ = lean_uint8_dec_eq(v___y_980_, v___x_1005_);
if (v___x_1006_ == 0)
{
uint8_t v___x_1007_; uint8_t v___x_1008_; 
v___x_1007_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1008_ = lean_uint8_dec_eq(v___y_980_, v___x_1007_);
if (v___x_1008_ == 0)
{
uint8_t v___x_1009_; uint8_t v___x_1010_; 
v___x_1009_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1010_ = lean_uint8_dec_eq(v___y_980_, v___x_1009_);
if (v___x_1010_ == 0)
{
uint8_t v___x_1011_; uint8_t v___x_1012_; 
v___x_1011_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1012_ = lean_uint8_dec_eq(v___y_980_, v___x_1011_);
v___y_988_ = v___x_1012_;
goto v___jp_987_;
}
else
{
v___y_988_ = v___x_1010_;
goto v___jp_987_;
}
}
else
{
v___y_988_ = v___x_1008_;
goto v___jp_987_;
}
}
else
{
v___y_988_ = v___x_1006_;
goto v___jp_987_;
}
}
else
{
v___y_988_ = v___x_1004_;
goto v___jp_987_;
}
}
else
{
v___y_988_ = v___x_1002_;
goto v___jp_987_;
}
}
else
{
v___y_988_ = v___x_1000_;
goto v___jp_987_;
}
}
else
{
v___y_988_ = v___x_998_;
goto v___jp_987_;
}
}
else
{
v___y_988_ = v___x_996_;
goto v___jp_987_;
}
}
else
{
return v___y_994_;
}
}
v___jp_1013_:
{
if (v___y_1014_ == 0)
{
uint8_t v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1016_ = lean_uint8_dec_eq(v___y_980_, v___x_1015_);
if (v___x_1016_ == 0)
{
uint8_t v___x_1017_; uint8_t v___x_1018_; 
v___x_1017_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1018_ = lean_uint8_dec_eq(v___y_980_, v___x_1017_);
v___y_994_ = v___x_1018_;
goto v___jp_993_;
}
else
{
v___y_994_ = v___x_1016_;
goto v___jp_993_;
}
}
else
{
return v___y_1014_;
}
}
v___jp_1019_:
{
if (v___y_1020_ == 0)
{
uint8_t v___x_1021_; uint8_t v___x_1022_; 
v___x_1021_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1022_ = lean_uint8_dec_eq(v___y_980_, v___x_1021_);
if (v___x_1022_ == 0)
{
uint8_t v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1024_ = lean_uint8_dec_eq(v___y_980_, v___x_1023_);
v___y_1014_ = v___x_1024_;
goto v___jp_1013_;
}
else
{
v___y_1014_ = v___x_1022_;
goto v___jp_1013_;
}
}
else
{
return v___y_1020_;
}
}
v___jp_1025_:
{
if (v___y_1026_ == 0)
{
uint8_t v___x_1027_; uint8_t v___x_1028_; 
v___x_1027_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1028_ = lean_uint8_dec_eq(v___y_980_, v___x_1027_);
if (v___x_1028_ == 0)
{
uint8_t v___x_1029_; uint8_t v___x_1030_; 
v___x_1029_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1030_ = lean_uint8_dec_eq(v___y_980_, v___x_1029_);
v___y_1020_ = v___x_1030_;
goto v___jp_1019_;
}
else
{
v___y_1020_ = v___x_1028_;
goto v___jp_1019_;
}
}
else
{
return v___y_1026_;
}
}
v___jp_1031_:
{
if (v___y_1032_ == 0)
{
uint8_t v___x_1033_; uint8_t v___x_1034_; 
v___x_1033_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1034_ = lean_uint8_dec_le(v___x_1033_, v___y_980_);
if (v___x_1034_ == 0)
{
v___y_1026_ = v___x_1034_;
goto v___jp_1025_;
}
else
{
uint8_t v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1036_ = lean_uint8_dec_le(v___y_980_, v___x_1035_);
v___y_1026_ = v___x_1036_;
goto v___jp_1025_;
}
}
else
{
return v___y_1032_;
}
}
v___jp_1037_:
{
if (v___y_1038_ == 0)
{
uint8_t v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1040_ = lean_uint8_dec_le(v___x_1039_, v___y_980_);
if (v___x_1040_ == 0)
{
v___y_1032_ = v___x_1040_;
goto v___jp_1031_;
}
else
{
uint8_t v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1042_ = lean_uint8_dec_le(v___y_980_, v___x_1041_);
v___y_1032_ = v___x_1042_;
goto v___jp_1031_;
}
}
else
{
return v___y_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed(lean_object* v___y_1047_){
_start:
{
uint8_t v___y_312__boxed_1048_; uint8_t v_res_1049_; lean_object* v_r_1050_; 
v___y_312__boxed_1048_ = lean_unbox(v___y_1047_);
v_res_1049_ = l_Std_Http_URI_EncodedFragment_encode___lam__0(v___y_312__boxed_1048_);
v_r_1050_ = lean_box(v_res_1049_);
return v_r_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object* v_s_1052_){
_start:
{
lean_object* v___f_1053_; lean_object* v___x_1054_; 
v___f_1053_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1054_ = l_Std_Http_URI_EncodedString_encode(v___f_1053_, v_s_1052_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___boxed(lean_object* v_s_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Std_Http_URI_EncodedFragment_encode(v_s_1055_);
lean_dec_ref(v_s_1055_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object* v_ba_1057_){
_start:
{
lean_object* v___f_1058_; lean_object* v___x_1059_; 
v___f_1058_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1059_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1058_, v_ba_1057_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x21(lean_object* v_ba_1060_){
_start:
{
lean_object* v___f_1061_; lean_object* v___x_1062_; 
v___f_1061_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1062_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1061_, v_ba_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object* v_fragment_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Std_Http_URI_EncodedString_decode___redArg(v_fragment_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode___boxed(lean_object* v_fragment_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Std_Http_URI_EncodedFragment_decode(v_fragment_1065_);
lean_dec_ref(v_fragment_1065_);
return v_res_1066_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedUserInfo_encode___lam__0(uint8_t v___y_1067_){
_start:
{
uint8_t v___y_1069_; uint8_t v___y_1073_; uint8_t v___y_1093_; uint8_t v___y_1099_; uint8_t v___y_1105_; uint8_t v___y_1111_; uint8_t v___y_1117_; uint8_t v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1123_ = lean_uint8_dec_le(v___x_1122_, v___y_1067_);
if (v___x_1123_ == 0)
{
v___y_1117_ = v___x_1123_;
goto v___jp_1116_;
}
else
{
uint8_t v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1125_ = lean_uint8_dec_le(v___y_1067_, v___x_1124_);
v___y_1117_ = v___x_1125_;
goto v___jp_1116_;
}
v___jp_1068_:
{
if (v___y_1069_ == 0)
{
uint8_t v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_1071_ = lean_uint8_dec_eq(v___y_1067_, v___x_1070_);
return v___x_1071_;
}
else
{
return v___y_1069_;
}
}
v___jp_1072_:
{
if (v___y_1073_ == 0)
{
uint8_t v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1075_ = lean_uint8_dec_eq(v___y_1067_, v___x_1074_);
if (v___x_1075_ == 0)
{
uint8_t v___x_1076_; uint8_t v___x_1077_; 
v___x_1076_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_1077_ = lean_uint8_dec_eq(v___y_1067_, v___x_1076_);
if (v___x_1077_ == 0)
{
uint8_t v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1079_ = lean_uint8_dec_eq(v___y_1067_, v___x_1078_);
if (v___x_1079_ == 0)
{
uint8_t v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1081_ = lean_uint8_dec_eq(v___y_1067_, v___x_1080_);
if (v___x_1081_ == 0)
{
uint8_t v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1083_ = lean_uint8_dec_eq(v___y_1067_, v___x_1082_);
if (v___x_1083_ == 0)
{
uint8_t v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1085_ = lean_uint8_dec_eq(v___y_1067_, v___x_1084_);
if (v___x_1085_ == 0)
{
uint8_t v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1087_ = lean_uint8_dec_eq(v___y_1067_, v___x_1086_);
if (v___x_1087_ == 0)
{
uint8_t v___x_1088_; uint8_t v___x_1089_; 
v___x_1088_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1089_ = lean_uint8_dec_eq(v___y_1067_, v___x_1088_);
if (v___x_1089_ == 0)
{
uint8_t v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1091_ = lean_uint8_dec_eq(v___y_1067_, v___x_1090_);
v___y_1069_ = v___x_1091_;
goto v___jp_1068_;
}
else
{
v___y_1069_ = v___x_1089_;
goto v___jp_1068_;
}
}
else
{
v___y_1069_ = v___x_1087_;
goto v___jp_1068_;
}
}
else
{
v___y_1069_ = v___x_1085_;
goto v___jp_1068_;
}
}
else
{
v___y_1069_ = v___x_1083_;
goto v___jp_1068_;
}
}
else
{
v___y_1069_ = v___x_1081_;
goto v___jp_1068_;
}
}
else
{
v___y_1069_ = v___x_1079_;
goto v___jp_1068_;
}
}
else
{
v___y_1069_ = v___x_1077_;
goto v___jp_1068_;
}
}
else
{
v___y_1069_ = v___x_1075_;
goto v___jp_1068_;
}
}
else
{
return v___y_1073_;
}
}
v___jp_1092_:
{
if (v___y_1093_ == 0)
{
uint8_t v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1095_ = lean_uint8_dec_eq(v___y_1067_, v___x_1094_);
if (v___x_1095_ == 0)
{
uint8_t v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1097_ = lean_uint8_dec_eq(v___y_1067_, v___x_1096_);
v___y_1073_ = v___x_1097_;
goto v___jp_1072_;
}
else
{
v___y_1073_ = v___x_1095_;
goto v___jp_1072_;
}
}
else
{
return v___y_1093_;
}
}
v___jp_1098_:
{
if (v___y_1099_ == 0)
{
uint8_t v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1101_ = lean_uint8_dec_eq(v___y_1067_, v___x_1100_);
if (v___x_1101_ == 0)
{
uint8_t v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1103_ = lean_uint8_dec_eq(v___y_1067_, v___x_1102_);
v___y_1093_ = v___x_1103_;
goto v___jp_1092_;
}
else
{
v___y_1093_ = v___x_1101_;
goto v___jp_1092_;
}
}
else
{
return v___y_1099_;
}
}
v___jp_1104_:
{
if (v___y_1105_ == 0)
{
uint8_t v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1107_ = lean_uint8_dec_eq(v___y_1067_, v___x_1106_);
if (v___x_1107_ == 0)
{
uint8_t v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1109_ = lean_uint8_dec_eq(v___y_1067_, v___x_1108_);
v___y_1099_ = v___x_1109_;
goto v___jp_1098_;
}
else
{
v___y_1099_ = v___x_1107_;
goto v___jp_1098_;
}
}
else
{
return v___y_1105_;
}
}
v___jp_1110_:
{
if (v___y_1111_ == 0)
{
uint8_t v___x_1112_; uint8_t v___x_1113_; 
v___x_1112_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1113_ = lean_uint8_dec_le(v___x_1112_, v___y_1067_);
if (v___x_1113_ == 0)
{
v___y_1105_ = v___x_1113_;
goto v___jp_1104_;
}
else
{
uint8_t v___x_1114_; uint8_t v___x_1115_; 
v___x_1114_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1115_ = lean_uint8_dec_le(v___y_1067_, v___x_1114_);
v___y_1105_ = v___x_1115_;
goto v___jp_1104_;
}
}
else
{
return v___y_1111_;
}
}
v___jp_1116_:
{
if (v___y_1117_ == 0)
{
uint8_t v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1119_ = lean_uint8_dec_le(v___x_1118_, v___y_1067_);
if (v___x_1119_ == 0)
{
v___y_1111_ = v___x_1119_;
goto v___jp_1110_;
}
else
{
uint8_t v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1121_ = lean_uint8_dec_le(v___y_1067_, v___x_1120_);
v___y_1111_ = v___x_1121_;
goto v___jp_1110_;
}
}
else
{
return v___y_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed(lean_object* v___y_1126_){
_start:
{
uint8_t v___y_271__boxed_1127_; uint8_t v_res_1128_; lean_object* v_r_1129_; 
v___y_271__boxed_1127_ = lean_unbox(v___y_1126_);
v_res_1128_ = l_Std_Http_URI_EncodedUserInfo_encode___lam__0(v___y_271__boxed_1127_);
v_r_1129_ = lean_box(v_res_1128_);
return v_r_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object* v_s_1131_){
_start:
{
lean_object* v___f_1132_; lean_object* v___x_1133_; 
v___f_1132_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1133_ = l_Std_Http_URI_EncodedString_encode(v___f_1132_, v_s_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___boxed(lean_object* v_s_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Std_Http_URI_EncodedUserInfo_encode(v_s_1134_);
lean_dec_ref(v_s_1134_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object* v_ba_1136_){
_start:
{
lean_object* v___f_1137_; lean_object* v___x_1138_; 
v___f_1137_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1138_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1137_, v_ba_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x21(lean_object* v_ba_1139_){
_start:
{
lean_object* v___f_1140_; lean_object* v___x_1141_; 
v___f_1140_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1141_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1140_, v_ba_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode(lean_object* v_userInfo_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Std_Http_URI_EncodedString_decode___redArg(v_userInfo_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode___boxed(lean_object* v_userInfo_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Std_Http_URI_EncodedUserInfo_decode(v_userInfo_1144_);
lean_dec_ref(v_userInfo_1144_);
return v_res_1145_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryParam_encode___lam__0(uint8_t v___y_1146_){
_start:
{
uint8_t v___y_1155_; uint8_t v___y_1157_; uint8_t v___y_1163_; uint8_t v___y_1169_; uint8_t v___y_1189_; uint8_t v___y_1195_; uint8_t v___y_1201_; uint8_t v___y_1207_; uint8_t v___y_1213_; uint8_t v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1219_ = lean_uint8_dec_le(v___x_1218_, v___y_1146_);
if (v___x_1219_ == 0)
{
v___y_1213_ = v___x_1219_;
goto v___jp_1212_;
}
else
{
uint8_t v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1221_ = lean_uint8_dec_le(v___y_1146_, v___x_1220_);
v___y_1213_ = v___x_1221_;
goto v___jp_1212_;
}
v___jp_1147_:
{
uint8_t v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1149_ = lean_uint8_dec_eq(v___y_1146_, v___x_1148_);
if (v___x_1149_ == 0)
{
uint8_t v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1151_ = lean_uint8_dec_eq(v___y_1146_, v___x_1150_);
if (v___x_1151_ == 0)
{
uint8_t v___x_1152_; 
v___x_1152_ = 1;
return v___x_1152_;
}
else
{
return v___x_1149_;
}
}
else
{
uint8_t v___x_1153_; 
v___x_1153_ = 0;
return v___x_1153_;
}
}
v___jp_1154_:
{
if (v___y_1155_ == 0)
{
return v___y_1155_;
}
else
{
goto v___jp_1147_;
}
}
v___jp_1156_:
{
if (v___y_1157_ == 0)
{
uint8_t v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0);
v___x_1159_ = lean_uint8_dec_eq(v___y_1146_, v___x_1158_);
if (v___x_1159_ == 0)
{
uint8_t v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1);
v___x_1161_ = lean_uint8_dec_eq(v___y_1146_, v___x_1160_);
v___y_1155_ = v___x_1161_;
goto v___jp_1154_;
}
else
{
v___y_1155_ = v___x_1159_;
goto v___jp_1154_;
}
}
else
{
goto v___jp_1147_;
}
}
v___jp_1162_:
{
if (v___y_1163_ == 0)
{
uint8_t v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_1165_ = lean_uint8_dec_eq(v___y_1146_, v___x_1164_);
if (v___x_1165_ == 0)
{
uint8_t v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_1167_ = lean_uint8_dec_eq(v___y_1146_, v___x_1166_);
v___y_1157_ = v___x_1167_;
goto v___jp_1156_;
}
else
{
v___y_1157_ = v___x_1165_;
goto v___jp_1156_;
}
}
else
{
goto v___jp_1147_;
}
}
v___jp_1168_:
{
if (v___y_1169_ == 0)
{
uint8_t v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1171_ = lean_uint8_dec_eq(v___y_1146_, v___x_1170_);
if (v___x_1171_ == 0)
{
uint8_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_1173_ = lean_uint8_dec_eq(v___y_1146_, v___x_1172_);
if (v___x_1173_ == 0)
{
uint8_t v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1175_ = lean_uint8_dec_eq(v___y_1146_, v___x_1174_);
if (v___x_1175_ == 0)
{
uint8_t v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1177_ = lean_uint8_dec_eq(v___y_1146_, v___x_1176_);
if (v___x_1177_ == 0)
{
uint8_t v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1179_ = lean_uint8_dec_eq(v___y_1146_, v___x_1178_);
if (v___x_1179_ == 0)
{
uint8_t v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1181_ = lean_uint8_dec_eq(v___y_1146_, v___x_1180_);
if (v___x_1181_ == 0)
{
uint8_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1183_ = lean_uint8_dec_eq(v___y_1146_, v___x_1182_);
if (v___x_1183_ == 0)
{
uint8_t v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1185_ = lean_uint8_dec_eq(v___y_1146_, v___x_1184_);
if (v___x_1185_ == 0)
{
uint8_t v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1187_ = lean_uint8_dec_eq(v___y_1146_, v___x_1186_);
v___y_1163_ = v___x_1187_;
goto v___jp_1162_;
}
else
{
v___y_1163_ = v___x_1185_;
goto v___jp_1162_;
}
}
else
{
v___y_1163_ = v___x_1183_;
goto v___jp_1162_;
}
}
else
{
v___y_1163_ = v___x_1181_;
goto v___jp_1162_;
}
}
else
{
v___y_1163_ = v___x_1179_;
goto v___jp_1162_;
}
}
else
{
v___y_1163_ = v___x_1177_;
goto v___jp_1162_;
}
}
else
{
v___y_1163_ = v___x_1175_;
goto v___jp_1162_;
}
}
else
{
v___y_1163_ = v___x_1173_;
goto v___jp_1162_;
}
}
else
{
v___y_1163_ = v___x_1171_;
goto v___jp_1162_;
}
}
else
{
goto v___jp_1147_;
}
}
v___jp_1188_:
{
if (v___y_1189_ == 0)
{
uint8_t v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1191_ = lean_uint8_dec_eq(v___y_1146_, v___x_1190_);
if (v___x_1191_ == 0)
{
uint8_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1193_ = lean_uint8_dec_eq(v___y_1146_, v___x_1192_);
v___y_1169_ = v___x_1193_;
goto v___jp_1168_;
}
else
{
v___y_1169_ = v___x_1191_;
goto v___jp_1168_;
}
}
else
{
goto v___jp_1147_;
}
}
v___jp_1194_:
{
if (v___y_1195_ == 0)
{
uint8_t v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1197_ = lean_uint8_dec_eq(v___y_1146_, v___x_1196_);
if (v___x_1197_ == 0)
{
uint8_t v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1199_ = lean_uint8_dec_eq(v___y_1146_, v___x_1198_);
v___y_1189_ = v___x_1199_;
goto v___jp_1188_;
}
else
{
v___y_1189_ = v___x_1197_;
goto v___jp_1188_;
}
}
else
{
goto v___jp_1147_;
}
}
v___jp_1200_:
{
if (v___y_1201_ == 0)
{
uint8_t v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1203_ = lean_uint8_dec_eq(v___y_1146_, v___x_1202_);
if (v___x_1203_ == 0)
{
uint8_t v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1205_ = lean_uint8_dec_eq(v___y_1146_, v___x_1204_);
v___y_1195_ = v___x_1205_;
goto v___jp_1194_;
}
else
{
v___y_1195_ = v___x_1203_;
goto v___jp_1194_;
}
}
else
{
goto v___jp_1147_;
}
}
v___jp_1206_:
{
if (v___y_1207_ == 0)
{
uint8_t v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1209_ = lean_uint8_dec_le(v___x_1208_, v___y_1146_);
if (v___x_1209_ == 0)
{
v___y_1201_ = v___x_1209_;
goto v___jp_1200_;
}
else
{
uint8_t v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1211_ = lean_uint8_dec_le(v___y_1146_, v___x_1210_);
v___y_1201_ = v___x_1211_;
goto v___jp_1200_;
}
}
else
{
goto v___jp_1147_;
}
}
v___jp_1212_:
{
if (v___y_1213_ == 0)
{
uint8_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1215_ = lean_uint8_dec_le(v___x_1214_, v___y_1146_);
if (v___x_1215_ == 0)
{
v___y_1207_ = v___x_1215_;
goto v___jp_1206_;
}
else
{
uint8_t v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1217_ = lean_uint8_dec_le(v___y_1146_, v___x_1216_);
v___y_1207_ = v___x_1217_;
goto v___jp_1206_;
}
}
else
{
goto v___jp_1147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed(lean_object* v___y_1222_){
_start:
{
uint8_t v___y_362__boxed_1223_; uint8_t v_res_1224_; lean_object* v_r_1225_; 
v___y_362__boxed_1223_ = lean_unbox(v___y_1222_);
v_res_1224_ = l_Std_Http_URI_EncodedQueryParam_encode___lam__0(v___y_362__boxed_1223_);
v_r_1225_ = lean_box(v_res_1224_);
return v_r_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode(lean_object* v_s_1227_){
_start:
{
lean_object* v___f_1228_; lean_object* v___x_1229_; 
v___f_1228_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1229_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_1227_, v___f_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___boxed(lean_object* v_s_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Std_Http_URI_EncodedQueryParam_encode(v_s_1230_);
lean_dec_ref(v_s_1230_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f(lean_object* v_ba_1232_){
_start:
{
lean_object* v___f_1233_; lean_object* v___x_1234_; 
v___f_1233_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1234_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_1232_, v___f_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x21(lean_object* v_ba_1235_){
_start:
{
lean_object* v___f_1236_; lean_object* v___x_1237_; 
v___f_1236_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1237_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v_ba_1235_, v___f_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object* v_s_1238_){
_start:
{
lean_object* v___f_1239_; lean_object* v___x_1240_; 
v___f_1239_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1240_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_1238_, v___f_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f___boxed(lean_object* v_s_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_s_1241_);
lean_dec_ref(v_s_1241_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object* v_param_1243_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_param_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode___boxed(lean_object* v_param_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Std_Http_URI_EncodedQueryParam_decode(v_param_1245_);
lean_dec_ref(v_param_1245_);
return v_res_1246_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Bitwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Internal_Char(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Data_URI_Encoding(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Internal_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Data_URI_Encoding(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Bitwise(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Internal_Char(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Data_URI_Encoding(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Internal_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_URI_Encoding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Data_URI_Encoding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Data_URI_Encoding(builtin);
}
#ifdef __cplusplus
}
#endif
