// Lean compiler output
// Module: Std.Http.Data.URI.Encoding
// Imports: import Init.Grind import Init.While import Init.Data.SInt.Lemmas import Init.Data.UInt.Lemmas import Init.Data.UInt.Bitwise import Init.Data.Array.Lemmas public import Init.Data.String.Basic public import Std.Http.Internal.Char
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
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
extern lean_object* l_ByteArray_empty;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_uint8_shift_left(uint8_t, uint8_t);
uint8_t lean_string_validate_utf8(lean_object*);
uint8_t lean_uint8_shift_right(uint8_t, uint8_t);
uint8_t lean_uint8_dec_lt(uint8_t, uint8_t);
uint8_t lean_uint8_land(uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_byte_array_uget(lean_object*, size_t);
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
lean_object* l_ByteArray_decEq___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidPercentEncoding(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidPercentEncoding___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_hexDigit(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Std.Http.Data.URI.Encoding"};
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_EncodedString_decode___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedString_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedString_instRepr___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedString_instRepr___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedString_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteArray_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedString_instBEq___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedString_instBEq___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0;
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(lean_object* v_ba_140_, lean_object* v_i_141_){
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop___boxed(lean_object* v_ba_199_, lean_object* v_i_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_199_, v_i_200_);
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
v___x_205_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_203_, v___x_204_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(lean_object* v_x_259_, uint8_t v_x_260_, lean_object* v_h__1_261_){
_start:
{
lean_object* v_data_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_data_262_ = lean_byte_array_data(v_x_259_);
v___x_263_ = lean_box(v_x_260_);
v___x_264_ = lean_apply_2(v_h__1_261_, v_data_262_, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg___boxed(lean_object* v_x_265_, lean_object* v_x_266_, lean_object* v_h__1_267_){
_start:
{
uint8_t v_x_17__boxed_268_; lean_object* v_res_269_; 
v_x_17__boxed_268_ = lean_unbox(v_x_266_);
v_res_269_ = l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(v_x_265_, v_x_17__boxed_268_, v_h__1_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(lean_object* v_motive_270_, lean_object* v_x_271_, uint8_t v_x_272_, lean_object* v_h__1_273_){
_start:
{
lean_object* v_data_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_data_274_ = lean_byte_array_data(v_x_271_);
v___x_275_ = lean_box(v_x_272_);
v___x_276_ = lean_apply_2(v_h__1_273_, v_data_274_, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___boxed(lean_object* v_motive_277_, lean_object* v_x_278_, lean_object* v_x_279_, lean_object* v_h__1_280_){
_start:
{
uint8_t v_x_29__boxed_281_; lean_object* v_res_282_; 
v_x_29__boxed_281_ = lean_unbox(v_x_279_);
v_res_282_ = l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(v_motive_277_, v_x_278_, v_x_29__boxed_281_, v_h__1_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter___redArg(lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_h__1_285_, lean_object* v_h__2_286_){
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
lean_dec_ref_known(v_x_283_, 2);
v___x_290_ = lean_apply_3(v_h__2_286_, v_head_288_, v_tail_289_, v_x_284_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter(lean_object* v_motive_291_, lean_object* v_x_292_, lean_object* v_x_293_, lean_object* v_h__1_294_, lean_object* v_h__2_295_){
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
lean_dec_ref_known(v_x_292_, 2);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(lean_object* v_s_308_, uint8_t v_c_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = lean_byte_array_push(v_s_308_, v_c_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg___boxed(lean_object* v_s_311_, lean_object* v_c_312_){
_start:
{
uint8_t v_c_boxed_313_; lean_object* v_res_314_; 
v_c_boxed_313_ = lean_unbox(v_c_312_);
v_res_314_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(v_s_311_, v_c_boxed_313_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(lean_object* v_r_315_, lean_object* v_s_316_, uint8_t v_c_317_, lean_object* v_h_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = lean_byte_array_push(v_s_316_, v_c_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___boxed(lean_object* v_r_320_, lean_object* v_s_321_, lean_object* v_c_322_, lean_object* v_h_323_){
_start:
{
uint8_t v_c_boxed_324_; lean_object* v_res_325_; 
v_c_boxed_324_ = lean_unbox(v_c_322_);
v_res_325_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(v_r_320_, v_s_321_, v_c_boxed_324_, v_h_323_);
lean_dec_ref(v_r_320_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(uint8_t v_b_326_, lean_object* v_s_327_){
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg___boxed(lean_object* v_b_338_, lean_object* v_s_339_){
_start:
{
uint8_t v_b_boxed_340_; lean_object* v_res_341_; 
v_b_boxed_340_ = lean_unbox(v_b_338_);
v_res_341_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_boxed_340_, v_s_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(lean_object* v_r_342_, uint8_t v_b_343_, lean_object* v_s_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_343_, v_s_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___boxed(lean_object* v_r_346_, lean_object* v_b_347_, lean_object* v_s_348_){
_start:
{
uint8_t v_b_boxed_349_; lean_object* v_res_350_; 
v_b_boxed_349_ = lean_unbox(v_b_347_);
v_res_350_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(v_r_346_, v_b_boxed_349_, v_s_348_);
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
v___x_365_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_362_, v_b_355_);
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
v___x_369_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_362_, v_b_355_);
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
v___x_405_ = lean_panic_fn_borrowed(v___x_404_, v_msg_403_);
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
lean_dec_ref_known(v___x_423_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(lean_object* v_len_460_, lean_object* v_rawBytes_461_, lean_object* v_a_462_){
_start:
{
lean_object* v_fst_463_; lean_object* v_snd_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_522_; 
v_fst_463_ = lean_ctor_get(v_a_462_, 0);
v_snd_464_ = lean_ctor_get(v_a_462_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_a_462_);
if (v_isSharedCheck_522_ == 0)
{
v___x_466_ = v_a_462_;
v_isShared_467_ = v_isSharedCheck_522_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_snd_464_);
lean_inc(v_fst_463_);
lean_dec(v_a_462_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_522_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
uint8_t v___x_468_; 
v___x_468_ = lean_nat_dec_lt(v_snd_464_, v_len_460_);
if (v___x_468_ == 0)
{
lean_object* v___x_470_; 
if (v_isShared_467_ == 0)
{
v___x_470_ = v___x_466_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_fst_463_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_snd_464_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
else
{
uint8_t v_percent_472_; uint8_t v___x_473_; uint8_t v___x_482_; 
v_percent_472_ = 37;
v___x_473_ = lean_byte_array_fget(v_rawBytes_461_, v_snd_464_);
v___x_482_ = lean_uint8_dec_eq(v___x_473_, v_percent_472_);
if (v___x_482_ == 0)
{
goto v___jp_474_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_nat_add(v_snd_464_, v___x_483_);
v___x_485_ = lean_nat_dec_lt(v___x_484_, v_len_460_);
if (v___x_485_ == 0)
{
lean_dec(v___x_484_);
goto v___jp_474_;
}
else
{
uint8_t v___x_486_; lean_object* v___x_487_; 
lean_del_object(v___x_466_);
v___x_486_ = lean_byte_array_fget(v_rawBytes_461_, v___x_484_);
lean_dec(v___x_484_);
v___x_487_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_486_);
if (lean_obj_tag(v___x_487_) == 1)
{
lean_object* v_val_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v_val_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_val_488_);
lean_dec_ref_known(v___x_487_, 1);
v___x_489_ = lean_unsigned_to_nat(2u);
v___x_490_ = lean_nat_add(v_snd_464_, v___x_489_);
v___x_491_ = lean_nat_dec_lt(v___x_490_, v_len_460_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec(v_val_488_);
lean_dec(v_snd_464_);
v___x_492_ = lean_byte_array_push(v_fst_463_, v___x_473_);
v___x_493_ = lean_byte_array_push(v___x_492_, v___x_486_);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v___x_490_);
v_a_462_ = v___x_494_;
goto _start;
}
else
{
uint8_t v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_byte_array_fget(v_rawBytes_461_, v___x_490_);
lean_dec(v___x_490_);
v___x_497_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_496_);
if (lean_obj_tag(v___x_497_) == 1)
{
lean_object* v_val_498_; uint8_t v___x_499_; uint8_t v___x_500_; uint8_t v___x_501_; uint8_t v___x_502_; uint8_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_val_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_val_498_);
lean_dec_ref_known(v___x_497_, 1);
v___x_499_ = 4;
v___x_500_ = lean_unbox(v_val_488_);
lean_dec(v_val_488_);
v___x_501_ = lean_uint8_shift_left(v___x_500_, v___x_499_);
v___x_502_ = lean_unbox(v_val_498_);
lean_dec(v_val_498_);
v___x_503_ = lean_uint8_add(v___x_501_, v___x_502_);
v___x_504_ = lean_byte_array_push(v_fst_463_, v___x_503_);
v___x_505_ = lean_unsigned_to_nat(3u);
v___x_506_ = lean_nat_add(v_snd_464_, v___x_505_);
lean_dec(v_snd_464_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_504_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
v_a_462_ = v___x_507_;
goto _start;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v___x_497_);
lean_dec(v_val_488_);
v___x_509_ = lean_byte_array_push(v_fst_463_, v___x_473_);
v___x_510_ = lean_byte_array_push(v___x_509_, v___x_486_);
v___x_511_ = lean_byte_array_push(v___x_510_, v___x_496_);
v___x_512_ = lean_unsigned_to_nat(3u);
v___x_513_ = lean_nat_add(v_snd_464_, v___x_512_);
lean_dec(v_snd_464_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_511_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v_a_462_ = v___x_514_;
goto _start;
}
}
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec(v___x_487_);
v___x_516_ = lean_byte_array_push(v_fst_463_, v___x_473_);
v___x_517_ = lean_byte_array_push(v___x_516_, v___x_486_);
v___x_518_ = lean_unsigned_to_nat(2u);
v___x_519_ = lean_nat_add(v_snd_464_, v___x_518_);
lean_dec(v_snd_464_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_517_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v_a_462_ = v___x_520_;
goto _start;
}
}
}
v___jp_474_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_475_ = lean_byte_array_push(v_fst_463_, v___x_473_);
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_add(v_snd_464_, v___x_476_);
lean_dec(v_snd_464_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 1, v___x_477_);
lean_ctor_set(v___x_466_, 0, v___x_475_);
v___x_479_ = v___x_466_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v___x_477_);
v___x_479_ = v_reuseFailAlloc_481_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
v_a_462_ = v___x_479_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg___boxed(lean_object* v_len_523_, lean_object* v_rawBytes_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_523_, v_rawBytes_524_, v_a_525_);
lean_dec_ref(v_rawBytes_524_);
lean_dec(v_len_523_);
return v_res_526_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0(void){
_start:
{
lean_object* v_i_527_; lean_object* v_decoded_528_; lean_object* v___x_529_; 
v_i_527_ = lean_unsigned_to_nat(0u);
v_decoded_528_ = l_ByteArray_empty;
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_decoded_528_);
lean_ctor_set(v___x_529_, 1, v_i_527_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg(lean_object* v_es_530_){
_start:
{
lean_object* v_len_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v_fst_534_; uint8_t v___x_535_; 
v_len_531_ = lean_byte_array_size(v_es_530_);
v___x_532_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_533_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_531_, v_es_530_, v___x_532_);
v_fst_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_fst_534_);
lean_dec_ref(v___x_533_);
v___x_535_ = lean_string_validate_utf8(v_fst_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
lean_dec(v_fst_534_);
v___x_536_ = lean_box(0);
return v___x_536_;
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_string_from_utf8_unchecked(v_fst_534_);
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg___boxed(lean_object* v_es_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_539_);
lean_dec_ref(v_es_539_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode(lean_object* v_r_541_, lean_object* v_es_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___boxed(lean_object* v_r_544_, lean_object* v_es_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Std_Http_URI_EncodedString_decode(v_r_544_, v_es_545_);
lean_dec_ref(v_es_545_);
lean_dec_ref(v_r_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(lean_object* v_len_547_, lean_object* v_rawBytes_548_, lean_object* v_inst_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_547_, v_rawBytes_548_, v_a_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___boxed(lean_object* v_len_552_, lean_object* v_rawBytes_553_, lean_object* v_inst_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(v_len_552_, v_rawBytes_553_, v_inst_554_, v_a_555_);
lean_dec_ref(v_rawBytes_553_);
lean_dec(v_len_552_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___lam__0(lean_object* v_es_557_, lean_object* v_n_558_){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_string_from_utf8_unchecked(v_es_557_);
v___x_560_ = l_String_quote(v___x_559_);
v___x_561_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed(lean_object* v_es_562_, lean_object* v_n_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Std_Http_URI_EncodedString_instRepr___lam__0(v_es_562_, v_n_563_);
lean_dec(v_n_563_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr(lean_object* v_r_566_){
_start:
{
lean_object* v___f_567_; 
v___f_567_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___closed__0));
return v___f_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___boxed(lean_object* v_r_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Std_Http_URI_EncodedString_instRepr(v_r_568_);
lean_dec_ref(v_r_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq(lean_object* v_r_571_){
_start:
{
lean_object* v___f_572_; 
v___f_572_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___closed__0));
return v___f_572_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___boxed(lean_object* v_r_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Std_Http_URI_EncodedString_instBEq(v_r_573_);
lean_dec_ref(v_r_573_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable(lean_object* v_r_576_){
_start:
{
lean_object* v___f_577_; 
v___f_577_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___closed__0));
return v___f_577_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___boxed(lean_object* v_r_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_Http_URI_EncodedString_instHashable(v_r_578_);
lean_dec_ref(v_r_578_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty(lean_object* v_r_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_ByteArray_empty;
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___boxed(lean_object* v_r_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_Http_URI_EncodedQueryString_empty(v_r_582_);
lean_dec_ref(v_r_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited(lean_object* v_r_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_ByteArray_empty;
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___boxed(lean_object* v_r_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_Http_URI_EncodedQueryString_instInhabited(v_r_586_);
lean_dec_ref(v_r_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(lean_object* v_s_588_, uint8_t v_c_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = lean_byte_array_push(v_s_588_, v_c_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg___boxed(lean_object* v_s_591_, lean_object* v_c_592_){
_start:
{
uint8_t v_c_boxed_593_; lean_object* v_res_594_; 
v_c_boxed_593_ = lean_unbox(v_c_592_);
v_res_594_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(v_s_591_, v_c_boxed_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(lean_object* v_r_595_, lean_object* v_s_596_, uint8_t v_c_597_, lean_object* v_h_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = lean_byte_array_push(v_s_596_, v_c_597_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___boxed(lean_object* v_r_600_, lean_object* v_s_601_, lean_object* v_c_602_, lean_object* v_h_603_){
_start:
{
uint8_t v_c_boxed_604_; lean_object* v_res_605_; 
v_c_boxed_604_ = lean_unbox(v_c_602_);
v_res_605_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(v_r_600_, v_s_601_, v_c_boxed_604_, v_h_603_);
lean_dec_ref(v_r_600_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(lean_object* v_ba_606_, lean_object* v_r_607_){
_start:
{
uint8_t v___x_608_; 
lean_inc_ref(v_ba_606_);
v___x_608_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_607_, v_ba_606_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
lean_dec_ref(v_ba_606_);
v___x_609_ = lean_box(0);
return v___x_609_;
}
else
{
uint8_t v___x_610_; 
v___x_610_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_606_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; 
lean_dec_ref(v_ba_606_);
v___x_611_ = lean_box(0);
return v___x_611_;
}
else
{
lean_object* v___x_612_; 
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v_ba_606_);
return v___x_612_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_613_){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = l_ByteArray_empty;
v___x_615_ = lean_panic_fn_borrowed(v___x_614_, v_msg_613_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(lean_object* v_r_616_, lean_object* v_msg_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v_msg_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_619_, lean_object* v_msg_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(v_r_619_, v_msg_620_);
lean_dec_ref(v_r_619_);
return v_res_621_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_624_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1));
v___x_625_ = lean_unsigned_to_nat(12u);
v___x_626_ = lean_unsigned_to_nat(438u);
v___x_627_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0));
v___x_628_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_629_ = l_mkPanicMessageWithDecl(v___x_628_, v___x_627_, v___x_626_, v___x_625_, v___x_624_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(lean_object* v_ba_630_, lean_object* v_r_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_630_, v_r_631_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_obj_once(&l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2, &l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2_once, _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2);
v___x_634_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v___x_633_);
return v___x_634_;
}
else
{
lean_object* v_val_635_; 
v_val_635_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_val_635_);
lean_dec_ref_known(v___x_632_, 1);
return v_val_635_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f(lean_object* v_s_636_, lean_object* v_r_637_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_string_to_utf8(v_s_636_);
v___x_639_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v___x_638_, v_r_637_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f___boxed(lean_object* v_s_640_, lean_object* v_r_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_640_, v_r_641_);
lean_dec_ref(v_s_640_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21(lean_object* v_s_643_, lean_object* v_r_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_string_to_utf8(v_s_643_);
v___x_646_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v___x_645_, v_r_644_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21___boxed(lean_object* v_s_647_, lean_object* v_r_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Std_Http_URI_EncodedQueryString_ofString_x21(v_s_647_, v_r_648_);
lean_dec_ref(v_s_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg(lean_object* v_ba_650_){
_start:
{
lean_inc_ref(v_ba_650_);
return v_ba_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg___boxed(lean_object* v_ba_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Std_Http_URI_EncodedQueryString_new___redArg(v_ba_651_);
lean_dec_ref(v_ba_651_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new(lean_object* v_r_653_, lean_object* v_ba_654_, lean_object* v_valid_655_, lean_object* v___validEncoding_656_){
_start:
{
lean_inc_ref(v_ba_654_);
return v_ba_654_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___boxed(lean_object* v_r_657_, lean_object* v_ba_658_, lean_object* v_valid_659_, lean_object* v___validEncoding_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Std_Http_URI_EncodedQueryString_new(v_r_657_, v_ba_658_, v_valid_659_, v___validEncoding_660_);
lean_dec_ref(v_ba_658_);
lean_dec_ref(v_r_657_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(uint8_t v_b_662_, lean_object* v_s_663_){
_start:
{
uint8_t v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; uint8_t v___x_667_; uint8_t v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; uint8_t v___x_671_; uint8_t v___x_672_; lean_object* v_ba_673_; 
v___x_664_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__0, &l_Std_Http_URI_isEncodedChar___closed__0_once, _init_l_Std_Http_URI_isEncodedChar___closed__0);
v___x_665_ = lean_byte_array_push(v_s_663_, v___x_664_);
v___x_666_ = 4;
v___x_667_ = lean_uint8_shift_right(v_b_662_, v___x_666_);
v___x_668_ = l_Std_Http_URI_hexDigit(v___x_667_);
v___x_669_ = lean_byte_array_push(v___x_665_, v___x_668_);
v___x_670_ = 15;
v___x_671_ = lean_uint8_land(v_b_662_, v___x_670_);
v___x_672_ = l_Std_Http_URI_hexDigit(v___x_671_);
v_ba_673_ = lean_byte_array_push(v___x_669_, v___x_672_);
return v_ba_673_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg___boxed(lean_object* v_b_674_, lean_object* v_s_675_){
_start:
{
uint8_t v_b_boxed_676_; lean_object* v_res_677_; 
v_b_boxed_676_ = lean_unbox(v_b_674_);
v_res_677_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_boxed_676_, v_s_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(lean_object* v_r_678_, uint8_t v_b_679_, lean_object* v_s_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_679_, v_s_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___boxed(lean_object* v_r_682_, lean_object* v_b_683_, lean_object* v_s_684_){
_start:
{
uint8_t v_b_boxed_685_; lean_object* v_res_686_; 
v_b_boxed_685_ = lean_unbox(v_b_683_);
v_res_686_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(v_r_682_, v_b_boxed_685_, v_s_684_);
lean_dec_ref(v_r_682_);
return v_res_686_;
}
}
static uint8_t _init_l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0(void){
_start:
{
uint32_t v___x_687_; uint8_t v___x_688_; 
v___x_687_ = 32;
v___x_688_ = lean_uint32_to_uint8(v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(lean_object* v_r_689_, lean_object* v_as_690_, size_t v_i_691_, size_t v_stop_692_, lean_object* v_b_693_){
_start:
{
lean_object* v___y_695_; uint8_t v___x_699_; 
v___x_699_ = lean_usize_dec_eq(v_i_691_, v_stop_692_);
if (v___x_699_ == 0)
{
uint8_t v___x_700_; uint8_t v___x_707_; uint8_t v___x_708_; 
v___x_700_ = lean_byte_array_uget(v_as_690_, v_i_691_);
v___x_707_ = 128;
v___x_708_ = lean_uint8_dec_lt(v___x_700_, v___x_707_);
if (v___x_708_ == 0)
{
goto v___jp_701_;
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_709_ = lean_box(v___x_700_);
lean_inc_ref(v_r_689_);
v___x_710_ = lean_apply_1(v_r_689_, v___x_709_);
v___x_711_ = lean_unbox(v___x_710_);
if (v___x_711_ == 0)
{
goto v___jp_701_;
}
else
{
lean_object* v___x_712_; 
v___x_712_ = lean_byte_array_push(v_b_693_, v___x_700_);
v___y_695_ = v___x_712_;
goto v___jp_694_;
}
}
v___jp_701_:
{
uint8_t v___x_702_; uint8_t v___x_703_; 
v___x_702_ = lean_uint8_once(&l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0, &l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0_once, _init_l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0);
v___x_703_ = lean_uint8_dec_eq(v___x_700_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
v___x_704_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v___x_700_, v_b_693_);
v___y_695_ = v___x_704_;
goto v___jp_694_;
}
else
{
uint8_t v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_706_ = lean_byte_array_push(v_b_693_, v___x_705_);
v___y_695_ = v___x_706_;
goto v___jp_694_;
}
}
}
else
{
lean_dec_ref(v_r_689_);
return v_b_693_;
}
v___jp_694_:
{
size_t v___x_696_; size_t v___x_697_; 
v___x_696_ = ((size_t)1ULL);
v___x_697_ = lean_usize_add(v_i_691_, v___x_696_);
v_i_691_ = v___x_697_;
v_b_693_ = v___y_695_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___boxed(lean_object* v_r_713_, lean_object* v_as_714_, lean_object* v_i_715_, lean_object* v_stop_716_, lean_object* v_b_717_){
_start:
{
size_t v_i_boxed_718_; size_t v_stop_boxed_719_; lean_object* v_res_720_; 
v_i_boxed_718_ = lean_unbox_usize(v_i_715_);
lean_dec(v_i_715_);
v_stop_boxed_719_ = lean_unbox_usize(v_stop_716_);
lean_dec(v_stop_716_);
v_res_720_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_713_, v_as_714_, v_i_boxed_718_, v_stop_boxed_719_, v_b_717_);
lean_dec_ref(v_as_714_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode(lean_object* v_s_721_, lean_object* v_r_722_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_723_ = l_ByteArray_empty;
v___x_724_ = lean_string_to_utf8(v_s_721_);
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = lean_byte_array_size(v___x_724_);
v___x_727_ = lean_nat_dec_lt(v___x_725_, v___x_726_);
if (v___x_727_ == 0)
{
lean_dec_ref(v___x_724_);
lean_dec_ref(v_r_722_);
return v___x_723_;
}
else
{
uint8_t v___x_728_; 
v___x_728_ = lean_nat_dec_le(v___x_726_, v___x_726_);
if (v___x_728_ == 0)
{
if (v___x_727_ == 0)
{
lean_dec_ref(v___x_724_);
lean_dec_ref(v_r_722_);
return v___x_723_;
}
else
{
size_t v___x_729_; size_t v___x_730_; lean_object* v___x_731_; 
v___x_729_ = ((size_t)0ULL);
v___x_730_ = lean_usize_of_nat(v___x_726_);
v___x_731_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_722_, v___x_724_, v___x_729_, v___x_730_, v___x_723_);
lean_dec_ref(v___x_724_);
return v___x_731_;
}
}
else
{
size_t v___x_732_; size_t v___x_733_; lean_object* v___x_734_; 
v___x_732_ = ((size_t)0ULL);
v___x_733_ = lean_usize_of_nat(v___x_726_);
v___x_734_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_722_, v___x_724_, v___x_732_, v___x_733_, v___x_723_);
lean_dec_ref(v___x_724_);
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode___boxed(lean_object* v_s_735_, lean_object* v_r_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_735_, v_r_736_);
lean_dec_ref(v_s_735_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___redArg(lean_object* v_es_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = lean_string_from_utf8_unchecked(v_es_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString(lean_object* v_r_740_, lean_object* v_es_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = lean_string_from_utf8_unchecked(v_es_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___boxed(lean_object* v_r_743_, lean_object* v_es_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Std_Http_URI_EncodedQueryString_toString(v_r_743_, v_es_744_);
lean_dec_ref(v_r_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(lean_object* v_len_746_, lean_object* v_rawBytes_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_fst_749_; lean_object* v_snd_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_816_; 
v_fst_749_ = lean_ctor_get(v_a_748_, 0);
v_snd_750_ = lean_ctor_get(v_a_748_, 1);
v_isSharedCheck_816_ = !lean_is_exclusive(v_a_748_);
if (v_isSharedCheck_816_ == 0)
{
v___x_752_ = v_a_748_;
v_isShared_753_ = v_isSharedCheck_816_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_snd_750_);
lean_inc(v_fst_749_);
lean_dec(v_a_748_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_816_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
uint8_t v___x_754_; 
v___x_754_ = lean_nat_dec_lt(v_snd_750_, v_len_746_);
if (v___x_754_ == 0)
{
lean_object* v___x_756_; 
if (v_isShared_753_ == 0)
{
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_fst_749_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_snd_750_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
else
{
uint8_t v_plus_758_; uint8_t v___x_759_; uint8_t v___x_768_; 
v_plus_758_ = 43;
v___x_759_ = lean_byte_array_fget(v_rawBytes_747_, v_snd_750_);
v___x_768_ = lean_uint8_dec_eq(v___x_759_, v_plus_758_);
if (v___x_768_ == 0)
{
uint8_t v_percent_769_; uint8_t v___x_770_; 
v_percent_769_ = 37;
v___x_770_ = lean_uint8_dec_eq(v___x_759_, v_percent_769_);
if (v___x_770_ == 0)
{
goto v___jp_760_;
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = lean_nat_add(v_snd_750_, v___x_771_);
v___x_773_ = lean_nat_dec_lt(v___x_772_, v_len_746_);
if (v___x_773_ == 0)
{
lean_dec(v___x_772_);
goto v___jp_760_;
}
else
{
uint8_t v___x_774_; lean_object* v___x_775_; 
lean_del_object(v___x_752_);
v___x_774_ = lean_byte_array_fget(v_rawBytes_747_, v___x_772_);
lean_dec(v___x_772_);
v___x_775_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_774_);
if (lean_obj_tag(v___x_775_) == 1)
{
lean_object* v_val_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v_val_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_val_776_);
lean_dec_ref_known(v___x_775_, 1);
v___x_777_ = lean_unsigned_to_nat(2u);
v___x_778_ = lean_nat_add(v_snd_750_, v___x_777_);
v___x_779_ = lean_nat_dec_lt(v___x_778_, v_len_746_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec(v_val_776_);
lean_dec(v_snd_750_);
v___x_780_ = lean_byte_array_push(v_fst_749_, v___x_759_);
v___x_781_ = lean_byte_array_push(v___x_780_, v___x_774_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v___x_778_);
v_a_748_ = v___x_782_;
goto _start;
}
else
{
uint8_t v___x_784_; lean_object* v___x_785_; 
v___x_784_ = lean_byte_array_fget(v_rawBytes_747_, v___x_778_);
lean_dec(v___x_778_);
v___x_785_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_784_);
if (lean_obj_tag(v___x_785_) == 1)
{
lean_object* v_val_786_; uint8_t v___x_787_; uint8_t v___x_788_; uint8_t v___x_789_; uint8_t v___x_790_; uint8_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_val_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_val_786_);
lean_dec_ref_known(v___x_785_, 1);
v___x_787_ = 4;
v___x_788_ = lean_unbox(v_val_776_);
lean_dec(v_val_776_);
v___x_789_ = lean_uint8_shift_left(v___x_788_, v___x_787_);
v___x_790_ = lean_unbox(v_val_786_);
lean_dec(v_val_786_);
v___x_791_ = lean_uint8_add(v___x_789_, v___x_790_);
v___x_792_ = lean_byte_array_push(v_fst_749_, v___x_791_);
v___x_793_ = lean_unsigned_to_nat(3u);
v___x_794_ = lean_nat_add(v_snd_750_, v___x_793_);
lean_dec(v_snd_750_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_792_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v_a_748_ = v___x_795_;
goto _start;
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec(v___x_785_);
lean_dec(v_val_776_);
v___x_797_ = lean_byte_array_push(v_fst_749_, v___x_759_);
v___x_798_ = lean_byte_array_push(v___x_797_, v___x_774_);
v___x_799_ = lean_byte_array_push(v___x_798_, v___x_784_);
v___x_800_ = lean_unsigned_to_nat(3u);
v___x_801_ = lean_nat_add(v_snd_750_, v___x_800_);
lean_dec(v_snd_750_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_799_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v_a_748_ = v___x_802_;
goto _start;
}
}
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec(v___x_775_);
v___x_804_ = lean_byte_array_push(v_fst_749_, v___x_759_);
v___x_805_ = lean_byte_array_push(v___x_804_, v___x_774_);
v___x_806_ = lean_unsigned_to_nat(2u);
v___x_807_ = lean_nat_add(v_snd_750_, v___x_806_);
lean_dec(v_snd_750_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_805_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v_a_748_ = v___x_808_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_del_object(v___x_752_);
v___x_810_ = 32;
v___x_811_ = lean_byte_array_push(v_fst_749_, v___x_810_);
v___x_812_ = lean_unsigned_to_nat(1u);
v___x_813_ = lean_nat_add(v_snd_750_, v___x_812_);
lean_dec(v_snd_750_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_811_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v_a_748_ = v___x_814_;
goto _start;
}
v___jp_760_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_761_ = lean_byte_array_push(v_fst_749_, v___x_759_);
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_add(v_snd_750_, v___x_762_);
lean_dec(v_snd_750_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 1, v___x_763_);
lean_ctor_set(v___x_752_, 0, v___x_761_);
v___x_765_ = v___x_752_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v___x_763_);
v___x_765_ = v_reuseFailAlloc_767_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
v_a_748_ = v___x_765_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg___boxed(lean_object* v_len_817_, lean_object* v_rawBytes_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_817_, v_rawBytes_818_, v_a_819_);
lean_dec_ref(v_rawBytes_818_);
lean_dec(v_len_817_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg(lean_object* v_es_821_){
_start:
{
lean_object* v_len_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_fst_825_; uint8_t v___x_826_; 
v_len_822_ = lean_byte_array_size(v_es_821_);
v___x_823_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_824_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_822_, v_es_821_, v___x_823_);
v_fst_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_fst_825_);
lean_dec_ref(v___x_824_);
v___x_826_ = lean_string_validate_utf8(v_fst_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; 
lean_dec(v_fst_825_);
v___x_827_ = lean_box(0);
return v___x_827_;
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_string_from_utf8_unchecked(v_fst_825_);
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg___boxed(lean_object* v_es_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_830_);
lean_dec_ref(v_es_830_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode(lean_object* v_r_832_, lean_object* v_es_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___boxed(lean_object* v_r_835_, lean_object* v_es_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Std_Http_URI_EncodedQueryString_decode(v_r_835_, v_es_836_);
lean_dec_ref(v_es_836_);
lean_dec_ref(v_r_835_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(lean_object* v_len_838_, lean_object* v_rawBytes_839_, lean_object* v_inst_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_838_, v_rawBytes_839_, v_a_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___boxed(lean_object* v_len_843_, lean_object* v_rawBytes_844_, lean_object* v_inst_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(v_len_843_, v_rawBytes_844_, v_inst_845_, v_a_846_);
lean_dec_ref(v_rawBytes_844_);
lean_dec(v_len_843_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringEncodedQueryString(lean_object* v_r_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = lean_alloc_closure((void*)(l_Std_Http_URI_EncodedQueryString_toString___boxed), 2, 1);
lean_closure_set(v___x_849_, 0, v_r_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString(lean_object* v_r_850_){
_start:
{
lean_object* v___f_851_; 
v___f_851_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___closed__0));
return v___f_851_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___boxed(lean_object* v_r_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Std_Http_URI_instReprEncodedQueryString(v_r_852_);
lean_dec_ref(v_r_852_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString(lean_object* v_r_854_){
_start:
{
lean_object* v___f_855_; 
v___f_855_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___closed__0));
return v___f_855_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___boxed(lean_object* v_r_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Std_Http_URI_instBEqEncodedQueryString(v_r_856_);
lean_dec_ref(v_r_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString(lean_object* v_r_858_){
_start:
{
lean_object* v___f_859_; 
v___f_859_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___closed__0));
return v___f_859_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___boxed(lean_object* v_r_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_Http_URI_instHashableEncodedQueryString(v_r_860_);
lean_dec_ref(v_r_860_);
return v_res_861_;
}
}
static uint64_t _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1(void){
_start:
{
lean_object* v___x_868_; uint64_t v___x_869_; 
v___x_868_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__0));
v___x_869_ = lean_byte_array_hash(v___x_868_);
return v___x_869_;
}
}
static lean_object* _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2));
v___x_877_ = lean_byte_array_size(v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT uint64_t l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0(lean_object* v_x_878_){
_start:
{
if (lean_obj_tag(v_x_878_) == 0)
{
uint64_t v___x_879_; 
v___x_879_ = lean_uint64_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1, &l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1);
return v___x_879_;
}
else
{
lean_object* v_val_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; uint64_t v___x_887_; 
v_val_880_ = lean_ctor_get(v_x_878_, 0);
v___x_881_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2));
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = lean_obj_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3, &l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3);
v___x_884_ = lean_byte_array_size(v_val_880_);
v___x_885_ = 0;
v___x_886_ = lean_byte_array_copy_slice(v_val_880_, v___x_882_, v___x_881_, v___x_883_, v___x_884_, v___x_885_);
v___x_887_ = lean_byte_array_hash(v___x_886_);
lean_dec_ref(v___x_886_);
return v___x_887_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___boxed(lean_object* v_x_888_){
_start:
{
uint64_t v_res_889_; lean_object* v_r_890_; 
v_res_889_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0(v_x_888_);
lean_dec(v_x_888_);
v_r_890_ = lean_box_uint64(v_res_889_);
return v_r_890_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString(lean_object* v_r_892_){
_start:
{
lean_object* v___f_893_; 
v___f_893_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___closed__0));
return v___f_893_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___boxed(lean_object* v_r_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_Http_URI_instHashableOptionEncodedQueryString(v_r_894_);
lean_dec_ref(v_r_894_);
return v_res_895_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0(void){
_start:
{
uint32_t v___x_896_; uint8_t v___x_897_; 
v___x_896_ = 58;
v___x_897_ = lean_uint32_to_uint8(v___x_896_);
return v___x_897_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1(void){
_start:
{
uint32_t v___x_898_; uint8_t v___x_899_; 
v___x_898_ = 64;
v___x_899_ = lean_uint32_to_uint8(v___x_898_);
return v___x_899_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2(void){
_start:
{
uint32_t v___x_900_; uint8_t v___x_901_; 
v___x_900_ = 38;
v___x_901_ = lean_uint32_to_uint8(v___x_900_);
return v___x_901_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3(void){
_start:
{
uint32_t v___x_902_; uint8_t v___x_903_; 
v___x_902_ = 39;
v___x_903_ = lean_uint32_to_uint8(v___x_902_);
return v___x_903_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4(void){
_start:
{
uint32_t v___x_904_; uint8_t v___x_905_; 
v___x_904_ = 40;
v___x_905_ = lean_uint32_to_uint8(v___x_904_);
return v___x_905_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5(void){
_start:
{
uint32_t v___x_906_; uint8_t v___x_907_; 
v___x_906_ = 41;
v___x_907_ = lean_uint32_to_uint8(v___x_906_);
return v___x_907_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6(void){
_start:
{
uint32_t v___x_908_; uint8_t v___x_909_; 
v___x_908_ = 42;
v___x_909_ = lean_uint32_to_uint8(v___x_908_);
return v___x_909_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7(void){
_start:
{
uint32_t v___x_910_; uint8_t v___x_911_; 
v___x_910_ = 44;
v___x_911_ = lean_uint32_to_uint8(v___x_910_);
return v___x_911_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8(void){
_start:
{
uint32_t v___x_912_; uint8_t v___x_913_; 
v___x_912_ = 59;
v___x_913_ = lean_uint32_to_uint8(v___x_912_);
return v___x_913_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9(void){
_start:
{
uint32_t v___x_914_; uint8_t v___x_915_; 
v___x_914_ = 61;
v___x_915_ = lean_uint32_to_uint8(v___x_914_);
return v___x_915_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10(void){
_start:
{
uint32_t v___x_916_; uint8_t v___x_917_; 
v___x_916_ = 33;
v___x_917_ = lean_uint32_to_uint8(v___x_916_);
return v___x_917_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11(void){
_start:
{
uint32_t v___x_918_; uint8_t v___x_919_; 
v___x_918_ = 36;
v___x_919_ = lean_uint32_to_uint8(v___x_918_);
return v___x_919_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12(void){
_start:
{
uint32_t v___x_920_; uint8_t v___x_921_; 
v___x_920_ = 95;
v___x_921_ = lean_uint32_to_uint8(v___x_920_);
return v___x_921_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13(void){
_start:
{
uint32_t v___x_922_; uint8_t v___x_923_; 
v___x_922_ = 126;
v___x_923_ = lean_uint32_to_uint8(v___x_922_);
return v___x_923_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14(void){
_start:
{
uint32_t v___x_924_; uint8_t v___x_925_; 
v___x_924_ = 45;
v___x_925_ = lean_uint32_to_uint8(v___x_924_);
return v___x_925_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15(void){
_start:
{
uint32_t v___x_926_; uint8_t v___x_927_; 
v___x_926_ = 46;
v___x_927_ = lean_uint32_to_uint8(v___x_926_);
return v___x_927_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16(void){
_start:
{
uint32_t v___x_928_; uint8_t v___x_929_; 
v___x_928_ = 90;
v___x_929_ = lean_uint32_to_uint8(v___x_928_);
return v___x_929_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17(void){
_start:
{
uint32_t v___x_930_; uint8_t v___x_931_; 
v___x_930_ = 122;
v___x_931_ = lean_uint32_to_uint8(v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0(uint8_t v___y_932_){
_start:
{
uint8_t v___y_934_; uint8_t v___y_940_; uint8_t v___y_960_; uint8_t v___y_966_; uint8_t v___y_972_; uint8_t v___y_978_; uint8_t v___y_984_; uint8_t v___x_989_; uint8_t v___x_990_; 
v___x_989_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_990_ = lean_uint8_dec_le(v___x_989_, v___y_932_);
if (v___x_990_ == 0)
{
v___y_984_ = v___x_990_;
goto v___jp_983_;
}
else
{
uint8_t v___x_991_; uint8_t v___x_992_; 
v___x_991_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_992_ = lean_uint8_dec_le(v___y_932_, v___x_991_);
v___y_984_ = v___x_992_;
goto v___jp_983_;
}
v___jp_933_:
{
if (v___y_934_ == 0)
{
uint8_t v___x_935_; uint8_t v___x_936_; 
v___x_935_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_936_ = lean_uint8_dec_eq(v___y_932_, v___x_935_);
if (v___x_936_ == 0)
{
uint8_t v___x_937_; uint8_t v___x_938_; 
v___x_937_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_938_ = lean_uint8_dec_eq(v___y_932_, v___x_937_);
return v___x_938_;
}
else
{
return v___x_936_;
}
}
else
{
return v___y_934_;
}
}
v___jp_939_:
{
if (v___y_940_ == 0)
{
uint8_t v___x_941_; uint8_t v___x_942_; 
v___x_941_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_942_ = lean_uint8_dec_eq(v___y_932_, v___x_941_);
if (v___x_942_ == 0)
{
uint8_t v___x_943_; uint8_t v___x_944_; 
v___x_943_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_944_ = lean_uint8_dec_eq(v___y_932_, v___x_943_);
if (v___x_944_ == 0)
{
uint8_t v___x_945_; uint8_t v___x_946_; 
v___x_945_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_946_ = lean_uint8_dec_eq(v___y_932_, v___x_945_);
if (v___x_946_ == 0)
{
uint8_t v___x_947_; uint8_t v___x_948_; 
v___x_947_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_948_ = lean_uint8_dec_eq(v___y_932_, v___x_947_);
if (v___x_948_ == 0)
{
uint8_t v___x_949_; uint8_t v___x_950_; 
v___x_949_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_950_ = lean_uint8_dec_eq(v___y_932_, v___x_949_);
if (v___x_950_ == 0)
{
uint8_t v___x_951_; uint8_t v___x_952_; 
v___x_951_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_952_ = lean_uint8_dec_eq(v___y_932_, v___x_951_);
if (v___x_952_ == 0)
{
uint8_t v___x_953_; uint8_t v___x_954_; 
v___x_953_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_954_ = lean_uint8_dec_eq(v___y_932_, v___x_953_);
if (v___x_954_ == 0)
{
uint8_t v___x_955_; uint8_t v___x_956_; 
v___x_955_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_956_ = lean_uint8_dec_eq(v___y_932_, v___x_955_);
if (v___x_956_ == 0)
{
uint8_t v___x_957_; uint8_t v___x_958_; 
v___x_957_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_958_ = lean_uint8_dec_eq(v___y_932_, v___x_957_);
v___y_934_ = v___x_958_;
goto v___jp_933_;
}
else
{
v___y_934_ = v___x_956_;
goto v___jp_933_;
}
}
else
{
v___y_934_ = v___x_954_;
goto v___jp_933_;
}
}
else
{
v___y_934_ = v___x_952_;
goto v___jp_933_;
}
}
else
{
v___y_934_ = v___x_950_;
goto v___jp_933_;
}
}
else
{
v___y_934_ = v___x_948_;
goto v___jp_933_;
}
}
else
{
v___y_934_ = v___x_946_;
goto v___jp_933_;
}
}
else
{
v___y_934_ = v___x_944_;
goto v___jp_933_;
}
}
else
{
v___y_934_ = v___x_942_;
goto v___jp_933_;
}
}
else
{
return v___y_940_;
}
}
v___jp_959_:
{
if (v___y_960_ == 0)
{
uint8_t v___x_961_; uint8_t v___x_962_; 
v___x_961_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_962_ = lean_uint8_dec_eq(v___y_932_, v___x_961_);
if (v___x_962_ == 0)
{
uint8_t v___x_963_; uint8_t v___x_964_; 
v___x_963_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_964_ = lean_uint8_dec_eq(v___y_932_, v___x_963_);
v___y_940_ = v___x_964_;
goto v___jp_939_;
}
else
{
v___y_940_ = v___x_962_;
goto v___jp_939_;
}
}
else
{
return v___y_960_;
}
}
v___jp_965_:
{
if (v___y_966_ == 0)
{
uint8_t v___x_967_; uint8_t v___x_968_; 
v___x_967_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_968_ = lean_uint8_dec_eq(v___y_932_, v___x_967_);
if (v___x_968_ == 0)
{
uint8_t v___x_969_; uint8_t v___x_970_; 
v___x_969_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_970_ = lean_uint8_dec_eq(v___y_932_, v___x_969_);
v___y_960_ = v___x_970_;
goto v___jp_959_;
}
else
{
v___y_960_ = v___x_968_;
goto v___jp_959_;
}
}
else
{
return v___y_966_;
}
}
v___jp_971_:
{
if (v___y_972_ == 0)
{
uint8_t v___x_973_; uint8_t v___x_974_; 
v___x_973_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_974_ = lean_uint8_dec_eq(v___y_932_, v___x_973_);
if (v___x_974_ == 0)
{
uint8_t v___x_975_; uint8_t v___x_976_; 
v___x_975_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_976_ = lean_uint8_dec_eq(v___y_932_, v___x_975_);
v___y_966_ = v___x_976_;
goto v___jp_965_;
}
else
{
v___y_966_ = v___x_974_;
goto v___jp_965_;
}
}
else
{
return v___y_972_;
}
}
v___jp_977_:
{
if (v___y_978_ == 0)
{
uint8_t v___x_979_; uint8_t v___x_980_; 
v___x_979_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_980_ = lean_uint8_dec_le(v___x_979_, v___y_932_);
if (v___x_980_ == 0)
{
v___y_972_ = v___x_980_;
goto v___jp_971_;
}
else
{
uint8_t v___x_981_; uint8_t v___x_982_; 
v___x_981_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_982_ = lean_uint8_dec_le(v___y_932_, v___x_981_);
v___y_972_ = v___x_982_;
goto v___jp_971_;
}
}
else
{
return v___y_978_;
}
}
v___jp_983_:
{
if (v___y_984_ == 0)
{
uint8_t v___x_985_; uint8_t v___x_986_; 
v___x_985_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_986_ = lean_uint8_dec_le(v___x_985_, v___y_932_);
if (v___x_986_ == 0)
{
v___y_978_ = v___x_986_;
goto v___jp_977_;
}
else
{
uint8_t v___x_987_; uint8_t v___x_988_; 
v___x_987_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_988_ = lean_uint8_dec_le(v___y_932_, v___x_987_);
v___y_978_ = v___x_988_;
goto v___jp_977_;
}
}
else
{
return v___y_984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___lam__0___boxed(lean_object* v___y_993_){
_start:
{
uint8_t v___y_318__boxed_994_; uint8_t v_res_995_; lean_object* v_r_996_; 
v___y_318__boxed_994_ = lean_unbox(v___y_993_);
v_res_995_ = l_Std_Http_URI_EncodedSegment_encode___lam__0(v___y_318__boxed_994_);
v_r_996_ = lean_box(v_res_995_);
return v_r_996_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode(lean_object* v_s_998_){
_start:
{
lean_object* v___f_999_; lean_object* v___x_1000_; 
v___f_999_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_1000_ = l_Std_Http_URI_EncodedString_encode(v___f_999_, v_s_998_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___boxed(lean_object* v_s_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Std_Http_URI_EncodedSegment_encode(v_s_1001_);
lean_dec_ref(v_s_1001_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object* v_ba_1003_){
_start:
{
lean_object* v___f_1004_; lean_object* v___x_1005_; 
v___f_1004_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_1005_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1004_, v_ba_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x21(lean_object* v_ba_1006_){
_start:
{
lean_object* v___f_1007_; lean_object* v___x_1008_; 
v___f_1007_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_1008_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1007_, v_ba_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object* v_segment_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Std_Http_URI_EncodedString_decode___redArg(v_segment_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode___boxed(lean_object* v_segment_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Std_Http_URI_EncodedSegment_decode(v_segment_1011_);
lean_dec_ref(v_segment_1011_);
return v_res_1012_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0(void){
_start:
{
uint32_t v___x_1013_; uint8_t v___x_1014_; 
v___x_1013_ = 47;
v___x_1014_ = lean_uint32_to_uint8(v___x_1013_);
return v___x_1014_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1(void){
_start:
{
uint32_t v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = 63;
v___x_1016_ = lean_uint32_to_uint8(v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedFragment_encode___lam__0(uint8_t v___y_1017_){
_start:
{
uint8_t v___y_1019_; uint8_t v___y_1025_; uint8_t v___y_1031_; uint8_t v___y_1051_; uint8_t v___y_1057_; uint8_t v___y_1063_; uint8_t v___y_1069_; uint8_t v___y_1075_; uint8_t v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1081_ = lean_uint8_dec_le(v___x_1080_, v___y_1017_);
if (v___x_1081_ == 0)
{
v___y_1075_ = v___x_1081_;
goto v___jp_1074_;
}
else
{
uint8_t v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1083_ = lean_uint8_dec_le(v___y_1017_, v___x_1082_);
v___y_1075_ = v___x_1083_;
goto v___jp_1074_;
}
v___jp_1018_:
{
if (v___y_1019_ == 0)
{
uint8_t v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0);
v___x_1021_ = lean_uint8_dec_eq(v___y_1017_, v___x_1020_);
if (v___x_1021_ == 0)
{
uint8_t v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1);
v___x_1023_ = lean_uint8_dec_eq(v___y_1017_, v___x_1022_);
return v___x_1023_;
}
else
{
return v___x_1021_;
}
}
else
{
return v___y_1019_;
}
}
v___jp_1024_:
{
if (v___y_1025_ == 0)
{
uint8_t v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_1027_ = lean_uint8_dec_eq(v___y_1017_, v___x_1026_);
if (v___x_1027_ == 0)
{
uint8_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_1029_ = lean_uint8_dec_eq(v___y_1017_, v___x_1028_);
v___y_1019_ = v___x_1029_;
goto v___jp_1018_;
}
else
{
v___y_1019_ = v___x_1027_;
goto v___jp_1018_;
}
}
else
{
return v___y_1025_;
}
}
v___jp_1030_:
{
if (v___y_1031_ == 0)
{
uint8_t v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1033_ = lean_uint8_dec_eq(v___y_1017_, v___x_1032_);
if (v___x_1033_ == 0)
{
uint8_t v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_1035_ = lean_uint8_dec_eq(v___y_1017_, v___x_1034_);
if (v___x_1035_ == 0)
{
uint8_t v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1037_ = lean_uint8_dec_eq(v___y_1017_, v___x_1036_);
if (v___x_1037_ == 0)
{
uint8_t v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1039_ = lean_uint8_dec_eq(v___y_1017_, v___x_1038_);
if (v___x_1039_ == 0)
{
uint8_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1041_ = lean_uint8_dec_eq(v___y_1017_, v___x_1040_);
if (v___x_1041_ == 0)
{
uint8_t v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1043_ = lean_uint8_dec_eq(v___y_1017_, v___x_1042_);
if (v___x_1043_ == 0)
{
uint8_t v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1045_ = lean_uint8_dec_eq(v___y_1017_, v___x_1044_);
if (v___x_1045_ == 0)
{
uint8_t v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1047_ = lean_uint8_dec_eq(v___y_1017_, v___x_1046_);
if (v___x_1047_ == 0)
{
uint8_t v___x_1048_; uint8_t v___x_1049_; 
v___x_1048_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1049_ = lean_uint8_dec_eq(v___y_1017_, v___x_1048_);
v___y_1025_ = v___x_1049_;
goto v___jp_1024_;
}
else
{
v___y_1025_ = v___x_1047_;
goto v___jp_1024_;
}
}
else
{
v___y_1025_ = v___x_1045_;
goto v___jp_1024_;
}
}
else
{
v___y_1025_ = v___x_1043_;
goto v___jp_1024_;
}
}
else
{
v___y_1025_ = v___x_1041_;
goto v___jp_1024_;
}
}
else
{
v___y_1025_ = v___x_1039_;
goto v___jp_1024_;
}
}
else
{
v___y_1025_ = v___x_1037_;
goto v___jp_1024_;
}
}
else
{
v___y_1025_ = v___x_1035_;
goto v___jp_1024_;
}
}
else
{
v___y_1025_ = v___x_1033_;
goto v___jp_1024_;
}
}
else
{
return v___y_1031_;
}
}
v___jp_1050_:
{
if (v___y_1051_ == 0)
{
uint8_t v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1053_ = lean_uint8_dec_eq(v___y_1017_, v___x_1052_);
if (v___x_1053_ == 0)
{
uint8_t v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1055_ = lean_uint8_dec_eq(v___y_1017_, v___x_1054_);
v___y_1031_ = v___x_1055_;
goto v___jp_1030_;
}
else
{
v___y_1031_ = v___x_1053_;
goto v___jp_1030_;
}
}
else
{
return v___y_1051_;
}
}
v___jp_1056_:
{
if (v___y_1057_ == 0)
{
uint8_t v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1059_ = lean_uint8_dec_eq(v___y_1017_, v___x_1058_);
if (v___x_1059_ == 0)
{
uint8_t v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1061_ = lean_uint8_dec_eq(v___y_1017_, v___x_1060_);
v___y_1051_ = v___x_1061_;
goto v___jp_1050_;
}
else
{
v___y_1051_ = v___x_1059_;
goto v___jp_1050_;
}
}
else
{
return v___y_1057_;
}
}
v___jp_1062_:
{
if (v___y_1063_ == 0)
{
uint8_t v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1065_ = lean_uint8_dec_eq(v___y_1017_, v___x_1064_);
if (v___x_1065_ == 0)
{
uint8_t v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1067_ = lean_uint8_dec_eq(v___y_1017_, v___x_1066_);
v___y_1057_ = v___x_1067_;
goto v___jp_1056_;
}
else
{
v___y_1057_ = v___x_1065_;
goto v___jp_1056_;
}
}
else
{
return v___y_1063_;
}
}
v___jp_1068_:
{
if (v___y_1069_ == 0)
{
uint8_t v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1071_ = lean_uint8_dec_le(v___x_1070_, v___y_1017_);
if (v___x_1071_ == 0)
{
v___y_1063_ = v___x_1071_;
goto v___jp_1062_;
}
else
{
uint8_t v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1073_ = lean_uint8_dec_le(v___y_1017_, v___x_1072_);
v___y_1063_ = v___x_1073_;
goto v___jp_1062_;
}
}
else
{
return v___y_1069_;
}
}
v___jp_1074_:
{
if (v___y_1075_ == 0)
{
uint8_t v___x_1076_; uint8_t v___x_1077_; 
v___x_1076_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1077_ = lean_uint8_dec_le(v___x_1076_, v___y_1017_);
if (v___x_1077_ == 0)
{
v___y_1069_ = v___x_1077_;
goto v___jp_1068_;
}
else
{
uint8_t v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1079_ = lean_uint8_dec_le(v___y_1017_, v___x_1078_);
v___y_1069_ = v___x_1079_;
goto v___jp_1068_;
}
}
else
{
return v___y_1075_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed(lean_object* v___y_1084_){
_start:
{
uint8_t v___y_312__boxed_1085_; uint8_t v_res_1086_; lean_object* v_r_1087_; 
v___y_312__boxed_1085_ = lean_unbox(v___y_1084_);
v_res_1086_ = l_Std_Http_URI_EncodedFragment_encode___lam__0(v___y_312__boxed_1085_);
v_r_1087_ = lean_box(v_res_1086_);
return v_r_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object* v_s_1089_){
_start:
{
lean_object* v___f_1090_; lean_object* v___x_1091_; 
v___f_1090_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1091_ = l_Std_Http_URI_EncodedString_encode(v___f_1090_, v_s_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___boxed(lean_object* v_s_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Std_Http_URI_EncodedFragment_encode(v_s_1092_);
lean_dec_ref(v_s_1092_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object* v_ba_1094_){
_start:
{
lean_object* v___f_1095_; lean_object* v___x_1096_; 
v___f_1095_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1096_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1095_, v_ba_1094_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x21(lean_object* v_ba_1097_){
_start:
{
lean_object* v___f_1098_; lean_object* v___x_1099_; 
v___f_1098_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1099_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1098_, v_ba_1097_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object* v_fragment_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Std_Http_URI_EncodedString_decode___redArg(v_fragment_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode___boxed(lean_object* v_fragment_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Std_Http_URI_EncodedFragment_decode(v_fragment_1102_);
lean_dec_ref(v_fragment_1102_);
return v_res_1103_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedUserInfo_encode___lam__0(uint8_t v___y_1104_){
_start:
{
uint8_t v___y_1106_; uint8_t v___y_1110_; uint8_t v___y_1130_; uint8_t v___y_1136_; uint8_t v___y_1142_; uint8_t v___y_1148_; uint8_t v___y_1154_; uint8_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1160_ = lean_uint8_dec_le(v___x_1159_, v___y_1104_);
if (v___x_1160_ == 0)
{
v___y_1154_ = v___x_1160_;
goto v___jp_1153_;
}
else
{
uint8_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1162_ = lean_uint8_dec_le(v___y_1104_, v___x_1161_);
v___y_1154_ = v___x_1162_;
goto v___jp_1153_;
}
v___jp_1105_:
{
if (v___y_1106_ == 0)
{
uint8_t v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_1108_ = lean_uint8_dec_eq(v___y_1104_, v___x_1107_);
return v___x_1108_;
}
else
{
return v___y_1106_;
}
}
v___jp_1109_:
{
if (v___y_1110_ == 0)
{
uint8_t v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1112_ = lean_uint8_dec_eq(v___y_1104_, v___x_1111_);
if (v___x_1112_ == 0)
{
uint8_t v___x_1113_; uint8_t v___x_1114_; 
v___x_1113_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_1114_ = lean_uint8_dec_eq(v___y_1104_, v___x_1113_);
if (v___x_1114_ == 0)
{
uint8_t v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1116_ = lean_uint8_dec_eq(v___y_1104_, v___x_1115_);
if (v___x_1116_ == 0)
{
uint8_t v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1118_ = lean_uint8_dec_eq(v___y_1104_, v___x_1117_);
if (v___x_1118_ == 0)
{
uint8_t v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1120_ = lean_uint8_dec_eq(v___y_1104_, v___x_1119_);
if (v___x_1120_ == 0)
{
uint8_t v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1122_ = lean_uint8_dec_eq(v___y_1104_, v___x_1121_);
if (v___x_1122_ == 0)
{
uint8_t v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1124_ = lean_uint8_dec_eq(v___y_1104_, v___x_1123_);
if (v___x_1124_ == 0)
{
uint8_t v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1126_ = lean_uint8_dec_eq(v___y_1104_, v___x_1125_);
if (v___x_1126_ == 0)
{
uint8_t v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1128_ = lean_uint8_dec_eq(v___y_1104_, v___x_1127_);
v___y_1106_ = v___x_1128_;
goto v___jp_1105_;
}
else
{
v___y_1106_ = v___x_1126_;
goto v___jp_1105_;
}
}
else
{
v___y_1106_ = v___x_1124_;
goto v___jp_1105_;
}
}
else
{
v___y_1106_ = v___x_1122_;
goto v___jp_1105_;
}
}
else
{
v___y_1106_ = v___x_1120_;
goto v___jp_1105_;
}
}
else
{
v___y_1106_ = v___x_1118_;
goto v___jp_1105_;
}
}
else
{
v___y_1106_ = v___x_1116_;
goto v___jp_1105_;
}
}
else
{
v___y_1106_ = v___x_1114_;
goto v___jp_1105_;
}
}
else
{
v___y_1106_ = v___x_1112_;
goto v___jp_1105_;
}
}
else
{
return v___y_1110_;
}
}
v___jp_1129_:
{
if (v___y_1130_ == 0)
{
uint8_t v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1132_ = lean_uint8_dec_eq(v___y_1104_, v___x_1131_);
if (v___x_1132_ == 0)
{
uint8_t v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1134_ = lean_uint8_dec_eq(v___y_1104_, v___x_1133_);
v___y_1110_ = v___x_1134_;
goto v___jp_1109_;
}
else
{
v___y_1110_ = v___x_1132_;
goto v___jp_1109_;
}
}
else
{
return v___y_1130_;
}
}
v___jp_1135_:
{
if (v___y_1136_ == 0)
{
uint8_t v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1138_ = lean_uint8_dec_eq(v___y_1104_, v___x_1137_);
if (v___x_1138_ == 0)
{
uint8_t v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1140_ = lean_uint8_dec_eq(v___y_1104_, v___x_1139_);
v___y_1130_ = v___x_1140_;
goto v___jp_1129_;
}
else
{
v___y_1130_ = v___x_1138_;
goto v___jp_1129_;
}
}
else
{
return v___y_1136_;
}
}
v___jp_1141_:
{
if (v___y_1142_ == 0)
{
uint8_t v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1144_ = lean_uint8_dec_eq(v___y_1104_, v___x_1143_);
if (v___x_1144_ == 0)
{
uint8_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1146_ = lean_uint8_dec_eq(v___y_1104_, v___x_1145_);
v___y_1136_ = v___x_1146_;
goto v___jp_1135_;
}
else
{
v___y_1136_ = v___x_1144_;
goto v___jp_1135_;
}
}
else
{
return v___y_1142_;
}
}
v___jp_1147_:
{
if (v___y_1148_ == 0)
{
uint8_t v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1150_ = lean_uint8_dec_le(v___x_1149_, v___y_1104_);
if (v___x_1150_ == 0)
{
v___y_1142_ = v___x_1150_;
goto v___jp_1141_;
}
else
{
uint8_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1152_ = lean_uint8_dec_le(v___y_1104_, v___x_1151_);
v___y_1142_ = v___x_1152_;
goto v___jp_1141_;
}
}
else
{
return v___y_1148_;
}
}
v___jp_1153_:
{
if (v___y_1154_ == 0)
{
uint8_t v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1156_ = lean_uint8_dec_le(v___x_1155_, v___y_1104_);
if (v___x_1156_ == 0)
{
v___y_1148_ = v___x_1156_;
goto v___jp_1147_;
}
else
{
uint8_t v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1158_ = lean_uint8_dec_le(v___y_1104_, v___x_1157_);
v___y_1148_ = v___x_1158_;
goto v___jp_1147_;
}
}
else
{
return v___y_1154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed(lean_object* v___y_1163_){
_start:
{
uint8_t v___y_271__boxed_1164_; uint8_t v_res_1165_; lean_object* v_r_1166_; 
v___y_271__boxed_1164_ = lean_unbox(v___y_1163_);
v_res_1165_ = l_Std_Http_URI_EncodedUserInfo_encode___lam__0(v___y_271__boxed_1164_);
v_r_1166_ = lean_box(v_res_1165_);
return v_r_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object* v_s_1168_){
_start:
{
lean_object* v___f_1169_; lean_object* v___x_1170_; 
v___f_1169_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1170_ = l_Std_Http_URI_EncodedString_encode(v___f_1169_, v_s_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___boxed(lean_object* v_s_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Std_Http_URI_EncodedUserInfo_encode(v_s_1171_);
lean_dec_ref(v_s_1171_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object* v_ba_1173_){
_start:
{
lean_object* v___f_1174_; lean_object* v___x_1175_; 
v___f_1174_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1175_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1174_, v_ba_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x21(lean_object* v_ba_1176_){
_start:
{
lean_object* v___f_1177_; lean_object* v___x_1178_; 
v___f_1177_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1178_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1177_, v_ba_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode(lean_object* v_userInfo_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Std_Http_URI_EncodedString_decode___redArg(v_userInfo_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode___boxed(lean_object* v_userInfo_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Std_Http_URI_EncodedUserInfo_decode(v_userInfo_1181_);
lean_dec_ref(v_userInfo_1181_);
return v_res_1182_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryParam_encode___lam__0(uint8_t v___y_1183_){
_start:
{
uint8_t v___y_1192_; uint8_t v___y_1194_; uint8_t v___y_1200_; uint8_t v___y_1206_; uint8_t v___y_1226_; uint8_t v___y_1232_; uint8_t v___y_1238_; uint8_t v___y_1244_; uint8_t v___y_1250_; uint8_t v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1256_ = lean_uint8_dec_le(v___x_1255_, v___y_1183_);
if (v___x_1256_ == 0)
{
v___y_1250_ = v___x_1256_;
goto v___jp_1249_;
}
else
{
uint8_t v___x_1257_; uint8_t v___x_1258_; 
v___x_1257_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1258_ = lean_uint8_dec_le(v___y_1183_, v___x_1257_);
v___y_1250_ = v___x_1258_;
goto v___jp_1249_;
}
v___jp_1184_:
{
uint8_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1186_ = lean_uint8_dec_eq(v___y_1183_, v___x_1185_);
if (v___x_1186_ == 0)
{
uint8_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1188_ = lean_uint8_dec_eq(v___y_1183_, v___x_1187_);
if (v___x_1188_ == 0)
{
uint8_t v___x_1189_; 
v___x_1189_ = 1;
return v___x_1189_;
}
else
{
return v___x_1186_;
}
}
else
{
uint8_t v___x_1190_; 
v___x_1190_ = 0;
return v___x_1190_;
}
}
v___jp_1191_:
{
if (v___y_1192_ == 0)
{
return v___y_1192_;
}
else
{
goto v___jp_1184_;
}
}
v___jp_1193_:
{
if (v___y_1194_ == 0)
{
uint8_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0);
v___x_1196_ = lean_uint8_dec_eq(v___y_1183_, v___x_1195_);
if (v___x_1196_ == 0)
{
uint8_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1);
v___x_1198_ = lean_uint8_dec_eq(v___y_1183_, v___x_1197_);
v___y_1192_ = v___x_1198_;
goto v___jp_1191_;
}
else
{
v___y_1192_ = v___x_1196_;
goto v___jp_1191_;
}
}
else
{
goto v___jp_1184_;
}
}
v___jp_1199_:
{
if (v___y_1200_ == 0)
{
uint8_t v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_1202_ = lean_uint8_dec_eq(v___y_1183_, v___x_1201_);
if (v___x_1202_ == 0)
{
uint8_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_1204_ = lean_uint8_dec_eq(v___y_1183_, v___x_1203_);
v___y_1194_ = v___x_1204_;
goto v___jp_1193_;
}
else
{
v___y_1194_ = v___x_1202_;
goto v___jp_1193_;
}
}
else
{
goto v___jp_1184_;
}
}
v___jp_1205_:
{
if (v___y_1206_ == 0)
{
uint8_t v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1208_ = lean_uint8_dec_eq(v___y_1183_, v___x_1207_);
if (v___x_1208_ == 0)
{
uint8_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_1210_ = lean_uint8_dec_eq(v___y_1183_, v___x_1209_);
if (v___x_1210_ == 0)
{
uint8_t v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1212_ = lean_uint8_dec_eq(v___y_1183_, v___x_1211_);
if (v___x_1212_ == 0)
{
uint8_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1214_ = lean_uint8_dec_eq(v___y_1183_, v___x_1213_);
if (v___x_1214_ == 0)
{
uint8_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1216_ = lean_uint8_dec_eq(v___y_1183_, v___x_1215_);
if (v___x_1216_ == 0)
{
uint8_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1218_ = lean_uint8_dec_eq(v___y_1183_, v___x_1217_);
if (v___x_1218_ == 0)
{
uint8_t v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1220_ = lean_uint8_dec_eq(v___y_1183_, v___x_1219_);
if (v___x_1220_ == 0)
{
uint8_t v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1222_ = lean_uint8_dec_eq(v___y_1183_, v___x_1221_);
if (v___x_1222_ == 0)
{
uint8_t v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1224_ = lean_uint8_dec_eq(v___y_1183_, v___x_1223_);
v___y_1200_ = v___x_1224_;
goto v___jp_1199_;
}
else
{
v___y_1200_ = v___x_1222_;
goto v___jp_1199_;
}
}
else
{
v___y_1200_ = v___x_1220_;
goto v___jp_1199_;
}
}
else
{
v___y_1200_ = v___x_1218_;
goto v___jp_1199_;
}
}
else
{
v___y_1200_ = v___x_1216_;
goto v___jp_1199_;
}
}
else
{
v___y_1200_ = v___x_1214_;
goto v___jp_1199_;
}
}
else
{
v___y_1200_ = v___x_1212_;
goto v___jp_1199_;
}
}
else
{
v___y_1200_ = v___x_1210_;
goto v___jp_1199_;
}
}
else
{
v___y_1200_ = v___x_1208_;
goto v___jp_1199_;
}
}
else
{
goto v___jp_1184_;
}
}
v___jp_1225_:
{
if (v___y_1226_ == 0)
{
uint8_t v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1228_ = lean_uint8_dec_eq(v___y_1183_, v___x_1227_);
if (v___x_1228_ == 0)
{
uint8_t v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1230_ = lean_uint8_dec_eq(v___y_1183_, v___x_1229_);
v___y_1206_ = v___x_1230_;
goto v___jp_1205_;
}
else
{
v___y_1206_ = v___x_1228_;
goto v___jp_1205_;
}
}
else
{
goto v___jp_1184_;
}
}
v___jp_1231_:
{
if (v___y_1232_ == 0)
{
uint8_t v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1234_ = lean_uint8_dec_eq(v___y_1183_, v___x_1233_);
if (v___x_1234_ == 0)
{
uint8_t v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1236_ = lean_uint8_dec_eq(v___y_1183_, v___x_1235_);
v___y_1226_ = v___x_1236_;
goto v___jp_1225_;
}
else
{
v___y_1226_ = v___x_1234_;
goto v___jp_1225_;
}
}
else
{
goto v___jp_1184_;
}
}
v___jp_1237_:
{
if (v___y_1238_ == 0)
{
uint8_t v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1240_ = lean_uint8_dec_eq(v___y_1183_, v___x_1239_);
if (v___x_1240_ == 0)
{
uint8_t v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1242_ = lean_uint8_dec_eq(v___y_1183_, v___x_1241_);
v___y_1232_ = v___x_1242_;
goto v___jp_1231_;
}
else
{
v___y_1232_ = v___x_1240_;
goto v___jp_1231_;
}
}
else
{
goto v___jp_1184_;
}
}
v___jp_1243_:
{
if (v___y_1244_ == 0)
{
uint8_t v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1246_ = lean_uint8_dec_le(v___x_1245_, v___y_1183_);
if (v___x_1246_ == 0)
{
v___y_1238_ = v___x_1246_;
goto v___jp_1237_;
}
else
{
uint8_t v___x_1247_; uint8_t v___x_1248_; 
v___x_1247_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1248_ = lean_uint8_dec_le(v___y_1183_, v___x_1247_);
v___y_1238_ = v___x_1248_;
goto v___jp_1237_;
}
}
else
{
goto v___jp_1184_;
}
}
v___jp_1249_:
{
if (v___y_1250_ == 0)
{
uint8_t v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1252_ = lean_uint8_dec_le(v___x_1251_, v___y_1183_);
if (v___x_1252_ == 0)
{
v___y_1244_ = v___x_1252_;
goto v___jp_1243_;
}
else
{
uint8_t v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1254_ = lean_uint8_dec_le(v___y_1183_, v___x_1253_);
v___y_1244_ = v___x_1254_;
goto v___jp_1243_;
}
}
else
{
goto v___jp_1184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed(lean_object* v___y_1259_){
_start:
{
uint8_t v___y_362__boxed_1260_; uint8_t v_res_1261_; lean_object* v_r_1262_; 
v___y_362__boxed_1260_ = lean_unbox(v___y_1259_);
v_res_1261_ = l_Std_Http_URI_EncodedQueryParam_encode___lam__0(v___y_362__boxed_1260_);
v_r_1262_ = lean_box(v_res_1261_);
return v_r_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode(lean_object* v_s_1264_){
_start:
{
lean_object* v___f_1265_; lean_object* v___x_1266_; 
v___f_1265_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1266_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_1264_, v___f_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___boxed(lean_object* v_s_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Std_Http_URI_EncodedQueryParam_encode(v_s_1267_);
lean_dec_ref(v_s_1267_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f(lean_object* v_ba_1269_){
_start:
{
lean_object* v___f_1270_; lean_object* v___x_1271_; 
v___f_1270_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1271_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_1269_, v___f_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x21(lean_object* v_ba_1272_){
_start:
{
lean_object* v___f_1273_; lean_object* v___x_1274_; 
v___f_1273_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1274_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v_ba_1272_, v___f_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object* v_s_1275_){
_start:
{
lean_object* v___f_1276_; lean_object* v___x_1277_; 
v___f_1276_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1277_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_1275_, v___f_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f___boxed(lean_object* v_s_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_s_1278_);
lean_dec_ref(v_s_1278_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object* v_param_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_param_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode___boxed(lean_object* v_param_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Std_Http_URI_EncodedQueryParam_decode(v_param_1282_);
lean_dec_ref(v_param_1282_);
return v_res_1283_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Bitwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal_Char(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_URI_Encoding(uint8_t builtin) {
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
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_URI_Encoding(uint8_t builtin) {
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
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Std_Http_Internal_Char(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_URI_Encoding(uint8_t builtin) {
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
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Internal_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_URI_Encoding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_URI_Encoding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_URI_Encoding(builtin);
}
#ifdef __cplusplus
}
#endif
