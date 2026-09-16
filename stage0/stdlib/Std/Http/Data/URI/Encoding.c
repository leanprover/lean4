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
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
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
uint8_t v___x_17_; uint8_t v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; uint8_t v___y_22_; uint8_t v___y_26_; uint8_t v___x_39_; uint8_t v___x_40_; 
v___x_17_ = 128;
v___x_18_ = lean_uint8_dec_lt(v_c_16_, v___x_17_);
v___x_19_ = lean_box(v_c_16_);
v___x_20_ = lean_apply_1(v_rule_15_, v___x_19_);
v___x_39_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_40_ = lean_uint8_dec_le(v___x_39_, v_c_16_);
if (v___x_40_ == 0)
{
goto v___jp_34_;
}
else
{
uint8_t v___x_41_; uint8_t v___x_42_; 
v___x_41_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_42_ = lean_uint8_dec_le(v_c_16_, v___x_41_);
if (v___x_42_ == 0)
{
goto v___jp_34_;
}
else
{
v___y_26_ = v___x_42_;
goto v___jp_25_;
}
}
v___jp_21_:
{
uint8_t v___x_23_; 
v___x_23_ = lean_unbox(v___x_20_);
if (v___x_23_ == 0)
{
if (v___x_18_ == 0)
{
return v___x_18_;
}
else
{
return v___y_22_;
}
}
else
{
if (v___x_18_ == 0)
{
return v___x_18_;
}
else
{
uint8_t v___x_24_; 
v___x_24_ = lean_unbox(v___x_20_);
return v___x_24_;
}
}
}
v___jp_25_:
{
if (v___y_26_ == 0)
{
uint8_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__0, &l_Std_Http_URI_isEncodedChar___closed__0_once, _init_l_Std_Http_URI_isEncodedChar___closed__0);
v___x_28_ = lean_uint8_dec_eq(v_c_16_, v___x_27_);
v___y_22_ = v___x_28_;
goto v___jp_21_;
}
else
{
v___y_22_ = v___y_26_;
goto v___jp_21_;
}
}
v___jp_29_:
{
uint8_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_31_ = lean_uint8_dec_le(v___x_30_, v_c_16_);
if (v___x_31_ == 0)
{
v___y_26_ = v___x_31_;
goto v___jp_25_;
}
else
{
uint8_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__2, &l_Std_Http_URI_isEncodedChar___closed__2_once, _init_l_Std_Http_URI_isEncodedChar___closed__2);
v___x_33_ = lean_uint8_dec_le(v_c_16_, v___x_32_);
v___y_26_ = v___x_33_;
goto v___jp_25_;
}
}
v___jp_34_:
{
uint8_t v___x_35_; uint8_t v___x_36_; 
v___x_35_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_36_ = lean_uint8_dec_le(v___x_35_, v_c_16_);
if (v___x_36_ == 0)
{
goto v___jp_29_;
}
else
{
uint8_t v___x_37_; uint8_t v___x_38_; 
v___x_37_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__4, &l_Std_Http_URI_isEncodedChar___closed__4_once, _init_l_Std_Http_URI_isEncodedChar___closed__4);
v___x_38_ = lean_uint8_dec_le(v_c_16_, v___x_37_);
if (v___x_38_ == 0)
{
goto v___jp_29_;
}
else
{
v___y_26_ = v___x_38_;
goto v___jp_25_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isEncodedChar___boxed(lean_object* v_rule_43_, lean_object* v_c_44_){
_start:
{
uint8_t v_c_boxed_45_; uint8_t v_res_46_; lean_object* v_r_47_; 
v_c_boxed_45_ = lean_unbox(v_c_44_);
v_res_46_ = l_Std_Http_URI_isEncodedChar(v_rule_43_, v_c_boxed_45_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
static uint8_t _init_l_Std_Http_URI_isEncodedQueryChar___closed__0(void){
_start:
{
uint32_t v___x_48_; uint8_t v___x_49_; 
v___x_48_ = 43;
v___x_49_ = lean_uint32_to_uint8(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isEncodedQueryChar(lean_object* v_rule_50_, uint8_t v_c_51_){
_start:
{
uint8_t v___x_52_; 
v___x_52_ = l_Std_Http_URI_isEncodedChar(v_rule_50_, v_c_51_);
if (v___x_52_ == 0)
{
uint8_t v___x_53_; uint8_t v___x_54_; 
v___x_53_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_54_ = lean_uint8_dec_eq(v_c_51_, v___x_53_);
return v___x_54_;
}
else
{
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isEncodedQueryChar___boxed(lean_object* v_rule_55_, lean_object* v_c_56_){
_start:
{
uint8_t v_c_boxed_57_; uint8_t v_res_58_; lean_object* v_r_59_; 
v_c_boxed_57_ = lean_unbox(v_c_56_);
v_res_58_ = l_Std_Http_URI_isEncodedQueryChar(v_rule_55_, v_c_boxed_57_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(lean_object* v_r_60_, uint8_t v___x_61_, uint8_t v_v_62_){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = l_Std_Http_URI_isEncodedChar(v_r_60_, v_v_62_);
if (v___x_63_ == 0)
{
return v___x_61_;
}
else
{
uint8_t v___x_64_; 
v___x_64_ = 0;
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed(lean_object* v_r_65_, lean_object* v___x_66_, lean_object* v_v_67_){
_start:
{
uint8_t v___x_61__boxed_68_; uint8_t v_v_boxed_69_; uint8_t v_res_70_; lean_object* v_r_71_; 
v___x_61__boxed_68_ = lean_unbox(v___x_66_);
v_v_boxed_69_ = lean_unbox(v_v_67_);
v_res_70_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(v_r_65_, v___x_61__boxed_68_, v_v_boxed_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars(lean_object* v_r_91_, lean_object* v_s_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_93_ = lean_byte_array_data(v_s_92_);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_array_get_size(v___x_93_);
v___x_96_ = ((lean_object*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9));
v___x_97_ = lean_nat_dec_lt(v___x_94_, v___x_95_);
if (v___x_97_ == 0)
{
uint8_t v___x_98_; 
lean_dec_ref(v___x_93_);
lean_dec_ref(v_r_91_);
v___x_98_ = 1;
return v___x_98_;
}
else
{
if (v___x_97_ == 0)
{
lean_dec_ref(v___x_93_);
lean_dec_ref(v_r_91_);
return v___x_97_;
}
else
{
lean_object* v___x_99_; lean_object* v___f_100_; size_t v___x_101_; size_t v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_99_ = lean_box(v___x_97_);
v___f_100_ = lean_alloc_closure((void*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed), 3, 2);
lean_closure_set(v___f_100_, 0, v_r_91_);
lean_closure_set(v___f_100_, 1, v___x_99_);
v___x_101_ = ((size_t)0ULL);
v___x_102_ = lean_usize_of_nat(v___x_95_);
v___x_103_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_96_, v___f_100_, v___x_93_, v___x_101_, v___x_102_);
v___x_104_ = lean_unbox(v___x_103_);
lean_dec(v___x_103_);
if (v___x_104_ == 0)
{
return v___x_97_;
}
else
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___boxed(lean_object* v_r_106_, lean_object* v_s_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_106_, v_s_107_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(lean_object* v_r_110_, uint8_t v___x_111_, uint8_t v_v_112_){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = l_Std_Http_URI_isEncodedQueryChar(v_r_110_, v_v_112_);
if (v___x_113_ == 0)
{
return v___x_111_;
}
else
{
uint8_t v___x_114_; 
v___x_114_ = 0;
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed(lean_object* v_r_115_, lean_object* v___x_116_, lean_object* v_v_117_){
_start:
{
uint8_t v___x_61__boxed_118_; uint8_t v_v_boxed_119_; uint8_t v_res_120_; lean_object* v_r_121_; 
v___x_61__boxed_118_ = lean_unbox(v___x_116_);
v_v_boxed_119_ = lean_unbox(v_v_117_);
v_res_120_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(v_r_115_, v___x_61__boxed_118_, v_v_boxed_119_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(lean_object* v_r_122_, lean_object* v_s_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_124_ = lean_byte_array_data(v_s_123_);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_array_get_size(v___x_124_);
v___x_127_ = ((lean_object*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9));
v___x_128_ = lean_nat_dec_lt(v___x_125_, v___x_126_);
if (v___x_128_ == 0)
{
uint8_t v___x_129_; 
lean_dec_ref(v___x_124_);
lean_dec_ref(v_r_122_);
v___x_129_ = 1;
return v___x_129_;
}
else
{
if (v___x_128_ == 0)
{
lean_dec_ref(v___x_124_);
lean_dec_ref(v_r_122_);
return v___x_128_;
}
else
{
lean_object* v___x_130_; lean_object* v___f_131_; size_t v___x_132_; size_t v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_130_ = lean_box(v___x_128_);
v___f_131_ = lean_alloc_closure((void*)(l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed), 3, 2);
lean_closure_set(v___f_131_, 0, v_r_122_);
lean_closure_set(v___f_131_, 1, v___x_130_);
v___x_132_ = ((size_t)0ULL);
v___x_133_ = lean_usize_of_nat(v___x_126_);
v___x_134_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_127_, v___f_131_, v___x_124_, v___x_132_, v___x_133_);
v___x_135_ = lean_unbox(v___x_134_);
lean_dec(v___x_134_);
if (v___x_135_ == 0)
{
return v___x_128_;
}
else
{
uint8_t v___x_136_; 
v___x_136_ = 0;
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___boxed(lean_object* v_r_137_, lean_object* v_s_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_137_, v_s_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(lean_object* v_ba_141_, lean_object* v_i_142_){
_start:
{
lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_147_ = lean_byte_array_size(v_ba_141_);
v___x_148_ = lean_nat_dec_lt(v_i_142_, v___x_147_);
if (v___x_148_ == 0)
{
uint8_t v___x_149_; 
lean_dec(v_i_142_);
v___x_149_ = 1;
return v___x_149_;
}
else
{
uint8_t v_c_150_; uint8_t v___x_151_; uint8_t v___x_152_; 
v_c_150_ = lean_byte_array_fget(v_ba_141_, v_i_142_);
v___x_151_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__0, &l_Std_Http_URI_isEncodedChar___closed__0_once, _init_l_Std_Http_URI_isEncodedChar___closed__0);
v___x_152_ = lean_uint8_dec_eq(v_c_150_, v___x_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = lean_nat_add(v_i_142_, v___x_153_);
lean_dec(v_i_142_);
v_i_142_ = v___x_154_;
goto _start;
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_156_ = lean_unsigned_to_nat(2u);
v___x_157_ = lean_nat_add(v_i_142_, v___x_156_);
v___x_158_ = lean_nat_dec_lt(v___x_157_, v___x_147_);
if (v___x_158_ == 0)
{
lean_dec(v___x_157_);
lean_dec(v_i_142_);
return v___x_158_;
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v_d1_161_; uint8_t v_d2_162_; uint8_t v___x_188_; uint8_t v___x_189_; 
v___x_159_ = lean_unsigned_to_nat(1u);
v___x_160_ = lean_nat_add(v_i_142_, v___x_159_);
v_d1_161_ = lean_byte_array_fget(v_ba_141_, v___x_160_);
lean_dec(v___x_160_);
v_d2_162_ = lean_byte_array_fget(v_ba_141_, v___x_157_);
lean_dec(v___x_157_);
v___x_188_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_189_ = lean_uint8_dec_le(v___x_188_, v_d1_161_);
if (v___x_189_ == 0)
{
goto v___jp_183_;
}
else
{
uint8_t v___x_190_; uint8_t v___x_191_; 
v___x_190_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_191_ = lean_uint8_dec_le(v_d1_161_, v___x_190_);
if (v___x_191_ == 0)
{
goto v___jp_183_;
}
else
{
goto v___jp_173_;
}
}
v___jp_163_:
{
uint8_t v___x_164_; uint8_t v___x_165_; 
v___x_164_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_165_ = lean_uint8_dec_le(v___x_164_, v_d2_162_);
if (v___x_165_ == 0)
{
lean_dec(v_i_142_);
return v___x_165_;
}
else
{
uint8_t v___x_166_; uint8_t v___x_167_; 
v___x_166_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__2, &l_Std_Http_URI_isEncodedChar___closed__2_once, _init_l_Std_Http_URI_isEncodedChar___closed__2);
v___x_167_ = lean_uint8_dec_le(v_d2_162_, v___x_166_);
if (v___x_167_ == 0)
{
lean_dec(v_i_142_);
return v___x_167_;
}
else
{
goto v___jp_143_;
}
}
}
v___jp_168_:
{
uint8_t v___x_169_; uint8_t v___x_170_; 
v___x_169_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_170_ = lean_uint8_dec_le(v___x_169_, v_d2_162_);
if (v___x_170_ == 0)
{
goto v___jp_163_;
}
else
{
uint8_t v___x_171_; uint8_t v___x_172_; 
v___x_171_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__4, &l_Std_Http_URI_isEncodedChar___closed__4_once, _init_l_Std_Http_URI_isEncodedChar___closed__4);
v___x_172_ = lean_uint8_dec_le(v_d2_162_, v___x_171_);
if (v___x_172_ == 0)
{
goto v___jp_163_;
}
else
{
goto v___jp_143_;
}
}
}
v___jp_173_:
{
uint8_t v___x_174_; uint8_t v___x_175_; 
v___x_174_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_175_ = lean_uint8_dec_le(v___x_174_, v_d2_162_);
if (v___x_175_ == 0)
{
goto v___jp_168_;
}
else
{
uint8_t v___x_176_; uint8_t v___x_177_; 
v___x_176_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_177_ = lean_uint8_dec_le(v_d2_162_, v___x_176_);
if (v___x_177_ == 0)
{
goto v___jp_168_;
}
else
{
goto v___jp_143_;
}
}
}
v___jp_178_:
{
uint8_t v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_180_ = lean_uint8_dec_le(v___x_179_, v_d1_161_);
if (v___x_180_ == 0)
{
lean_dec(v_i_142_);
return v___x_180_;
}
else
{
uint8_t v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__2, &l_Std_Http_URI_isEncodedChar___closed__2_once, _init_l_Std_Http_URI_isEncodedChar___closed__2);
v___x_182_ = lean_uint8_dec_le(v_d1_161_, v___x_181_);
if (v___x_182_ == 0)
{
lean_dec(v_i_142_);
return v___x_182_;
}
else
{
goto v___jp_173_;
}
}
}
v___jp_183_:
{
uint8_t v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_185_ = lean_uint8_dec_le(v___x_184_, v_d1_161_);
if (v___x_185_ == 0)
{
goto v___jp_178_;
}
else
{
uint8_t v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__4, &l_Std_Http_URI_isEncodedChar___closed__4_once, _init_l_Std_Http_URI_isEncodedChar___closed__4);
v___x_187_ = lean_uint8_dec_le(v_d1_161_, v___x_186_);
if (v___x_187_ == 0)
{
goto v___jp_178_;
}
else
{
goto v___jp_173_;
}
}
}
}
}
}
v___jp_143_:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(3u);
v___x_145_ = lean_nat_add(v_i_142_, v___x_144_);
lean_dec(v_i_142_);
v_i_142_ = v___x_145_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop___boxed(lean_object* v_ba_192_, lean_object* v_i_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_192_, v_i_193_);
lean_dec_ref(v_ba_192_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidPercentEncoding(lean_object* v_ba_196_){
_start:
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_196_, v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidPercentEncoding___boxed(lean_object* v_ba_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_199_);
lean_dec_ref(v_ba_199_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_hexDigit(uint8_t v_n_202_){
_start:
{
uint8_t v___x_203_; uint8_t v___x_204_; 
v___x_203_ = 10;
v___x_204_ = lean_uint8_dec_lt(v_n_202_, v___x_203_);
if (v___x_204_ == 0)
{
uint8_t v___x_205_; uint8_t v___x_206_; uint8_t v___x_207_; 
v___x_205_ = lean_uint8_sub(v_n_202_, v___x_203_);
v___x_206_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_207_ = lean_uint8_add(v___x_205_, v___x_206_);
return v___x_207_;
}
else
{
uint8_t v___x_208_; uint8_t v___x_209_; 
v___x_208_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_209_ = lean_uint8_add(v_n_202_, v___x_208_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigit___boxed(lean_object* v_n_210_){
_start:
{
uint8_t v_n_boxed_211_; uint8_t v_res_212_; lean_object* v_r_213_; 
v_n_boxed_211_ = lean_unbox(v_n_210_);
v_res_212_ = l_Std_Http_URI_hexDigit(v_n_boxed_211_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f(uint8_t v_c_214_){
_start:
{
uint8_t v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_238_ = lean_uint8_dec_le(v___x_237_, v_c_214_);
if (v___x_238_ == 0)
{
goto v___jp_227_;
}
else
{
uint8_t v___x_239_; uint8_t v___x_240_; 
v___x_239_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_240_ = lean_uint8_dec_le(v_c_214_, v___x_239_);
if (v___x_240_ == 0)
{
goto v___jp_227_;
}
else
{
uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_uint8_sub(v_c_214_, v___x_237_);
v___x_242_ = lean_box(v___x_241_);
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
v___jp_215_:
{
uint8_t v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_217_ = lean_uint8_dec_le(v___x_216_, v_c_214_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; 
v___x_218_ = lean_box(0);
return v___x_218_;
}
else
{
uint8_t v___x_219_; uint8_t v___x_220_; 
v___x_219_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__2, &l_Std_Http_URI_isEncodedChar___closed__2_once, _init_l_Std_Http_URI_isEncodedChar___closed__2);
v___x_220_ = lean_uint8_dec_le(v_c_214_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_box(0);
return v___x_221_;
}
else
{
uint8_t v___x_222_; uint8_t v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_222_ = lean_uint8_sub(v_c_214_, v___x_216_);
v___x_223_ = 10;
v___x_224_ = lean_uint8_add(v___x_222_, v___x_223_);
v___x_225_ = lean_box(v___x_224_);
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
}
v___jp_227_:
{
uint8_t v___x_228_; uint8_t v___x_229_; 
v___x_228_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_229_ = lean_uint8_dec_le(v___x_228_, v_c_214_);
if (v___x_229_ == 0)
{
goto v___jp_215_;
}
else
{
uint8_t v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__4, &l_Std_Http_URI_isEncodedChar___closed__4_once, _init_l_Std_Http_URI_isEncodedChar___closed__4);
v___x_231_ = lean_uint8_dec_le(v_c_214_, v___x_230_);
if (v___x_231_ == 0)
{
goto v___jp_215_;
}
else
{
uint8_t v___x_232_; uint8_t v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_232_ = lean_uint8_sub(v_c_214_, v___x_228_);
v___x_233_ = 10;
v___x_234_ = lean_uint8_add(v___x_232_, v___x_233_);
v___x_235_ = lean_box(v___x_234_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f___boxed(lean_object* v_c_244_){
_start:
{
uint8_t v_c_boxed_245_; lean_object* v_res_246_; 
v_c_boxed_245_ = lean_unbox(v_c_244_);
v_res_246_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_c_boxed_245_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(lean_object* v_x_247_, uint8_t v_x_248_, lean_object* v_h__1_249_){
_start:
{
lean_object* v_data_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_data_250_ = lean_byte_array_data(v_x_247_);
v___x_251_ = lean_box(v_x_248_);
v___x_252_ = lean_apply_2(v_h__1_249_, v_data_250_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg___boxed(lean_object* v_x_253_, lean_object* v_x_254_, lean_object* v_h__1_255_){
_start:
{
uint8_t v_x_17__boxed_256_; lean_object* v_res_257_; 
v_x_17__boxed_256_ = lean_unbox(v_x_254_);
v_res_257_ = l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(v_x_253_, v_x_17__boxed_256_, v_h__1_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(lean_object* v_motive_258_, lean_object* v_x_259_, uint8_t v_x_260_, lean_object* v_h__1_261_){
_start:
{
lean_object* v_data_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_data_262_ = lean_byte_array_data(v_x_259_);
v___x_263_ = lean_box(v_x_260_);
v___x_264_ = lean_apply_2(v_h__1_261_, v_data_262_, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___boxed(lean_object* v_motive_265_, lean_object* v_x_266_, lean_object* v_x_267_, lean_object* v_h__1_268_){
_start:
{
uint8_t v_x_29__boxed_269_; lean_object* v_res_270_; 
v_x_29__boxed_269_ = lean_unbox(v_x_267_);
v_res_270_ = l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(v_motive_265_, v_x_266_, v_x_29__boxed_269_, v_h__1_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter___redArg(lean_object* v_x_271_, lean_object* v_x_272_, lean_object* v_h__1_273_, lean_object* v_h__2_274_){
_start:
{
if (lean_obj_tag(v_x_271_) == 0)
{
lean_object* v___x_275_; 
lean_dec(v_h__2_274_);
v___x_275_ = lean_apply_1(v_h__1_273_, v_x_272_);
return v___x_275_;
}
else
{
lean_object* v_head_276_; lean_object* v_tail_277_; lean_object* v___x_278_; 
lean_dec(v_h__1_273_);
v_head_276_ = lean_ctor_get(v_x_271_, 0);
lean_inc(v_head_276_);
v_tail_277_ = lean_ctor_get(v_x_271_, 1);
lean_inc(v_tail_277_);
lean_dec_ref_known(v_x_271_, 2);
v___x_278_ = lean_apply_3(v_h__2_274_, v_head_276_, v_tail_277_, v_x_272_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter(lean_object* v_motive_279_, lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v_h__1_282_, lean_object* v_h__2_283_){
_start:
{
if (lean_obj_tag(v_x_280_) == 0)
{
lean_object* v___x_284_; 
lean_dec(v_h__2_283_);
v___x_284_ = lean_apply_1(v_h__1_282_, v_x_281_);
return v___x_284_;
}
else
{
lean_object* v_head_285_; lean_object* v_tail_286_; lean_object* v___x_287_; 
lean_dec(v_h__1_282_);
v_head_285_ = lean_ctor_get(v_x_280_, 0);
lean_inc(v_head_285_);
v_tail_286_ = lean_ctor_get(v_x_280_, 1);
lean_inc(v_tail_286_);
lean_dec_ref_known(v_x_280_, 2);
v___x_287_ = lean_apply_3(v_h__2_283_, v_head_285_, v_tail_286_, v_x_281_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty(lean_object* v_r_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_ByteArray_empty;
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___boxed(lean_object* v_r_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Std_Http_URI_EncodedString_empty(v_r_290_);
lean_dec_ref(v_r_290_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited(lean_object* v_r_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_ByteArray_empty;
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___boxed(lean_object* v_r_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Std_Http_URI_EncodedString_instInhabited(v_r_294_);
lean_dec_ref(v_r_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(lean_object* v_s_296_, uint8_t v_c_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = lean_byte_array_push(v_s_296_, v_c_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg___boxed(lean_object* v_s_299_, lean_object* v_c_300_){
_start:
{
uint8_t v_c_boxed_301_; lean_object* v_res_302_; 
v_c_boxed_301_ = lean_unbox(v_c_300_);
v_res_302_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(v_s_299_, v_c_boxed_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(lean_object* v_r_303_, lean_object* v_s_304_, uint8_t v_c_305_, lean_object* v_h_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = lean_byte_array_push(v_s_304_, v_c_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___boxed(lean_object* v_r_308_, lean_object* v_s_309_, lean_object* v_c_310_, lean_object* v_h_311_){
_start:
{
uint8_t v_c_boxed_312_; lean_object* v_res_313_; 
v_c_boxed_312_ = lean_unbox(v_c_310_);
v_res_313_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(v_r_308_, v_s_309_, v_c_boxed_312_, v_h_311_);
lean_dec_ref(v_r_308_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(uint8_t v_b_314_, lean_object* v_s_315_){
_start:
{
uint8_t v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; uint8_t v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; uint8_t v___x_323_; uint8_t v___x_324_; lean_object* v_ba_325_; 
v___x_316_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__0, &l_Std_Http_URI_isEncodedChar___closed__0_once, _init_l_Std_Http_URI_isEncodedChar___closed__0);
v___x_317_ = lean_byte_array_push(v_s_315_, v___x_316_);
v___x_318_ = 4;
v___x_319_ = lean_uint8_shift_right(v_b_314_, v___x_318_);
v___x_320_ = l_Std_Http_URI_hexDigit(v___x_319_);
v___x_321_ = lean_byte_array_push(v___x_317_, v___x_320_);
v___x_322_ = 15;
v___x_323_ = lean_uint8_land(v_b_314_, v___x_322_);
v___x_324_ = l_Std_Http_URI_hexDigit(v___x_323_);
v_ba_325_ = lean_byte_array_push(v___x_321_, v___x_324_);
return v_ba_325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg___boxed(lean_object* v_b_326_, lean_object* v_s_327_){
_start:
{
uint8_t v_b_boxed_328_; lean_object* v_res_329_; 
v_b_boxed_328_ = lean_unbox(v_b_326_);
v_res_329_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_boxed_328_, v_s_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(lean_object* v_r_330_, uint8_t v_b_331_, lean_object* v_s_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_331_, v_s_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___boxed(lean_object* v_r_334_, lean_object* v_b_335_, lean_object* v_s_336_){
_start:
{
uint8_t v_b_boxed_337_; lean_object* v_res_338_; 
v_b_boxed_337_ = lean_unbox(v_b_335_);
v_res_338_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(v_r_334_, v_b_boxed_337_, v_s_336_);
lean_dec_ref(v_r_334_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(lean_object* v_r_339_, lean_object* v_as_340_, size_t v_i_341_, size_t v_stop_342_, lean_object* v_b_343_){
_start:
{
lean_object* v___y_345_; uint8_t v___x_349_; 
v___x_349_ = lean_usize_dec_eq(v_i_341_, v_stop_342_);
if (v___x_349_ == 0)
{
uint8_t v___x_350_; uint8_t v___y_352_; uint8_t v___x_355_; uint8_t v___x_356_; 
v___x_350_ = lean_byte_array_uget(v_as_340_, v_i_341_);
v___x_355_ = 128;
v___x_356_ = lean_uint8_dec_lt(v___x_350_, v___x_355_);
if (v___x_356_ == 0)
{
v___y_352_ = v___x_356_;
goto v___jp_351_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_357_ = lean_box(v___x_350_);
lean_inc_ref(v_r_339_);
v___x_358_ = lean_apply_1(v_r_339_, v___x_357_);
v___x_359_ = lean_unbox(v___x_358_);
v___y_352_ = v___x_359_;
goto v___jp_351_;
}
v___jp_351_:
{
if (v___y_352_ == 0)
{
lean_object* v___x_353_; 
v___x_353_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_350_, v_b_343_);
v___y_345_ = v___x_353_;
goto v___jp_344_;
}
else
{
lean_object* v___x_354_; 
v___x_354_ = lean_byte_array_push(v_b_343_, v___x_350_);
v___y_345_ = v___x_354_;
goto v___jp_344_;
}
}
}
else
{
lean_dec_ref(v_r_339_);
return v_b_343_;
}
v___jp_344_:
{
size_t v___x_346_; size_t v___x_347_; 
v___x_346_ = ((size_t)1ULL);
v___x_347_ = lean_usize_add(v_i_341_, v___x_346_);
v_i_341_ = v___x_347_;
v_b_343_ = v___y_345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0___boxed(lean_object* v_r_360_, lean_object* v_as_361_, lean_object* v_i_362_, lean_object* v_stop_363_, lean_object* v_b_364_){
_start:
{
size_t v_i_boxed_365_; size_t v_stop_boxed_366_; lean_object* v_res_367_; 
v_i_boxed_365_ = lean_unbox_usize(v_i_362_);
lean_dec(v_i_362_);
v_stop_boxed_366_ = lean_unbox_usize(v_stop_363_);
lean_dec(v_stop_363_);
v_res_367_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_360_, v_as_361_, v_i_boxed_365_, v_stop_boxed_366_, v_b_364_);
lean_dec_ref(v_as_361_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode(lean_object* v_r_368_, lean_object* v_s_369_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_370_ = l_ByteArray_empty;
v___x_371_ = lean_string_to_utf8(v_s_369_);
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = lean_byte_array_size(v___x_371_);
v___x_374_ = lean_nat_dec_lt(v___x_372_, v___x_373_);
if (v___x_374_ == 0)
{
lean_dec_ref(v___x_371_);
lean_dec_ref(v_r_368_);
return v___x_370_;
}
else
{
uint8_t v___x_375_; 
v___x_375_ = lean_nat_dec_le(v___x_373_, v___x_373_);
if (v___x_375_ == 0)
{
if (v___x_374_ == 0)
{
lean_dec_ref(v___x_371_);
lean_dec_ref(v_r_368_);
return v___x_370_;
}
else
{
size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; 
v___x_376_ = ((size_t)0ULL);
v___x_377_ = lean_usize_of_nat(v___x_373_);
v___x_378_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_368_, v___x_371_, v___x_376_, v___x_377_, v___x_370_);
lean_dec_ref(v___x_371_);
return v___x_378_;
}
}
else
{
size_t v___x_379_; size_t v___x_380_; lean_object* v___x_381_; 
v___x_379_ = ((size_t)0ULL);
v___x_380_ = lean_usize_of_nat(v___x_373_);
v___x_381_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_368_, v___x_371_, v___x_379_, v___x_380_, v___x_370_);
lean_dec_ref(v___x_371_);
return v___x_381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode___boxed(lean_object* v_r_382_, lean_object* v_s_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_Http_URI_EncodedString_encode(v_r_382_, v_s_383_);
lean_dec_ref(v_s_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x3f(lean_object* v_r_385_, lean_object* v_ba_386_){
_start:
{
uint8_t v___x_387_; 
lean_inc_ref(v_ba_386_);
v___x_387_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_385_, v_ba_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
lean_dec_ref(v_ba_386_);
v___x_388_ = lean_box(0);
return v___x_388_;
}
else
{
uint8_t v___x_389_; 
v___x_389_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_386_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
lean_dec_ref(v_ba_386_);
v___x_390_ = lean_box(0);
return v___x_390_;
}
else
{
lean_object* v___x_391_; 
v___x_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_391_, 0, v_ba_386_);
return v___x_391_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_392_){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = l_ByteArray_empty;
v___x_394_ = lean_panic_fn_borrowed(v___x_393_, v_msg_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(lean_object* v_r_395_, lean_object* v_msg_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v_msg_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_398_, lean_object* v_msg_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(v_r_398_, v_msg_399_);
lean_dec_ref(v_r_398_);
return v_res_400_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_404_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2));
v___x_405_ = lean_unsigned_to_nat(12u);
v___x_406_ = lean_unsigned_to_nat(320u);
v___x_407_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1));
v___x_408_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_409_ = l_mkPanicMessageWithDecl(v___x_408_, v___x_407_, v___x_406_, v___x_405_, v___x_404_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x21(lean_object* v_r_410_, lean_object* v_ba_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_410_, v_ba_411_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_obj_once(&l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3, &l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3_once, _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3);
v___x_414_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v___x_413_);
return v___x_414_;
}
else
{
lean_object* v_val_415_; 
v_val_415_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_val_415_);
lean_dec_ref_known(v___x_412_, 1);
return v_val_415_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f(lean_object* v_r_416_, lean_object* v_s_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_string_to_utf8(v_s_417_);
v___x_419_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_416_, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f___boxed(lean_object* v_r_420_, lean_object* v_s_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Std_Http_URI_EncodedString_ofString_x3f(v_r_420_, v_s_421_);
lean_dec_ref(v_s_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21(lean_object* v_r_423_, lean_object* v_s_424_){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_string_to_utf8(v_s_424_);
v___x_426_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v_r_423_, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21___boxed(lean_object* v_r_427_, lean_object* v_s_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_Http_URI_EncodedString_ofString_x21(v_r_427_, v_s_428_);
lean_dec_ref(v_s_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg(lean_object* v_ba_430_){
_start:
{
lean_inc_ref(v_ba_430_);
return v_ba_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg___boxed(lean_object* v_ba_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_Http_URI_EncodedString_new___redArg(v_ba_431_);
lean_dec_ref(v_ba_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new(lean_object* v_r_433_, lean_object* v_ba_434_, lean_object* v_valid_435_, lean_object* v___validEncoding_436_){
_start:
{
lean_inc_ref(v_ba_434_);
return v_ba_434_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___boxed(lean_object* v_r_437_, lean_object* v_ba_438_, lean_object* v_valid_439_, lean_object* v___validEncoding_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_Http_URI_EncodedString_new(v_r_437_, v_ba_438_, v_valid_439_, v___validEncoding_440_);
lean_dec_ref(v_ba_438_);
lean_dec_ref(v_r_437_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___lam__0(lean_object* v_es_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = lean_string_from_utf8_unchecked(v_es_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString(lean_object* v_r_445_){
_start:
{
lean_object* v___f_446_; 
v___f_446_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instToString___closed__0));
return v___f_446_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___boxed(lean_object* v_r_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_Http_URI_EncodedString_instToString(v_r_447_);
lean_dec_ref(v_r_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(lean_object* v_len_449_, lean_object* v_rawBytes_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_fst_452_; lean_object* v_snd_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_518_; 
v_fst_452_ = lean_ctor_get(v_a_451_, 0);
v_snd_453_ = lean_ctor_get(v_a_451_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_a_451_);
if (v_isSharedCheck_518_ == 0)
{
v___x_455_ = v_a_451_;
v_isShared_456_ = v_isSharedCheck_518_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_snd_453_);
lean_inc(v_fst_452_);
lean_dec(v_a_451_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_518_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
uint8_t v___x_457_; 
v___x_457_ = lean_nat_dec_lt(v_snd_453_, v_len_449_);
if (v___x_457_ == 0)
{
lean_object* v___x_459_; 
if (v_isShared_456_ == 0)
{
v___x_459_ = v___x_455_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_fst_452_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_snd_453_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
else
{
uint8_t v_percent_461_; uint8_t v___x_462_; uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___y_467_; 
v_percent_461_ = 37;
v___x_462_ = lean_byte_array_fget(v_rawBytes_450_, v_snd_453_);
v___x_463_ = lean_uint8_dec_eq(v___x_462_, v_percent_461_);
v___x_464_ = lean_unsigned_to_nat(1u);
v___x_465_ = lean_nat_add(v_snd_453_, v___x_464_);
if (v___x_463_ == 0)
{
v___y_467_ = v___x_463_;
goto v___jp_466_;
}
else
{
uint8_t v___x_517_; 
v___x_517_ = lean_nat_dec_lt(v___x_465_, v_len_449_);
v___y_467_ = v___x_517_;
goto v___jp_466_;
}
v___jp_466_:
{
if (v___y_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_470_; 
lean_dec(v_snd_453_);
v___x_468_ = lean_byte_array_push(v_fst_452_, v___x_462_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_465_);
lean_ctor_set(v___x_455_, 0, v___x_468_);
v___x_470_ = v___x_455_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_465_);
v___x_470_ = v_reuseFailAlloc_472_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
v_a_451_ = v___x_470_;
goto _start;
}
}
else
{
uint8_t v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_byte_array_fget(v_rawBytes_450_, v___x_465_);
lean_dec(v___x_465_);
v___x_474_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_473_);
if (lean_obj_tag(v___x_474_) == 1)
{
lean_object* v_val_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v_val_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_val_475_);
lean_dec_ref_known(v___x_474_, 1);
v___x_476_ = lean_unsigned_to_nat(2u);
v___x_477_ = lean_nat_add(v_snd_453_, v___x_476_);
v___x_478_ = lean_nat_dec_lt(v___x_477_, v_len_449_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
lean_dec(v_val_475_);
lean_dec(v_snd_453_);
v___x_479_ = lean_byte_array_push(v_fst_452_, v___x_462_);
v___x_480_ = lean_byte_array_push(v___x_479_, v___x_473_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_477_);
lean_ctor_set(v___x_455_, 0, v___x_480_);
v___x_482_ = v___x_455_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_477_);
v___x_482_ = v_reuseFailAlloc_484_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
v_a_451_ = v___x_482_;
goto _start;
}
}
else
{
uint8_t v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_byte_array_fget(v_rawBytes_450_, v___x_477_);
lean_dec(v___x_477_);
v___x_486_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_485_);
if (lean_obj_tag(v___x_486_) == 1)
{
lean_object* v_val_487_; uint8_t v___x_488_; uint8_t v___x_489_; uint8_t v___x_490_; uint8_t v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
v_val_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_val_487_);
lean_dec_ref_known(v___x_486_, 1);
v___x_488_ = 4;
v___x_489_ = lean_unbox(v_val_475_);
lean_dec(v_val_475_);
v___x_490_ = lean_uint8_shift_left(v___x_489_, v___x_488_);
v___x_491_ = lean_unbox(v_val_487_);
lean_dec(v_val_487_);
v___x_492_ = lean_uint8_add(v___x_490_, v___x_491_);
v___x_493_ = lean_byte_array_push(v_fst_452_, v___x_492_);
v___x_494_ = lean_unsigned_to_nat(3u);
v___x_495_ = lean_nat_add(v_snd_453_, v___x_494_);
lean_dec(v_snd_453_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_495_);
lean_ctor_set(v___x_455_, 0, v___x_493_);
v___x_497_ = v___x_455_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_493_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_495_);
v___x_497_ = v_reuseFailAlloc_499_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
v_a_451_ = v___x_497_;
goto _start;
}
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
lean_dec(v___x_486_);
lean_dec(v_val_475_);
v___x_500_ = lean_byte_array_push(v_fst_452_, v___x_462_);
v___x_501_ = lean_byte_array_push(v___x_500_, v___x_473_);
v___x_502_ = lean_byte_array_push(v___x_501_, v___x_485_);
v___x_503_ = lean_unsigned_to_nat(3u);
v___x_504_ = lean_nat_add(v_snd_453_, v___x_503_);
lean_dec(v_snd_453_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_504_);
lean_ctor_set(v___x_455_, 0, v___x_502_);
v___x_506_ = v___x_455_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v___x_504_);
v___x_506_ = v_reuseFailAlloc_508_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
v_a_451_ = v___x_506_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
lean_dec(v___x_474_);
v___x_509_ = lean_byte_array_push(v_fst_452_, v___x_462_);
v___x_510_ = lean_byte_array_push(v___x_509_, v___x_473_);
v___x_511_ = lean_unsigned_to_nat(2u);
v___x_512_ = lean_nat_add(v_snd_453_, v___x_511_);
lean_dec(v_snd_453_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_512_);
lean_ctor_set(v___x_455_, 0, v___x_510_);
v___x_514_ = v___x_455_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v___x_512_);
v___x_514_ = v_reuseFailAlloc_516_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
v_a_451_ = v___x_514_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg___boxed(lean_object* v_len_519_, lean_object* v_rawBytes_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_519_, v_rawBytes_520_, v_a_521_);
lean_dec_ref(v_rawBytes_520_);
lean_dec(v_len_519_);
return v_res_522_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0(void){
_start:
{
lean_object* v_i_523_; lean_object* v_decoded_524_; lean_object* v___x_525_; 
v_i_523_ = lean_unsigned_to_nat(0u);
v_decoded_524_ = l_ByteArray_empty;
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v_decoded_524_);
lean_ctor_set(v___x_525_, 1, v_i_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg(lean_object* v_es_526_){
_start:
{
lean_object* v_len_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v_fst_530_; uint8_t v___x_531_; 
v_len_527_ = lean_byte_array_size(v_es_526_);
v___x_528_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_529_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_527_, v_es_526_, v___x_528_);
v_fst_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_fst_530_);
lean_dec_ref(v___x_529_);
v___x_531_ = lean_string_validate_utf8(v_fst_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; 
lean_dec(v_fst_530_);
v___x_532_ = lean_box(0);
return v___x_532_;
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_string_from_utf8_unchecked(v_fst_530_);
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg___boxed(lean_object* v_es_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_535_);
lean_dec_ref(v_es_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode(lean_object* v_r_537_, lean_object* v_es_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___boxed(lean_object* v_r_540_, lean_object* v_es_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_Http_URI_EncodedString_decode(v_r_540_, v_es_541_);
lean_dec_ref(v_es_541_);
lean_dec_ref(v_r_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(lean_object* v_len_543_, lean_object* v_rawBytes_544_, lean_object* v_inst_545_, lean_object* v_a_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_543_, v_rawBytes_544_, v_a_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___boxed(lean_object* v_len_548_, lean_object* v_rawBytes_549_, lean_object* v_inst_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(v_len_548_, v_rawBytes_549_, v_inst_550_, v_a_551_);
lean_dec_ref(v_rawBytes_549_);
lean_dec(v_len_548_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___lam__0(lean_object* v_es_553_, lean_object* v_n_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = lean_string_from_utf8_unchecked(v_es_553_);
v___x_556_ = l_String_quote(v___x_555_);
v___x_557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed(lean_object* v_es_558_, lean_object* v_n_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_Http_URI_EncodedString_instRepr___lam__0(v_es_558_, v_n_559_);
lean_dec(v_n_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr(lean_object* v_r_562_){
_start:
{
lean_object* v___f_563_; 
v___f_563_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___closed__0));
return v___f_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___boxed(lean_object* v_r_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Std_Http_URI_EncodedString_instRepr(v_r_564_);
lean_dec_ref(v_r_564_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq(lean_object* v_r_567_){
_start:
{
lean_object* v___f_568_; 
v___f_568_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___closed__0));
return v___f_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___boxed(lean_object* v_r_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_Http_URI_EncodedString_instBEq(v_r_569_);
lean_dec_ref(v_r_569_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable(lean_object* v_r_572_){
_start:
{
lean_object* v___f_573_; 
v___f_573_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___closed__0));
return v___f_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___boxed(lean_object* v_r_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_Http_URI_EncodedString_instHashable(v_r_574_);
lean_dec_ref(v_r_574_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty(lean_object* v_r_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_ByteArray_empty;
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___boxed(lean_object* v_r_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_Http_URI_EncodedQueryString_empty(v_r_578_);
lean_dec_ref(v_r_578_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited(lean_object* v_r_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_ByteArray_empty;
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___boxed(lean_object* v_r_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_Http_URI_EncodedQueryString_instInhabited(v_r_582_);
lean_dec_ref(v_r_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(lean_object* v_s_584_, uint8_t v_c_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = lean_byte_array_push(v_s_584_, v_c_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg___boxed(lean_object* v_s_587_, lean_object* v_c_588_){
_start:
{
uint8_t v_c_boxed_589_; lean_object* v_res_590_; 
v_c_boxed_589_ = lean_unbox(v_c_588_);
v_res_590_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(v_s_587_, v_c_boxed_589_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(lean_object* v_r_591_, lean_object* v_s_592_, uint8_t v_c_593_, lean_object* v_h_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = lean_byte_array_push(v_s_592_, v_c_593_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___boxed(lean_object* v_r_596_, lean_object* v_s_597_, lean_object* v_c_598_, lean_object* v_h_599_){
_start:
{
uint8_t v_c_boxed_600_; lean_object* v_res_601_; 
v_c_boxed_600_ = lean_unbox(v_c_598_);
v_res_601_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(v_r_596_, v_s_597_, v_c_boxed_600_, v_h_599_);
lean_dec_ref(v_r_596_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(lean_object* v_ba_602_, lean_object* v_r_603_){
_start:
{
uint8_t v___x_604_; 
lean_inc_ref(v_ba_602_);
v___x_604_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_603_, v_ba_602_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
lean_dec_ref(v_ba_602_);
v___x_605_ = lean_box(0);
return v___x_605_;
}
else
{
uint8_t v___x_606_; 
v___x_606_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_602_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; 
lean_dec_ref(v_ba_602_);
v___x_607_ = lean_box(0);
return v___x_607_;
}
else
{
lean_object* v___x_608_; 
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v_ba_602_);
return v___x_608_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_609_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = l_ByteArray_empty;
v___x_611_ = lean_panic_fn_borrowed(v___x_610_, v_msg_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(lean_object* v_r_612_, lean_object* v_msg_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v_msg_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_615_, lean_object* v_msg_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(v_r_615_, v_msg_616_);
lean_dec_ref(v_r_615_);
return v_res_617_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_620_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1));
v___x_621_ = lean_unsigned_to_nat(12u);
v___x_622_ = lean_unsigned_to_nat(438u);
v___x_623_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0));
v___x_624_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_625_ = l_mkPanicMessageWithDecl(v___x_624_, v___x_623_, v___x_622_, v___x_621_, v___x_620_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(lean_object* v_ba_626_, lean_object* v_r_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_626_, v_r_627_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_obj_once(&l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2, &l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2_once, _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2);
v___x_630_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v___x_629_);
return v___x_630_;
}
else
{
lean_object* v_val_631_; 
v_val_631_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v___x_628_, 1);
return v_val_631_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f(lean_object* v_s_632_, lean_object* v_r_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_string_to_utf8(v_s_632_);
v___x_635_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v___x_634_, v_r_633_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f___boxed(lean_object* v_s_636_, lean_object* v_r_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_636_, v_r_637_);
lean_dec_ref(v_s_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21(lean_object* v_s_639_, lean_object* v_r_640_){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_string_to_utf8(v_s_639_);
v___x_642_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v___x_641_, v_r_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21___boxed(lean_object* v_s_643_, lean_object* v_r_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_Http_URI_EncodedQueryString_ofString_x21(v_s_643_, v_r_644_);
lean_dec_ref(v_s_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg(lean_object* v_ba_646_){
_start:
{
lean_inc_ref(v_ba_646_);
return v_ba_646_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg___boxed(lean_object* v_ba_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Std_Http_URI_EncodedQueryString_new___redArg(v_ba_647_);
lean_dec_ref(v_ba_647_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new(lean_object* v_r_649_, lean_object* v_ba_650_, lean_object* v_valid_651_, lean_object* v___validEncoding_652_){
_start:
{
lean_inc_ref(v_ba_650_);
return v_ba_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___boxed(lean_object* v_r_653_, lean_object* v_ba_654_, lean_object* v_valid_655_, lean_object* v___validEncoding_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Std_Http_URI_EncodedQueryString_new(v_r_653_, v_ba_654_, v_valid_655_, v___validEncoding_656_);
lean_dec_ref(v_ba_654_);
lean_dec_ref(v_r_653_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(uint8_t v_b_658_, lean_object* v_s_659_){
_start:
{
uint8_t v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; uint8_t v___x_663_; uint8_t v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; uint8_t v___x_667_; uint8_t v___x_668_; lean_object* v_ba_669_; 
v___x_660_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__0, &l_Std_Http_URI_isEncodedChar___closed__0_once, _init_l_Std_Http_URI_isEncodedChar___closed__0);
v___x_661_ = lean_byte_array_push(v_s_659_, v___x_660_);
v___x_662_ = 4;
v___x_663_ = lean_uint8_shift_right(v_b_658_, v___x_662_);
v___x_664_ = l_Std_Http_URI_hexDigit(v___x_663_);
v___x_665_ = lean_byte_array_push(v___x_661_, v___x_664_);
v___x_666_ = 15;
v___x_667_ = lean_uint8_land(v_b_658_, v___x_666_);
v___x_668_ = l_Std_Http_URI_hexDigit(v___x_667_);
v_ba_669_ = lean_byte_array_push(v___x_665_, v___x_668_);
return v_ba_669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg___boxed(lean_object* v_b_670_, lean_object* v_s_671_){
_start:
{
uint8_t v_b_boxed_672_; lean_object* v_res_673_; 
v_b_boxed_672_ = lean_unbox(v_b_670_);
v_res_673_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_boxed_672_, v_s_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(lean_object* v_r_674_, uint8_t v_b_675_, lean_object* v_s_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_675_, v_s_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___boxed(lean_object* v_r_678_, lean_object* v_b_679_, lean_object* v_s_680_){
_start:
{
uint8_t v_b_boxed_681_; lean_object* v_res_682_; 
v_b_boxed_681_ = lean_unbox(v_b_679_);
v_res_682_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(v_r_678_, v_b_boxed_681_, v_s_680_);
lean_dec_ref(v_r_678_);
return v_res_682_;
}
}
static uint8_t _init_l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0(void){
_start:
{
uint32_t v___x_683_; uint8_t v___x_684_; 
v___x_683_ = 32;
v___x_684_ = lean_uint32_to_uint8(v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(lean_object* v_r_685_, lean_object* v_as_686_, size_t v_i_687_, size_t v_stop_688_, lean_object* v_b_689_){
_start:
{
lean_object* v___y_691_; uint8_t v___x_695_; 
v___x_695_ = lean_usize_dec_eq(v_i_687_, v_stop_688_);
if (v___x_695_ == 0)
{
uint8_t v___x_696_; uint8_t v___y_698_; uint8_t v___x_705_; uint8_t v___x_706_; 
v___x_696_ = lean_byte_array_uget(v_as_686_, v_i_687_);
v___x_705_ = 128;
v___x_706_ = lean_uint8_dec_lt(v___x_696_, v___x_705_);
if (v___x_706_ == 0)
{
v___y_698_ = v___x_706_;
goto v___jp_697_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_707_ = lean_box(v___x_696_);
lean_inc_ref(v_r_685_);
v___x_708_ = lean_apply_1(v_r_685_, v___x_707_);
v___x_709_ = lean_unbox(v___x_708_);
v___y_698_ = v___x_709_;
goto v___jp_697_;
}
v___jp_697_:
{
if (v___y_698_ == 0)
{
uint8_t v___x_699_; uint8_t v___x_700_; 
v___x_699_ = lean_uint8_once(&l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0, &l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0_once, _init_l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0);
v___x_700_ = lean_uint8_dec_eq(v___x_696_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
v___x_701_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v___x_696_, v_b_689_);
v___y_691_ = v___x_701_;
goto v___jp_690_;
}
else
{
uint8_t v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_703_ = lean_byte_array_push(v_b_689_, v___x_702_);
v___y_691_ = v___x_703_;
goto v___jp_690_;
}
}
else
{
lean_object* v___x_704_; 
v___x_704_ = lean_byte_array_push(v_b_689_, v___x_696_);
v___y_691_ = v___x_704_;
goto v___jp_690_;
}
}
}
else
{
lean_dec_ref(v_r_685_);
return v_b_689_;
}
v___jp_690_:
{
size_t v___x_692_; size_t v___x_693_; 
v___x_692_ = ((size_t)1ULL);
v___x_693_ = lean_usize_add(v_i_687_, v___x_692_);
v_i_687_ = v___x_693_;
v_b_689_ = v___y_691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___boxed(lean_object* v_r_710_, lean_object* v_as_711_, lean_object* v_i_712_, lean_object* v_stop_713_, lean_object* v_b_714_){
_start:
{
size_t v_i_boxed_715_; size_t v_stop_boxed_716_; lean_object* v_res_717_; 
v_i_boxed_715_ = lean_unbox_usize(v_i_712_);
lean_dec(v_i_712_);
v_stop_boxed_716_ = lean_unbox_usize(v_stop_713_);
lean_dec(v_stop_713_);
v_res_717_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_710_, v_as_711_, v_i_boxed_715_, v_stop_boxed_716_, v_b_714_);
lean_dec_ref(v_as_711_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode(lean_object* v_s_718_, lean_object* v_r_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_720_ = l_ByteArray_empty;
v___x_721_ = lean_string_to_utf8(v_s_718_);
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_byte_array_size(v___x_721_);
v___x_724_ = lean_nat_dec_lt(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_dec_ref(v___x_721_);
lean_dec_ref(v_r_719_);
return v___x_720_;
}
else
{
uint8_t v___x_725_; 
v___x_725_ = lean_nat_dec_le(v___x_723_, v___x_723_);
if (v___x_725_ == 0)
{
if (v___x_724_ == 0)
{
lean_dec_ref(v___x_721_);
lean_dec_ref(v_r_719_);
return v___x_720_;
}
else
{
size_t v___x_726_; size_t v___x_727_; lean_object* v___x_728_; 
v___x_726_ = ((size_t)0ULL);
v___x_727_ = lean_usize_of_nat(v___x_723_);
v___x_728_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_719_, v___x_721_, v___x_726_, v___x_727_, v___x_720_);
lean_dec_ref(v___x_721_);
return v___x_728_;
}
}
else
{
size_t v___x_729_; size_t v___x_730_; lean_object* v___x_731_; 
v___x_729_ = ((size_t)0ULL);
v___x_730_ = lean_usize_of_nat(v___x_723_);
v___x_731_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_719_, v___x_721_, v___x_729_, v___x_730_, v___x_720_);
lean_dec_ref(v___x_721_);
return v___x_731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode___boxed(lean_object* v_s_732_, lean_object* v_r_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_732_, v_r_733_);
lean_dec_ref(v_s_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___redArg(lean_object* v_es_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = lean_string_from_utf8_unchecked(v_es_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString(lean_object* v_r_737_, lean_object* v_es_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = lean_string_from_utf8_unchecked(v_es_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___boxed(lean_object* v_r_740_, lean_object* v_es_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Std_Http_URI_EncodedQueryString_toString(v_r_740_, v_es_741_);
lean_dec_ref(v_r_740_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(lean_object* v_len_743_, lean_object* v_rawBytes_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_fst_746_; lean_object* v_snd_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_822_; 
v_fst_746_ = lean_ctor_get(v_a_745_, 0);
v_snd_747_ = lean_ctor_get(v_a_745_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v_a_745_);
if (v_isSharedCheck_822_ == 0)
{
v___x_749_ = v_a_745_;
v_isShared_750_ = v_isSharedCheck_822_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_snd_747_);
lean_inc(v_fst_746_);
lean_dec(v_a_745_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_822_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
uint8_t v___x_751_; 
v___x_751_ = lean_nat_dec_lt(v_snd_747_, v_len_743_);
if (v___x_751_ == 0)
{
lean_object* v___x_753_; 
if (v_isShared_750_ == 0)
{
v___x_753_ = v___x_749_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_fst_746_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_snd_747_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
else
{
uint8_t v_plus_755_; uint8_t v___x_756_; uint8_t v___x_757_; 
v_plus_755_ = 43;
v___x_756_ = lean_byte_array_fget(v_rawBytes_744_, v_snd_747_);
v___x_757_ = lean_uint8_dec_eq(v___x_756_, v_plus_755_);
if (v___x_757_ == 0)
{
uint8_t v_percent_758_; uint8_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___y_763_; 
v_percent_758_ = 37;
v___x_759_ = lean_uint8_dec_eq(v___x_756_, v_percent_758_);
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_nat_add(v_snd_747_, v___x_760_);
if (v___x_759_ == 0)
{
v___y_763_ = v___x_759_;
goto v___jp_762_;
}
else
{
uint8_t v___x_813_; 
v___x_813_ = lean_nat_dec_lt(v___x_761_, v_len_743_);
v___y_763_ = v___x_813_;
goto v___jp_762_;
}
v___jp_762_:
{
if (v___y_763_ == 0)
{
lean_object* v___x_764_; lean_object* v___x_766_; 
lean_dec(v_snd_747_);
v___x_764_ = lean_byte_array_push(v_fst_746_, v___x_756_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_761_);
lean_ctor_set(v___x_749_, 0, v___x_764_);
v___x_766_ = v___x_749_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v___x_761_);
v___x_766_ = v_reuseFailAlloc_768_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
v_a_745_ = v___x_766_;
goto _start;
}
}
else
{
uint8_t v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_byte_array_fget(v_rawBytes_744_, v___x_761_);
lean_dec(v___x_761_);
v___x_770_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_769_);
if (lean_obj_tag(v___x_770_) == 1)
{
lean_object* v_val_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v_val_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_val_771_);
lean_dec_ref_known(v___x_770_, 1);
v___x_772_ = lean_unsigned_to_nat(2u);
v___x_773_ = lean_nat_add(v_snd_747_, v___x_772_);
v___x_774_ = lean_nat_dec_lt(v___x_773_, v_len_743_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
lean_dec(v_val_771_);
lean_dec(v_snd_747_);
v___x_775_ = lean_byte_array_push(v_fst_746_, v___x_756_);
v___x_776_ = lean_byte_array_push(v___x_775_, v___x_769_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_773_);
lean_ctor_set(v___x_749_, 0, v___x_776_);
v___x_778_ = v___x_749_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_773_);
v___x_778_ = v_reuseFailAlloc_780_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
v_a_745_ = v___x_778_;
goto _start;
}
}
else
{
uint8_t v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_byte_array_fget(v_rawBytes_744_, v___x_773_);
lean_dec(v___x_773_);
v___x_782_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_781_);
if (lean_obj_tag(v___x_782_) == 1)
{
lean_object* v_val_783_; uint8_t v___x_784_; uint8_t v___x_785_; uint8_t v___x_786_; uint8_t v___x_787_; uint8_t v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
v_val_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_val_783_);
lean_dec_ref_known(v___x_782_, 1);
v___x_784_ = 4;
v___x_785_ = lean_unbox(v_val_771_);
lean_dec(v_val_771_);
v___x_786_ = lean_uint8_shift_left(v___x_785_, v___x_784_);
v___x_787_ = lean_unbox(v_val_783_);
lean_dec(v_val_783_);
v___x_788_ = lean_uint8_add(v___x_786_, v___x_787_);
v___x_789_ = lean_byte_array_push(v_fst_746_, v___x_788_);
v___x_790_ = lean_unsigned_to_nat(3u);
v___x_791_ = lean_nat_add(v_snd_747_, v___x_790_);
lean_dec(v_snd_747_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_791_);
lean_ctor_set(v___x_749_, 0, v___x_789_);
v___x_793_ = v___x_749_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_791_);
v___x_793_ = v_reuseFailAlloc_795_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
v_a_745_ = v___x_793_;
goto _start;
}
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
lean_dec(v___x_782_);
lean_dec(v_val_771_);
v___x_796_ = lean_byte_array_push(v_fst_746_, v___x_756_);
v___x_797_ = lean_byte_array_push(v___x_796_, v___x_769_);
v___x_798_ = lean_byte_array_push(v___x_797_, v___x_781_);
v___x_799_ = lean_unsigned_to_nat(3u);
v___x_800_ = lean_nat_add(v_snd_747_, v___x_799_);
lean_dec(v_snd_747_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_800_);
lean_ctor_set(v___x_749_, 0, v___x_798_);
v___x_802_ = v___x_749_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v___x_800_);
v___x_802_ = v_reuseFailAlloc_804_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
v_a_745_ = v___x_802_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
lean_dec(v___x_770_);
v___x_805_ = lean_byte_array_push(v_fst_746_, v___x_756_);
v___x_806_ = lean_byte_array_push(v___x_805_, v___x_769_);
v___x_807_ = lean_unsigned_to_nat(2u);
v___x_808_ = lean_nat_add(v_snd_747_, v___x_807_);
lean_dec(v_snd_747_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_808_);
lean_ctor_set(v___x_749_, 0, v___x_806_);
v___x_810_ = v___x_749_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_808_);
v___x_810_ = v_reuseFailAlloc_812_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
v_a_745_ = v___x_810_;
goto _start;
}
}
}
}
}
else
{
uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_814_ = 32;
v___x_815_ = lean_byte_array_push(v_fst_746_, v___x_814_);
v___x_816_ = lean_unsigned_to_nat(1u);
v___x_817_ = lean_nat_add(v_snd_747_, v___x_816_);
lean_dec(v_snd_747_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_817_);
lean_ctor_set(v___x_749_, 0, v___x_815_);
v___x_819_ = v___x_749_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_817_);
v___x_819_ = v_reuseFailAlloc_821_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
v_a_745_ = v___x_819_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg___boxed(lean_object* v_len_823_, lean_object* v_rawBytes_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_823_, v_rawBytes_824_, v_a_825_);
lean_dec_ref(v_rawBytes_824_);
lean_dec(v_len_823_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg(lean_object* v_es_827_){
_start:
{
lean_object* v_len_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v_fst_831_; uint8_t v___x_832_; 
v_len_828_ = lean_byte_array_size(v_es_827_);
v___x_829_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_830_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_828_, v_es_827_, v___x_829_);
v_fst_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_fst_831_);
lean_dec_ref(v___x_830_);
v___x_832_ = lean_string_validate_utf8(v_fst_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; 
lean_dec(v_fst_831_);
v___x_833_ = lean_box(0);
return v___x_833_;
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_string_from_utf8_unchecked(v_fst_831_);
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg___boxed(lean_object* v_es_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_836_);
lean_dec_ref(v_es_836_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode(lean_object* v_r_838_, lean_object* v_es_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___boxed(lean_object* v_r_841_, lean_object* v_es_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Std_Http_URI_EncodedQueryString_decode(v_r_841_, v_es_842_);
lean_dec_ref(v_es_842_);
lean_dec_ref(v_r_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(lean_object* v_len_844_, lean_object* v_rawBytes_845_, lean_object* v_inst_846_, lean_object* v_a_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_844_, v_rawBytes_845_, v_a_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___boxed(lean_object* v_len_849_, lean_object* v_rawBytes_850_, lean_object* v_inst_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(v_len_849_, v_rawBytes_850_, v_inst_851_, v_a_852_);
lean_dec_ref(v_rawBytes_850_);
lean_dec(v_len_849_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringEncodedQueryString(lean_object* v_r_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = lean_alloc_closure((void*)(l_Std_Http_URI_EncodedQueryString_toString___boxed), 2, 1);
lean_closure_set(v___x_855_, 0, v_r_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString(lean_object* v_r_856_){
_start:
{
lean_object* v___f_857_; 
v___f_857_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___closed__0));
return v___f_857_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___boxed(lean_object* v_r_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Std_Http_URI_instReprEncodedQueryString(v_r_858_);
lean_dec_ref(v_r_858_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString(lean_object* v_r_860_){
_start:
{
lean_object* v___f_861_; 
v___f_861_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___closed__0));
return v___f_861_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___boxed(lean_object* v_r_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Std_Http_URI_instBEqEncodedQueryString(v_r_862_);
lean_dec_ref(v_r_862_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString(lean_object* v_r_864_){
_start:
{
lean_object* v___f_865_; 
v___f_865_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___closed__0));
return v___f_865_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___boxed(lean_object* v_r_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Std_Http_URI_instHashableEncodedQueryString(v_r_866_);
lean_dec_ref(v_r_866_);
return v_res_867_;
}
}
static uint64_t _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1(void){
_start:
{
lean_object* v___x_874_; uint64_t v___x_875_; 
v___x_874_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__0));
v___x_875_ = lean_byte_array_hash(v___x_874_);
return v___x_875_;
}
}
static lean_object* _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2));
v___x_883_ = lean_byte_array_size(v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT uint64_t l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0(lean_object* v_x_884_){
_start:
{
if (lean_obj_tag(v_x_884_) == 0)
{
uint64_t v___x_885_; 
v___x_885_ = lean_uint64_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1, &l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1);
return v___x_885_;
}
else
{
lean_object* v_val_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; lean_object* v___x_892_; uint64_t v___x_893_; 
v_val_886_ = lean_ctor_get(v_x_884_, 0);
v___x_887_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2));
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = lean_obj_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3, &l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3);
v___x_890_ = lean_byte_array_size(v_val_886_);
v___x_891_ = 0;
v___x_892_ = lean_byte_array_copy_slice(v_val_886_, v___x_888_, v___x_887_, v___x_889_, v___x_890_, v___x_891_);
v___x_893_ = lean_byte_array_hash(v___x_892_);
lean_dec_ref(v___x_892_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___boxed(lean_object* v_x_894_){
_start:
{
uint64_t v_res_895_; lean_object* v_r_896_; 
v_res_895_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0(v_x_894_);
lean_dec(v_x_894_);
v_r_896_ = lean_box_uint64(v_res_895_);
return v_r_896_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString(lean_object* v_r_898_){
_start:
{
lean_object* v___f_899_; 
v___f_899_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___closed__0));
return v___f_899_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___boxed(lean_object* v_r_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_Http_URI_instHashableOptionEncodedQueryString(v_r_900_);
lean_dec_ref(v_r_900_);
return v_res_901_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0(void){
_start:
{
uint32_t v___x_902_; uint8_t v___x_903_; 
v___x_902_ = 45;
v___x_903_ = lean_uint32_to_uint8(v___x_902_);
return v___x_903_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1(void){
_start:
{
uint32_t v___x_904_; uint8_t v___x_905_; 
v___x_904_ = 46;
v___x_905_ = lean_uint32_to_uint8(v___x_904_);
return v___x_905_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2(void){
_start:
{
uint32_t v___x_906_; uint8_t v___x_907_; 
v___x_906_ = 95;
v___x_907_ = lean_uint32_to_uint8(v___x_906_);
return v___x_907_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3(void){
_start:
{
uint32_t v___x_908_; uint8_t v___x_909_; 
v___x_908_ = 126;
v___x_909_ = lean_uint32_to_uint8(v___x_908_);
return v___x_909_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4(void){
_start:
{
uint32_t v___x_910_; uint8_t v___x_911_; 
v___x_910_ = 33;
v___x_911_ = lean_uint32_to_uint8(v___x_910_);
return v___x_911_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5(void){
_start:
{
uint32_t v___x_912_; uint8_t v___x_913_; 
v___x_912_ = 36;
v___x_913_ = lean_uint32_to_uint8(v___x_912_);
return v___x_913_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6(void){
_start:
{
uint32_t v___x_914_; uint8_t v___x_915_; 
v___x_914_ = 38;
v___x_915_ = lean_uint32_to_uint8(v___x_914_);
return v___x_915_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7(void){
_start:
{
uint32_t v___x_916_; uint8_t v___x_917_; 
v___x_916_ = 39;
v___x_917_ = lean_uint32_to_uint8(v___x_916_);
return v___x_917_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8(void){
_start:
{
uint32_t v___x_918_; uint8_t v___x_919_; 
v___x_918_ = 40;
v___x_919_ = lean_uint32_to_uint8(v___x_918_);
return v___x_919_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9(void){
_start:
{
uint32_t v___x_920_; uint8_t v___x_921_; 
v___x_920_ = 41;
v___x_921_ = lean_uint32_to_uint8(v___x_920_);
return v___x_921_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10(void){
_start:
{
uint32_t v___x_922_; uint8_t v___x_923_; 
v___x_922_ = 42;
v___x_923_ = lean_uint32_to_uint8(v___x_922_);
return v___x_923_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11(void){
_start:
{
uint32_t v___x_924_; uint8_t v___x_925_; 
v___x_924_ = 44;
v___x_925_ = lean_uint32_to_uint8(v___x_924_);
return v___x_925_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12(void){
_start:
{
uint32_t v___x_926_; uint8_t v___x_927_; 
v___x_926_ = 59;
v___x_927_ = lean_uint32_to_uint8(v___x_926_);
return v___x_927_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13(void){
_start:
{
uint32_t v___x_928_; uint8_t v___x_929_; 
v___x_928_ = 61;
v___x_929_ = lean_uint32_to_uint8(v___x_928_);
return v___x_929_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14(void){
_start:
{
uint32_t v___x_930_; uint8_t v___x_931_; 
v___x_930_ = 58;
v___x_931_ = lean_uint32_to_uint8(v___x_930_);
return v___x_931_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15(void){
_start:
{
uint32_t v___x_932_; uint8_t v___x_933_; 
v___x_932_ = 64;
v___x_933_ = lean_uint32_to_uint8(v___x_932_);
return v___x_933_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16(void){
_start:
{
uint32_t v___x_934_; uint8_t v___x_935_; 
v___x_934_ = 90;
v___x_935_ = lean_uint32_to_uint8(v___x_934_);
return v___x_935_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17(void){
_start:
{
uint32_t v___x_936_; uint8_t v___x_937_; 
v___x_936_ = 122;
v___x_937_ = lean_uint32_to_uint8(v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0(uint8_t v___y_938_){
_start:
{
uint8_t v___x_984_; uint8_t v___x_985_; 
v___x_984_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_985_ = lean_uint8_dec_le(v___x_984_, v___y_938_);
if (v___x_985_ == 0)
{
goto v___jp_979_;
}
else
{
uint8_t v___x_986_; uint8_t v___x_987_; 
v___x_986_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_987_ = lean_uint8_dec_le(v___y_938_, v___x_986_);
if (v___x_987_ == 0)
{
goto v___jp_979_;
}
else
{
return v___x_987_;
}
}
v___jp_939_:
{
uint8_t v___x_940_; uint8_t v___x_941_; 
v___x_940_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_941_ = lean_uint8_dec_eq(v___y_938_, v___x_940_);
if (v___x_941_ == 0)
{
uint8_t v___x_942_; uint8_t v___x_943_; 
v___x_942_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_943_ = lean_uint8_dec_eq(v___y_938_, v___x_942_);
if (v___x_943_ == 0)
{
uint8_t v___x_944_; uint8_t v___x_945_; 
v___x_944_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_945_ = lean_uint8_dec_eq(v___y_938_, v___x_944_);
if (v___x_945_ == 0)
{
uint8_t v___x_946_; uint8_t v___x_947_; 
v___x_946_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_947_ = lean_uint8_dec_eq(v___y_938_, v___x_946_);
if (v___x_947_ == 0)
{
uint8_t v___x_948_; uint8_t v___x_949_; 
v___x_948_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_949_ = lean_uint8_dec_eq(v___y_938_, v___x_948_);
if (v___x_949_ == 0)
{
uint8_t v___x_950_; uint8_t v___x_951_; 
v___x_950_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_951_ = lean_uint8_dec_eq(v___y_938_, v___x_950_);
if (v___x_951_ == 0)
{
uint8_t v___x_952_; uint8_t v___x_953_; 
v___x_952_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_953_ = lean_uint8_dec_eq(v___y_938_, v___x_952_);
if (v___x_953_ == 0)
{
uint8_t v___x_954_; uint8_t v___x_955_; 
v___x_954_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_955_ = lean_uint8_dec_eq(v___y_938_, v___x_954_);
if (v___x_955_ == 0)
{
uint8_t v___x_956_; uint8_t v___x_957_; 
v___x_956_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_957_ = lean_uint8_dec_eq(v___y_938_, v___x_956_);
if (v___x_957_ == 0)
{
uint8_t v___x_958_; uint8_t v___x_959_; 
v___x_958_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_959_ = lean_uint8_dec_eq(v___y_938_, v___x_958_);
if (v___x_959_ == 0)
{
uint8_t v___x_960_; uint8_t v___x_961_; 
v___x_960_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_961_ = lean_uint8_dec_eq(v___y_938_, v___x_960_);
if (v___x_961_ == 0)
{
uint8_t v___x_962_; uint8_t v___x_963_; 
v___x_962_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_963_ = lean_uint8_dec_eq(v___y_938_, v___x_962_);
if (v___x_963_ == 0)
{
uint8_t v___x_964_; uint8_t v___x_965_; 
v___x_964_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_965_ = lean_uint8_dec_eq(v___y_938_, v___x_964_);
if (v___x_965_ == 0)
{
uint8_t v___x_966_; uint8_t v___x_967_; 
v___x_966_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_967_ = lean_uint8_dec_eq(v___y_938_, v___x_966_);
if (v___x_967_ == 0)
{
uint8_t v___x_968_; uint8_t v___x_969_; 
v___x_968_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_969_ = lean_uint8_dec_eq(v___y_938_, v___x_968_);
if (v___x_969_ == 0)
{
uint8_t v___x_970_; uint8_t v___x_971_; 
v___x_970_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_971_ = lean_uint8_dec_eq(v___y_938_, v___x_970_);
if (v___x_971_ == 0)
{
uint8_t v___x_972_; uint8_t v___x_973_; 
v___x_972_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_973_ = lean_uint8_dec_eq(v___y_938_, v___x_972_);
return v___x_973_;
}
else
{
return v___x_971_;
}
}
else
{
return v___x_969_;
}
}
else
{
return v___x_967_;
}
}
else
{
return v___x_965_;
}
}
else
{
return v___x_963_;
}
}
else
{
return v___x_961_;
}
}
else
{
return v___x_959_;
}
}
else
{
return v___x_957_;
}
}
else
{
return v___x_955_;
}
}
else
{
return v___x_953_;
}
}
else
{
return v___x_951_;
}
}
else
{
return v___x_949_;
}
}
else
{
return v___x_947_;
}
}
else
{
return v___x_945_;
}
}
else
{
return v___x_943_;
}
}
else
{
return v___x_941_;
}
}
v___jp_974_:
{
uint8_t v___x_975_; uint8_t v___x_976_; 
v___x_975_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_976_ = lean_uint8_dec_le(v___x_975_, v___y_938_);
if (v___x_976_ == 0)
{
goto v___jp_939_;
}
else
{
uint8_t v___x_977_; uint8_t v___x_978_; 
v___x_977_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_978_ = lean_uint8_dec_le(v___y_938_, v___x_977_);
if (v___x_978_ == 0)
{
goto v___jp_939_;
}
else
{
return v___x_978_;
}
}
}
v___jp_979_:
{
uint8_t v___x_980_; uint8_t v___x_981_; 
v___x_980_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_981_ = lean_uint8_dec_le(v___x_980_, v___y_938_);
if (v___x_981_ == 0)
{
goto v___jp_974_;
}
else
{
uint8_t v___x_982_; uint8_t v___x_983_; 
v___x_982_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_983_ = lean_uint8_dec_le(v___y_938_, v___x_982_);
if (v___x_983_ == 0)
{
goto v___jp_974_;
}
else
{
return v___x_983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___lam__0___boxed(lean_object* v___y_988_){
_start:
{
uint8_t v___y_347__boxed_989_; uint8_t v_res_990_; lean_object* v_r_991_; 
v___y_347__boxed_989_ = lean_unbox(v___y_988_);
v_res_990_ = l_Std_Http_URI_EncodedSegment_encode___lam__0(v___y_347__boxed_989_);
v_r_991_ = lean_box(v_res_990_);
return v_r_991_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode(lean_object* v_s_993_){
_start:
{
lean_object* v___f_994_; lean_object* v___x_995_; 
v___f_994_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_995_ = l_Std_Http_URI_EncodedString_encode(v___f_994_, v_s_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___boxed(lean_object* v_s_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Std_Http_URI_EncodedSegment_encode(v_s_996_);
lean_dec_ref(v_s_996_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object* v_ba_998_){
_start:
{
lean_object* v___f_999_; lean_object* v___x_1000_; 
v___f_999_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_1000_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_999_, v_ba_998_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x21(lean_object* v_ba_1001_){
_start:
{
lean_object* v___f_1002_; lean_object* v___x_1003_; 
v___f_1002_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_1003_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1002_, v_ba_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object* v_segment_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Std_Http_URI_EncodedString_decode___redArg(v_segment_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode___boxed(lean_object* v_segment_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_Http_URI_EncodedSegment_decode(v_segment_1006_);
lean_dec_ref(v_segment_1006_);
return v_res_1007_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0(void){
_start:
{
uint32_t v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = 47;
v___x_1009_ = lean_uint32_to_uint8(v___x_1008_);
return v___x_1009_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1(void){
_start:
{
uint32_t v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = 63;
v___x_1011_ = lean_uint32_to_uint8(v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedFragment_encode___lam__0(uint8_t v___y_1012_){
_start:
{
uint8_t v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1063_ = lean_uint8_dec_le(v___x_1062_, v___y_1012_);
if (v___x_1063_ == 0)
{
goto v___jp_1057_;
}
else
{
uint8_t v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1065_ = lean_uint8_dec_le(v___y_1012_, v___x_1064_);
if (v___x_1065_ == 0)
{
goto v___jp_1057_;
}
else
{
return v___x_1065_;
}
}
v___jp_1013_:
{
uint8_t v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_1015_ = lean_uint8_dec_eq(v___y_1012_, v___x_1014_);
if (v___x_1015_ == 0)
{
uint8_t v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_1017_ = lean_uint8_dec_eq(v___y_1012_, v___x_1016_);
if (v___x_1017_ == 0)
{
uint8_t v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1019_ = lean_uint8_dec_eq(v___y_1012_, v___x_1018_);
if (v___x_1019_ == 0)
{
uint8_t v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_1021_ = lean_uint8_dec_eq(v___y_1012_, v___x_1020_);
if (v___x_1021_ == 0)
{
uint8_t v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1023_ = lean_uint8_dec_eq(v___y_1012_, v___x_1022_);
if (v___x_1023_ == 0)
{
uint8_t v___x_1024_; uint8_t v___x_1025_; 
v___x_1024_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1025_ = lean_uint8_dec_eq(v___y_1012_, v___x_1024_);
if (v___x_1025_ == 0)
{
uint8_t v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1027_ = lean_uint8_dec_eq(v___y_1012_, v___x_1026_);
if (v___x_1027_ == 0)
{
uint8_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1029_ = lean_uint8_dec_eq(v___y_1012_, v___x_1028_);
if (v___x_1029_ == 0)
{
uint8_t v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1031_ = lean_uint8_dec_eq(v___y_1012_, v___x_1030_);
if (v___x_1031_ == 0)
{
uint8_t v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1033_ = lean_uint8_dec_eq(v___y_1012_, v___x_1032_);
if (v___x_1033_ == 0)
{
uint8_t v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1035_ = lean_uint8_dec_eq(v___y_1012_, v___x_1034_);
if (v___x_1035_ == 0)
{
uint8_t v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1037_ = lean_uint8_dec_eq(v___y_1012_, v___x_1036_);
if (v___x_1037_ == 0)
{
uint8_t v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1039_ = lean_uint8_dec_eq(v___y_1012_, v___x_1038_);
if (v___x_1039_ == 0)
{
uint8_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1041_ = lean_uint8_dec_eq(v___y_1012_, v___x_1040_);
if (v___x_1041_ == 0)
{
uint8_t v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1043_ = lean_uint8_dec_eq(v___y_1012_, v___x_1042_);
if (v___x_1043_ == 0)
{
uint8_t v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1045_ = lean_uint8_dec_eq(v___y_1012_, v___x_1044_);
if (v___x_1045_ == 0)
{
uint8_t v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1047_ = lean_uint8_dec_eq(v___y_1012_, v___x_1046_);
if (v___x_1047_ == 0)
{
uint8_t v___x_1048_; uint8_t v___x_1049_; 
v___x_1048_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0);
v___x_1049_ = lean_uint8_dec_eq(v___y_1012_, v___x_1048_);
if (v___x_1049_ == 0)
{
uint8_t v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1);
v___x_1051_ = lean_uint8_dec_eq(v___y_1012_, v___x_1050_);
return v___x_1051_;
}
else
{
return v___x_1049_;
}
}
else
{
return v___x_1047_;
}
}
else
{
return v___x_1045_;
}
}
else
{
return v___x_1043_;
}
}
else
{
return v___x_1041_;
}
}
else
{
return v___x_1039_;
}
}
else
{
return v___x_1037_;
}
}
else
{
return v___x_1035_;
}
}
else
{
return v___x_1033_;
}
}
else
{
return v___x_1031_;
}
}
else
{
return v___x_1029_;
}
}
else
{
return v___x_1027_;
}
}
else
{
return v___x_1025_;
}
}
else
{
return v___x_1023_;
}
}
else
{
return v___x_1021_;
}
}
else
{
return v___x_1019_;
}
}
else
{
return v___x_1017_;
}
}
else
{
return v___x_1015_;
}
}
v___jp_1052_:
{
uint8_t v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1054_ = lean_uint8_dec_le(v___x_1053_, v___y_1012_);
if (v___x_1054_ == 0)
{
goto v___jp_1013_;
}
else
{
uint8_t v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1056_ = lean_uint8_dec_le(v___y_1012_, v___x_1055_);
if (v___x_1056_ == 0)
{
goto v___jp_1013_;
}
else
{
return v___x_1056_;
}
}
}
v___jp_1057_:
{
uint8_t v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1059_ = lean_uint8_dec_le(v___x_1058_, v___y_1012_);
if (v___x_1059_ == 0)
{
goto v___jp_1052_;
}
else
{
uint8_t v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1061_ = lean_uint8_dec_le(v___y_1012_, v___x_1060_);
if (v___x_1061_ == 0)
{
goto v___jp_1052_;
}
else
{
return v___x_1061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed(lean_object* v___y_1066_){
_start:
{
uint8_t v___y_343__boxed_1067_; uint8_t v_res_1068_; lean_object* v_r_1069_; 
v___y_343__boxed_1067_ = lean_unbox(v___y_1066_);
v_res_1068_ = l_Std_Http_URI_EncodedFragment_encode___lam__0(v___y_343__boxed_1067_);
v_r_1069_ = lean_box(v_res_1068_);
return v_r_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object* v_s_1071_){
_start:
{
lean_object* v___f_1072_; lean_object* v___x_1073_; 
v___f_1072_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1073_ = l_Std_Http_URI_EncodedString_encode(v___f_1072_, v_s_1071_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___boxed(lean_object* v_s_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Std_Http_URI_EncodedFragment_encode(v_s_1074_);
lean_dec_ref(v_s_1074_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object* v_ba_1076_){
_start:
{
lean_object* v___f_1077_; lean_object* v___x_1078_; 
v___f_1077_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1078_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1077_, v_ba_1076_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x21(lean_object* v_ba_1079_){
_start:
{
lean_object* v___f_1080_; lean_object* v___x_1081_; 
v___f_1080_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1081_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1080_, v_ba_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object* v_fragment_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Std_Http_URI_EncodedString_decode___redArg(v_fragment_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode___boxed(lean_object* v_fragment_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Std_Http_URI_EncodedFragment_decode(v_fragment_1084_);
lean_dec_ref(v_fragment_1084_);
return v_res_1085_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedUserInfo_encode___lam__0(uint8_t v___y_1086_){
_start:
{
uint8_t v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1131_ = lean_uint8_dec_le(v___x_1130_, v___y_1086_);
if (v___x_1131_ == 0)
{
goto v___jp_1125_;
}
else
{
uint8_t v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1133_ = lean_uint8_dec_le(v___y_1086_, v___x_1132_);
if (v___x_1133_ == 0)
{
goto v___jp_1125_;
}
else
{
return v___x_1133_;
}
}
v___jp_1087_:
{
uint8_t v___x_1088_; uint8_t v___x_1089_; 
v___x_1088_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_1089_ = lean_uint8_dec_eq(v___y_1086_, v___x_1088_);
if (v___x_1089_ == 0)
{
uint8_t v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_1091_ = lean_uint8_dec_eq(v___y_1086_, v___x_1090_);
if (v___x_1091_ == 0)
{
uint8_t v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1093_ = lean_uint8_dec_eq(v___y_1086_, v___x_1092_);
if (v___x_1093_ == 0)
{
uint8_t v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_1095_ = lean_uint8_dec_eq(v___y_1086_, v___x_1094_);
if (v___x_1095_ == 0)
{
uint8_t v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1097_ = lean_uint8_dec_eq(v___y_1086_, v___x_1096_);
if (v___x_1097_ == 0)
{
uint8_t v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1099_ = lean_uint8_dec_eq(v___y_1086_, v___x_1098_);
if (v___x_1099_ == 0)
{
uint8_t v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1101_ = lean_uint8_dec_eq(v___y_1086_, v___x_1100_);
if (v___x_1101_ == 0)
{
uint8_t v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1103_ = lean_uint8_dec_eq(v___y_1086_, v___x_1102_);
if (v___x_1103_ == 0)
{
uint8_t v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1105_ = lean_uint8_dec_eq(v___y_1086_, v___x_1104_);
if (v___x_1105_ == 0)
{
uint8_t v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1107_ = lean_uint8_dec_eq(v___y_1086_, v___x_1106_);
if (v___x_1107_ == 0)
{
uint8_t v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1109_ = lean_uint8_dec_eq(v___y_1086_, v___x_1108_);
if (v___x_1109_ == 0)
{
uint8_t v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1111_ = lean_uint8_dec_eq(v___y_1086_, v___x_1110_);
if (v___x_1111_ == 0)
{
uint8_t v___x_1112_; uint8_t v___x_1113_; 
v___x_1112_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1113_ = lean_uint8_dec_eq(v___y_1086_, v___x_1112_);
if (v___x_1113_ == 0)
{
uint8_t v___x_1114_; uint8_t v___x_1115_; 
v___x_1114_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1115_ = lean_uint8_dec_eq(v___y_1086_, v___x_1114_);
if (v___x_1115_ == 0)
{
uint8_t v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1117_ = lean_uint8_dec_eq(v___y_1086_, v___x_1116_);
if (v___x_1117_ == 0)
{
uint8_t v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1119_ = lean_uint8_dec_eq(v___y_1086_, v___x_1118_);
return v___x_1119_;
}
else
{
return v___x_1117_;
}
}
else
{
return v___x_1115_;
}
}
else
{
return v___x_1113_;
}
}
else
{
return v___x_1111_;
}
}
else
{
return v___x_1109_;
}
}
else
{
return v___x_1107_;
}
}
else
{
return v___x_1105_;
}
}
else
{
return v___x_1103_;
}
}
else
{
return v___x_1101_;
}
}
else
{
return v___x_1099_;
}
}
else
{
return v___x_1097_;
}
}
else
{
return v___x_1095_;
}
}
else
{
return v___x_1093_;
}
}
else
{
return v___x_1091_;
}
}
else
{
return v___x_1089_;
}
}
v___jp_1120_:
{
uint8_t v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1122_ = lean_uint8_dec_le(v___x_1121_, v___y_1086_);
if (v___x_1122_ == 0)
{
goto v___jp_1087_;
}
else
{
uint8_t v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1124_ = lean_uint8_dec_le(v___y_1086_, v___x_1123_);
if (v___x_1124_ == 0)
{
goto v___jp_1087_;
}
else
{
return v___x_1124_;
}
}
}
v___jp_1125_:
{
uint8_t v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1127_ = lean_uint8_dec_le(v___x_1126_, v___y_1086_);
if (v___x_1127_ == 0)
{
goto v___jp_1120_;
}
else
{
uint8_t v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1129_ = lean_uint8_dec_le(v___y_1086_, v___x_1128_);
if (v___x_1129_ == 0)
{
goto v___jp_1120_;
}
else
{
return v___x_1129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed(lean_object* v___y_1134_){
_start:
{
uint8_t v___y_297__boxed_1135_; uint8_t v_res_1136_; lean_object* v_r_1137_; 
v___y_297__boxed_1135_ = lean_unbox(v___y_1134_);
v_res_1136_ = l_Std_Http_URI_EncodedUserInfo_encode___lam__0(v___y_297__boxed_1135_);
v_r_1137_ = lean_box(v_res_1136_);
return v_r_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object* v_s_1139_){
_start:
{
lean_object* v___f_1140_; lean_object* v___x_1141_; 
v___f_1140_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1141_ = l_Std_Http_URI_EncodedString_encode(v___f_1140_, v_s_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___boxed(lean_object* v_s_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Std_Http_URI_EncodedUserInfo_encode(v_s_1142_);
lean_dec_ref(v_s_1142_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object* v_ba_1144_){
_start:
{
lean_object* v___f_1145_; lean_object* v___x_1146_; 
v___f_1145_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1146_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1145_, v_ba_1144_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x21(lean_object* v_ba_1147_){
_start:
{
lean_object* v___f_1148_; lean_object* v___x_1149_; 
v___f_1148_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1149_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1148_, v_ba_1147_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode(lean_object* v_userInfo_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Std_Http_URI_EncodedString_decode___redArg(v_userInfo_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode___boxed(lean_object* v_userInfo_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Std_Http_URI_EncodedUserInfo_decode(v_userInfo_1152_);
lean_dec_ref(v_userInfo_1152_);
return v_res_1153_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryParam_encode___lam__0(uint8_t v___y_1154_){
_start:
{
uint8_t v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1212_ = lean_uint8_dec_le(v___x_1211_, v___y_1154_);
if (v___x_1212_ == 0)
{
goto v___jp_1206_;
}
else
{
uint8_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1214_ = lean_uint8_dec_le(v___y_1154_, v___x_1213_);
if (v___x_1214_ == 0)
{
goto v___jp_1206_;
}
else
{
goto v___jp_1155_;
}
}
v___jp_1155_:
{
uint8_t v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1157_ = lean_uint8_dec_eq(v___y_1154_, v___x_1156_);
if (v___x_1157_ == 0)
{
uint8_t v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1159_ = lean_uint8_dec_eq(v___y_1154_, v___x_1158_);
if (v___x_1159_ == 0)
{
uint8_t v___x_1160_; 
v___x_1160_ = 1;
return v___x_1160_;
}
else
{
return v___x_1157_;
}
}
else
{
uint8_t v___x_1161_; 
v___x_1161_ = 0;
return v___x_1161_;
}
}
v___jp_1162_:
{
uint8_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_1164_ = lean_uint8_dec_eq(v___y_1154_, v___x_1163_);
if (v___x_1164_ == 0)
{
uint8_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_1166_ = lean_uint8_dec_eq(v___y_1154_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint8_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1168_ = lean_uint8_dec_eq(v___y_1154_, v___x_1167_);
if (v___x_1168_ == 0)
{
uint8_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_1170_ = lean_uint8_dec_eq(v___y_1154_, v___x_1169_);
if (v___x_1170_ == 0)
{
uint8_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1172_ = lean_uint8_dec_eq(v___y_1154_, v___x_1171_);
if (v___x_1172_ == 0)
{
uint8_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1174_ = lean_uint8_dec_eq(v___y_1154_, v___x_1173_);
if (v___x_1174_ == 0)
{
uint8_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1176_ = lean_uint8_dec_eq(v___y_1154_, v___x_1175_);
if (v___x_1176_ == 0)
{
uint8_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1178_ = lean_uint8_dec_eq(v___y_1154_, v___x_1177_);
if (v___x_1178_ == 0)
{
uint8_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1180_ = lean_uint8_dec_eq(v___y_1154_, v___x_1179_);
if (v___x_1180_ == 0)
{
uint8_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1182_ = lean_uint8_dec_eq(v___y_1154_, v___x_1181_);
if (v___x_1182_ == 0)
{
uint8_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1184_ = lean_uint8_dec_eq(v___y_1154_, v___x_1183_);
if (v___x_1184_ == 0)
{
uint8_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1186_ = lean_uint8_dec_eq(v___y_1154_, v___x_1185_);
if (v___x_1186_ == 0)
{
uint8_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1188_ = lean_uint8_dec_eq(v___y_1154_, v___x_1187_);
if (v___x_1188_ == 0)
{
uint8_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1190_ = lean_uint8_dec_eq(v___y_1154_, v___x_1189_);
if (v___x_1190_ == 0)
{
uint8_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1192_ = lean_uint8_dec_eq(v___y_1154_, v___x_1191_);
if (v___x_1192_ == 0)
{
uint8_t v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1194_ = lean_uint8_dec_eq(v___y_1154_, v___x_1193_);
if (v___x_1194_ == 0)
{
uint8_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1196_ = lean_uint8_dec_eq(v___y_1154_, v___x_1195_);
if (v___x_1196_ == 0)
{
uint8_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0);
v___x_1198_ = lean_uint8_dec_eq(v___y_1154_, v___x_1197_);
if (v___x_1198_ == 0)
{
uint8_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1);
v___x_1200_ = lean_uint8_dec_eq(v___y_1154_, v___x_1199_);
if (v___x_1200_ == 0)
{
return v___x_1200_;
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
}
v___jp_1201_:
{
uint8_t v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1203_ = lean_uint8_dec_le(v___x_1202_, v___y_1154_);
if (v___x_1203_ == 0)
{
goto v___jp_1162_;
}
else
{
uint8_t v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1205_ = lean_uint8_dec_le(v___y_1154_, v___x_1204_);
if (v___x_1205_ == 0)
{
goto v___jp_1162_;
}
else
{
goto v___jp_1155_;
}
}
}
v___jp_1206_:
{
uint8_t v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1208_ = lean_uint8_dec_le(v___x_1207_, v___y_1154_);
if (v___x_1208_ == 0)
{
goto v___jp_1201_;
}
else
{
uint8_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1210_ = lean_uint8_dec_le(v___y_1154_, v___x_1209_);
if (v___x_1210_ == 0)
{
goto v___jp_1201_;
}
else
{
goto v___jp_1155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed(lean_object* v___y_1215_){
_start:
{
uint8_t v___y_419__boxed_1216_; uint8_t v_res_1217_; lean_object* v_r_1218_; 
v___y_419__boxed_1216_ = lean_unbox(v___y_1215_);
v_res_1217_ = l_Std_Http_URI_EncodedQueryParam_encode___lam__0(v___y_419__boxed_1216_);
v_r_1218_ = lean_box(v_res_1217_);
return v_r_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode(lean_object* v_s_1220_){
_start:
{
lean_object* v___f_1221_; lean_object* v___x_1222_; 
v___f_1221_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1222_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_1220_, v___f_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___boxed(lean_object* v_s_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Std_Http_URI_EncodedQueryParam_encode(v_s_1223_);
lean_dec_ref(v_s_1223_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f(lean_object* v_ba_1225_){
_start:
{
lean_object* v___f_1226_; lean_object* v___x_1227_; 
v___f_1226_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1227_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_1225_, v___f_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x21(lean_object* v_ba_1228_){
_start:
{
lean_object* v___f_1229_; lean_object* v___x_1230_; 
v___f_1229_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1230_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v_ba_1228_, v___f_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object* v_s_1231_){
_start:
{
lean_object* v___f_1232_; lean_object* v___x_1233_; 
v___f_1232_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1233_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_1231_, v___f_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f___boxed(lean_object* v_s_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_s_1234_);
lean_dec_ref(v_s_1234_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object* v_param_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_param_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode___boxed(lean_object* v_param_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Std_Http_URI_EncodedQueryParam_decode(v_param_1238_);
lean_dec_ref(v_param_1238_);
return v_res_1239_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_URI_Encoding(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
