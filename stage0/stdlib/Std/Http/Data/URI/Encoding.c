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
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(lean_object* v_r_59_, uint8_t v_v_60_){
_start:
{
uint8_t v___x_61_; uint8_t v___x_62_; 
v___x_61_ = l_Std_Http_URI_isEncodedChar(v_r_59_, v_v_60_);
v___x_62_ = lean_bool_not(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed(lean_object* v_r_63_, lean_object* v_v_64_){
_start:
{
uint8_t v_v_boxed_65_; uint8_t v_res_66_; lean_object* v_r_67_; 
v_v_boxed_65_ = lean_unbox(v_v_64_);
v_res_66_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(v_r_63_, v_v_boxed_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars(lean_object* v_r_87_, lean_object* v_s_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_89_ = lean_byte_array_data(v_s_88_);
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_array_get_size(v___x_89_);
v___x_92_ = ((lean_object*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9));
v___x_93_ = lean_nat_dec_lt(v___x_90_, v___x_91_);
if (v___x_93_ == 0)
{
uint8_t v___x_94_; 
lean_dec_ref(v___x_89_);
lean_dec_ref(v_r_87_);
v___x_94_ = lean_bool_not(v___x_93_);
return v___x_94_;
}
else
{
if (v___x_93_ == 0)
{
uint8_t v___x_95_; 
lean_dec_ref(v___x_89_);
lean_dec_ref(v_r_87_);
v___x_95_ = lean_bool_not(v___x_93_);
return v___x_95_;
}
else
{
lean_object* v___f_96_; size_t v___x_97_; size_t v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; uint8_t v___x_101_; 
v___f_96_ = lean_alloc_closure((void*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed), 2, 1);
lean_closure_set(v___f_96_, 0, v_r_87_);
v___x_97_ = ((size_t)0ULL);
v___x_98_ = lean_usize_of_nat(v___x_91_);
v___x_99_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_92_, v___f_96_, v___x_89_, v___x_97_, v___x_98_);
v___x_100_ = lean_unbox(v___x_99_);
lean_dec(v___x_99_);
v___x_101_ = lean_bool_not(v___x_100_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___boxed(lean_object* v_r_102_, lean_object* v_s_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_102_, v_s_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(lean_object* v_r_106_, uint8_t v_v_107_){
_start:
{
uint8_t v___x_108_; uint8_t v___x_109_; 
v___x_108_ = l_Std_Http_URI_isEncodedQueryChar(v_r_106_, v_v_107_);
v___x_109_ = lean_bool_not(v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed(lean_object* v_r_110_, lean_object* v_v_111_){
_start:
{
uint8_t v_v_boxed_112_; uint8_t v_res_113_; lean_object* v_r_114_; 
v_v_boxed_112_ = lean_unbox(v_v_111_);
v_res_113_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(v_r_110_, v_v_boxed_112_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(lean_object* v_r_115_, lean_object* v_s_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_117_ = lean_byte_array_data(v_s_116_);
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_array_get_size(v___x_117_);
v___x_120_ = ((lean_object*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9));
v___x_121_ = lean_nat_dec_lt(v___x_118_, v___x_119_);
if (v___x_121_ == 0)
{
uint8_t v___x_122_; 
lean_dec_ref(v___x_117_);
lean_dec_ref(v_r_115_);
v___x_122_ = lean_bool_not(v___x_121_);
return v___x_122_;
}
else
{
if (v___x_121_ == 0)
{
uint8_t v___x_123_; 
lean_dec_ref(v___x_117_);
lean_dec_ref(v_r_115_);
v___x_123_ = lean_bool_not(v___x_121_);
return v___x_123_;
}
else
{
lean_object* v___f_124_; size_t v___x_125_; size_t v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; uint8_t v___x_129_; 
v___f_124_ = lean_alloc_closure((void*)(l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed), 2, 1);
lean_closure_set(v___f_124_, 0, v_r_115_);
v___x_125_ = ((size_t)0ULL);
v___x_126_ = lean_usize_of_nat(v___x_119_);
v___x_127_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_120_, v___f_124_, v___x_117_, v___x_125_, v___x_126_);
v___x_128_ = lean_unbox(v___x_127_);
lean_dec(v___x_127_);
v___x_129_ = lean_bool_not(v___x_128_);
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___boxed(lean_object* v_r_130_, lean_object* v_s_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_130_, v_s_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(lean_object* v_ba_134_, lean_object* v_i_135_){
_start:
{
uint8_t v___y_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = lean_byte_array_size(v_ba_134_);
v___x_143_ = lean_nat_dec_lt(v_i_135_, v___x_142_);
if (v___x_143_ == 0)
{
uint8_t v___x_144_; 
lean_dec(v_i_135_);
v___x_144_ = 1;
return v___x_144_;
}
else
{
uint8_t v_c_145_; uint8_t v___x_146_; uint8_t v___x_147_; 
v_c_145_ = lean_byte_array_fget(v_ba_134_, v_i_135_);
v___x_146_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__0, &l_Std_Http_URI_isEncodedChar___closed__0_once, _init_l_Std_Http_URI_isEncodedChar___closed__0);
v___x_147_ = lean_uint8_dec_eq(v_c_145_, v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_add(v_i_135_, v___x_148_);
lean_dec(v_i_135_);
v_i_135_ = v___x_149_;
goto _start;
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_151_ = lean_unsigned_to_nat(2u);
v___x_152_ = lean_nat_add(v_i_135_, v___x_151_);
v___x_153_ = lean_nat_dec_lt(v___x_152_, v___x_142_);
if (v___x_153_ == 0)
{
lean_dec(v___x_152_);
lean_dec(v_i_135_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v_d1_156_; uint8_t v_d2_157_; uint8_t v___y_159_; uint8_t v___y_165_; uint8_t v___y_176_; uint8_t v___y_178_; uint8_t v___y_184_; uint8_t v___x_189_; uint8_t v___x_190_; 
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_i_135_, v___x_154_);
v_d1_156_ = lean_byte_array_fget(v_ba_134_, v___x_155_);
lean_dec(v___x_155_);
v_d2_157_ = lean_byte_array_fget(v_ba_134_, v___x_152_);
lean_dec(v___x_152_);
v___x_189_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_190_ = lean_uint8_dec_le(v___x_189_, v_d1_156_);
if (v___x_190_ == 0)
{
v___y_184_ = v___x_190_;
goto v___jp_183_;
}
else
{
uint8_t v___x_191_; uint8_t v___x_192_; 
v___x_191_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_192_ = lean_uint8_dec_le(v_d1_156_, v___x_191_);
v___y_184_ = v___x_192_;
goto v___jp_183_;
}
v___jp_158_:
{
if (v___y_159_ == 0)
{
uint8_t v___x_160_; uint8_t v___x_161_; 
v___x_160_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_161_ = lean_uint8_dec_le(v___x_160_, v_d2_157_);
if (v___x_161_ == 0)
{
v___y_141_ = v___x_161_;
goto v___jp_140_;
}
else
{
uint8_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__2, &l_Std_Http_URI_isEncodedChar___closed__2_once, _init_l_Std_Http_URI_isEncodedChar___closed__2);
v___x_163_ = lean_uint8_dec_le(v_d2_157_, v___x_162_);
v___y_141_ = v___x_163_;
goto v___jp_140_;
}
}
else
{
goto v___jp_136_;
}
}
v___jp_164_:
{
if (v___y_165_ == 0)
{
uint8_t v___x_166_; uint8_t v___x_167_; 
v___x_166_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_167_ = lean_uint8_dec_le(v___x_166_, v_d2_157_);
if (v___x_167_ == 0)
{
v___y_159_ = v___x_167_;
goto v___jp_158_;
}
else
{
uint8_t v___x_168_; uint8_t v___x_169_; 
v___x_168_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__4, &l_Std_Http_URI_isEncodedChar___closed__4_once, _init_l_Std_Http_URI_isEncodedChar___closed__4);
v___x_169_ = lean_uint8_dec_le(v_d2_157_, v___x_168_);
v___y_159_ = v___x_169_;
goto v___jp_158_;
}
}
else
{
goto v___jp_136_;
}
}
v___jp_170_:
{
uint8_t v___x_171_; uint8_t v___x_172_; 
v___x_171_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_172_ = lean_uint8_dec_le(v___x_171_, v_d2_157_);
if (v___x_172_ == 0)
{
v___y_165_ = v___x_172_;
goto v___jp_164_;
}
else
{
uint8_t v___x_173_; uint8_t v___x_174_; 
v___x_173_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_174_ = lean_uint8_dec_le(v_d2_157_, v___x_173_);
v___y_165_ = v___x_174_;
goto v___jp_164_;
}
}
v___jp_175_:
{
if (v___y_176_ == 0)
{
lean_dec(v_i_135_);
return v___y_176_;
}
else
{
goto v___jp_170_;
}
}
v___jp_177_:
{
if (v___y_178_ == 0)
{
uint8_t v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_180_ = lean_uint8_dec_le(v___x_179_, v_d1_156_);
if (v___x_180_ == 0)
{
v___y_176_ = v___x_180_;
goto v___jp_175_;
}
else
{
uint8_t v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__2, &l_Std_Http_URI_isEncodedChar___closed__2_once, _init_l_Std_Http_URI_isEncodedChar___closed__2);
v___x_182_ = lean_uint8_dec_le(v_d1_156_, v___x_181_);
v___y_176_ = v___x_182_;
goto v___jp_175_;
}
}
else
{
goto v___jp_170_;
}
}
v___jp_183_:
{
if (v___y_184_ == 0)
{
uint8_t v___x_185_; uint8_t v___x_186_; 
v___x_185_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_186_ = lean_uint8_dec_le(v___x_185_, v_d1_156_);
if (v___x_186_ == 0)
{
v___y_178_ = v___x_186_;
goto v___jp_177_;
}
else
{
uint8_t v___x_187_; uint8_t v___x_188_; 
v___x_187_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__4, &l_Std_Http_URI_isEncodedChar___closed__4_once, _init_l_Std_Http_URI_isEncodedChar___closed__4);
v___x_188_ = lean_uint8_dec_le(v_d1_156_, v___x_187_);
v___y_178_ = v___x_188_;
goto v___jp_177_;
}
}
else
{
goto v___jp_170_;
}
}
}
}
}
v___jp_136_:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_unsigned_to_nat(3u);
v___x_138_ = lean_nat_add(v_i_135_, v___x_137_);
lean_dec(v_i_135_);
v_i_135_ = v___x_138_;
goto _start;
}
v___jp_140_:
{
if (v___y_141_ == 0)
{
lean_dec(v_i_135_);
return v___y_141_;
}
else
{
goto v___jp_136_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop___boxed(lean_object* v_ba_193_, lean_object* v_i_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_193_, v_i_194_);
lean_dec_ref(v_ba_193_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidPercentEncoding(lean_object* v_ba_197_){
_start:
{
lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_197_, v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidPercentEncoding___boxed(lean_object* v_ba_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_200_);
lean_dec_ref(v_ba_200_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_hexDigit(uint8_t v_n_203_){
_start:
{
uint8_t v___x_204_; uint8_t v___x_205_; 
v___x_204_ = 10;
v___x_205_ = lean_uint8_dec_lt(v_n_203_, v___x_204_);
if (v___x_205_ == 0)
{
uint8_t v___x_206_; uint8_t v___x_207_; uint8_t v___x_208_; 
v___x_206_ = lean_uint8_sub(v_n_203_, v___x_204_);
v___x_207_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_208_ = lean_uint8_add(v___x_206_, v___x_207_);
return v___x_208_;
}
else
{
uint8_t v___x_209_; uint8_t v___x_210_; 
v___x_209_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_210_ = lean_uint8_add(v_n_203_, v___x_209_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigit___boxed(lean_object* v_n_211_){
_start:
{
uint8_t v_n_boxed_212_; uint8_t v_res_213_; lean_object* v_r_214_; 
v_n_boxed_212_ = lean_unbox(v_n_211_);
v_res_213_ = l_Std_Http_URI_hexDigit(v_n_boxed_212_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f(uint8_t v_c_215_){
_start:
{
uint8_t v___y_217_; uint8_t v___y_218_; uint8_t v___y_226_; uint8_t v___y_227_; uint8_t v___x_237_; uint8_t v___y_239_; uint8_t v___x_247_; 
v___x_237_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_247_ = lean_uint8_dec_le(v___x_237_, v_c_215_);
if (v___x_247_ == 0)
{
v___y_239_ = v___x_247_;
goto v___jp_238_;
}
else
{
uint8_t v___x_248_; uint8_t v___x_249_; 
v___x_248_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_249_ = lean_uint8_dec_le(v_c_215_, v___x_248_);
v___y_239_ = v___x_249_;
goto v___jp_238_;
}
v___jp_216_:
{
if (v___y_218_ == 0)
{
lean_object* v___x_219_; 
v___x_219_ = lean_box(0);
return v___x_219_;
}
else
{
uint8_t v___x_220_; uint8_t v___x_221_; uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_220_ = lean_uint8_sub(v_c_215_, v___y_217_);
v___x_221_ = 10;
v___x_222_ = lean_uint8_add(v___x_220_, v___x_221_);
v___x_223_ = lean_box(v___x_222_);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
v___jp_225_:
{
if (v___y_227_ == 0)
{
uint8_t v___x_228_; uint8_t v___x_229_; 
v___x_228_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_229_ = lean_uint8_dec_le(v___x_228_, v_c_215_);
if (v___x_229_ == 0)
{
v___y_217_ = v___x_228_;
v___y_218_ = v___x_229_;
goto v___jp_216_;
}
else
{
uint8_t v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__2, &l_Std_Http_URI_isEncodedChar___closed__2_once, _init_l_Std_Http_URI_isEncodedChar___closed__2);
v___x_231_ = lean_uint8_dec_le(v_c_215_, v___x_230_);
v___y_217_ = v___x_228_;
v___y_218_ = v___x_231_;
goto v___jp_216_;
}
}
else
{
uint8_t v___x_232_; uint8_t v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_232_ = lean_uint8_sub(v_c_215_, v___y_226_);
v___x_233_ = 10;
v___x_234_ = lean_uint8_add(v___x_232_, v___x_233_);
v___x_235_ = lean_box(v___x_234_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
v___jp_238_:
{
if (v___y_239_ == 0)
{
uint8_t v___x_240_; uint8_t v___x_241_; 
v___x_240_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_241_ = lean_uint8_dec_le(v___x_240_, v_c_215_);
if (v___x_241_ == 0)
{
v___y_226_ = v___x_240_;
v___y_227_ = v___x_241_;
goto v___jp_225_;
}
else
{
uint8_t v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__4, &l_Std_Http_URI_isEncodedChar___closed__4_once, _init_l_Std_Http_URI_isEncodedChar___closed__4);
v___x_243_ = lean_uint8_dec_le(v_c_215_, v___x_242_);
v___y_226_ = v___x_240_;
v___y_227_ = v___x_243_;
goto v___jp_225_;
}
}
else
{
uint8_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_uint8_sub(v_c_215_, v___x_237_);
v___x_245_ = lean_box(v___x_244_);
v___x_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f___boxed(lean_object* v_c_250_){
_start:
{
uint8_t v_c_boxed_251_; lean_object* v_res_252_; 
v_c_boxed_251_ = lean_unbox(v_c_250_);
v_res_252_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_c_boxed_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(lean_object* v_x_253_, uint8_t v_x_254_, lean_object* v_h__1_255_){
_start:
{
lean_object* v_data_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_data_256_ = lean_byte_array_data(v_x_253_);
v___x_257_ = lean_box(v_x_254_);
v___x_258_ = lean_apply_2(v_h__1_255_, v_data_256_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg___boxed(lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_h__1_261_){
_start:
{
uint8_t v_x_17__boxed_262_; lean_object* v_res_263_; 
v_x_17__boxed_262_ = lean_unbox(v_x_260_);
v_res_263_ = l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(v_x_259_, v_x_17__boxed_262_, v_h__1_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(lean_object* v_motive_264_, lean_object* v_x_265_, uint8_t v_x_266_, lean_object* v_h__1_267_){
_start:
{
lean_object* v_data_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_data_268_ = lean_byte_array_data(v_x_265_);
v___x_269_ = lean_box(v_x_266_);
v___x_270_ = lean_apply_2(v_h__1_267_, v_data_268_, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___boxed(lean_object* v_motive_271_, lean_object* v_x_272_, lean_object* v_x_273_, lean_object* v_h__1_274_){
_start:
{
uint8_t v_x_29__boxed_275_; lean_object* v_res_276_; 
v_x_29__boxed_275_ = lean_unbox(v_x_273_);
v_res_276_ = l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(v_motive_271_, v_x_272_, v_x_29__boxed_275_, v_h__1_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter___redArg(lean_object* v_x_277_, lean_object* v_x_278_, lean_object* v_h__1_279_, lean_object* v_h__2_280_){
_start:
{
if (lean_obj_tag(v_x_277_) == 0)
{
lean_object* v___x_281_; 
lean_dec(v_h__2_280_);
v___x_281_ = lean_apply_1(v_h__1_279_, v_x_278_);
return v___x_281_;
}
else
{
lean_object* v_head_282_; lean_object* v_tail_283_; lean_object* v___x_284_; 
lean_dec(v_h__1_279_);
v_head_282_ = lean_ctor_get(v_x_277_, 0);
lean_inc(v_head_282_);
v_tail_283_ = lean_ctor_get(v_x_277_, 1);
lean_inc(v_tail_283_);
lean_dec_ref_known(v_x_277_, 2);
v___x_284_ = lean_apply_3(v_h__2_280_, v_head_282_, v_tail_283_, v_x_278_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter(lean_object* v_motive_285_, lean_object* v_x_286_, lean_object* v_x_287_, lean_object* v_h__1_288_, lean_object* v_h__2_289_){
_start:
{
if (lean_obj_tag(v_x_286_) == 0)
{
lean_object* v___x_290_; 
lean_dec(v_h__2_289_);
v___x_290_ = lean_apply_1(v_h__1_288_, v_x_287_);
return v___x_290_;
}
else
{
lean_object* v_head_291_; lean_object* v_tail_292_; lean_object* v___x_293_; 
lean_dec(v_h__1_288_);
v_head_291_ = lean_ctor_get(v_x_286_, 0);
lean_inc(v_head_291_);
v_tail_292_ = lean_ctor_get(v_x_286_, 1);
lean_inc(v_tail_292_);
lean_dec_ref_known(v_x_286_, 2);
v___x_293_ = lean_apply_3(v_h__2_289_, v_head_291_, v_tail_292_, v_x_287_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty(lean_object* v_r_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_ByteArray_empty;
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___boxed(lean_object* v_r_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Std_Http_URI_EncodedString_empty(v_r_296_);
lean_dec_ref(v_r_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited(lean_object* v_r_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_ByteArray_empty;
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___boxed(lean_object* v_r_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Std_Http_URI_EncodedString_instInhabited(v_r_300_);
lean_dec_ref(v_r_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(lean_object* v_s_302_, uint8_t v_c_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = lean_byte_array_push(v_s_302_, v_c_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg___boxed(lean_object* v_s_305_, lean_object* v_c_306_){
_start:
{
uint8_t v_c_boxed_307_; lean_object* v_res_308_; 
v_c_boxed_307_ = lean_unbox(v_c_306_);
v_res_308_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(v_s_305_, v_c_boxed_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(lean_object* v_r_309_, lean_object* v_s_310_, uint8_t v_c_311_, lean_object* v_h_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = lean_byte_array_push(v_s_310_, v_c_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___boxed(lean_object* v_r_314_, lean_object* v_s_315_, lean_object* v_c_316_, lean_object* v_h_317_){
_start:
{
uint8_t v_c_boxed_318_; lean_object* v_res_319_; 
v_c_boxed_318_ = lean_unbox(v_c_316_);
v_res_319_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(v_r_314_, v_s_315_, v_c_boxed_318_, v_h_317_);
lean_dec_ref(v_r_314_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(uint8_t v_b_320_, lean_object* v_s_321_){
_start:
{
uint8_t v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; uint8_t v___x_325_; uint8_t v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; uint8_t v___x_329_; uint8_t v___x_330_; lean_object* v_ba_331_; 
v___x_322_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__0, &l_Std_Http_URI_isEncodedChar___closed__0_once, _init_l_Std_Http_URI_isEncodedChar___closed__0);
v___x_323_ = lean_byte_array_push(v_s_321_, v___x_322_);
v___x_324_ = 4;
v___x_325_ = lean_uint8_shift_right(v_b_320_, v___x_324_);
v___x_326_ = l_Std_Http_URI_hexDigit(v___x_325_);
v___x_327_ = lean_byte_array_push(v___x_323_, v___x_326_);
v___x_328_ = 15;
v___x_329_ = lean_uint8_land(v_b_320_, v___x_328_);
v___x_330_ = l_Std_Http_URI_hexDigit(v___x_329_);
v_ba_331_ = lean_byte_array_push(v___x_327_, v___x_330_);
return v_ba_331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg___boxed(lean_object* v_b_332_, lean_object* v_s_333_){
_start:
{
uint8_t v_b_boxed_334_; lean_object* v_res_335_; 
v_b_boxed_334_ = lean_unbox(v_b_332_);
v_res_335_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_boxed_334_, v_s_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(lean_object* v_r_336_, uint8_t v_b_337_, lean_object* v_s_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_337_, v_s_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___boxed(lean_object* v_r_340_, lean_object* v_b_341_, lean_object* v_s_342_){
_start:
{
uint8_t v_b_boxed_343_; lean_object* v_res_344_; 
v_b_boxed_343_ = lean_unbox(v_b_341_);
v_res_344_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(v_r_340_, v_b_boxed_343_, v_s_342_);
lean_dec_ref(v_r_340_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(lean_object* v_r_345_, lean_object* v_as_346_, size_t v_i_347_, size_t v_stop_348_, lean_object* v_b_349_){
_start:
{
lean_object* v___y_351_; uint8_t v___x_355_; 
v___x_355_ = lean_usize_dec_eq(v_i_347_, v_stop_348_);
if (v___x_355_ == 0)
{
uint8_t v___x_356_; uint8_t v___x_357_; uint8_t v___x_358_; 
v___x_356_ = lean_byte_array_uget(v_as_346_, v_i_347_);
v___x_357_ = 128;
v___x_358_ = lean_uint8_dec_lt(v___x_356_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
v___x_359_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_356_, v_b_349_);
v___y_351_ = v___x_359_;
goto v___jp_350_;
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_360_ = lean_box(v___x_356_);
lean_inc_ref(v_r_345_);
v___x_361_ = lean_apply_1(v_r_345_, v___x_360_);
v___x_362_ = lean_unbox(v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
v___x_363_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_356_, v_b_349_);
v___y_351_ = v___x_363_;
goto v___jp_350_;
}
else
{
lean_object* v___x_364_; 
v___x_364_ = lean_byte_array_push(v_b_349_, v___x_356_);
v___y_351_ = v___x_364_;
goto v___jp_350_;
}
}
}
else
{
lean_dec_ref(v_r_345_);
return v_b_349_;
}
v___jp_350_:
{
size_t v___x_352_; size_t v___x_353_; 
v___x_352_ = ((size_t)1ULL);
v___x_353_ = lean_usize_add(v_i_347_, v___x_352_);
v_i_347_ = v___x_353_;
v_b_349_ = v___y_351_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0___boxed(lean_object* v_r_365_, lean_object* v_as_366_, lean_object* v_i_367_, lean_object* v_stop_368_, lean_object* v_b_369_){
_start:
{
size_t v_i_boxed_370_; size_t v_stop_boxed_371_; lean_object* v_res_372_; 
v_i_boxed_370_ = lean_unbox_usize(v_i_367_);
lean_dec(v_i_367_);
v_stop_boxed_371_ = lean_unbox_usize(v_stop_368_);
lean_dec(v_stop_368_);
v_res_372_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_365_, v_as_366_, v_i_boxed_370_, v_stop_boxed_371_, v_b_369_);
lean_dec_ref(v_as_366_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode(lean_object* v_r_373_, lean_object* v_s_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_375_ = l_ByteArray_empty;
v___x_376_ = lean_string_to_utf8(v_s_374_);
v___x_377_ = lean_unsigned_to_nat(0u);
v___x_378_ = lean_byte_array_size(v___x_376_);
v___x_379_ = lean_nat_dec_lt(v___x_377_, v___x_378_);
if (v___x_379_ == 0)
{
lean_dec_ref(v___x_376_);
lean_dec_ref(v_r_373_);
return v___x_375_;
}
else
{
uint8_t v___x_380_; 
v___x_380_ = lean_nat_dec_le(v___x_378_, v___x_378_);
if (v___x_380_ == 0)
{
if (v___x_379_ == 0)
{
lean_dec_ref(v___x_376_);
lean_dec_ref(v_r_373_);
return v___x_375_;
}
else
{
size_t v___x_381_; size_t v___x_382_; lean_object* v___x_383_; 
v___x_381_ = ((size_t)0ULL);
v___x_382_ = lean_usize_of_nat(v___x_378_);
v___x_383_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_373_, v___x_376_, v___x_381_, v___x_382_, v___x_375_);
lean_dec_ref(v___x_376_);
return v___x_383_;
}
}
else
{
size_t v___x_384_; size_t v___x_385_; lean_object* v___x_386_; 
v___x_384_ = ((size_t)0ULL);
v___x_385_ = lean_usize_of_nat(v___x_378_);
v___x_386_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_373_, v___x_376_, v___x_384_, v___x_385_, v___x_375_);
lean_dec_ref(v___x_376_);
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode___boxed(lean_object* v_r_387_, lean_object* v_s_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_Http_URI_EncodedString_encode(v_r_387_, v_s_388_);
lean_dec_ref(v_s_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x3f(lean_object* v_r_390_, lean_object* v_ba_391_){
_start:
{
uint8_t v___x_392_; 
lean_inc_ref(v_ba_391_);
v___x_392_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_390_, v_ba_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
lean_dec_ref(v_ba_391_);
v___x_393_ = lean_box(0);
return v___x_393_;
}
else
{
uint8_t v___x_394_; 
v___x_394_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_391_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
lean_dec_ref(v_ba_391_);
v___x_395_ = lean_box(0);
return v___x_395_;
}
else
{
lean_object* v___x_396_; 
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v_ba_391_);
return v___x_396_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = l_ByteArray_empty;
v___x_399_ = lean_panic_fn_borrowed(v___x_398_, v_msg_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(lean_object* v_r_400_, lean_object* v_msg_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v_msg_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_403_, lean_object* v_msg_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(v_r_403_, v_msg_404_);
lean_dec_ref(v_r_403_);
return v_res_405_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_409_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2));
v___x_410_ = lean_unsigned_to_nat(12u);
v___x_411_ = lean_unsigned_to_nat(320u);
v___x_412_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1));
v___x_413_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_414_ = l_mkPanicMessageWithDecl(v___x_413_, v___x_412_, v___x_411_, v___x_410_, v___x_409_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x21(lean_object* v_r_415_, lean_object* v_ba_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_415_, v_ba_416_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_obj_once(&l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3, &l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3_once, _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3);
v___x_419_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v___x_418_);
return v___x_419_;
}
else
{
lean_object* v_val_420_; 
v_val_420_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_val_420_);
lean_dec_ref_known(v___x_417_, 1);
return v_val_420_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f(lean_object* v_r_421_, lean_object* v_s_422_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_string_to_utf8(v_s_422_);
v___x_424_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_421_, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f___boxed(lean_object* v_r_425_, lean_object* v_s_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_Http_URI_EncodedString_ofString_x3f(v_r_425_, v_s_426_);
lean_dec_ref(v_s_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21(lean_object* v_r_428_, lean_object* v_s_429_){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_string_to_utf8(v_s_429_);
v___x_431_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v_r_428_, v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21___boxed(lean_object* v_r_432_, lean_object* v_s_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_Http_URI_EncodedString_ofString_x21(v_r_432_, v_s_433_);
lean_dec_ref(v_s_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg(lean_object* v_ba_435_){
_start:
{
lean_inc_ref(v_ba_435_);
return v_ba_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg___boxed(lean_object* v_ba_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_Http_URI_EncodedString_new___redArg(v_ba_436_);
lean_dec_ref(v_ba_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new(lean_object* v_r_438_, lean_object* v_ba_439_, lean_object* v_valid_440_, lean_object* v___validEncoding_441_){
_start:
{
lean_inc_ref(v_ba_439_);
return v_ba_439_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___boxed(lean_object* v_r_442_, lean_object* v_ba_443_, lean_object* v_valid_444_, lean_object* v___validEncoding_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_Http_URI_EncodedString_new(v_r_442_, v_ba_443_, v_valid_444_, v___validEncoding_445_);
lean_dec_ref(v_ba_443_);
lean_dec_ref(v_r_442_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___lam__0(lean_object* v_es_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = lean_string_from_utf8_unchecked(v_es_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString(lean_object* v_r_450_){
_start:
{
lean_object* v___f_451_; 
v___f_451_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instToString___closed__0));
return v___f_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___boxed(lean_object* v_r_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Std_Http_URI_EncodedString_instToString(v_r_452_);
lean_dec_ref(v_r_452_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(lean_object* v_len_454_, lean_object* v_rawBytes_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_fst_457_; lean_object* v_snd_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_516_; 
v_fst_457_ = lean_ctor_get(v_a_456_, 0);
v_snd_458_ = lean_ctor_get(v_a_456_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_a_456_);
if (v_isSharedCheck_516_ == 0)
{
v___x_460_ = v_a_456_;
v_isShared_461_ = v_isSharedCheck_516_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_snd_458_);
lean_inc(v_fst_457_);
lean_dec(v_a_456_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_516_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
uint8_t v___x_462_; 
v___x_462_ = lean_nat_dec_lt(v_snd_458_, v_len_454_);
if (v___x_462_ == 0)
{
lean_object* v___x_464_; 
if (v_isShared_461_ == 0)
{
v___x_464_ = v___x_460_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_fst_457_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_snd_458_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
else
{
uint8_t v_percent_466_; uint8_t v___x_467_; uint8_t v___x_476_; 
v_percent_466_ = 37;
v___x_467_ = lean_byte_array_fget(v_rawBytes_455_, v_snd_458_);
v___x_476_ = lean_uint8_dec_eq(v___x_467_, v_percent_466_);
if (v___x_476_ == 0)
{
goto v___jp_468_;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_477_ = lean_unsigned_to_nat(1u);
v___x_478_ = lean_nat_add(v_snd_458_, v___x_477_);
v___x_479_ = lean_nat_dec_lt(v___x_478_, v_len_454_);
if (v___x_479_ == 0)
{
lean_dec(v___x_478_);
goto v___jp_468_;
}
else
{
uint8_t v___x_480_; lean_object* v___x_481_; 
lean_del_object(v___x_460_);
v___x_480_ = lean_byte_array_fget(v_rawBytes_455_, v___x_478_);
lean_dec(v___x_478_);
v___x_481_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_480_);
if (lean_obj_tag(v___x_481_) == 1)
{
lean_object* v_val_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v_val_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_val_482_);
lean_dec_ref_known(v___x_481_, 1);
v___x_483_ = lean_unsigned_to_nat(2u);
v___x_484_ = lean_nat_add(v_snd_458_, v___x_483_);
v___x_485_ = lean_nat_dec_lt(v___x_484_, v_len_454_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec(v_val_482_);
lean_dec(v_snd_458_);
v___x_486_ = lean_byte_array_push(v_fst_457_, v___x_467_);
v___x_487_ = lean_byte_array_push(v___x_486_, v___x_480_);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___x_484_);
v_a_456_ = v___x_488_;
goto _start;
}
else
{
uint8_t v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_byte_array_fget(v_rawBytes_455_, v___x_484_);
lean_dec(v___x_484_);
v___x_491_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_490_);
if (lean_obj_tag(v___x_491_) == 1)
{
lean_object* v_val_492_; uint8_t v___x_493_; uint8_t v___x_494_; uint8_t v___x_495_; uint8_t v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_val_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_val_492_);
lean_dec_ref_known(v___x_491_, 1);
v___x_493_ = 4;
v___x_494_ = lean_unbox(v_val_482_);
lean_dec(v_val_482_);
v___x_495_ = lean_uint8_shift_left(v___x_494_, v___x_493_);
v___x_496_ = lean_unbox(v_val_492_);
lean_dec(v_val_492_);
v___x_497_ = lean_uint8_add(v___x_495_, v___x_496_);
v___x_498_ = lean_byte_array_push(v_fst_457_, v___x_497_);
v___x_499_ = lean_unsigned_to_nat(3u);
v___x_500_ = lean_nat_add(v_snd_458_, v___x_499_);
lean_dec(v_snd_458_);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_498_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v_a_456_ = v___x_501_;
goto _start;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec(v___x_491_);
lean_dec(v_val_482_);
v___x_503_ = lean_byte_array_push(v_fst_457_, v___x_467_);
v___x_504_ = lean_byte_array_push(v___x_503_, v___x_480_);
v___x_505_ = lean_byte_array_push(v___x_504_, v___x_490_);
v___x_506_ = lean_unsigned_to_nat(3u);
v___x_507_ = lean_nat_add(v_snd_458_, v___x_506_);
lean_dec(v_snd_458_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_505_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v_a_456_ = v___x_508_;
goto _start;
}
}
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v___x_481_);
v___x_510_ = lean_byte_array_push(v_fst_457_, v___x_467_);
v___x_511_ = lean_byte_array_push(v___x_510_, v___x_480_);
v___x_512_ = lean_unsigned_to_nat(2u);
v___x_513_ = lean_nat_add(v_snd_458_, v___x_512_);
lean_dec(v_snd_458_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_511_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v_a_456_ = v___x_514_;
goto _start;
}
}
}
v___jp_468_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_469_ = lean_byte_array_push(v_fst_457_, v___x_467_);
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = lean_nat_add(v_snd_458_, v___x_470_);
lean_dec(v_snd_458_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 1, v___x_471_);
lean_ctor_set(v___x_460_, 0, v___x_469_);
v___x_473_ = v___x_460_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_471_);
v___x_473_ = v_reuseFailAlloc_475_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
v_a_456_ = v___x_473_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg___boxed(lean_object* v_len_517_, lean_object* v_rawBytes_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_517_, v_rawBytes_518_, v_a_519_);
lean_dec_ref(v_rawBytes_518_);
lean_dec(v_len_517_);
return v_res_520_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0(void){
_start:
{
lean_object* v_i_521_; lean_object* v_decoded_522_; lean_object* v___x_523_; 
v_i_521_ = lean_unsigned_to_nat(0u);
v_decoded_522_ = l_ByteArray_empty;
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v_decoded_522_);
lean_ctor_set(v___x_523_, 1, v_i_521_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg(lean_object* v_es_524_){
_start:
{
lean_object* v_len_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v_fst_528_; uint8_t v___x_529_; 
v_len_525_ = lean_byte_array_size(v_es_524_);
v___x_526_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_527_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_525_, v_es_524_, v___x_526_);
v_fst_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_fst_528_);
lean_dec_ref(v___x_527_);
v___x_529_ = lean_string_validate_utf8(v_fst_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; 
lean_dec(v_fst_528_);
v___x_530_ = lean_box(0);
return v___x_530_;
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_string_from_utf8_unchecked(v_fst_528_);
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg___boxed(lean_object* v_es_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_533_);
lean_dec_ref(v_es_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode(lean_object* v_r_535_, lean_object* v_es_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___boxed(lean_object* v_r_538_, lean_object* v_es_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_Http_URI_EncodedString_decode(v_r_538_, v_es_539_);
lean_dec_ref(v_es_539_);
lean_dec_ref(v_r_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(lean_object* v_len_541_, lean_object* v_rawBytes_542_, lean_object* v_inst_543_, lean_object* v_a_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_541_, v_rawBytes_542_, v_a_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___boxed(lean_object* v_len_546_, lean_object* v_rawBytes_547_, lean_object* v_inst_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(v_len_546_, v_rawBytes_547_, v_inst_548_, v_a_549_);
lean_dec_ref(v_rawBytes_547_);
lean_dec(v_len_546_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___lam__0(lean_object* v_es_551_, lean_object* v_n_552_){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = lean_string_from_utf8_unchecked(v_es_551_);
v___x_554_ = l_String_quote(v___x_553_);
v___x_555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed(lean_object* v_es_556_, lean_object* v_n_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_Http_URI_EncodedString_instRepr___lam__0(v_es_556_, v_n_557_);
lean_dec(v_n_557_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr(lean_object* v_r_560_){
_start:
{
lean_object* v___f_561_; 
v___f_561_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___closed__0));
return v___f_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___boxed(lean_object* v_r_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Std_Http_URI_EncodedString_instRepr(v_r_562_);
lean_dec_ref(v_r_562_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq(lean_object* v_r_565_){
_start:
{
lean_object* v___f_566_; 
v___f_566_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___closed__0));
return v___f_566_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___boxed(lean_object* v_r_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Std_Http_URI_EncodedString_instBEq(v_r_567_);
lean_dec_ref(v_r_567_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable(lean_object* v_r_570_){
_start:
{
lean_object* v___f_571_; 
v___f_571_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___closed__0));
return v___f_571_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___boxed(lean_object* v_r_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_Http_URI_EncodedString_instHashable(v_r_572_);
lean_dec_ref(v_r_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty(lean_object* v_r_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_ByteArray_empty;
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___boxed(lean_object* v_r_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Std_Http_URI_EncodedQueryString_empty(v_r_576_);
lean_dec_ref(v_r_576_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited(lean_object* v_r_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_ByteArray_empty;
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___boxed(lean_object* v_r_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_Http_URI_EncodedQueryString_instInhabited(v_r_580_);
lean_dec_ref(v_r_580_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(lean_object* v_s_582_, uint8_t v_c_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = lean_byte_array_push(v_s_582_, v_c_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg___boxed(lean_object* v_s_585_, lean_object* v_c_586_){
_start:
{
uint8_t v_c_boxed_587_; lean_object* v_res_588_; 
v_c_boxed_587_ = lean_unbox(v_c_586_);
v_res_588_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(v_s_585_, v_c_boxed_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(lean_object* v_r_589_, lean_object* v_s_590_, uint8_t v_c_591_, lean_object* v_h_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = lean_byte_array_push(v_s_590_, v_c_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___boxed(lean_object* v_r_594_, lean_object* v_s_595_, lean_object* v_c_596_, lean_object* v_h_597_){
_start:
{
uint8_t v_c_boxed_598_; lean_object* v_res_599_; 
v_c_boxed_598_ = lean_unbox(v_c_596_);
v_res_599_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(v_r_594_, v_s_595_, v_c_boxed_598_, v_h_597_);
lean_dec_ref(v_r_594_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(lean_object* v_ba_600_, lean_object* v_r_601_){
_start:
{
uint8_t v___x_602_; 
lean_inc_ref(v_ba_600_);
v___x_602_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_601_, v_ba_600_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; 
lean_dec_ref(v_ba_600_);
v___x_603_ = lean_box(0);
return v___x_603_;
}
else
{
uint8_t v___x_604_; 
v___x_604_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_600_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
lean_dec_ref(v_ba_600_);
v___x_605_ = lean_box(0);
return v___x_605_;
}
else
{
lean_object* v___x_606_; 
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v_ba_600_);
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = l_ByteArray_empty;
v___x_609_ = lean_panic_fn_borrowed(v___x_608_, v_msg_607_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(lean_object* v_r_610_, lean_object* v_msg_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v_msg_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_613_, lean_object* v_msg_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(v_r_613_, v_msg_614_);
lean_dec_ref(v_r_613_);
return v_res_615_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_618_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1));
v___x_619_ = lean_unsigned_to_nat(12u);
v___x_620_ = lean_unsigned_to_nat(438u);
v___x_621_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0));
v___x_622_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_623_ = l_mkPanicMessageWithDecl(v___x_622_, v___x_621_, v___x_620_, v___x_619_, v___x_618_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(lean_object* v_ba_624_, lean_object* v_r_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_624_, v_r_625_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_obj_once(&l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2, &l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2_once, _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2);
v___x_628_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v___x_627_);
return v___x_628_;
}
else
{
lean_object* v_val_629_; 
v_val_629_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_val_629_);
lean_dec_ref_known(v___x_626_, 1);
return v_val_629_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f(lean_object* v_s_630_, lean_object* v_r_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_string_to_utf8(v_s_630_);
v___x_633_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v___x_632_, v_r_631_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f___boxed(lean_object* v_s_634_, lean_object* v_r_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_634_, v_r_635_);
lean_dec_ref(v_s_634_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21(lean_object* v_s_637_, lean_object* v_r_638_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_string_to_utf8(v_s_637_);
v___x_640_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v___x_639_, v_r_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21___boxed(lean_object* v_s_641_, lean_object* v_r_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Std_Http_URI_EncodedQueryString_ofString_x21(v_s_641_, v_r_642_);
lean_dec_ref(v_s_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg(lean_object* v_ba_644_){
_start:
{
lean_inc_ref(v_ba_644_);
return v_ba_644_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg___boxed(lean_object* v_ba_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Std_Http_URI_EncodedQueryString_new___redArg(v_ba_645_);
lean_dec_ref(v_ba_645_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new(lean_object* v_r_647_, lean_object* v_ba_648_, lean_object* v_valid_649_, lean_object* v___validEncoding_650_){
_start:
{
lean_inc_ref(v_ba_648_);
return v_ba_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___boxed(lean_object* v_r_651_, lean_object* v_ba_652_, lean_object* v_valid_653_, lean_object* v___validEncoding_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Std_Http_URI_EncodedQueryString_new(v_r_651_, v_ba_652_, v_valid_653_, v___validEncoding_654_);
lean_dec_ref(v_ba_652_);
lean_dec_ref(v_r_651_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(uint8_t v_b_656_, lean_object* v_s_657_){
_start:
{
uint8_t v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; uint8_t v___x_661_; uint8_t v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; uint8_t v___x_665_; uint8_t v___x_666_; lean_object* v_ba_667_; 
v___x_658_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__0, &l_Std_Http_URI_isEncodedChar___closed__0_once, _init_l_Std_Http_URI_isEncodedChar___closed__0);
v___x_659_ = lean_byte_array_push(v_s_657_, v___x_658_);
v___x_660_ = 4;
v___x_661_ = lean_uint8_shift_right(v_b_656_, v___x_660_);
v___x_662_ = l_Std_Http_URI_hexDigit(v___x_661_);
v___x_663_ = lean_byte_array_push(v___x_659_, v___x_662_);
v___x_664_ = 15;
v___x_665_ = lean_uint8_land(v_b_656_, v___x_664_);
v___x_666_ = l_Std_Http_URI_hexDigit(v___x_665_);
v_ba_667_ = lean_byte_array_push(v___x_663_, v___x_666_);
return v_ba_667_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg___boxed(lean_object* v_b_668_, lean_object* v_s_669_){
_start:
{
uint8_t v_b_boxed_670_; lean_object* v_res_671_; 
v_b_boxed_670_ = lean_unbox(v_b_668_);
v_res_671_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_boxed_670_, v_s_669_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(lean_object* v_r_672_, uint8_t v_b_673_, lean_object* v_s_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_673_, v_s_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___boxed(lean_object* v_r_676_, lean_object* v_b_677_, lean_object* v_s_678_){
_start:
{
uint8_t v_b_boxed_679_; lean_object* v_res_680_; 
v_b_boxed_679_ = lean_unbox(v_b_677_);
v_res_680_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(v_r_676_, v_b_boxed_679_, v_s_678_);
lean_dec_ref(v_r_676_);
return v_res_680_;
}
}
static uint8_t _init_l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0(void){
_start:
{
uint32_t v___x_681_; uint8_t v___x_682_; 
v___x_681_ = 32;
v___x_682_ = lean_uint32_to_uint8(v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(lean_object* v_r_683_, lean_object* v_as_684_, size_t v_i_685_, size_t v_stop_686_, lean_object* v_b_687_){
_start:
{
lean_object* v___y_689_; uint8_t v___x_693_; 
v___x_693_ = lean_usize_dec_eq(v_i_685_, v_stop_686_);
if (v___x_693_ == 0)
{
uint8_t v___x_694_; uint8_t v___x_701_; uint8_t v___x_702_; 
v___x_694_ = lean_byte_array_uget(v_as_684_, v_i_685_);
v___x_701_ = 128;
v___x_702_ = lean_uint8_dec_lt(v___x_694_, v___x_701_);
if (v___x_702_ == 0)
{
goto v___jp_695_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_703_ = lean_box(v___x_694_);
lean_inc_ref(v_r_683_);
v___x_704_ = lean_apply_1(v_r_683_, v___x_703_);
v___x_705_ = lean_unbox(v___x_704_);
if (v___x_705_ == 0)
{
goto v___jp_695_;
}
else
{
lean_object* v___x_706_; 
v___x_706_ = lean_byte_array_push(v_b_687_, v___x_694_);
v___y_689_ = v___x_706_;
goto v___jp_688_;
}
}
v___jp_695_:
{
uint8_t v___x_696_; uint8_t v___x_697_; 
v___x_696_ = lean_uint8_once(&l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0, &l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0_once, _init_l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0);
v___x_697_ = lean_uint8_dec_eq(v___x_694_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
v___x_698_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v___x_694_, v_b_687_);
v___y_689_ = v___x_698_;
goto v___jp_688_;
}
else
{
uint8_t v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_700_ = lean_byte_array_push(v_b_687_, v___x_699_);
v___y_689_ = v___x_700_;
goto v___jp_688_;
}
}
}
else
{
lean_dec_ref(v_r_683_);
return v_b_687_;
}
v___jp_688_:
{
size_t v___x_690_; size_t v___x_691_; 
v___x_690_ = ((size_t)1ULL);
v___x_691_ = lean_usize_add(v_i_685_, v___x_690_);
v_i_685_ = v___x_691_;
v_b_687_ = v___y_689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___boxed(lean_object* v_r_707_, lean_object* v_as_708_, lean_object* v_i_709_, lean_object* v_stop_710_, lean_object* v_b_711_){
_start:
{
size_t v_i_boxed_712_; size_t v_stop_boxed_713_; lean_object* v_res_714_; 
v_i_boxed_712_ = lean_unbox_usize(v_i_709_);
lean_dec(v_i_709_);
v_stop_boxed_713_ = lean_unbox_usize(v_stop_710_);
lean_dec(v_stop_710_);
v_res_714_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_707_, v_as_708_, v_i_boxed_712_, v_stop_boxed_713_, v_b_711_);
lean_dec_ref(v_as_708_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode(lean_object* v_s_715_, lean_object* v_r_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_717_ = l_ByteArray_empty;
v___x_718_ = lean_string_to_utf8(v_s_715_);
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = lean_byte_array_size(v___x_718_);
v___x_721_ = lean_nat_dec_lt(v___x_719_, v___x_720_);
if (v___x_721_ == 0)
{
lean_dec_ref(v___x_718_);
lean_dec_ref(v_r_716_);
return v___x_717_;
}
else
{
uint8_t v___x_722_; 
v___x_722_ = lean_nat_dec_le(v___x_720_, v___x_720_);
if (v___x_722_ == 0)
{
if (v___x_721_ == 0)
{
lean_dec_ref(v___x_718_);
lean_dec_ref(v_r_716_);
return v___x_717_;
}
else
{
size_t v___x_723_; size_t v___x_724_; lean_object* v___x_725_; 
v___x_723_ = ((size_t)0ULL);
v___x_724_ = lean_usize_of_nat(v___x_720_);
v___x_725_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_716_, v___x_718_, v___x_723_, v___x_724_, v___x_717_);
lean_dec_ref(v___x_718_);
return v___x_725_;
}
}
else
{
size_t v___x_726_; size_t v___x_727_; lean_object* v___x_728_; 
v___x_726_ = ((size_t)0ULL);
v___x_727_ = lean_usize_of_nat(v___x_720_);
v___x_728_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_716_, v___x_718_, v___x_726_, v___x_727_, v___x_717_);
lean_dec_ref(v___x_718_);
return v___x_728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode___boxed(lean_object* v_s_729_, lean_object* v_r_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_729_, v_r_730_);
lean_dec_ref(v_s_729_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___redArg(lean_object* v_es_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = lean_string_from_utf8_unchecked(v_es_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString(lean_object* v_r_734_, lean_object* v_es_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = lean_string_from_utf8_unchecked(v_es_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___boxed(lean_object* v_r_737_, lean_object* v_es_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_Http_URI_EncodedQueryString_toString(v_r_737_, v_es_738_);
lean_dec_ref(v_r_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(lean_object* v_len_740_, lean_object* v_rawBytes_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_fst_743_; lean_object* v_snd_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_810_; 
v_fst_743_ = lean_ctor_get(v_a_742_, 0);
v_snd_744_ = lean_ctor_get(v_a_742_, 1);
v_isSharedCheck_810_ = !lean_is_exclusive(v_a_742_);
if (v_isSharedCheck_810_ == 0)
{
v___x_746_ = v_a_742_;
v_isShared_747_ = v_isSharedCheck_810_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_snd_744_);
lean_inc(v_fst_743_);
lean_dec(v_a_742_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_810_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
uint8_t v___x_748_; 
v___x_748_ = lean_nat_dec_lt(v_snd_744_, v_len_740_);
if (v___x_748_ == 0)
{
lean_object* v___x_750_; 
if (v_isShared_747_ == 0)
{
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_fst_743_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_snd_744_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
else
{
uint8_t v_plus_752_; uint8_t v___x_753_; uint8_t v___x_762_; 
v_plus_752_ = 43;
v___x_753_ = lean_byte_array_fget(v_rawBytes_741_, v_snd_744_);
v___x_762_ = lean_uint8_dec_eq(v___x_753_, v_plus_752_);
if (v___x_762_ == 0)
{
uint8_t v_percent_763_; uint8_t v___x_764_; 
v_percent_763_ = 37;
v___x_764_ = lean_uint8_dec_eq(v___x_753_, v_percent_763_);
if (v___x_764_ == 0)
{
goto v___jp_754_;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_765_ = lean_unsigned_to_nat(1u);
v___x_766_ = lean_nat_add(v_snd_744_, v___x_765_);
v___x_767_ = lean_nat_dec_lt(v___x_766_, v_len_740_);
if (v___x_767_ == 0)
{
lean_dec(v___x_766_);
goto v___jp_754_;
}
else
{
uint8_t v___x_768_; lean_object* v___x_769_; 
lean_del_object(v___x_746_);
v___x_768_ = lean_byte_array_fget(v_rawBytes_741_, v___x_766_);
lean_dec(v___x_766_);
v___x_769_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_768_);
if (lean_obj_tag(v___x_769_) == 1)
{
lean_object* v_val_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_val_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v___x_769_, 1);
v___x_771_ = lean_unsigned_to_nat(2u);
v___x_772_ = lean_nat_add(v_snd_744_, v___x_771_);
v___x_773_ = lean_nat_dec_lt(v___x_772_, v_len_740_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec(v_val_770_);
lean_dec(v_snd_744_);
v___x_774_ = lean_byte_array_push(v_fst_743_, v___x_753_);
v___x_775_ = lean_byte_array_push(v___x_774_, v___x_768_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v___x_772_);
v_a_742_ = v___x_776_;
goto _start;
}
else
{
uint8_t v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_byte_array_fget(v_rawBytes_741_, v___x_772_);
lean_dec(v___x_772_);
v___x_779_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_778_);
if (lean_obj_tag(v___x_779_) == 1)
{
lean_object* v_val_780_; uint8_t v___x_781_; uint8_t v___x_782_; uint8_t v___x_783_; uint8_t v___x_784_; uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_val_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_val_780_);
lean_dec_ref_known(v___x_779_, 1);
v___x_781_ = 4;
v___x_782_ = lean_unbox(v_val_770_);
lean_dec(v_val_770_);
v___x_783_ = lean_uint8_shift_left(v___x_782_, v___x_781_);
v___x_784_ = lean_unbox(v_val_780_);
lean_dec(v_val_780_);
v___x_785_ = lean_uint8_add(v___x_783_, v___x_784_);
v___x_786_ = lean_byte_array_push(v_fst_743_, v___x_785_);
v___x_787_ = lean_unsigned_to_nat(3u);
v___x_788_ = lean_nat_add(v_snd_744_, v___x_787_);
lean_dec(v_snd_744_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_786_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v_a_742_ = v___x_789_;
goto _start;
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
lean_dec(v___x_779_);
lean_dec(v_val_770_);
v___x_791_ = lean_byte_array_push(v_fst_743_, v___x_753_);
v___x_792_ = lean_byte_array_push(v___x_791_, v___x_768_);
v___x_793_ = lean_byte_array_push(v___x_792_, v___x_778_);
v___x_794_ = lean_unsigned_to_nat(3u);
v___x_795_ = lean_nat_add(v_snd_744_, v___x_794_);
lean_dec(v_snd_744_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_793_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v_a_742_ = v___x_796_;
goto _start;
}
}
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec(v___x_769_);
v___x_798_ = lean_byte_array_push(v_fst_743_, v___x_753_);
v___x_799_ = lean_byte_array_push(v___x_798_, v___x_768_);
v___x_800_ = lean_unsigned_to_nat(2u);
v___x_801_ = lean_nat_add(v_snd_744_, v___x_800_);
lean_dec(v_snd_744_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_799_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v_a_742_ = v___x_802_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_del_object(v___x_746_);
v___x_804_ = 32;
v___x_805_ = lean_byte_array_push(v_fst_743_, v___x_804_);
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = lean_nat_add(v_snd_744_, v___x_806_);
lean_dec(v_snd_744_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_805_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v_a_742_ = v___x_808_;
goto _start;
}
v___jp_754_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_755_ = lean_byte_array_push(v_fst_743_, v___x_753_);
v___x_756_ = lean_unsigned_to_nat(1u);
v___x_757_ = lean_nat_add(v_snd_744_, v___x_756_);
lean_dec(v_snd_744_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_757_);
lean_ctor_set(v___x_746_, 0, v___x_755_);
v___x_759_ = v___x_746_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___x_757_);
v___x_759_ = v_reuseFailAlloc_761_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
v_a_742_ = v___x_759_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg___boxed(lean_object* v_len_811_, lean_object* v_rawBytes_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_811_, v_rawBytes_812_, v_a_813_);
lean_dec_ref(v_rawBytes_812_);
lean_dec(v_len_811_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg(lean_object* v_es_815_){
_start:
{
lean_object* v_len_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v_fst_819_; uint8_t v___x_820_; 
v_len_816_ = lean_byte_array_size(v_es_815_);
v___x_817_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_818_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_816_, v_es_815_, v___x_817_);
v_fst_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_fst_819_);
lean_dec_ref(v___x_818_);
v___x_820_ = lean_string_validate_utf8(v_fst_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; 
lean_dec(v_fst_819_);
v___x_821_ = lean_box(0);
return v___x_821_;
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_string_from_utf8_unchecked(v_fst_819_);
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg___boxed(lean_object* v_es_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_824_);
lean_dec_ref(v_es_824_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode(lean_object* v_r_826_, lean_object* v_es_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___boxed(lean_object* v_r_829_, lean_object* v_es_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Std_Http_URI_EncodedQueryString_decode(v_r_829_, v_es_830_);
lean_dec_ref(v_es_830_);
lean_dec_ref(v_r_829_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(lean_object* v_len_832_, lean_object* v_rawBytes_833_, lean_object* v_inst_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_832_, v_rawBytes_833_, v_a_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___boxed(lean_object* v_len_837_, lean_object* v_rawBytes_838_, lean_object* v_inst_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(v_len_837_, v_rawBytes_838_, v_inst_839_, v_a_840_);
lean_dec_ref(v_rawBytes_838_);
lean_dec(v_len_837_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringEncodedQueryString(lean_object* v_r_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = lean_alloc_closure((void*)(l_Std_Http_URI_EncodedQueryString_toString___boxed), 2, 1);
lean_closure_set(v___x_843_, 0, v_r_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString(lean_object* v_r_844_){
_start:
{
lean_object* v___f_845_; 
v___f_845_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___closed__0));
return v___f_845_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___boxed(lean_object* v_r_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Std_Http_URI_instReprEncodedQueryString(v_r_846_);
lean_dec_ref(v_r_846_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString(lean_object* v_r_848_){
_start:
{
lean_object* v___f_849_; 
v___f_849_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___closed__0));
return v___f_849_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___boxed(lean_object* v_r_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Std_Http_URI_instBEqEncodedQueryString(v_r_850_);
lean_dec_ref(v_r_850_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString(lean_object* v_r_852_){
_start:
{
lean_object* v___f_853_; 
v___f_853_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___closed__0));
return v___f_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___boxed(lean_object* v_r_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Std_Http_URI_instHashableEncodedQueryString(v_r_854_);
lean_dec_ref(v_r_854_);
return v_res_855_;
}
}
static uint64_t _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1(void){
_start:
{
lean_object* v___x_862_; uint64_t v___x_863_; 
v___x_862_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__0));
v___x_863_ = lean_byte_array_hash(v___x_862_);
return v___x_863_;
}
}
static lean_object* _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2));
v___x_871_ = lean_byte_array_size(v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT uint64_t l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0(lean_object* v_x_872_){
_start:
{
if (lean_obj_tag(v_x_872_) == 0)
{
uint64_t v___x_873_; 
v___x_873_ = lean_uint64_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1, &l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1);
return v___x_873_;
}
else
{
lean_object* v_val_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; lean_object* v___x_880_; uint64_t v___x_881_; 
v_val_874_ = lean_ctor_get(v_x_872_, 0);
v___x_875_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2));
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = lean_obj_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3, &l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3);
v___x_878_ = lean_byte_array_size(v_val_874_);
v___x_879_ = 0;
v___x_880_ = lean_byte_array_copy_slice(v_val_874_, v___x_876_, v___x_875_, v___x_877_, v___x_878_, v___x_879_);
v___x_881_ = lean_byte_array_hash(v___x_880_);
lean_dec_ref(v___x_880_);
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___boxed(lean_object* v_x_882_){
_start:
{
uint64_t v_res_883_; lean_object* v_r_884_; 
v_res_883_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0(v_x_882_);
lean_dec(v_x_882_);
v_r_884_ = lean_box_uint64(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString(lean_object* v_r_886_){
_start:
{
lean_object* v___f_887_; 
v___f_887_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___closed__0));
return v___f_887_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___boxed(lean_object* v_r_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Std_Http_URI_instHashableOptionEncodedQueryString(v_r_888_);
lean_dec_ref(v_r_888_);
return v_res_889_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0(void){
_start:
{
uint32_t v___x_890_; uint8_t v___x_891_; 
v___x_890_ = 58;
v___x_891_ = lean_uint32_to_uint8(v___x_890_);
return v___x_891_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1(void){
_start:
{
uint32_t v___x_892_; uint8_t v___x_893_; 
v___x_892_ = 64;
v___x_893_ = lean_uint32_to_uint8(v___x_892_);
return v___x_893_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2(void){
_start:
{
uint32_t v___x_894_; uint8_t v___x_895_; 
v___x_894_ = 38;
v___x_895_ = lean_uint32_to_uint8(v___x_894_);
return v___x_895_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3(void){
_start:
{
uint32_t v___x_896_; uint8_t v___x_897_; 
v___x_896_ = 39;
v___x_897_ = lean_uint32_to_uint8(v___x_896_);
return v___x_897_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4(void){
_start:
{
uint32_t v___x_898_; uint8_t v___x_899_; 
v___x_898_ = 40;
v___x_899_ = lean_uint32_to_uint8(v___x_898_);
return v___x_899_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5(void){
_start:
{
uint32_t v___x_900_; uint8_t v___x_901_; 
v___x_900_ = 41;
v___x_901_ = lean_uint32_to_uint8(v___x_900_);
return v___x_901_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6(void){
_start:
{
uint32_t v___x_902_; uint8_t v___x_903_; 
v___x_902_ = 42;
v___x_903_ = lean_uint32_to_uint8(v___x_902_);
return v___x_903_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7(void){
_start:
{
uint32_t v___x_904_; uint8_t v___x_905_; 
v___x_904_ = 44;
v___x_905_ = lean_uint32_to_uint8(v___x_904_);
return v___x_905_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8(void){
_start:
{
uint32_t v___x_906_; uint8_t v___x_907_; 
v___x_906_ = 59;
v___x_907_ = lean_uint32_to_uint8(v___x_906_);
return v___x_907_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9(void){
_start:
{
uint32_t v___x_908_; uint8_t v___x_909_; 
v___x_908_ = 61;
v___x_909_ = lean_uint32_to_uint8(v___x_908_);
return v___x_909_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10(void){
_start:
{
uint32_t v___x_910_; uint8_t v___x_911_; 
v___x_910_ = 33;
v___x_911_ = lean_uint32_to_uint8(v___x_910_);
return v___x_911_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11(void){
_start:
{
uint32_t v___x_912_; uint8_t v___x_913_; 
v___x_912_ = 36;
v___x_913_ = lean_uint32_to_uint8(v___x_912_);
return v___x_913_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12(void){
_start:
{
uint32_t v___x_914_; uint8_t v___x_915_; 
v___x_914_ = 95;
v___x_915_ = lean_uint32_to_uint8(v___x_914_);
return v___x_915_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13(void){
_start:
{
uint32_t v___x_916_; uint8_t v___x_917_; 
v___x_916_ = 126;
v___x_917_ = lean_uint32_to_uint8(v___x_916_);
return v___x_917_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14(void){
_start:
{
uint32_t v___x_918_; uint8_t v___x_919_; 
v___x_918_ = 45;
v___x_919_ = lean_uint32_to_uint8(v___x_918_);
return v___x_919_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15(void){
_start:
{
uint32_t v___x_920_; uint8_t v___x_921_; 
v___x_920_ = 46;
v___x_921_ = lean_uint32_to_uint8(v___x_920_);
return v___x_921_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16(void){
_start:
{
uint32_t v___x_922_; uint8_t v___x_923_; 
v___x_922_ = 90;
v___x_923_ = lean_uint32_to_uint8(v___x_922_);
return v___x_923_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17(void){
_start:
{
uint32_t v___x_924_; uint8_t v___x_925_; 
v___x_924_ = 122;
v___x_925_ = lean_uint32_to_uint8(v___x_924_);
return v___x_925_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0(uint8_t v___y_926_){
_start:
{
uint8_t v___y_928_; uint8_t v___y_934_; uint8_t v___y_954_; uint8_t v___y_960_; uint8_t v___y_966_; uint8_t v___y_972_; uint8_t v___y_978_; uint8_t v___x_983_; uint8_t v___x_984_; 
v___x_983_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_984_ = lean_uint8_dec_le(v___x_983_, v___y_926_);
if (v___x_984_ == 0)
{
v___y_978_ = v___x_984_;
goto v___jp_977_;
}
else
{
uint8_t v___x_985_; uint8_t v___x_986_; 
v___x_985_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_986_ = lean_uint8_dec_le(v___y_926_, v___x_985_);
v___y_978_ = v___x_986_;
goto v___jp_977_;
}
v___jp_927_:
{
if (v___y_928_ == 0)
{
uint8_t v___x_929_; uint8_t v___x_930_; 
v___x_929_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_930_ = lean_uint8_dec_eq(v___y_926_, v___x_929_);
if (v___x_930_ == 0)
{
uint8_t v___x_931_; uint8_t v___x_932_; 
v___x_931_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_932_ = lean_uint8_dec_eq(v___y_926_, v___x_931_);
return v___x_932_;
}
else
{
return v___x_930_;
}
}
else
{
return v___y_928_;
}
}
v___jp_933_:
{
if (v___y_934_ == 0)
{
uint8_t v___x_935_; uint8_t v___x_936_; 
v___x_935_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_936_ = lean_uint8_dec_eq(v___y_926_, v___x_935_);
if (v___x_936_ == 0)
{
uint8_t v___x_937_; uint8_t v___x_938_; 
v___x_937_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_938_ = lean_uint8_dec_eq(v___y_926_, v___x_937_);
if (v___x_938_ == 0)
{
uint8_t v___x_939_; uint8_t v___x_940_; 
v___x_939_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_940_ = lean_uint8_dec_eq(v___y_926_, v___x_939_);
if (v___x_940_ == 0)
{
uint8_t v___x_941_; uint8_t v___x_942_; 
v___x_941_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_942_ = lean_uint8_dec_eq(v___y_926_, v___x_941_);
if (v___x_942_ == 0)
{
uint8_t v___x_943_; uint8_t v___x_944_; 
v___x_943_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_944_ = lean_uint8_dec_eq(v___y_926_, v___x_943_);
if (v___x_944_ == 0)
{
uint8_t v___x_945_; uint8_t v___x_946_; 
v___x_945_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_946_ = lean_uint8_dec_eq(v___y_926_, v___x_945_);
if (v___x_946_ == 0)
{
uint8_t v___x_947_; uint8_t v___x_948_; 
v___x_947_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_948_ = lean_uint8_dec_eq(v___y_926_, v___x_947_);
if (v___x_948_ == 0)
{
uint8_t v___x_949_; uint8_t v___x_950_; 
v___x_949_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_950_ = lean_uint8_dec_eq(v___y_926_, v___x_949_);
if (v___x_950_ == 0)
{
uint8_t v___x_951_; uint8_t v___x_952_; 
v___x_951_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_952_ = lean_uint8_dec_eq(v___y_926_, v___x_951_);
v___y_928_ = v___x_952_;
goto v___jp_927_;
}
else
{
v___y_928_ = v___x_950_;
goto v___jp_927_;
}
}
else
{
v___y_928_ = v___x_948_;
goto v___jp_927_;
}
}
else
{
v___y_928_ = v___x_946_;
goto v___jp_927_;
}
}
else
{
v___y_928_ = v___x_944_;
goto v___jp_927_;
}
}
else
{
v___y_928_ = v___x_942_;
goto v___jp_927_;
}
}
else
{
v___y_928_ = v___x_940_;
goto v___jp_927_;
}
}
else
{
v___y_928_ = v___x_938_;
goto v___jp_927_;
}
}
else
{
v___y_928_ = v___x_936_;
goto v___jp_927_;
}
}
else
{
return v___y_934_;
}
}
v___jp_953_:
{
if (v___y_954_ == 0)
{
uint8_t v___x_955_; uint8_t v___x_956_; 
v___x_955_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_956_ = lean_uint8_dec_eq(v___y_926_, v___x_955_);
if (v___x_956_ == 0)
{
uint8_t v___x_957_; uint8_t v___x_958_; 
v___x_957_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_958_ = lean_uint8_dec_eq(v___y_926_, v___x_957_);
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
return v___y_954_;
}
}
v___jp_959_:
{
if (v___y_960_ == 0)
{
uint8_t v___x_961_; uint8_t v___x_962_; 
v___x_961_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_962_ = lean_uint8_dec_eq(v___y_926_, v___x_961_);
if (v___x_962_ == 0)
{
uint8_t v___x_963_; uint8_t v___x_964_; 
v___x_963_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_964_ = lean_uint8_dec_eq(v___y_926_, v___x_963_);
v___y_954_ = v___x_964_;
goto v___jp_953_;
}
else
{
v___y_954_ = v___x_962_;
goto v___jp_953_;
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
v___x_967_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_968_ = lean_uint8_dec_eq(v___y_926_, v___x_967_);
if (v___x_968_ == 0)
{
uint8_t v___x_969_; uint8_t v___x_970_; 
v___x_969_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_970_ = lean_uint8_dec_eq(v___y_926_, v___x_969_);
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
v___x_973_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_974_ = lean_uint8_dec_le(v___x_973_, v___y_926_);
if (v___x_974_ == 0)
{
v___y_966_ = v___x_974_;
goto v___jp_965_;
}
else
{
uint8_t v___x_975_; uint8_t v___x_976_; 
v___x_975_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_976_ = lean_uint8_dec_le(v___y_926_, v___x_975_);
v___y_966_ = v___x_976_;
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
v___x_979_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_980_ = lean_uint8_dec_le(v___x_979_, v___y_926_);
if (v___x_980_ == 0)
{
v___y_972_ = v___x_980_;
goto v___jp_971_;
}
else
{
uint8_t v___x_981_; uint8_t v___x_982_; 
v___x_981_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_982_ = lean_uint8_dec_le(v___y_926_, v___x_981_);
v___y_972_ = v___x_982_;
goto v___jp_971_;
}
}
else
{
return v___y_978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___lam__0___boxed(lean_object* v___y_987_){
_start:
{
uint8_t v___y_318__boxed_988_; uint8_t v_res_989_; lean_object* v_r_990_; 
v___y_318__boxed_988_ = lean_unbox(v___y_987_);
v_res_989_ = l_Std_Http_URI_EncodedSegment_encode___lam__0(v___y_318__boxed_988_);
v_r_990_ = lean_box(v_res_989_);
return v_r_990_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode(lean_object* v_s_992_){
_start:
{
lean_object* v___f_993_; lean_object* v___x_994_; 
v___f_993_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_994_ = l_Std_Http_URI_EncodedString_encode(v___f_993_, v_s_992_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___boxed(lean_object* v_s_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Std_Http_URI_EncodedSegment_encode(v_s_995_);
lean_dec_ref(v_s_995_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object* v_ba_997_){
_start:
{
lean_object* v___f_998_; lean_object* v___x_999_; 
v___f_998_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_999_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_998_, v_ba_997_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x21(lean_object* v_ba_1000_){
_start:
{
lean_object* v___f_1001_; lean_object* v___x_1002_; 
v___f_1001_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_1002_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1001_, v_ba_1000_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object* v_segment_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Std_Http_URI_EncodedString_decode___redArg(v_segment_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode___boxed(lean_object* v_segment_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Std_Http_URI_EncodedSegment_decode(v_segment_1005_);
lean_dec_ref(v_segment_1005_);
return v_res_1006_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0(void){
_start:
{
uint32_t v___x_1007_; uint8_t v___x_1008_; 
v___x_1007_ = 47;
v___x_1008_ = lean_uint32_to_uint8(v___x_1007_);
return v___x_1008_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1(void){
_start:
{
uint32_t v___x_1009_; uint8_t v___x_1010_; 
v___x_1009_ = 63;
v___x_1010_ = lean_uint32_to_uint8(v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedFragment_encode___lam__0(uint8_t v___y_1011_){
_start:
{
uint8_t v___y_1013_; uint8_t v___y_1019_; uint8_t v___y_1025_; uint8_t v___y_1045_; uint8_t v___y_1051_; uint8_t v___y_1057_; uint8_t v___y_1063_; uint8_t v___y_1069_; uint8_t v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1075_ = lean_uint8_dec_le(v___x_1074_, v___y_1011_);
if (v___x_1075_ == 0)
{
v___y_1069_ = v___x_1075_;
goto v___jp_1068_;
}
else
{
uint8_t v___x_1076_; uint8_t v___x_1077_; 
v___x_1076_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1077_ = lean_uint8_dec_le(v___y_1011_, v___x_1076_);
v___y_1069_ = v___x_1077_;
goto v___jp_1068_;
}
v___jp_1012_:
{
if (v___y_1013_ == 0)
{
uint8_t v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0);
v___x_1015_ = lean_uint8_dec_eq(v___y_1011_, v___x_1014_);
if (v___x_1015_ == 0)
{
uint8_t v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1);
v___x_1017_ = lean_uint8_dec_eq(v___y_1011_, v___x_1016_);
return v___x_1017_;
}
else
{
return v___x_1015_;
}
}
else
{
return v___y_1013_;
}
}
v___jp_1018_:
{
if (v___y_1019_ == 0)
{
uint8_t v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_1021_ = lean_uint8_dec_eq(v___y_1011_, v___x_1020_);
if (v___x_1021_ == 0)
{
uint8_t v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_1023_ = lean_uint8_dec_eq(v___y_1011_, v___x_1022_);
v___y_1013_ = v___x_1023_;
goto v___jp_1012_;
}
else
{
v___y_1013_ = v___x_1021_;
goto v___jp_1012_;
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
v___x_1026_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1027_ = lean_uint8_dec_eq(v___y_1011_, v___x_1026_);
if (v___x_1027_ == 0)
{
uint8_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_1029_ = lean_uint8_dec_eq(v___y_1011_, v___x_1028_);
if (v___x_1029_ == 0)
{
uint8_t v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1031_ = lean_uint8_dec_eq(v___y_1011_, v___x_1030_);
if (v___x_1031_ == 0)
{
uint8_t v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1033_ = lean_uint8_dec_eq(v___y_1011_, v___x_1032_);
if (v___x_1033_ == 0)
{
uint8_t v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1035_ = lean_uint8_dec_eq(v___y_1011_, v___x_1034_);
if (v___x_1035_ == 0)
{
uint8_t v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1037_ = lean_uint8_dec_eq(v___y_1011_, v___x_1036_);
if (v___x_1037_ == 0)
{
uint8_t v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1039_ = lean_uint8_dec_eq(v___y_1011_, v___x_1038_);
if (v___x_1039_ == 0)
{
uint8_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1041_ = lean_uint8_dec_eq(v___y_1011_, v___x_1040_);
if (v___x_1041_ == 0)
{
uint8_t v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1043_ = lean_uint8_dec_eq(v___y_1011_, v___x_1042_);
v___y_1019_ = v___x_1043_;
goto v___jp_1018_;
}
else
{
v___y_1019_ = v___x_1041_;
goto v___jp_1018_;
}
}
else
{
v___y_1019_ = v___x_1039_;
goto v___jp_1018_;
}
}
else
{
v___y_1019_ = v___x_1037_;
goto v___jp_1018_;
}
}
else
{
v___y_1019_ = v___x_1035_;
goto v___jp_1018_;
}
}
else
{
v___y_1019_ = v___x_1033_;
goto v___jp_1018_;
}
}
else
{
v___y_1019_ = v___x_1031_;
goto v___jp_1018_;
}
}
else
{
v___y_1019_ = v___x_1029_;
goto v___jp_1018_;
}
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
v___jp_1044_:
{
if (v___y_1045_ == 0)
{
uint8_t v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1047_ = lean_uint8_dec_eq(v___y_1011_, v___x_1046_);
if (v___x_1047_ == 0)
{
uint8_t v___x_1048_; uint8_t v___x_1049_; 
v___x_1048_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1049_ = lean_uint8_dec_eq(v___y_1011_, v___x_1048_);
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
return v___y_1045_;
}
}
v___jp_1050_:
{
if (v___y_1051_ == 0)
{
uint8_t v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1053_ = lean_uint8_dec_eq(v___y_1011_, v___x_1052_);
if (v___x_1053_ == 0)
{
uint8_t v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1055_ = lean_uint8_dec_eq(v___y_1011_, v___x_1054_);
v___y_1045_ = v___x_1055_;
goto v___jp_1044_;
}
else
{
v___y_1045_ = v___x_1053_;
goto v___jp_1044_;
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
v___x_1058_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1059_ = lean_uint8_dec_eq(v___y_1011_, v___x_1058_);
if (v___x_1059_ == 0)
{
uint8_t v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1061_ = lean_uint8_dec_eq(v___y_1011_, v___x_1060_);
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
v___x_1064_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1065_ = lean_uint8_dec_le(v___x_1064_, v___y_1011_);
if (v___x_1065_ == 0)
{
v___y_1057_ = v___x_1065_;
goto v___jp_1056_;
}
else
{
uint8_t v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1067_ = lean_uint8_dec_le(v___y_1011_, v___x_1066_);
v___y_1057_ = v___x_1067_;
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
v___x_1070_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1071_ = lean_uint8_dec_le(v___x_1070_, v___y_1011_);
if (v___x_1071_ == 0)
{
v___y_1063_ = v___x_1071_;
goto v___jp_1062_;
}
else
{
uint8_t v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1073_ = lean_uint8_dec_le(v___y_1011_, v___x_1072_);
v___y_1063_ = v___x_1073_;
goto v___jp_1062_;
}
}
else
{
return v___y_1069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed(lean_object* v___y_1078_){
_start:
{
uint8_t v___y_312__boxed_1079_; uint8_t v_res_1080_; lean_object* v_r_1081_; 
v___y_312__boxed_1079_ = lean_unbox(v___y_1078_);
v_res_1080_ = l_Std_Http_URI_EncodedFragment_encode___lam__0(v___y_312__boxed_1079_);
v_r_1081_ = lean_box(v_res_1080_);
return v_r_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object* v_s_1083_){
_start:
{
lean_object* v___f_1084_; lean_object* v___x_1085_; 
v___f_1084_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1085_ = l_Std_Http_URI_EncodedString_encode(v___f_1084_, v_s_1083_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___boxed(lean_object* v_s_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Std_Http_URI_EncodedFragment_encode(v_s_1086_);
lean_dec_ref(v_s_1086_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object* v_ba_1088_){
_start:
{
lean_object* v___f_1089_; lean_object* v___x_1090_; 
v___f_1089_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1090_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1089_, v_ba_1088_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x21(lean_object* v_ba_1091_){
_start:
{
lean_object* v___f_1092_; lean_object* v___x_1093_; 
v___f_1092_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1093_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1092_, v_ba_1091_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object* v_fragment_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Std_Http_URI_EncodedString_decode___redArg(v_fragment_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode___boxed(lean_object* v_fragment_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Std_Http_URI_EncodedFragment_decode(v_fragment_1096_);
lean_dec_ref(v_fragment_1096_);
return v_res_1097_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedUserInfo_encode___lam__0(uint8_t v___y_1098_){
_start:
{
uint8_t v___y_1100_; uint8_t v___y_1104_; uint8_t v___y_1124_; uint8_t v___y_1130_; uint8_t v___y_1136_; uint8_t v___y_1142_; uint8_t v___y_1148_; uint8_t v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1154_ = lean_uint8_dec_le(v___x_1153_, v___y_1098_);
if (v___x_1154_ == 0)
{
v___y_1148_ = v___x_1154_;
goto v___jp_1147_;
}
else
{
uint8_t v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1156_ = lean_uint8_dec_le(v___y_1098_, v___x_1155_);
v___y_1148_ = v___x_1156_;
goto v___jp_1147_;
}
v___jp_1099_:
{
if (v___y_1100_ == 0)
{
uint8_t v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_1102_ = lean_uint8_dec_eq(v___y_1098_, v___x_1101_);
return v___x_1102_;
}
else
{
return v___y_1100_;
}
}
v___jp_1103_:
{
if (v___y_1104_ == 0)
{
uint8_t v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1106_ = lean_uint8_dec_eq(v___y_1098_, v___x_1105_);
if (v___x_1106_ == 0)
{
uint8_t v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_1108_ = lean_uint8_dec_eq(v___y_1098_, v___x_1107_);
if (v___x_1108_ == 0)
{
uint8_t v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1110_ = lean_uint8_dec_eq(v___y_1098_, v___x_1109_);
if (v___x_1110_ == 0)
{
uint8_t v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1112_ = lean_uint8_dec_eq(v___y_1098_, v___x_1111_);
if (v___x_1112_ == 0)
{
uint8_t v___x_1113_; uint8_t v___x_1114_; 
v___x_1113_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1114_ = lean_uint8_dec_eq(v___y_1098_, v___x_1113_);
if (v___x_1114_ == 0)
{
uint8_t v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1116_ = lean_uint8_dec_eq(v___y_1098_, v___x_1115_);
if (v___x_1116_ == 0)
{
uint8_t v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1118_ = lean_uint8_dec_eq(v___y_1098_, v___x_1117_);
if (v___x_1118_ == 0)
{
uint8_t v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1120_ = lean_uint8_dec_eq(v___y_1098_, v___x_1119_);
if (v___x_1120_ == 0)
{
uint8_t v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1122_ = lean_uint8_dec_eq(v___y_1098_, v___x_1121_);
v___y_1100_ = v___x_1122_;
goto v___jp_1099_;
}
else
{
v___y_1100_ = v___x_1120_;
goto v___jp_1099_;
}
}
else
{
v___y_1100_ = v___x_1118_;
goto v___jp_1099_;
}
}
else
{
v___y_1100_ = v___x_1116_;
goto v___jp_1099_;
}
}
else
{
v___y_1100_ = v___x_1114_;
goto v___jp_1099_;
}
}
else
{
v___y_1100_ = v___x_1112_;
goto v___jp_1099_;
}
}
else
{
v___y_1100_ = v___x_1110_;
goto v___jp_1099_;
}
}
else
{
v___y_1100_ = v___x_1108_;
goto v___jp_1099_;
}
}
else
{
v___y_1100_ = v___x_1106_;
goto v___jp_1099_;
}
}
else
{
return v___y_1104_;
}
}
v___jp_1123_:
{
if (v___y_1124_ == 0)
{
uint8_t v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1126_ = lean_uint8_dec_eq(v___y_1098_, v___x_1125_);
if (v___x_1126_ == 0)
{
uint8_t v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1128_ = lean_uint8_dec_eq(v___y_1098_, v___x_1127_);
v___y_1104_ = v___x_1128_;
goto v___jp_1103_;
}
else
{
v___y_1104_ = v___x_1126_;
goto v___jp_1103_;
}
}
else
{
return v___y_1124_;
}
}
v___jp_1129_:
{
if (v___y_1130_ == 0)
{
uint8_t v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1132_ = lean_uint8_dec_eq(v___y_1098_, v___x_1131_);
if (v___x_1132_ == 0)
{
uint8_t v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1134_ = lean_uint8_dec_eq(v___y_1098_, v___x_1133_);
v___y_1124_ = v___x_1134_;
goto v___jp_1123_;
}
else
{
v___y_1124_ = v___x_1132_;
goto v___jp_1123_;
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
v___x_1137_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1138_ = lean_uint8_dec_eq(v___y_1098_, v___x_1137_);
if (v___x_1138_ == 0)
{
uint8_t v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1140_ = lean_uint8_dec_eq(v___y_1098_, v___x_1139_);
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
v___x_1143_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1144_ = lean_uint8_dec_le(v___x_1143_, v___y_1098_);
if (v___x_1144_ == 0)
{
v___y_1136_ = v___x_1144_;
goto v___jp_1135_;
}
else
{
uint8_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1146_ = lean_uint8_dec_le(v___y_1098_, v___x_1145_);
v___y_1136_ = v___x_1146_;
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
v___x_1149_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1150_ = lean_uint8_dec_le(v___x_1149_, v___y_1098_);
if (v___x_1150_ == 0)
{
v___y_1142_ = v___x_1150_;
goto v___jp_1141_;
}
else
{
uint8_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1152_ = lean_uint8_dec_le(v___y_1098_, v___x_1151_);
v___y_1142_ = v___x_1152_;
goto v___jp_1141_;
}
}
else
{
return v___y_1148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed(lean_object* v___y_1157_){
_start:
{
uint8_t v___y_271__boxed_1158_; uint8_t v_res_1159_; lean_object* v_r_1160_; 
v___y_271__boxed_1158_ = lean_unbox(v___y_1157_);
v_res_1159_ = l_Std_Http_URI_EncodedUserInfo_encode___lam__0(v___y_271__boxed_1158_);
v_r_1160_ = lean_box(v_res_1159_);
return v_r_1160_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object* v_s_1162_){
_start:
{
lean_object* v___f_1163_; lean_object* v___x_1164_; 
v___f_1163_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1164_ = l_Std_Http_URI_EncodedString_encode(v___f_1163_, v_s_1162_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___boxed(lean_object* v_s_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Std_Http_URI_EncodedUserInfo_encode(v_s_1165_);
lean_dec_ref(v_s_1165_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object* v_ba_1167_){
_start:
{
lean_object* v___f_1168_; lean_object* v___x_1169_; 
v___f_1168_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1169_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1168_, v_ba_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x21(lean_object* v_ba_1170_){
_start:
{
lean_object* v___f_1171_; lean_object* v___x_1172_; 
v___f_1171_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1172_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1171_, v_ba_1170_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode(lean_object* v_userInfo_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Std_Http_URI_EncodedString_decode___redArg(v_userInfo_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode___boxed(lean_object* v_userInfo_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Std_Http_URI_EncodedUserInfo_decode(v_userInfo_1175_);
lean_dec_ref(v_userInfo_1175_);
return v_res_1176_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryParam_encode___lam__0(uint8_t v___y_1177_){
_start:
{
uint8_t v___y_1186_; uint8_t v___y_1188_; uint8_t v___y_1194_; uint8_t v___y_1200_; uint8_t v___y_1220_; uint8_t v___y_1226_; uint8_t v___y_1232_; uint8_t v___y_1238_; uint8_t v___y_1244_; uint8_t v___x_1249_; uint8_t v___x_1250_; 
v___x_1249_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1250_ = lean_uint8_dec_le(v___x_1249_, v___y_1177_);
if (v___x_1250_ == 0)
{
v___y_1244_ = v___x_1250_;
goto v___jp_1243_;
}
else
{
uint8_t v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1252_ = lean_uint8_dec_le(v___y_1177_, v___x_1251_);
v___y_1244_ = v___x_1252_;
goto v___jp_1243_;
}
v___jp_1178_:
{
uint8_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1180_ = lean_uint8_dec_eq(v___y_1177_, v___x_1179_);
if (v___x_1180_ == 0)
{
uint8_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1182_ = lean_uint8_dec_eq(v___y_1177_, v___x_1181_);
if (v___x_1182_ == 0)
{
uint8_t v___x_1183_; 
v___x_1183_ = 1;
return v___x_1183_;
}
else
{
return v___x_1180_;
}
}
else
{
uint8_t v___x_1184_; 
v___x_1184_ = 0;
return v___x_1184_;
}
}
v___jp_1185_:
{
if (v___y_1186_ == 0)
{
return v___y_1186_;
}
else
{
goto v___jp_1178_;
}
}
v___jp_1187_:
{
if (v___y_1188_ == 0)
{
uint8_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0);
v___x_1190_ = lean_uint8_dec_eq(v___y_1177_, v___x_1189_);
if (v___x_1190_ == 0)
{
uint8_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1);
v___x_1192_ = lean_uint8_dec_eq(v___y_1177_, v___x_1191_);
v___y_1186_ = v___x_1192_;
goto v___jp_1185_;
}
else
{
v___y_1186_ = v___x_1190_;
goto v___jp_1185_;
}
}
else
{
goto v___jp_1178_;
}
}
v___jp_1193_:
{
if (v___y_1194_ == 0)
{
uint8_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_1196_ = lean_uint8_dec_eq(v___y_1177_, v___x_1195_);
if (v___x_1196_ == 0)
{
uint8_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_1198_ = lean_uint8_dec_eq(v___y_1177_, v___x_1197_);
v___y_1188_ = v___x_1198_;
goto v___jp_1187_;
}
else
{
v___y_1188_ = v___x_1196_;
goto v___jp_1187_;
}
}
else
{
goto v___jp_1178_;
}
}
v___jp_1199_:
{
if (v___y_1200_ == 0)
{
uint8_t v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1202_ = lean_uint8_dec_eq(v___y_1177_, v___x_1201_);
if (v___x_1202_ == 0)
{
uint8_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_1204_ = lean_uint8_dec_eq(v___y_1177_, v___x_1203_);
if (v___x_1204_ == 0)
{
uint8_t v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1206_ = lean_uint8_dec_eq(v___y_1177_, v___x_1205_);
if (v___x_1206_ == 0)
{
uint8_t v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1208_ = lean_uint8_dec_eq(v___y_1177_, v___x_1207_);
if (v___x_1208_ == 0)
{
uint8_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1210_ = lean_uint8_dec_eq(v___y_1177_, v___x_1209_);
if (v___x_1210_ == 0)
{
uint8_t v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1212_ = lean_uint8_dec_eq(v___y_1177_, v___x_1211_);
if (v___x_1212_ == 0)
{
uint8_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1214_ = lean_uint8_dec_eq(v___y_1177_, v___x_1213_);
if (v___x_1214_ == 0)
{
uint8_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1216_ = lean_uint8_dec_eq(v___y_1177_, v___x_1215_);
if (v___x_1216_ == 0)
{
uint8_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1218_ = lean_uint8_dec_eq(v___y_1177_, v___x_1217_);
v___y_1194_ = v___x_1218_;
goto v___jp_1193_;
}
else
{
v___y_1194_ = v___x_1216_;
goto v___jp_1193_;
}
}
else
{
v___y_1194_ = v___x_1214_;
goto v___jp_1193_;
}
}
else
{
v___y_1194_ = v___x_1212_;
goto v___jp_1193_;
}
}
else
{
v___y_1194_ = v___x_1210_;
goto v___jp_1193_;
}
}
else
{
v___y_1194_ = v___x_1208_;
goto v___jp_1193_;
}
}
else
{
v___y_1194_ = v___x_1206_;
goto v___jp_1193_;
}
}
else
{
v___y_1194_ = v___x_1204_;
goto v___jp_1193_;
}
}
else
{
v___y_1194_ = v___x_1202_;
goto v___jp_1193_;
}
}
else
{
goto v___jp_1178_;
}
}
v___jp_1219_:
{
if (v___y_1220_ == 0)
{
uint8_t v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1222_ = lean_uint8_dec_eq(v___y_1177_, v___x_1221_);
if (v___x_1222_ == 0)
{
uint8_t v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1224_ = lean_uint8_dec_eq(v___y_1177_, v___x_1223_);
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
goto v___jp_1178_;
}
}
v___jp_1225_:
{
if (v___y_1226_ == 0)
{
uint8_t v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1228_ = lean_uint8_dec_eq(v___y_1177_, v___x_1227_);
if (v___x_1228_ == 0)
{
uint8_t v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1230_ = lean_uint8_dec_eq(v___y_1177_, v___x_1229_);
v___y_1220_ = v___x_1230_;
goto v___jp_1219_;
}
else
{
v___y_1220_ = v___x_1228_;
goto v___jp_1219_;
}
}
else
{
goto v___jp_1178_;
}
}
v___jp_1231_:
{
if (v___y_1232_ == 0)
{
uint8_t v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1234_ = lean_uint8_dec_eq(v___y_1177_, v___x_1233_);
if (v___x_1234_ == 0)
{
uint8_t v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1236_ = lean_uint8_dec_eq(v___y_1177_, v___x_1235_);
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
goto v___jp_1178_;
}
}
v___jp_1237_:
{
if (v___y_1238_ == 0)
{
uint8_t v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1240_ = lean_uint8_dec_le(v___x_1239_, v___y_1177_);
if (v___x_1240_ == 0)
{
v___y_1232_ = v___x_1240_;
goto v___jp_1231_;
}
else
{
uint8_t v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1242_ = lean_uint8_dec_le(v___y_1177_, v___x_1241_);
v___y_1232_ = v___x_1242_;
goto v___jp_1231_;
}
}
else
{
goto v___jp_1178_;
}
}
v___jp_1243_:
{
if (v___y_1244_ == 0)
{
uint8_t v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1246_ = lean_uint8_dec_le(v___x_1245_, v___y_1177_);
if (v___x_1246_ == 0)
{
v___y_1238_ = v___x_1246_;
goto v___jp_1237_;
}
else
{
uint8_t v___x_1247_; uint8_t v___x_1248_; 
v___x_1247_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1248_ = lean_uint8_dec_le(v___y_1177_, v___x_1247_);
v___y_1238_ = v___x_1248_;
goto v___jp_1237_;
}
}
else
{
goto v___jp_1178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed(lean_object* v___y_1253_){
_start:
{
uint8_t v___y_362__boxed_1254_; uint8_t v_res_1255_; lean_object* v_r_1256_; 
v___y_362__boxed_1254_ = lean_unbox(v___y_1253_);
v_res_1255_ = l_Std_Http_URI_EncodedQueryParam_encode___lam__0(v___y_362__boxed_1254_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode(lean_object* v_s_1258_){
_start:
{
lean_object* v___f_1259_; lean_object* v___x_1260_; 
v___f_1259_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1260_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_1258_, v___f_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___boxed(lean_object* v_s_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Std_Http_URI_EncodedQueryParam_encode(v_s_1261_);
lean_dec_ref(v_s_1261_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f(lean_object* v_ba_1263_){
_start:
{
lean_object* v___f_1264_; lean_object* v___x_1265_; 
v___f_1264_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1265_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_1263_, v___f_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x21(lean_object* v_ba_1266_){
_start:
{
lean_object* v___f_1267_; lean_object* v___x_1268_; 
v___f_1267_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1268_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v_ba_1266_, v___f_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object* v_s_1269_){
_start:
{
lean_object* v___f_1270_; lean_object* v___x_1271_; 
v___f_1270_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1271_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_1269_, v___f_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f___boxed(lean_object* v_s_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_s_1272_);
lean_dec_ref(v_s_1272_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object* v_param_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_param_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode___boxed(lean_object* v_param_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Std_Http_URI_EncodedQueryParam_decode(v_param_1276_);
lean_dec_ref(v_param_1276_);
return v_res_1277_;
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
