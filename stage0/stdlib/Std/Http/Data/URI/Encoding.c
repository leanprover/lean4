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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_ByteArray_decEq___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ByteArray_hash___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_isEncodedChar(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_isEncodedChar___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___redArg();
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedString_instToString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_EncodedString_instToString___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedString_instToString___redArg___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedString_instToString___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg();
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg();
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteArray_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___redArg();
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteArray_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___redArg();
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___redArg();
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___redArg();
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___redArg();
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___redArg();
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___boxed(lean_object*);
static const lean_sarray_object l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_sarray_object) + 1, .m_other = 1, .m_tag = 248}, .m_size = 1, .m_capacity = 1, .m_data = {0}};
static const lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1;
static const lean_sarray_object l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_sarray_object) + 1, .m_other = 1, .m_tag = 248}, .m_size = 1, .m_capacity = 1, .m_data = {1}};
static const lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__2 = (const lean_object*)&l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3;
LEAN_EXPORT uint64_t l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___closed__0 = (const lean_object*)&l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg();
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Http_URI_isEncodedChar(lean_object* v_rule_1_, uint8_t v_c_2_){
_start:
{
uint8_t v___x_3_; uint8_t v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___y_8_; uint8_t v___y_12_; uint8_t v___x_25_; uint8_t v___x_26_; 
v___x_3_ = 128;
v___x_4_ = lean_uint8_dec_lt(v_c_2_, v___x_3_);
v___x_5_ = lean_box(v_c_2_);
v___x_6_ = lean_apply_1(v_rule_1_, v___x_5_);
v___x_25_ = 48;
v___x_26_ = lean_uint8_dec_le(v___x_25_, v_c_2_);
if (v___x_26_ == 0)
{
goto v___jp_20_;
}
else
{
uint8_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = 57;
v___x_28_ = lean_uint8_dec_le(v_c_2_, v___x_27_);
if (v___x_28_ == 0)
{
goto v___jp_20_;
}
else
{
v___y_12_ = v___x_28_;
goto v___jp_11_;
}
}
v___jp_7_:
{
uint8_t v___x_9_; 
v___x_9_ = lean_unbox(v___x_6_);
if (v___x_9_ == 0)
{
if (v___x_4_ == 0)
{
return v___x_4_;
}
else
{
return v___y_8_;
}
}
else
{
if (v___x_4_ == 0)
{
return v___x_4_;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = lean_unbox(v___x_6_);
return v___x_10_;
}
}
}
v___jp_11_:
{
if (v___y_12_ == 0)
{
uint8_t v___x_13_; uint8_t v___x_14_; 
v___x_13_ = 37;
v___x_14_ = lean_uint8_dec_eq(v_c_2_, v___x_13_);
v___y_8_ = v___x_14_;
goto v___jp_7_;
}
else
{
v___y_8_ = v___y_12_;
goto v___jp_7_;
}
}
v___jp_15_:
{
uint8_t v___x_16_; uint8_t v___x_17_; 
v___x_16_ = 65;
v___x_17_ = lean_uint8_dec_le(v___x_16_, v_c_2_);
if (v___x_17_ == 0)
{
v___y_12_ = v___x_17_;
goto v___jp_11_;
}
else
{
uint8_t v___x_18_; uint8_t v___x_19_; 
v___x_18_ = 70;
v___x_19_ = lean_uint8_dec_le(v_c_2_, v___x_18_);
v___y_12_ = v___x_19_;
goto v___jp_11_;
}
}
v___jp_20_:
{
uint8_t v___x_21_; uint8_t v___x_22_; 
v___x_21_ = 97;
v___x_22_ = lean_uint8_dec_le(v___x_21_, v_c_2_);
if (v___x_22_ == 0)
{
goto v___jp_15_;
}
else
{
uint8_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 102;
v___x_24_ = lean_uint8_dec_le(v_c_2_, v___x_23_);
if (v___x_24_ == 0)
{
goto v___jp_15_;
}
else
{
v___y_12_ = v___x_24_;
goto v___jp_11_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isEncodedChar___boxed(lean_object* v_rule_29_, lean_object* v_c_30_){
_start:
{
uint8_t v_c_boxed_31_; uint8_t v_res_32_; lean_object* v_r_33_; 
v_c_boxed_31_ = lean_unbox(v_c_30_);
v_res_32_ = l_Std_Http_URI_isEncodedChar(v_rule_29_, v_c_boxed_31_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isEncodedQueryChar(lean_object* v_rule_34_, uint8_t v_c_35_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = l_Std_Http_URI_isEncodedChar(v_rule_34_, v_c_35_);
if (v___x_36_ == 0)
{
uint8_t v___x_37_; uint8_t v___x_38_; 
v___x_37_ = 43;
v___x_38_ = lean_uint8_dec_eq(v_c_35_, v___x_37_);
return v___x_38_;
}
else
{
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isEncodedQueryChar___boxed(lean_object* v_rule_39_, lean_object* v_c_40_){
_start:
{
uint8_t v_c_boxed_41_; uint8_t v_res_42_; lean_object* v_r_43_; 
v_c_boxed_41_ = lean_unbox(v_c_40_);
v_res_42_ = l_Std_Http_URI_isEncodedQueryChar(v_rule_39_, v_c_boxed_41_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(lean_object* v_r_44_, uint8_t v___x_45_, uint8_t v_v_46_){
_start:
{
uint8_t v___x_47_; 
v___x_47_ = l_Std_Http_URI_isEncodedChar(v_r_44_, v_v_46_);
if (v___x_47_ == 0)
{
return v___x_45_;
}
else
{
uint8_t v___x_48_; 
v___x_48_ = 0;
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed(lean_object* v_r_49_, lean_object* v___x_50_, lean_object* v_v_51_){
_start:
{
uint8_t v___x_61__boxed_52_; uint8_t v_v_boxed_53_; uint8_t v_res_54_; lean_object* v_r_55_; 
v___x_61__boxed_52_ = lean_unbox(v___x_50_);
v_v_boxed_53_ = lean_unbox(v_v_51_);
v_res_54_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(v_r_49_, v___x_61__boxed_52_, v_v_boxed_53_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars(lean_object* v_r_75_, lean_object* v_s_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_77_ = lean_byte_array_data(v_s_76_);
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_array_get_size(v___x_77_);
v___x_80_ = ((lean_object*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9));
v___x_81_ = lean_nat_dec_lt(v___x_78_, v___x_79_);
if (v___x_81_ == 0)
{
uint8_t v___x_82_; 
lean_dec_ref(v___x_77_);
lean_dec_ref(v_r_75_);
v___x_82_ = 1;
return v___x_82_;
}
else
{
if (v___x_81_ == 0)
{
lean_dec_ref(v___x_77_);
lean_dec_ref(v_r_75_);
return v___x_81_;
}
else
{
lean_object* v___x_83_; lean_object* v___f_84_; size_t v___x_85_; size_t v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_83_ = lean_box(v___x_81_);
v___f_84_ = lean_alloc_closure((void*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed), 3, 2);
lean_closure_set(v___f_84_, 0, v_r_75_);
lean_closure_set(v___f_84_, 1, v___x_83_);
v___x_85_ = ((size_t)0ULL);
v___x_86_ = lean_usize_of_nat(v___x_79_);
v___x_87_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_80_, v___f_84_, v___x_77_, v___x_85_, v___x_86_);
v___x_88_ = lean_unbox(v___x_87_);
lean_dec(v___x_87_);
if (v___x_88_ == 0)
{
return v___x_81_;
}
else
{
uint8_t v___x_89_; 
v___x_89_ = 0;
return v___x_89_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___boxed(lean_object* v_r_90_, lean_object* v_s_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_90_, v_s_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(lean_object* v_r_94_, uint8_t v___x_95_, uint8_t v_v_96_){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = l_Std_Http_URI_isEncodedQueryChar(v_r_94_, v_v_96_);
if (v___x_97_ == 0)
{
return v___x_95_;
}
else
{
uint8_t v___x_98_; 
v___x_98_ = 0;
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed(lean_object* v_r_99_, lean_object* v___x_100_, lean_object* v_v_101_){
_start:
{
uint8_t v___x_61__boxed_102_; uint8_t v_v_boxed_103_; uint8_t v_res_104_; lean_object* v_r_105_; 
v___x_61__boxed_102_ = lean_unbox(v___x_100_);
v_v_boxed_103_ = lean_unbox(v_v_101_);
v_res_104_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(v_r_99_, v___x_61__boxed_102_, v_v_boxed_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(lean_object* v_r_106_, lean_object* v_s_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_108_ = lean_byte_array_data(v_s_107_);
v___x_109_ = lean_unsigned_to_nat(0u);
v___x_110_ = lean_array_get_size(v___x_108_);
v___x_111_ = ((lean_object*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9));
v___x_112_ = lean_nat_dec_lt(v___x_109_, v___x_110_);
if (v___x_112_ == 0)
{
uint8_t v___x_113_; 
lean_dec_ref(v___x_108_);
lean_dec_ref(v_r_106_);
v___x_113_ = 1;
return v___x_113_;
}
else
{
if (v___x_112_ == 0)
{
lean_dec_ref(v___x_108_);
lean_dec_ref(v_r_106_);
return v___x_112_;
}
else
{
lean_object* v___x_114_; lean_object* v___f_115_; size_t v___x_116_; size_t v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_114_ = lean_box(v___x_112_);
v___f_115_ = lean_alloc_closure((void*)(l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed), 3, 2);
lean_closure_set(v___f_115_, 0, v_r_106_);
lean_closure_set(v___f_115_, 1, v___x_114_);
v___x_116_ = ((size_t)0ULL);
v___x_117_ = lean_usize_of_nat(v___x_110_);
v___x_118_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_111_, v___f_115_, v___x_108_, v___x_116_, v___x_117_);
v___x_119_ = lean_unbox(v___x_118_);
lean_dec(v___x_118_);
if (v___x_119_ == 0)
{
return v___x_112_;
}
else
{
uint8_t v___x_120_; 
v___x_120_ = 0;
return v___x_120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___boxed(lean_object* v_r_121_, lean_object* v_s_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_121_, v_s_122_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(lean_object* v_ba_125_, lean_object* v_i_126_){
_start:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = lean_byte_array_size(v_ba_125_);
v___x_132_ = lean_nat_dec_lt(v_i_126_, v___x_131_);
if (v___x_132_ == 0)
{
uint8_t v___x_133_; 
lean_dec(v_i_126_);
v___x_133_ = 1;
return v___x_133_;
}
else
{
uint8_t v_c_134_; uint8_t v___x_135_; uint8_t v___x_136_; 
v_c_134_ = lean_byte_array_fget(v_ba_125_, v_i_126_);
v___x_135_ = 37;
v___x_136_ = lean_uint8_dec_eq(v_c_134_, v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = lean_nat_add(v_i_126_, v___x_137_);
lean_dec(v_i_126_);
v_i_126_ = v___x_138_;
goto _start;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_140_ = lean_unsigned_to_nat(2u);
v___x_141_ = lean_nat_add(v_i_126_, v___x_140_);
v___x_142_ = lean_nat_dec_lt(v___x_141_, v___x_131_);
if (v___x_142_ == 0)
{
lean_dec(v___x_141_);
lean_dec(v_i_126_);
return v___x_142_;
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v_d1_145_; uint8_t v_d2_146_; uint8_t v___x_172_; uint8_t v___x_173_; 
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = lean_nat_add(v_i_126_, v___x_143_);
v_d1_145_ = lean_byte_array_fget(v_ba_125_, v___x_144_);
lean_dec(v___x_144_);
v_d2_146_ = lean_byte_array_fget(v_ba_125_, v___x_141_);
lean_dec(v___x_141_);
v___x_172_ = 48;
v___x_173_ = lean_uint8_dec_le(v___x_172_, v_d1_145_);
if (v___x_173_ == 0)
{
goto v___jp_167_;
}
else
{
uint8_t v___x_174_; uint8_t v___x_175_; 
v___x_174_ = 57;
v___x_175_ = lean_uint8_dec_le(v_d1_145_, v___x_174_);
if (v___x_175_ == 0)
{
goto v___jp_167_;
}
else
{
goto v___jp_157_;
}
}
v___jp_147_:
{
uint8_t v___x_148_; uint8_t v___x_149_; 
v___x_148_ = 65;
v___x_149_ = lean_uint8_dec_le(v___x_148_, v_d2_146_);
if (v___x_149_ == 0)
{
lean_dec(v_i_126_);
return v___x_149_;
}
else
{
uint8_t v___x_150_; uint8_t v___x_151_; 
v___x_150_ = 70;
v___x_151_ = lean_uint8_dec_le(v_d2_146_, v___x_150_);
if (v___x_151_ == 0)
{
lean_dec(v_i_126_);
return v___x_151_;
}
else
{
goto v___jp_127_;
}
}
}
v___jp_152_:
{
uint8_t v___x_153_; uint8_t v___x_154_; 
v___x_153_ = 97;
v___x_154_ = lean_uint8_dec_le(v___x_153_, v_d2_146_);
if (v___x_154_ == 0)
{
goto v___jp_147_;
}
else
{
uint8_t v___x_155_; uint8_t v___x_156_; 
v___x_155_ = 102;
v___x_156_ = lean_uint8_dec_le(v_d2_146_, v___x_155_);
if (v___x_156_ == 0)
{
goto v___jp_147_;
}
else
{
goto v___jp_127_;
}
}
}
v___jp_157_:
{
uint8_t v___x_158_; uint8_t v___x_159_; 
v___x_158_ = 48;
v___x_159_ = lean_uint8_dec_le(v___x_158_, v_d2_146_);
if (v___x_159_ == 0)
{
goto v___jp_152_;
}
else
{
uint8_t v___x_160_; uint8_t v___x_161_; 
v___x_160_ = 57;
v___x_161_ = lean_uint8_dec_le(v_d2_146_, v___x_160_);
if (v___x_161_ == 0)
{
goto v___jp_152_;
}
else
{
goto v___jp_127_;
}
}
}
v___jp_162_:
{
uint8_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = 65;
v___x_164_ = lean_uint8_dec_le(v___x_163_, v_d1_145_);
if (v___x_164_ == 0)
{
lean_dec(v_i_126_);
return v___x_164_;
}
else
{
uint8_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = 70;
v___x_166_ = lean_uint8_dec_le(v_d1_145_, v___x_165_);
if (v___x_166_ == 0)
{
lean_dec(v_i_126_);
return v___x_166_;
}
else
{
goto v___jp_157_;
}
}
}
v___jp_167_:
{
uint8_t v___x_168_; uint8_t v___x_169_; 
v___x_168_ = 97;
v___x_169_ = lean_uint8_dec_le(v___x_168_, v_d1_145_);
if (v___x_169_ == 0)
{
goto v___jp_162_;
}
else
{
uint8_t v___x_170_; uint8_t v___x_171_; 
v___x_170_ = 102;
v___x_171_ = lean_uint8_dec_le(v_d1_145_, v___x_170_);
if (v___x_171_ == 0)
{
goto v___jp_162_;
}
else
{
goto v___jp_157_;
}
}
}
}
}
}
v___jp_127_:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(3u);
v___x_129_ = lean_nat_add(v_i_126_, v___x_128_);
lean_dec(v_i_126_);
v_i_126_ = v___x_129_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop___boxed(lean_object* v_ba_176_, lean_object* v_i_177_){
_start:
{
uint8_t v_res_178_; lean_object* v_r_179_; 
v_res_178_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_176_, v_i_177_);
lean_dec_ref(v_ba_176_);
v_r_179_ = lean_box(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidPercentEncoding(lean_object* v_ba_180_){
_start:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_180_, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidPercentEncoding___boxed(lean_object* v_ba_183_){
_start:
{
uint8_t v_res_184_; lean_object* v_r_185_; 
v_res_184_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_183_);
lean_dec_ref(v_ba_183_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_hexDigit(uint8_t v_n_186_){
_start:
{
uint8_t v___x_187_; uint8_t v___x_188_; 
v___x_187_ = 10;
v___x_188_ = lean_uint8_dec_lt(v_n_186_, v___x_187_);
if (v___x_188_ == 0)
{
uint8_t v___x_189_; uint8_t v___x_190_; uint8_t v___x_191_; 
v___x_189_ = lean_uint8_sub(v_n_186_, v___x_187_);
v___x_190_ = 65;
v___x_191_ = lean_uint8_add(v___x_189_, v___x_190_);
return v___x_191_;
}
else
{
uint8_t v___x_192_; uint8_t v___x_193_; 
v___x_192_ = 48;
v___x_193_ = lean_uint8_add(v_n_186_, v___x_192_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigit___boxed(lean_object* v_n_194_){
_start:
{
uint8_t v_n_boxed_195_; uint8_t v_res_196_; lean_object* v_r_197_; 
v_n_boxed_195_ = lean_unbox(v_n_194_);
v_res_196_ = l_Std_Http_URI_hexDigit(v_n_boxed_195_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f(uint8_t v_c_198_){
_start:
{
uint8_t v___x_221_; uint8_t v___x_222_; 
v___x_221_ = 48;
v___x_222_ = lean_uint8_dec_le(v___x_221_, v_c_198_);
if (v___x_222_ == 0)
{
goto v___jp_211_;
}
else
{
uint8_t v___x_223_; uint8_t v___x_224_; 
v___x_223_ = 57;
v___x_224_ = lean_uint8_dec_le(v_c_198_, v___x_223_);
if (v___x_224_ == 0)
{
goto v___jp_211_;
}
else
{
uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_uint8_sub(v_c_198_, v___x_221_);
v___x_226_ = lean_box(v___x_225_);
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
v___jp_199_:
{
uint8_t v___x_200_; uint8_t v___x_201_; 
v___x_200_ = 65;
v___x_201_ = lean_uint8_dec_le(v___x_200_, v_c_198_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; 
v___x_202_ = lean_box(0);
return v___x_202_;
}
else
{
uint8_t v___x_203_; uint8_t v___x_204_; 
v___x_203_ = 70;
v___x_204_ = lean_uint8_dec_le(v_c_198_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
v___x_205_ = lean_box(0);
return v___x_205_;
}
else
{
uint8_t v___x_206_; uint8_t v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_206_ = lean_uint8_sub(v_c_198_, v___x_200_);
v___x_207_ = 10;
v___x_208_ = lean_uint8_add(v___x_206_, v___x_207_);
v___x_209_ = lean_box(v___x_208_);
v___x_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
}
v___jp_211_:
{
uint8_t v___x_212_; uint8_t v___x_213_; 
v___x_212_ = 97;
v___x_213_ = lean_uint8_dec_le(v___x_212_, v_c_198_);
if (v___x_213_ == 0)
{
goto v___jp_199_;
}
else
{
uint8_t v___x_214_; uint8_t v___x_215_; 
v___x_214_ = 102;
v___x_215_ = lean_uint8_dec_le(v_c_198_, v___x_214_);
if (v___x_215_ == 0)
{
goto v___jp_199_;
}
else
{
uint8_t v___x_216_; uint8_t v___x_217_; uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_216_ = lean_uint8_sub(v_c_198_, v___x_212_);
v___x_217_ = 10;
v___x_218_ = lean_uint8_add(v___x_216_, v___x_217_);
v___x_219_ = lean_box(v___x_218_);
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f___boxed(lean_object* v_c_228_){
_start:
{
uint8_t v_c_boxed_229_; lean_object* v_res_230_; 
v_c_boxed_229_ = lean_unbox(v_c_228_);
v_res_230_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_c_boxed_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(lean_object* v_x_231_, uint8_t v_x_232_, lean_object* v_h__1_233_){
_start:
{
lean_object* v_data_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_data_234_ = lean_byte_array_data(v_x_231_);
v___x_235_ = lean_box(v_x_232_);
v___x_236_ = lean_apply_2(v_h__1_233_, v_data_234_, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg___boxed(lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_h__1_239_){
_start:
{
uint8_t v_x_17__boxed_240_; lean_object* v_res_241_; 
v_x_17__boxed_240_ = lean_unbox(v_x_238_);
v_res_241_ = l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(v_x_237_, v_x_17__boxed_240_, v_h__1_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(lean_object* v_motive_242_, lean_object* v_x_243_, uint8_t v_x_244_, lean_object* v_h__1_245_){
_start:
{
lean_object* v_data_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_data_246_ = lean_byte_array_data(v_x_243_);
v___x_247_ = lean_box(v_x_244_);
v___x_248_ = lean_apply_2(v_h__1_245_, v_data_246_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___boxed(lean_object* v_motive_249_, lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_h__1_252_){
_start:
{
uint8_t v_x_29__boxed_253_; lean_object* v_res_254_; 
v_x_29__boxed_253_ = lean_unbox(v_x_251_);
v_res_254_ = l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(v_motive_249_, v_x_250_, v_x_29__boxed_253_, v_h__1_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter___redArg(lean_object* v_x_255_, lean_object* v_x_256_, lean_object* v_h__1_257_, lean_object* v_h__2_258_){
_start:
{
if (lean_obj_tag(v_x_255_) == 0)
{
lean_object* v___x_259_; 
lean_dec(v_h__2_258_);
v___x_259_ = lean_apply_1(v_h__1_257_, v_x_256_);
return v___x_259_;
}
else
{
lean_object* v_head_260_; lean_object* v_tail_261_; lean_object* v___x_262_; 
lean_dec(v_h__1_257_);
v_head_260_ = lean_ctor_get(v_x_255_, 0);
lean_inc(v_head_260_);
v_tail_261_ = lean_ctor_get(v_x_255_, 1);
lean_inc(v_tail_261_);
lean_dec_ref_known(v_x_255_, 2);
v___x_262_ = lean_apply_3(v_h__2_258_, v_head_260_, v_tail_261_, v_x_256_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter(lean_object* v_motive_263_, lean_object* v_x_264_, lean_object* v_x_265_, lean_object* v_h__1_266_, lean_object* v_h__2_267_){
_start:
{
if (lean_obj_tag(v_x_264_) == 0)
{
lean_object* v___x_268_; 
lean_dec(v_h__2_267_);
v___x_268_ = lean_apply_1(v_h__1_266_, v_x_265_);
return v___x_268_;
}
else
{
lean_object* v_head_269_; lean_object* v_tail_270_; lean_object* v___x_271_; 
lean_dec(v_h__1_266_);
v_head_269_ = lean_ctor_get(v_x_264_, 0);
lean_inc(v_head_269_);
v_tail_270_ = lean_ctor_get(v_x_264_, 1);
lean_inc(v_tail_270_);
lean_dec_ref_known(v_x_264_, 2);
v___x_271_ = lean_apply_3(v_h__2_267_, v_head_269_, v_tail_270_, v_x_265_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___redArg(){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_ByteArray_empty;
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___redArg___boxed(lean_object* v___dummy_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Std_Http_URI_EncodedString_empty___redArg();
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty(lean_object* v_r_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_ByteArray_empty;
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___boxed(lean_object* v_r_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_Http_URI_EncodedString_empty(v_r_278_);
lean_dec_ref(v_r_278_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___redArg(){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_ByteArray_empty;
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___redArg___boxed(lean_object* v___dummy_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Std_Http_URI_EncodedString_instInhabited___redArg();
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited(lean_object* v_r_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_ByteArray_empty;
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___boxed(lean_object* v_r_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Std_Http_URI_EncodedString_instInhabited(v_r_286_);
lean_dec_ref(v_r_286_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(lean_object* v_s_288_, uint8_t v_c_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_byte_array_push(v_s_288_, v_c_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg___boxed(lean_object* v_s_291_, lean_object* v_c_292_){
_start:
{
uint8_t v_c_boxed_293_; lean_object* v_res_294_; 
v_c_boxed_293_ = lean_unbox(v_c_292_);
v_res_294_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(v_s_291_, v_c_boxed_293_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(lean_object* v_r_295_, lean_object* v_s_296_, uint8_t v_c_297_, lean_object* v_h_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = lean_byte_array_push(v_s_296_, v_c_297_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___boxed(lean_object* v_r_300_, lean_object* v_s_301_, lean_object* v_c_302_, lean_object* v_h_303_){
_start:
{
uint8_t v_c_boxed_304_; lean_object* v_res_305_; 
v_c_boxed_304_ = lean_unbox(v_c_302_);
v_res_305_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(v_r_300_, v_s_301_, v_c_boxed_304_, v_h_303_);
lean_dec_ref(v_r_300_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(uint8_t v_b_306_, lean_object* v_s_307_){
_start:
{
uint8_t v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; uint8_t v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; uint8_t v___x_315_; uint8_t v___x_316_; lean_object* v_ba_317_; 
v___x_308_ = 37;
v___x_309_ = lean_byte_array_push(v_s_307_, v___x_308_);
v___x_310_ = 4;
v___x_311_ = lean_uint8_shift_right(v_b_306_, v___x_310_);
v___x_312_ = l_Std_Http_URI_hexDigit(v___x_311_);
v___x_313_ = lean_byte_array_push(v___x_309_, v___x_312_);
v___x_314_ = 15;
v___x_315_ = lean_uint8_land(v_b_306_, v___x_314_);
v___x_316_ = l_Std_Http_URI_hexDigit(v___x_315_);
v_ba_317_ = lean_byte_array_push(v___x_313_, v___x_316_);
return v_ba_317_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg___boxed(lean_object* v_b_318_, lean_object* v_s_319_){
_start:
{
uint8_t v_b_boxed_320_; lean_object* v_res_321_; 
v_b_boxed_320_ = lean_unbox(v_b_318_);
v_res_321_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_boxed_320_, v_s_319_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(lean_object* v_r_322_, uint8_t v_b_323_, lean_object* v_s_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_323_, v_s_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___boxed(lean_object* v_r_326_, lean_object* v_b_327_, lean_object* v_s_328_){
_start:
{
uint8_t v_b_boxed_329_; lean_object* v_res_330_; 
v_b_boxed_329_ = lean_unbox(v_b_327_);
v_res_330_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(v_r_326_, v_b_boxed_329_, v_s_328_);
lean_dec_ref(v_r_326_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(lean_object* v_r_331_, lean_object* v_as_332_, size_t v_i_333_, size_t v_stop_334_, lean_object* v_b_335_){
_start:
{
lean_object* v___y_337_; uint8_t v___x_341_; 
v___x_341_ = lean_usize_dec_eq(v_i_333_, v_stop_334_);
if (v___x_341_ == 0)
{
uint8_t v___x_342_; uint8_t v___y_344_; uint8_t v___x_347_; uint8_t v___x_348_; 
v___x_342_ = lean_byte_array_uget(v_as_332_, v_i_333_);
v___x_347_ = 128;
v___x_348_ = lean_uint8_dec_lt(v___x_342_, v___x_347_);
if (v___x_348_ == 0)
{
v___y_344_ = v___x_348_;
goto v___jp_343_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_349_ = lean_box(v___x_342_);
lean_inc_ref(v_r_331_);
v___x_350_ = lean_apply_1(v_r_331_, v___x_349_);
v___x_351_ = lean_unbox(v___x_350_);
v___y_344_ = v___x_351_;
goto v___jp_343_;
}
v___jp_343_:
{
if (v___y_344_ == 0)
{
lean_object* v___x_345_; 
v___x_345_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_342_, v_b_335_);
v___y_337_ = v___x_345_;
goto v___jp_336_;
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_byte_array_push(v_b_335_, v___x_342_);
v___y_337_ = v___x_346_;
goto v___jp_336_;
}
}
}
else
{
lean_dec_ref(v_r_331_);
return v_b_335_;
}
v___jp_336_:
{
size_t v___x_338_; size_t v___x_339_; 
v___x_338_ = ((size_t)1ULL);
v___x_339_ = lean_usize_add(v_i_333_, v___x_338_);
v_i_333_ = v___x_339_;
v_b_335_ = v___y_337_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0___boxed(lean_object* v_r_352_, lean_object* v_as_353_, lean_object* v_i_354_, lean_object* v_stop_355_, lean_object* v_b_356_){
_start:
{
size_t v_i_boxed_357_; size_t v_stop_boxed_358_; lean_object* v_res_359_; 
v_i_boxed_357_ = lean_unbox_usize(v_i_354_);
lean_dec(v_i_354_);
v_stop_boxed_358_ = lean_unbox_usize(v_stop_355_);
lean_dec(v_stop_355_);
v_res_359_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_352_, v_as_353_, v_i_boxed_357_, v_stop_boxed_358_, v_b_356_);
lean_dec_ref(v_as_353_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode(lean_object* v_r_360_, lean_object* v_s_361_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_362_ = l_ByteArray_empty;
v___x_363_ = lean_string_to_utf8(v_s_361_);
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = lean_byte_array_size(v___x_363_);
v___x_366_ = lean_nat_dec_lt(v___x_364_, v___x_365_);
if (v___x_366_ == 0)
{
lean_dec_ref(v___x_363_);
lean_dec_ref(v_r_360_);
return v___x_362_;
}
else
{
uint8_t v___x_367_; 
v___x_367_ = lean_nat_dec_le(v___x_365_, v___x_365_);
if (v___x_367_ == 0)
{
if (v___x_366_ == 0)
{
lean_dec_ref(v___x_363_);
lean_dec_ref(v_r_360_);
return v___x_362_;
}
else
{
size_t v___x_368_; size_t v___x_369_; lean_object* v___x_370_; 
v___x_368_ = ((size_t)0ULL);
v___x_369_ = lean_usize_of_nat(v___x_365_);
v___x_370_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_360_, v___x_363_, v___x_368_, v___x_369_, v___x_362_);
lean_dec_ref(v___x_363_);
return v___x_370_;
}
}
else
{
size_t v___x_371_; size_t v___x_372_; lean_object* v___x_373_; 
v___x_371_ = ((size_t)0ULL);
v___x_372_ = lean_usize_of_nat(v___x_365_);
v___x_373_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_360_, v___x_363_, v___x_371_, v___x_372_, v___x_362_);
lean_dec_ref(v___x_363_);
return v___x_373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode___boxed(lean_object* v_r_374_, lean_object* v_s_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Std_Http_URI_EncodedString_encode(v_r_374_, v_s_375_);
lean_dec_ref(v_s_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x3f(lean_object* v_r_377_, lean_object* v_ba_378_){
_start:
{
uint8_t v___x_379_; 
lean_inc_ref(v_ba_378_);
v___x_379_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_377_, v_ba_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; 
lean_dec_ref(v_ba_378_);
v___x_380_ = lean_box(0);
return v___x_380_;
}
else
{
uint8_t v___x_381_; 
v___x_381_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_378_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; 
lean_dec_ref(v_ba_378_);
v___x_382_ = lean_box(0);
return v___x_382_;
}
else
{
lean_object* v___x_383_; 
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v_ba_378_);
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_384_){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = l_ByteArray_empty;
v___x_386_ = lean_panic_fn_borrowed(v___x_385_, v_msg_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(lean_object* v_r_387_, lean_object* v_msg_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v_msg_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_390_, lean_object* v_msg_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(v_r_390_, v_msg_391_);
lean_dec_ref(v_r_390_);
return v_res_392_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_396_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2));
v___x_397_ = lean_unsigned_to_nat(12u);
v___x_398_ = lean_unsigned_to_nat(320u);
v___x_399_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1));
v___x_400_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_401_ = l_mkPanicMessageWithDecl(v___x_400_, v___x_399_, v___x_398_, v___x_397_, v___x_396_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x21(lean_object* v_r_402_, lean_object* v_ba_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_402_, v_ba_403_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3, &l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3_once, _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3);
v___x_406_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v___x_405_);
return v___x_406_;
}
else
{
lean_object* v_val_407_; 
v_val_407_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_val_407_);
lean_dec_ref_known(v___x_404_, 1);
return v_val_407_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f(lean_object* v_r_408_, lean_object* v_s_409_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_string_to_utf8(v_s_409_);
v___x_411_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_408_, v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f___boxed(lean_object* v_r_412_, lean_object* v_s_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_Http_URI_EncodedString_ofString_x3f(v_r_412_, v_s_413_);
lean_dec_ref(v_s_413_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21(lean_object* v_r_415_, lean_object* v_s_416_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_string_to_utf8(v_s_416_);
v___x_418_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v_r_415_, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21___boxed(lean_object* v_r_419_, lean_object* v_s_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Std_Http_URI_EncodedString_ofString_x21(v_r_419_, v_s_420_);
lean_dec_ref(v_s_420_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg(lean_object* v_ba_422_){
_start:
{
lean_inc_ref(v_ba_422_);
return v_ba_422_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg___boxed(lean_object* v_ba_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_Http_URI_EncodedString_new___redArg(v_ba_423_);
lean_dec_ref(v_ba_423_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new(lean_object* v_r_425_, lean_object* v_ba_426_, lean_object* v_valid_427_, lean_object* v___validEncoding_428_){
_start:
{
lean_inc_ref(v_ba_426_);
return v_ba_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___boxed(lean_object* v_r_429_, lean_object* v_ba_430_, lean_object* v_valid_431_, lean_object* v___validEncoding_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_Http_URI_EncodedString_new(v_r_429_, v_ba_430_, v_valid_431_, v___validEncoding_432_);
lean_dec_ref(v_ba_430_);
lean_dec_ref(v_r_429_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg___lam__0(lean_object* v_es_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = lean_string_from_utf8_unchecked(v_es_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg(){
_start:
{
lean_object* v___f_438_; 
v___f_438_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instToString___redArg___closed__0));
return v___f_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg___boxed(lean_object* v___dummy_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Std_Http_URI_EncodedString_instToString___redArg();
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString(lean_object* v_r_441_){
_start:
{
lean_object* v___f_442_; 
v___f_442_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instToString___redArg___closed__0));
return v___f_442_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___boxed(lean_object* v_r_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Std_Http_URI_EncodedString_instToString(v_r_443_);
lean_dec_ref(v_r_443_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(lean_object* v_len_445_, lean_object* v_rawBytes_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_fst_448_; lean_object* v_snd_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_514_; 
v_fst_448_ = lean_ctor_get(v_a_447_, 0);
v_snd_449_ = lean_ctor_get(v_a_447_, 1);
v_isSharedCheck_514_ = !lean_is_exclusive(v_a_447_);
if (v_isSharedCheck_514_ == 0)
{
v___x_451_ = v_a_447_;
v_isShared_452_ = v_isSharedCheck_514_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_snd_449_);
lean_inc(v_fst_448_);
lean_dec(v_a_447_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_514_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
uint8_t v___x_453_; 
v___x_453_ = lean_nat_dec_lt(v_snd_449_, v_len_445_);
if (v___x_453_ == 0)
{
lean_object* v___x_455_; 
if (v_isShared_452_ == 0)
{
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_fst_448_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_snd_449_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
else
{
uint8_t v_percent_457_; uint8_t v___x_458_; uint8_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___y_463_; 
v_percent_457_ = 37;
v___x_458_ = lean_byte_array_fget(v_rawBytes_446_, v_snd_449_);
v___x_459_ = lean_uint8_dec_eq(v___x_458_, v_percent_457_);
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_nat_add(v_snd_449_, v___x_460_);
if (v___x_459_ == 0)
{
v___y_463_ = v___x_459_;
goto v___jp_462_;
}
else
{
uint8_t v___x_513_; 
v___x_513_ = lean_nat_dec_lt(v___x_461_, v_len_445_);
v___y_463_ = v___x_513_;
goto v___jp_462_;
}
v___jp_462_:
{
if (v___y_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_466_; 
lean_dec(v_snd_449_);
v___x_464_ = lean_byte_array_push(v_fst_448_, v___x_458_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_461_);
lean_ctor_set(v___x_451_, 0, v___x_464_);
v___x_466_ = v___x_451_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v___x_461_);
v___x_466_ = v_reuseFailAlloc_468_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
v_a_447_ = v___x_466_;
goto _start;
}
}
else
{
uint8_t v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_byte_array_fget(v_rawBytes_446_, v___x_461_);
lean_dec(v___x_461_);
v___x_470_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_469_);
if (lean_obj_tag(v___x_470_) == 1)
{
lean_object* v_val_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v_val_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_val_471_);
lean_dec_ref_known(v___x_470_, 1);
v___x_472_ = lean_unsigned_to_nat(2u);
v___x_473_ = lean_nat_add(v_snd_449_, v___x_472_);
v___x_474_ = lean_nat_dec_lt(v___x_473_, v_len_445_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
lean_dec(v_val_471_);
lean_dec(v_snd_449_);
v___x_475_ = lean_byte_array_push(v_fst_448_, v___x_458_);
v___x_476_ = lean_byte_array_push(v___x_475_, v___x_469_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_473_);
lean_ctor_set(v___x_451_, 0, v___x_476_);
v___x_478_ = v___x_451_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_473_);
v___x_478_ = v_reuseFailAlloc_480_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
v_a_447_ = v___x_478_;
goto _start;
}
}
else
{
uint8_t v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_byte_array_fget(v_rawBytes_446_, v___x_473_);
lean_dec(v___x_473_);
v___x_482_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_481_);
if (lean_obj_tag(v___x_482_) == 1)
{
lean_object* v_val_483_; uint8_t v___x_484_; uint8_t v___x_485_; uint8_t v___x_486_; uint8_t v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v_val_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_val_483_);
lean_dec_ref_known(v___x_482_, 1);
v___x_484_ = 4;
v___x_485_ = lean_unbox(v_val_471_);
lean_dec(v_val_471_);
v___x_486_ = lean_uint8_shift_left(v___x_485_, v___x_484_);
v___x_487_ = lean_unbox(v_val_483_);
lean_dec(v_val_483_);
v___x_488_ = lean_uint8_add(v___x_486_, v___x_487_);
v___x_489_ = lean_byte_array_push(v_fst_448_, v___x_488_);
v___x_490_ = lean_unsigned_to_nat(3u);
v___x_491_ = lean_nat_add(v_snd_449_, v___x_490_);
lean_dec(v_snd_449_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_491_);
lean_ctor_set(v___x_451_, 0, v___x_489_);
v___x_493_ = v___x_451_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_491_);
v___x_493_ = v_reuseFailAlloc_495_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
v_a_447_ = v___x_493_;
goto _start;
}
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
lean_dec(v___x_482_);
lean_dec(v_val_471_);
v___x_496_ = lean_byte_array_push(v_fst_448_, v___x_458_);
v___x_497_ = lean_byte_array_push(v___x_496_, v___x_469_);
v___x_498_ = lean_byte_array_push(v___x_497_, v___x_481_);
v___x_499_ = lean_unsigned_to_nat(3u);
v___x_500_ = lean_nat_add(v_snd_449_, v___x_499_);
lean_dec(v_snd_449_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_500_);
lean_ctor_set(v___x_451_, 0, v___x_498_);
v___x_502_ = v___x_451_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_500_);
v___x_502_ = v_reuseFailAlloc_504_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
v_a_447_ = v___x_502_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
lean_dec(v___x_470_);
v___x_505_ = lean_byte_array_push(v_fst_448_, v___x_458_);
v___x_506_ = lean_byte_array_push(v___x_505_, v___x_469_);
v___x_507_ = lean_unsigned_to_nat(2u);
v___x_508_ = lean_nat_add(v_snd_449_, v___x_507_);
lean_dec(v_snd_449_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_508_);
lean_ctor_set(v___x_451_, 0, v___x_506_);
v___x_510_ = v___x_451_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v___x_508_);
v___x_510_ = v_reuseFailAlloc_512_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
v_a_447_ = v___x_510_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg___boxed(lean_object* v_len_515_, lean_object* v_rawBytes_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_515_, v_rawBytes_516_, v_a_517_);
lean_dec_ref(v_rawBytes_516_);
lean_dec(v_len_515_);
return v_res_518_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0(void){
_start:
{
lean_object* v_i_519_; lean_object* v_decoded_520_; lean_object* v___x_521_; 
v_i_519_ = lean_unsigned_to_nat(0u);
v_decoded_520_ = l_ByteArray_empty;
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v_decoded_520_);
lean_ctor_set(v___x_521_, 1, v_i_519_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg(lean_object* v_es_522_){
_start:
{
lean_object* v_len_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v_fst_526_; uint8_t v___x_527_; 
v_len_523_ = lean_byte_array_size(v_es_522_);
v___x_524_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_525_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_523_, v_es_522_, v___x_524_);
v_fst_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_fst_526_);
lean_dec_ref(v___x_525_);
v___x_527_ = lean_string_validate_utf8(v_fst_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
lean_dec(v_fst_526_);
v___x_528_ = lean_box(0);
return v___x_528_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_string_from_utf8_unchecked(v_fst_526_);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg___boxed(lean_object* v_es_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_531_);
lean_dec_ref(v_es_531_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode(lean_object* v_r_533_, lean_object* v_es_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___boxed(lean_object* v_r_536_, lean_object* v_es_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_Http_URI_EncodedString_decode(v_r_536_, v_es_537_);
lean_dec_ref(v_es_537_);
lean_dec_ref(v_r_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(lean_object* v_len_539_, lean_object* v_rawBytes_540_, lean_object* v_inst_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_539_, v_rawBytes_540_, v_a_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___boxed(lean_object* v_len_544_, lean_object* v_rawBytes_545_, lean_object* v_inst_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(v_len_544_, v_rawBytes_545_, v_inst_546_, v_a_547_);
lean_dec_ref(v_rawBytes_545_);
lean_dec(v_len_544_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0(lean_object* v_es_549_, lean_object* v_n_550_){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = lean_string_from_utf8_unchecked(v_es_549_);
v___x_552_ = l_String_quote(v___x_551_);
v___x_553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0___boxed(lean_object* v_es_554_, lean_object* v_n_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0(v_es_554_, v_n_555_);
lean_dec(v_n_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg(){
_start:
{
lean_object* v___f_559_; 
v___f_559_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___boxed(lean_object* v___dummy_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_Http_URI_EncodedString_instRepr___redArg();
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr(lean_object* v_r_562_){
_start:
{
lean_object* v___f_563_; 
v___f_563_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
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
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___redArg(){
_start:
{
lean_object* v___f_568_; 
v___f_568_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___redArg___boxed(lean_object* v___dummy_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_Http_URI_EncodedString_instBEq___redArg();
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq(lean_object* v_r_571_){
_start:
{
lean_object* v___f_572_; 
v___f_572_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
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
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___redArg(){
_start:
{
lean_object* v___f_577_; 
v___f_577_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_577_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___redArg___boxed(lean_object* v___dummy_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_Http_URI_EncodedString_instHashable___redArg();
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable(lean_object* v_r_580_){
_start:
{
lean_object* v___f_581_; 
v___f_581_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_581_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___boxed(lean_object* v_r_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_Http_URI_EncodedString_instHashable(v_r_582_);
lean_dec_ref(v_r_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___redArg(){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_ByteArray_empty;
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___redArg___boxed(lean_object* v___dummy_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_Http_URI_EncodedQueryString_empty___redArg();
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty(lean_object* v_r_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_ByteArray_empty;
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___boxed(lean_object* v_r_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Std_Http_URI_EncodedQueryString_empty(v_r_590_);
lean_dec_ref(v_r_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___redArg(){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_ByteArray_empty;
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___redArg___boxed(lean_object* v___dummy_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_Http_URI_EncodedQueryString_instInhabited___redArg();
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited(lean_object* v_r_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_ByteArray_empty;
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___boxed(lean_object* v_r_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Std_Http_URI_EncodedQueryString_instInhabited(v_r_598_);
lean_dec_ref(v_r_598_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(lean_object* v_s_600_, uint8_t v_c_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = lean_byte_array_push(v_s_600_, v_c_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg___boxed(lean_object* v_s_603_, lean_object* v_c_604_){
_start:
{
uint8_t v_c_boxed_605_; lean_object* v_res_606_; 
v_c_boxed_605_ = lean_unbox(v_c_604_);
v_res_606_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(v_s_603_, v_c_boxed_605_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(lean_object* v_r_607_, lean_object* v_s_608_, uint8_t v_c_609_, lean_object* v_h_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = lean_byte_array_push(v_s_608_, v_c_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___boxed(lean_object* v_r_612_, lean_object* v_s_613_, lean_object* v_c_614_, lean_object* v_h_615_){
_start:
{
uint8_t v_c_boxed_616_; lean_object* v_res_617_; 
v_c_boxed_616_ = lean_unbox(v_c_614_);
v_res_617_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(v_r_612_, v_s_613_, v_c_boxed_616_, v_h_615_);
lean_dec_ref(v_r_612_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(lean_object* v_ba_618_, lean_object* v_r_619_){
_start:
{
uint8_t v___x_620_; 
lean_inc_ref(v_ba_618_);
v___x_620_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_619_, v_ba_618_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
lean_dec_ref(v_ba_618_);
v___x_621_ = lean_box(0);
return v___x_621_;
}
else
{
uint8_t v___x_622_; 
v___x_622_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_618_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
lean_dec_ref(v_ba_618_);
v___x_623_ = lean_box(0);
return v___x_623_;
}
else
{
lean_object* v___x_624_; 
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v_ba_618_);
return v___x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = l_ByteArray_empty;
v___x_627_ = lean_panic_fn_borrowed(v___x_626_, v_msg_625_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(lean_object* v_r_628_, lean_object* v_msg_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v_msg_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_631_, lean_object* v_msg_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(v_r_631_, v_msg_632_);
lean_dec_ref(v_r_631_);
return v_res_633_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_636_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1));
v___x_637_ = lean_unsigned_to_nat(12u);
v___x_638_ = lean_unsigned_to_nat(438u);
v___x_639_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0));
v___x_640_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_641_ = l_mkPanicMessageWithDecl(v___x_640_, v___x_639_, v___x_638_, v___x_637_, v___x_636_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(lean_object* v_ba_642_, lean_object* v_r_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_642_, v_r_643_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_obj_once(&l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2, &l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2_once, _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2);
v___x_646_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v___x_645_);
return v___x_646_;
}
else
{
lean_object* v_val_647_; 
v_val_647_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v___x_644_, 1);
return v_val_647_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f(lean_object* v_s_648_, lean_object* v_r_649_){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_string_to_utf8(v_s_648_);
v___x_651_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v___x_650_, v_r_649_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f___boxed(lean_object* v_s_652_, lean_object* v_r_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_652_, v_r_653_);
lean_dec_ref(v_s_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21(lean_object* v_s_655_, lean_object* v_r_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_string_to_utf8(v_s_655_);
v___x_658_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v___x_657_, v_r_656_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21___boxed(lean_object* v_s_659_, lean_object* v_r_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Std_Http_URI_EncodedQueryString_ofString_x21(v_s_659_, v_r_660_);
lean_dec_ref(v_s_659_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg(lean_object* v_ba_662_){
_start:
{
lean_inc_ref(v_ba_662_);
return v_ba_662_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg___boxed(lean_object* v_ba_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Std_Http_URI_EncodedQueryString_new___redArg(v_ba_663_);
lean_dec_ref(v_ba_663_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new(lean_object* v_r_665_, lean_object* v_ba_666_, lean_object* v_valid_667_, lean_object* v___validEncoding_668_){
_start:
{
lean_inc_ref(v_ba_666_);
return v_ba_666_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___boxed(lean_object* v_r_669_, lean_object* v_ba_670_, lean_object* v_valid_671_, lean_object* v___validEncoding_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_Http_URI_EncodedQueryString_new(v_r_669_, v_ba_670_, v_valid_671_, v___validEncoding_672_);
lean_dec_ref(v_ba_670_);
lean_dec_ref(v_r_669_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(uint8_t v_b_674_, lean_object* v_s_675_){
_start:
{
uint8_t v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; uint8_t v___x_679_; uint8_t v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; uint8_t v___x_683_; uint8_t v___x_684_; lean_object* v_ba_685_; 
v___x_676_ = 37;
v___x_677_ = lean_byte_array_push(v_s_675_, v___x_676_);
v___x_678_ = 4;
v___x_679_ = lean_uint8_shift_right(v_b_674_, v___x_678_);
v___x_680_ = l_Std_Http_URI_hexDigit(v___x_679_);
v___x_681_ = lean_byte_array_push(v___x_677_, v___x_680_);
v___x_682_ = 15;
v___x_683_ = lean_uint8_land(v_b_674_, v___x_682_);
v___x_684_ = l_Std_Http_URI_hexDigit(v___x_683_);
v_ba_685_ = lean_byte_array_push(v___x_681_, v___x_684_);
return v_ba_685_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg___boxed(lean_object* v_b_686_, lean_object* v_s_687_){
_start:
{
uint8_t v_b_boxed_688_; lean_object* v_res_689_; 
v_b_boxed_688_ = lean_unbox(v_b_686_);
v_res_689_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_boxed_688_, v_s_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(lean_object* v_r_690_, uint8_t v_b_691_, lean_object* v_s_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_691_, v_s_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___boxed(lean_object* v_r_694_, lean_object* v_b_695_, lean_object* v_s_696_){
_start:
{
uint8_t v_b_boxed_697_; lean_object* v_res_698_; 
v_b_boxed_697_ = lean_unbox(v_b_695_);
v_res_698_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(v_r_694_, v_b_boxed_697_, v_s_696_);
lean_dec_ref(v_r_694_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(lean_object* v_r_699_, lean_object* v_as_700_, size_t v_i_701_, size_t v_stop_702_, lean_object* v_b_703_){
_start:
{
lean_object* v___y_705_; uint8_t v___x_709_; 
v___x_709_ = lean_usize_dec_eq(v_i_701_, v_stop_702_);
if (v___x_709_ == 0)
{
uint8_t v___x_710_; uint8_t v___y_712_; uint8_t v___x_719_; uint8_t v___x_720_; 
v___x_710_ = lean_byte_array_uget(v_as_700_, v_i_701_);
v___x_719_ = 128;
v___x_720_ = lean_uint8_dec_lt(v___x_710_, v___x_719_);
if (v___x_720_ == 0)
{
v___y_712_ = v___x_720_;
goto v___jp_711_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_721_ = lean_box(v___x_710_);
lean_inc_ref(v_r_699_);
v___x_722_ = lean_apply_1(v_r_699_, v___x_721_);
v___x_723_ = lean_unbox(v___x_722_);
v___y_712_ = v___x_723_;
goto v___jp_711_;
}
v___jp_711_:
{
if (v___y_712_ == 0)
{
uint8_t v___x_713_; uint8_t v___x_714_; 
v___x_713_ = 32;
v___x_714_ = lean_uint8_dec_eq(v___x_710_, v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
v___x_715_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v___x_710_, v_b_703_);
v___y_705_ = v___x_715_;
goto v___jp_704_;
}
else
{
uint8_t v___x_716_; lean_object* v___x_717_; 
v___x_716_ = 43;
v___x_717_ = lean_byte_array_push(v_b_703_, v___x_716_);
v___y_705_ = v___x_717_;
goto v___jp_704_;
}
}
else
{
lean_object* v___x_718_; 
v___x_718_ = lean_byte_array_push(v_b_703_, v___x_710_);
v___y_705_ = v___x_718_;
goto v___jp_704_;
}
}
}
else
{
lean_dec_ref(v_r_699_);
return v_b_703_;
}
v___jp_704_:
{
size_t v___x_706_; size_t v___x_707_; 
v___x_706_ = ((size_t)1ULL);
v___x_707_ = lean_usize_add(v_i_701_, v___x_706_);
v_i_701_ = v___x_707_;
v_b_703_ = v___y_705_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___boxed(lean_object* v_r_724_, lean_object* v_as_725_, lean_object* v_i_726_, lean_object* v_stop_727_, lean_object* v_b_728_){
_start:
{
size_t v_i_boxed_729_; size_t v_stop_boxed_730_; lean_object* v_res_731_; 
v_i_boxed_729_ = lean_unbox_usize(v_i_726_);
lean_dec(v_i_726_);
v_stop_boxed_730_ = lean_unbox_usize(v_stop_727_);
lean_dec(v_stop_727_);
v_res_731_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_724_, v_as_725_, v_i_boxed_729_, v_stop_boxed_730_, v_b_728_);
lean_dec_ref(v_as_725_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode(lean_object* v_s_732_, lean_object* v_r_733_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_734_ = l_ByteArray_empty;
v___x_735_ = lean_string_to_utf8(v_s_732_);
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = lean_byte_array_size(v___x_735_);
v___x_738_ = lean_nat_dec_lt(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
lean_dec_ref(v___x_735_);
lean_dec_ref(v_r_733_);
return v___x_734_;
}
else
{
uint8_t v___x_739_; 
v___x_739_ = lean_nat_dec_le(v___x_737_, v___x_737_);
if (v___x_739_ == 0)
{
if (v___x_738_ == 0)
{
lean_dec_ref(v___x_735_);
lean_dec_ref(v_r_733_);
return v___x_734_;
}
else
{
size_t v___x_740_; size_t v___x_741_; lean_object* v___x_742_; 
v___x_740_ = ((size_t)0ULL);
v___x_741_ = lean_usize_of_nat(v___x_737_);
v___x_742_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_733_, v___x_735_, v___x_740_, v___x_741_, v___x_734_);
lean_dec_ref(v___x_735_);
return v___x_742_;
}
}
else
{
size_t v___x_743_; size_t v___x_744_; lean_object* v___x_745_; 
v___x_743_ = ((size_t)0ULL);
v___x_744_ = lean_usize_of_nat(v___x_737_);
v___x_745_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_733_, v___x_735_, v___x_743_, v___x_744_, v___x_734_);
lean_dec_ref(v___x_735_);
return v___x_745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode___boxed(lean_object* v_s_746_, lean_object* v_r_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_746_, v_r_747_);
lean_dec_ref(v_s_746_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___redArg(lean_object* v_es_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = lean_string_from_utf8_unchecked(v_es_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString(lean_object* v_r_751_, lean_object* v_es_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = lean_string_from_utf8_unchecked(v_es_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___boxed(lean_object* v_r_754_, lean_object* v_es_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_Http_URI_EncodedQueryString_toString(v_r_754_, v_es_755_);
lean_dec_ref(v_r_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(lean_object* v_len_757_, lean_object* v_rawBytes_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_fst_760_; lean_object* v_snd_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_836_; 
v_fst_760_ = lean_ctor_get(v_a_759_, 0);
v_snd_761_ = lean_ctor_get(v_a_759_, 1);
v_isSharedCheck_836_ = !lean_is_exclusive(v_a_759_);
if (v_isSharedCheck_836_ == 0)
{
v___x_763_ = v_a_759_;
v_isShared_764_ = v_isSharedCheck_836_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_snd_761_);
lean_inc(v_fst_760_);
lean_dec(v_a_759_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_836_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
uint8_t v___x_765_; 
v___x_765_ = lean_nat_dec_lt(v_snd_761_, v_len_757_);
if (v___x_765_ == 0)
{
lean_object* v___x_767_; 
if (v_isShared_764_ == 0)
{
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_fst_760_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_snd_761_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
else
{
uint8_t v_plus_769_; uint8_t v___x_770_; uint8_t v___x_771_; 
v_plus_769_ = 43;
v___x_770_ = lean_byte_array_fget(v_rawBytes_758_, v_snd_761_);
v___x_771_ = lean_uint8_dec_eq(v___x_770_, v_plus_769_);
if (v___x_771_ == 0)
{
uint8_t v_percent_772_; uint8_t v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___y_777_; 
v_percent_772_ = 37;
v___x_773_ = lean_uint8_dec_eq(v___x_770_, v_percent_772_);
v___x_774_ = lean_unsigned_to_nat(1u);
v___x_775_ = lean_nat_add(v_snd_761_, v___x_774_);
if (v___x_773_ == 0)
{
v___y_777_ = v___x_773_;
goto v___jp_776_;
}
else
{
uint8_t v___x_827_; 
v___x_827_ = lean_nat_dec_lt(v___x_775_, v_len_757_);
v___y_777_ = v___x_827_;
goto v___jp_776_;
}
v___jp_776_:
{
if (v___y_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_780_; 
lean_dec(v_snd_761_);
v___x_778_ = lean_byte_array_push(v_fst_760_, v___x_770_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v___x_775_);
lean_ctor_set(v___x_763_, 0, v___x_778_);
v___x_780_ = v___x_763_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v___x_775_);
v___x_780_ = v_reuseFailAlloc_782_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
v_a_759_ = v___x_780_;
goto _start;
}
}
else
{
uint8_t v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_byte_array_fget(v_rawBytes_758_, v___x_775_);
lean_dec(v___x_775_);
v___x_784_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_783_);
if (lean_obj_tag(v___x_784_) == 1)
{
lean_object* v_val_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_val_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_val_785_);
lean_dec_ref_known(v___x_784_, 1);
v___x_786_ = lean_unsigned_to_nat(2u);
v___x_787_ = lean_nat_add(v_snd_761_, v___x_786_);
v___x_788_ = lean_nat_dec_lt(v___x_787_, v_len_757_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
lean_dec(v_val_785_);
lean_dec(v_snd_761_);
v___x_789_ = lean_byte_array_push(v_fst_760_, v___x_770_);
v___x_790_ = lean_byte_array_push(v___x_789_, v___x_783_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v___x_787_);
lean_ctor_set(v___x_763_, 0, v___x_790_);
v___x_792_ = v___x_763_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_787_);
v___x_792_ = v_reuseFailAlloc_794_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
v_a_759_ = v___x_792_;
goto _start;
}
}
else
{
uint8_t v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_byte_array_fget(v_rawBytes_758_, v___x_787_);
lean_dec(v___x_787_);
v___x_796_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_795_);
if (lean_obj_tag(v___x_796_) == 1)
{
lean_object* v_val_797_; uint8_t v___x_798_; uint8_t v___x_799_; uint8_t v___x_800_; uint8_t v___x_801_; uint8_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v_val_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_val_797_);
lean_dec_ref_known(v___x_796_, 1);
v___x_798_ = 4;
v___x_799_ = lean_unbox(v_val_785_);
lean_dec(v_val_785_);
v___x_800_ = lean_uint8_shift_left(v___x_799_, v___x_798_);
v___x_801_ = lean_unbox(v_val_797_);
lean_dec(v_val_797_);
v___x_802_ = lean_uint8_add(v___x_800_, v___x_801_);
v___x_803_ = lean_byte_array_push(v_fst_760_, v___x_802_);
v___x_804_ = lean_unsigned_to_nat(3u);
v___x_805_ = lean_nat_add(v_snd_761_, v___x_804_);
lean_dec(v_snd_761_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v___x_805_);
lean_ctor_set(v___x_763_, 0, v___x_803_);
v___x_807_ = v___x_763_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_805_);
v___x_807_ = v_reuseFailAlloc_809_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
v_a_759_ = v___x_807_;
goto _start;
}
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
lean_dec(v___x_796_);
lean_dec(v_val_785_);
v___x_810_ = lean_byte_array_push(v_fst_760_, v___x_770_);
v___x_811_ = lean_byte_array_push(v___x_810_, v___x_783_);
v___x_812_ = lean_byte_array_push(v___x_811_, v___x_795_);
v___x_813_ = lean_unsigned_to_nat(3u);
v___x_814_ = lean_nat_add(v_snd_761_, v___x_813_);
lean_dec(v_snd_761_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v___x_814_);
lean_ctor_set(v___x_763_, 0, v___x_812_);
v___x_816_ = v___x_763_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_814_);
v___x_816_ = v_reuseFailAlloc_818_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
v_a_759_ = v___x_816_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
lean_dec(v___x_784_);
v___x_819_ = lean_byte_array_push(v_fst_760_, v___x_770_);
v___x_820_ = lean_byte_array_push(v___x_819_, v___x_783_);
v___x_821_ = lean_unsigned_to_nat(2u);
v___x_822_ = lean_nat_add(v_snd_761_, v___x_821_);
lean_dec(v_snd_761_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v___x_822_);
lean_ctor_set(v___x_763_, 0, v___x_820_);
v___x_824_ = v___x_763_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v___x_822_);
v___x_824_ = v_reuseFailAlloc_826_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
v_a_759_ = v___x_824_;
goto _start;
}
}
}
}
}
else
{
uint8_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_828_ = 32;
v___x_829_ = lean_byte_array_push(v_fst_760_, v___x_828_);
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = lean_nat_add(v_snd_761_, v___x_830_);
lean_dec(v_snd_761_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v___x_831_);
lean_ctor_set(v___x_763_, 0, v___x_829_);
v___x_833_ = v___x_763_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_831_);
v___x_833_ = v_reuseFailAlloc_835_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
v_a_759_ = v___x_833_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg___boxed(lean_object* v_len_837_, lean_object* v_rawBytes_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_837_, v_rawBytes_838_, v_a_839_);
lean_dec_ref(v_rawBytes_838_);
lean_dec(v_len_837_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg(lean_object* v_es_841_){
_start:
{
lean_object* v_len_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v_fst_845_; uint8_t v___x_846_; 
v_len_842_ = lean_byte_array_size(v_es_841_);
v___x_843_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_844_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_842_, v_es_841_, v___x_843_);
v_fst_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_fst_845_);
lean_dec_ref(v___x_844_);
v___x_846_ = lean_string_validate_utf8(v_fst_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
lean_dec(v_fst_845_);
v___x_847_ = lean_box(0);
return v___x_847_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_string_from_utf8_unchecked(v_fst_845_);
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg___boxed(lean_object* v_es_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_850_);
lean_dec_ref(v_es_850_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode(lean_object* v_r_852_, lean_object* v_es_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___boxed(lean_object* v_r_855_, lean_object* v_es_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Std_Http_URI_EncodedQueryString_decode(v_r_855_, v_es_856_);
lean_dec_ref(v_es_856_);
lean_dec_ref(v_r_855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(lean_object* v_len_858_, lean_object* v_rawBytes_859_, lean_object* v_inst_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_858_, v_rawBytes_859_, v_a_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___boxed(lean_object* v_len_863_, lean_object* v_rawBytes_864_, lean_object* v_inst_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(v_len_863_, v_rawBytes_864_, v_inst_865_, v_a_866_);
lean_dec_ref(v_rawBytes_864_);
lean_dec(v_len_863_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringEncodedQueryString(lean_object* v_r_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = lean_alloc_closure((void*)(l_Std_Http_URI_EncodedQueryString_toString___boxed), 2, 1);
lean_closure_set(v___x_869_, 0, v_r_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_871_; 
v___f_871_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_871_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___redArg___boxed(lean_object* v___dummy_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Std_Http_URI_instReprEncodedQueryString___redArg();
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString(lean_object* v_r_874_){
_start:
{
lean_object* v___f_875_; 
v___f_875_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_875_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___boxed(lean_object* v_r_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_Http_URI_instReprEncodedQueryString(v_r_876_);
lean_dec_ref(v_r_876_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_879_; 
v___f_879_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_879_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___redArg___boxed(lean_object* v___dummy_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Std_Http_URI_instBEqEncodedQueryString___redArg();
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString(lean_object* v_r_882_){
_start:
{
lean_object* v___f_883_; 
v___f_883_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_883_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___boxed(lean_object* v_r_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_Http_URI_instBEqEncodedQueryString(v_r_884_);
lean_dec_ref(v_r_884_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_887_; 
v___f_887_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_887_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___redArg___boxed(lean_object* v___dummy_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Std_Http_URI_instHashableEncodedQueryString___redArg();
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString(lean_object* v_r_890_){
_start:
{
lean_object* v___f_891_; 
v___f_891_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_891_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___boxed(lean_object* v_r_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_Http_URI_instHashableEncodedQueryString(v_r_892_);
lean_dec_ref(v_r_892_);
return v_res_893_;
}
}
static uint64_t _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_900_; uint64_t v___x_901_; 
v___x_900_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__0));
v___x_901_ = lean_byte_array_hash(v___x_900_);
return v___x_901_;
}
}
static lean_object* _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__2));
v___x_909_ = lean_byte_array_size(v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT uint64_t l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0(lean_object* v_x_910_){
_start:
{
if (lean_obj_tag(v_x_910_) == 0)
{
uint64_t v___x_911_; 
v___x_911_ = lean_uint64_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1, &l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1);
return v___x_911_;
}
else
{
lean_object* v_val_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; lean_object* v___x_918_; uint64_t v___x_919_; 
v_val_912_ = lean_ctor_get(v_x_910_, 0);
v___x_913_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__2));
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = lean_obj_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3, &l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3);
v___x_916_ = lean_byte_array_size(v_val_912_);
v___x_917_ = 0;
v___x_918_ = lean_byte_array_copy_slice(v_val_912_, v___x_914_, v___x_913_, v___x_915_, v___x_916_, v___x_917_);
v___x_919_ = lean_byte_array_hash(v___x_918_);
lean_dec_ref(v___x_918_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___boxed(lean_object* v_x_920_){
_start:
{
uint64_t v_res_921_; lean_object* v_r_922_; 
v_res_921_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0(v_x_920_);
lean_dec(v_x_920_);
v_r_922_ = lean_box_uint64(v_res_921_);
return v_r_922_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_925_; 
v___f_925_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___closed__0));
return v___f_925_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___boxed(lean_object* v___dummy_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg();
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString(lean_object* v_r_928_){
_start:
{
lean_object* v___f_929_; 
v___f_929_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___closed__0));
return v___f_929_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___boxed(lean_object* v_r_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Std_Http_URI_instHashableOptionEncodedQueryString(v_r_930_);
lean_dec_ref(v_r_930_);
return v_res_931_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0(uint8_t v___y_932_){
_start:
{
uint8_t v___x_978_; uint8_t v___x_979_; 
v___x_978_ = 48;
v___x_979_ = lean_uint8_dec_le(v___x_978_, v___y_932_);
if (v___x_979_ == 0)
{
goto v___jp_973_;
}
else
{
uint8_t v___x_980_; uint8_t v___x_981_; 
v___x_980_ = 57;
v___x_981_ = lean_uint8_dec_le(v___y_932_, v___x_980_);
if (v___x_981_ == 0)
{
goto v___jp_973_;
}
else
{
return v___x_981_;
}
}
v___jp_933_:
{
uint8_t v___x_934_; uint8_t v___x_935_; 
v___x_934_ = 45;
v___x_935_ = lean_uint8_dec_eq(v___y_932_, v___x_934_);
if (v___x_935_ == 0)
{
uint8_t v___x_936_; uint8_t v___x_937_; 
v___x_936_ = 46;
v___x_937_ = lean_uint8_dec_eq(v___y_932_, v___x_936_);
if (v___x_937_ == 0)
{
uint8_t v___x_938_; uint8_t v___x_939_; 
v___x_938_ = 95;
v___x_939_ = lean_uint8_dec_eq(v___y_932_, v___x_938_);
if (v___x_939_ == 0)
{
uint8_t v___x_940_; uint8_t v___x_941_; 
v___x_940_ = 126;
v___x_941_ = lean_uint8_dec_eq(v___y_932_, v___x_940_);
if (v___x_941_ == 0)
{
uint8_t v___x_942_; uint8_t v___x_943_; 
v___x_942_ = 33;
v___x_943_ = lean_uint8_dec_eq(v___y_932_, v___x_942_);
if (v___x_943_ == 0)
{
uint8_t v___x_944_; uint8_t v___x_945_; 
v___x_944_ = 36;
v___x_945_ = lean_uint8_dec_eq(v___y_932_, v___x_944_);
if (v___x_945_ == 0)
{
uint8_t v___x_946_; uint8_t v___x_947_; 
v___x_946_ = 38;
v___x_947_ = lean_uint8_dec_eq(v___y_932_, v___x_946_);
if (v___x_947_ == 0)
{
uint8_t v___x_948_; uint8_t v___x_949_; 
v___x_948_ = 39;
v___x_949_ = lean_uint8_dec_eq(v___y_932_, v___x_948_);
if (v___x_949_ == 0)
{
uint8_t v___x_950_; uint8_t v___x_951_; 
v___x_950_ = 40;
v___x_951_ = lean_uint8_dec_eq(v___y_932_, v___x_950_);
if (v___x_951_ == 0)
{
uint8_t v___x_952_; uint8_t v___x_953_; 
v___x_952_ = 41;
v___x_953_ = lean_uint8_dec_eq(v___y_932_, v___x_952_);
if (v___x_953_ == 0)
{
uint8_t v___x_954_; uint8_t v___x_955_; 
v___x_954_ = 42;
v___x_955_ = lean_uint8_dec_eq(v___y_932_, v___x_954_);
if (v___x_955_ == 0)
{
uint8_t v___x_956_; uint8_t v___x_957_; 
v___x_956_ = 43;
v___x_957_ = lean_uint8_dec_eq(v___y_932_, v___x_956_);
if (v___x_957_ == 0)
{
uint8_t v___x_958_; uint8_t v___x_959_; 
v___x_958_ = 44;
v___x_959_ = lean_uint8_dec_eq(v___y_932_, v___x_958_);
if (v___x_959_ == 0)
{
uint8_t v___x_960_; uint8_t v___x_961_; 
v___x_960_ = 59;
v___x_961_ = lean_uint8_dec_eq(v___y_932_, v___x_960_);
if (v___x_961_ == 0)
{
uint8_t v___x_962_; uint8_t v___x_963_; 
v___x_962_ = 61;
v___x_963_ = lean_uint8_dec_eq(v___y_932_, v___x_962_);
if (v___x_963_ == 0)
{
uint8_t v___x_964_; uint8_t v___x_965_; 
v___x_964_ = 58;
v___x_965_ = lean_uint8_dec_eq(v___y_932_, v___x_964_);
if (v___x_965_ == 0)
{
uint8_t v___x_966_; uint8_t v___x_967_; 
v___x_966_ = 64;
v___x_967_ = lean_uint8_dec_eq(v___y_932_, v___x_966_);
return v___x_967_;
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
else
{
return v___x_939_;
}
}
else
{
return v___x_937_;
}
}
else
{
return v___x_935_;
}
}
v___jp_968_:
{
uint8_t v___x_969_; uint8_t v___x_970_; 
v___x_969_ = 65;
v___x_970_ = lean_uint8_dec_le(v___x_969_, v___y_932_);
if (v___x_970_ == 0)
{
goto v___jp_933_;
}
else
{
uint8_t v___x_971_; uint8_t v___x_972_; 
v___x_971_ = 90;
v___x_972_ = lean_uint8_dec_le(v___y_932_, v___x_971_);
if (v___x_972_ == 0)
{
goto v___jp_933_;
}
else
{
return v___x_972_;
}
}
}
v___jp_973_:
{
uint8_t v___x_974_; uint8_t v___x_975_; 
v___x_974_ = 97;
v___x_975_ = lean_uint8_dec_le(v___x_974_, v___y_932_);
if (v___x_975_ == 0)
{
goto v___jp_968_;
}
else
{
uint8_t v___x_976_; uint8_t v___x_977_; 
v___x_976_ = 122;
v___x_977_ = lean_uint8_dec_le(v___y_932_, v___x_976_);
if (v___x_977_ == 0)
{
goto v___jp_968_;
}
else
{
return v___x_977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___lam__0___boxed(lean_object* v___y_982_){
_start:
{
uint8_t v___y_265__boxed_983_; uint8_t v_res_984_; lean_object* v_r_985_; 
v___y_265__boxed_983_ = lean_unbox(v___y_982_);
v_res_984_ = l_Std_Http_URI_EncodedSegment_encode___lam__0(v___y_265__boxed_983_);
v_r_985_ = lean_box(v_res_984_);
return v_r_985_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode(lean_object* v_s_987_){
_start:
{
lean_object* v___f_988_; lean_object* v___x_989_; 
v___f_988_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_989_ = l_Std_Http_URI_EncodedString_encode(v___f_988_, v_s_987_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___boxed(lean_object* v_s_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Std_Http_URI_EncodedSegment_encode(v_s_990_);
lean_dec_ref(v_s_990_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object* v_ba_992_){
_start:
{
lean_object* v___f_993_; lean_object* v___x_994_; 
v___f_993_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_994_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_993_, v_ba_992_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x21(lean_object* v_ba_995_){
_start:
{
lean_object* v___f_996_; lean_object* v___x_997_; 
v___f_996_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_997_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_996_, v_ba_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object* v_segment_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Std_Http_URI_EncodedString_decode___redArg(v_segment_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode___boxed(lean_object* v_segment_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Std_Http_URI_EncodedSegment_decode(v_segment_1000_);
lean_dec_ref(v_segment_1000_);
return v_res_1001_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedFragment_encode___lam__0(uint8_t v___y_1002_){
_start:
{
uint8_t v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = 48;
v___x_1053_ = lean_uint8_dec_le(v___x_1052_, v___y_1002_);
if (v___x_1053_ == 0)
{
goto v___jp_1047_;
}
else
{
uint8_t v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = 57;
v___x_1055_ = lean_uint8_dec_le(v___y_1002_, v___x_1054_);
if (v___x_1055_ == 0)
{
goto v___jp_1047_;
}
else
{
return v___x_1055_;
}
}
v___jp_1003_:
{
uint8_t v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = 45;
v___x_1005_ = lean_uint8_dec_eq(v___y_1002_, v___x_1004_);
if (v___x_1005_ == 0)
{
uint8_t v___x_1006_; uint8_t v___x_1007_; 
v___x_1006_ = 46;
v___x_1007_ = lean_uint8_dec_eq(v___y_1002_, v___x_1006_);
if (v___x_1007_ == 0)
{
uint8_t v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = 95;
v___x_1009_ = lean_uint8_dec_eq(v___y_1002_, v___x_1008_);
if (v___x_1009_ == 0)
{
uint8_t v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = 126;
v___x_1011_ = lean_uint8_dec_eq(v___y_1002_, v___x_1010_);
if (v___x_1011_ == 0)
{
uint8_t v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = 33;
v___x_1013_ = lean_uint8_dec_eq(v___y_1002_, v___x_1012_);
if (v___x_1013_ == 0)
{
uint8_t v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = 36;
v___x_1015_ = lean_uint8_dec_eq(v___y_1002_, v___x_1014_);
if (v___x_1015_ == 0)
{
uint8_t v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = 38;
v___x_1017_ = lean_uint8_dec_eq(v___y_1002_, v___x_1016_);
if (v___x_1017_ == 0)
{
uint8_t v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = 39;
v___x_1019_ = lean_uint8_dec_eq(v___y_1002_, v___x_1018_);
if (v___x_1019_ == 0)
{
uint8_t v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = 40;
v___x_1021_ = lean_uint8_dec_eq(v___y_1002_, v___x_1020_);
if (v___x_1021_ == 0)
{
uint8_t v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = 41;
v___x_1023_ = lean_uint8_dec_eq(v___y_1002_, v___x_1022_);
if (v___x_1023_ == 0)
{
uint8_t v___x_1024_; uint8_t v___x_1025_; 
v___x_1024_ = 42;
v___x_1025_ = lean_uint8_dec_eq(v___y_1002_, v___x_1024_);
if (v___x_1025_ == 0)
{
uint8_t v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = 43;
v___x_1027_ = lean_uint8_dec_eq(v___y_1002_, v___x_1026_);
if (v___x_1027_ == 0)
{
uint8_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = 44;
v___x_1029_ = lean_uint8_dec_eq(v___y_1002_, v___x_1028_);
if (v___x_1029_ == 0)
{
uint8_t v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = 59;
v___x_1031_ = lean_uint8_dec_eq(v___y_1002_, v___x_1030_);
if (v___x_1031_ == 0)
{
uint8_t v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = 61;
v___x_1033_ = lean_uint8_dec_eq(v___y_1002_, v___x_1032_);
if (v___x_1033_ == 0)
{
uint8_t v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = 58;
v___x_1035_ = lean_uint8_dec_eq(v___y_1002_, v___x_1034_);
if (v___x_1035_ == 0)
{
uint8_t v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = 64;
v___x_1037_ = lean_uint8_dec_eq(v___y_1002_, v___x_1036_);
if (v___x_1037_ == 0)
{
uint8_t v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = 47;
v___x_1039_ = lean_uint8_dec_eq(v___y_1002_, v___x_1038_);
if (v___x_1039_ == 0)
{
uint8_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = 63;
v___x_1041_ = lean_uint8_dec_eq(v___y_1002_, v___x_1040_);
return v___x_1041_;
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
else
{
return v___x_1013_;
}
}
else
{
return v___x_1011_;
}
}
else
{
return v___x_1009_;
}
}
else
{
return v___x_1007_;
}
}
else
{
return v___x_1005_;
}
}
v___jp_1042_:
{
uint8_t v___x_1043_; uint8_t v___x_1044_; 
v___x_1043_ = 65;
v___x_1044_ = lean_uint8_dec_le(v___x_1043_, v___y_1002_);
if (v___x_1044_ == 0)
{
goto v___jp_1003_;
}
else
{
uint8_t v___x_1045_; uint8_t v___x_1046_; 
v___x_1045_ = 90;
v___x_1046_ = lean_uint8_dec_le(v___y_1002_, v___x_1045_);
if (v___x_1046_ == 0)
{
goto v___jp_1003_;
}
else
{
return v___x_1046_;
}
}
}
v___jp_1047_:
{
uint8_t v___x_1048_; uint8_t v___x_1049_; 
v___x_1048_ = 97;
v___x_1049_ = lean_uint8_dec_le(v___x_1048_, v___y_1002_);
if (v___x_1049_ == 0)
{
goto v___jp_1042_;
}
else
{
uint8_t v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = 122;
v___x_1051_ = lean_uint8_dec_le(v___y_1002_, v___x_1050_);
if (v___x_1051_ == 0)
{
goto v___jp_1042_;
}
else
{
return v___x_1051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed(lean_object* v___y_1056_){
_start:
{
uint8_t v___y_289__boxed_1057_; uint8_t v_res_1058_; lean_object* v_r_1059_; 
v___y_289__boxed_1057_ = lean_unbox(v___y_1056_);
v_res_1058_ = l_Std_Http_URI_EncodedFragment_encode___lam__0(v___y_289__boxed_1057_);
v_r_1059_ = lean_box(v_res_1058_);
return v_r_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object* v_s_1061_){
_start:
{
lean_object* v___f_1062_; lean_object* v___x_1063_; 
v___f_1062_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1063_ = l_Std_Http_URI_EncodedString_encode(v___f_1062_, v_s_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___boxed(lean_object* v_s_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Std_Http_URI_EncodedFragment_encode(v_s_1064_);
lean_dec_ref(v_s_1064_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object* v_ba_1066_){
_start:
{
lean_object* v___f_1067_; lean_object* v___x_1068_; 
v___f_1067_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1068_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1067_, v_ba_1066_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x21(lean_object* v_ba_1069_){
_start:
{
lean_object* v___f_1070_; lean_object* v___x_1071_; 
v___f_1070_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1071_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1070_, v_ba_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object* v_fragment_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Std_Http_URI_EncodedString_decode___redArg(v_fragment_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode___boxed(lean_object* v_fragment_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Std_Http_URI_EncodedFragment_decode(v_fragment_1074_);
lean_dec_ref(v_fragment_1074_);
return v_res_1075_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedUserInfo_encode___lam__0(uint8_t v___y_1076_){
_start:
{
uint8_t v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = 48;
v___x_1121_ = lean_uint8_dec_le(v___x_1120_, v___y_1076_);
if (v___x_1121_ == 0)
{
goto v___jp_1115_;
}
else
{
uint8_t v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = 57;
v___x_1123_ = lean_uint8_dec_le(v___y_1076_, v___x_1122_);
if (v___x_1123_ == 0)
{
goto v___jp_1115_;
}
else
{
return v___x_1123_;
}
}
v___jp_1077_:
{
uint8_t v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = 45;
v___x_1079_ = lean_uint8_dec_eq(v___y_1076_, v___x_1078_);
if (v___x_1079_ == 0)
{
uint8_t v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = 46;
v___x_1081_ = lean_uint8_dec_eq(v___y_1076_, v___x_1080_);
if (v___x_1081_ == 0)
{
uint8_t v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = 95;
v___x_1083_ = lean_uint8_dec_eq(v___y_1076_, v___x_1082_);
if (v___x_1083_ == 0)
{
uint8_t v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = 126;
v___x_1085_ = lean_uint8_dec_eq(v___y_1076_, v___x_1084_);
if (v___x_1085_ == 0)
{
uint8_t v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = 33;
v___x_1087_ = lean_uint8_dec_eq(v___y_1076_, v___x_1086_);
if (v___x_1087_ == 0)
{
uint8_t v___x_1088_; uint8_t v___x_1089_; 
v___x_1088_ = 36;
v___x_1089_ = lean_uint8_dec_eq(v___y_1076_, v___x_1088_);
if (v___x_1089_ == 0)
{
uint8_t v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = 38;
v___x_1091_ = lean_uint8_dec_eq(v___y_1076_, v___x_1090_);
if (v___x_1091_ == 0)
{
uint8_t v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = 39;
v___x_1093_ = lean_uint8_dec_eq(v___y_1076_, v___x_1092_);
if (v___x_1093_ == 0)
{
uint8_t v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = 40;
v___x_1095_ = lean_uint8_dec_eq(v___y_1076_, v___x_1094_);
if (v___x_1095_ == 0)
{
uint8_t v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = 41;
v___x_1097_ = lean_uint8_dec_eq(v___y_1076_, v___x_1096_);
if (v___x_1097_ == 0)
{
uint8_t v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = 42;
v___x_1099_ = lean_uint8_dec_eq(v___y_1076_, v___x_1098_);
if (v___x_1099_ == 0)
{
uint8_t v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = 43;
v___x_1101_ = lean_uint8_dec_eq(v___y_1076_, v___x_1100_);
if (v___x_1101_ == 0)
{
uint8_t v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = 44;
v___x_1103_ = lean_uint8_dec_eq(v___y_1076_, v___x_1102_);
if (v___x_1103_ == 0)
{
uint8_t v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = 59;
v___x_1105_ = lean_uint8_dec_eq(v___y_1076_, v___x_1104_);
if (v___x_1105_ == 0)
{
uint8_t v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = 61;
v___x_1107_ = lean_uint8_dec_eq(v___y_1076_, v___x_1106_);
if (v___x_1107_ == 0)
{
uint8_t v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = 58;
v___x_1109_ = lean_uint8_dec_eq(v___y_1076_, v___x_1108_);
return v___x_1109_;
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
else
{
return v___x_1087_;
}
}
else
{
return v___x_1085_;
}
}
else
{
return v___x_1083_;
}
}
else
{
return v___x_1081_;
}
}
else
{
return v___x_1079_;
}
}
v___jp_1110_:
{
uint8_t v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = 65;
v___x_1112_ = lean_uint8_dec_le(v___x_1111_, v___y_1076_);
if (v___x_1112_ == 0)
{
goto v___jp_1077_;
}
else
{
uint8_t v___x_1113_; uint8_t v___x_1114_; 
v___x_1113_ = 90;
v___x_1114_ = lean_uint8_dec_le(v___y_1076_, v___x_1113_);
if (v___x_1114_ == 0)
{
goto v___jp_1077_;
}
else
{
return v___x_1114_;
}
}
}
v___jp_1115_:
{
uint8_t v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = 97;
v___x_1117_ = lean_uint8_dec_le(v___x_1116_, v___y_1076_);
if (v___x_1117_ == 0)
{
goto v___jp_1110_;
}
else
{
uint8_t v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = 122;
v___x_1119_ = lean_uint8_dec_le(v___y_1076_, v___x_1118_);
if (v___x_1119_ == 0)
{
goto v___jp_1110_;
}
else
{
return v___x_1119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed(lean_object* v___y_1124_){
_start:
{
uint8_t v___y_253__boxed_1125_; uint8_t v_res_1126_; lean_object* v_r_1127_; 
v___y_253__boxed_1125_ = lean_unbox(v___y_1124_);
v_res_1126_ = l_Std_Http_URI_EncodedUserInfo_encode___lam__0(v___y_253__boxed_1125_);
v_r_1127_ = lean_box(v_res_1126_);
return v_r_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object* v_s_1129_){
_start:
{
lean_object* v___f_1130_; lean_object* v___x_1131_; 
v___f_1130_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1131_ = l_Std_Http_URI_EncodedString_encode(v___f_1130_, v_s_1129_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___boxed(lean_object* v_s_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Std_Http_URI_EncodedUserInfo_encode(v_s_1132_);
lean_dec_ref(v_s_1132_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object* v_ba_1134_){
_start:
{
lean_object* v___f_1135_; lean_object* v___x_1136_; 
v___f_1135_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1136_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1135_, v_ba_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x21(lean_object* v_ba_1137_){
_start:
{
lean_object* v___f_1138_; lean_object* v___x_1139_; 
v___f_1138_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1139_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1138_, v_ba_1137_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode(lean_object* v_userInfo_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Std_Http_URI_EncodedString_decode___redArg(v_userInfo_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode___boxed(lean_object* v_userInfo_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Std_Http_URI_EncodedUserInfo_decode(v_userInfo_1142_);
lean_dec_ref(v_userInfo_1142_);
return v_res_1143_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryParam_encode___lam__0(uint8_t v___y_1144_){
_start:
{
uint8_t v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = 48;
v___x_1202_ = lean_uint8_dec_le(v___x_1201_, v___y_1144_);
if (v___x_1202_ == 0)
{
goto v___jp_1196_;
}
else
{
uint8_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = 57;
v___x_1204_ = lean_uint8_dec_le(v___y_1144_, v___x_1203_);
if (v___x_1204_ == 0)
{
goto v___jp_1196_;
}
else
{
goto v___jp_1145_;
}
}
v___jp_1145_:
{
uint8_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = 38;
v___x_1147_ = lean_uint8_dec_eq(v___y_1144_, v___x_1146_);
if (v___x_1147_ == 0)
{
uint8_t v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = 61;
v___x_1149_ = lean_uint8_dec_eq(v___y_1144_, v___x_1148_);
if (v___x_1149_ == 0)
{
uint8_t v___x_1150_; 
v___x_1150_ = 1;
return v___x_1150_;
}
else
{
return v___x_1147_;
}
}
else
{
uint8_t v___x_1151_; 
v___x_1151_ = 0;
return v___x_1151_;
}
}
v___jp_1152_:
{
uint8_t v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = 45;
v___x_1154_ = lean_uint8_dec_eq(v___y_1144_, v___x_1153_);
if (v___x_1154_ == 0)
{
uint8_t v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = 46;
v___x_1156_ = lean_uint8_dec_eq(v___y_1144_, v___x_1155_);
if (v___x_1156_ == 0)
{
uint8_t v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = 95;
v___x_1158_ = lean_uint8_dec_eq(v___y_1144_, v___x_1157_);
if (v___x_1158_ == 0)
{
uint8_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = 126;
v___x_1160_ = lean_uint8_dec_eq(v___y_1144_, v___x_1159_);
if (v___x_1160_ == 0)
{
uint8_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = 33;
v___x_1162_ = lean_uint8_dec_eq(v___y_1144_, v___x_1161_);
if (v___x_1162_ == 0)
{
uint8_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = 36;
v___x_1164_ = lean_uint8_dec_eq(v___y_1144_, v___x_1163_);
if (v___x_1164_ == 0)
{
uint8_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = 38;
v___x_1166_ = lean_uint8_dec_eq(v___y_1144_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint8_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = 39;
v___x_1168_ = lean_uint8_dec_eq(v___y_1144_, v___x_1167_);
if (v___x_1168_ == 0)
{
uint8_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = 40;
v___x_1170_ = lean_uint8_dec_eq(v___y_1144_, v___x_1169_);
if (v___x_1170_ == 0)
{
uint8_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = 41;
v___x_1172_ = lean_uint8_dec_eq(v___y_1144_, v___x_1171_);
if (v___x_1172_ == 0)
{
uint8_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = 42;
v___x_1174_ = lean_uint8_dec_eq(v___y_1144_, v___x_1173_);
if (v___x_1174_ == 0)
{
uint8_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = 43;
v___x_1176_ = lean_uint8_dec_eq(v___y_1144_, v___x_1175_);
if (v___x_1176_ == 0)
{
uint8_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = 44;
v___x_1178_ = lean_uint8_dec_eq(v___y_1144_, v___x_1177_);
if (v___x_1178_ == 0)
{
uint8_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = 59;
v___x_1180_ = lean_uint8_dec_eq(v___y_1144_, v___x_1179_);
if (v___x_1180_ == 0)
{
uint8_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = 61;
v___x_1182_ = lean_uint8_dec_eq(v___y_1144_, v___x_1181_);
if (v___x_1182_ == 0)
{
uint8_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = 58;
v___x_1184_ = lean_uint8_dec_eq(v___y_1144_, v___x_1183_);
if (v___x_1184_ == 0)
{
uint8_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = 64;
v___x_1186_ = lean_uint8_dec_eq(v___y_1144_, v___x_1185_);
if (v___x_1186_ == 0)
{
uint8_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = 47;
v___x_1188_ = lean_uint8_dec_eq(v___y_1144_, v___x_1187_);
if (v___x_1188_ == 0)
{
uint8_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = 63;
v___x_1190_ = lean_uint8_dec_eq(v___y_1144_, v___x_1189_);
if (v___x_1190_ == 0)
{
return v___x_1190_;
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
v___jp_1191_:
{
uint8_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = 65;
v___x_1193_ = lean_uint8_dec_le(v___x_1192_, v___y_1144_);
if (v___x_1193_ == 0)
{
goto v___jp_1152_;
}
else
{
uint8_t v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = 90;
v___x_1195_ = lean_uint8_dec_le(v___y_1144_, v___x_1194_);
if (v___x_1195_ == 0)
{
goto v___jp_1152_;
}
else
{
goto v___jp_1145_;
}
}
}
v___jp_1196_:
{
uint8_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = 97;
v___x_1198_ = lean_uint8_dec_le(v___x_1197_, v___y_1144_);
if (v___x_1198_ == 0)
{
goto v___jp_1191_;
}
else
{
uint8_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = 122;
v___x_1200_ = lean_uint8_dec_le(v___y_1144_, v___x_1199_);
if (v___x_1200_ == 0)
{
goto v___jp_1191_;
}
else
{
goto v___jp_1145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed(lean_object* v___y_1205_){
_start:
{
uint8_t v___y_363__boxed_1206_; uint8_t v_res_1207_; lean_object* v_r_1208_; 
v___y_363__boxed_1206_ = lean_unbox(v___y_1205_);
v_res_1207_ = l_Std_Http_URI_EncodedQueryParam_encode___lam__0(v___y_363__boxed_1206_);
v_r_1208_ = lean_box(v_res_1207_);
return v_r_1208_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode(lean_object* v_s_1210_){
_start:
{
lean_object* v___f_1211_; lean_object* v___x_1212_; 
v___f_1211_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1212_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_1210_, v___f_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___boxed(lean_object* v_s_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Std_Http_URI_EncodedQueryParam_encode(v_s_1213_);
lean_dec_ref(v_s_1213_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f(lean_object* v_ba_1215_){
_start:
{
lean_object* v___f_1216_; lean_object* v___x_1217_; 
v___f_1216_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1217_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_1215_, v___f_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x21(lean_object* v_ba_1218_){
_start:
{
lean_object* v___f_1219_; lean_object* v___x_1220_; 
v___f_1219_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1220_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v_ba_1218_, v___f_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object* v_s_1221_){
_start:
{
lean_object* v___f_1222_; lean_object* v___x_1223_; 
v___f_1222_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1223_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_1221_, v___f_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f___boxed(lean_object* v_s_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_s_1224_);
lean_dec_ref(v_s_1224_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object* v_param_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_param_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode___boxed(lean_object* v_param_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Std_Http_URI_EncodedQueryParam_decode(v_param_1228_);
lean_dec_ref(v_param_1228_);
return v_res_1229_;
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
