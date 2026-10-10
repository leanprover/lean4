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
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
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
uint8_t l_Std_Http_URI_isEncodedChar(lean_object* v_rule_1_, uint8_t v_c_2_){
_start:
{
uint8_t v___x_16_; uint8_t v___x_17_; 
v___x_16_ = 128;
v___x_17_ = lean_uint8_dec_lt(v_c_2_, v___x_16_);
if (v___x_17_ == 0)
{
lean_dec_ref(v_rule_1_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_18_ = lean_box(v_c_2_);
v___x_19_ = lean_apply_1(v_rule_1_, v___x_18_);
v___x_20_ = lean_unbox(v___x_19_);
if (v___x_20_ == 0)
{
uint8_t v___x_21_; uint8_t v___x_22_; 
v___x_21_ = 48;
v___x_22_ = lean_uint8_dec_le(v___x_21_, v_c_2_);
if (v___x_22_ == 0)
{
goto v___jp_11_;
}
else
{
uint8_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 57;
v___x_24_ = lean_uint8_dec_le(v_c_2_, v___x_23_);
if (v___x_24_ == 0)
{
goto v___jp_11_;
}
else
{
return v___x_24_;
}
}
}
else
{
uint8_t v___x_25_; 
v___x_25_ = lean_unbox(v___x_19_);
return v___x_25_;
}
}
v___jp_3_:
{
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = 37;
v___x_5_ = lean_uint8_dec_eq(v_c_2_, v___x_4_);
return v___x_5_;
}
v___jp_6_:
{
uint8_t v___x_7_; uint8_t v___x_8_; 
v___x_7_ = 65;
v___x_8_ = lean_uint8_dec_le(v___x_7_, v_c_2_);
if (v___x_8_ == 0)
{
goto v___jp_3_;
}
else
{
uint8_t v___x_9_; uint8_t v___x_10_; 
v___x_9_ = 70;
v___x_10_ = lean_uint8_dec_le(v_c_2_, v___x_9_);
if (v___x_10_ == 0)
{
goto v___jp_3_;
}
else
{
return v___x_10_;
}
}
}
v___jp_11_:
{
uint8_t v___x_12_; uint8_t v___x_13_; 
v___x_12_ = 97;
v___x_13_ = lean_uint8_dec_le(v___x_12_, v_c_2_);
if (v___x_13_ == 0)
{
goto v___jp_6_;
}
else
{
uint8_t v___x_14_; uint8_t v___x_15_; 
v___x_14_ = 102;
v___x_15_ = lean_uint8_dec_le(v_c_2_, v___x_14_);
if (v___x_15_ == 0)
{
goto v___jp_6_;
}
else
{
return v___x_15_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_isEncodedChar_0interp(lean_interpreter_value* stack)
{
lean_object* v_rule_1_ = stack[0].m_obj;
uint8_t v_c_2_ = stack[1].m_num;
uint8_t v_res_26_;
v_res_26_ = l_Std_Http_URI_isEncodedChar(v_rule_1_, v_c_2_);
stack->m_num = v_res_26_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isEncodedChar___boxed(lean_object* v_rule_27_, lean_object* v_c_28_){
_start:
{
uint8_t v_c_boxed_29_; uint8_t v_res_30_; lean_object* v_r_31_; 
v_c_boxed_29_ = lean_unbox(v_c_28_);
v_res_30_ = l_Std_Http_URI_isEncodedChar(v_rule_27_, v_c_boxed_29_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
uint8_t l_Std_Http_URI_isEncodedQueryChar(lean_object* v_rule_32_, uint8_t v_c_33_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = l_Std_Http_URI_isEncodedChar(v_rule_32_, v_c_33_);
if (v___x_34_ == 0)
{
uint8_t v___x_35_; uint8_t v___x_36_; 
v___x_35_ = 43;
v___x_36_ = lean_uint8_dec_eq(v_c_33_, v___x_35_);
return v___x_36_;
}
else
{
return v___x_34_;
}
}
}
LEAN_EXPORT void l_Std_Http_URI_isEncodedQueryChar_0interp(lean_interpreter_value* stack)
{
lean_object* v_rule_32_ = stack[0].m_obj;
uint8_t v_c_33_ = stack[1].m_num;
uint8_t v_res_37_;
v_res_37_ = l_Std_Http_URI_isEncodedQueryChar(v_rule_32_, v_c_33_);
stack->m_num = v_res_37_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isEncodedQueryChar___boxed(lean_object* v_rule_38_, lean_object* v_c_39_){
_start:
{
uint8_t v_c_boxed_40_; uint8_t v_res_41_; lean_object* v_r_42_; 
v_c_boxed_40_ = lean_unbox(v_c_39_);
v_res_41_ = l_Std_Http_URI_isEncodedQueryChar(v_rule_38_, v_c_boxed_40_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(lean_object* v_r_43_, uint8_t v___x_44_, uint8_t v_v_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = l_Std_Http_URI_isEncodedChar(v_r_43_, v_v_45_);
if (v___x_46_ == 0)
{
return v___x_44_;
}
else
{
uint8_t v___x_47_; 
v___x_47_ = 0;
return v___x_47_;
}
}
}
LEAN_EXPORT void l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_43_ = stack[0].m_obj;
uint8_t v___x_44_ = stack[1].m_num;
uint8_t v_v_45_ = stack[2].m_num;
uint8_t v_res_48_;
v_res_48_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(v_r_43_, v___x_44_, v_v_45_);
stack->m_num = v_res_48_;
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
uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars(lean_object* v_r_75_, lean_object* v_s_76_){
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
LEAN_EXPORT void l_Std_Http_URI_instDecidableIsAllowedEncodedChars_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_75_ = stack[0].m_obj;
lean_object* v_s_76_ = stack[1].m_obj;
uint8_t v_res_90_;
v_res_90_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_75_, v_s_76_);
stack->m_num = v_res_90_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___boxed(lean_object* v_r_91_, lean_object* v_s_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_91_, v_s_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(lean_object* v_r_95_, uint8_t v___x_96_, uint8_t v_v_97_){
_start:
{
uint8_t v___x_98_; 
v___x_98_ = l_Std_Http_URI_isEncodedQueryChar(v_r_95_, v_v_97_);
if (v___x_98_ == 0)
{
return v___x_96_;
}
else
{
uint8_t v___x_99_; 
v___x_99_ = 0;
return v___x_99_;
}
}
}
LEAN_EXPORT void l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_95_ = stack[0].m_obj;
uint8_t v___x_96_ = stack[1].m_num;
uint8_t v_v_97_ = stack[2].m_num;
uint8_t v_res_100_;
v_res_100_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(v_r_95_, v___x_96_, v_v_97_);
stack->m_num = v_res_100_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed(lean_object* v_r_101_, lean_object* v___x_102_, lean_object* v_v_103_){
_start:
{
uint8_t v___x_61__boxed_104_; uint8_t v_v_boxed_105_; uint8_t v_res_106_; lean_object* v_r_107_; 
v___x_61__boxed_104_ = lean_unbox(v___x_102_);
v_v_boxed_105_ = lean_unbox(v_v_103_);
v_res_106_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(v_r_101_, v___x_61__boxed_104_, v_v_boxed_105_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(lean_object* v_r_108_, lean_object* v_s_109_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_110_ = lean_byte_array_data(v_s_109_);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_array_get_size(v___x_110_);
v___x_113_ = ((lean_object*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9));
v___x_114_ = lean_nat_dec_lt(v___x_111_, v___x_112_);
if (v___x_114_ == 0)
{
uint8_t v___x_115_; 
lean_dec_ref(v___x_110_);
lean_dec_ref(v_r_108_);
v___x_115_ = 1;
return v___x_115_;
}
else
{
if (v___x_114_ == 0)
{
lean_dec_ref(v___x_110_);
lean_dec_ref(v_r_108_);
return v___x_114_;
}
else
{
lean_object* v___x_116_; lean_object* v___f_117_; size_t v___x_118_; size_t v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_116_ = lean_box(v___x_114_);
v___f_117_ = lean_alloc_closure((void*)(l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed), 3, 2);
lean_closure_set(v___f_117_, 0, v_r_108_);
lean_closure_set(v___f_117_, 1, v___x_116_);
v___x_118_ = ((size_t)0ULL);
v___x_119_ = lean_usize_of_nat(v___x_112_);
v___x_120_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_113_, v___f_117_, v___x_110_, v___x_118_, v___x_119_);
v___x_121_ = lean_unbox(v___x_120_);
lean_dec(v___x_120_);
if (v___x_121_ == 0)
{
return v___x_114_;
}
else
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_108_ = stack[0].m_obj;
lean_object* v_s_109_ = stack[1].m_obj;
uint8_t v_res_123_;
v_res_123_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_108_, v_s_109_);
stack->m_num = v_res_123_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___boxed(lean_object* v_r_124_, lean_object* v_s_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_124_, v_s_125_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
uint8_t l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(lean_object* v_ba_128_, lean_object* v_i_129_){
_start:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_byte_array_size(v_ba_128_);
v___x_135_ = lean_nat_dec_lt(v_i_129_, v___x_134_);
if (v___x_135_ == 0)
{
uint8_t v___x_136_; 
lean_dec(v_i_129_);
v___x_136_ = 1;
return v___x_136_;
}
else
{
uint8_t v_c_137_; uint8_t v___x_138_; uint8_t v___x_139_; 
v_c_137_ = lean_byte_array_fget(v_ba_128_, v_i_129_);
v___x_138_ = 37;
v___x_139_ = lean_uint8_dec_eq(v_c_137_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_add(v_i_129_, v___x_140_);
lean_dec(v_i_129_);
v_i_129_ = v___x_141_;
goto _start;
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_143_ = lean_unsigned_to_nat(2u);
v___x_144_ = lean_nat_add(v_i_129_, v___x_143_);
v___x_145_ = lean_nat_dec_lt(v___x_144_, v___x_134_);
if (v___x_145_ == 0)
{
lean_dec(v___x_144_);
lean_dec(v_i_129_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v_d1_148_; uint8_t v_d2_149_; uint8_t v___x_175_; uint8_t v___x_176_; 
v___x_146_ = lean_unsigned_to_nat(1u);
v___x_147_ = lean_nat_add(v_i_129_, v___x_146_);
v_d1_148_ = lean_byte_array_fget(v_ba_128_, v___x_147_);
lean_dec(v___x_147_);
v_d2_149_ = lean_byte_array_fget(v_ba_128_, v___x_144_);
lean_dec(v___x_144_);
v___x_175_ = 48;
v___x_176_ = lean_uint8_dec_le(v___x_175_, v_d1_148_);
if (v___x_176_ == 0)
{
goto v___jp_170_;
}
else
{
uint8_t v___x_177_; uint8_t v___x_178_; 
v___x_177_ = 57;
v___x_178_ = lean_uint8_dec_le(v_d1_148_, v___x_177_);
if (v___x_178_ == 0)
{
goto v___jp_170_;
}
else
{
goto v___jp_160_;
}
}
v___jp_150_:
{
uint8_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 65;
v___x_152_ = lean_uint8_dec_le(v___x_151_, v_d2_149_);
if (v___x_152_ == 0)
{
lean_dec(v_i_129_);
return v___x_152_;
}
else
{
uint8_t v___x_153_; uint8_t v___x_154_; 
v___x_153_ = 70;
v___x_154_ = lean_uint8_dec_le(v_d2_149_, v___x_153_);
if (v___x_154_ == 0)
{
lean_dec(v_i_129_);
return v___x_154_;
}
else
{
goto v___jp_130_;
}
}
}
v___jp_155_:
{
uint8_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = 97;
v___x_157_ = lean_uint8_dec_le(v___x_156_, v_d2_149_);
if (v___x_157_ == 0)
{
goto v___jp_150_;
}
else
{
uint8_t v___x_158_; uint8_t v___x_159_; 
v___x_158_ = 102;
v___x_159_ = lean_uint8_dec_le(v_d2_149_, v___x_158_);
if (v___x_159_ == 0)
{
goto v___jp_150_;
}
else
{
goto v___jp_130_;
}
}
}
v___jp_160_:
{
uint8_t v___x_161_; uint8_t v___x_162_; 
v___x_161_ = 48;
v___x_162_ = lean_uint8_dec_le(v___x_161_, v_d2_149_);
if (v___x_162_ == 0)
{
goto v___jp_155_;
}
else
{
uint8_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = 57;
v___x_164_ = lean_uint8_dec_le(v_d2_149_, v___x_163_);
if (v___x_164_ == 0)
{
goto v___jp_155_;
}
else
{
goto v___jp_130_;
}
}
}
v___jp_165_:
{
uint8_t v___x_166_; uint8_t v___x_167_; 
v___x_166_ = 65;
v___x_167_ = lean_uint8_dec_le(v___x_166_, v_d1_148_);
if (v___x_167_ == 0)
{
lean_dec(v_i_129_);
return v___x_167_;
}
else
{
uint8_t v___x_168_; uint8_t v___x_169_; 
v___x_168_ = 70;
v___x_169_ = lean_uint8_dec_le(v_d1_148_, v___x_168_);
if (v___x_169_ == 0)
{
lean_dec(v_i_129_);
return v___x_169_;
}
else
{
goto v___jp_160_;
}
}
}
v___jp_170_:
{
uint8_t v___x_171_; uint8_t v___x_172_; 
v___x_171_ = 97;
v___x_172_ = lean_uint8_dec_le(v___x_171_, v_d1_148_);
if (v___x_172_ == 0)
{
goto v___jp_165_;
}
else
{
uint8_t v___x_173_; uint8_t v___x_174_; 
v___x_173_ = 102;
v___x_174_ = lean_uint8_dec_le(v_d1_148_, v___x_173_);
if (v___x_174_ == 0)
{
goto v___jp_165_;
}
else
{
goto v___jp_160_;
}
}
}
}
}
}
v___jp_130_:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(3u);
v___x_132_ = lean_nat_add(v_i_129_, v___x_131_);
lean_dec(v_i_129_);
v_i_129_ = v___x_132_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_ba_128_ = stack[0].m_obj;
lean_object* v_i_129_ = stack[1].m_obj;
uint8_t v_res_179_;
v_res_179_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_128_, v_i_129_);
stack->m_num = v_res_179_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop___boxed(lean_object* v_ba_180_, lean_object* v_i_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_180_, v_i_181_);
lean_dec_ref(v_ba_180_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
uint8_t l_Std_Http_URI_isValidPercentEncoding(lean_object* v_ba_184_){
_start:
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_184_, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT void l_Std_Http_URI_isValidPercentEncoding_0interp(lean_interpreter_value* stack)
{
lean_object* v_ba_184_ = stack[0].m_obj;
uint8_t v_res_187_;
v_res_187_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_184_);
stack->m_num = v_res_187_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidPercentEncoding___boxed(lean_object* v_ba_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_188_);
lean_dec_ref(v_ba_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
uint8_t l_Std_Http_URI_hexDigit(uint8_t v_n_191_){
_start:
{
uint8_t v___x_192_; uint8_t v___x_193_; 
v___x_192_ = 10;
v___x_193_ = lean_uint8_dec_lt(v_n_191_, v___x_192_);
if (v___x_193_ == 0)
{
uint8_t v___x_194_; uint8_t v___x_195_; uint8_t v___x_196_; 
v___x_194_ = lean_uint8_sub(v_n_191_, v___x_192_);
v___x_195_ = 65;
v___x_196_ = lean_uint8_add(v___x_194_, v___x_195_);
return v___x_196_;
}
else
{
uint8_t v___x_197_; uint8_t v___x_198_; 
v___x_197_ = 48;
v___x_198_ = lean_uint8_add(v_n_191_, v___x_197_);
return v___x_198_;
}
}
}
LEAN_EXPORT void l_Std_Http_URI_hexDigit_0interp(lean_interpreter_value* stack)
{
uint8_t v_n_191_ = stack[0].m_num;
uint8_t v_res_199_;
v_res_199_ = l_Std_Http_URI_hexDigit(v_n_191_);
stack->m_num = v_res_199_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigit___boxed(lean_object* v_n_200_){
_start:
{
uint8_t v_n_boxed_201_; uint8_t v_res_202_; lean_object* v_r_203_; 
v_n_boxed_201_ = lean_unbox(v_n_200_);
v_res_202_ = l_Std_Http_URI_hexDigit(v_n_boxed_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f(uint8_t v_c_204_){
_start:
{
uint8_t v___x_227_; uint8_t v___x_228_; 
v___x_227_ = 48;
v___x_228_ = lean_uint8_dec_le(v___x_227_, v_c_204_);
if (v___x_228_ == 0)
{
goto v___jp_217_;
}
else
{
uint8_t v___x_229_; uint8_t v___x_230_; 
v___x_229_ = 57;
v___x_230_ = lean_uint8_dec_le(v_c_204_, v___x_229_);
if (v___x_230_ == 0)
{
goto v___jp_217_;
}
else
{
uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_uint8_sub(v_c_204_, v___x_227_);
v___x_232_ = lean_box(v___x_231_);
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
v___jp_205_:
{
uint8_t v___x_206_; uint8_t v___x_207_; 
v___x_206_ = 65;
v___x_207_ = lean_uint8_dec_le(v___x_206_, v_c_204_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
v___x_208_ = lean_box(0);
return v___x_208_;
}
else
{
uint8_t v___x_209_; uint8_t v___x_210_; 
v___x_209_ = 70;
v___x_210_ = lean_uint8_dec_le(v_c_204_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; 
v___x_211_ = lean_box(0);
return v___x_211_;
}
else
{
uint8_t v___x_212_; uint8_t v___x_213_; uint8_t v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_212_ = lean_uint8_sub(v_c_204_, v___x_206_);
v___x_213_ = 10;
v___x_214_ = lean_uint8_add(v___x_212_, v___x_213_);
v___x_215_ = lean_box(v___x_214_);
v___x_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
}
}
v___jp_217_:
{
uint8_t v___x_218_; uint8_t v___x_219_; 
v___x_218_ = 97;
v___x_219_ = lean_uint8_dec_le(v___x_218_, v_c_204_);
if (v___x_219_ == 0)
{
goto v___jp_205_;
}
else
{
uint8_t v___x_220_; uint8_t v___x_221_; 
v___x_220_ = 102;
v___x_221_ = lean_uint8_dec_le(v_c_204_, v___x_220_);
if (v___x_221_ == 0)
{
goto v___jp_205_;
}
else
{
uint8_t v___x_222_; uint8_t v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_222_ = lean_uint8_sub(v_c_204_, v___x_218_);
v___x_223_ = 10;
v___x_224_ = lean_uint8_add(v___x_222_, v___x_223_);
v___x_225_ = lean_box(v___x_224_);
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_hexDigitToUInt8_x3f_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_204_ = stack[0].m_num;
lean_object* v_res_234_;
v_res_234_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_c_204_);
stack->m_obj
 = v_res_234_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f___boxed(lean_object* v_c_235_){
_start:
{
uint8_t v_c_boxed_236_; lean_object* v_res_237_; 
v_c_boxed_236_ = lean_unbox(v_c_235_);
v_res_237_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_c_boxed_236_);
return v_res_237_;
}
}
lean_object* l_Std_Http_URI_EncodedString_empty___redArg(){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_ByteArray_empty;
return v___x_239_;
}
}
LEAN_EXPORT void l_Std_Http_URI_EncodedString_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_240_;
v_res_240_ = l_Std_Http_URI_EncodedString_empty___redArg();
stack->m_obj
 = v_res_240_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___redArg___boxed(lean_object* v___dummy_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_Http_URI_EncodedString_empty___redArg();
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty(lean_object* v_r_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_ByteArray_empty;
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___boxed(lean_object* v_r_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Std_Http_URI_EncodedString_empty(v_r_245_);
lean_dec_ref(v_r_245_);
return v_res_246_;
}
}
lean_object* l_Std_Http_URI_EncodedString_instInhabited___redArg(){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_ByteArray_empty;
return v___x_248_;
}
}
LEAN_EXPORT void l_Std_Http_URI_EncodedString_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_249_;
v_res_249_ = l_Std_Http_URI_EncodedString_instInhabited___redArg();
stack->m_obj
 = v_res_249_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___redArg___boxed(lean_object* v___dummy_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Std_Http_URI_EncodedString_instInhabited___redArg();
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited(lean_object* v_r_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_ByteArray_empty;
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___boxed(lean_object* v_r_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_Http_URI_EncodedString_instInhabited(v_r_254_);
lean_dec_ref(v_r_254_);
return v_res_255_;
}
}
lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(lean_object* v_s_256_, uint8_t v_c_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_byte_array_push(v_s_256_, v_c_257_);
return v___x_258_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_256_ = stack[0].m_obj;
uint8_t v_c_257_ = stack[1].m_num;
lean_object* v_res_259_;
v_res_259_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(v_s_256_, v_c_257_);
stack->m_obj
 = v_res_259_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg___boxed(lean_object* v_s_260_, lean_object* v_c_261_){
_start:
{
uint8_t v_c_boxed_262_; lean_object* v_res_263_; 
v_c_boxed_262_ = lean_unbox(v_c_261_);
v_res_263_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(v_s_260_, v_c_boxed_262_);
return v_res_263_;
}
}
lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(lean_object* v_r_264_, lean_object* v_s_265_, uint8_t v_c_266_, lean_object* v_h_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_byte_array_push(v_s_265_, v_c_266_);
return v___x_268_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_264_ = stack[0].m_obj;
lean_object* v_s_265_ = stack[1].m_obj;
uint8_t v_c_266_ = stack[2].m_num;
lean_object* v_res_269_;
v_res_269_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(v_r_264_, v_s_265_, v_c_266_, lean_box(0));
stack->m_obj
 = v_res_269_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___boxed(lean_object* v_r_270_, lean_object* v_s_271_, lean_object* v_c_272_, lean_object* v_h_273_){
_start:
{
uint8_t v_c_boxed_274_; lean_object* v_res_275_; 
v_c_boxed_274_ = lean_unbox(v_c_272_);
v_res_275_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(v_r_270_, v_s_271_, v_c_boxed_274_, v_h_273_);
lean_dec_ref(v_r_270_);
return v_res_275_;
}
}
lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(uint8_t v_b_276_, lean_object* v_s_277_){
_start:
{
uint8_t v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; uint8_t v___x_281_; uint8_t v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; uint8_t v___x_285_; uint8_t v___x_286_; lean_object* v_ba_287_; 
v___x_278_ = 37;
v___x_279_ = lean_byte_array_push(v_s_277_, v___x_278_);
v___x_280_ = 4;
v___x_281_ = lean_uint8_shift_right(v_b_276_, v___x_280_);
v___x_282_ = l_Std_Http_URI_hexDigit(v___x_281_);
v___x_283_ = lean_byte_array_push(v___x_279_, v___x_282_);
v___x_284_ = 15;
v___x_285_ = lean_uint8_land(v_b_276_, v___x_284_);
v___x_286_ = l_Std_Http_URI_hexDigit(v___x_285_);
v_ba_287_ = lean_byte_array_push(v___x_283_, v___x_286_);
return v_ba_287_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_276_ = stack[0].m_num;
lean_object* v_s_277_ = stack[1].m_obj;
lean_object* v_res_288_;
v_res_288_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_276_, v_s_277_);
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg___boxed(lean_object* v_b_289_, lean_object* v_s_290_){
_start:
{
uint8_t v_b_boxed_291_; lean_object* v_res_292_; 
v_b_boxed_291_ = lean_unbox(v_b_289_);
v_res_292_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_boxed_291_, v_s_290_);
return v_res_292_;
}
}
lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(lean_object* v_r_293_, uint8_t v_b_294_, lean_object* v_s_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_294_, v_s_295_);
return v___x_296_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_293_ = stack[0].m_obj;
uint8_t v_b_294_ = stack[1].m_num;
lean_object* v_s_295_ = stack[2].m_obj;
lean_object* v_res_297_;
v_res_297_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(v_r_293_, v_b_294_, v_s_295_);
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___boxed(lean_object* v_r_298_, lean_object* v_b_299_, lean_object* v_s_300_){
_start:
{
uint8_t v_b_boxed_301_; lean_object* v_res_302_; 
v_b_boxed_301_ = lean_unbox(v_b_299_);
v_res_302_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(v_r_298_, v_b_boxed_301_, v_s_300_);
lean_dec_ref(v_r_298_);
return v_res_302_;
}
}
lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(lean_object* v_r_303_, lean_object* v_as_304_, size_t v_i_305_, size_t v_stop_306_, lean_object* v_b_307_){
_start:
{
lean_object* v___y_309_; uint8_t v___x_313_; 
v___x_313_ = lean_usize_dec_eq(v_i_305_, v_stop_306_);
if (v___x_313_ == 0)
{
uint8_t v___x_314_; uint8_t v___x_315_; uint8_t v___x_316_; 
v___x_314_ = lean_byte_array_uget(v_as_304_, v_i_305_);
v___x_315_ = 128;
v___x_316_ = lean_uint8_dec_lt(v___x_314_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
v___x_317_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_314_, v_b_307_);
v___y_309_ = v___x_317_;
goto v___jp_308_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_318_ = lean_box(v___x_314_);
lean_inc_ref(v_r_303_);
v___x_319_ = lean_apply_1(v_r_303_, v___x_318_);
v___x_320_ = lean_unbox(v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; 
v___x_321_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_314_, v_b_307_);
v___y_309_ = v___x_321_;
goto v___jp_308_;
}
else
{
lean_object* v___x_322_; 
v___x_322_ = lean_byte_array_push(v_b_307_, v___x_314_);
v___y_309_ = v___x_322_;
goto v___jp_308_;
}
}
}
else
{
lean_dec_ref(v_r_303_);
return v_b_307_;
}
v___jp_308_:
{
size_t v___x_310_; size_t v___x_311_; 
v___x_310_ = ((size_t)1ULL);
v___x_311_ = lean_usize_add(v_i_305_, v___x_310_);
v_i_305_ = v___x_311_;
v_b_307_ = v___y_309_;
goto _start;
}
}
}
LEAN_EXPORT void l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_303_ = stack[0].m_obj;
lean_object* v_as_304_ = stack[1].m_obj;
size_t v_i_305_ = stack[2].m_num;
size_t v_stop_306_ = stack[3].m_num;
lean_object* v_b_307_ = stack[4].m_obj;
lean_object* v_res_323_;
v_res_323_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_303_, v_as_304_, v_i_305_, v_stop_306_, v_b_307_);
stack->m_obj
 = v_res_323_;
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0___boxed(lean_object* v_r_324_, lean_object* v_as_325_, lean_object* v_i_326_, lean_object* v_stop_327_, lean_object* v_b_328_){
_start:
{
size_t v_i_boxed_329_; size_t v_stop_boxed_330_; lean_object* v_res_331_; 
v_i_boxed_329_ = lean_unbox_usize(v_i_326_);
lean_dec(v_i_326_);
v_stop_boxed_330_ = lean_unbox_usize(v_stop_327_);
lean_dec(v_stop_327_);
v_res_331_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_324_, v_as_325_, v_i_boxed_329_, v_stop_boxed_330_, v_b_328_);
lean_dec_ref(v_as_325_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode(lean_object* v_r_332_, lean_object* v_s_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_334_ = l_ByteArray_empty;
v___x_335_ = lean_string_to_utf8(v_s_333_);
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = lean_byte_array_size(v___x_335_);
v___x_338_ = lean_nat_dec_lt(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_dec_ref(v___x_335_);
lean_dec_ref(v_r_332_);
return v___x_334_;
}
else
{
uint8_t v___x_339_; 
v___x_339_ = lean_nat_dec_le(v___x_337_, v___x_337_);
if (v___x_339_ == 0)
{
if (v___x_338_ == 0)
{
lean_dec_ref(v___x_335_);
lean_dec_ref(v_r_332_);
return v___x_334_;
}
else
{
size_t v___x_340_; size_t v___x_341_; lean_object* v___x_342_; 
v___x_340_ = ((size_t)0ULL);
v___x_341_ = lean_usize_of_nat(v___x_337_);
v___x_342_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_332_, v___x_335_, v___x_340_, v___x_341_, v___x_334_);
lean_dec_ref(v___x_335_);
return v___x_342_;
}
}
else
{
size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v___x_343_ = ((size_t)0ULL);
v___x_344_ = lean_usize_of_nat(v___x_337_);
v___x_345_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_332_, v___x_335_, v___x_343_, v___x_344_, v___x_334_);
lean_dec_ref(v___x_335_);
return v___x_345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode___boxed(lean_object* v_r_346_, lean_object* v_s_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_Http_URI_EncodedString_encode(v_r_346_, v_s_347_);
lean_dec_ref(v_s_347_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x3f(lean_object* v_r_349_, lean_object* v_ba_350_){
_start:
{
uint8_t v___x_351_; 
lean_inc_ref(v_ba_350_);
v___x_351_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_349_, v_ba_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
lean_dec_ref(v_ba_350_);
v___x_352_ = lean_box(0);
return v___x_352_;
}
else
{
uint8_t v___x_353_; 
v___x_353_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_350_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; 
lean_dec_ref(v_ba_350_);
v___x_354_ = lean_box(0);
return v___x_354_;
}
else
{
lean_object* v___x_355_; 
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v_ba_350_);
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_356_){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = l_ByteArray_empty;
v___x_358_ = lean_panic_fn_borrowed(v___x_357_, v_msg_356_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(lean_object* v_r_359_, lean_object* v_msg_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v_msg_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_362_, lean_object* v_msg_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(v_r_362_, v_msg_363_);
lean_dec_ref(v_r_362_);
return v_res_364_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_368_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2));
v___x_369_ = lean_unsigned_to_nat(12u);
v___x_370_ = lean_unsigned_to_nat(320u);
v___x_371_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1));
v___x_372_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_373_ = l_mkPanicMessageWithDecl(v___x_372_, v___x_371_, v___x_370_, v___x_369_, v___x_368_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x21(lean_object* v_r_374_, lean_object* v_ba_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_374_, v_ba_375_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_obj_once(&l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3, &l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3_once, _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3);
v___x_378_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v___x_377_);
return v___x_378_;
}
else
{
lean_object* v_val_379_; 
v_val_379_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_val_379_);
lean_dec_ref_known(v___x_376_, 1);
return v_val_379_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f(lean_object* v_r_380_, lean_object* v_s_381_){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_string_to_utf8(v_s_381_);
v___x_383_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_380_, v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f___boxed(lean_object* v_r_384_, lean_object* v_s_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Std_Http_URI_EncodedString_ofString_x3f(v_r_384_, v_s_385_);
lean_dec_ref(v_s_385_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21(lean_object* v_r_387_, lean_object* v_s_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_string_to_utf8(v_s_388_);
v___x_390_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v_r_387_, v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21___boxed(lean_object* v_r_391_, lean_object* v_s_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_Http_URI_EncodedString_ofString_x21(v_r_391_, v_s_392_);
lean_dec_ref(v_s_392_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg(lean_object* v_ba_394_){
_start:
{
lean_inc_ref(v_ba_394_);
return v_ba_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg___boxed(lean_object* v_ba_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Std_Http_URI_EncodedString_new___redArg(v_ba_395_);
lean_dec_ref(v_ba_395_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new(lean_object* v_r_397_, lean_object* v_ba_398_, lean_object* v_valid_399_, lean_object* v___validEncoding_400_){
_start:
{
lean_inc_ref(v_ba_398_);
return v_ba_398_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___boxed(lean_object* v_r_401_, lean_object* v_ba_402_, lean_object* v_valid_403_, lean_object* v___validEncoding_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_Http_URI_EncodedString_new(v_r_401_, v_ba_402_, v_valid_403_, v___validEncoding_404_);
lean_dec_ref(v_ba_402_);
lean_dec_ref(v_r_401_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg___lam__0(lean_object* v_es_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lean_string_from_utf8_unchecked(v_es_406_);
return v___x_407_;
}
}
lean_object* l_Std_Http_URI_EncodedString_instToString___redArg(){
_start:
{
lean_object* v___f_410_; 
v___f_410_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instToString___redArg___closed__0));
return v___f_410_;
}
}
LEAN_EXPORT void l_Std_Http_URI_EncodedString_instToString___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_411_;
v_res_411_ = l_Std_Http_URI_EncodedString_instToString___redArg();
stack->m_obj
 = v_res_411_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg___boxed(lean_object* v___dummy_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Std_Http_URI_EncodedString_instToString___redArg();
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString(lean_object* v_r_414_){
_start:
{
lean_object* v___f_415_; 
v___f_415_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instToString___redArg___closed__0));
return v___f_415_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___boxed(lean_object* v_r_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_Http_URI_EncodedString_instToString(v_r_416_);
lean_dec_ref(v_r_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(lean_object* v_len_418_, lean_object* v_rawBytes_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_fst_421_; lean_object* v_snd_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_480_; 
v_fst_421_ = lean_ctor_get(v_a_420_, 0);
v_snd_422_ = lean_ctor_get(v_a_420_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_a_420_);
if (v_isSharedCheck_480_ == 0)
{
v___x_424_ = v_a_420_;
v_isShared_425_ = v_isSharedCheck_480_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_snd_422_);
lean_inc(v_fst_421_);
lean_dec(v_a_420_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_480_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
uint8_t v___x_426_; 
v___x_426_ = lean_nat_dec_lt(v_snd_422_, v_len_418_);
if (v___x_426_ == 0)
{
lean_object* v___x_428_; 
if (v_isShared_425_ == 0)
{
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_fst_421_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_snd_422_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
else
{
uint8_t v_percent_430_; uint8_t v___x_431_; uint8_t v___x_440_; 
v_percent_430_ = 37;
v___x_431_ = lean_byte_array_fget(v_rawBytes_419_, v_snd_422_);
v___x_440_ = lean_uint8_dec_eq(v___x_431_, v_percent_430_);
if (v___x_440_ == 0)
{
goto v___jp_432_;
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = lean_nat_add(v_snd_422_, v___x_441_);
v___x_443_ = lean_nat_dec_lt(v___x_442_, v_len_418_);
if (v___x_443_ == 0)
{
lean_dec(v___x_442_);
goto v___jp_432_;
}
else
{
uint8_t v___x_444_; lean_object* v___x_445_; 
lean_del_object(v___x_424_);
v___x_444_ = lean_byte_array_fget(v_rawBytes_419_, v___x_442_);
lean_dec(v___x_442_);
v___x_445_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_444_);
if (lean_obj_tag(v___x_445_) == 1)
{
lean_object* v_val_446_; lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_val_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v___x_445_, 1);
v___x_447_ = lean_unsigned_to_nat(2u);
v___x_448_ = lean_nat_add(v_snd_422_, v___x_447_);
v___x_449_ = lean_nat_dec_lt(v___x_448_, v_len_418_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec(v_val_446_);
lean_dec(v_snd_422_);
v___x_450_ = lean_byte_array_push(v_fst_421_, v___x_431_);
v___x_451_ = lean_byte_array_push(v___x_450_, v___x_444_);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v___x_448_);
v_a_420_ = v___x_452_;
goto _start;
}
else
{
uint8_t v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_byte_array_fget(v_rawBytes_419_, v___x_448_);
lean_dec(v___x_448_);
v___x_455_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_454_);
if (lean_obj_tag(v___x_455_) == 1)
{
lean_object* v_val_456_; uint8_t v___x_457_; uint8_t v___x_458_; uint8_t v___x_459_; uint8_t v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_val_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_val_456_);
lean_dec_ref_known(v___x_455_, 1);
v___x_457_ = 4;
v___x_458_ = lean_unbox(v_val_446_);
lean_dec(v_val_446_);
v___x_459_ = lean_uint8_shift_left(v___x_458_, v___x_457_);
v___x_460_ = lean_unbox(v_val_456_);
lean_dec(v_val_456_);
v___x_461_ = lean_uint8_add(v___x_459_, v___x_460_);
v___x_462_ = lean_byte_array_push(v_fst_421_, v___x_461_);
v___x_463_ = lean_unsigned_to_nat(3u);
v___x_464_ = lean_nat_add(v_snd_422_, v___x_463_);
lean_dec(v_snd_422_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_462_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v_a_420_ = v___x_465_;
goto _start;
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec(v___x_455_);
lean_dec(v_val_446_);
v___x_467_ = lean_byte_array_push(v_fst_421_, v___x_431_);
v___x_468_ = lean_byte_array_push(v___x_467_, v___x_444_);
v___x_469_ = lean_byte_array_push(v___x_468_, v___x_454_);
v___x_470_ = lean_unsigned_to_nat(3u);
v___x_471_ = lean_nat_add(v_snd_422_, v___x_470_);
lean_dec(v_snd_422_);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_469_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v_a_420_ = v___x_472_;
goto _start;
}
}
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v___x_445_);
v___x_474_ = lean_byte_array_push(v_fst_421_, v___x_431_);
v___x_475_ = lean_byte_array_push(v___x_474_, v___x_444_);
v___x_476_ = lean_unsigned_to_nat(2u);
v___x_477_ = lean_nat_add(v_snd_422_, v___x_476_);
lean_dec(v_snd_422_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_475_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v_a_420_ = v___x_478_;
goto _start;
}
}
}
v___jp_432_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_433_ = lean_byte_array_push(v_fst_421_, v___x_431_);
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = lean_nat_add(v_snd_422_, v___x_434_);
lean_dec(v_snd_422_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 1, v___x_435_);
lean_ctor_set(v___x_424_, 0, v___x_433_);
v___x_437_ = v___x_424_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v___x_435_);
v___x_437_ = v_reuseFailAlloc_439_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
v_a_420_ = v___x_437_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg___boxed(lean_object* v_len_481_, lean_object* v_rawBytes_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_481_, v_rawBytes_482_, v_a_483_);
lean_dec_ref(v_rawBytes_482_);
lean_dec(v_len_481_);
return v_res_484_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0(void){
_start:
{
lean_object* v_i_485_; lean_object* v_decoded_486_; lean_object* v___x_487_; 
v_i_485_ = lean_unsigned_to_nat(0u);
v_decoded_486_ = l_ByteArray_empty;
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v_decoded_486_);
lean_ctor_set(v___x_487_, 1, v_i_485_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg(lean_object* v_es_488_){
_start:
{
lean_object* v_len_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v_fst_492_; uint8_t v___x_493_; 
v_len_489_ = lean_byte_array_size(v_es_488_);
v___x_490_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_491_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_489_, v_es_488_, v___x_490_);
v_fst_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_fst_492_);
lean_dec_ref(v___x_491_);
v___x_493_ = lean_string_validate_utf8(v_fst_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
lean_dec(v_fst_492_);
v___x_494_ = lean_box(0);
return v___x_494_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_string_from_utf8_unchecked(v_fst_492_);
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg___boxed(lean_object* v_es_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_497_);
lean_dec_ref(v_es_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode(lean_object* v_r_499_, lean_object* v_es_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___boxed(lean_object* v_r_502_, lean_object* v_es_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Std_Http_URI_EncodedString_decode(v_r_502_, v_es_503_);
lean_dec_ref(v_es_503_);
lean_dec_ref(v_r_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(lean_object* v_len_505_, lean_object* v_rawBytes_506_, lean_object* v_inst_507_, lean_object* v_a_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_505_, v_rawBytes_506_, v_a_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___boxed(lean_object* v_len_510_, lean_object* v_rawBytes_511_, lean_object* v_inst_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(v_len_510_, v_rawBytes_511_, v_inst_512_, v_a_513_);
lean_dec_ref(v_rawBytes_511_);
lean_dec(v_len_510_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0(lean_object* v_es_515_, lean_object* v_n_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = lean_string_from_utf8_unchecked(v_es_515_);
v___x_518_ = l_String_quote(v___x_517_);
v___x_519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0___boxed(lean_object* v_es_520_, lean_object* v_n_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0(v_es_520_, v_n_521_);
lean_dec(v_n_521_);
return v_res_522_;
}
}
lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg(){
_start:
{
lean_object* v___f_525_; 
v___f_525_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_525_;
}
}
LEAN_EXPORT void l_Std_Http_URI_EncodedString_instRepr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_526_;
v_res_526_ = l_Std_Http_URI_EncodedString_instRepr___redArg();
stack->m_obj
 = v_res_526_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___boxed(lean_object* v___dummy_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Http_URI_EncodedString_instRepr___redArg();
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr(lean_object* v_r_529_){
_start:
{
lean_object* v___f_530_; 
v___f_530_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___boxed(lean_object* v_r_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_Http_URI_EncodedString_instRepr(v_r_531_);
lean_dec_ref(v_r_531_);
return v_res_532_;
}
}
lean_object* l_Std_Http_URI_EncodedString_instBEq___redArg(){
_start:
{
lean_object* v___f_535_; 
v___f_535_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_535_;
}
}
LEAN_EXPORT void l_Std_Http_URI_EncodedString_instBEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_536_;
v_res_536_ = l_Std_Http_URI_EncodedString_instBEq___redArg();
stack->m_obj
 = v_res_536_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___redArg___boxed(lean_object* v___dummy_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_Http_URI_EncodedString_instBEq___redArg();
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq(lean_object* v_r_539_){
_start:
{
lean_object* v___f_540_; 
v___f_540_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___boxed(lean_object* v_r_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_Http_URI_EncodedString_instBEq(v_r_541_);
lean_dec_ref(v_r_541_);
return v_res_542_;
}
}
lean_object* l_Std_Http_URI_EncodedString_instHashable___redArg(){
_start:
{
lean_object* v___f_545_; 
v___f_545_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_545_;
}
}
LEAN_EXPORT void l_Std_Http_URI_EncodedString_instHashable___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_546_;
v_res_546_ = l_Std_Http_URI_EncodedString_instHashable___redArg();
stack->m_obj
 = v_res_546_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___redArg___boxed(lean_object* v___dummy_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_Http_URI_EncodedString_instHashable___redArg();
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable(lean_object* v_r_549_){
_start:
{
lean_object* v___f_550_; 
v___f_550_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___boxed(lean_object* v_r_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_Http_URI_EncodedString_instHashable(v_r_551_);
lean_dec_ref(v_r_551_);
return v_res_552_;
}
}
lean_object* l_Std_Http_URI_EncodedQueryString_empty___redArg(){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_ByteArray_empty;
return v___x_554_;
}
}
LEAN_EXPORT void l_Std_Http_URI_EncodedQueryString_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_555_;
v_res_555_ = l_Std_Http_URI_EncodedQueryString_empty___redArg();
stack->m_obj
 = v_res_555_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___redArg___boxed(lean_object* v___dummy_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_Http_URI_EncodedQueryString_empty___redArg();
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty(lean_object* v_r_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_ByteArray_empty;
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___boxed(lean_object* v_r_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_Http_URI_EncodedQueryString_empty(v_r_560_);
lean_dec_ref(v_r_560_);
return v_res_561_;
}
}
lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___redArg(){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_ByteArray_empty;
return v___x_563_;
}
}
LEAN_EXPORT void l_Std_Http_URI_EncodedQueryString_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_564_;
v_res_564_ = l_Std_Http_URI_EncodedQueryString_instInhabited___redArg();
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___redArg___boxed(lean_object* v___dummy_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Std_Http_URI_EncodedQueryString_instInhabited___redArg();
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited(lean_object* v_r_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_ByteArray_empty;
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___boxed(lean_object* v_r_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_Http_URI_EncodedQueryString_instInhabited(v_r_569_);
lean_dec_ref(v_r_569_);
return v_res_570_;
}
}
lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(lean_object* v_s_571_, uint8_t v_c_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = lean_byte_array_push(v_s_571_, v_c_572_);
return v___x_573_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_571_ = stack[0].m_obj;
uint8_t v_c_572_ = stack[1].m_num;
lean_object* v_res_574_;
v_res_574_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(v_s_571_, v_c_572_);
stack->m_obj
 = v_res_574_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg___boxed(lean_object* v_s_575_, lean_object* v_c_576_){
_start:
{
uint8_t v_c_boxed_577_; lean_object* v_res_578_; 
v_c_boxed_577_ = lean_unbox(v_c_576_);
v_res_578_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(v_s_575_, v_c_boxed_577_);
return v_res_578_;
}
}
lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(lean_object* v_r_579_, lean_object* v_s_580_, uint8_t v_c_581_, lean_object* v_h_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = lean_byte_array_push(v_s_580_, v_c_581_);
return v___x_583_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_579_ = stack[0].m_obj;
lean_object* v_s_580_ = stack[1].m_obj;
uint8_t v_c_581_ = stack[2].m_num;
lean_object* v_res_584_;
v_res_584_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(v_r_579_, v_s_580_, v_c_581_, lean_box(0));
stack->m_obj
 = v_res_584_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___boxed(lean_object* v_r_585_, lean_object* v_s_586_, lean_object* v_c_587_, lean_object* v_h_588_){
_start:
{
uint8_t v_c_boxed_589_; lean_object* v_res_590_; 
v_c_boxed_589_ = lean_unbox(v_c_587_);
v_res_590_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(v_r_585_, v_s_586_, v_c_boxed_589_, v_h_588_);
lean_dec_ref(v_r_585_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(lean_object* v_ba_591_, lean_object* v_r_592_){
_start:
{
uint8_t v___x_593_; 
lean_inc_ref(v_ba_591_);
v___x_593_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_592_, v_ba_591_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
lean_dec_ref(v_ba_591_);
v___x_594_ = lean_box(0);
return v___x_594_;
}
else
{
uint8_t v___x_595_; 
v___x_595_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_591_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
lean_dec_ref(v_ba_591_);
v___x_596_ = lean_box(0);
return v___x_596_;
}
else
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v_ba_591_);
return v___x_597_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_598_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = l_ByteArray_empty;
v___x_600_ = lean_panic_fn_borrowed(v___x_599_, v_msg_598_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(lean_object* v_r_601_, lean_object* v_msg_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v_msg_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_604_, lean_object* v_msg_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(v_r_604_, v_msg_605_);
lean_dec_ref(v_r_604_);
return v_res_606_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_609_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1));
v___x_610_ = lean_unsigned_to_nat(12u);
v___x_611_ = lean_unsigned_to_nat(438u);
v___x_612_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0));
v___x_613_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_614_ = l_mkPanicMessageWithDecl(v___x_613_, v___x_612_, v___x_611_, v___x_610_, v___x_609_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(lean_object* v_ba_615_, lean_object* v_r_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_615_, v_r_616_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_obj_once(&l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2, &l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2_once, _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2);
v___x_619_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v___x_618_);
return v___x_619_;
}
else
{
lean_object* v_val_620_; 
v_val_620_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_val_620_);
lean_dec_ref_known(v___x_617_, 1);
return v_val_620_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f(lean_object* v_s_621_, lean_object* v_r_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_string_to_utf8(v_s_621_);
v___x_624_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v___x_623_, v_r_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f___boxed(lean_object* v_s_625_, lean_object* v_r_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_625_, v_r_626_);
lean_dec_ref(v_s_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21(lean_object* v_s_628_, lean_object* v_r_629_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_string_to_utf8(v_s_628_);
v___x_631_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v___x_630_, v_r_629_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21___boxed(lean_object* v_s_632_, lean_object* v_r_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_Http_URI_EncodedQueryString_ofString_x21(v_s_632_, v_r_633_);
lean_dec_ref(v_s_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg(lean_object* v_ba_635_){
_start:
{
lean_inc_ref(v_ba_635_);
return v_ba_635_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg___boxed(lean_object* v_ba_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Std_Http_URI_EncodedQueryString_new___redArg(v_ba_636_);
lean_dec_ref(v_ba_636_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new(lean_object* v_r_638_, lean_object* v_ba_639_, lean_object* v_valid_640_, lean_object* v___validEncoding_641_){
_start:
{
lean_inc_ref(v_ba_639_);
return v_ba_639_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___boxed(lean_object* v_r_642_, lean_object* v_ba_643_, lean_object* v_valid_644_, lean_object* v___validEncoding_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Std_Http_URI_EncodedQueryString_new(v_r_642_, v_ba_643_, v_valid_644_, v___validEncoding_645_);
lean_dec_ref(v_ba_643_);
lean_dec_ref(v_r_642_);
return v_res_646_;
}
}
lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(uint8_t v_b_647_, lean_object* v_s_648_){
_start:
{
uint8_t v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; uint8_t v___x_652_; uint8_t v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; uint8_t v___x_656_; uint8_t v___x_657_; lean_object* v_ba_658_; 
v___x_649_ = 37;
v___x_650_ = lean_byte_array_push(v_s_648_, v___x_649_);
v___x_651_ = 4;
v___x_652_ = lean_uint8_shift_right(v_b_647_, v___x_651_);
v___x_653_ = l_Std_Http_URI_hexDigit(v___x_652_);
v___x_654_ = lean_byte_array_push(v___x_650_, v___x_653_);
v___x_655_ = 15;
v___x_656_ = lean_uint8_land(v_b_647_, v___x_655_);
v___x_657_ = l_Std_Http_URI_hexDigit(v___x_656_);
v_ba_658_ = lean_byte_array_push(v___x_654_, v___x_657_);
return v_ba_658_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_647_ = stack[0].m_num;
lean_object* v_s_648_ = stack[1].m_obj;
lean_object* v_res_659_;
v_res_659_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_647_, v_s_648_);
stack->m_obj
 = v_res_659_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg___boxed(lean_object* v_b_660_, lean_object* v_s_661_){
_start:
{
uint8_t v_b_boxed_662_; lean_object* v_res_663_; 
v_b_boxed_662_ = lean_unbox(v_b_660_);
v_res_663_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_boxed_662_, v_s_661_);
return v_res_663_;
}
}
lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(lean_object* v_r_664_, uint8_t v_b_665_, lean_object* v_s_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_665_, v_s_666_);
return v___x_667_;
}
}
LEAN_EXPORT void l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_664_ = stack[0].m_obj;
uint8_t v_b_665_ = stack[1].m_num;
lean_object* v_s_666_ = stack[2].m_obj;
lean_object* v_res_668_;
v_res_668_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(v_r_664_, v_b_665_, v_s_666_);
stack->m_obj
 = v_res_668_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___boxed(lean_object* v_r_669_, lean_object* v_b_670_, lean_object* v_s_671_){
_start:
{
uint8_t v_b_boxed_672_; lean_object* v_res_673_; 
v_b_boxed_672_ = lean_unbox(v_b_670_);
v_res_673_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(v_r_669_, v_b_boxed_672_, v_s_671_);
lean_dec_ref(v_r_669_);
return v_res_673_;
}
}
lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(lean_object* v_r_674_, lean_object* v_as_675_, size_t v_i_676_, size_t v_stop_677_, lean_object* v_b_678_){
_start:
{
lean_object* v___y_680_; uint8_t v___x_684_; 
v___x_684_ = lean_usize_dec_eq(v_i_676_, v_stop_677_);
if (v___x_684_ == 0)
{
uint8_t v___x_685_; uint8_t v___x_692_; uint8_t v___x_693_; 
v___x_685_ = lean_byte_array_uget(v_as_675_, v_i_676_);
v___x_692_ = 128;
v___x_693_ = lean_uint8_dec_lt(v___x_685_, v___x_692_);
if (v___x_693_ == 0)
{
goto v___jp_686_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_694_ = lean_box(v___x_685_);
lean_inc_ref(v_r_674_);
v___x_695_ = lean_apply_1(v_r_674_, v___x_694_);
v___x_696_ = lean_unbox(v___x_695_);
if (v___x_696_ == 0)
{
goto v___jp_686_;
}
else
{
lean_object* v___x_697_; 
v___x_697_ = lean_byte_array_push(v_b_678_, v___x_685_);
v___y_680_ = v___x_697_;
goto v___jp_679_;
}
}
v___jp_686_:
{
uint8_t v___x_687_; uint8_t v___x_688_; 
v___x_687_ = 32;
v___x_688_ = lean_uint8_dec_eq(v___x_685_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
v___x_689_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v___x_685_, v_b_678_);
v___y_680_ = v___x_689_;
goto v___jp_679_;
}
else
{
uint8_t v___x_690_; lean_object* v___x_691_; 
v___x_690_ = 43;
v___x_691_ = lean_byte_array_push(v_b_678_, v___x_690_);
v___y_680_ = v___x_691_;
goto v___jp_679_;
}
}
}
else
{
lean_dec_ref(v_r_674_);
return v_b_678_;
}
v___jp_679_:
{
size_t v___x_681_; size_t v___x_682_; 
v___x_681_ = ((size_t)1ULL);
v___x_682_ = lean_usize_add(v_i_676_, v___x_681_);
v_i_676_ = v___x_682_;
v_b_678_ = v___y_680_;
goto _start;
}
}
}
LEAN_EXPORT void l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_674_ = stack[0].m_obj;
lean_object* v_as_675_ = stack[1].m_obj;
size_t v_i_676_ = stack[2].m_num;
size_t v_stop_677_ = stack[3].m_num;
lean_object* v_b_678_ = stack[4].m_obj;
lean_object* v_res_698_;
v_res_698_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_674_, v_as_675_, v_i_676_, v_stop_677_, v_b_678_);
stack->m_obj
 = v_res_698_;
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___boxed(lean_object* v_r_699_, lean_object* v_as_700_, lean_object* v_i_701_, lean_object* v_stop_702_, lean_object* v_b_703_){
_start:
{
size_t v_i_boxed_704_; size_t v_stop_boxed_705_; lean_object* v_res_706_; 
v_i_boxed_704_ = lean_unbox_usize(v_i_701_);
lean_dec(v_i_701_);
v_stop_boxed_705_ = lean_unbox_usize(v_stop_702_);
lean_dec(v_stop_702_);
v_res_706_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_699_, v_as_700_, v_i_boxed_704_, v_stop_boxed_705_, v_b_703_);
lean_dec_ref(v_as_700_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode(lean_object* v_s_707_, lean_object* v_r_708_){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_709_ = l_ByteArray_empty;
v___x_710_ = lean_string_to_utf8(v_s_707_);
v___x_711_ = lean_unsigned_to_nat(0u);
v___x_712_ = lean_byte_array_size(v___x_710_);
v___x_713_ = lean_nat_dec_lt(v___x_711_, v___x_712_);
if (v___x_713_ == 0)
{
lean_dec_ref(v___x_710_);
lean_dec_ref(v_r_708_);
return v___x_709_;
}
else
{
uint8_t v___x_714_; 
v___x_714_ = lean_nat_dec_le(v___x_712_, v___x_712_);
if (v___x_714_ == 0)
{
if (v___x_713_ == 0)
{
lean_dec_ref(v___x_710_);
lean_dec_ref(v_r_708_);
return v___x_709_;
}
else
{
size_t v___x_715_; size_t v___x_716_; lean_object* v___x_717_; 
v___x_715_ = ((size_t)0ULL);
v___x_716_ = lean_usize_of_nat(v___x_712_);
v___x_717_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_708_, v___x_710_, v___x_715_, v___x_716_, v___x_709_);
lean_dec_ref(v___x_710_);
return v___x_717_;
}
}
else
{
size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; 
v___x_718_ = ((size_t)0ULL);
v___x_719_ = lean_usize_of_nat(v___x_712_);
v___x_720_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_708_, v___x_710_, v___x_718_, v___x_719_, v___x_709_);
lean_dec_ref(v___x_710_);
return v___x_720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode___boxed(lean_object* v_s_721_, lean_object* v_r_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_721_, v_r_722_);
lean_dec_ref(v_s_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___redArg(lean_object* v_es_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = lean_string_from_utf8_unchecked(v_es_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString(lean_object* v_r_726_, lean_object* v_es_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = lean_string_from_utf8_unchecked(v_es_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___boxed(lean_object* v_r_729_, lean_object* v_es_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Std_Http_URI_EncodedQueryString_toString(v_r_729_, v_es_730_);
lean_dec_ref(v_r_729_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(lean_object* v_len_732_, lean_object* v_rawBytes_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_fst_735_; lean_object* v_snd_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_802_; 
v_fst_735_ = lean_ctor_get(v_a_734_, 0);
v_snd_736_ = lean_ctor_get(v_a_734_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v_a_734_);
if (v_isSharedCheck_802_ == 0)
{
v___x_738_ = v_a_734_;
v_isShared_739_ = v_isSharedCheck_802_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_snd_736_);
lean_inc(v_fst_735_);
lean_dec(v_a_734_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_802_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
uint8_t v___x_740_; 
v___x_740_ = lean_nat_dec_lt(v_snd_736_, v_len_732_);
if (v___x_740_ == 0)
{
lean_object* v___x_742_; 
if (v_isShared_739_ == 0)
{
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_fst_735_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_snd_736_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
else
{
uint8_t v_plus_744_; uint8_t v___x_745_; uint8_t v___x_754_; 
v_plus_744_ = 43;
v___x_745_ = lean_byte_array_fget(v_rawBytes_733_, v_snd_736_);
v___x_754_ = lean_uint8_dec_eq(v___x_745_, v_plus_744_);
if (v___x_754_ == 0)
{
uint8_t v_percent_755_; uint8_t v___x_756_; 
v_percent_755_ = 37;
v___x_756_ = lean_uint8_dec_eq(v___x_745_, v_percent_755_);
if (v___x_756_ == 0)
{
goto v___jp_746_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_757_ = lean_unsigned_to_nat(1u);
v___x_758_ = lean_nat_add(v_snd_736_, v___x_757_);
v___x_759_ = lean_nat_dec_lt(v___x_758_, v_len_732_);
if (v___x_759_ == 0)
{
lean_dec(v___x_758_);
goto v___jp_746_;
}
else
{
uint8_t v___x_760_; lean_object* v___x_761_; 
lean_del_object(v___x_738_);
v___x_760_ = lean_byte_array_fget(v_rawBytes_733_, v___x_758_);
lean_dec(v___x_758_);
v___x_761_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_760_);
if (lean_obj_tag(v___x_761_) == 1)
{
lean_object* v_val_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v_val_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_val_762_);
lean_dec_ref_known(v___x_761_, 1);
v___x_763_ = lean_unsigned_to_nat(2u);
v___x_764_ = lean_nat_add(v_snd_736_, v___x_763_);
v___x_765_ = lean_nat_dec_lt(v___x_764_, v_len_732_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec(v_val_762_);
lean_dec(v_snd_736_);
v___x_766_ = lean_byte_array_push(v_fst_735_, v___x_745_);
v___x_767_ = lean_byte_array_push(v___x_766_, v___x_760_);
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
lean_ctor_set(v___x_768_, 1, v___x_764_);
v_a_734_ = v___x_768_;
goto _start;
}
else
{
uint8_t v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_byte_array_fget(v_rawBytes_733_, v___x_764_);
lean_dec(v___x_764_);
v___x_771_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_770_);
if (lean_obj_tag(v___x_771_) == 1)
{
lean_object* v_val_772_; uint8_t v___x_773_; uint8_t v___x_774_; uint8_t v___x_775_; uint8_t v___x_776_; uint8_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_val_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_val_772_);
lean_dec_ref_known(v___x_771_, 1);
v___x_773_ = 4;
v___x_774_ = lean_unbox(v_val_762_);
lean_dec(v_val_762_);
v___x_775_ = lean_uint8_shift_left(v___x_774_, v___x_773_);
v___x_776_ = lean_unbox(v_val_772_);
lean_dec(v_val_772_);
v___x_777_ = lean_uint8_add(v___x_775_, v___x_776_);
v___x_778_ = lean_byte_array_push(v_fst_735_, v___x_777_);
v___x_779_ = lean_unsigned_to_nat(3u);
v___x_780_ = lean_nat_add(v_snd_736_, v___x_779_);
lean_dec(v_snd_736_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_778_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v_a_734_ = v___x_781_;
goto _start;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec(v___x_771_);
lean_dec(v_val_762_);
v___x_783_ = lean_byte_array_push(v_fst_735_, v___x_745_);
v___x_784_ = lean_byte_array_push(v___x_783_, v___x_760_);
v___x_785_ = lean_byte_array_push(v___x_784_, v___x_770_);
v___x_786_ = lean_unsigned_to_nat(3u);
v___x_787_ = lean_nat_add(v_snd_736_, v___x_786_);
lean_dec(v_snd_736_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_785_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v_a_734_ = v___x_788_;
goto _start;
}
}
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
lean_dec(v___x_761_);
v___x_790_ = lean_byte_array_push(v_fst_735_, v___x_745_);
v___x_791_ = lean_byte_array_push(v___x_790_, v___x_760_);
v___x_792_ = lean_unsigned_to_nat(2u);
v___x_793_ = lean_nat_add(v_snd_736_, v___x_792_);
lean_dec(v_snd_736_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_791_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v_a_734_ = v___x_794_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_del_object(v___x_738_);
v___x_796_ = 32;
v___x_797_ = lean_byte_array_push(v_fst_735_, v___x_796_);
v___x_798_ = lean_unsigned_to_nat(1u);
v___x_799_ = lean_nat_add(v_snd_736_, v___x_798_);
lean_dec(v_snd_736_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_797_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v_a_734_ = v___x_800_;
goto _start;
}
v___jp_746_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_747_ = lean_byte_array_push(v_fst_735_, v___x_745_);
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = lean_nat_add(v_snd_736_, v___x_748_);
lean_dec(v_snd_736_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v___x_749_);
lean_ctor_set(v___x_738_, 0, v___x_747_);
v___x_751_ = v___x_738_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v___x_749_);
v___x_751_ = v_reuseFailAlloc_753_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
v_a_734_ = v___x_751_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg___boxed(lean_object* v_len_803_, lean_object* v_rawBytes_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_803_, v_rawBytes_804_, v_a_805_);
lean_dec_ref(v_rawBytes_804_);
lean_dec(v_len_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg(lean_object* v_es_807_){
_start:
{
lean_object* v_len_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v_fst_811_; uint8_t v___x_812_; 
v_len_808_ = lean_byte_array_size(v_es_807_);
v___x_809_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_810_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_808_, v_es_807_, v___x_809_);
v_fst_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_fst_811_);
lean_dec_ref(v___x_810_);
v___x_812_ = lean_string_validate_utf8(v_fst_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
lean_dec(v_fst_811_);
v___x_813_ = lean_box(0);
return v___x_813_;
}
else
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_string_from_utf8_unchecked(v_fst_811_);
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg___boxed(lean_object* v_es_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_816_);
lean_dec_ref(v_es_816_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode(lean_object* v_r_818_, lean_object* v_es_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___boxed(lean_object* v_r_821_, lean_object* v_es_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Std_Http_URI_EncodedQueryString_decode(v_r_821_, v_es_822_);
lean_dec_ref(v_es_822_);
lean_dec_ref(v_r_821_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(lean_object* v_len_824_, lean_object* v_rawBytes_825_, lean_object* v_inst_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_824_, v_rawBytes_825_, v_a_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___boxed(lean_object* v_len_829_, lean_object* v_rawBytes_830_, lean_object* v_inst_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(v_len_829_, v_rawBytes_830_, v_inst_831_, v_a_832_);
lean_dec_ref(v_rawBytes_830_);
lean_dec(v_len_829_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringEncodedQueryString(lean_object* v_r_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = lean_alloc_closure((void*)(l_Std_Http_URI_EncodedQueryString_toString___boxed), 2, 1);
lean_closure_set(v___x_835_, 0, v_r_834_);
return v___x_835_;
}
}
lean_object* l_Std_Http_URI_instReprEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_837_; 
v___f_837_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_837_;
}
}
LEAN_EXPORT void l_Std_Http_URI_instReprEncodedQueryString___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_838_;
v_res_838_ = l_Std_Http_URI_instReprEncodedQueryString___redArg();
stack->m_obj
 = v_res_838_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___redArg___boxed(lean_object* v___dummy_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_Http_URI_instReprEncodedQueryString___redArg();
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString(lean_object* v_r_841_){
_start:
{
lean_object* v___f_842_; 
v___f_842_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_842_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___boxed(lean_object* v_r_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_Http_URI_instReprEncodedQueryString(v_r_843_);
lean_dec_ref(v_r_843_);
return v_res_844_;
}
}
lean_object* l_Std_Http_URI_instBEqEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_846_; 
v___f_846_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_846_;
}
}
LEAN_EXPORT void l_Std_Http_URI_instBEqEncodedQueryString___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_847_;
v_res_847_ = l_Std_Http_URI_instBEqEncodedQueryString___redArg();
stack->m_obj
 = v_res_847_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___redArg___boxed(lean_object* v___dummy_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std_Http_URI_instBEqEncodedQueryString___redArg();
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString(lean_object* v_r_850_){
_start:
{
lean_object* v___f_851_; 
v___f_851_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_851_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___boxed(lean_object* v_r_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Std_Http_URI_instBEqEncodedQueryString(v_r_852_);
lean_dec_ref(v_r_852_);
return v_res_853_;
}
}
lean_object* l_Std_Http_URI_instHashableEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_855_; 
v___f_855_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_855_;
}
}
LEAN_EXPORT void l_Std_Http_URI_instHashableEncodedQueryString___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_856_;
v_res_856_ = l_Std_Http_URI_instHashableEncodedQueryString___redArg();
stack->m_obj
 = v_res_856_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___redArg___boxed(lean_object* v___dummy_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Std_Http_URI_instHashableEncodedQueryString___redArg();
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString(lean_object* v_r_859_){
_start:
{
lean_object* v___f_860_; 
v___f_860_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_860_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___boxed(lean_object* v_r_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Std_Http_URI_instHashableEncodedQueryString(v_r_861_);
lean_dec_ref(v_r_861_);
return v_res_862_;
}
}
static uint64_t _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_869_; uint64_t v___x_870_; 
v___x_869_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__0));
v___x_870_ = lean_byte_array_hash(v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__2));
v___x_878_ = lean_byte_array_size(v___x_877_);
return v___x_878_;
}
}
uint64_t l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0(lean_object* v_x_879_){
_start:
{
if (lean_obj_tag(v_x_879_) == 0)
{
uint64_t v___x_880_; 
v___x_880_ = lean_uint64_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1, &l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1);
return v___x_880_;
}
else
{
lean_object* v_val_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; lean_object* v___x_887_; uint64_t v___x_888_; 
v_val_881_ = lean_ctor_get(v_x_879_, 0);
v___x_882_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__2));
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_obj_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3, &l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3);
v___x_885_ = lean_byte_array_size(v_val_881_);
v___x_886_ = 0;
v___x_887_ = lean_byte_array_copy_slice(v_val_881_, v___x_883_, v___x_882_, v___x_884_, v___x_885_, v___x_886_);
v___x_888_ = lean_byte_array_hash(v___x_887_);
lean_dec_ref(v___x_887_);
return v___x_888_;
}
}
}
LEAN_EXPORT void l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_879_ = stack[0].m_obj;
uint64_t v_res_889_;
v_res_889_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0(v_x_879_);
stack->m_num = v_res_889_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___boxed(lean_object* v_x_890_){
_start:
{
uint64_t v_res_891_; lean_object* v_r_892_; 
v_res_891_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0(v_x_890_);
lean_dec(v_x_890_);
v_r_892_ = lean_box_uint64(v_res_891_);
return v_r_892_;
}
}
lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_895_; 
v___f_895_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___closed__0));
return v___f_895_;
}
}
LEAN_EXPORT void l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_896_;
v_res_896_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg();
stack->m_obj
 = v_res_896_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___boxed(lean_object* v___dummy_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg();
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString(lean_object* v_r_899_){
_start:
{
lean_object* v___f_900_; 
v___f_900_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___closed__0));
return v___f_900_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___boxed(lean_object* v_r_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_Http_URI_instHashableOptionEncodedQueryString(v_r_901_);
lean_dec_ref(v_r_901_);
return v_res_902_;
}
}
uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0(uint8_t v___y_903_){
_start:
{
uint8_t v___x_949_; uint8_t v___x_950_; 
v___x_949_ = 48;
v___x_950_ = lean_uint8_dec_le(v___x_949_, v___y_903_);
if (v___x_950_ == 0)
{
goto v___jp_944_;
}
else
{
uint8_t v___x_951_; uint8_t v___x_952_; 
v___x_951_ = 57;
v___x_952_ = lean_uint8_dec_le(v___y_903_, v___x_951_);
if (v___x_952_ == 0)
{
goto v___jp_944_;
}
else
{
return v___x_952_;
}
}
v___jp_904_:
{
uint8_t v___x_905_; uint8_t v___x_906_; 
v___x_905_ = 45;
v___x_906_ = lean_uint8_dec_eq(v___y_903_, v___x_905_);
if (v___x_906_ == 0)
{
uint8_t v___x_907_; uint8_t v___x_908_; 
v___x_907_ = 46;
v___x_908_ = lean_uint8_dec_eq(v___y_903_, v___x_907_);
if (v___x_908_ == 0)
{
uint8_t v___x_909_; uint8_t v___x_910_; 
v___x_909_ = 95;
v___x_910_ = lean_uint8_dec_eq(v___y_903_, v___x_909_);
if (v___x_910_ == 0)
{
uint8_t v___x_911_; uint8_t v___x_912_; 
v___x_911_ = 126;
v___x_912_ = lean_uint8_dec_eq(v___y_903_, v___x_911_);
if (v___x_912_ == 0)
{
uint8_t v___x_913_; uint8_t v___x_914_; 
v___x_913_ = 33;
v___x_914_ = lean_uint8_dec_eq(v___y_903_, v___x_913_);
if (v___x_914_ == 0)
{
uint8_t v___x_915_; uint8_t v___x_916_; 
v___x_915_ = 36;
v___x_916_ = lean_uint8_dec_eq(v___y_903_, v___x_915_);
if (v___x_916_ == 0)
{
uint8_t v___x_917_; uint8_t v___x_918_; 
v___x_917_ = 38;
v___x_918_ = lean_uint8_dec_eq(v___y_903_, v___x_917_);
if (v___x_918_ == 0)
{
uint8_t v___x_919_; uint8_t v___x_920_; 
v___x_919_ = 39;
v___x_920_ = lean_uint8_dec_eq(v___y_903_, v___x_919_);
if (v___x_920_ == 0)
{
uint8_t v___x_921_; uint8_t v___x_922_; 
v___x_921_ = 40;
v___x_922_ = lean_uint8_dec_eq(v___y_903_, v___x_921_);
if (v___x_922_ == 0)
{
uint8_t v___x_923_; uint8_t v___x_924_; 
v___x_923_ = 41;
v___x_924_ = lean_uint8_dec_eq(v___y_903_, v___x_923_);
if (v___x_924_ == 0)
{
uint8_t v___x_925_; uint8_t v___x_926_; 
v___x_925_ = 42;
v___x_926_ = lean_uint8_dec_eq(v___y_903_, v___x_925_);
if (v___x_926_ == 0)
{
uint8_t v___x_927_; uint8_t v___x_928_; 
v___x_927_ = 43;
v___x_928_ = lean_uint8_dec_eq(v___y_903_, v___x_927_);
if (v___x_928_ == 0)
{
uint8_t v___x_929_; uint8_t v___x_930_; 
v___x_929_ = 44;
v___x_930_ = lean_uint8_dec_eq(v___y_903_, v___x_929_);
if (v___x_930_ == 0)
{
uint8_t v___x_931_; uint8_t v___x_932_; 
v___x_931_ = 59;
v___x_932_ = lean_uint8_dec_eq(v___y_903_, v___x_931_);
if (v___x_932_ == 0)
{
uint8_t v___x_933_; uint8_t v___x_934_; 
v___x_933_ = 61;
v___x_934_ = lean_uint8_dec_eq(v___y_903_, v___x_933_);
if (v___x_934_ == 0)
{
uint8_t v___x_935_; uint8_t v___x_936_; 
v___x_935_ = 58;
v___x_936_ = lean_uint8_dec_eq(v___y_903_, v___x_935_);
if (v___x_936_ == 0)
{
uint8_t v___x_937_; uint8_t v___x_938_; 
v___x_937_ = 64;
v___x_938_ = lean_uint8_dec_eq(v___y_903_, v___x_937_);
return v___x_938_;
}
else
{
return v___x_936_;
}
}
else
{
return v___x_934_;
}
}
else
{
return v___x_932_;
}
}
else
{
return v___x_930_;
}
}
else
{
return v___x_928_;
}
}
else
{
return v___x_926_;
}
}
else
{
return v___x_924_;
}
}
else
{
return v___x_922_;
}
}
else
{
return v___x_920_;
}
}
else
{
return v___x_918_;
}
}
else
{
return v___x_916_;
}
}
else
{
return v___x_914_;
}
}
else
{
return v___x_912_;
}
}
else
{
return v___x_910_;
}
}
else
{
return v___x_908_;
}
}
else
{
return v___x_906_;
}
}
v___jp_939_:
{
uint8_t v___x_940_; uint8_t v___x_941_; 
v___x_940_ = 65;
v___x_941_ = lean_uint8_dec_le(v___x_940_, v___y_903_);
if (v___x_941_ == 0)
{
goto v___jp_904_;
}
else
{
uint8_t v___x_942_; uint8_t v___x_943_; 
v___x_942_ = 90;
v___x_943_ = lean_uint8_dec_le(v___y_903_, v___x_942_);
if (v___x_943_ == 0)
{
goto v___jp_904_;
}
else
{
return v___x_943_;
}
}
}
v___jp_944_:
{
uint8_t v___x_945_; uint8_t v___x_946_; 
v___x_945_ = 97;
v___x_946_ = lean_uint8_dec_le(v___x_945_, v___y_903_);
if (v___x_946_ == 0)
{
goto v___jp_939_;
}
else
{
uint8_t v___x_947_; uint8_t v___x_948_; 
v___x_947_ = 122;
v___x_948_ = lean_uint8_dec_le(v___y_903_, v___x_947_);
if (v___x_948_ == 0)
{
goto v___jp_939_;
}
else
{
return v___x_948_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_EncodedSegment_encode___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_903_ = stack[0].m_num;
uint8_t v_res_953_;
v_res_953_ = l_Std_Http_URI_EncodedSegment_encode___lam__0(v___y_903_);
stack->m_num = v_res_953_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___lam__0___boxed(lean_object* v___y_954_){
_start:
{
uint8_t v___y_265__boxed_955_; uint8_t v_res_956_; lean_object* v_r_957_; 
v___y_265__boxed_955_ = lean_unbox(v___y_954_);
v_res_956_ = l_Std_Http_URI_EncodedSegment_encode___lam__0(v___y_265__boxed_955_);
v_r_957_ = lean_box(v_res_956_);
return v_r_957_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode(lean_object* v_s_959_){
_start:
{
lean_object* v___f_960_; lean_object* v___x_961_; 
v___f_960_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_961_ = l_Std_Http_URI_EncodedString_encode(v___f_960_, v_s_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___boxed(lean_object* v_s_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Std_Http_URI_EncodedSegment_encode(v_s_962_);
lean_dec_ref(v_s_962_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object* v_ba_964_){
_start:
{
lean_object* v___f_965_; lean_object* v___x_966_; 
v___f_965_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_966_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_965_, v_ba_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x21(lean_object* v_ba_967_){
_start:
{
lean_object* v___f_968_; lean_object* v___x_969_; 
v___f_968_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_969_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_968_, v_ba_967_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object* v_segment_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Std_Http_URI_EncodedString_decode___redArg(v_segment_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode___boxed(lean_object* v_segment_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Std_Http_URI_EncodedSegment_decode(v_segment_972_);
lean_dec_ref(v_segment_972_);
return v_res_973_;
}
}
uint8_t l_Std_Http_URI_EncodedFragment_encode___lam__0(uint8_t v___y_974_){
_start:
{
uint8_t v___x_1024_; uint8_t v___x_1025_; 
v___x_1024_ = 48;
v___x_1025_ = lean_uint8_dec_le(v___x_1024_, v___y_974_);
if (v___x_1025_ == 0)
{
goto v___jp_1019_;
}
else
{
uint8_t v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = 57;
v___x_1027_ = lean_uint8_dec_le(v___y_974_, v___x_1026_);
if (v___x_1027_ == 0)
{
goto v___jp_1019_;
}
else
{
return v___x_1027_;
}
}
v___jp_975_:
{
uint8_t v___x_976_; uint8_t v___x_977_; 
v___x_976_ = 45;
v___x_977_ = lean_uint8_dec_eq(v___y_974_, v___x_976_);
if (v___x_977_ == 0)
{
uint8_t v___x_978_; uint8_t v___x_979_; 
v___x_978_ = 46;
v___x_979_ = lean_uint8_dec_eq(v___y_974_, v___x_978_);
if (v___x_979_ == 0)
{
uint8_t v___x_980_; uint8_t v___x_981_; 
v___x_980_ = 95;
v___x_981_ = lean_uint8_dec_eq(v___y_974_, v___x_980_);
if (v___x_981_ == 0)
{
uint8_t v___x_982_; uint8_t v___x_983_; 
v___x_982_ = 126;
v___x_983_ = lean_uint8_dec_eq(v___y_974_, v___x_982_);
if (v___x_983_ == 0)
{
uint8_t v___x_984_; uint8_t v___x_985_; 
v___x_984_ = 33;
v___x_985_ = lean_uint8_dec_eq(v___y_974_, v___x_984_);
if (v___x_985_ == 0)
{
uint8_t v___x_986_; uint8_t v___x_987_; 
v___x_986_ = 36;
v___x_987_ = lean_uint8_dec_eq(v___y_974_, v___x_986_);
if (v___x_987_ == 0)
{
uint8_t v___x_988_; uint8_t v___x_989_; 
v___x_988_ = 38;
v___x_989_ = lean_uint8_dec_eq(v___y_974_, v___x_988_);
if (v___x_989_ == 0)
{
uint8_t v___x_990_; uint8_t v___x_991_; 
v___x_990_ = 39;
v___x_991_ = lean_uint8_dec_eq(v___y_974_, v___x_990_);
if (v___x_991_ == 0)
{
uint8_t v___x_992_; uint8_t v___x_993_; 
v___x_992_ = 40;
v___x_993_ = lean_uint8_dec_eq(v___y_974_, v___x_992_);
if (v___x_993_ == 0)
{
uint8_t v___x_994_; uint8_t v___x_995_; 
v___x_994_ = 41;
v___x_995_ = lean_uint8_dec_eq(v___y_974_, v___x_994_);
if (v___x_995_ == 0)
{
uint8_t v___x_996_; uint8_t v___x_997_; 
v___x_996_ = 42;
v___x_997_ = lean_uint8_dec_eq(v___y_974_, v___x_996_);
if (v___x_997_ == 0)
{
uint8_t v___x_998_; uint8_t v___x_999_; 
v___x_998_ = 43;
v___x_999_ = lean_uint8_dec_eq(v___y_974_, v___x_998_);
if (v___x_999_ == 0)
{
uint8_t v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = 44;
v___x_1001_ = lean_uint8_dec_eq(v___y_974_, v___x_1000_);
if (v___x_1001_ == 0)
{
uint8_t v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = 59;
v___x_1003_ = lean_uint8_dec_eq(v___y_974_, v___x_1002_);
if (v___x_1003_ == 0)
{
uint8_t v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = 61;
v___x_1005_ = lean_uint8_dec_eq(v___y_974_, v___x_1004_);
if (v___x_1005_ == 0)
{
uint8_t v___x_1006_; uint8_t v___x_1007_; 
v___x_1006_ = 58;
v___x_1007_ = lean_uint8_dec_eq(v___y_974_, v___x_1006_);
if (v___x_1007_ == 0)
{
uint8_t v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = 64;
v___x_1009_ = lean_uint8_dec_eq(v___y_974_, v___x_1008_);
if (v___x_1009_ == 0)
{
uint8_t v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = 47;
v___x_1011_ = lean_uint8_dec_eq(v___y_974_, v___x_1010_);
if (v___x_1011_ == 0)
{
uint8_t v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = 63;
v___x_1013_ = lean_uint8_dec_eq(v___y_974_, v___x_1012_);
return v___x_1013_;
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
else
{
return v___x_1003_;
}
}
else
{
return v___x_1001_;
}
}
else
{
return v___x_999_;
}
}
else
{
return v___x_997_;
}
}
else
{
return v___x_995_;
}
}
else
{
return v___x_993_;
}
}
else
{
return v___x_991_;
}
}
else
{
return v___x_989_;
}
}
else
{
return v___x_987_;
}
}
else
{
return v___x_985_;
}
}
else
{
return v___x_983_;
}
}
else
{
return v___x_981_;
}
}
else
{
return v___x_979_;
}
}
else
{
return v___x_977_;
}
}
v___jp_1014_:
{
uint8_t v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = 65;
v___x_1016_ = lean_uint8_dec_le(v___x_1015_, v___y_974_);
if (v___x_1016_ == 0)
{
goto v___jp_975_;
}
else
{
uint8_t v___x_1017_; uint8_t v___x_1018_; 
v___x_1017_ = 90;
v___x_1018_ = lean_uint8_dec_le(v___y_974_, v___x_1017_);
if (v___x_1018_ == 0)
{
goto v___jp_975_;
}
else
{
return v___x_1018_;
}
}
}
v___jp_1019_:
{
uint8_t v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = 97;
v___x_1021_ = lean_uint8_dec_le(v___x_1020_, v___y_974_);
if (v___x_1021_ == 0)
{
goto v___jp_1014_;
}
else
{
uint8_t v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = 122;
v___x_1023_ = lean_uint8_dec_le(v___y_974_, v___x_1022_);
if (v___x_1023_ == 0)
{
goto v___jp_1014_;
}
else
{
return v___x_1023_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_EncodedFragment_encode___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_974_ = stack[0].m_num;
uint8_t v_res_1028_;
v_res_1028_ = l_Std_Http_URI_EncodedFragment_encode___lam__0(v___y_974_);
stack->m_num = v_res_1028_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed(lean_object* v___y_1029_){
_start:
{
uint8_t v___y_289__boxed_1030_; uint8_t v_res_1031_; lean_object* v_r_1032_; 
v___y_289__boxed_1030_ = lean_unbox(v___y_1029_);
v_res_1031_ = l_Std_Http_URI_EncodedFragment_encode___lam__0(v___y_289__boxed_1030_);
v_r_1032_ = lean_box(v_res_1031_);
return v_r_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object* v_s_1034_){
_start:
{
lean_object* v___f_1035_; lean_object* v___x_1036_; 
v___f_1035_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1036_ = l_Std_Http_URI_EncodedString_encode(v___f_1035_, v_s_1034_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___boxed(lean_object* v_s_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Std_Http_URI_EncodedFragment_encode(v_s_1037_);
lean_dec_ref(v_s_1037_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object* v_ba_1039_){
_start:
{
lean_object* v___f_1040_; lean_object* v___x_1041_; 
v___f_1040_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1041_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1040_, v_ba_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x21(lean_object* v_ba_1042_){
_start:
{
lean_object* v___f_1043_; lean_object* v___x_1044_; 
v___f_1043_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1044_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1043_, v_ba_1042_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object* v_fragment_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Std_Http_URI_EncodedString_decode___redArg(v_fragment_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode___boxed(lean_object* v_fragment_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Std_Http_URI_EncodedFragment_decode(v_fragment_1047_);
lean_dec_ref(v_fragment_1047_);
return v_res_1048_;
}
}
uint8_t l_Std_Http_URI_EncodedUserInfo_encode___lam__0(uint8_t v___y_1049_){
_start:
{
uint8_t v___x_1093_; uint8_t v___x_1094_; 
v___x_1093_ = 48;
v___x_1094_ = lean_uint8_dec_le(v___x_1093_, v___y_1049_);
if (v___x_1094_ == 0)
{
goto v___jp_1088_;
}
else
{
uint8_t v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = 57;
v___x_1096_ = lean_uint8_dec_le(v___y_1049_, v___x_1095_);
if (v___x_1096_ == 0)
{
goto v___jp_1088_;
}
else
{
return v___x_1096_;
}
}
v___jp_1050_:
{
uint8_t v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = 45;
v___x_1052_ = lean_uint8_dec_eq(v___y_1049_, v___x_1051_);
if (v___x_1052_ == 0)
{
uint8_t v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = 46;
v___x_1054_ = lean_uint8_dec_eq(v___y_1049_, v___x_1053_);
if (v___x_1054_ == 0)
{
uint8_t v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = 95;
v___x_1056_ = lean_uint8_dec_eq(v___y_1049_, v___x_1055_);
if (v___x_1056_ == 0)
{
uint8_t v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = 126;
v___x_1058_ = lean_uint8_dec_eq(v___y_1049_, v___x_1057_);
if (v___x_1058_ == 0)
{
uint8_t v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = 33;
v___x_1060_ = lean_uint8_dec_eq(v___y_1049_, v___x_1059_);
if (v___x_1060_ == 0)
{
uint8_t v___x_1061_; uint8_t v___x_1062_; 
v___x_1061_ = 36;
v___x_1062_ = lean_uint8_dec_eq(v___y_1049_, v___x_1061_);
if (v___x_1062_ == 0)
{
uint8_t v___x_1063_; uint8_t v___x_1064_; 
v___x_1063_ = 38;
v___x_1064_ = lean_uint8_dec_eq(v___y_1049_, v___x_1063_);
if (v___x_1064_ == 0)
{
uint8_t v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = 39;
v___x_1066_ = lean_uint8_dec_eq(v___y_1049_, v___x_1065_);
if (v___x_1066_ == 0)
{
uint8_t v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = 40;
v___x_1068_ = lean_uint8_dec_eq(v___y_1049_, v___x_1067_);
if (v___x_1068_ == 0)
{
uint8_t v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = 41;
v___x_1070_ = lean_uint8_dec_eq(v___y_1049_, v___x_1069_);
if (v___x_1070_ == 0)
{
uint8_t v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = 42;
v___x_1072_ = lean_uint8_dec_eq(v___y_1049_, v___x_1071_);
if (v___x_1072_ == 0)
{
uint8_t v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = 43;
v___x_1074_ = lean_uint8_dec_eq(v___y_1049_, v___x_1073_);
if (v___x_1074_ == 0)
{
uint8_t v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = 44;
v___x_1076_ = lean_uint8_dec_eq(v___y_1049_, v___x_1075_);
if (v___x_1076_ == 0)
{
uint8_t v___x_1077_; uint8_t v___x_1078_; 
v___x_1077_ = 59;
v___x_1078_ = lean_uint8_dec_eq(v___y_1049_, v___x_1077_);
if (v___x_1078_ == 0)
{
uint8_t v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = 61;
v___x_1080_ = lean_uint8_dec_eq(v___y_1049_, v___x_1079_);
if (v___x_1080_ == 0)
{
uint8_t v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = 58;
v___x_1082_ = lean_uint8_dec_eq(v___y_1049_, v___x_1081_);
return v___x_1082_;
}
else
{
return v___x_1080_;
}
}
else
{
return v___x_1078_;
}
}
else
{
return v___x_1076_;
}
}
else
{
return v___x_1074_;
}
}
else
{
return v___x_1072_;
}
}
else
{
return v___x_1070_;
}
}
else
{
return v___x_1068_;
}
}
else
{
return v___x_1066_;
}
}
else
{
return v___x_1064_;
}
}
else
{
return v___x_1062_;
}
}
else
{
return v___x_1060_;
}
}
else
{
return v___x_1058_;
}
}
else
{
return v___x_1056_;
}
}
else
{
return v___x_1054_;
}
}
else
{
return v___x_1052_;
}
}
v___jp_1083_:
{
uint8_t v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = 65;
v___x_1085_ = lean_uint8_dec_le(v___x_1084_, v___y_1049_);
if (v___x_1085_ == 0)
{
goto v___jp_1050_;
}
else
{
uint8_t v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = 90;
v___x_1087_ = lean_uint8_dec_le(v___y_1049_, v___x_1086_);
if (v___x_1087_ == 0)
{
goto v___jp_1050_;
}
else
{
return v___x_1087_;
}
}
}
v___jp_1088_:
{
uint8_t v___x_1089_; uint8_t v___x_1090_; 
v___x_1089_ = 97;
v___x_1090_ = lean_uint8_dec_le(v___x_1089_, v___y_1049_);
if (v___x_1090_ == 0)
{
goto v___jp_1083_;
}
else
{
uint8_t v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = 122;
v___x_1092_ = lean_uint8_dec_le(v___y_1049_, v___x_1091_);
if (v___x_1092_ == 0)
{
goto v___jp_1083_;
}
else
{
return v___x_1092_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_EncodedUserInfo_encode___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_1049_ = stack[0].m_num;
uint8_t v_res_1097_;
v_res_1097_ = l_Std_Http_URI_EncodedUserInfo_encode___lam__0(v___y_1049_);
stack->m_num = v_res_1097_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed(lean_object* v___y_1098_){
_start:
{
uint8_t v___y_253__boxed_1099_; uint8_t v_res_1100_; lean_object* v_r_1101_; 
v___y_253__boxed_1099_ = lean_unbox(v___y_1098_);
v_res_1100_ = l_Std_Http_URI_EncodedUserInfo_encode___lam__0(v___y_253__boxed_1099_);
v_r_1101_ = lean_box(v_res_1100_);
return v_r_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object* v_s_1103_){
_start:
{
lean_object* v___f_1104_; lean_object* v___x_1105_; 
v___f_1104_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1105_ = l_Std_Http_URI_EncodedString_encode(v___f_1104_, v_s_1103_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___boxed(lean_object* v_s_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Std_Http_URI_EncodedUserInfo_encode(v_s_1106_);
lean_dec_ref(v_s_1106_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object* v_ba_1108_){
_start:
{
lean_object* v___f_1109_; lean_object* v___x_1110_; 
v___f_1109_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1110_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1109_, v_ba_1108_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x21(lean_object* v_ba_1111_){
_start:
{
lean_object* v___f_1112_; lean_object* v___x_1113_; 
v___f_1112_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1113_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1112_, v_ba_1111_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode(lean_object* v_userInfo_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Std_Http_URI_EncodedString_decode___redArg(v_userInfo_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode___boxed(lean_object* v_userInfo_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_Http_URI_EncodedUserInfo_decode(v_userInfo_1116_);
lean_dec_ref(v_userInfo_1116_);
return v_res_1117_;
}
}
uint8_t l_Std_Http_URI_EncodedQueryParam_encode___lam__0(uint8_t v___y_1118_){
_start:
{
uint8_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = 48;
v___x_1176_ = lean_uint8_dec_le(v___x_1175_, v___y_1118_);
if (v___x_1176_ == 0)
{
goto v___jp_1170_;
}
else
{
uint8_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = 57;
v___x_1178_ = lean_uint8_dec_le(v___y_1118_, v___x_1177_);
if (v___x_1178_ == 0)
{
goto v___jp_1170_;
}
else
{
goto v___jp_1119_;
}
}
v___jp_1119_:
{
uint8_t v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = 38;
v___x_1121_ = lean_uint8_dec_eq(v___y_1118_, v___x_1120_);
if (v___x_1121_ == 0)
{
uint8_t v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = 61;
v___x_1123_ = lean_uint8_dec_eq(v___y_1118_, v___x_1122_);
if (v___x_1123_ == 0)
{
uint8_t v___x_1124_; 
v___x_1124_ = 1;
return v___x_1124_;
}
else
{
return v___x_1121_;
}
}
else
{
uint8_t v___x_1125_; 
v___x_1125_ = 0;
return v___x_1125_;
}
}
v___jp_1126_:
{
uint8_t v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = 45;
v___x_1128_ = lean_uint8_dec_eq(v___y_1118_, v___x_1127_);
if (v___x_1128_ == 0)
{
uint8_t v___x_1129_; uint8_t v___x_1130_; 
v___x_1129_ = 46;
v___x_1130_ = lean_uint8_dec_eq(v___y_1118_, v___x_1129_);
if (v___x_1130_ == 0)
{
uint8_t v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = 95;
v___x_1132_ = lean_uint8_dec_eq(v___y_1118_, v___x_1131_);
if (v___x_1132_ == 0)
{
uint8_t v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = 126;
v___x_1134_ = lean_uint8_dec_eq(v___y_1118_, v___x_1133_);
if (v___x_1134_ == 0)
{
uint8_t v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = 33;
v___x_1136_ = lean_uint8_dec_eq(v___y_1118_, v___x_1135_);
if (v___x_1136_ == 0)
{
uint8_t v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = 36;
v___x_1138_ = lean_uint8_dec_eq(v___y_1118_, v___x_1137_);
if (v___x_1138_ == 0)
{
uint8_t v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = 38;
v___x_1140_ = lean_uint8_dec_eq(v___y_1118_, v___x_1139_);
if (v___x_1140_ == 0)
{
uint8_t v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = 39;
v___x_1142_ = lean_uint8_dec_eq(v___y_1118_, v___x_1141_);
if (v___x_1142_ == 0)
{
uint8_t v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = 40;
v___x_1144_ = lean_uint8_dec_eq(v___y_1118_, v___x_1143_);
if (v___x_1144_ == 0)
{
uint8_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = 41;
v___x_1146_ = lean_uint8_dec_eq(v___y_1118_, v___x_1145_);
if (v___x_1146_ == 0)
{
uint8_t v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = 42;
v___x_1148_ = lean_uint8_dec_eq(v___y_1118_, v___x_1147_);
if (v___x_1148_ == 0)
{
uint8_t v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = 43;
v___x_1150_ = lean_uint8_dec_eq(v___y_1118_, v___x_1149_);
if (v___x_1150_ == 0)
{
uint8_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = 44;
v___x_1152_ = lean_uint8_dec_eq(v___y_1118_, v___x_1151_);
if (v___x_1152_ == 0)
{
uint8_t v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = 59;
v___x_1154_ = lean_uint8_dec_eq(v___y_1118_, v___x_1153_);
if (v___x_1154_ == 0)
{
uint8_t v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = 61;
v___x_1156_ = lean_uint8_dec_eq(v___y_1118_, v___x_1155_);
if (v___x_1156_ == 0)
{
uint8_t v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = 58;
v___x_1158_ = lean_uint8_dec_eq(v___y_1118_, v___x_1157_);
if (v___x_1158_ == 0)
{
uint8_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = 64;
v___x_1160_ = lean_uint8_dec_eq(v___y_1118_, v___x_1159_);
if (v___x_1160_ == 0)
{
uint8_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = 47;
v___x_1162_ = lean_uint8_dec_eq(v___y_1118_, v___x_1161_);
if (v___x_1162_ == 0)
{
uint8_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = 63;
v___x_1164_ = lean_uint8_dec_eq(v___y_1118_, v___x_1163_);
if (v___x_1164_ == 0)
{
return v___x_1164_;
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
v___jp_1165_:
{
uint8_t v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = 65;
v___x_1167_ = lean_uint8_dec_le(v___x_1166_, v___y_1118_);
if (v___x_1167_ == 0)
{
goto v___jp_1126_;
}
else
{
uint8_t v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = 90;
v___x_1169_ = lean_uint8_dec_le(v___y_1118_, v___x_1168_);
if (v___x_1169_ == 0)
{
goto v___jp_1126_;
}
else
{
goto v___jp_1119_;
}
}
}
v___jp_1170_:
{
uint8_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = 97;
v___x_1172_ = lean_uint8_dec_le(v___x_1171_, v___y_1118_);
if (v___x_1172_ == 0)
{
goto v___jp_1165_;
}
else
{
uint8_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = 122;
v___x_1174_ = lean_uint8_dec_le(v___y_1118_, v___x_1173_);
if (v___x_1174_ == 0)
{
goto v___jp_1165_;
}
else
{
goto v___jp_1119_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_EncodedQueryParam_encode___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_1118_ = stack[0].m_num;
uint8_t v_res_1179_;
v_res_1179_ = l_Std_Http_URI_EncodedQueryParam_encode___lam__0(v___y_1118_);
stack->m_num = v_res_1179_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed(lean_object* v___y_1180_){
_start:
{
uint8_t v___y_363__boxed_1181_; uint8_t v_res_1182_; lean_object* v_r_1183_; 
v___y_363__boxed_1181_ = lean_unbox(v___y_1180_);
v_res_1182_ = l_Std_Http_URI_EncodedQueryParam_encode___lam__0(v___y_363__boxed_1181_);
v_r_1183_ = lean_box(v_res_1182_);
return v_r_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode(lean_object* v_s_1185_){
_start:
{
lean_object* v___f_1186_; lean_object* v___x_1187_; 
v___f_1186_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1187_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_1185_, v___f_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___boxed(lean_object* v_s_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Std_Http_URI_EncodedQueryParam_encode(v_s_1188_);
lean_dec_ref(v_s_1188_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f(lean_object* v_ba_1190_){
_start:
{
lean_object* v___f_1191_; lean_object* v___x_1192_; 
v___f_1191_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1192_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_1190_, v___f_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x21(lean_object* v_ba_1193_){
_start:
{
lean_object* v___f_1194_; lean_object* v___x_1195_; 
v___f_1194_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1195_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v_ba_1193_, v___f_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object* v_s_1196_){
_start:
{
lean_object* v___f_1197_; lean_object* v___x_1198_; 
v___f_1197_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1198_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_1196_, v___f_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f___boxed(lean_object* v_s_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_s_1199_);
lean_dec_ref(v_s_1199_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object* v_param_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_param_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode___boxed(lean_object* v_param_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Std_Http_URI_EncodedQueryParam_decode(v_param_1203_);
lean_dec_ref(v_param_1203_);
return v_res_1204_;
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
