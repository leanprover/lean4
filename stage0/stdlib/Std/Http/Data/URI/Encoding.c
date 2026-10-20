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
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedFragment_encode___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedFragment_encode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedFragment_encode___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedFragment_encode___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedUserInfo_encode___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedUserInfo_encode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedUserInfo_encode___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedUserInfo_encode___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryParam_encode___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedQueryParam_encode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedQueryParam_encode___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedQueryParam_encode___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_isEncodedChar(lean_object* v_rule_1_, uint8_t v_c_2_){
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
LEAN_EXPORT lean_object* l_Std_Http_URI_isEncodedChar___boxed(lean_object* v_rule_26_, lean_object* v_c_27_){
_start:
{
uint8_t v_c_boxed_28_; uint8_t v_res_29_; lean_object* v_r_30_; 
v_c_boxed_28_ = lean_unbox(v_c_27_);
v_res_29_ = l_Std_Http_URI_isEncodedChar(v_rule_26_, v_c_boxed_28_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isEncodedQueryChar(lean_object* v_rule_31_, uint8_t v_c_32_){
_start:
{
uint8_t v___x_33_; 
v___x_33_ = l_Std_Http_URI_isEncodedChar(v_rule_31_, v_c_32_);
if (v___x_33_ == 0)
{
uint8_t v___x_34_; uint8_t v___x_35_; 
v___x_34_ = 43;
v___x_35_ = lean_uint8_dec_eq(v_c_32_, v___x_34_);
return v___x_35_;
}
else
{
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isEncodedQueryChar___boxed(lean_object* v_rule_36_, lean_object* v_c_37_){
_start:
{
uint8_t v_c_boxed_38_; uint8_t v_res_39_; lean_object* v_r_40_; 
v_c_boxed_38_ = lean_unbox(v_c_37_);
v_res_39_ = l_Std_Http_URI_isEncodedQueryChar(v_rule_36_, v_c_boxed_38_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(lean_object* v_r_41_, uint8_t v___x_42_, uint8_t v_v_43_){
_start:
{
uint8_t v___x_44_; 
v___x_44_ = l_Std_Http_URI_isEncodedChar(v_r_41_, v_v_43_);
if (v___x_44_ == 0)
{
return v___x_42_;
}
else
{
uint8_t v___x_45_; 
v___x_45_ = 0;
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed(lean_object* v_r_46_, lean_object* v___x_47_, lean_object* v_v_48_){
_start:
{
uint8_t v___x_61__boxed_49_; uint8_t v_v_boxed_50_; uint8_t v_res_51_; lean_object* v_r_52_; 
v___x_61__boxed_49_ = lean_unbox(v___x_47_);
v_v_boxed_50_ = lean_unbox(v_v_48_);
v_res_51_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(v_r_46_, v___x_61__boxed_49_, v_v_boxed_50_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars(lean_object* v_r_72_, lean_object* v_s_73_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_74_ = lean_byte_array_data(v_s_73_);
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = lean_array_get_size(v___x_74_);
v___x_77_ = ((lean_object*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9));
v___x_78_ = lean_nat_dec_lt(v___x_75_, v___x_76_);
if (v___x_78_ == 0)
{
uint8_t v___x_79_; 
lean_dec_ref(v___x_74_);
lean_dec_ref(v_r_72_);
v___x_79_ = 1;
return v___x_79_;
}
else
{
if (v___x_78_ == 0)
{
lean_dec_ref(v___x_74_);
lean_dec_ref(v_r_72_);
return v___x_78_;
}
else
{
lean_object* v___x_80_; lean_object* v___f_81_; size_t v___x_82_; size_t v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_80_ = lean_box(v___x_78_);
v___f_81_ = lean_alloc_closure((void*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed), 3, 2);
lean_closure_set(v___f_81_, 0, v_r_72_);
lean_closure_set(v___f_81_, 1, v___x_80_);
v___x_82_ = ((size_t)0ULL);
v___x_83_ = lean_usize_of_nat(v___x_76_);
v___x_84_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_77_, v___f_81_, v___x_74_, v___x_82_, v___x_83_);
v___x_85_ = lean_unbox(v___x_84_);
lean_dec(v___x_84_);
if (v___x_85_ == 0)
{
return v___x_78_;
}
else
{
uint8_t v___x_86_; 
v___x_86_ = 0;
return v___x_86_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___boxed(lean_object* v_r_87_, lean_object* v_s_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_87_, v_s_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(lean_object* v_r_91_, uint8_t v___x_92_, uint8_t v_v_93_){
_start:
{
uint8_t v___x_94_; 
v___x_94_ = l_Std_Http_URI_isEncodedQueryChar(v_r_91_, v_v_93_);
if (v___x_94_ == 0)
{
return v___x_92_;
}
else
{
uint8_t v___x_95_; 
v___x_95_ = 0;
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed(lean_object* v_r_96_, lean_object* v___x_97_, lean_object* v_v_98_){
_start:
{
uint8_t v___x_61__boxed_99_; uint8_t v_v_boxed_100_; uint8_t v_res_101_; lean_object* v_r_102_; 
v___x_61__boxed_99_ = lean_unbox(v___x_97_);
v_v_boxed_100_ = lean_unbox(v_v_98_);
v_res_101_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(v_r_96_, v___x_61__boxed_99_, v_v_boxed_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(lean_object* v_r_103_, lean_object* v_s_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_105_ = lean_byte_array_data(v_s_104_);
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = lean_array_get_size(v___x_105_);
v___x_108_ = ((lean_object*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___closed__9));
v___x_109_ = lean_nat_dec_lt(v___x_106_, v___x_107_);
if (v___x_109_ == 0)
{
uint8_t v___x_110_; 
lean_dec_ref(v___x_105_);
lean_dec_ref(v_r_103_);
v___x_110_ = 1;
return v___x_110_;
}
else
{
if (v___x_109_ == 0)
{
lean_dec_ref(v___x_105_);
lean_dec_ref(v_r_103_);
return v___x_109_;
}
else
{
lean_object* v___x_111_; lean_object* v___f_112_; size_t v___x_113_; size_t v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_111_ = lean_box(v___x_109_);
v___f_112_ = lean_alloc_closure((void*)(l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed), 3, 2);
lean_closure_set(v___f_112_, 0, v_r_103_);
lean_closure_set(v___f_112_, 1, v___x_111_);
v___x_113_ = ((size_t)0ULL);
v___x_114_ = lean_usize_of_nat(v___x_107_);
v___x_115_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_108_, v___f_112_, v___x_105_, v___x_113_, v___x_114_);
v___x_116_ = lean_unbox(v___x_115_);
lean_dec(v___x_115_);
if (v___x_116_ == 0)
{
return v___x_109_;
}
else
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___boxed(lean_object* v_r_118_, lean_object* v_s_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_118_, v_s_119_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(lean_object* v_ba_122_, lean_object* v_i_123_){
_start:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = lean_byte_array_size(v_ba_122_);
v___x_129_ = lean_nat_dec_lt(v_i_123_, v___x_128_);
if (v___x_129_ == 0)
{
uint8_t v___x_130_; 
lean_dec(v_i_123_);
v___x_130_ = 1;
return v___x_130_;
}
else
{
uint8_t v_c_131_; uint8_t v___x_132_; uint8_t v___x_133_; 
v_c_131_ = lean_byte_array_fget(v_ba_122_, v_i_123_);
v___x_132_ = 37;
v___x_133_ = lean_uint8_dec_eq(v_c_131_, v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_add(v_i_123_, v___x_134_);
lean_dec(v_i_123_);
v_i_123_ = v___x_135_;
goto _start;
}
else
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_137_ = lean_unsigned_to_nat(2u);
v___x_138_ = lean_nat_add(v_i_123_, v___x_137_);
v___x_139_ = lean_nat_dec_lt(v___x_138_, v___x_128_);
if (v___x_139_ == 0)
{
lean_dec(v___x_138_);
lean_dec(v_i_123_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v_d1_142_; uint8_t v_d2_143_; uint8_t v___x_169_; uint8_t v___x_170_; 
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_add(v_i_123_, v___x_140_);
v_d1_142_ = lean_byte_array_fget(v_ba_122_, v___x_141_);
lean_dec(v___x_141_);
v_d2_143_ = lean_byte_array_fget(v_ba_122_, v___x_138_);
lean_dec(v___x_138_);
v___x_169_ = 48;
v___x_170_ = lean_uint8_dec_le(v___x_169_, v_d1_142_);
if (v___x_170_ == 0)
{
goto v___jp_164_;
}
else
{
uint8_t v___x_171_; uint8_t v___x_172_; 
v___x_171_ = 57;
v___x_172_ = lean_uint8_dec_le(v_d1_142_, v___x_171_);
if (v___x_172_ == 0)
{
goto v___jp_164_;
}
else
{
goto v___jp_154_;
}
}
v___jp_144_:
{
uint8_t v___x_145_; uint8_t v___x_146_; 
v___x_145_ = 65;
v___x_146_ = lean_uint8_dec_le(v___x_145_, v_d2_143_);
if (v___x_146_ == 0)
{
lean_dec(v_i_123_);
return v___x_146_;
}
else
{
uint8_t v___x_147_; uint8_t v___x_148_; 
v___x_147_ = 70;
v___x_148_ = lean_uint8_dec_le(v_d2_143_, v___x_147_);
if (v___x_148_ == 0)
{
lean_dec(v_i_123_);
return v___x_148_;
}
else
{
goto v___jp_124_;
}
}
}
v___jp_149_:
{
uint8_t v___x_150_; uint8_t v___x_151_; 
v___x_150_ = 97;
v___x_151_ = lean_uint8_dec_le(v___x_150_, v_d2_143_);
if (v___x_151_ == 0)
{
goto v___jp_144_;
}
else
{
uint8_t v___x_152_; uint8_t v___x_153_; 
v___x_152_ = 102;
v___x_153_ = lean_uint8_dec_le(v_d2_143_, v___x_152_);
if (v___x_153_ == 0)
{
goto v___jp_144_;
}
else
{
goto v___jp_124_;
}
}
}
v___jp_154_:
{
uint8_t v___x_155_; uint8_t v___x_156_; 
v___x_155_ = 48;
v___x_156_ = lean_uint8_dec_le(v___x_155_, v_d2_143_);
if (v___x_156_ == 0)
{
goto v___jp_149_;
}
else
{
uint8_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 57;
v___x_158_ = lean_uint8_dec_le(v_d2_143_, v___x_157_);
if (v___x_158_ == 0)
{
goto v___jp_149_;
}
else
{
goto v___jp_124_;
}
}
}
v___jp_159_:
{
uint8_t v___x_160_; uint8_t v___x_161_; 
v___x_160_ = 65;
v___x_161_ = lean_uint8_dec_le(v___x_160_, v_d1_142_);
if (v___x_161_ == 0)
{
lean_dec(v_i_123_);
return v___x_161_;
}
else
{
uint8_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = 70;
v___x_163_ = lean_uint8_dec_le(v_d1_142_, v___x_162_);
if (v___x_163_ == 0)
{
lean_dec(v_i_123_);
return v___x_163_;
}
else
{
goto v___jp_154_;
}
}
}
v___jp_164_:
{
uint8_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = 97;
v___x_166_ = lean_uint8_dec_le(v___x_165_, v_d1_142_);
if (v___x_166_ == 0)
{
goto v___jp_159_;
}
else
{
uint8_t v___x_167_; uint8_t v___x_168_; 
v___x_167_ = 102;
v___x_168_ = lean_uint8_dec_le(v_d1_142_, v___x_167_);
if (v___x_168_ == 0)
{
goto v___jp_159_;
}
else
{
goto v___jp_154_;
}
}
}
}
}
}
v___jp_124_:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(3u);
v___x_126_ = lean_nat_add(v_i_123_, v___x_125_);
lean_dec(v_i_123_);
v_i_123_ = v___x_126_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop___boxed(lean_object* v_ba_173_, lean_object* v_i_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_173_, v_i_174_);
lean_dec_ref(v_ba_173_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidPercentEncoding(lean_object* v_ba_177_){
_start:
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_177_, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidPercentEncoding___boxed(lean_object* v_ba_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_180_);
lean_dec_ref(v_ba_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_hexDigit(uint8_t v_n_183_){
_start:
{
uint8_t v___x_184_; uint8_t v___x_185_; 
v___x_184_ = 10;
v___x_185_ = lean_uint8_dec_lt(v_n_183_, v___x_184_);
if (v___x_185_ == 0)
{
uint8_t v___x_186_; uint8_t v___x_187_; uint8_t v___x_188_; 
v___x_186_ = lean_uint8_sub(v_n_183_, v___x_184_);
v___x_187_ = 65;
v___x_188_ = lean_uint8_add(v___x_186_, v___x_187_);
return v___x_188_;
}
else
{
uint8_t v___x_189_; uint8_t v___x_190_; 
v___x_189_ = 48;
v___x_190_ = lean_uint8_add(v_n_183_, v___x_189_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigit___boxed(lean_object* v_n_191_){
_start:
{
uint8_t v_n_boxed_192_; uint8_t v_res_193_; lean_object* v_r_194_; 
v_n_boxed_192_ = lean_unbox(v_n_191_);
v_res_193_ = l_Std_Http_URI_hexDigit(v_n_boxed_192_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f(uint8_t v_c_195_){
_start:
{
uint8_t v___x_218_; uint8_t v___x_219_; 
v___x_218_ = 48;
v___x_219_ = lean_uint8_dec_le(v___x_218_, v_c_195_);
if (v___x_219_ == 0)
{
goto v___jp_208_;
}
else
{
uint8_t v___x_220_; uint8_t v___x_221_; 
v___x_220_ = 57;
v___x_221_ = lean_uint8_dec_le(v_c_195_, v___x_220_);
if (v___x_221_ == 0)
{
goto v___jp_208_;
}
else
{
uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = lean_uint8_sub(v_c_195_, v___x_218_);
v___x_223_ = lean_box(v___x_222_);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
v___jp_196_:
{
uint8_t v___x_197_; uint8_t v___x_198_; 
v___x_197_ = 65;
v___x_198_ = lean_uint8_dec_le(v___x_197_, v_c_195_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
v___x_199_ = lean_box(0);
return v___x_199_;
}
else
{
uint8_t v___x_200_; uint8_t v___x_201_; 
v___x_200_ = 70;
v___x_201_ = lean_uint8_dec_le(v_c_195_, v___x_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; 
v___x_202_ = lean_box(0);
return v___x_202_;
}
else
{
uint8_t v___x_203_; uint8_t v___x_204_; uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_203_ = lean_uint8_sub(v_c_195_, v___x_197_);
v___x_204_ = 10;
v___x_205_ = lean_uint8_add(v___x_203_, v___x_204_);
v___x_206_ = lean_box(v___x_205_);
v___x_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
}
v___jp_208_:
{
uint8_t v___x_209_; uint8_t v___x_210_; 
v___x_209_ = 97;
v___x_210_ = lean_uint8_dec_le(v___x_209_, v_c_195_);
if (v___x_210_ == 0)
{
goto v___jp_196_;
}
else
{
uint8_t v___x_211_; uint8_t v___x_212_; 
v___x_211_ = 102;
v___x_212_ = lean_uint8_dec_le(v_c_195_, v___x_211_);
if (v___x_212_ == 0)
{
goto v___jp_196_;
}
else
{
uint8_t v___x_213_; uint8_t v___x_214_; uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_213_ = lean_uint8_sub(v_c_195_, v___x_209_);
v___x_214_ = 10;
v___x_215_ = lean_uint8_add(v___x_213_, v___x_214_);
v___x_216_ = lean_box(v___x_215_);
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f___boxed(lean_object* v_c_225_){
_start:
{
uint8_t v_c_boxed_226_; lean_object* v_res_227_; 
v_c_boxed_226_ = lean_unbox(v_c_225_);
v_res_227_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_c_boxed_226_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___redArg(){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_ByteArray_empty;
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___redArg___boxed(lean_object* v___dummy_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Std_Http_URI_EncodedString_empty___redArg();
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty(lean_object* v_r_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_ByteArray_empty;
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___boxed(lean_object* v_r_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_Http_URI_EncodedString_empty(v_r_234_);
lean_dec_ref(v_r_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___redArg(){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_ByteArray_empty;
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___redArg___boxed(lean_object* v___dummy_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_Http_URI_EncodedString_instInhabited___redArg();
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited(lean_object* v_r_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_ByteArray_empty;
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___boxed(lean_object* v_r_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Std_Http_URI_EncodedString_instInhabited(v_r_242_);
lean_dec_ref(v_r_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(lean_object* v_s_244_, uint8_t v_c_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_byte_array_push(v_s_244_, v_c_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg___boxed(lean_object* v_s_247_, lean_object* v_c_248_){
_start:
{
uint8_t v_c_boxed_249_; lean_object* v_res_250_; 
v_c_boxed_249_ = lean_unbox(v_c_248_);
v_res_250_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(v_s_247_, v_c_boxed_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(lean_object* v_r_251_, lean_object* v_s_252_, uint8_t v_c_253_, lean_object* v_h_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lean_byte_array_push(v_s_252_, v_c_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___boxed(lean_object* v_r_256_, lean_object* v_s_257_, lean_object* v_c_258_, lean_object* v_h_259_){
_start:
{
uint8_t v_c_boxed_260_; lean_object* v_res_261_; 
v_c_boxed_260_ = lean_unbox(v_c_258_);
v_res_261_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(v_r_256_, v_s_257_, v_c_boxed_260_, v_h_259_);
lean_dec_ref(v_r_256_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(uint8_t v_b_262_, lean_object* v_s_263_){
_start:
{
uint8_t v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; uint8_t v___x_267_; uint8_t v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; uint8_t v___x_271_; uint8_t v___x_272_; lean_object* v_ba_273_; 
v___x_264_ = 37;
v___x_265_ = lean_byte_array_push(v_s_263_, v___x_264_);
v___x_266_ = 4;
v___x_267_ = lean_uint8_shift_right(v_b_262_, v___x_266_);
v___x_268_ = l_Std_Http_URI_hexDigit(v___x_267_);
v___x_269_ = lean_byte_array_push(v___x_265_, v___x_268_);
v___x_270_ = 15;
v___x_271_ = lean_uint8_land(v_b_262_, v___x_270_);
v___x_272_ = l_Std_Http_URI_hexDigit(v___x_271_);
v_ba_273_ = lean_byte_array_push(v___x_269_, v___x_272_);
return v_ba_273_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg___boxed(lean_object* v_b_274_, lean_object* v_s_275_){
_start:
{
uint8_t v_b_boxed_276_; lean_object* v_res_277_; 
v_b_boxed_276_ = lean_unbox(v_b_274_);
v_res_277_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_boxed_276_, v_s_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(lean_object* v_r_278_, uint8_t v_b_279_, lean_object* v_s_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_279_, v_s_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___boxed(lean_object* v_r_282_, lean_object* v_b_283_, lean_object* v_s_284_){
_start:
{
uint8_t v_b_boxed_285_; lean_object* v_res_286_; 
v_b_boxed_285_ = lean_unbox(v_b_283_);
v_res_286_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(v_r_282_, v_b_boxed_285_, v_s_284_);
lean_dec_ref(v_r_282_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(lean_object* v_r_287_, lean_object* v_as_288_, size_t v_i_289_, size_t v_stop_290_, lean_object* v_b_291_){
_start:
{
lean_object* v___y_293_; uint8_t v___x_297_; 
v___x_297_ = lean_usize_dec_eq(v_i_289_, v_stop_290_);
if (v___x_297_ == 0)
{
uint8_t v___x_298_; uint8_t v___x_299_; uint8_t v___x_300_; 
v___x_298_ = lean_byte_array_uget(v_as_288_, v_i_289_);
v___x_299_ = 128;
v___x_300_ = lean_uint8_dec_lt(v___x_298_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
v___x_301_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_298_, v_b_291_);
v___y_293_ = v___x_301_;
goto v___jp_292_;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_302_ = lean_box(v___x_298_);
lean_inc_ref(v_r_287_);
v___x_303_ = lean_apply_1(v_r_287_, v___x_302_);
v___x_304_ = lean_unbox(v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
v___x_305_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_298_, v_b_291_);
v___y_293_ = v___x_305_;
goto v___jp_292_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_byte_array_push(v_b_291_, v___x_298_);
v___y_293_ = v___x_306_;
goto v___jp_292_;
}
}
}
else
{
lean_dec_ref(v_r_287_);
return v_b_291_;
}
v___jp_292_:
{
size_t v___x_294_; size_t v___x_295_; 
v___x_294_ = ((size_t)1ULL);
v___x_295_ = lean_usize_add(v_i_289_, v___x_294_);
v_i_289_ = v___x_295_;
v_b_291_ = v___y_293_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0___boxed(lean_object* v_r_307_, lean_object* v_as_308_, lean_object* v_i_309_, lean_object* v_stop_310_, lean_object* v_b_311_){
_start:
{
size_t v_i_boxed_312_; size_t v_stop_boxed_313_; lean_object* v_res_314_; 
v_i_boxed_312_ = lean_unbox_usize(v_i_309_);
lean_dec(v_i_309_);
v_stop_boxed_313_ = lean_unbox_usize(v_stop_310_);
lean_dec(v_stop_310_);
v_res_314_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_307_, v_as_308_, v_i_boxed_312_, v_stop_boxed_313_, v_b_311_);
lean_dec_ref(v_as_308_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode(lean_object* v_r_315_, lean_object* v_s_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_317_ = l_ByteArray_empty;
v___x_318_ = lean_string_to_utf8(v_s_316_);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_byte_array_size(v___x_318_);
v___x_321_ = lean_nat_dec_lt(v___x_319_, v___x_320_);
if (v___x_321_ == 0)
{
lean_dec_ref(v___x_318_);
lean_dec_ref(v_r_315_);
return v___x_317_;
}
else
{
size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; 
v___x_322_ = ((size_t)0ULL);
v___x_323_ = lean_usize_of_nat(v___x_320_);
v___x_324_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_315_, v___x_318_, v___x_322_, v___x_323_, v___x_317_);
lean_dec_ref(v___x_318_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x3f(lean_object* v_r_325_, lean_object* v_ba_326_){
_start:
{
uint8_t v___x_327_; 
lean_inc_ref(v_ba_326_);
v___x_327_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_325_, v_ba_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; 
lean_dec_ref(v_ba_326_);
v___x_328_ = lean_box(0);
return v___x_328_;
}
else
{
uint8_t v___x_329_; 
v___x_329_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_326_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
lean_dec_ref(v_ba_326_);
v___x_330_ = lean_box(0);
return v___x_330_;
}
else
{
lean_object* v___x_331_; 
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v_ba_326_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_332_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = l_ByteArray_empty;
v___x_334_ = lean_panic_fn_borrowed(v___x_333_, v_msg_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(lean_object* v_r_335_, lean_object* v_msg_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v_msg_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_338_, lean_object* v_msg_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(v_r_338_, v_msg_339_);
lean_dec_ref(v_r_338_);
return v_res_340_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_344_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2));
v___x_345_ = lean_unsigned_to_nat(12u);
v___x_346_ = lean_unsigned_to_nat(319u);
v___x_347_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1));
v___x_348_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_349_ = l_mkPanicMessageWithDecl(v___x_348_, v___x_347_, v___x_346_, v___x_345_, v___x_344_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x21(lean_object* v_r_350_, lean_object* v_ba_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_350_, v_ba_351_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_obj_once(&l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3, &l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3_once, _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3);
v___x_354_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v___x_353_);
return v___x_354_;
}
else
{
lean_object* v_val_355_; 
v_val_355_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_val_355_);
lean_dec_ref_known(v___x_352_, 1);
return v_val_355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f(lean_object* v_r_356_, lean_object* v_s_357_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_string_to_utf8(v_s_357_);
v___x_359_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_356_, v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21(lean_object* v_r_360_, lean_object* v_s_361_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_string_to_utf8(v_s_361_);
v___x_363_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v_r_360_, v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg(lean_object* v_ba_364_){
_start:
{
lean_inc_ref(v_ba_364_);
return v_ba_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg___boxed(lean_object* v_ba_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Std_Http_URI_EncodedString_new___redArg(v_ba_365_);
lean_dec_ref(v_ba_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new(lean_object* v_r_367_, lean_object* v_ba_368_, lean_object* v_valid_369_, lean_object* v___validEncoding_370_){
_start:
{
lean_inc_ref(v_ba_368_);
return v_ba_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___boxed(lean_object* v_r_371_, lean_object* v_ba_372_, lean_object* v_valid_373_, lean_object* v___validEncoding_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_Http_URI_EncodedString_new(v_r_371_, v_ba_372_, v_valid_373_, v___validEncoding_374_);
lean_dec_ref(v_ba_372_);
lean_dec_ref(v_r_371_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg___lam__0(lean_object* v_es_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_string_from_utf8_unchecked(v_es_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg(){
_start:
{
lean_object* v___f_380_; 
v___f_380_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instToString___redArg___closed__0));
return v___f_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg___boxed(lean_object* v___dummy_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Std_Http_URI_EncodedString_instToString___redArg();
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString(lean_object* v_r_383_){
_start:
{
lean_object* v___f_384_; 
v___f_384_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instToString___redArg___closed__0));
return v___f_384_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___boxed(lean_object* v_r_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Std_Http_URI_EncodedString_instToString(v_r_385_);
lean_dec_ref(v_r_385_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(lean_object* v_len_387_, lean_object* v_rawBytes_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_fst_390_; lean_object* v_snd_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_449_; 
v_fst_390_ = lean_ctor_get(v_a_389_, 0);
v_snd_391_ = lean_ctor_get(v_a_389_, 1);
v_isSharedCheck_449_ = !lean_is_exclusive(v_a_389_);
if (v_isSharedCheck_449_ == 0)
{
v___x_393_ = v_a_389_;
v_isShared_394_ = v_isSharedCheck_449_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_snd_391_);
lean_inc(v_fst_390_);
lean_dec(v_a_389_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_449_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
uint8_t v___x_395_; 
v___x_395_ = lean_nat_dec_lt(v_snd_391_, v_len_387_);
if (v___x_395_ == 0)
{
lean_object* v___x_397_; 
if (v_isShared_394_ == 0)
{
v___x_397_ = v___x_393_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_fst_390_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_snd_391_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
else
{
uint8_t v_percent_399_; uint8_t v___x_400_; uint8_t v___x_409_; 
v_percent_399_ = 37;
v___x_400_ = lean_byte_array_fget(v_rawBytes_388_, v_snd_391_);
v___x_409_ = lean_uint8_dec_eq(v___x_400_, v_percent_399_);
if (v___x_409_ == 0)
{
goto v___jp_401_;
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_410_ = lean_unsigned_to_nat(1u);
v___x_411_ = lean_nat_add(v_snd_391_, v___x_410_);
v___x_412_ = lean_nat_dec_lt(v___x_411_, v_len_387_);
if (v___x_412_ == 0)
{
lean_dec(v___x_411_);
goto v___jp_401_;
}
else
{
uint8_t v___x_413_; lean_object* v___x_414_; 
lean_del_object(v___x_393_);
v___x_413_ = lean_byte_array_fget(v_rawBytes_388_, v___x_411_);
lean_dec(v___x_411_);
v___x_414_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_413_);
if (lean_obj_tag(v___x_414_) == 1)
{
lean_object* v_val_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v_val_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_val_415_);
lean_dec_ref_known(v___x_414_, 1);
v___x_416_ = lean_unsigned_to_nat(2u);
v___x_417_ = lean_nat_add(v_snd_391_, v___x_416_);
v___x_418_ = lean_nat_dec_lt(v___x_417_, v_len_387_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec(v_val_415_);
lean_dec(v_snd_391_);
v___x_419_ = lean_byte_array_push(v_fst_390_, v___x_400_);
v___x_420_ = lean_byte_array_push(v___x_419_, v___x_413_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_417_);
v_a_389_ = v___x_421_;
goto _start;
}
else
{
uint8_t v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_byte_array_fget(v_rawBytes_388_, v___x_417_);
lean_dec(v___x_417_);
v___x_424_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_423_);
if (lean_obj_tag(v___x_424_) == 1)
{
lean_object* v_val_425_; uint8_t v___x_426_; uint8_t v___x_427_; uint8_t v___x_428_; uint8_t v___x_429_; uint8_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_val_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_val_425_);
lean_dec_ref_known(v___x_424_, 1);
v___x_426_ = 4;
v___x_427_ = lean_unbox(v_val_415_);
lean_dec(v_val_415_);
v___x_428_ = lean_uint8_shift_left(v___x_427_, v___x_426_);
v___x_429_ = lean_unbox(v_val_425_);
lean_dec(v_val_425_);
v___x_430_ = lean_uint8_add(v___x_428_, v___x_429_);
v___x_431_ = lean_byte_array_push(v_fst_390_, v___x_430_);
v___x_432_ = lean_unsigned_to_nat(3u);
v___x_433_ = lean_nat_add(v_snd_391_, v___x_432_);
lean_dec(v_snd_391_);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_431_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v_a_389_ = v___x_434_;
goto _start;
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec(v___x_424_);
lean_dec(v_val_415_);
v___x_436_ = lean_byte_array_push(v_fst_390_, v___x_400_);
v___x_437_ = lean_byte_array_push(v___x_436_, v___x_413_);
v___x_438_ = lean_byte_array_push(v___x_437_, v___x_423_);
v___x_439_ = lean_unsigned_to_nat(3u);
v___x_440_ = lean_nat_add(v_snd_391_, v___x_439_);
lean_dec(v_snd_391_);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_438_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v_a_389_ = v___x_441_;
goto _start;
}
}
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec(v___x_414_);
v___x_443_ = lean_byte_array_push(v_fst_390_, v___x_400_);
v___x_444_ = lean_byte_array_push(v___x_443_, v___x_413_);
v___x_445_ = lean_unsigned_to_nat(2u);
v___x_446_ = lean_nat_add(v_snd_391_, v___x_445_);
lean_dec(v_snd_391_);
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_444_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v_a_389_ = v___x_447_;
goto _start;
}
}
}
v___jp_401_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_402_ = lean_byte_array_push(v_fst_390_, v___x_400_);
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_nat_add(v_snd_391_, v___x_403_);
lean_dec(v_snd_391_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 1, v___x_404_);
lean_ctor_set(v___x_393_, 0, v___x_402_);
v___x_406_ = v___x_393_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_404_);
v___x_406_ = v_reuseFailAlloc_408_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
v_a_389_ = v___x_406_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg___boxed(lean_object* v_len_450_, lean_object* v_rawBytes_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_450_, v_rawBytes_451_, v_a_452_);
lean_dec_ref(v_rawBytes_451_);
lean_dec(v_len_450_);
return v_res_453_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0(void){
_start:
{
lean_object* v_i_454_; lean_object* v_decoded_455_; lean_object* v___x_456_; 
v_i_454_ = lean_unsigned_to_nat(0u);
v_decoded_455_ = l_ByteArray_empty;
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v_decoded_455_);
lean_ctor_set(v___x_456_, 1, v_i_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg(lean_object* v_es_457_){
_start:
{
lean_object* v_len_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v_fst_461_; uint8_t v___x_462_; 
v_len_458_ = lean_byte_array_size(v_es_457_);
v___x_459_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_460_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_458_, v_es_457_, v___x_459_);
v_fst_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_fst_461_);
lean_dec_ref(v___x_460_);
v___x_462_ = lean_string_validate_utf8(v_fst_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
lean_dec(v_fst_461_);
v___x_463_ = lean_box(0);
return v___x_463_;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_string_from_utf8_unchecked(v_fst_461_);
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg___boxed(lean_object* v_es_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_466_);
lean_dec_ref(v_es_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode(lean_object* v_r_468_, lean_object* v_es_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___boxed(lean_object* v_r_471_, lean_object* v_es_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Std_Http_URI_EncodedString_decode(v_r_471_, v_es_472_);
lean_dec_ref(v_es_472_);
lean_dec_ref(v_r_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(lean_object* v_len_474_, lean_object* v_rawBytes_475_, lean_object* v_inst_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_474_, v_rawBytes_475_, v_a_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___boxed(lean_object* v_len_479_, lean_object* v_rawBytes_480_, lean_object* v_inst_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(v_len_479_, v_rawBytes_480_, v_inst_481_, v_a_482_);
lean_dec_ref(v_rawBytes_480_);
lean_dec(v_len_479_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0(lean_object* v_es_484_, lean_object* v_n_485_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_string_from_utf8_unchecked(v_es_484_);
v___x_487_ = l_String_quote(v___x_486_);
v___x_488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0___boxed(lean_object* v_es_489_, lean_object* v_n_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0(v_es_489_, v_n_490_);
lean_dec(v_n_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg(){
_start:
{
lean_object* v___f_494_; 
v___f_494_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___boxed(lean_object* v___dummy_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Std_Http_URI_EncodedString_instRepr___redArg();
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr(lean_object* v_r_497_){
_start:
{
lean_object* v___f_498_; 
v___f_498_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___boxed(lean_object* v_r_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_Http_URI_EncodedString_instRepr(v_r_499_);
lean_dec_ref(v_r_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___redArg(){
_start:
{
lean_object* v___f_503_; 
v___f_503_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_503_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___redArg___boxed(lean_object* v___dummy_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Std_Http_URI_EncodedString_instBEq___redArg();
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq(lean_object* v_r_506_){
_start:
{
lean_object* v___f_507_; 
v___f_507_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___boxed(lean_object* v_r_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_Http_URI_EncodedString_instBEq(v_r_508_);
lean_dec_ref(v_r_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___redArg(){
_start:
{
lean_object* v___f_512_; 
v___f_512_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___redArg___boxed(lean_object* v___dummy_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_Http_URI_EncodedString_instHashable___redArg();
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable(lean_object* v_r_515_){
_start:
{
lean_object* v___f_516_; 
v___f_516_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_516_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___boxed(lean_object* v_r_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_Http_URI_EncodedString_instHashable(v_r_517_);
lean_dec_ref(v_r_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___redArg(){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_ByteArray_empty;
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___redArg___boxed(lean_object* v___dummy_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Std_Http_URI_EncodedQueryString_empty___redArg();
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty(lean_object* v_r_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_ByteArray_empty;
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___boxed(lean_object* v_r_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_Http_URI_EncodedQueryString_empty(v_r_525_);
lean_dec_ref(v_r_525_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___redArg(){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_ByteArray_empty;
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___redArg___boxed(lean_object* v___dummy_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Std_Http_URI_EncodedQueryString_instInhabited___redArg();
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited(lean_object* v_r_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_ByteArray_empty;
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___boxed(lean_object* v_r_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_Http_URI_EncodedQueryString_instInhabited(v_r_533_);
lean_dec_ref(v_r_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(lean_object* v_s_535_, uint8_t v_c_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = lean_byte_array_push(v_s_535_, v_c_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg___boxed(lean_object* v_s_538_, lean_object* v_c_539_){
_start:
{
uint8_t v_c_boxed_540_; lean_object* v_res_541_; 
v_c_boxed_540_ = lean_unbox(v_c_539_);
v_res_541_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(v_s_538_, v_c_boxed_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(lean_object* v_r_542_, lean_object* v_s_543_, uint8_t v_c_544_, lean_object* v_h_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lean_byte_array_push(v_s_543_, v_c_544_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___boxed(lean_object* v_r_547_, lean_object* v_s_548_, lean_object* v_c_549_, lean_object* v_h_550_){
_start:
{
uint8_t v_c_boxed_551_; lean_object* v_res_552_; 
v_c_boxed_551_ = lean_unbox(v_c_549_);
v_res_552_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(v_r_547_, v_s_548_, v_c_boxed_551_, v_h_550_);
lean_dec_ref(v_r_547_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(lean_object* v_ba_553_, lean_object* v_r_554_){
_start:
{
uint8_t v___x_555_; 
lean_inc_ref(v_ba_553_);
v___x_555_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_554_, v_ba_553_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
lean_dec_ref(v_ba_553_);
v___x_556_ = lean_box(0);
return v___x_556_;
}
else
{
uint8_t v___x_557_; 
v___x_557_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_553_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
lean_dec_ref(v_ba_553_);
v___x_558_ = lean_box(0);
return v___x_558_;
}
else
{
lean_object* v___x_559_; 
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v_ba_553_);
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = l_ByteArray_empty;
v___x_562_ = lean_panic_fn_borrowed(v___x_561_, v_msg_560_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(lean_object* v_r_563_, lean_object* v_msg_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v_msg_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_566_, lean_object* v_msg_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(v_r_566_, v_msg_567_);
lean_dec_ref(v_r_566_);
return v_res_568_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_571_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1));
v___x_572_ = lean_unsigned_to_nat(12u);
v___x_573_ = lean_unsigned_to_nat(437u);
v___x_574_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0));
v___x_575_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_576_ = l_mkPanicMessageWithDecl(v___x_575_, v___x_574_, v___x_573_, v___x_572_, v___x_571_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(lean_object* v_ba_577_, lean_object* v_r_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_577_, v_r_578_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_obj_once(&l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2, &l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2_once, _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2);
v___x_581_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v___x_580_);
return v___x_581_;
}
else
{
lean_object* v_val_582_; 
v_val_582_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_val_582_);
lean_dec_ref_known(v___x_579_, 1);
return v_val_582_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f(lean_object* v_s_583_, lean_object* v_r_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = lean_string_to_utf8(v_s_583_);
v___x_586_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v___x_585_, v_r_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21(lean_object* v_s_587_, lean_object* v_r_588_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_string_to_utf8(v_s_587_);
v___x_590_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v___x_589_, v_r_588_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg(lean_object* v_ba_591_){
_start:
{
lean_inc_ref(v_ba_591_);
return v_ba_591_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg___boxed(lean_object* v_ba_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Std_Http_URI_EncodedQueryString_new___redArg(v_ba_592_);
lean_dec_ref(v_ba_592_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new(lean_object* v_r_594_, lean_object* v_ba_595_, lean_object* v_valid_596_, lean_object* v___validEncoding_597_){
_start:
{
lean_inc_ref(v_ba_595_);
return v_ba_595_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___boxed(lean_object* v_r_598_, lean_object* v_ba_599_, lean_object* v_valid_600_, lean_object* v___validEncoding_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_Http_URI_EncodedQueryString_new(v_r_598_, v_ba_599_, v_valid_600_, v___validEncoding_601_);
lean_dec_ref(v_ba_599_);
lean_dec_ref(v_r_598_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(uint8_t v_b_603_, lean_object* v_s_604_){
_start:
{
uint8_t v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; uint8_t v___x_608_; uint8_t v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; uint8_t v___x_612_; uint8_t v___x_613_; lean_object* v_ba_614_; 
v___x_605_ = 37;
v___x_606_ = lean_byte_array_push(v_s_604_, v___x_605_);
v___x_607_ = 4;
v___x_608_ = lean_uint8_shift_right(v_b_603_, v___x_607_);
v___x_609_ = l_Std_Http_URI_hexDigit(v___x_608_);
v___x_610_ = lean_byte_array_push(v___x_606_, v___x_609_);
v___x_611_ = 15;
v___x_612_ = lean_uint8_land(v_b_603_, v___x_611_);
v___x_613_ = l_Std_Http_URI_hexDigit(v___x_612_);
v_ba_614_ = lean_byte_array_push(v___x_610_, v___x_613_);
return v_ba_614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg___boxed(lean_object* v_b_615_, lean_object* v_s_616_){
_start:
{
uint8_t v_b_boxed_617_; lean_object* v_res_618_; 
v_b_boxed_617_ = lean_unbox(v_b_615_);
v_res_618_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_boxed_617_, v_s_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(lean_object* v_r_619_, uint8_t v_b_620_, lean_object* v_s_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_620_, v_s_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___boxed(lean_object* v_r_623_, lean_object* v_b_624_, lean_object* v_s_625_){
_start:
{
uint8_t v_b_boxed_626_; lean_object* v_res_627_; 
v_b_boxed_626_ = lean_unbox(v_b_624_);
v_res_627_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(v_r_623_, v_b_boxed_626_, v_s_625_);
lean_dec_ref(v_r_623_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(lean_object* v_r_628_, lean_object* v_as_629_, size_t v_i_630_, size_t v_stop_631_, lean_object* v_b_632_){
_start:
{
lean_object* v___y_634_; uint8_t v___x_638_; 
v___x_638_ = lean_usize_dec_eq(v_i_630_, v_stop_631_);
if (v___x_638_ == 0)
{
uint8_t v___x_639_; uint8_t v___x_646_; uint8_t v___x_647_; 
v___x_639_ = lean_byte_array_uget(v_as_629_, v_i_630_);
v___x_646_ = 128;
v___x_647_ = lean_uint8_dec_lt(v___x_639_, v___x_646_);
if (v___x_647_ == 0)
{
goto v___jp_640_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_648_ = lean_box(v___x_639_);
lean_inc_ref(v_r_628_);
v___x_649_ = lean_apply_1(v_r_628_, v___x_648_);
v___x_650_ = lean_unbox(v___x_649_);
if (v___x_650_ == 0)
{
goto v___jp_640_;
}
else
{
lean_object* v___x_651_; 
v___x_651_ = lean_byte_array_push(v_b_632_, v___x_639_);
v___y_634_ = v___x_651_;
goto v___jp_633_;
}
}
v___jp_640_:
{
uint8_t v___x_641_; uint8_t v___x_642_; 
v___x_641_ = 32;
v___x_642_ = lean_uint8_dec_eq(v___x_639_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
v___x_643_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v___x_639_, v_b_632_);
v___y_634_ = v___x_643_;
goto v___jp_633_;
}
else
{
uint8_t v___x_644_; lean_object* v___x_645_; 
v___x_644_ = 43;
v___x_645_ = lean_byte_array_push(v_b_632_, v___x_644_);
v___y_634_ = v___x_645_;
goto v___jp_633_;
}
}
}
else
{
lean_dec_ref(v_r_628_);
return v_b_632_;
}
v___jp_633_:
{
size_t v___x_635_; size_t v___x_636_; 
v___x_635_ = ((size_t)1ULL);
v___x_636_ = lean_usize_add(v_i_630_, v___x_635_);
v_i_630_ = v___x_636_;
v_b_632_ = v___y_634_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___boxed(lean_object* v_r_652_, lean_object* v_as_653_, lean_object* v_i_654_, lean_object* v_stop_655_, lean_object* v_b_656_){
_start:
{
size_t v_i_boxed_657_; size_t v_stop_boxed_658_; lean_object* v_res_659_; 
v_i_boxed_657_ = lean_unbox_usize(v_i_654_);
lean_dec(v_i_654_);
v_stop_boxed_658_ = lean_unbox_usize(v_stop_655_);
lean_dec(v_stop_655_);
v_res_659_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_652_, v_as_653_, v_i_boxed_657_, v_stop_boxed_658_, v_b_656_);
lean_dec_ref(v_as_653_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode(lean_object* v_s_660_, lean_object* v_r_661_){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_662_ = l_ByteArray_empty;
v___x_663_ = lean_string_to_utf8(v_s_660_);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_byte_array_size(v___x_663_);
v___x_666_ = lean_nat_dec_lt(v___x_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_dec_ref(v___x_663_);
lean_dec_ref(v_r_661_);
return v___x_662_;
}
else
{
size_t v___x_667_; size_t v___x_668_; lean_object* v___x_669_; 
v___x_667_ = ((size_t)0ULL);
v___x_668_ = lean_usize_of_nat(v___x_665_);
v___x_669_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_661_, v___x_663_, v___x_667_, v___x_668_, v___x_662_);
lean_dec_ref(v___x_663_);
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___redArg(lean_object* v_es_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = lean_string_from_utf8_unchecked(v_es_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString(lean_object* v_r_672_, lean_object* v_es_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = lean_string_from_utf8_unchecked(v_es_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___boxed(lean_object* v_r_675_, lean_object* v_es_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_Http_URI_EncodedQueryString_toString(v_r_675_, v_es_676_);
lean_dec_ref(v_r_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(lean_object* v_len_678_, lean_object* v_rawBytes_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_fst_681_; lean_object* v_snd_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_748_; 
v_fst_681_ = lean_ctor_get(v_a_680_, 0);
v_snd_682_ = lean_ctor_get(v_a_680_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v_a_680_);
if (v_isSharedCheck_748_ == 0)
{
v___x_684_ = v_a_680_;
v_isShared_685_ = v_isSharedCheck_748_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_snd_682_);
lean_inc(v_fst_681_);
lean_dec(v_a_680_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_748_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
uint8_t v___x_686_; 
v___x_686_ = lean_nat_dec_lt(v_snd_682_, v_len_678_);
if (v___x_686_ == 0)
{
lean_object* v___x_688_; 
if (v_isShared_685_ == 0)
{
v___x_688_ = v___x_684_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_fst_681_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_snd_682_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
else
{
uint8_t v_plus_690_; uint8_t v___x_691_; uint8_t v___x_700_; 
v_plus_690_ = 43;
v___x_691_ = lean_byte_array_fget(v_rawBytes_679_, v_snd_682_);
v___x_700_ = lean_uint8_dec_eq(v___x_691_, v_plus_690_);
if (v___x_700_ == 0)
{
uint8_t v_percent_701_; uint8_t v___x_702_; 
v_percent_701_ = 37;
v___x_702_ = lean_uint8_dec_eq(v___x_691_, v_percent_701_);
if (v___x_702_ == 0)
{
goto v___jp_692_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = lean_nat_add(v_snd_682_, v___x_703_);
v___x_705_ = lean_nat_dec_lt(v___x_704_, v_len_678_);
if (v___x_705_ == 0)
{
lean_dec(v___x_704_);
goto v___jp_692_;
}
else
{
uint8_t v___x_706_; lean_object* v___x_707_; 
lean_del_object(v___x_684_);
v___x_706_ = lean_byte_array_fget(v_rawBytes_679_, v___x_704_);
lean_dec(v___x_704_);
v___x_707_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_706_);
if (lean_obj_tag(v___x_707_) == 1)
{
lean_object* v_val_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_val_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_val_708_);
lean_dec_ref_known(v___x_707_, 1);
v___x_709_ = lean_unsigned_to_nat(2u);
v___x_710_ = lean_nat_add(v_snd_682_, v___x_709_);
v___x_711_ = lean_nat_dec_lt(v___x_710_, v_len_678_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec(v_val_708_);
lean_dec(v_snd_682_);
v___x_712_ = lean_byte_array_push(v_fst_681_, v___x_691_);
v___x_713_ = lean_byte_array_push(v___x_712_, v___x_706_);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___x_710_);
v_a_680_ = v___x_714_;
goto _start;
}
else
{
uint8_t v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_byte_array_fget(v_rawBytes_679_, v___x_710_);
lean_dec(v___x_710_);
v___x_717_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_716_);
if (lean_obj_tag(v___x_717_) == 1)
{
lean_object* v_val_718_; uint8_t v___x_719_; uint8_t v___x_720_; uint8_t v___x_721_; uint8_t v___x_722_; uint8_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v_val_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_val_718_);
lean_dec_ref_known(v___x_717_, 1);
v___x_719_ = 4;
v___x_720_ = lean_unbox(v_val_708_);
lean_dec(v_val_708_);
v___x_721_ = lean_uint8_shift_left(v___x_720_, v___x_719_);
v___x_722_ = lean_unbox(v_val_718_);
lean_dec(v_val_718_);
v___x_723_ = lean_uint8_add(v___x_721_, v___x_722_);
v___x_724_ = lean_byte_array_push(v_fst_681_, v___x_723_);
v___x_725_ = lean_unsigned_to_nat(3u);
v___x_726_ = lean_nat_add(v_snd_682_, v___x_725_);
lean_dec(v_snd_682_);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_724_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v_a_680_ = v___x_727_;
goto _start;
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
lean_dec(v___x_717_);
lean_dec(v_val_708_);
v___x_729_ = lean_byte_array_push(v_fst_681_, v___x_691_);
v___x_730_ = lean_byte_array_push(v___x_729_, v___x_706_);
v___x_731_ = lean_byte_array_push(v___x_730_, v___x_716_);
v___x_732_ = lean_unsigned_to_nat(3u);
v___x_733_ = lean_nat_add(v_snd_682_, v___x_732_);
lean_dec(v_snd_682_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_731_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v_a_680_ = v___x_734_;
goto _start;
}
}
}
else
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
lean_dec(v___x_707_);
v___x_736_ = lean_byte_array_push(v_fst_681_, v___x_691_);
v___x_737_ = lean_byte_array_push(v___x_736_, v___x_706_);
v___x_738_ = lean_unsigned_to_nat(2u);
v___x_739_ = lean_nat_add(v_snd_682_, v___x_738_);
lean_dec(v_snd_682_);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_737_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v_a_680_ = v___x_740_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
lean_del_object(v___x_684_);
v___x_742_ = 32;
v___x_743_ = lean_byte_array_push(v_fst_681_, v___x_742_);
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = lean_nat_add(v_snd_682_, v___x_744_);
lean_dec(v_snd_682_);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_743_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v_a_680_ = v___x_746_;
goto _start;
}
v___jp_692_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_693_ = lean_byte_array_push(v_fst_681_, v___x_691_);
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = lean_nat_add(v_snd_682_, v___x_694_);
lean_dec(v_snd_682_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_695_);
lean_ctor_set(v___x_684_, 0, v___x_693_);
v___x_697_ = v___x_684_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v___x_695_);
v___x_697_ = v_reuseFailAlloc_699_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
v_a_680_ = v___x_697_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg___boxed(lean_object* v_len_749_, lean_object* v_rawBytes_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_749_, v_rawBytes_750_, v_a_751_);
lean_dec_ref(v_rawBytes_750_);
lean_dec(v_len_749_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg(lean_object* v_es_753_){
_start:
{
lean_object* v_len_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v_fst_757_; uint8_t v___x_758_; 
v_len_754_ = lean_byte_array_size(v_es_753_);
v___x_755_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_756_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_754_, v_es_753_, v___x_755_);
v_fst_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_fst_757_);
lean_dec_ref(v___x_756_);
v___x_758_ = lean_string_validate_utf8(v_fst_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
lean_dec(v_fst_757_);
v___x_759_ = lean_box(0);
return v___x_759_;
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_string_from_utf8_unchecked(v_fst_757_);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg___boxed(lean_object* v_es_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_762_);
lean_dec_ref(v_es_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode(lean_object* v_r_764_, lean_object* v_es_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___boxed(lean_object* v_r_767_, lean_object* v_es_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Std_Http_URI_EncodedQueryString_decode(v_r_767_, v_es_768_);
lean_dec_ref(v_es_768_);
lean_dec_ref(v_r_767_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(lean_object* v_len_770_, lean_object* v_rawBytes_771_, lean_object* v_inst_772_, lean_object* v_a_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_770_, v_rawBytes_771_, v_a_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___boxed(lean_object* v_len_775_, lean_object* v_rawBytes_776_, lean_object* v_inst_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(v_len_775_, v_rawBytes_776_, v_inst_777_, v_a_778_);
lean_dec_ref(v_rawBytes_776_);
lean_dec(v_len_775_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringEncodedQueryString(lean_object* v_r_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = lean_alloc_closure((void*)(l_Std_Http_URI_EncodedQueryString_toString___boxed), 2, 1);
lean_closure_set(v___x_781_, 0, v_r_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_783_; 
v___f_783_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_783_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___redArg___boxed(lean_object* v___dummy_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_Http_URI_instReprEncodedQueryString___redArg();
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString(lean_object* v_r_786_){
_start:
{
lean_object* v___f_787_; 
v___f_787_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_787_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___boxed(lean_object* v_r_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_Http_URI_instReprEncodedQueryString(v_r_788_);
lean_dec_ref(v_r_788_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_791_; 
v___f_791_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_791_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___redArg___boxed(lean_object* v___dummy_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Std_Http_URI_instBEqEncodedQueryString___redArg();
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString(lean_object* v_r_794_){
_start:
{
lean_object* v___f_795_; 
v___f_795_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_795_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___boxed(lean_object* v_r_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std_Http_URI_instBEqEncodedQueryString(v_r_796_);
lean_dec_ref(v_r_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_799_; 
v___f_799_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_799_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___redArg___boxed(lean_object* v___dummy_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Std_Http_URI_instHashableEncodedQueryString___redArg();
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString(lean_object* v_r_802_){
_start:
{
lean_object* v___f_803_; 
v___f_803_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_803_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___boxed(lean_object* v_r_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Std_Http_URI_instHashableEncodedQueryString(v_r_804_);
lean_dec_ref(v_r_804_);
return v_res_805_;
}
}
static uint64_t _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_812_; uint64_t v___x_813_; 
v___x_812_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__0));
v___x_813_ = lean_byte_array_hash(v___x_812_);
return v___x_813_;
}
}
static lean_object* _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__2));
v___x_821_ = lean_byte_array_size(v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT uint64_t l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0(lean_object* v_x_822_){
_start:
{
if (lean_obj_tag(v_x_822_) == 0)
{
uint64_t v___x_823_; 
v___x_823_ = lean_uint64_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1, &l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1);
return v___x_823_;
}
else
{
lean_object* v_val_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; lean_object* v___x_830_; uint64_t v___x_831_; 
v_val_824_ = lean_ctor_get(v_x_822_, 0);
v___x_825_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__2));
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = lean_obj_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3, &l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3);
v___x_828_ = lean_byte_array_size(v_val_824_);
v___x_829_ = 0;
v___x_830_ = lean_byte_array_copy_slice(v_val_824_, v___x_826_, v___x_825_, v___x_827_, v___x_828_, v___x_829_);
v___x_831_ = lean_byte_array_hash(v___x_830_);
lean_dec_ref(v___x_830_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___boxed(lean_object* v_x_832_){
_start:
{
uint64_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0(v_x_832_);
lean_dec(v_x_832_);
v_r_834_ = lean_box_uint64(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_837_; 
v___f_837_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___closed__0));
return v___f_837_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___boxed(lean_object* v___dummy_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg();
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString(lean_object* v_r_840_){
_start:
{
lean_object* v___f_841_; 
v___f_841_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___closed__0));
return v___f_841_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___boxed(lean_object* v_r_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Std_Http_URI_instHashableOptionEncodedQueryString(v_r_842_);
lean_dec_ref(v_r_842_);
return v_res_843_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0(uint8_t v___y_844_){
_start:
{
uint8_t v___x_890_; uint8_t v___x_891_; 
v___x_890_ = 48;
v___x_891_ = lean_uint8_dec_le(v___x_890_, v___y_844_);
if (v___x_891_ == 0)
{
goto v___jp_885_;
}
else
{
uint8_t v___x_892_; uint8_t v___x_893_; 
v___x_892_ = 57;
v___x_893_ = lean_uint8_dec_le(v___y_844_, v___x_892_);
if (v___x_893_ == 0)
{
goto v___jp_885_;
}
else
{
return v___x_893_;
}
}
v___jp_845_:
{
uint8_t v___x_846_; uint8_t v___x_847_; 
v___x_846_ = 45;
v___x_847_ = lean_uint8_dec_eq(v___y_844_, v___x_846_);
if (v___x_847_ == 0)
{
uint8_t v___x_848_; uint8_t v___x_849_; 
v___x_848_ = 46;
v___x_849_ = lean_uint8_dec_eq(v___y_844_, v___x_848_);
if (v___x_849_ == 0)
{
uint8_t v___x_850_; uint8_t v___x_851_; 
v___x_850_ = 95;
v___x_851_ = lean_uint8_dec_eq(v___y_844_, v___x_850_);
if (v___x_851_ == 0)
{
uint8_t v___x_852_; uint8_t v___x_853_; 
v___x_852_ = 126;
v___x_853_ = lean_uint8_dec_eq(v___y_844_, v___x_852_);
if (v___x_853_ == 0)
{
uint8_t v___x_854_; uint8_t v___x_855_; 
v___x_854_ = 33;
v___x_855_ = lean_uint8_dec_eq(v___y_844_, v___x_854_);
if (v___x_855_ == 0)
{
uint8_t v___x_856_; uint8_t v___x_857_; 
v___x_856_ = 36;
v___x_857_ = lean_uint8_dec_eq(v___y_844_, v___x_856_);
if (v___x_857_ == 0)
{
uint8_t v___x_858_; uint8_t v___x_859_; 
v___x_858_ = 38;
v___x_859_ = lean_uint8_dec_eq(v___y_844_, v___x_858_);
if (v___x_859_ == 0)
{
uint8_t v___x_860_; uint8_t v___x_861_; 
v___x_860_ = 39;
v___x_861_ = lean_uint8_dec_eq(v___y_844_, v___x_860_);
if (v___x_861_ == 0)
{
uint8_t v___x_862_; uint8_t v___x_863_; 
v___x_862_ = 40;
v___x_863_ = lean_uint8_dec_eq(v___y_844_, v___x_862_);
if (v___x_863_ == 0)
{
uint8_t v___x_864_; uint8_t v___x_865_; 
v___x_864_ = 41;
v___x_865_ = lean_uint8_dec_eq(v___y_844_, v___x_864_);
if (v___x_865_ == 0)
{
uint8_t v___x_866_; uint8_t v___x_867_; 
v___x_866_ = 42;
v___x_867_ = lean_uint8_dec_eq(v___y_844_, v___x_866_);
if (v___x_867_ == 0)
{
uint8_t v___x_868_; uint8_t v___x_869_; 
v___x_868_ = 43;
v___x_869_ = lean_uint8_dec_eq(v___y_844_, v___x_868_);
if (v___x_869_ == 0)
{
uint8_t v___x_870_; uint8_t v___x_871_; 
v___x_870_ = 44;
v___x_871_ = lean_uint8_dec_eq(v___y_844_, v___x_870_);
if (v___x_871_ == 0)
{
uint8_t v___x_872_; uint8_t v___x_873_; 
v___x_872_ = 59;
v___x_873_ = lean_uint8_dec_eq(v___y_844_, v___x_872_);
if (v___x_873_ == 0)
{
uint8_t v___x_874_; uint8_t v___x_875_; 
v___x_874_ = 61;
v___x_875_ = lean_uint8_dec_eq(v___y_844_, v___x_874_);
if (v___x_875_ == 0)
{
uint8_t v___x_876_; uint8_t v___x_877_; 
v___x_876_ = 58;
v___x_877_ = lean_uint8_dec_eq(v___y_844_, v___x_876_);
if (v___x_877_ == 0)
{
uint8_t v___x_878_; uint8_t v___x_879_; 
v___x_878_ = 64;
v___x_879_ = lean_uint8_dec_eq(v___y_844_, v___x_878_);
return v___x_879_;
}
else
{
return v___x_877_;
}
}
else
{
return v___x_875_;
}
}
else
{
return v___x_873_;
}
}
else
{
return v___x_871_;
}
}
else
{
return v___x_869_;
}
}
else
{
return v___x_867_;
}
}
else
{
return v___x_865_;
}
}
else
{
return v___x_863_;
}
}
else
{
return v___x_861_;
}
}
else
{
return v___x_859_;
}
}
else
{
return v___x_857_;
}
}
else
{
return v___x_855_;
}
}
else
{
return v___x_853_;
}
}
else
{
return v___x_851_;
}
}
else
{
return v___x_849_;
}
}
else
{
return v___x_847_;
}
}
v___jp_880_:
{
uint8_t v___x_881_; uint8_t v___x_882_; 
v___x_881_ = 65;
v___x_882_ = lean_uint8_dec_le(v___x_881_, v___y_844_);
if (v___x_882_ == 0)
{
goto v___jp_845_;
}
else
{
uint8_t v___x_883_; uint8_t v___x_884_; 
v___x_883_ = 90;
v___x_884_ = lean_uint8_dec_le(v___y_844_, v___x_883_);
if (v___x_884_ == 0)
{
goto v___jp_845_;
}
else
{
return v___x_884_;
}
}
}
v___jp_885_:
{
uint8_t v___x_886_; uint8_t v___x_887_; 
v___x_886_ = 97;
v___x_887_ = lean_uint8_dec_le(v___x_886_, v___y_844_);
if (v___x_887_ == 0)
{
goto v___jp_880_;
}
else
{
uint8_t v___x_888_; uint8_t v___x_889_; 
v___x_888_ = 122;
v___x_889_ = lean_uint8_dec_le(v___y_844_, v___x_888_);
if (v___x_889_ == 0)
{
goto v___jp_880_;
}
else
{
return v___x_889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___lam__0___boxed(lean_object* v___y_894_){
_start:
{
uint8_t v___y_265__boxed_895_; uint8_t v_res_896_; lean_object* v_r_897_; 
v___y_265__boxed_895_ = lean_unbox(v___y_894_);
v_res_896_ = l_Std_Http_URI_EncodedSegment_encode___lam__0(v___y_265__boxed_895_);
v_r_897_ = lean_box(v_res_896_);
return v_r_897_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode(lean_object* v_s_899_){
_start:
{
lean_object* v___f_900_; lean_object* v___x_901_; 
v___f_900_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_901_ = l_Std_Http_URI_EncodedString_encode(v___f_900_, v_s_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object* v_ba_902_){
_start:
{
lean_object* v___f_903_; lean_object* v___x_904_; 
v___f_903_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_904_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_903_, v_ba_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x21(lean_object* v_ba_905_){
_start:
{
lean_object* v___f_906_; lean_object* v___x_907_; 
v___f_906_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_907_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_906_, v_ba_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object* v_segment_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Std_Http_URI_EncodedString_decode___redArg(v_segment_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode___boxed(lean_object* v_segment_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Std_Http_URI_EncodedSegment_decode(v_segment_910_);
lean_dec_ref(v_segment_910_);
return v_res_911_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedFragment_encode___lam__0(uint8_t v___y_912_){
_start:
{
uint8_t v___x_962_; uint8_t v___x_963_; 
v___x_962_ = 48;
v___x_963_ = lean_uint8_dec_le(v___x_962_, v___y_912_);
if (v___x_963_ == 0)
{
goto v___jp_957_;
}
else
{
uint8_t v___x_964_; uint8_t v___x_965_; 
v___x_964_ = 57;
v___x_965_ = lean_uint8_dec_le(v___y_912_, v___x_964_);
if (v___x_965_ == 0)
{
goto v___jp_957_;
}
else
{
return v___x_965_;
}
}
v___jp_913_:
{
uint8_t v___x_914_; uint8_t v___x_915_; 
v___x_914_ = 45;
v___x_915_ = lean_uint8_dec_eq(v___y_912_, v___x_914_);
if (v___x_915_ == 0)
{
uint8_t v___x_916_; uint8_t v___x_917_; 
v___x_916_ = 46;
v___x_917_ = lean_uint8_dec_eq(v___y_912_, v___x_916_);
if (v___x_917_ == 0)
{
uint8_t v___x_918_; uint8_t v___x_919_; 
v___x_918_ = 95;
v___x_919_ = lean_uint8_dec_eq(v___y_912_, v___x_918_);
if (v___x_919_ == 0)
{
uint8_t v___x_920_; uint8_t v___x_921_; 
v___x_920_ = 126;
v___x_921_ = lean_uint8_dec_eq(v___y_912_, v___x_920_);
if (v___x_921_ == 0)
{
uint8_t v___x_922_; uint8_t v___x_923_; 
v___x_922_ = 33;
v___x_923_ = lean_uint8_dec_eq(v___y_912_, v___x_922_);
if (v___x_923_ == 0)
{
uint8_t v___x_924_; uint8_t v___x_925_; 
v___x_924_ = 36;
v___x_925_ = lean_uint8_dec_eq(v___y_912_, v___x_924_);
if (v___x_925_ == 0)
{
uint8_t v___x_926_; uint8_t v___x_927_; 
v___x_926_ = 38;
v___x_927_ = lean_uint8_dec_eq(v___y_912_, v___x_926_);
if (v___x_927_ == 0)
{
uint8_t v___x_928_; uint8_t v___x_929_; 
v___x_928_ = 39;
v___x_929_ = lean_uint8_dec_eq(v___y_912_, v___x_928_);
if (v___x_929_ == 0)
{
uint8_t v___x_930_; uint8_t v___x_931_; 
v___x_930_ = 40;
v___x_931_ = lean_uint8_dec_eq(v___y_912_, v___x_930_);
if (v___x_931_ == 0)
{
uint8_t v___x_932_; uint8_t v___x_933_; 
v___x_932_ = 41;
v___x_933_ = lean_uint8_dec_eq(v___y_912_, v___x_932_);
if (v___x_933_ == 0)
{
uint8_t v___x_934_; uint8_t v___x_935_; 
v___x_934_ = 42;
v___x_935_ = lean_uint8_dec_eq(v___y_912_, v___x_934_);
if (v___x_935_ == 0)
{
uint8_t v___x_936_; uint8_t v___x_937_; 
v___x_936_ = 43;
v___x_937_ = lean_uint8_dec_eq(v___y_912_, v___x_936_);
if (v___x_937_ == 0)
{
uint8_t v___x_938_; uint8_t v___x_939_; 
v___x_938_ = 44;
v___x_939_ = lean_uint8_dec_eq(v___y_912_, v___x_938_);
if (v___x_939_ == 0)
{
uint8_t v___x_940_; uint8_t v___x_941_; 
v___x_940_ = 59;
v___x_941_ = lean_uint8_dec_eq(v___y_912_, v___x_940_);
if (v___x_941_ == 0)
{
uint8_t v___x_942_; uint8_t v___x_943_; 
v___x_942_ = 61;
v___x_943_ = lean_uint8_dec_eq(v___y_912_, v___x_942_);
if (v___x_943_ == 0)
{
uint8_t v___x_944_; uint8_t v___x_945_; 
v___x_944_ = 58;
v___x_945_ = lean_uint8_dec_eq(v___y_912_, v___x_944_);
if (v___x_945_ == 0)
{
uint8_t v___x_946_; uint8_t v___x_947_; 
v___x_946_ = 64;
v___x_947_ = lean_uint8_dec_eq(v___y_912_, v___x_946_);
if (v___x_947_ == 0)
{
uint8_t v___x_948_; uint8_t v___x_949_; 
v___x_948_ = 47;
v___x_949_ = lean_uint8_dec_eq(v___y_912_, v___x_948_);
if (v___x_949_ == 0)
{
uint8_t v___x_950_; uint8_t v___x_951_; 
v___x_950_ = 63;
v___x_951_ = lean_uint8_dec_eq(v___y_912_, v___x_950_);
return v___x_951_;
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
else
{
return v___x_933_;
}
}
else
{
return v___x_931_;
}
}
else
{
return v___x_929_;
}
}
else
{
return v___x_927_;
}
}
else
{
return v___x_925_;
}
}
else
{
return v___x_923_;
}
}
else
{
return v___x_921_;
}
}
else
{
return v___x_919_;
}
}
else
{
return v___x_917_;
}
}
else
{
return v___x_915_;
}
}
v___jp_952_:
{
uint8_t v___x_953_; uint8_t v___x_954_; 
v___x_953_ = 65;
v___x_954_ = lean_uint8_dec_le(v___x_953_, v___y_912_);
if (v___x_954_ == 0)
{
goto v___jp_913_;
}
else
{
uint8_t v___x_955_; uint8_t v___x_956_; 
v___x_955_ = 90;
v___x_956_ = lean_uint8_dec_le(v___y_912_, v___x_955_);
if (v___x_956_ == 0)
{
goto v___jp_913_;
}
else
{
return v___x_956_;
}
}
}
v___jp_957_:
{
uint8_t v___x_958_; uint8_t v___x_959_; 
v___x_958_ = 97;
v___x_959_ = lean_uint8_dec_le(v___x_958_, v___y_912_);
if (v___x_959_ == 0)
{
goto v___jp_952_;
}
else
{
uint8_t v___x_960_; uint8_t v___x_961_; 
v___x_960_ = 122;
v___x_961_ = lean_uint8_dec_le(v___y_912_, v___x_960_);
if (v___x_961_ == 0)
{
goto v___jp_952_;
}
else
{
return v___x_961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed(lean_object* v___y_966_){
_start:
{
uint8_t v___y_289__boxed_967_; uint8_t v_res_968_; lean_object* v_r_969_; 
v___y_289__boxed_967_ = lean_unbox(v___y_966_);
v_res_968_ = l_Std_Http_URI_EncodedFragment_encode___lam__0(v___y_289__boxed_967_);
v_r_969_ = lean_box(v_res_968_);
return v_r_969_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object* v_s_971_){
_start:
{
lean_object* v___f_972_; lean_object* v___x_973_; 
v___f_972_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_973_ = l_Std_Http_URI_EncodedString_encode(v___f_972_, v_s_971_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object* v_ba_974_){
_start:
{
lean_object* v___f_975_; lean_object* v___x_976_; 
v___f_975_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_976_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_975_, v_ba_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x21(lean_object* v_ba_977_){
_start:
{
lean_object* v___f_978_; lean_object* v___x_979_; 
v___f_978_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_979_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_978_, v_ba_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object* v_fragment_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Std_Http_URI_EncodedString_decode___redArg(v_fragment_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode___boxed(lean_object* v_fragment_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Std_Http_URI_EncodedFragment_decode(v_fragment_982_);
lean_dec_ref(v_fragment_982_);
return v_res_983_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedUserInfo_encode___lam__0(uint8_t v___y_984_){
_start:
{
uint8_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = 48;
v___x_1029_ = lean_uint8_dec_le(v___x_1028_, v___y_984_);
if (v___x_1029_ == 0)
{
goto v___jp_1023_;
}
else
{
uint8_t v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = 57;
v___x_1031_ = lean_uint8_dec_le(v___y_984_, v___x_1030_);
if (v___x_1031_ == 0)
{
goto v___jp_1023_;
}
else
{
return v___x_1031_;
}
}
v___jp_985_:
{
uint8_t v___x_986_; uint8_t v___x_987_; 
v___x_986_ = 45;
v___x_987_ = lean_uint8_dec_eq(v___y_984_, v___x_986_);
if (v___x_987_ == 0)
{
uint8_t v___x_988_; uint8_t v___x_989_; 
v___x_988_ = 46;
v___x_989_ = lean_uint8_dec_eq(v___y_984_, v___x_988_);
if (v___x_989_ == 0)
{
uint8_t v___x_990_; uint8_t v___x_991_; 
v___x_990_ = 95;
v___x_991_ = lean_uint8_dec_eq(v___y_984_, v___x_990_);
if (v___x_991_ == 0)
{
uint8_t v___x_992_; uint8_t v___x_993_; 
v___x_992_ = 126;
v___x_993_ = lean_uint8_dec_eq(v___y_984_, v___x_992_);
if (v___x_993_ == 0)
{
uint8_t v___x_994_; uint8_t v___x_995_; 
v___x_994_ = 33;
v___x_995_ = lean_uint8_dec_eq(v___y_984_, v___x_994_);
if (v___x_995_ == 0)
{
uint8_t v___x_996_; uint8_t v___x_997_; 
v___x_996_ = 36;
v___x_997_ = lean_uint8_dec_eq(v___y_984_, v___x_996_);
if (v___x_997_ == 0)
{
uint8_t v___x_998_; uint8_t v___x_999_; 
v___x_998_ = 38;
v___x_999_ = lean_uint8_dec_eq(v___y_984_, v___x_998_);
if (v___x_999_ == 0)
{
uint8_t v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = 39;
v___x_1001_ = lean_uint8_dec_eq(v___y_984_, v___x_1000_);
if (v___x_1001_ == 0)
{
uint8_t v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = 40;
v___x_1003_ = lean_uint8_dec_eq(v___y_984_, v___x_1002_);
if (v___x_1003_ == 0)
{
uint8_t v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = 41;
v___x_1005_ = lean_uint8_dec_eq(v___y_984_, v___x_1004_);
if (v___x_1005_ == 0)
{
uint8_t v___x_1006_; uint8_t v___x_1007_; 
v___x_1006_ = 42;
v___x_1007_ = lean_uint8_dec_eq(v___y_984_, v___x_1006_);
if (v___x_1007_ == 0)
{
uint8_t v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = 43;
v___x_1009_ = lean_uint8_dec_eq(v___y_984_, v___x_1008_);
if (v___x_1009_ == 0)
{
uint8_t v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = 44;
v___x_1011_ = lean_uint8_dec_eq(v___y_984_, v___x_1010_);
if (v___x_1011_ == 0)
{
uint8_t v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = 59;
v___x_1013_ = lean_uint8_dec_eq(v___y_984_, v___x_1012_);
if (v___x_1013_ == 0)
{
uint8_t v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = 61;
v___x_1015_ = lean_uint8_dec_eq(v___y_984_, v___x_1014_);
if (v___x_1015_ == 0)
{
uint8_t v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = 58;
v___x_1017_ = lean_uint8_dec_eq(v___y_984_, v___x_1016_);
return v___x_1017_;
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
v___jp_1018_:
{
uint8_t v___x_1019_; uint8_t v___x_1020_; 
v___x_1019_ = 65;
v___x_1020_ = lean_uint8_dec_le(v___x_1019_, v___y_984_);
if (v___x_1020_ == 0)
{
goto v___jp_985_;
}
else
{
uint8_t v___x_1021_; uint8_t v___x_1022_; 
v___x_1021_ = 90;
v___x_1022_ = lean_uint8_dec_le(v___y_984_, v___x_1021_);
if (v___x_1022_ == 0)
{
goto v___jp_985_;
}
else
{
return v___x_1022_;
}
}
}
v___jp_1023_:
{
uint8_t v___x_1024_; uint8_t v___x_1025_; 
v___x_1024_ = 97;
v___x_1025_ = lean_uint8_dec_le(v___x_1024_, v___y_984_);
if (v___x_1025_ == 0)
{
goto v___jp_1018_;
}
else
{
uint8_t v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = 122;
v___x_1027_ = lean_uint8_dec_le(v___y_984_, v___x_1026_);
if (v___x_1027_ == 0)
{
goto v___jp_1018_;
}
else
{
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed(lean_object* v___y_1032_){
_start:
{
uint8_t v___y_253__boxed_1033_; uint8_t v_res_1034_; lean_object* v_r_1035_; 
v___y_253__boxed_1033_ = lean_unbox(v___y_1032_);
v_res_1034_ = l_Std_Http_URI_EncodedUserInfo_encode___lam__0(v___y_253__boxed_1033_);
v_r_1035_ = lean_box(v_res_1034_);
return v_r_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object* v_s_1037_){
_start:
{
lean_object* v___f_1038_; lean_object* v___x_1039_; 
v___f_1038_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1039_ = l_Std_Http_URI_EncodedString_encode(v___f_1038_, v_s_1037_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object* v_ba_1040_){
_start:
{
lean_object* v___f_1041_; lean_object* v___x_1042_; 
v___f_1041_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1042_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1041_, v_ba_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x21(lean_object* v_ba_1043_){
_start:
{
lean_object* v___f_1044_; lean_object* v___x_1045_; 
v___f_1044_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1045_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1044_, v_ba_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode(lean_object* v_userInfo_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Std_Http_URI_EncodedString_decode___redArg(v_userInfo_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode___boxed(lean_object* v_userInfo_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Std_Http_URI_EncodedUserInfo_decode(v_userInfo_1048_);
lean_dec_ref(v_userInfo_1048_);
return v_res_1049_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryParam_encode___lam__0(uint8_t v___y_1050_){
_start:
{
uint8_t v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = 48;
v___x_1108_ = lean_uint8_dec_le(v___x_1107_, v___y_1050_);
if (v___x_1108_ == 0)
{
goto v___jp_1102_;
}
else
{
uint8_t v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = 57;
v___x_1110_ = lean_uint8_dec_le(v___y_1050_, v___x_1109_);
if (v___x_1110_ == 0)
{
goto v___jp_1102_;
}
else
{
goto v___jp_1051_;
}
}
v___jp_1051_:
{
uint8_t v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = 38;
v___x_1053_ = lean_uint8_dec_eq(v___y_1050_, v___x_1052_);
if (v___x_1053_ == 0)
{
uint8_t v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = 61;
v___x_1055_ = lean_uint8_dec_eq(v___y_1050_, v___x_1054_);
if (v___x_1055_ == 0)
{
uint8_t v___x_1056_; 
v___x_1056_ = 1;
return v___x_1056_;
}
else
{
return v___x_1053_;
}
}
else
{
uint8_t v___x_1057_; 
v___x_1057_ = 0;
return v___x_1057_;
}
}
v___jp_1058_:
{
uint8_t v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = 45;
v___x_1060_ = lean_uint8_dec_eq(v___y_1050_, v___x_1059_);
if (v___x_1060_ == 0)
{
uint8_t v___x_1061_; uint8_t v___x_1062_; 
v___x_1061_ = 46;
v___x_1062_ = lean_uint8_dec_eq(v___y_1050_, v___x_1061_);
if (v___x_1062_ == 0)
{
uint8_t v___x_1063_; uint8_t v___x_1064_; 
v___x_1063_ = 95;
v___x_1064_ = lean_uint8_dec_eq(v___y_1050_, v___x_1063_);
if (v___x_1064_ == 0)
{
uint8_t v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = 126;
v___x_1066_ = lean_uint8_dec_eq(v___y_1050_, v___x_1065_);
if (v___x_1066_ == 0)
{
uint8_t v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = 33;
v___x_1068_ = lean_uint8_dec_eq(v___y_1050_, v___x_1067_);
if (v___x_1068_ == 0)
{
uint8_t v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = 36;
v___x_1070_ = lean_uint8_dec_eq(v___y_1050_, v___x_1069_);
if (v___x_1070_ == 0)
{
uint8_t v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = 38;
v___x_1072_ = lean_uint8_dec_eq(v___y_1050_, v___x_1071_);
if (v___x_1072_ == 0)
{
uint8_t v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = 39;
v___x_1074_ = lean_uint8_dec_eq(v___y_1050_, v___x_1073_);
if (v___x_1074_ == 0)
{
uint8_t v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = 40;
v___x_1076_ = lean_uint8_dec_eq(v___y_1050_, v___x_1075_);
if (v___x_1076_ == 0)
{
uint8_t v___x_1077_; uint8_t v___x_1078_; 
v___x_1077_ = 41;
v___x_1078_ = lean_uint8_dec_eq(v___y_1050_, v___x_1077_);
if (v___x_1078_ == 0)
{
uint8_t v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = 42;
v___x_1080_ = lean_uint8_dec_eq(v___y_1050_, v___x_1079_);
if (v___x_1080_ == 0)
{
uint8_t v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = 43;
v___x_1082_ = lean_uint8_dec_eq(v___y_1050_, v___x_1081_);
if (v___x_1082_ == 0)
{
uint8_t v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = 44;
v___x_1084_ = lean_uint8_dec_eq(v___y_1050_, v___x_1083_);
if (v___x_1084_ == 0)
{
uint8_t v___x_1085_; uint8_t v___x_1086_; 
v___x_1085_ = 59;
v___x_1086_ = lean_uint8_dec_eq(v___y_1050_, v___x_1085_);
if (v___x_1086_ == 0)
{
uint8_t v___x_1087_; uint8_t v___x_1088_; 
v___x_1087_ = 61;
v___x_1088_ = lean_uint8_dec_eq(v___y_1050_, v___x_1087_);
if (v___x_1088_ == 0)
{
uint8_t v___x_1089_; uint8_t v___x_1090_; 
v___x_1089_ = 58;
v___x_1090_ = lean_uint8_dec_eq(v___y_1050_, v___x_1089_);
if (v___x_1090_ == 0)
{
uint8_t v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = 64;
v___x_1092_ = lean_uint8_dec_eq(v___y_1050_, v___x_1091_);
if (v___x_1092_ == 0)
{
uint8_t v___x_1093_; uint8_t v___x_1094_; 
v___x_1093_ = 47;
v___x_1094_ = lean_uint8_dec_eq(v___y_1050_, v___x_1093_);
if (v___x_1094_ == 0)
{
uint8_t v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = 63;
v___x_1096_ = lean_uint8_dec_eq(v___y_1050_, v___x_1095_);
if (v___x_1096_ == 0)
{
return v___x_1096_;
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
else
{
goto v___jp_1051_;
}
}
v___jp_1097_:
{
uint8_t v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = 65;
v___x_1099_ = lean_uint8_dec_le(v___x_1098_, v___y_1050_);
if (v___x_1099_ == 0)
{
goto v___jp_1058_;
}
else
{
uint8_t v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = 90;
v___x_1101_ = lean_uint8_dec_le(v___y_1050_, v___x_1100_);
if (v___x_1101_ == 0)
{
goto v___jp_1058_;
}
else
{
goto v___jp_1051_;
}
}
}
v___jp_1102_:
{
uint8_t v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = 97;
v___x_1104_ = lean_uint8_dec_le(v___x_1103_, v___y_1050_);
if (v___x_1104_ == 0)
{
goto v___jp_1097_;
}
else
{
uint8_t v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = 122;
v___x_1106_ = lean_uint8_dec_le(v___y_1050_, v___x_1105_);
if (v___x_1106_ == 0)
{
goto v___jp_1097_;
}
else
{
goto v___jp_1051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed(lean_object* v___y_1111_){
_start:
{
uint8_t v___y_363__boxed_1112_; uint8_t v_res_1113_; lean_object* v_r_1114_; 
v___y_363__boxed_1112_ = lean_unbox(v___y_1111_);
v_res_1113_ = l_Std_Http_URI_EncodedQueryParam_encode___lam__0(v___y_363__boxed_1112_);
v_r_1114_ = lean_box(v_res_1113_);
return v_r_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode(lean_object* v_s_1116_){
_start:
{
lean_object* v___f_1117_; lean_object* v___x_1118_; 
v___f_1117_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1118_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_1116_, v___f_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f(lean_object* v_ba_1119_){
_start:
{
lean_object* v___f_1120_; lean_object* v___x_1121_; 
v___f_1120_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1121_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_1119_, v___f_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x21(lean_object* v_ba_1122_){
_start:
{
lean_object* v___f_1123_; lean_object* v___x_1124_; 
v___f_1123_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1124_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v_ba_1122_, v___f_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object* v_s_1125_){
_start:
{
lean_object* v___f_1126_; lean_object* v___x_1127_; 
v___f_1126_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1127_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_1125_, v___f_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object* v_param_1128_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_param_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode___boxed(lean_object* v_param_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Std_Http_URI_EncodedQueryParam_decode(v_param_1130_);
lean_dec_ref(v_param_1130_);
return v_res_1131_;
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
