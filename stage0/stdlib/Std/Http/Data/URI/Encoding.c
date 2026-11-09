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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(lean_object* v_x_228_, uint8_t v_x_229_, lean_object* v_h__1_230_){
_start:
{
lean_object* v_data_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_data_231_ = lean_byte_array_data(v_x_228_);
v___x_232_ = lean_box(v_x_229_);
v___x_233_ = lean_apply_2(v_h__1_230_, v_data_231_, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg___boxed(lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_h__1_236_){
_start:
{
uint8_t v_x_17__boxed_237_; lean_object* v_res_238_; 
v_x_17__boxed_237_ = lean_unbox(v_x_235_);
v_res_238_ = l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(v_x_234_, v_x_17__boxed_237_, v_h__1_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(lean_object* v_motive_239_, lean_object* v_x_240_, uint8_t v_x_241_, lean_object* v_h__1_242_){
_start:
{
lean_object* v_data_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_data_243_ = lean_byte_array_data(v_x_240_);
v___x_244_ = lean_box(v_x_241_);
v___x_245_ = lean_apply_2(v_h__1_242_, v_data_243_, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___boxed(lean_object* v_motive_246_, lean_object* v_x_247_, lean_object* v_x_248_, lean_object* v_h__1_249_){
_start:
{
uint8_t v_x_29__boxed_250_; lean_object* v_res_251_; 
v_x_29__boxed_250_ = lean_unbox(v_x_248_);
v_res_251_ = l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(v_motive_246_, v_x_247_, v_x_29__boxed_250_, v_h__1_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter___redArg(lean_object* v_x_252_, lean_object* v_x_253_, lean_object* v_h__1_254_, lean_object* v_h__2_255_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
lean_object* v___x_256_; 
lean_dec(v_h__2_255_);
v___x_256_ = lean_apply_1(v_h__1_254_, v_x_253_);
return v___x_256_;
}
else
{
lean_object* v_head_257_; lean_object* v_tail_258_; lean_object* v___x_259_; 
lean_dec(v_h__1_254_);
v_head_257_ = lean_ctor_get(v_x_252_, 0);
lean_inc(v_head_257_);
v_tail_258_ = lean_ctor_get(v_x_252_, 1);
lean_inc(v_tail_258_);
lean_dec_ref_known(v_x_252_, 2);
v___x_259_ = lean_apply_3(v_h__2_255_, v_head_257_, v_tail_258_, v_x_253_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter(lean_object* v_motive_260_, lean_object* v_x_261_, lean_object* v_x_262_, lean_object* v_h__1_263_, lean_object* v_h__2_264_){
_start:
{
if (lean_obj_tag(v_x_261_) == 0)
{
lean_object* v___x_265_; 
lean_dec(v_h__2_264_);
v___x_265_ = lean_apply_1(v_h__1_263_, v_x_262_);
return v___x_265_;
}
else
{
lean_object* v_head_266_; lean_object* v_tail_267_; lean_object* v___x_268_; 
lean_dec(v_h__1_263_);
v_head_266_ = lean_ctor_get(v_x_261_, 0);
lean_inc(v_head_266_);
v_tail_267_ = lean_ctor_get(v_x_261_, 1);
lean_inc(v_tail_267_);
lean_dec_ref_known(v_x_261_, 2);
v___x_268_ = lean_apply_3(v_h__2_264_, v_head_266_, v_tail_267_, v_x_262_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___redArg(){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_ByteArray_empty;
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___redArg___boxed(lean_object* v___dummy_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Std_Http_URI_EncodedString_empty___redArg();
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty(lean_object* v_r_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_ByteArray_empty;
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___boxed(lean_object* v_r_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Std_Http_URI_EncodedString_empty(v_r_275_);
lean_dec_ref(v_r_275_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___redArg(){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_ByteArray_empty;
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___redArg___boxed(lean_object* v___dummy_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Std_Http_URI_EncodedString_instInhabited___redArg();
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited(lean_object* v_r_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_ByteArray_empty;
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___boxed(lean_object* v_r_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Std_Http_URI_EncodedString_instInhabited(v_r_283_);
lean_dec_ref(v_r_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(lean_object* v_s_285_, uint8_t v_c_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_byte_array_push(v_s_285_, v_c_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg___boxed(lean_object* v_s_288_, lean_object* v_c_289_){
_start:
{
uint8_t v_c_boxed_290_; lean_object* v_res_291_; 
v_c_boxed_290_ = lean_unbox(v_c_289_);
v_res_291_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(v_s_288_, v_c_boxed_290_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(lean_object* v_r_292_, lean_object* v_s_293_, uint8_t v_c_294_, lean_object* v_h_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = lean_byte_array_push(v_s_293_, v_c_294_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___boxed(lean_object* v_r_297_, lean_object* v_s_298_, lean_object* v_c_299_, lean_object* v_h_300_){
_start:
{
uint8_t v_c_boxed_301_; lean_object* v_res_302_; 
v_c_boxed_301_ = lean_unbox(v_c_299_);
v_res_302_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(v_r_297_, v_s_298_, v_c_boxed_301_, v_h_300_);
lean_dec_ref(v_r_297_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(uint8_t v_b_303_, lean_object* v_s_304_){
_start:
{
uint8_t v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; uint8_t v___x_308_; uint8_t v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; uint8_t v___x_312_; uint8_t v___x_313_; lean_object* v_ba_314_; 
v___x_305_ = 37;
v___x_306_ = lean_byte_array_push(v_s_304_, v___x_305_);
v___x_307_ = 4;
v___x_308_ = lean_uint8_shift_right(v_b_303_, v___x_307_);
v___x_309_ = l_Std_Http_URI_hexDigit(v___x_308_);
v___x_310_ = lean_byte_array_push(v___x_306_, v___x_309_);
v___x_311_ = 15;
v___x_312_ = lean_uint8_land(v_b_303_, v___x_311_);
v___x_313_ = l_Std_Http_URI_hexDigit(v___x_312_);
v_ba_314_ = lean_byte_array_push(v___x_310_, v___x_313_);
return v_ba_314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg___boxed(lean_object* v_b_315_, lean_object* v_s_316_){
_start:
{
uint8_t v_b_boxed_317_; lean_object* v_res_318_; 
v_b_boxed_317_ = lean_unbox(v_b_315_);
v_res_318_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_boxed_317_, v_s_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(lean_object* v_r_319_, uint8_t v_b_320_, lean_object* v_s_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_320_, v_s_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___boxed(lean_object* v_r_323_, lean_object* v_b_324_, lean_object* v_s_325_){
_start:
{
uint8_t v_b_boxed_326_; lean_object* v_res_327_; 
v_b_boxed_326_ = lean_unbox(v_b_324_);
v_res_327_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(v_r_323_, v_b_boxed_326_, v_s_325_);
lean_dec_ref(v_r_323_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(lean_object* v_r_328_, lean_object* v_as_329_, size_t v_i_330_, size_t v_stop_331_, lean_object* v_b_332_){
_start:
{
lean_object* v___y_334_; uint8_t v___x_338_; 
v___x_338_ = lean_usize_dec_eq(v_i_330_, v_stop_331_);
if (v___x_338_ == 0)
{
uint8_t v___x_339_; uint8_t v___x_340_; uint8_t v___x_341_; 
v___x_339_ = lean_byte_array_uget(v_as_329_, v_i_330_);
v___x_340_ = 128;
v___x_341_ = lean_uint8_dec_lt(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
v___x_342_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_339_, v_b_332_);
v___y_334_ = v___x_342_;
goto v___jp_333_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_343_ = lean_box(v___x_339_);
lean_inc_ref(v_r_328_);
v___x_344_ = lean_apply_1(v_r_328_, v___x_343_);
v___x_345_ = lean_unbox(v___x_344_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
v___x_346_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_339_, v_b_332_);
v___y_334_ = v___x_346_;
goto v___jp_333_;
}
else
{
lean_object* v___x_347_; 
v___x_347_ = lean_byte_array_push(v_b_332_, v___x_339_);
v___y_334_ = v___x_347_;
goto v___jp_333_;
}
}
}
else
{
lean_dec_ref(v_r_328_);
return v_b_332_;
}
v___jp_333_:
{
size_t v___x_335_; size_t v___x_336_; 
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_add(v_i_330_, v___x_335_);
v_i_330_ = v___x_336_;
v_b_332_ = v___y_334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0___boxed(lean_object* v_r_348_, lean_object* v_as_349_, lean_object* v_i_350_, lean_object* v_stop_351_, lean_object* v_b_352_){
_start:
{
size_t v_i_boxed_353_; size_t v_stop_boxed_354_; lean_object* v_res_355_; 
v_i_boxed_353_ = lean_unbox_usize(v_i_350_);
lean_dec(v_i_350_);
v_stop_boxed_354_ = lean_unbox_usize(v_stop_351_);
lean_dec(v_stop_351_);
v_res_355_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_348_, v_as_349_, v_i_boxed_353_, v_stop_boxed_354_, v_b_352_);
lean_dec_ref(v_as_349_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode(lean_object* v_r_356_, lean_object* v_s_357_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_358_ = l_ByteArray_empty;
v___x_359_ = lean_string_to_utf8(v_s_357_);
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = lean_byte_array_size(v___x_359_);
v___x_362_ = lean_nat_dec_lt(v___x_360_, v___x_361_);
if (v___x_362_ == 0)
{
lean_dec_ref(v___x_359_);
lean_dec_ref(v_r_356_);
return v___x_358_;
}
else
{
size_t v___x_363_; size_t v___x_364_; lean_object* v___x_365_; 
v___x_363_ = ((size_t)0ULL);
v___x_364_ = lean_usize_of_nat(v___x_361_);
v___x_365_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_356_, v___x_359_, v___x_363_, v___x_364_, v___x_358_);
lean_dec_ref(v___x_359_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x3f(lean_object* v_r_366_, lean_object* v_ba_367_){
_start:
{
uint8_t v___x_368_; 
lean_inc_ref(v_ba_367_);
v___x_368_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_366_, v_ba_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
lean_dec_ref(v_ba_367_);
v___x_369_ = lean_box(0);
return v___x_369_;
}
else
{
uint8_t v___x_370_; 
v___x_370_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_367_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec_ref(v_ba_367_);
v___x_371_ = lean_box(0);
return v___x_371_;
}
else
{
lean_object* v___x_372_; 
v___x_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_372_, 0, v_ba_367_);
return v___x_372_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_373_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = l_ByteArray_empty;
v___x_375_ = lean_panic_fn_borrowed(v___x_374_, v_msg_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(lean_object* v_r_376_, lean_object* v_msg_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v_msg_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_379_, lean_object* v_msg_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(v_r_379_, v_msg_380_);
lean_dec_ref(v_r_379_);
return v_res_381_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_385_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2));
v___x_386_ = lean_unsigned_to_nat(12u);
v___x_387_ = lean_unsigned_to_nat(319u);
v___x_388_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1));
v___x_389_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_390_ = l_mkPanicMessageWithDecl(v___x_389_, v___x_388_, v___x_387_, v___x_386_, v___x_385_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x21(lean_object* v_r_391_, lean_object* v_ba_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_391_, v_ba_392_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_obj_once(&l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3, &l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3_once, _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3);
v___x_395_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v___x_394_);
return v___x_395_;
}
else
{
lean_object* v_val_396_; 
v_val_396_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_val_396_);
lean_dec_ref_known(v___x_393_, 1);
return v_val_396_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f(lean_object* v_r_397_, lean_object* v_s_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_string_to_utf8(v_s_398_);
v___x_400_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_397_, v___x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21(lean_object* v_r_401_, lean_object* v_s_402_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_string_to_utf8(v_s_402_);
v___x_404_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v_r_401_, v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg(lean_object* v_ba_405_){
_start:
{
lean_inc_ref(v_ba_405_);
return v_ba_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg___boxed(lean_object* v_ba_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Std_Http_URI_EncodedString_new___redArg(v_ba_406_);
lean_dec_ref(v_ba_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new(lean_object* v_r_408_, lean_object* v_ba_409_, lean_object* v_valid_410_, lean_object* v___validEncoding_411_){
_start:
{
lean_inc_ref(v_ba_409_);
return v_ba_409_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___boxed(lean_object* v_r_412_, lean_object* v_ba_413_, lean_object* v_valid_414_, lean_object* v___validEncoding_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_Http_URI_EncodedString_new(v_r_412_, v_ba_413_, v_valid_414_, v___validEncoding_415_);
lean_dec_ref(v_ba_413_);
lean_dec_ref(v_r_412_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg___lam__0(lean_object* v_es_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = lean_string_from_utf8_unchecked(v_es_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg(){
_start:
{
lean_object* v___f_421_; 
v___f_421_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instToString___redArg___closed__0));
return v___f_421_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg___boxed(lean_object* v___dummy_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_Http_URI_EncodedString_instToString___redArg();
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString(lean_object* v_r_424_){
_start:
{
lean_object* v___f_425_; 
v___f_425_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instToString___redArg___closed__0));
return v___f_425_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___boxed(lean_object* v_r_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_Http_URI_EncodedString_instToString(v_r_426_);
lean_dec_ref(v_r_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(lean_object* v_len_428_, lean_object* v_rawBytes_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_fst_431_; lean_object* v_snd_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_490_; 
v_fst_431_ = lean_ctor_get(v_a_430_, 0);
v_snd_432_ = lean_ctor_get(v_a_430_, 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v_a_430_);
if (v_isSharedCheck_490_ == 0)
{
v___x_434_ = v_a_430_;
v_isShared_435_ = v_isSharedCheck_490_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_snd_432_);
lean_inc(v_fst_431_);
lean_dec(v_a_430_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_490_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
uint8_t v___x_436_; 
v___x_436_ = lean_nat_dec_lt(v_snd_432_, v_len_428_);
if (v___x_436_ == 0)
{
lean_object* v___x_438_; 
if (v_isShared_435_ == 0)
{
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_fst_431_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_snd_432_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
else
{
uint8_t v_percent_440_; uint8_t v___x_441_; uint8_t v___x_450_; 
v_percent_440_ = 37;
v___x_441_ = lean_byte_array_fget(v_rawBytes_429_, v_snd_432_);
v___x_450_ = lean_uint8_dec_eq(v___x_441_, v_percent_440_);
if (v___x_450_ == 0)
{
goto v___jp_442_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_nat_add(v_snd_432_, v___x_451_);
v___x_453_ = lean_nat_dec_lt(v___x_452_, v_len_428_);
if (v___x_453_ == 0)
{
lean_dec(v___x_452_);
goto v___jp_442_;
}
else
{
uint8_t v___x_454_; lean_object* v___x_455_; 
lean_del_object(v___x_434_);
v___x_454_ = lean_byte_array_fget(v_rawBytes_429_, v___x_452_);
lean_dec(v___x_452_);
v___x_455_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_454_);
if (lean_obj_tag(v___x_455_) == 1)
{
lean_object* v_val_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v_val_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_val_456_);
lean_dec_ref_known(v___x_455_, 1);
v___x_457_ = lean_unsigned_to_nat(2u);
v___x_458_ = lean_nat_add(v_snd_432_, v___x_457_);
v___x_459_ = lean_nat_dec_lt(v___x_458_, v_len_428_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
lean_dec(v_val_456_);
lean_dec(v_snd_432_);
v___x_460_ = lean_byte_array_push(v_fst_431_, v___x_441_);
v___x_461_ = lean_byte_array_push(v___x_460_, v___x_454_);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_458_);
v_a_430_ = v___x_462_;
goto _start;
}
else
{
uint8_t v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_byte_array_fget(v_rawBytes_429_, v___x_458_);
lean_dec(v___x_458_);
v___x_465_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_464_);
if (lean_obj_tag(v___x_465_) == 1)
{
lean_object* v_val_466_; uint8_t v___x_467_; uint8_t v___x_468_; uint8_t v___x_469_; uint8_t v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_val_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_466_);
lean_dec_ref_known(v___x_465_, 1);
v___x_467_ = 4;
v___x_468_ = lean_unbox(v_val_456_);
lean_dec(v_val_456_);
v___x_469_ = lean_uint8_shift_left(v___x_468_, v___x_467_);
v___x_470_ = lean_unbox(v_val_466_);
lean_dec(v_val_466_);
v___x_471_ = lean_uint8_add(v___x_469_, v___x_470_);
v___x_472_ = lean_byte_array_push(v_fst_431_, v___x_471_);
v___x_473_ = lean_unsigned_to_nat(3u);
v___x_474_ = lean_nat_add(v_snd_432_, v___x_473_);
lean_dec(v_snd_432_);
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_472_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v_a_430_ = v___x_475_;
goto _start;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec(v___x_465_);
lean_dec(v_val_456_);
v___x_477_ = lean_byte_array_push(v_fst_431_, v___x_441_);
v___x_478_ = lean_byte_array_push(v___x_477_, v___x_454_);
v___x_479_ = lean_byte_array_push(v___x_478_, v___x_464_);
v___x_480_ = lean_unsigned_to_nat(3u);
v___x_481_ = lean_nat_add(v_snd_432_, v___x_480_);
lean_dec(v_snd_432_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_479_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v_a_430_ = v___x_482_;
goto _start;
}
}
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec(v___x_455_);
v___x_484_ = lean_byte_array_push(v_fst_431_, v___x_441_);
v___x_485_ = lean_byte_array_push(v___x_484_, v___x_454_);
v___x_486_ = lean_unsigned_to_nat(2u);
v___x_487_ = lean_nat_add(v_snd_432_, v___x_486_);
lean_dec(v_snd_432_);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_485_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v_a_430_ = v___x_488_;
goto _start;
}
}
}
v___jp_442_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_443_ = lean_byte_array_push(v_fst_431_, v___x_441_);
v___x_444_ = lean_unsigned_to_nat(1u);
v___x_445_ = lean_nat_add(v_snd_432_, v___x_444_);
lean_dec(v_snd_432_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_445_);
lean_ctor_set(v___x_434_, 0, v___x_443_);
v___x_447_ = v___x_434_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v___x_445_);
v___x_447_ = v_reuseFailAlloc_449_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
v_a_430_ = v___x_447_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg___boxed(lean_object* v_len_491_, lean_object* v_rawBytes_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_491_, v_rawBytes_492_, v_a_493_);
lean_dec_ref(v_rawBytes_492_);
lean_dec(v_len_491_);
return v_res_494_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0(void){
_start:
{
lean_object* v_i_495_; lean_object* v_decoded_496_; lean_object* v___x_497_; 
v_i_495_ = lean_unsigned_to_nat(0u);
v_decoded_496_ = l_ByteArray_empty;
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v_decoded_496_);
lean_ctor_set(v___x_497_, 1, v_i_495_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg(lean_object* v_es_498_){
_start:
{
lean_object* v_len_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v_fst_502_; uint8_t v___x_503_; 
v_len_499_ = lean_byte_array_size(v_es_498_);
v___x_500_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_501_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_499_, v_es_498_, v___x_500_);
v_fst_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_fst_502_);
lean_dec_ref(v___x_501_);
v___x_503_ = lean_string_validate_utf8(v_fst_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
lean_dec(v_fst_502_);
v___x_504_ = lean_box(0);
return v___x_504_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_string_from_utf8_unchecked(v_fst_502_);
v___x_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg___boxed(lean_object* v_es_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_507_);
lean_dec_ref(v_es_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode(lean_object* v_r_509_, lean_object* v_es_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___boxed(lean_object* v_r_512_, lean_object* v_es_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_Http_URI_EncodedString_decode(v_r_512_, v_es_513_);
lean_dec_ref(v_es_513_);
lean_dec_ref(v_r_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(lean_object* v_len_515_, lean_object* v_rawBytes_516_, lean_object* v_inst_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_515_, v_rawBytes_516_, v_a_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___boxed(lean_object* v_len_520_, lean_object* v_rawBytes_521_, lean_object* v_inst_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(v_len_520_, v_rawBytes_521_, v_inst_522_, v_a_523_);
lean_dec_ref(v_rawBytes_521_);
lean_dec(v_len_520_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0(lean_object* v_es_525_, lean_object* v_n_526_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_527_ = lean_string_from_utf8_unchecked(v_es_525_);
v___x_528_ = l_String_quote(v___x_527_);
v___x_529_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0___boxed(lean_object* v_es_530_, lean_object* v_n_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0(v_es_530_, v_n_531_);
lean_dec(v_n_531_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg(){
_start:
{
lean_object* v___f_535_; 
v___f_535_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___boxed(lean_object* v___dummy_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_Http_URI_EncodedString_instRepr___redArg();
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr(lean_object* v_r_538_){
_start:
{
lean_object* v___f_539_; 
v___f_539_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___boxed(lean_object* v_r_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_Http_URI_EncodedString_instRepr(v_r_540_);
lean_dec_ref(v_r_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___redArg(){
_start:
{
lean_object* v___f_544_; 
v___f_544_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___redArg___boxed(lean_object* v___dummy_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Std_Http_URI_EncodedString_instBEq___redArg();
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq(lean_object* v_r_547_){
_start:
{
lean_object* v___f_548_; 
v___f_548_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___boxed(lean_object* v_r_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_Http_URI_EncodedString_instBEq(v_r_549_);
lean_dec_ref(v_r_549_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___redArg(){
_start:
{
lean_object* v___f_553_; 
v___f_553_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_553_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___redArg___boxed(lean_object* v___dummy_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Std_Http_URI_EncodedString_instHashable___redArg();
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable(lean_object* v_r_556_){
_start:
{
lean_object* v___f_557_; 
v___f_557_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___boxed(lean_object* v_r_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_Http_URI_EncodedString_instHashable(v_r_558_);
lean_dec_ref(v_r_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___redArg(){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_ByteArray_empty;
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___redArg___boxed(lean_object* v___dummy_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Std_Http_URI_EncodedQueryString_empty___redArg();
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty(lean_object* v_r_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_ByteArray_empty;
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___boxed(lean_object* v_r_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_Http_URI_EncodedQueryString_empty(v_r_566_);
lean_dec_ref(v_r_566_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___redArg(){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_ByteArray_empty;
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___redArg___boxed(lean_object* v___dummy_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Std_Http_URI_EncodedQueryString_instInhabited___redArg();
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited(lean_object* v_r_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_ByteArray_empty;
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___boxed(lean_object* v_r_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_Http_URI_EncodedQueryString_instInhabited(v_r_574_);
lean_dec_ref(v_r_574_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(lean_object* v_s_576_, uint8_t v_c_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = lean_byte_array_push(v_s_576_, v_c_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg___boxed(lean_object* v_s_579_, lean_object* v_c_580_){
_start:
{
uint8_t v_c_boxed_581_; lean_object* v_res_582_; 
v_c_boxed_581_ = lean_unbox(v_c_580_);
v_res_582_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(v_s_579_, v_c_boxed_581_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(lean_object* v_r_583_, lean_object* v_s_584_, uint8_t v_c_585_, lean_object* v_h_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = lean_byte_array_push(v_s_584_, v_c_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___boxed(lean_object* v_r_588_, lean_object* v_s_589_, lean_object* v_c_590_, lean_object* v_h_591_){
_start:
{
uint8_t v_c_boxed_592_; lean_object* v_res_593_; 
v_c_boxed_592_ = lean_unbox(v_c_590_);
v_res_593_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(v_r_588_, v_s_589_, v_c_boxed_592_, v_h_591_);
lean_dec_ref(v_r_588_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(lean_object* v_ba_594_, lean_object* v_r_595_){
_start:
{
uint8_t v___x_596_; 
lean_inc_ref(v_ba_594_);
v___x_596_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_595_, v_ba_594_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; 
lean_dec_ref(v_ba_594_);
v___x_597_ = lean_box(0);
return v___x_597_;
}
else
{
uint8_t v___x_598_; 
v___x_598_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_594_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
lean_dec_ref(v_ba_594_);
v___x_599_ = lean_box(0);
return v___x_599_;
}
else
{
lean_object* v___x_600_; 
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v_ba_594_);
return v___x_600_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_601_){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = l_ByteArray_empty;
v___x_603_ = lean_panic_fn_borrowed(v___x_602_, v_msg_601_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(lean_object* v_r_604_, lean_object* v_msg_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v_msg_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_607_, lean_object* v_msg_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(v_r_607_, v_msg_608_);
lean_dec_ref(v_r_607_);
return v_res_609_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_612_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1));
v___x_613_ = lean_unsigned_to_nat(12u);
v___x_614_ = lean_unsigned_to_nat(437u);
v___x_615_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0));
v___x_616_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_617_ = l_mkPanicMessageWithDecl(v___x_616_, v___x_615_, v___x_614_, v___x_613_, v___x_612_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(lean_object* v_ba_618_, lean_object* v_r_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_618_, v_r_619_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_obj_once(&l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2, &l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2_once, _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2);
v___x_622_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v___x_621_);
return v___x_622_;
}
else
{
lean_object* v_val_623_; 
v_val_623_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_val_623_);
lean_dec_ref_known(v___x_620_, 1);
return v_val_623_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f(lean_object* v_s_624_, lean_object* v_r_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_string_to_utf8(v_s_624_);
v___x_627_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v___x_626_, v_r_625_);
return v___x_627_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(uint8_t v_b_644_, lean_object* v_s_645_){
_start:
{
uint8_t v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; uint8_t v___x_649_; uint8_t v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; uint8_t v___x_653_; uint8_t v___x_654_; lean_object* v_ba_655_; 
v___x_646_ = 37;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg___boxed(lean_object* v_b_656_, lean_object* v_s_657_){
_start:
{
uint8_t v_b_boxed_658_; lean_object* v_res_659_; 
v_b_boxed_658_ = lean_unbox(v_b_656_);
v_res_659_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_boxed_658_, v_s_657_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(lean_object* v_r_660_, uint8_t v_b_661_, lean_object* v_s_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_661_, v_s_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___boxed(lean_object* v_r_664_, lean_object* v_b_665_, lean_object* v_s_666_){
_start:
{
uint8_t v_b_boxed_667_; lean_object* v_res_668_; 
v_b_boxed_667_ = lean_unbox(v_b_665_);
v_res_668_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(v_r_664_, v_b_boxed_667_, v_s_666_);
lean_dec_ref(v_r_664_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(lean_object* v_r_669_, lean_object* v_as_670_, size_t v_i_671_, size_t v_stop_672_, lean_object* v_b_673_){
_start:
{
lean_object* v___y_675_; uint8_t v___x_679_; 
v___x_679_ = lean_usize_dec_eq(v_i_671_, v_stop_672_);
if (v___x_679_ == 0)
{
uint8_t v___x_680_; uint8_t v___x_681_; uint8_t v___x_687_; 
v___x_680_ = lean_byte_array_uget(v_as_670_, v_i_671_);
v___x_681_ = 43;
v___x_687_ = lean_uint8_dec_eq(v___x_680_, v___x_681_);
if (v___x_687_ == 0)
{
uint8_t v___x_688_; uint8_t v___x_689_; 
v___x_688_ = 128;
v___x_689_ = lean_uint8_dec_lt(v___x_680_, v___x_688_);
if (v___x_689_ == 0)
{
goto v___jp_682_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = lean_box(v___x_680_);
lean_inc_ref(v_r_669_);
v___x_691_ = lean_apply_1(v_r_669_, v___x_690_);
v___x_692_ = lean_unbox(v___x_691_);
if (v___x_692_ == 0)
{
goto v___jp_682_;
}
else
{
lean_object* v___x_693_; 
v___x_693_ = lean_byte_array_push(v_b_673_, v___x_680_);
v___y_675_ = v___x_693_;
goto v___jp_674_;
}
}
}
else
{
lean_object* v___x_694_; 
v___x_694_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v___x_680_, v_b_673_);
v___y_675_ = v___x_694_;
goto v___jp_674_;
}
v___jp_682_:
{
uint8_t v___x_683_; uint8_t v___x_684_; 
v___x_683_ = 32;
v___x_684_ = lean_uint8_dec_eq(v___x_680_, v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
v___x_685_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v___x_680_, v_b_673_);
v___y_675_ = v___x_685_;
goto v___jp_674_;
}
else
{
lean_object* v___x_686_; 
v___x_686_ = lean_byte_array_push(v_b_673_, v___x_681_);
v___y_675_ = v___x_686_;
goto v___jp_674_;
}
}
}
else
{
lean_dec_ref(v_r_669_);
return v_b_673_;
}
v___jp_674_:
{
size_t v___x_676_; size_t v___x_677_; 
v___x_676_ = ((size_t)1ULL);
v___x_677_ = lean_usize_add(v_i_671_, v___x_676_);
v_i_671_ = v___x_677_;
v_b_673_ = v___y_675_;
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
size_t v___x_710_; size_t v___x_711_; lean_object* v___x_712_; 
v___x_710_ = ((size_t)0ULL);
v___x_711_ = lean_usize_of_nat(v___x_708_);
v___x_712_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_704_, v___x_706_, v___x_710_, v___x_711_, v___x_705_);
lean_dec_ref(v___x_706_);
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___redArg(lean_object* v_es_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = lean_string_from_utf8_unchecked(v_es_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString(lean_object* v_r_715_, lean_object* v_es_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_string_from_utf8_unchecked(v_es_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___boxed(lean_object* v_r_718_, lean_object* v_es_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_Http_URI_EncodedQueryString_toString(v_r_718_, v_es_719_);
lean_dec_ref(v_r_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(lean_object* v_len_721_, lean_object* v_rawBytes_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_fst_724_; lean_object* v_snd_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_791_; 
v_fst_724_ = lean_ctor_get(v_a_723_, 0);
v_snd_725_ = lean_ctor_get(v_a_723_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v_a_723_);
if (v_isSharedCheck_791_ == 0)
{
v___x_727_ = v_a_723_;
v_isShared_728_ = v_isSharedCheck_791_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_snd_725_);
lean_inc(v_fst_724_);
lean_dec(v_a_723_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_791_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
uint8_t v___x_729_; 
v___x_729_ = lean_nat_dec_lt(v_snd_725_, v_len_721_);
if (v___x_729_ == 0)
{
lean_object* v___x_731_; 
if (v_isShared_728_ == 0)
{
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_fst_724_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_snd_725_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
else
{
uint8_t v_plus_733_; uint8_t v___x_734_; uint8_t v___x_743_; 
v_plus_733_ = 43;
v___x_734_ = lean_byte_array_fget(v_rawBytes_722_, v_snd_725_);
v___x_743_ = lean_uint8_dec_eq(v___x_734_, v_plus_733_);
if (v___x_743_ == 0)
{
uint8_t v_percent_744_; uint8_t v___x_745_; 
v_percent_744_ = 37;
v___x_745_ = lean_uint8_dec_eq(v___x_734_, v_percent_744_);
if (v___x_745_ == 0)
{
goto v___jp_735_;
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_nat_add(v_snd_725_, v___x_746_);
v___x_748_ = lean_nat_dec_lt(v___x_747_, v_len_721_);
if (v___x_748_ == 0)
{
lean_dec(v___x_747_);
goto v___jp_735_;
}
else
{
uint8_t v___x_749_; lean_object* v___x_750_; 
lean_del_object(v___x_727_);
v___x_749_ = lean_byte_array_fget(v_rawBytes_722_, v___x_747_);
lean_dec(v___x_747_);
v___x_750_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_749_);
if (lean_obj_tag(v___x_750_) == 1)
{
lean_object* v_val_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v_val_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_val_751_);
lean_dec_ref_known(v___x_750_, 1);
v___x_752_ = lean_unsigned_to_nat(2u);
v___x_753_ = lean_nat_add(v_snd_725_, v___x_752_);
v___x_754_ = lean_nat_dec_lt(v___x_753_, v_len_721_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec(v_val_751_);
lean_dec(v_snd_725_);
v___x_755_ = lean_byte_array_push(v_fst_724_, v___x_734_);
v___x_756_ = lean_byte_array_push(v___x_755_, v___x_749_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
lean_ctor_set(v___x_757_, 1, v___x_753_);
v_a_723_ = v___x_757_;
goto _start;
}
else
{
uint8_t v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_byte_array_fget(v_rawBytes_722_, v___x_753_);
lean_dec(v___x_753_);
v___x_760_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_759_);
if (lean_obj_tag(v___x_760_) == 1)
{
lean_object* v_val_761_; uint8_t v___x_762_; uint8_t v___x_763_; uint8_t v___x_764_; uint8_t v___x_765_; uint8_t v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_val_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_val_761_);
lean_dec_ref_known(v___x_760_, 1);
v___x_762_ = 4;
v___x_763_ = lean_unbox(v_val_751_);
lean_dec(v_val_751_);
v___x_764_ = lean_uint8_shift_left(v___x_763_, v___x_762_);
v___x_765_ = lean_unbox(v_val_761_);
lean_dec(v_val_761_);
v___x_766_ = lean_uint8_add(v___x_764_, v___x_765_);
v___x_767_ = lean_byte_array_push(v_fst_724_, v___x_766_);
v___x_768_ = lean_unsigned_to_nat(3u);
v___x_769_ = lean_nat_add(v_snd_725_, v___x_768_);
lean_dec(v_snd_725_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_767_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v_a_723_ = v___x_770_;
goto _start;
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
lean_dec(v___x_760_);
lean_dec(v_val_751_);
v___x_772_ = lean_byte_array_push(v_fst_724_, v___x_734_);
v___x_773_ = lean_byte_array_push(v___x_772_, v___x_749_);
v___x_774_ = lean_byte_array_push(v___x_773_, v___x_759_);
v___x_775_ = lean_unsigned_to_nat(3u);
v___x_776_ = lean_nat_add(v_snd_725_, v___x_775_);
lean_dec(v_snd_725_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_774_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v_a_723_ = v___x_777_;
goto _start;
}
}
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec(v___x_750_);
v___x_779_ = lean_byte_array_push(v_fst_724_, v___x_734_);
v___x_780_ = lean_byte_array_push(v___x_779_, v___x_749_);
v___x_781_ = lean_unsigned_to_nat(2u);
v___x_782_ = lean_nat_add(v_snd_725_, v___x_781_);
lean_dec(v_snd_725_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_780_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v_a_723_ = v___x_783_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
lean_del_object(v___x_727_);
v___x_785_ = 32;
v___x_786_ = lean_byte_array_push(v_fst_724_, v___x_785_);
v___x_787_ = lean_unsigned_to_nat(1u);
v___x_788_ = lean_nat_add(v_snd_725_, v___x_787_);
lean_dec(v_snd_725_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_786_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v_a_723_ = v___x_789_;
goto _start;
}
v___jp_735_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_736_ = lean_byte_array_push(v_fst_724_, v___x_734_);
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_nat_add(v_snd_725_, v___x_737_);
lean_dec(v_snd_725_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v___x_738_);
lean_ctor_set(v___x_727_, 0, v___x_736_);
v___x_740_ = v___x_727_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_738_);
v___x_740_ = v_reuseFailAlloc_742_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
v_a_723_ = v___x_740_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg___boxed(lean_object* v_len_792_, lean_object* v_rawBytes_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_792_, v_rawBytes_793_, v_a_794_);
lean_dec_ref(v_rawBytes_793_);
lean_dec(v_len_792_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg(lean_object* v_es_796_){
_start:
{
lean_object* v_len_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v_fst_800_; uint8_t v___x_801_; 
v_len_797_ = lean_byte_array_size(v_es_796_);
v___x_798_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_799_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_797_, v_es_796_, v___x_798_);
v_fst_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_fst_800_);
lean_dec_ref(v___x_799_);
v___x_801_ = lean_string_validate_utf8(v_fst_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; 
lean_dec(v_fst_800_);
v___x_802_ = lean_box(0);
return v___x_802_;
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_string_from_utf8_unchecked(v_fst_800_);
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg___boxed(lean_object* v_es_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_805_);
lean_dec_ref(v_es_805_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode(lean_object* v_r_807_, lean_object* v_es_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___boxed(lean_object* v_r_810_, lean_object* v_es_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Std_Http_URI_EncodedQueryString_decode(v_r_810_, v_es_811_);
lean_dec_ref(v_es_811_);
lean_dec_ref(v_r_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(lean_object* v_len_813_, lean_object* v_rawBytes_814_, lean_object* v_inst_815_, lean_object* v_a_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_813_, v_rawBytes_814_, v_a_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___boxed(lean_object* v_len_818_, lean_object* v_rawBytes_819_, lean_object* v_inst_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(v_len_818_, v_rawBytes_819_, v_inst_820_, v_a_821_);
lean_dec_ref(v_rawBytes_819_);
lean_dec(v_len_818_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringEncodedQueryString(lean_object* v_r_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = lean_alloc_closure((void*)(l_Std_Http_URI_EncodedQueryString_toString___boxed), 2, 1);
lean_closure_set(v___x_824_, 0, v_r_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_826_; 
v___f_826_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_826_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___redArg___boxed(lean_object* v___dummy_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Std_Http_URI_instReprEncodedQueryString___redArg();
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString(lean_object* v_r_829_){
_start:
{
lean_object* v___f_830_; 
v___f_830_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_830_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___boxed(lean_object* v_r_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_Http_URI_instReprEncodedQueryString(v_r_831_);
lean_dec_ref(v_r_831_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_834_; 
v___f_834_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_834_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___redArg___boxed(lean_object* v___dummy_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_Http_URI_instBEqEncodedQueryString___redArg();
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString(lean_object* v_r_837_){
_start:
{
lean_object* v___f_838_; 
v___f_838_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_838_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___boxed(lean_object* v_r_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_Http_URI_instBEqEncodedQueryString(v_r_839_);
lean_dec_ref(v_r_839_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_842_; 
v___f_842_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_842_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___redArg___boxed(lean_object* v___dummy_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_Http_URI_instHashableEncodedQueryString___redArg();
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString(lean_object* v_r_845_){
_start:
{
lean_object* v___f_846_; 
v___f_846_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_846_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___boxed(lean_object* v_r_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_Http_URI_instHashableEncodedQueryString(v_r_847_);
lean_dec_ref(v_r_847_);
return v_res_848_;
}
}
static uint64_t _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_855_; uint64_t v___x_856_; 
v___x_855_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__0));
v___x_856_ = lean_byte_array_hash(v___x_855_);
return v___x_856_;
}
}
static lean_object* _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__2));
v___x_864_ = lean_byte_array_size(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT uint64_t l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0(lean_object* v_x_865_){
_start:
{
if (lean_obj_tag(v_x_865_) == 0)
{
uint64_t v___x_866_; 
v___x_866_ = lean_uint64_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1, &l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1);
return v___x_866_;
}
else
{
lean_object* v_val_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___x_872_; lean_object* v___x_873_; uint64_t v___x_874_; 
v_val_867_ = lean_ctor_get(v_x_865_, 0);
v___x_868_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__2));
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = lean_obj_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3, &l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3);
v___x_871_ = lean_byte_array_size(v_val_867_);
v___x_872_ = 0;
v___x_873_ = lean_byte_array_copy_slice(v_val_867_, v___x_869_, v___x_868_, v___x_870_, v___x_871_, v___x_872_);
v___x_874_ = lean_byte_array_hash(v___x_873_);
lean_dec_ref(v___x_873_);
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___boxed(lean_object* v_x_875_){
_start:
{
uint64_t v_res_876_; lean_object* v_r_877_; 
v_res_876_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0(v_x_875_);
lean_dec(v_x_875_);
v_r_877_ = lean_box_uint64(v_res_876_);
return v_r_877_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_880_; 
v___f_880_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___closed__0));
return v___f_880_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___boxed(lean_object* v___dummy_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg();
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString(lean_object* v_r_883_){
_start:
{
lean_object* v___f_884_; 
v___f_884_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___closed__0));
return v___f_884_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___boxed(lean_object* v_r_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Std_Http_URI_instHashableOptionEncodedQueryString(v_r_885_);
lean_dec_ref(v_r_885_);
return v_res_886_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0(uint8_t v___y_887_){
_start:
{
uint8_t v___x_933_; uint8_t v___x_934_; 
v___x_933_ = 48;
v___x_934_ = lean_uint8_dec_le(v___x_933_, v___y_887_);
if (v___x_934_ == 0)
{
goto v___jp_928_;
}
else
{
uint8_t v___x_935_; uint8_t v___x_936_; 
v___x_935_ = 57;
v___x_936_ = lean_uint8_dec_le(v___y_887_, v___x_935_);
if (v___x_936_ == 0)
{
goto v___jp_928_;
}
else
{
return v___x_936_;
}
}
v___jp_888_:
{
uint8_t v___x_889_; uint8_t v___x_890_; 
v___x_889_ = 45;
v___x_890_ = lean_uint8_dec_eq(v___y_887_, v___x_889_);
if (v___x_890_ == 0)
{
uint8_t v___x_891_; uint8_t v___x_892_; 
v___x_891_ = 46;
v___x_892_ = lean_uint8_dec_eq(v___y_887_, v___x_891_);
if (v___x_892_ == 0)
{
uint8_t v___x_893_; uint8_t v___x_894_; 
v___x_893_ = 95;
v___x_894_ = lean_uint8_dec_eq(v___y_887_, v___x_893_);
if (v___x_894_ == 0)
{
uint8_t v___x_895_; uint8_t v___x_896_; 
v___x_895_ = 126;
v___x_896_ = lean_uint8_dec_eq(v___y_887_, v___x_895_);
if (v___x_896_ == 0)
{
uint8_t v___x_897_; uint8_t v___x_898_; 
v___x_897_ = 33;
v___x_898_ = lean_uint8_dec_eq(v___y_887_, v___x_897_);
if (v___x_898_ == 0)
{
uint8_t v___x_899_; uint8_t v___x_900_; 
v___x_899_ = 36;
v___x_900_ = lean_uint8_dec_eq(v___y_887_, v___x_899_);
if (v___x_900_ == 0)
{
uint8_t v___x_901_; uint8_t v___x_902_; 
v___x_901_ = 38;
v___x_902_ = lean_uint8_dec_eq(v___y_887_, v___x_901_);
if (v___x_902_ == 0)
{
uint8_t v___x_903_; uint8_t v___x_904_; 
v___x_903_ = 39;
v___x_904_ = lean_uint8_dec_eq(v___y_887_, v___x_903_);
if (v___x_904_ == 0)
{
uint8_t v___x_905_; uint8_t v___x_906_; 
v___x_905_ = 40;
v___x_906_ = lean_uint8_dec_eq(v___y_887_, v___x_905_);
if (v___x_906_ == 0)
{
uint8_t v___x_907_; uint8_t v___x_908_; 
v___x_907_ = 41;
v___x_908_ = lean_uint8_dec_eq(v___y_887_, v___x_907_);
if (v___x_908_ == 0)
{
uint8_t v___x_909_; uint8_t v___x_910_; 
v___x_909_ = 42;
v___x_910_ = lean_uint8_dec_eq(v___y_887_, v___x_909_);
if (v___x_910_ == 0)
{
uint8_t v___x_911_; uint8_t v___x_912_; 
v___x_911_ = 43;
v___x_912_ = lean_uint8_dec_eq(v___y_887_, v___x_911_);
if (v___x_912_ == 0)
{
uint8_t v___x_913_; uint8_t v___x_914_; 
v___x_913_ = 44;
v___x_914_ = lean_uint8_dec_eq(v___y_887_, v___x_913_);
if (v___x_914_ == 0)
{
uint8_t v___x_915_; uint8_t v___x_916_; 
v___x_915_ = 59;
v___x_916_ = lean_uint8_dec_eq(v___y_887_, v___x_915_);
if (v___x_916_ == 0)
{
uint8_t v___x_917_; uint8_t v___x_918_; 
v___x_917_ = 61;
v___x_918_ = lean_uint8_dec_eq(v___y_887_, v___x_917_);
if (v___x_918_ == 0)
{
uint8_t v___x_919_; uint8_t v___x_920_; 
v___x_919_ = 58;
v___x_920_ = lean_uint8_dec_eq(v___y_887_, v___x_919_);
if (v___x_920_ == 0)
{
uint8_t v___x_921_; uint8_t v___x_922_; 
v___x_921_ = 64;
v___x_922_ = lean_uint8_dec_eq(v___y_887_, v___x_921_);
return v___x_922_;
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
else
{
return v___x_904_;
}
}
else
{
return v___x_902_;
}
}
else
{
return v___x_900_;
}
}
else
{
return v___x_898_;
}
}
else
{
return v___x_896_;
}
}
else
{
return v___x_894_;
}
}
else
{
return v___x_892_;
}
}
else
{
return v___x_890_;
}
}
v___jp_923_:
{
uint8_t v___x_924_; uint8_t v___x_925_; 
v___x_924_ = 65;
v___x_925_ = lean_uint8_dec_le(v___x_924_, v___y_887_);
if (v___x_925_ == 0)
{
goto v___jp_888_;
}
else
{
uint8_t v___x_926_; uint8_t v___x_927_; 
v___x_926_ = 90;
v___x_927_ = lean_uint8_dec_le(v___y_887_, v___x_926_);
if (v___x_927_ == 0)
{
goto v___jp_888_;
}
else
{
return v___x_927_;
}
}
}
v___jp_928_:
{
uint8_t v___x_929_; uint8_t v___x_930_; 
v___x_929_ = 97;
v___x_930_ = lean_uint8_dec_le(v___x_929_, v___y_887_);
if (v___x_930_ == 0)
{
goto v___jp_923_;
}
else
{
uint8_t v___x_931_; uint8_t v___x_932_; 
v___x_931_ = 122;
v___x_932_ = lean_uint8_dec_le(v___y_887_, v___x_931_);
if (v___x_932_ == 0)
{
goto v___jp_923_;
}
else
{
return v___x_932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___lam__0___boxed(lean_object* v___y_937_){
_start:
{
uint8_t v___y_265__boxed_938_; uint8_t v_res_939_; lean_object* v_r_940_; 
v___y_265__boxed_938_ = lean_unbox(v___y_937_);
v_res_939_ = l_Std_Http_URI_EncodedSegment_encode___lam__0(v___y_265__boxed_938_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode(lean_object* v_s_942_){
_start:
{
lean_object* v___f_943_; lean_object* v___x_944_; 
v___f_943_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_944_ = l_Std_Http_URI_EncodedString_encode(v___f_943_, v_s_942_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object* v_ba_945_){
_start:
{
lean_object* v___f_946_; lean_object* v___x_947_; 
v___f_946_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_947_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_946_, v_ba_945_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x21(lean_object* v_ba_948_){
_start:
{
lean_object* v___f_949_; lean_object* v___x_950_; 
v___f_949_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_950_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_949_, v_ba_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object* v_segment_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Std_Http_URI_EncodedString_decode___redArg(v_segment_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode___boxed(lean_object* v_segment_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Std_Http_URI_EncodedSegment_decode(v_segment_953_);
lean_dec_ref(v_segment_953_);
return v_res_954_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedFragment_encode___lam__0(uint8_t v___y_955_){
_start:
{
uint8_t v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = 48;
v___x_1006_ = lean_uint8_dec_le(v___x_1005_, v___y_955_);
if (v___x_1006_ == 0)
{
goto v___jp_1000_;
}
else
{
uint8_t v___x_1007_; uint8_t v___x_1008_; 
v___x_1007_ = 57;
v___x_1008_ = lean_uint8_dec_le(v___y_955_, v___x_1007_);
if (v___x_1008_ == 0)
{
goto v___jp_1000_;
}
else
{
return v___x_1008_;
}
}
v___jp_956_:
{
uint8_t v___x_957_; uint8_t v___x_958_; 
v___x_957_ = 45;
v___x_958_ = lean_uint8_dec_eq(v___y_955_, v___x_957_);
if (v___x_958_ == 0)
{
uint8_t v___x_959_; uint8_t v___x_960_; 
v___x_959_ = 46;
v___x_960_ = lean_uint8_dec_eq(v___y_955_, v___x_959_);
if (v___x_960_ == 0)
{
uint8_t v___x_961_; uint8_t v___x_962_; 
v___x_961_ = 95;
v___x_962_ = lean_uint8_dec_eq(v___y_955_, v___x_961_);
if (v___x_962_ == 0)
{
uint8_t v___x_963_; uint8_t v___x_964_; 
v___x_963_ = 126;
v___x_964_ = lean_uint8_dec_eq(v___y_955_, v___x_963_);
if (v___x_964_ == 0)
{
uint8_t v___x_965_; uint8_t v___x_966_; 
v___x_965_ = 33;
v___x_966_ = lean_uint8_dec_eq(v___y_955_, v___x_965_);
if (v___x_966_ == 0)
{
uint8_t v___x_967_; uint8_t v___x_968_; 
v___x_967_ = 36;
v___x_968_ = lean_uint8_dec_eq(v___y_955_, v___x_967_);
if (v___x_968_ == 0)
{
uint8_t v___x_969_; uint8_t v___x_970_; 
v___x_969_ = 38;
v___x_970_ = lean_uint8_dec_eq(v___y_955_, v___x_969_);
if (v___x_970_ == 0)
{
uint8_t v___x_971_; uint8_t v___x_972_; 
v___x_971_ = 39;
v___x_972_ = lean_uint8_dec_eq(v___y_955_, v___x_971_);
if (v___x_972_ == 0)
{
uint8_t v___x_973_; uint8_t v___x_974_; 
v___x_973_ = 40;
v___x_974_ = lean_uint8_dec_eq(v___y_955_, v___x_973_);
if (v___x_974_ == 0)
{
uint8_t v___x_975_; uint8_t v___x_976_; 
v___x_975_ = 41;
v___x_976_ = lean_uint8_dec_eq(v___y_955_, v___x_975_);
if (v___x_976_ == 0)
{
uint8_t v___x_977_; uint8_t v___x_978_; 
v___x_977_ = 42;
v___x_978_ = lean_uint8_dec_eq(v___y_955_, v___x_977_);
if (v___x_978_ == 0)
{
uint8_t v___x_979_; uint8_t v___x_980_; 
v___x_979_ = 43;
v___x_980_ = lean_uint8_dec_eq(v___y_955_, v___x_979_);
if (v___x_980_ == 0)
{
uint8_t v___x_981_; uint8_t v___x_982_; 
v___x_981_ = 44;
v___x_982_ = lean_uint8_dec_eq(v___y_955_, v___x_981_);
if (v___x_982_ == 0)
{
uint8_t v___x_983_; uint8_t v___x_984_; 
v___x_983_ = 59;
v___x_984_ = lean_uint8_dec_eq(v___y_955_, v___x_983_);
if (v___x_984_ == 0)
{
uint8_t v___x_985_; uint8_t v___x_986_; 
v___x_985_ = 61;
v___x_986_ = lean_uint8_dec_eq(v___y_955_, v___x_985_);
if (v___x_986_ == 0)
{
uint8_t v___x_987_; uint8_t v___x_988_; 
v___x_987_ = 58;
v___x_988_ = lean_uint8_dec_eq(v___y_955_, v___x_987_);
if (v___x_988_ == 0)
{
uint8_t v___x_989_; uint8_t v___x_990_; 
v___x_989_ = 64;
v___x_990_ = lean_uint8_dec_eq(v___y_955_, v___x_989_);
if (v___x_990_ == 0)
{
uint8_t v___x_991_; uint8_t v___x_992_; 
v___x_991_ = 47;
v___x_992_ = lean_uint8_dec_eq(v___y_955_, v___x_991_);
if (v___x_992_ == 0)
{
uint8_t v___x_993_; uint8_t v___x_994_; 
v___x_993_ = 63;
v___x_994_ = lean_uint8_dec_eq(v___y_955_, v___x_993_);
return v___x_994_;
}
else
{
return v___x_992_;
}
}
else
{
return v___x_990_;
}
}
else
{
return v___x_988_;
}
}
else
{
return v___x_986_;
}
}
else
{
return v___x_984_;
}
}
else
{
return v___x_982_;
}
}
else
{
return v___x_980_;
}
}
else
{
return v___x_978_;
}
}
else
{
return v___x_976_;
}
}
else
{
return v___x_974_;
}
}
else
{
return v___x_972_;
}
}
else
{
return v___x_970_;
}
}
else
{
return v___x_968_;
}
}
else
{
return v___x_966_;
}
}
else
{
return v___x_964_;
}
}
else
{
return v___x_962_;
}
}
else
{
return v___x_960_;
}
}
else
{
return v___x_958_;
}
}
v___jp_995_:
{
uint8_t v___x_996_; uint8_t v___x_997_; 
v___x_996_ = 65;
v___x_997_ = lean_uint8_dec_le(v___x_996_, v___y_955_);
if (v___x_997_ == 0)
{
goto v___jp_956_;
}
else
{
uint8_t v___x_998_; uint8_t v___x_999_; 
v___x_998_ = 90;
v___x_999_ = lean_uint8_dec_le(v___y_955_, v___x_998_);
if (v___x_999_ == 0)
{
goto v___jp_956_;
}
else
{
return v___x_999_;
}
}
}
v___jp_1000_:
{
uint8_t v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = 97;
v___x_1002_ = lean_uint8_dec_le(v___x_1001_, v___y_955_);
if (v___x_1002_ == 0)
{
goto v___jp_995_;
}
else
{
uint8_t v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = 122;
v___x_1004_ = lean_uint8_dec_le(v___y_955_, v___x_1003_);
if (v___x_1004_ == 0)
{
goto v___jp_995_;
}
else
{
return v___x_1004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed(lean_object* v___y_1009_){
_start:
{
uint8_t v___y_289__boxed_1010_; uint8_t v_res_1011_; lean_object* v_r_1012_; 
v___y_289__boxed_1010_ = lean_unbox(v___y_1009_);
v_res_1011_ = l_Std_Http_URI_EncodedFragment_encode___lam__0(v___y_289__boxed_1010_);
v_r_1012_ = lean_box(v_res_1011_);
return v_r_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object* v_s_1014_){
_start:
{
lean_object* v___f_1015_; lean_object* v___x_1016_; 
v___f_1015_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1016_ = l_Std_Http_URI_EncodedString_encode(v___f_1015_, v_s_1014_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object* v_ba_1017_){
_start:
{
lean_object* v___f_1018_; lean_object* v___x_1019_; 
v___f_1018_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1019_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1018_, v_ba_1017_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x21(lean_object* v_ba_1020_){
_start:
{
lean_object* v___f_1021_; lean_object* v___x_1022_; 
v___f_1021_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1022_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1021_, v_ba_1020_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object* v_fragment_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Std_Http_URI_EncodedString_decode___redArg(v_fragment_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode___boxed(lean_object* v_fragment_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Std_Http_URI_EncodedFragment_decode(v_fragment_1025_);
lean_dec_ref(v_fragment_1025_);
return v_res_1026_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedUserInfo_encode___lam__0(uint8_t v___y_1027_){
_start:
{
uint8_t v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = 48;
v___x_1072_ = lean_uint8_dec_le(v___x_1071_, v___y_1027_);
if (v___x_1072_ == 0)
{
goto v___jp_1066_;
}
else
{
uint8_t v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = 57;
v___x_1074_ = lean_uint8_dec_le(v___y_1027_, v___x_1073_);
if (v___x_1074_ == 0)
{
goto v___jp_1066_;
}
else
{
return v___x_1074_;
}
}
v___jp_1028_:
{
uint8_t v___x_1029_; uint8_t v___x_1030_; 
v___x_1029_ = 45;
v___x_1030_ = lean_uint8_dec_eq(v___y_1027_, v___x_1029_);
if (v___x_1030_ == 0)
{
uint8_t v___x_1031_; uint8_t v___x_1032_; 
v___x_1031_ = 46;
v___x_1032_ = lean_uint8_dec_eq(v___y_1027_, v___x_1031_);
if (v___x_1032_ == 0)
{
uint8_t v___x_1033_; uint8_t v___x_1034_; 
v___x_1033_ = 95;
v___x_1034_ = lean_uint8_dec_eq(v___y_1027_, v___x_1033_);
if (v___x_1034_ == 0)
{
uint8_t v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = 126;
v___x_1036_ = lean_uint8_dec_eq(v___y_1027_, v___x_1035_);
if (v___x_1036_ == 0)
{
uint8_t v___x_1037_; uint8_t v___x_1038_; 
v___x_1037_ = 33;
v___x_1038_ = lean_uint8_dec_eq(v___y_1027_, v___x_1037_);
if (v___x_1038_ == 0)
{
uint8_t v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = 36;
v___x_1040_ = lean_uint8_dec_eq(v___y_1027_, v___x_1039_);
if (v___x_1040_ == 0)
{
uint8_t v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = 38;
v___x_1042_ = lean_uint8_dec_eq(v___y_1027_, v___x_1041_);
if (v___x_1042_ == 0)
{
uint8_t v___x_1043_; uint8_t v___x_1044_; 
v___x_1043_ = 39;
v___x_1044_ = lean_uint8_dec_eq(v___y_1027_, v___x_1043_);
if (v___x_1044_ == 0)
{
uint8_t v___x_1045_; uint8_t v___x_1046_; 
v___x_1045_ = 40;
v___x_1046_ = lean_uint8_dec_eq(v___y_1027_, v___x_1045_);
if (v___x_1046_ == 0)
{
uint8_t v___x_1047_; uint8_t v___x_1048_; 
v___x_1047_ = 41;
v___x_1048_ = lean_uint8_dec_eq(v___y_1027_, v___x_1047_);
if (v___x_1048_ == 0)
{
uint8_t v___x_1049_; uint8_t v___x_1050_; 
v___x_1049_ = 42;
v___x_1050_ = lean_uint8_dec_eq(v___y_1027_, v___x_1049_);
if (v___x_1050_ == 0)
{
uint8_t v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = 43;
v___x_1052_ = lean_uint8_dec_eq(v___y_1027_, v___x_1051_);
if (v___x_1052_ == 0)
{
uint8_t v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = 44;
v___x_1054_ = lean_uint8_dec_eq(v___y_1027_, v___x_1053_);
if (v___x_1054_ == 0)
{
uint8_t v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = 59;
v___x_1056_ = lean_uint8_dec_eq(v___y_1027_, v___x_1055_);
if (v___x_1056_ == 0)
{
uint8_t v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = 61;
v___x_1058_ = lean_uint8_dec_eq(v___y_1027_, v___x_1057_);
if (v___x_1058_ == 0)
{
uint8_t v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = 58;
v___x_1060_ = lean_uint8_dec_eq(v___y_1027_, v___x_1059_);
return v___x_1060_;
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
else
{
return v___x_1050_;
}
}
else
{
return v___x_1048_;
}
}
else
{
return v___x_1046_;
}
}
else
{
return v___x_1044_;
}
}
else
{
return v___x_1042_;
}
}
else
{
return v___x_1040_;
}
}
else
{
return v___x_1038_;
}
}
else
{
return v___x_1036_;
}
}
else
{
return v___x_1034_;
}
}
else
{
return v___x_1032_;
}
}
else
{
return v___x_1030_;
}
}
v___jp_1061_:
{
uint8_t v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = 65;
v___x_1063_ = lean_uint8_dec_le(v___x_1062_, v___y_1027_);
if (v___x_1063_ == 0)
{
goto v___jp_1028_;
}
else
{
uint8_t v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = 90;
v___x_1065_ = lean_uint8_dec_le(v___y_1027_, v___x_1064_);
if (v___x_1065_ == 0)
{
goto v___jp_1028_;
}
else
{
return v___x_1065_;
}
}
}
v___jp_1066_:
{
uint8_t v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = 97;
v___x_1068_ = lean_uint8_dec_le(v___x_1067_, v___y_1027_);
if (v___x_1068_ == 0)
{
goto v___jp_1061_;
}
else
{
uint8_t v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = 122;
v___x_1070_ = lean_uint8_dec_le(v___y_1027_, v___x_1069_);
if (v___x_1070_ == 0)
{
goto v___jp_1061_;
}
else
{
return v___x_1070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed(lean_object* v___y_1075_){
_start:
{
uint8_t v___y_253__boxed_1076_; uint8_t v_res_1077_; lean_object* v_r_1078_; 
v___y_253__boxed_1076_ = lean_unbox(v___y_1075_);
v_res_1077_ = l_Std_Http_URI_EncodedUserInfo_encode___lam__0(v___y_253__boxed_1076_);
v_r_1078_ = lean_box(v_res_1077_);
return v_r_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object* v_s_1080_){
_start:
{
lean_object* v___f_1081_; lean_object* v___x_1082_; 
v___f_1081_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1082_ = l_Std_Http_URI_EncodedString_encode(v___f_1081_, v_s_1080_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object* v_ba_1083_){
_start:
{
lean_object* v___f_1084_; lean_object* v___x_1085_; 
v___f_1084_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1085_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1084_, v_ba_1083_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x21(lean_object* v_ba_1086_){
_start:
{
lean_object* v___f_1087_; lean_object* v___x_1088_; 
v___f_1087_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1088_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1087_, v_ba_1086_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode(lean_object* v_userInfo_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Std_Http_URI_EncodedString_decode___redArg(v_userInfo_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode___boxed(lean_object* v_userInfo_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Std_Http_URI_EncodedUserInfo_decode(v_userInfo_1091_);
lean_dec_ref(v_userInfo_1091_);
return v_res_1092_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryParam_encode___lam__0(uint8_t v___y_1093_){
_start:
{
uint8_t v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = 48;
v___x_1151_ = lean_uint8_dec_le(v___x_1150_, v___y_1093_);
if (v___x_1151_ == 0)
{
goto v___jp_1145_;
}
else
{
uint8_t v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = 57;
v___x_1153_ = lean_uint8_dec_le(v___y_1093_, v___x_1152_);
if (v___x_1153_ == 0)
{
goto v___jp_1145_;
}
else
{
goto v___jp_1094_;
}
}
v___jp_1094_:
{
uint8_t v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = 38;
v___x_1096_ = lean_uint8_dec_eq(v___y_1093_, v___x_1095_);
if (v___x_1096_ == 0)
{
uint8_t v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = 61;
v___x_1098_ = lean_uint8_dec_eq(v___y_1093_, v___x_1097_);
if (v___x_1098_ == 0)
{
uint8_t v___x_1099_; 
v___x_1099_ = 1;
return v___x_1099_;
}
else
{
return v___x_1096_;
}
}
else
{
uint8_t v___x_1100_; 
v___x_1100_ = 0;
return v___x_1100_;
}
}
v___jp_1101_:
{
uint8_t v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = 45;
v___x_1103_ = lean_uint8_dec_eq(v___y_1093_, v___x_1102_);
if (v___x_1103_ == 0)
{
uint8_t v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = 46;
v___x_1105_ = lean_uint8_dec_eq(v___y_1093_, v___x_1104_);
if (v___x_1105_ == 0)
{
uint8_t v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = 95;
v___x_1107_ = lean_uint8_dec_eq(v___y_1093_, v___x_1106_);
if (v___x_1107_ == 0)
{
uint8_t v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = 126;
v___x_1109_ = lean_uint8_dec_eq(v___y_1093_, v___x_1108_);
if (v___x_1109_ == 0)
{
uint8_t v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = 33;
v___x_1111_ = lean_uint8_dec_eq(v___y_1093_, v___x_1110_);
if (v___x_1111_ == 0)
{
uint8_t v___x_1112_; uint8_t v___x_1113_; 
v___x_1112_ = 36;
v___x_1113_ = lean_uint8_dec_eq(v___y_1093_, v___x_1112_);
if (v___x_1113_ == 0)
{
uint8_t v___x_1114_; uint8_t v___x_1115_; 
v___x_1114_ = 38;
v___x_1115_ = lean_uint8_dec_eq(v___y_1093_, v___x_1114_);
if (v___x_1115_ == 0)
{
uint8_t v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = 39;
v___x_1117_ = lean_uint8_dec_eq(v___y_1093_, v___x_1116_);
if (v___x_1117_ == 0)
{
uint8_t v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = 40;
v___x_1119_ = lean_uint8_dec_eq(v___y_1093_, v___x_1118_);
if (v___x_1119_ == 0)
{
uint8_t v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = 41;
v___x_1121_ = lean_uint8_dec_eq(v___y_1093_, v___x_1120_);
if (v___x_1121_ == 0)
{
uint8_t v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = 42;
v___x_1123_ = lean_uint8_dec_eq(v___y_1093_, v___x_1122_);
if (v___x_1123_ == 0)
{
uint8_t v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = 43;
v___x_1125_ = lean_uint8_dec_eq(v___y_1093_, v___x_1124_);
if (v___x_1125_ == 0)
{
uint8_t v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = 44;
v___x_1127_ = lean_uint8_dec_eq(v___y_1093_, v___x_1126_);
if (v___x_1127_ == 0)
{
uint8_t v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = 59;
v___x_1129_ = lean_uint8_dec_eq(v___y_1093_, v___x_1128_);
if (v___x_1129_ == 0)
{
uint8_t v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = 61;
v___x_1131_ = lean_uint8_dec_eq(v___y_1093_, v___x_1130_);
if (v___x_1131_ == 0)
{
uint8_t v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = 58;
v___x_1133_ = lean_uint8_dec_eq(v___y_1093_, v___x_1132_);
if (v___x_1133_ == 0)
{
uint8_t v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = 64;
v___x_1135_ = lean_uint8_dec_eq(v___y_1093_, v___x_1134_);
if (v___x_1135_ == 0)
{
uint8_t v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = 47;
v___x_1137_ = lean_uint8_dec_eq(v___y_1093_, v___x_1136_);
if (v___x_1137_ == 0)
{
uint8_t v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = 63;
v___x_1139_ = lean_uint8_dec_eq(v___y_1093_, v___x_1138_);
if (v___x_1139_ == 0)
{
return v___x_1139_;
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
else
{
goto v___jp_1094_;
}
}
v___jp_1140_:
{
uint8_t v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = 65;
v___x_1142_ = lean_uint8_dec_le(v___x_1141_, v___y_1093_);
if (v___x_1142_ == 0)
{
goto v___jp_1101_;
}
else
{
uint8_t v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = 90;
v___x_1144_ = lean_uint8_dec_le(v___y_1093_, v___x_1143_);
if (v___x_1144_ == 0)
{
goto v___jp_1101_;
}
else
{
goto v___jp_1094_;
}
}
}
v___jp_1145_:
{
uint8_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = 97;
v___x_1147_ = lean_uint8_dec_le(v___x_1146_, v___y_1093_);
if (v___x_1147_ == 0)
{
goto v___jp_1140_;
}
else
{
uint8_t v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = 122;
v___x_1149_ = lean_uint8_dec_le(v___y_1093_, v___x_1148_);
if (v___x_1149_ == 0)
{
goto v___jp_1140_;
}
else
{
goto v___jp_1094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed(lean_object* v___y_1154_){
_start:
{
uint8_t v___y_363__boxed_1155_; uint8_t v_res_1156_; lean_object* v_r_1157_; 
v___y_363__boxed_1155_ = lean_unbox(v___y_1154_);
v_res_1156_ = l_Std_Http_URI_EncodedQueryParam_encode___lam__0(v___y_363__boxed_1155_);
v_r_1157_ = lean_box(v_res_1156_);
return v_r_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode(lean_object* v_s_1159_){
_start:
{
lean_object* v___f_1160_; lean_object* v___x_1161_; 
v___f_1160_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1161_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_1159_, v___f_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f(lean_object* v_ba_1162_){
_start:
{
lean_object* v___f_1163_; lean_object* v___x_1164_; 
v___f_1163_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1164_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_1162_, v___f_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x21(lean_object* v_ba_1165_){
_start:
{
lean_object* v___f_1166_; lean_object* v___x_1167_; 
v___f_1166_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1167_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v_ba_1165_, v___f_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object* v_s_1168_){
_start:
{
lean_object* v___f_1169_; lean_object* v___x_1170_; 
v___f_1169_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1170_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_1168_, v___f_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object* v_param_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_param_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode___boxed(lean_object* v_param_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Std_Http_URI_EncodedQueryParam_decode(v_param_1173_);
lean_dec_ref(v_param_1173_);
return v_res_1174_;
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
