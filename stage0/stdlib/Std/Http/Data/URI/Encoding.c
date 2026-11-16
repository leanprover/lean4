// Lean compiler output
// Module: Std.Http.Data.URI.Encoding
// Imports: import Init.Grind import Init.While import Init.Data.SInt.Lemmas import Init.Data.UInt.Lemmas import Init.Data.UInt.Bitwise import Init.Data.Array.Lemmas public import Init.Data.String.Basic import Init.Data.String.Lossy public import Std.Http.Internal.Char
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
lean_object* lean_byte_array_data(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_ByteArray_decEq___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_ByteArray_hash___boxed(lean_object*);
lean_object* l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_isEncodedChar(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_isEncodedChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_isEncodedQueryChar(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_isEncodedQueryChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encodeEscaping_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encodeEscaping_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encodeEscaping(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedString_ofByteArray_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedString_ofByteArray_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedString_ofByteArray_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedString_ofByteArray_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_URI_EncodedString_decodeLossy___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_URI_EncodedString_decodeLossy___redArg___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedString_decodeLossy___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decodeLossy___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decodeLossy___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decodeLossy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decodeLossy___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_URI_EncodedQueryString_decodesTo___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_URI_EncodedQueryString_decodesTo___redArg___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedQueryString_decodesTo___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_URI_EncodedQueryString_decodesTo___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_URI_EncodedQueryString_decodesTo___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_URI_EncodedQueryString_decodesTo___redArg___closed__1 = (const lean_object*)&l_Std_Http_URI_EncodedQueryString_decodesTo___redArg___closed__1_value;
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryString_decodesTo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decodesTo___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryString_decodesTo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decodesTo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f___closed__0 = (const lean_object*)&l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f___closed__0_value;
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
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(lean_object* v_s_41_, lean_object* v_r_42_, lean_object* v_i_43_, lean_object* v_h_44_){
_start:
{
uint8_t v___x_45_; uint8_t v___x_46_; 
v___x_45_ = lean_byte_array_fget(v_s_41_, v_i_43_);
v___x_46_ = l_Std_Http_URI_isEncodedChar(v_r_42_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed(lean_object* v_s_47_, lean_object* v_r_48_, lean_object* v_i_49_, lean_object* v_h_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(v_s_47_, v_r_48_, v_i_49_, v_h_50_);
lean_dec(v_i_49_);
lean_dec_ref(v_s_47_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedChars(lean_object* v_r_53_, lean_object* v_s_54_){
_start:
{
lean_object* v___f_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
lean_inc_ref(v_s_54_);
v___f_55_ = lean_alloc_closure((void*)(l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0___boxed), 4, 2);
lean_closure_set(v___f_55_, 0, v_s_54_);
lean_closure_set(v___f_55_, 1, v_r_53_);
v___x_56_ = lean_byte_array_size(v_s_54_);
lean_dec_ref(v_s_54_);
v___x_57_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(v___x_56_, v___f_55_, v___x_56_, lean_box(0));
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedChars___boxed(lean_object* v_r_58_, lean_object* v_s_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_58_, v_s_59_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(lean_object* v_s_62_, lean_object* v_r_63_, lean_object* v_i_64_, lean_object* v_h_65_){
_start:
{
uint8_t v___x_66_; uint8_t v___x_67_; 
v___x_66_ = lean_byte_array_fget(v_s_62_, v_i_64_);
v___x_67_ = l_Std_Http_URI_isEncodedQueryChar(v_r_63_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed(lean_object* v_s_68_, lean_object* v_r_69_, lean_object* v_i_70_, lean_object* v_h_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(v_s_68_, v_r_69_, v_i_70_, v_h_71_);
lean_dec(v_i_70_);
lean_dec_ref(v_s_68_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(lean_object* v_r_74_, lean_object* v_s_75_){
_start:
{
lean_object* v___f_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
lean_inc_ref(v_s_75_);
v___f_76_ = lean_alloc_closure((void*)(l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0___boxed), 4, 2);
lean_closure_set(v___f_76_, 0, v_s_75_);
lean_closure_set(v___f_76_, 1, v_r_74_);
v___x_77_ = lean_byte_array_size(v_s_75_);
lean_dec_ref(v_s_75_);
v___x_78_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(v___x_77_, v___f_76_, v___x_77_, lean_box(0));
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___boxed(lean_object* v_r_79_, lean_object* v_s_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_79_, v_s_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(lean_object* v_ba_83_, lean_object* v_i_84_){
_start:
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = lean_byte_array_size(v_ba_83_);
v___x_90_ = lean_nat_dec_lt(v_i_84_, v___x_89_);
if (v___x_90_ == 0)
{
uint8_t v___x_91_; 
lean_dec(v_i_84_);
v___x_91_ = 1;
return v___x_91_;
}
else
{
uint8_t v_c_92_; uint8_t v___x_93_; uint8_t v___x_94_; 
v_c_92_ = lean_byte_array_fget(v_ba_83_, v_i_84_);
v___x_93_ = 37;
v___x_94_ = lean_uint8_dec_eq(v_c_92_, v___x_93_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(1u);
v___x_96_ = lean_nat_add(v_i_84_, v___x_95_);
lean_dec(v_i_84_);
v_i_84_ = v___x_96_;
goto _start;
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_98_ = lean_unsigned_to_nat(2u);
v___x_99_ = lean_nat_add(v_i_84_, v___x_98_);
v___x_100_ = lean_nat_dec_lt(v___x_99_, v___x_89_);
if (v___x_100_ == 0)
{
lean_dec(v___x_99_);
lean_dec(v_i_84_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v_d1_103_; uint8_t v_d2_104_; uint8_t v___x_130_; uint8_t v___x_131_; 
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_add(v_i_84_, v___x_101_);
v_d1_103_ = lean_byte_array_fget(v_ba_83_, v___x_102_);
lean_dec(v___x_102_);
v_d2_104_ = lean_byte_array_fget(v_ba_83_, v___x_99_);
lean_dec(v___x_99_);
v___x_130_ = 48;
v___x_131_ = lean_uint8_dec_le(v___x_130_, v_d1_103_);
if (v___x_131_ == 0)
{
goto v___jp_125_;
}
else
{
uint8_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = 57;
v___x_133_ = lean_uint8_dec_le(v_d1_103_, v___x_132_);
if (v___x_133_ == 0)
{
goto v___jp_125_;
}
else
{
goto v___jp_115_;
}
}
v___jp_105_:
{
uint8_t v___x_106_; uint8_t v___x_107_; 
v___x_106_ = 65;
v___x_107_ = lean_uint8_dec_le(v___x_106_, v_d2_104_);
if (v___x_107_ == 0)
{
lean_dec(v_i_84_);
return v___x_107_;
}
else
{
uint8_t v___x_108_; uint8_t v___x_109_; 
v___x_108_ = 70;
v___x_109_ = lean_uint8_dec_le(v_d2_104_, v___x_108_);
if (v___x_109_ == 0)
{
lean_dec(v_i_84_);
return v___x_109_;
}
else
{
goto v___jp_85_;
}
}
}
v___jp_110_:
{
uint8_t v___x_111_; uint8_t v___x_112_; 
v___x_111_ = 97;
v___x_112_ = lean_uint8_dec_le(v___x_111_, v_d2_104_);
if (v___x_112_ == 0)
{
goto v___jp_105_;
}
else
{
uint8_t v___x_113_; uint8_t v___x_114_; 
v___x_113_ = 102;
v___x_114_ = lean_uint8_dec_le(v_d2_104_, v___x_113_);
if (v___x_114_ == 0)
{
goto v___jp_105_;
}
else
{
goto v___jp_85_;
}
}
}
v___jp_115_:
{
uint8_t v___x_116_; uint8_t v___x_117_; 
v___x_116_ = 48;
v___x_117_ = lean_uint8_dec_le(v___x_116_, v_d2_104_);
if (v___x_117_ == 0)
{
goto v___jp_110_;
}
else
{
uint8_t v___x_118_; uint8_t v___x_119_; 
v___x_118_ = 57;
v___x_119_ = lean_uint8_dec_le(v_d2_104_, v___x_118_);
if (v___x_119_ == 0)
{
goto v___jp_110_;
}
else
{
goto v___jp_85_;
}
}
}
v___jp_120_:
{
uint8_t v___x_121_; uint8_t v___x_122_; 
v___x_121_ = 65;
v___x_122_ = lean_uint8_dec_le(v___x_121_, v_d1_103_);
if (v___x_122_ == 0)
{
lean_dec(v_i_84_);
return v___x_122_;
}
else
{
uint8_t v___x_123_; uint8_t v___x_124_; 
v___x_123_ = 70;
v___x_124_ = lean_uint8_dec_le(v_d1_103_, v___x_123_);
if (v___x_124_ == 0)
{
lean_dec(v_i_84_);
return v___x_124_;
}
else
{
goto v___jp_115_;
}
}
}
v___jp_125_:
{
uint8_t v___x_126_; uint8_t v___x_127_; 
v___x_126_ = 97;
v___x_127_ = lean_uint8_dec_le(v___x_126_, v_d1_103_);
if (v___x_127_ == 0)
{
goto v___jp_120_;
}
else
{
uint8_t v___x_128_; uint8_t v___x_129_; 
v___x_128_ = 102;
v___x_129_ = lean_uint8_dec_le(v_d1_103_, v___x_128_);
if (v___x_129_ == 0)
{
goto v___jp_120_;
}
else
{
goto v___jp_115_;
}
}
}
}
}
}
v___jp_85_:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(3u);
v___x_87_ = lean_nat_add(v_i_84_, v___x_86_);
lean_dec(v_i_84_);
v_i_84_ = v___x_87_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop___boxed(lean_object* v_ba_134_, lean_object* v_i_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_134_, v_i_135_);
lean_dec_ref(v_ba_134_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidPercentEncoding(lean_object* v_ba_138_){
_start:
{
lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_isValidPercentEncoding_loop(v_ba_138_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidPercentEncoding___boxed(lean_object* v_ba_141_){
_start:
{
uint8_t v_res_142_; lean_object* v_r_143_; 
v_res_142_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_141_);
lean_dec_ref(v_ba_141_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_hexDigit(uint8_t v_n_144_){
_start:
{
uint8_t v___x_145_; uint8_t v___x_146_; 
v___x_145_ = 10;
v___x_146_ = lean_uint8_dec_lt(v_n_144_, v___x_145_);
if (v___x_146_ == 0)
{
uint8_t v___x_147_; uint8_t v___x_148_; uint8_t v___x_149_; 
v___x_147_ = lean_uint8_sub(v_n_144_, v___x_145_);
v___x_148_ = 65;
v___x_149_ = lean_uint8_add(v___x_147_, v___x_148_);
return v___x_149_;
}
else
{
uint8_t v___x_150_; uint8_t v___x_151_; 
v___x_150_ = 48;
v___x_151_ = lean_uint8_add(v_n_144_, v___x_150_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigit___boxed(lean_object* v_n_152_){
_start:
{
uint8_t v_n_boxed_153_; uint8_t v_res_154_; lean_object* v_r_155_; 
v_n_boxed_153_ = lean_unbox(v_n_152_);
v_res_154_ = l_Std_Http_URI_hexDigit(v_n_boxed_153_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f(uint8_t v_c_156_){
_start:
{
uint8_t v___x_179_; uint8_t v___x_180_; 
v___x_179_ = 48;
v___x_180_ = lean_uint8_dec_le(v___x_179_, v_c_156_);
if (v___x_180_ == 0)
{
goto v___jp_169_;
}
else
{
uint8_t v___x_181_; uint8_t v___x_182_; 
v___x_181_ = 57;
v___x_182_ = lean_uint8_dec_le(v_c_156_, v___x_181_);
if (v___x_182_ == 0)
{
goto v___jp_169_;
}
else
{
uint8_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_uint8_sub(v_c_156_, v___x_179_);
v___x_184_ = lean_box(v___x_183_);
v___x_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
}
v___jp_157_:
{
uint8_t v___x_158_; uint8_t v___x_159_; 
v___x_158_ = 65;
v___x_159_ = lean_uint8_dec_le(v___x_158_, v_c_156_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
v___x_160_ = lean_box(0);
return v___x_160_;
}
else
{
uint8_t v___x_161_; uint8_t v___x_162_; 
v___x_161_ = 70;
v___x_162_ = lean_uint8_dec_le(v_c_156_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
v___x_163_ = lean_box(0);
return v___x_163_;
}
else
{
uint8_t v___x_164_; uint8_t v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_164_ = lean_uint8_sub(v_c_156_, v___x_158_);
v___x_165_ = 10;
v___x_166_ = lean_uint8_add(v___x_164_, v___x_165_);
v___x_167_ = lean_box(v___x_166_);
v___x_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
return v___x_168_;
}
}
}
v___jp_169_:
{
uint8_t v___x_170_; uint8_t v___x_171_; 
v___x_170_ = 97;
v___x_171_ = lean_uint8_dec_le(v___x_170_, v_c_156_);
if (v___x_171_ == 0)
{
goto v___jp_157_;
}
else
{
uint8_t v___x_172_; uint8_t v___x_173_; 
v___x_172_ = 102;
v___x_173_ = lean_uint8_dec_le(v_c_156_, v___x_172_);
if (v___x_173_ == 0)
{
goto v___jp_157_;
}
else
{
uint8_t v___x_174_; uint8_t v___x_175_; uint8_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_174_ = lean_uint8_sub(v_c_156_, v___x_170_);
v___x_175_ = 10;
v___x_176_ = lean_uint8_add(v___x_174_, v___x_175_);
v___x_177_ = lean_box(v___x_176_);
v___x_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_hexDigitToUInt8_x3f___boxed(lean_object* v_c_186_){
_start:
{
uint8_t v_c_boxed_187_; lean_object* v_res_188_; 
v_c_boxed_187_ = lean_unbox(v_c_186_);
v_res_188_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_c_boxed_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(lean_object* v_x_189_, uint8_t v_x_190_, lean_object* v_h__1_191_){
_start:
{
lean_object* v_data_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_data_192_ = lean_byte_array_data(v_x_189_);
v___x_193_ = lean_box(v_x_190_);
v___x_194_ = lean_apply_2(v_h__1_191_, v_data_192_, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg___boxed(lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_h__1_197_){
_start:
{
uint8_t v_x_17__boxed_198_; lean_object* v_res_199_; 
v_x_17__boxed_198_ = lean_unbox(v_x_196_);
v_res_199_ = l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(v_x_195_, v_x_17__boxed_198_, v_h__1_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(lean_object* v_motive_200_, lean_object* v_x_201_, uint8_t v_x_202_, lean_object* v_h__1_203_){
_start:
{
lean_object* v_data_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_data_204_ = lean_byte_array_data(v_x_201_);
v___x_205_ = lean_box(v_x_202_);
v___x_206_ = lean_apply_2(v_h__1_203_, v_data_204_, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___boxed(lean_object* v_motive_207_, lean_object* v_x_208_, lean_object* v_x_209_, lean_object* v_h__1_210_){
_start:
{
uint8_t v_x_29__boxed_211_; lean_object* v_res_212_; 
v_x_29__boxed_211_ = lean_unbox(v_x_209_);
v_res_212_ = l___private_Std_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(v_motive_207_, v_x_208_, v_x_29__boxed_211_, v_h__1_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter___redArg(lean_object* v_x_213_, lean_object* v_x_214_, lean_object* v_h__1_215_, lean_object* v_h__2_216_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
lean_object* v___x_217_; 
lean_dec(v_h__2_216_);
v___x_217_ = lean_apply_1(v_h__1_215_, v_x_214_);
return v___x_217_;
}
else
{
lean_object* v_head_218_; lean_object* v_tail_219_; lean_object* v___x_220_; 
lean_dec(v_h__1_215_);
v_head_218_ = lean_ctor_get(v_x_213_, 0);
lean_inc(v_head_218_);
v_tail_219_ = lean_ctor_get(v_x_213_, 1);
lean_inc(v_tail_219_);
lean_dec_ref_known(v_x_213_, 2);
v___x_220_ = lean_apply_3(v_h__2_216_, v_head_218_, v_tail_219_, v_x_214_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter(lean_object* v_motive_221_, lean_object* v_x_222_, lean_object* v_x_223_, lean_object* v_h__1_224_, lean_object* v_h__2_225_){
_start:
{
if (lean_obj_tag(v_x_222_) == 0)
{
lean_object* v___x_226_; 
lean_dec(v_h__2_225_);
v___x_226_ = lean_apply_1(v_h__1_224_, v_x_223_);
return v___x_226_;
}
else
{
lean_object* v_head_227_; lean_object* v_tail_228_; lean_object* v___x_229_; 
lean_dec(v_h__1_224_);
v_head_227_ = lean_ctor_get(v_x_222_, 0);
lean_inc(v_head_227_);
v_tail_228_ = lean_ctor_get(v_x_222_, 1);
lean_inc(v_tail_228_);
lean_dec_ref_known(v_x_222_, 2);
v___x_229_ = lean_apply_3(v_h__2_225_, v_head_227_, v_tail_228_, v_x_223_);
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___redArg(){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_ByteArray_empty;
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___redArg___boxed(lean_object* v___dummy_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Std_Http_URI_EncodedString_empty___redArg();
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty(lean_object* v_r_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_ByteArray_empty;
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___boxed(lean_object* v_r_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Std_Http_URI_EncodedString_empty(v_r_236_);
lean_dec_ref(v_r_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___redArg(){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_ByteArray_empty;
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___redArg___boxed(lean_object* v___dummy_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Std_Http_URI_EncodedString_instInhabited___redArg();
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited(lean_object* v_r_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_ByteArray_empty;
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___boxed(lean_object* v_r_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Http_URI_EncodedString_instInhabited(v_r_244_);
lean_dec_ref(v_r_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(lean_object* v_s_246_, uint8_t v_c_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lean_byte_array_push(v_s_246_, v_c_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg___boxed(lean_object* v_s_249_, lean_object* v_c_250_){
_start:
{
uint8_t v_c_boxed_251_; lean_object* v_res_252_; 
v_c_boxed_251_ = lean_unbox(v_c_250_);
v_res_252_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(v_s_249_, v_c_boxed_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(lean_object* v_r_253_, lean_object* v_s_254_, uint8_t v_c_255_, lean_object* v_h_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_byte_array_push(v_s_254_, v_c_255_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___boxed(lean_object* v_r_258_, lean_object* v_s_259_, lean_object* v_c_260_, lean_object* v_h_261_){
_start:
{
uint8_t v_c_boxed_262_; lean_object* v_res_263_; 
v_c_boxed_262_ = lean_unbox(v_c_260_);
v_res_263_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(v_r_258_, v_s_259_, v_c_boxed_262_, v_h_261_);
lean_dec_ref(v_r_258_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(uint8_t v_b_264_, lean_object* v_s_265_){
_start:
{
uint8_t v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; uint8_t v___x_269_; uint8_t v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; uint8_t v___x_273_; uint8_t v___x_274_; lean_object* v_ba_275_; 
v___x_266_ = 37;
v___x_267_ = lean_byte_array_push(v_s_265_, v___x_266_);
v___x_268_ = 4;
v___x_269_ = lean_uint8_shift_right(v_b_264_, v___x_268_);
v___x_270_ = l_Std_Http_URI_hexDigit(v___x_269_);
v___x_271_ = lean_byte_array_push(v___x_267_, v___x_270_);
v___x_272_ = 15;
v___x_273_ = lean_uint8_land(v_b_264_, v___x_272_);
v___x_274_ = l_Std_Http_URI_hexDigit(v___x_273_);
v_ba_275_ = lean_byte_array_push(v___x_271_, v___x_274_);
return v_ba_275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg___boxed(lean_object* v_b_276_, lean_object* v_s_277_){
_start:
{
uint8_t v_b_boxed_278_; lean_object* v_res_279_; 
v_b_boxed_278_ = lean_unbox(v_b_276_);
v_res_279_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_boxed_278_, v_s_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(lean_object* v_r_280_, uint8_t v_b_281_, lean_object* v_s_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_281_, v_s_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___boxed(lean_object* v_r_284_, lean_object* v_b_285_, lean_object* v_s_286_){
_start:
{
uint8_t v_b_boxed_287_; lean_object* v_res_288_; 
v_b_boxed_287_ = lean_unbox(v_b_285_);
v_res_288_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(v_r_284_, v_b_boxed_287_, v_s_286_);
lean_dec_ref(v_r_284_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(lean_object* v_r_289_, lean_object* v_as_290_, size_t v_i_291_, size_t v_stop_292_, lean_object* v_b_293_){
_start:
{
lean_object* v___y_295_; uint8_t v___x_299_; 
v___x_299_ = lean_usize_dec_eq(v_i_291_, v_stop_292_);
if (v___x_299_ == 0)
{
uint8_t v___x_300_; uint8_t v___x_301_; uint8_t v___x_302_; 
v___x_300_ = lean_byte_array_uget(v_as_290_, v_i_291_);
v___x_301_ = 128;
v___x_302_ = lean_uint8_dec_lt(v___x_300_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; 
v___x_303_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_300_, v_b_293_);
v___y_295_ = v___x_303_;
goto v___jp_294_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = lean_box(v___x_300_);
lean_inc_ref(v_r_289_);
v___x_305_ = lean_apply_1(v_r_289_, v___x_304_);
v___x_306_ = lean_unbox(v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; 
v___x_307_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_300_, v_b_293_);
v___y_295_ = v___x_307_;
goto v___jp_294_;
}
else
{
lean_object* v___x_308_; 
v___x_308_ = lean_byte_array_push(v_b_293_, v___x_300_);
v___y_295_ = v___x_308_;
goto v___jp_294_;
}
}
}
else
{
lean_dec_ref(v_r_289_);
return v_b_293_;
}
v___jp_294_:
{
size_t v___x_296_; size_t v___x_297_; 
v___x_296_ = ((size_t)1ULL);
v___x_297_ = lean_usize_add(v_i_291_, v___x_296_);
v_i_291_ = v___x_297_;
v_b_293_ = v___y_295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0___boxed(lean_object* v_r_309_, lean_object* v_as_310_, lean_object* v_i_311_, lean_object* v_stop_312_, lean_object* v_b_313_){
_start:
{
size_t v_i_boxed_314_; size_t v_stop_boxed_315_; lean_object* v_res_316_; 
v_i_boxed_314_ = lean_unbox_usize(v_i_311_);
lean_dec(v_i_311_);
v_stop_boxed_315_ = lean_unbox_usize(v_stop_312_);
lean_dec(v_stop_312_);
v_res_316_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_309_, v_as_310_, v_i_boxed_314_, v_stop_boxed_315_, v_b_313_);
lean_dec_ref(v_as_310_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode(lean_object* v_r_317_, lean_object* v_s_318_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_319_ = l_ByteArray_empty;
v___x_320_ = lean_string_to_utf8(v_s_318_);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_byte_array_size(v___x_320_);
v___x_323_ = lean_nat_dec_lt(v___x_321_, v___x_322_);
if (v___x_323_ == 0)
{
lean_dec_ref(v___x_320_);
lean_dec_ref(v_r_317_);
return v___x_319_;
}
else
{
size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; 
v___x_324_ = ((size_t)0ULL);
v___x_325_ = lean_usize_of_nat(v___x_322_);
v___x_326_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_317_, v___x_320_, v___x_324_, v___x_325_, v___x_319_);
lean_dec_ref(v___x_320_);
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encodeEscaping_spec__0(lean_object* v_r_327_, lean_object* v_escape_328_, lean_object* v_as_329_, size_t v_i_330_, size_t v_stop_331_, lean_object* v_b_332_){
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
lean_inc_ref(v_r_327_);
v___x_344_ = lean_apply_1(v_r_327_, v___x_343_);
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
lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_347_ = lean_box(v___x_339_);
lean_inc_ref(v_escape_328_);
v___x_348_ = lean_apply_1(v_escape_328_, v___x_347_);
v___x_349_ = lean_unbox(v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
v___x_350_ = lean_byte_array_push(v_b_332_, v___x_339_);
v___y_334_ = v___x_350_;
goto v___jp_333_;
}
else
{
lean_object* v___x_351_; 
v___x_351_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_339_, v_b_332_);
v___y_334_ = v___x_351_;
goto v___jp_333_;
}
}
}
}
else
{
lean_dec_ref(v_escape_328_);
lean_dec_ref(v_r_327_);
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
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encodeEscaping_spec__0___boxed(lean_object* v_r_352_, lean_object* v_escape_353_, lean_object* v_as_354_, lean_object* v_i_355_, lean_object* v_stop_356_, lean_object* v_b_357_){
_start:
{
size_t v_i_boxed_358_; size_t v_stop_boxed_359_; lean_object* v_res_360_; 
v_i_boxed_358_ = lean_unbox_usize(v_i_355_);
lean_dec(v_i_355_);
v_stop_boxed_359_ = lean_unbox_usize(v_stop_356_);
lean_dec(v_stop_356_);
v_res_360_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encodeEscaping_spec__0(v_r_352_, v_escape_353_, v_as_354_, v_i_boxed_358_, v_stop_boxed_359_, v_b_357_);
lean_dec_ref(v_as_354_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encodeEscaping(lean_object* v_r_361_, lean_object* v_s_362_, lean_object* v_escape_363_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_364_ = l_ByteArray_empty;
v___x_365_ = lean_string_to_utf8(v_s_362_);
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_byte_array_size(v___x_365_);
v___x_368_ = lean_nat_dec_lt(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_dec_ref(v___x_365_);
lean_dec_ref(v_escape_363_);
lean_dec_ref(v_r_361_);
return v___x_364_;
}
else
{
size_t v___x_369_; size_t v___x_370_; lean_object* v___x_371_; 
v___x_369_ = ((size_t)0ULL);
v___x_370_ = lean_usize_of_nat(v___x_367_);
v___x_371_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encodeEscaping_spec__0(v_r_361_, v_escape_363_, v___x_365_, v___x_369_, v___x_370_, v___x_364_);
lean_dec_ref(v___x_365_);
return v___x_371_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedString_ofByteArray_x3f_spec__0___redArg(lean_object* v_ba_372_, lean_object* v_r_373_, lean_object* v_n_374_, lean_object* v_i_375_){
_start:
{
lean_object* v_zero_376_; uint8_t v_isZero_377_; 
v_zero_376_ = lean_unsigned_to_nat(0u);
v_isZero_377_ = lean_nat_dec_eq(v_i_375_, v_zero_376_);
if (v_isZero_377_ == 1)
{
lean_dec(v_i_375_);
lean_dec_ref(v_r_373_);
return v_isZero_377_;
}
else
{
lean_object* v_one_378_; lean_object* v_n_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; uint8_t v___x_383_; 
v_one_378_ = lean_unsigned_to_nat(1u);
v_n_379_ = lean_nat_sub(v_i_375_, v_one_378_);
lean_dec(v_i_375_);
v___x_380_ = lean_nat_add(v_n_379_, v_one_378_);
v___x_381_ = lean_nat_sub(v_n_374_, v___x_380_);
lean_dec(v___x_380_);
v___x_382_ = lean_byte_array_fget(v_ba_372_, v___x_381_);
lean_dec(v___x_381_);
lean_inc_ref(v_r_373_);
v___x_383_ = l_Std_Http_URI_isEncodedChar(v_r_373_, v___x_382_);
if (v___x_383_ == 0)
{
lean_dec(v_n_379_);
lean_dec_ref(v_r_373_);
return v___x_383_;
}
else
{
v_i_375_ = v_n_379_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedString_ofByteArray_x3f_spec__0___redArg___boxed(lean_object* v_ba_385_, lean_object* v_r_386_, lean_object* v_n_387_, lean_object* v_i_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedString_ofByteArray_x3f_spec__0___redArg(v_ba_385_, v_r_386_, v_n_387_, v_i_388_);
lean_dec(v_n_387_);
lean_dec_ref(v_ba_385_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x3f(lean_object* v_r_391_, lean_object* v_ba_392_){
_start:
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = lean_byte_array_size(v_ba_392_);
v___x_394_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedString_ofByteArray_x3f_spec__0___redArg(v_ba_392_, v_r_391_, v___x_393_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
lean_dec_ref(v_ba_392_);
v___x_395_ = lean_box(0);
return v___x_395_;
}
else
{
uint8_t v___x_396_; 
v___x_396_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_392_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; 
lean_dec_ref(v_ba_392_);
v___x_397_ = lean_box(0);
return v___x_397_;
}
else
{
lean_object* v___x_398_; 
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v_ba_392_);
return v___x_398_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedString_ofByteArray_x3f_spec__0(lean_object* v_ba_399_, lean_object* v_r_400_, lean_object* v_n_401_, lean_object* v_i_402_, lean_object* v_a_403_){
_start:
{
uint8_t v___x_404_; 
v___x_404_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedString_ofByteArray_x3f_spec__0___redArg(v_ba_399_, v_r_400_, v_n_401_, v_i_402_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedString_ofByteArray_x3f_spec__0___boxed(lean_object* v_ba_405_, lean_object* v_r_406_, lean_object* v_n_407_, lean_object* v_i_408_, lean_object* v_a_409_){
_start:
{
uint8_t v_res_410_; lean_object* v_r_411_; 
v_res_410_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedString_ofByteArray_x3f_spec__0(v_ba_405_, v_r_406_, v_n_407_, v_i_408_, v_a_409_);
lean_dec(v_n_407_);
lean_dec_ref(v_ba_405_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_412_){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = l_ByteArray_empty;
v___x_414_ = lean_panic_fn_borrowed(v___x_413_, v_msg_412_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(lean_object* v_r_415_, lean_object* v_msg_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v_msg_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_418_, lean_object* v_msg_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(v_r_418_, v_msg_419_);
lean_dec_ref(v_r_418_);
return v_res_420_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_424_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2));
v___x_425_ = lean_unsigned_to_nat(12u);
v___x_426_ = lean_unsigned_to_nat(342u);
v___x_427_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1));
v___x_428_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_429_ = l_mkPanicMessageWithDecl(v___x_428_, v___x_427_, v___x_426_, v___x_425_, v___x_424_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x21(lean_object* v_r_430_, lean_object* v_ba_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_430_, v_ba_431_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_obj_once(&l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3, &l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3_once, _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3);
v___x_434_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v___x_433_);
return v___x_434_;
}
else
{
lean_object* v_val_435_; 
v_val_435_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_val_435_);
lean_dec_ref_known(v___x_432_, 1);
return v_val_435_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f(lean_object* v_r_436_, lean_object* v_s_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_string_to_utf8(v_s_437_);
v___x_439_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_436_, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21(lean_object* v_r_440_, lean_object* v_s_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_string_to_utf8(v_s_441_);
v___x_443_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v_r_440_, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg(lean_object* v_ba_444_){
_start:
{
lean_inc_ref(v_ba_444_);
return v_ba_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg___boxed(lean_object* v_ba_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_Http_URI_EncodedString_new___redArg(v_ba_445_);
lean_dec_ref(v_ba_445_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new(lean_object* v_r_447_, lean_object* v_ba_448_, lean_object* v_valid_449_, lean_object* v___validEncoding_450_){
_start:
{
lean_inc_ref(v_ba_448_);
return v_ba_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___boxed(lean_object* v_r_451_, lean_object* v_ba_452_, lean_object* v_valid_453_, lean_object* v___validEncoding_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Std_Http_URI_EncodedString_new(v_r_451_, v_ba_452_, v_valid_453_, v___validEncoding_454_);
lean_dec_ref(v_ba_452_);
lean_dec_ref(v_r_451_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg___lam__0(lean_object* v_es_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lean_string_from_utf8_unchecked(v_es_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg(){
_start:
{
lean_object* v___f_460_; 
v___f_460_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instToString___redArg___closed__0));
return v___f_460_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg___boxed(lean_object* v___dummy_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_Http_URI_EncodedString_instToString___redArg();
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString(lean_object* v_r_463_){
_start:
{
lean_object* v___f_464_; 
v___f_464_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instToString___redArg___closed__0));
return v___f_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___boxed(lean_object* v_r_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_Http_URI_EncodedString_instToString(v_r_465_);
lean_dec_ref(v_r_465_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes_spec__0___redArg(lean_object* v_len_467_, lean_object* v_rawBytes_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_fst_470_; lean_object* v_snd_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_529_; 
v_fst_470_ = lean_ctor_get(v_a_469_, 0);
v_snd_471_ = lean_ctor_get(v_a_469_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v_a_469_);
if (v_isSharedCheck_529_ == 0)
{
v___x_473_ = v_a_469_;
v_isShared_474_ = v_isSharedCheck_529_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_snd_471_);
lean_inc(v_fst_470_);
lean_dec(v_a_469_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_529_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
uint8_t v___x_475_; 
v___x_475_ = lean_nat_dec_lt(v_snd_471_, v_len_467_);
if (v___x_475_ == 0)
{
lean_object* v___x_477_; 
if (v_isShared_474_ == 0)
{
v___x_477_ = v___x_473_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_fst_470_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_snd_471_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
else
{
uint8_t v_percent_479_; uint8_t v___x_480_; uint8_t v___x_489_; 
v_percent_479_ = 37;
v___x_480_ = lean_byte_array_fget(v_rawBytes_468_, v_snd_471_);
v___x_489_ = lean_uint8_dec_eq(v___x_480_, v_percent_479_);
if (v___x_489_ == 0)
{
goto v___jp_481_;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_add(v_snd_471_, v___x_490_);
v___x_492_ = lean_nat_dec_lt(v___x_491_, v_len_467_);
if (v___x_492_ == 0)
{
lean_dec(v___x_491_);
goto v___jp_481_;
}
else
{
uint8_t v___x_493_; lean_object* v___x_494_; 
lean_del_object(v___x_473_);
v___x_493_ = lean_byte_array_fget(v_rawBytes_468_, v___x_491_);
lean_dec(v___x_491_);
v___x_494_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_493_);
if (lean_obj_tag(v___x_494_) == 1)
{
lean_object* v_val_495_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v_val_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v___x_494_, 1);
v___x_496_ = lean_unsigned_to_nat(2u);
v___x_497_ = lean_nat_add(v_snd_471_, v___x_496_);
v___x_498_ = lean_nat_dec_lt(v___x_497_, v_len_467_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec(v_val_495_);
lean_dec(v_snd_471_);
v___x_499_ = lean_byte_array_push(v_fst_470_, v___x_480_);
v___x_500_ = lean_byte_array_push(v___x_499_, v___x_493_);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v___x_497_);
v_a_469_ = v___x_501_;
goto _start;
}
else
{
uint8_t v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_byte_array_fget(v_rawBytes_468_, v___x_497_);
lean_dec(v___x_497_);
v___x_504_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_503_);
if (lean_obj_tag(v___x_504_) == 1)
{
lean_object* v_val_505_; uint8_t v___x_506_; uint8_t v___x_507_; uint8_t v___x_508_; uint8_t v___x_509_; uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_val_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v___x_504_, 1);
v___x_506_ = 4;
v___x_507_ = lean_unbox(v_val_495_);
lean_dec(v_val_495_);
v___x_508_ = lean_uint8_shift_left(v___x_507_, v___x_506_);
v___x_509_ = lean_unbox(v_val_505_);
lean_dec(v_val_505_);
v___x_510_ = lean_uint8_add(v___x_508_, v___x_509_);
v___x_511_ = lean_byte_array_push(v_fst_470_, v___x_510_);
v___x_512_ = lean_unsigned_to_nat(3u);
v___x_513_ = lean_nat_add(v_snd_471_, v___x_512_);
lean_dec(v_snd_471_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_511_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v_a_469_ = v___x_514_;
goto _start;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v___x_504_);
lean_dec(v_val_495_);
v___x_516_ = lean_byte_array_push(v_fst_470_, v___x_480_);
v___x_517_ = lean_byte_array_push(v___x_516_, v___x_493_);
v___x_518_ = lean_byte_array_push(v___x_517_, v___x_503_);
v___x_519_ = lean_unsigned_to_nat(3u);
v___x_520_ = lean_nat_add(v_snd_471_, v___x_519_);
lean_dec(v_snd_471_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_518_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v_a_469_ = v___x_521_;
goto _start;
}
}
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v___x_494_);
v___x_523_ = lean_byte_array_push(v_fst_470_, v___x_480_);
v___x_524_ = lean_byte_array_push(v___x_523_, v___x_493_);
v___x_525_ = lean_unsigned_to_nat(2u);
v___x_526_ = lean_nat_add(v_snd_471_, v___x_525_);
lean_dec(v_snd_471_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_524_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v_a_469_ = v___x_527_;
goto _start;
}
}
}
v___jp_481_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_482_ = lean_byte_array_push(v_fst_470_, v___x_480_);
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_nat_add(v_snd_471_, v___x_483_);
lean_dec(v_snd_471_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v___x_484_);
lean_ctor_set(v___x_473_, 0, v___x_482_);
v___x_486_ = v___x_473_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_488_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
v_a_469_ = v___x_486_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes_spec__0___redArg___boxed(lean_object* v_len_530_, lean_object* v_rawBytes_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes_spec__0___redArg(v_len_530_, v_rawBytes_531_, v_a_532_);
lean_dec_ref(v_rawBytes_531_);
lean_dec(v_len_530_);
return v_res_533_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg___closed__0(void){
_start:
{
lean_object* v_i_534_; lean_object* v_decoded_535_; lean_object* v___x_536_; 
v_i_534_ = lean_unsigned_to_nat(0u);
v_decoded_535_ = l_ByteArray_empty;
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v_decoded_535_);
lean_ctor_set(v___x_536_, 1, v_i_534_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg(lean_object* v_es_537_){
_start:
{
lean_object* v_len_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v_fst_541_; 
v_len_538_ = lean_byte_array_size(v_es_537_);
v___x_539_ = lean_obj_once(&l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg___closed__0, &l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg___closed__0_once, _init_l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg___closed__0);
v___x_540_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes_spec__0___redArg(v_len_538_, v_es_537_, v___x_539_);
v_fst_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_fst_541_);
lean_dec_ref(v___x_540_);
return v_fst_541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg___boxed(lean_object* v_es_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg(v_es_542_);
lean_dec_ref(v_es_542_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes(lean_object* v_r_544_, lean_object* v_es_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg(v_es_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___boxed(lean_object* v_r_547_, lean_object* v_es_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes(v_r_547_, v_es_548_);
lean_dec_ref(v_es_548_);
lean_dec_ref(v_r_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes_spec__0(lean_object* v_len_550_, lean_object* v_rawBytes_551_, lean_object* v_inst_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes_spec__0___redArg(v_len_550_, v_rawBytes_551_, v_a_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes_spec__0___boxed(lean_object* v_len_555_, lean_object* v_rawBytes_556_, lean_object* v_inst_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes_spec__0(v_len_555_, v_rawBytes_556_, v_inst_557_, v_a_558_);
lean_dec_ref(v_rawBytes_556_);
lean_dec(v_len_555_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg(lean_object* v_es_560_){
_start:
{
lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg(v_es_560_);
v___x_562_ = lean_string_validate_utf8(v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; 
lean_dec(v___x_561_);
v___x_563_ = lean_box(0);
return v___x_563_;
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_string_from_utf8_unchecked(v___x_561_);
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg___boxed(lean_object* v_es_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_566_);
lean_dec_ref(v_es_566_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode(lean_object* v_r_568_, lean_object* v_es_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___boxed(lean_object* v_r_571_, lean_object* v_es_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_Http_URI_EncodedString_decode(v_r_571_, v_es_572_);
lean_dec_ref(v_es_572_);
lean_dec_ref(v_r_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decodeLossy___redArg(lean_object* v_es_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_576_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg(v_es_575_);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = ((lean_object*)(l_Std_Http_URI_EncodedString_decodeLossy___redArg___closed__0));
v___x_579_ = l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(v___x_576_, v___x_577_, v___x_578_);
lean_dec(v___x_576_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decodeLossy___redArg___boxed(lean_object* v_es_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_Http_URI_EncodedString_decodeLossy___redArg(v_es_580_);
lean_dec_ref(v_es_580_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decodeLossy(lean_object* v_r_582_, lean_object* v_es_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Std_Http_URI_EncodedString_decodeLossy___redArg(v_es_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decodeLossy___boxed(lean_object* v_r_585_, lean_object* v_es_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_Http_URI_EncodedString_decodeLossy(v_r_585_, v_es_586_);
lean_dec_ref(v_es_586_);
lean_dec_ref(v_r_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0(lean_object* v_es_588_, lean_object* v_n_589_){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_string_from_utf8_unchecked(v_es_588_);
v___x_591_ = l_String_quote(v___x_590_);
v___x_592_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0___boxed(lean_object* v_es_593_, lean_object* v_n_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0(v_es_593_, v_n_594_);
lean_dec(v_n_594_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg(){
_start:
{
lean_object* v___f_598_; 
v___f_598_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_598_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___boxed(lean_object* v___dummy_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_Http_URI_EncodedString_instRepr___redArg();
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr(lean_object* v_r_601_){
_start:
{
lean_object* v___f_602_; 
v___f_602_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_602_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___boxed(lean_object* v_r_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Std_Http_URI_EncodedString_instRepr(v_r_603_);
lean_dec_ref(v_r_603_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___redArg(){
_start:
{
lean_object* v___f_607_; 
v___f_607_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___redArg___boxed(lean_object* v___dummy_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_Http_URI_EncodedString_instBEq___redArg();
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq(lean_object* v_r_610_){
_start:
{
lean_object* v___f_611_; 
v___f_611_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___boxed(lean_object* v_r_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Std_Http_URI_EncodedString_instBEq(v_r_612_);
lean_dec_ref(v_r_612_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___redArg(){
_start:
{
lean_object* v___f_616_; 
v___f_616_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_616_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___redArg___boxed(lean_object* v___dummy_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Std_Http_URI_EncodedString_instHashable___redArg();
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable(lean_object* v_r_619_){
_start:
{
lean_object* v___f_620_; 
v___f_620_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___boxed(lean_object* v_r_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Std_Http_URI_EncodedString_instHashable(v_r_621_);
lean_dec_ref(v_r_621_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___redArg(){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_ByteArray_empty;
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___redArg___boxed(lean_object* v___dummy_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_Http_URI_EncodedQueryString_empty___redArg();
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty(lean_object* v_r_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_ByteArray_empty;
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___boxed(lean_object* v_r_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_Http_URI_EncodedQueryString_empty(v_r_629_);
lean_dec_ref(v_r_629_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___redArg(){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_ByteArray_empty;
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___redArg___boxed(lean_object* v___dummy_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_Http_URI_EncodedQueryString_instInhabited___redArg();
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited(lean_object* v_r_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_ByteArray_empty;
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___boxed(lean_object* v_r_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_Http_URI_EncodedQueryString_instInhabited(v_r_637_);
lean_dec_ref(v_r_637_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(lean_object* v_s_639_, uint8_t v_c_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = lean_byte_array_push(v_s_639_, v_c_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg___boxed(lean_object* v_s_642_, lean_object* v_c_643_){
_start:
{
uint8_t v_c_boxed_644_; lean_object* v_res_645_; 
v_c_boxed_644_ = lean_unbox(v_c_643_);
v_res_645_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(v_s_642_, v_c_boxed_644_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(lean_object* v_r_646_, lean_object* v_s_647_, uint8_t v_c_648_, lean_object* v_h_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = lean_byte_array_push(v_s_647_, v_c_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___boxed(lean_object* v_r_651_, lean_object* v_s_652_, lean_object* v_c_653_, lean_object* v_h_654_){
_start:
{
uint8_t v_c_boxed_655_; lean_object* v_res_656_; 
v_c_boxed_655_ = lean_unbox(v_c_653_);
v_res_656_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(v_r_651_, v_s_652_, v_c_boxed_655_, v_h_654_);
lean_dec_ref(v_r_651_);
return v_res_656_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x3f_spec__0___redArg(lean_object* v_ba_657_, lean_object* v_r_658_, lean_object* v_n_659_, lean_object* v_i_660_){
_start:
{
lean_object* v_zero_661_; uint8_t v_isZero_662_; 
v_zero_661_ = lean_unsigned_to_nat(0u);
v_isZero_662_ = lean_nat_dec_eq(v_i_660_, v_zero_661_);
if (v_isZero_662_ == 1)
{
lean_dec(v_i_660_);
lean_dec_ref(v_r_658_);
return v_isZero_662_;
}
else
{
lean_object* v_one_663_; lean_object* v_n_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; uint8_t v___x_668_; 
v_one_663_ = lean_unsigned_to_nat(1u);
v_n_664_ = lean_nat_sub(v_i_660_, v_one_663_);
lean_dec(v_i_660_);
v___x_665_ = lean_nat_add(v_n_664_, v_one_663_);
v___x_666_ = lean_nat_sub(v_n_659_, v___x_665_);
lean_dec(v___x_665_);
v___x_667_ = lean_byte_array_fget(v_ba_657_, v___x_666_);
lean_dec(v___x_666_);
lean_inc_ref(v_r_658_);
v___x_668_ = l_Std_Http_URI_isEncodedQueryChar(v_r_658_, v___x_667_);
if (v___x_668_ == 0)
{
lean_dec(v_n_664_);
lean_dec_ref(v_r_658_);
return v___x_668_;
}
else
{
v_i_660_ = v_n_664_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x3f_spec__0___redArg___boxed(lean_object* v_ba_670_, lean_object* v_r_671_, lean_object* v_n_672_, lean_object* v_i_673_){
_start:
{
uint8_t v_res_674_; lean_object* v_r_675_; 
v_res_674_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x3f_spec__0___redArg(v_ba_670_, v_r_671_, v_n_672_, v_i_673_);
lean_dec(v_n_672_);
lean_dec_ref(v_ba_670_);
v_r_675_ = lean_box(v_res_674_);
return v_r_675_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(lean_object* v_ba_676_, lean_object* v_r_677_){
_start:
{
lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_678_ = lean_byte_array_size(v_ba_676_);
v___x_679_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x3f_spec__0___redArg(v_ba_676_, v_r_677_, v___x_678_, v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
lean_dec_ref(v_ba_676_);
v___x_680_ = lean_box(0);
return v___x_680_;
}
else
{
uint8_t v___x_681_; 
v___x_681_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_676_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
lean_dec_ref(v_ba_676_);
v___x_682_ = lean_box(0);
return v___x_682_;
}
else
{
lean_object* v___x_683_; 
v___x_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_683_, 0, v_ba_676_);
return v___x_683_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x3f_spec__0(lean_object* v_ba_684_, lean_object* v_r_685_, lean_object* v_n_686_, lean_object* v_i_687_, lean_object* v_a_688_){
_start:
{
uint8_t v___x_689_; 
v___x_689_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x3f_spec__0___redArg(v_ba_684_, v_r_685_, v_n_686_, v_i_687_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x3f_spec__0___boxed(lean_object* v_ba_690_, lean_object* v_r_691_, lean_object* v_n_692_, lean_object* v_i_693_, lean_object* v_a_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x3f_spec__0(v_ba_690_, v_r_691_, v_n_692_, v_i_693_, v_a_694_);
lean_dec(v_n_692_);
lean_dec_ref(v_ba_690_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_697_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = l_ByteArray_empty;
v___x_699_ = lean_panic_fn_borrowed(v___x_698_, v_msg_697_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(lean_object* v_r_700_, lean_object* v_msg_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v_msg_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_703_, lean_object* v_msg_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(v_r_703_, v_msg_704_);
lean_dec_ref(v_r_703_);
return v_res_705_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_708_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1));
v___x_709_ = lean_unsigned_to_nat(12u);
v___x_710_ = lean_unsigned_to_nat(474u);
v___x_711_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0));
v___x_712_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_713_ = l_mkPanicMessageWithDecl(v___x_712_, v___x_711_, v___x_710_, v___x_709_, v___x_708_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(lean_object* v_ba_714_, lean_object* v_r_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_714_, v_r_715_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_obj_once(&l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2, &l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2_once, _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2);
v___x_718_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v___x_717_);
return v___x_718_;
}
else
{
lean_object* v_val_719_; 
v_val_719_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_val_719_);
lean_dec_ref_known(v___x_716_, 1);
return v_val_719_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f(lean_object* v_s_720_, lean_object* v_r_721_){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_string_to_utf8(v_s_720_);
v___x_723_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v___x_722_, v_r_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21(lean_object* v_s_724_, lean_object* v_r_725_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_string_to_utf8(v_s_724_);
v___x_727_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v___x_726_, v_r_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg(lean_object* v_ba_728_){
_start:
{
lean_inc_ref(v_ba_728_);
return v_ba_728_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg___boxed(lean_object* v_ba_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_Http_URI_EncodedQueryString_new___redArg(v_ba_729_);
lean_dec_ref(v_ba_729_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new(lean_object* v_r_731_, lean_object* v_ba_732_, lean_object* v_valid_733_, lean_object* v___validEncoding_734_){
_start:
{
lean_inc_ref(v_ba_732_);
return v_ba_732_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___boxed(lean_object* v_r_735_, lean_object* v_ba_736_, lean_object* v_valid_737_, lean_object* v___validEncoding_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_Http_URI_EncodedQueryString_new(v_r_735_, v_ba_736_, v_valid_737_, v___validEncoding_738_);
lean_dec_ref(v_ba_736_);
lean_dec_ref(v_r_735_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(uint8_t v_b_740_, lean_object* v_s_741_){
_start:
{
uint8_t v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; uint8_t v___x_745_; uint8_t v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; uint8_t v___x_749_; uint8_t v___x_750_; lean_object* v_ba_751_; 
v___x_742_ = 37;
v___x_743_ = lean_byte_array_push(v_s_741_, v___x_742_);
v___x_744_ = 4;
v___x_745_ = lean_uint8_shift_right(v_b_740_, v___x_744_);
v___x_746_ = l_Std_Http_URI_hexDigit(v___x_745_);
v___x_747_ = lean_byte_array_push(v___x_743_, v___x_746_);
v___x_748_ = 15;
v___x_749_ = lean_uint8_land(v_b_740_, v___x_748_);
v___x_750_ = l_Std_Http_URI_hexDigit(v___x_749_);
v_ba_751_ = lean_byte_array_push(v___x_747_, v___x_750_);
return v_ba_751_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg___boxed(lean_object* v_b_752_, lean_object* v_s_753_){
_start:
{
uint8_t v_b_boxed_754_; lean_object* v_res_755_; 
v_b_boxed_754_ = lean_unbox(v_b_752_);
v_res_755_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_boxed_754_, v_s_753_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(lean_object* v_r_756_, uint8_t v_b_757_, lean_object* v_s_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_757_, v_s_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___boxed(lean_object* v_r_760_, lean_object* v_b_761_, lean_object* v_s_762_){
_start:
{
uint8_t v_b_boxed_763_; lean_object* v_res_764_; 
v_b_boxed_763_ = lean_unbox(v_b_761_);
v_res_764_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(v_r_760_, v_b_boxed_763_, v_s_762_);
lean_dec_ref(v_r_760_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(lean_object* v_r_765_, lean_object* v_as_766_, size_t v_i_767_, size_t v_stop_768_, lean_object* v_b_769_){
_start:
{
lean_object* v___y_771_; uint8_t v___x_775_; 
v___x_775_ = lean_usize_dec_eq(v_i_767_, v_stop_768_);
if (v___x_775_ == 0)
{
uint8_t v___x_776_; uint8_t v___x_777_; uint8_t v___x_783_; 
v___x_776_ = lean_byte_array_uget(v_as_766_, v_i_767_);
v___x_777_ = 43;
v___x_783_ = lean_uint8_dec_eq(v___x_776_, v___x_777_);
if (v___x_783_ == 0)
{
uint8_t v___x_784_; uint8_t v___x_785_; 
v___x_784_ = 128;
v___x_785_ = lean_uint8_dec_lt(v___x_776_, v___x_784_);
if (v___x_785_ == 0)
{
goto v___jp_778_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_786_ = lean_box(v___x_776_);
lean_inc_ref(v_r_765_);
v___x_787_ = lean_apply_1(v_r_765_, v___x_786_);
v___x_788_ = lean_unbox(v___x_787_);
if (v___x_788_ == 0)
{
goto v___jp_778_;
}
else
{
lean_object* v___x_789_; 
v___x_789_ = lean_byte_array_push(v_b_769_, v___x_776_);
v___y_771_ = v___x_789_;
goto v___jp_770_;
}
}
}
else
{
lean_object* v___x_790_; 
v___x_790_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v___x_776_, v_b_769_);
v___y_771_ = v___x_790_;
goto v___jp_770_;
}
v___jp_778_:
{
uint8_t v___x_779_; uint8_t v___x_780_; 
v___x_779_ = 32;
v___x_780_ = lean_uint8_dec_eq(v___x_776_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
v___x_781_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v___x_776_, v_b_769_);
v___y_771_ = v___x_781_;
goto v___jp_770_;
}
else
{
lean_object* v___x_782_; 
v___x_782_ = lean_byte_array_push(v_b_769_, v___x_777_);
v___y_771_ = v___x_782_;
goto v___jp_770_;
}
}
}
else
{
lean_dec_ref(v_r_765_);
return v_b_769_;
}
v___jp_770_:
{
size_t v___x_772_; size_t v___x_773_; 
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_add(v_i_767_, v___x_772_);
v_i_767_ = v___x_773_;
v_b_769_ = v___y_771_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___boxed(lean_object* v_r_791_, lean_object* v_as_792_, lean_object* v_i_793_, lean_object* v_stop_794_, lean_object* v_b_795_){
_start:
{
size_t v_i_boxed_796_; size_t v_stop_boxed_797_; lean_object* v_res_798_; 
v_i_boxed_796_ = lean_unbox_usize(v_i_793_);
lean_dec(v_i_793_);
v_stop_boxed_797_ = lean_unbox_usize(v_stop_794_);
lean_dec(v_stop_794_);
v_res_798_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_791_, v_as_792_, v_i_boxed_796_, v_stop_boxed_797_, v_b_795_);
lean_dec_ref(v_as_792_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode(lean_object* v_s_799_, lean_object* v_r_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_801_ = l_ByteArray_empty;
v___x_802_ = lean_string_to_utf8(v_s_799_);
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = lean_byte_array_size(v___x_802_);
v___x_805_ = lean_nat_dec_lt(v___x_803_, v___x_804_);
if (v___x_805_ == 0)
{
lean_dec_ref(v___x_802_);
lean_dec_ref(v_r_800_);
return v___x_801_;
}
else
{
size_t v___x_806_; size_t v___x_807_; lean_object* v___x_808_; 
v___x_806_ = ((size_t)0ULL);
v___x_807_ = lean_usize_of_nat(v___x_804_);
v___x_808_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_800_, v___x_802_, v___x_806_, v___x_807_, v___x_801_);
lean_dec_ref(v___x_802_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___redArg(lean_object* v_es_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = lean_string_from_utf8_unchecked(v_es_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString(lean_object* v_r_811_, lean_object* v_es_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = lean_string_from_utf8_unchecked(v_es_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___boxed(lean_object* v_r_814_, lean_object* v_es_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_Http_URI_EncodedQueryString_toString(v_r_814_, v_es_815_);
lean_dec_ref(v_r_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(lean_object* v_len_817_, lean_object* v_rawBytes_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_fst_820_; lean_object* v_snd_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_887_; 
v_fst_820_ = lean_ctor_get(v_a_819_, 0);
v_snd_821_ = lean_ctor_get(v_a_819_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_a_819_);
if (v_isSharedCheck_887_ == 0)
{
v___x_823_ = v_a_819_;
v_isShared_824_ = v_isSharedCheck_887_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_snd_821_);
lean_inc(v_fst_820_);
lean_dec(v_a_819_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_887_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
uint8_t v___x_825_; 
v___x_825_ = lean_nat_dec_lt(v_snd_821_, v_len_817_);
if (v___x_825_ == 0)
{
lean_object* v___x_827_; 
if (v_isShared_824_ == 0)
{
v___x_827_ = v___x_823_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_fst_820_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_snd_821_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
else
{
uint8_t v_plus_829_; uint8_t v___x_830_; uint8_t v___x_839_; 
v_plus_829_ = 43;
v___x_830_ = lean_byte_array_fget(v_rawBytes_818_, v_snd_821_);
v___x_839_ = lean_uint8_dec_eq(v___x_830_, v_plus_829_);
if (v___x_839_ == 0)
{
uint8_t v_percent_840_; uint8_t v___x_841_; 
v_percent_840_ = 37;
v___x_841_ = lean_uint8_dec_eq(v___x_830_, v_percent_840_);
if (v___x_841_ == 0)
{
goto v___jp_831_;
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_842_ = lean_unsigned_to_nat(1u);
v___x_843_ = lean_nat_add(v_snd_821_, v___x_842_);
v___x_844_ = lean_nat_dec_lt(v___x_843_, v_len_817_);
if (v___x_844_ == 0)
{
lean_dec(v___x_843_);
goto v___jp_831_;
}
else
{
uint8_t v___x_845_; lean_object* v___x_846_; 
lean_del_object(v___x_823_);
v___x_845_ = lean_byte_array_fget(v_rawBytes_818_, v___x_843_);
lean_dec(v___x_843_);
v___x_846_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_845_);
if (lean_obj_tag(v___x_846_) == 1)
{
lean_object* v_val_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v_val_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_val_847_);
lean_dec_ref_known(v___x_846_, 1);
v___x_848_ = lean_unsigned_to_nat(2u);
v___x_849_ = lean_nat_add(v_snd_821_, v___x_848_);
v___x_850_ = lean_nat_dec_lt(v___x_849_, v_len_817_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec(v_val_847_);
lean_dec(v_snd_821_);
v___x_851_ = lean_byte_array_push(v_fst_820_, v___x_830_);
v___x_852_ = lean_byte_array_push(v___x_851_, v___x_845_);
v___x_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v___x_849_);
v_a_819_ = v___x_853_;
goto _start;
}
else
{
uint8_t v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_byte_array_fget(v_rawBytes_818_, v___x_849_);
lean_dec(v___x_849_);
v___x_856_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_855_);
if (lean_obj_tag(v___x_856_) == 1)
{
lean_object* v_val_857_; uint8_t v___x_858_; uint8_t v___x_859_; uint8_t v___x_860_; uint8_t v___x_861_; uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_val_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_val_857_);
lean_dec_ref_known(v___x_856_, 1);
v___x_858_ = 4;
v___x_859_ = lean_unbox(v_val_847_);
lean_dec(v_val_847_);
v___x_860_ = lean_uint8_shift_left(v___x_859_, v___x_858_);
v___x_861_ = lean_unbox(v_val_857_);
lean_dec(v_val_857_);
v___x_862_ = lean_uint8_add(v___x_860_, v___x_861_);
v___x_863_ = lean_byte_array_push(v_fst_820_, v___x_862_);
v___x_864_ = lean_unsigned_to_nat(3u);
v___x_865_ = lean_nat_add(v_snd_821_, v___x_864_);
lean_dec(v_snd_821_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_863_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v_a_819_ = v___x_866_;
goto _start;
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec(v___x_856_);
lean_dec(v_val_847_);
v___x_868_ = lean_byte_array_push(v_fst_820_, v___x_830_);
v___x_869_ = lean_byte_array_push(v___x_868_, v___x_845_);
v___x_870_ = lean_byte_array_push(v___x_869_, v___x_855_);
v___x_871_ = lean_unsigned_to_nat(3u);
v___x_872_ = lean_nat_add(v_snd_821_, v___x_871_);
lean_dec(v_snd_821_);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_870_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v_a_819_ = v___x_873_;
goto _start;
}
}
}
else
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
lean_dec(v___x_846_);
v___x_875_ = lean_byte_array_push(v_fst_820_, v___x_830_);
v___x_876_ = lean_byte_array_push(v___x_875_, v___x_845_);
v___x_877_ = lean_unsigned_to_nat(2u);
v___x_878_ = lean_nat_add(v_snd_821_, v___x_877_);
lean_dec(v_snd_821_);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_876_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v_a_819_ = v___x_879_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
lean_del_object(v___x_823_);
v___x_881_ = 32;
v___x_882_ = lean_byte_array_push(v_fst_820_, v___x_881_);
v___x_883_ = lean_unsigned_to_nat(1u);
v___x_884_ = lean_nat_add(v_snd_821_, v___x_883_);
lean_dec(v_snd_821_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_882_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v_a_819_ = v___x_885_;
goto _start;
}
v___jp_831_:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_832_ = lean_byte_array_push(v_fst_820_, v___x_830_);
v___x_833_ = lean_unsigned_to_nat(1u);
v___x_834_ = lean_nat_add(v_snd_821_, v___x_833_);
lean_dec(v_snd_821_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v___x_834_);
lean_ctor_set(v___x_823_, 0, v___x_832_);
v___x_836_ = v___x_823_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v___x_834_);
v___x_836_ = v_reuseFailAlloc_838_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
v_a_819_ = v___x_836_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg___boxed(lean_object* v_len_888_, lean_object* v_rawBytes_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_888_, v_rawBytes_889_, v_a_890_);
lean_dec_ref(v_rawBytes_889_);
lean_dec(v_len_888_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg(lean_object* v_es_892_){
_start:
{
lean_object* v_len_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v_fst_896_; uint8_t v___x_897_; 
v_len_893_ = lean_byte_array_size(v_es_892_);
v___x_894_ = lean_obj_once(&l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg___closed__0, &l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg___closed__0_once, _init_l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_decodeBytes___redArg___closed__0);
v___x_895_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_893_, v_es_892_, v___x_894_);
v_fst_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_fst_896_);
lean_dec_ref(v___x_895_);
v___x_897_ = lean_string_validate_utf8(v_fst_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
lean_dec(v_fst_896_);
v___x_898_ = lean_box(0);
return v___x_898_;
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_string_from_utf8_unchecked(v_fst_896_);
v___x_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg___boxed(lean_object* v_es_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_901_);
lean_dec_ref(v_es_901_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode(lean_object* v_r_903_, lean_object* v_es_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___boxed(lean_object* v_r_906_, lean_object* v_es_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_Http_URI_EncodedQueryString_decode(v_r_906_, v_es_907_);
lean_dec_ref(v_es_907_);
lean_dec_ref(v_r_906_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(lean_object* v_len_909_, lean_object* v_rawBytes_910_, lean_object* v_inst_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_909_, v_rawBytes_910_, v_a_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___boxed(lean_object* v_len_914_, lean_object* v_rawBytes_915_, lean_object* v_inst_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(v_len_914_, v_rawBytes_915_, v_inst_916_, v_a_917_);
lean_dec_ref(v_rawBytes_915_);
lean_dec(v_len_914_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___lam__0(lean_object* v_key_919_, lean_object* v_j_920_, uint8_t v_b_921_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_922_ = lean_string_utf8_byte_size(v_key_919_);
v___x_923_ = lean_unsigned_to_nat(1u);
v___x_924_ = lean_nat_add(v_j_920_, v___x_923_);
v___x_925_ = lean_nat_dec_le(v___x_924_, v___x_922_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; 
lean_dec(v___x_924_);
lean_dec(v_j_920_);
v___x_926_ = lean_box(0);
return v___x_926_;
}
else
{
uint8_t v___x_927_; uint8_t v___x_928_; 
v___x_927_ = lean_string_get_byte_fast(v_key_919_, v_j_920_);
v___x_928_ = lean_uint8_dec_eq(v___x_927_, v_b_921_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
lean_dec(v___x_924_);
v___x_929_ = lean_box(0);
return v___x_929_;
}
else
{
lean_object* v___x_930_; 
v___x_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_924_);
return v___x_930_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___lam__0___boxed(lean_object* v_key_931_, lean_object* v_j_932_, lean_object* v_b_933_){
_start:
{
uint8_t v_b_boxed_934_; lean_object* v_res_935_; 
v_b_boxed_934_ = lean_unbox(v_b_933_);
v_res_935_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___lam__0(v_key_931_, v_j_932_, v_b_boxed_934_);
lean_dec_ref(v_key_931_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg(lean_object* v_len_939_, lean_object* v_rawBytes_940_, lean_object* v_key_941_, lean_object* v_a_942_){
_start:
{
lean_object* v_snd_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_1025_; 
v_snd_943_ = lean_ctor_get(v_a_942_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_a_942_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v_a_942_, 0);
lean_dec(v_unused_1026_);
v___x_945_ = v_a_942_;
v_isShared_946_ = v_isSharedCheck_1025_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_snd_943_);
lean_dec(v_a_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_1025_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_fst_947_; lean_object* v_snd_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_1024_; 
v_fst_947_ = lean_ctor_get(v_snd_943_, 0);
v_snd_948_ = lean_ctor_get(v_snd_943_, 1);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_snd_943_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_950_ = v_snd_943_;
v_isShared_951_ = v_isSharedCheck_1024_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_snd_948_);
lean_inc(v_fst_947_);
lean_dec(v_snd_943_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_1024_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_960_; lean_object* v_fst_962_; lean_object* v_snd_963_; uint8_t v___x_967_; 
v___x_960_ = lean_box(0);
v___x_967_ = lean_nat_dec_lt(v_fst_947_, v_len_939_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; 
lean_del_object(v___x_950_);
lean_del_object(v___x_945_);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v_fst_947_);
lean_ctor_set(v___x_968_, 1, v_snd_948_);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_960_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
return v___x_969_;
}
else
{
uint8_t v_plus_970_; uint8_t v___x_971_; uint8_t v___x_977_; 
v_plus_970_ = 43;
v___x_971_ = lean_byte_array_fget(v_rawBytes_940_, v_fst_947_);
v___x_977_ = lean_uint8_dec_eq(v___x_971_, v_plus_970_);
if (v___x_977_ == 0)
{
uint8_t v_percent_978_; uint8_t v___x_979_; 
v_percent_978_ = 37;
v___x_979_ = lean_uint8_dec_eq(v___x_971_, v_percent_978_);
if (v___x_979_ == 0)
{
goto v___jp_972_;
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_980_ = lean_unsigned_to_nat(1u);
v___x_981_ = lean_nat_add(v_fst_947_, v___x_980_);
v___x_982_ = lean_nat_dec_lt(v___x_981_, v_len_939_);
if (v___x_982_ == 0)
{
lean_dec(v___x_981_);
goto v___jp_972_;
}
else
{
uint8_t v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_byte_array_fget(v_rawBytes_940_, v___x_981_);
lean_dec(v___x_981_);
v___x_984_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_983_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v___x_985_; 
lean_inc(v_snd_948_);
v___x_985_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___lam__0(v_key_941_, v_snd_948_, v___x_971_);
if (lean_obj_tag(v___x_985_) == 0)
{
goto v___jp_952_;
}
else
{
lean_object* v_val_986_; lean_object* v___x_987_; 
v_val_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_val_986_);
lean_dec_ref_known(v___x_985_, 1);
v___x_987_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___lam__0(v_key_941_, v_val_986_, v___x_983_);
if (lean_obj_tag(v___x_987_) == 0)
{
goto v___jp_952_;
}
else
{
lean_object* v_val_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
lean_del_object(v___x_950_);
lean_dec(v_snd_948_);
lean_del_object(v___x_945_);
v_val_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_val_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = lean_unsigned_to_nat(2u);
v___x_990_ = lean_nat_add(v_fst_947_, v___x_989_);
lean_dec(v_fst_947_);
v_fst_962_ = v_val_988_;
v_snd_963_ = v___x_990_;
goto v___jp_961_;
}
}
}
else
{
lean_object* v_val_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v_val_991_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v___x_984_, 1);
v___x_992_ = lean_unsigned_to_nat(2u);
v___x_993_ = lean_nat_add(v_fst_947_, v___x_992_);
v___x_994_ = lean_nat_dec_lt(v___x_993_, v_len_939_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; 
lean_dec(v_val_991_);
lean_inc(v_snd_948_);
v___x_995_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___lam__0(v_key_941_, v_snd_948_, v___x_971_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_dec(v___x_993_);
goto v___jp_952_;
}
else
{
lean_object* v_val_996_; lean_object* v___x_997_; 
v_val_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_val_996_);
lean_dec_ref_known(v___x_995_, 1);
v___x_997_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___lam__0(v_key_941_, v_val_996_, v___x_983_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_dec(v___x_993_);
goto v___jp_952_;
}
else
{
lean_object* v_val_998_; 
lean_del_object(v___x_950_);
lean_dec(v_snd_948_);
lean_dec(v_fst_947_);
lean_del_object(v___x_945_);
v_val_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v___x_997_, 1);
v_fst_962_ = v_val_998_;
v_snd_963_ = v___x_993_;
goto v___jp_961_;
}
}
}
else
{
uint8_t v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_byte_array_fget(v_rawBytes_940_, v___x_993_);
lean_dec(v___x_993_);
v___x_1000_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_999_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v___x_1001_; 
lean_dec(v_val_991_);
lean_inc(v_snd_948_);
v___x_1001_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___lam__0(v_key_941_, v_snd_948_, v___x_971_);
if (lean_obj_tag(v___x_1001_) == 0)
{
goto v___jp_952_;
}
else
{
lean_object* v_val_1002_; lean_object* v___x_1003_; 
v_val_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_val_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___lam__0(v_key_941_, v_val_1002_, v___x_983_);
if (lean_obj_tag(v___x_1003_) == 0)
{
goto v___jp_952_;
}
else
{
lean_object* v_val_1004_; lean_object* v___x_1005_; 
v_val_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_val_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___lam__0(v_key_941_, v_val_1004_, v___x_999_);
if (lean_obj_tag(v___x_1005_) == 0)
{
goto v___jp_952_;
}
else
{
lean_object* v_val_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_del_object(v___x_950_);
lean_dec(v_snd_948_);
lean_del_object(v___x_945_);
v_val_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_val_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = lean_unsigned_to_nat(3u);
v___x_1008_ = lean_nat_add(v_fst_947_, v___x_1007_);
lean_dec(v_fst_947_);
v_fst_962_ = v_val_1006_;
v_snd_963_ = v___x_1008_;
goto v___jp_961_;
}
}
}
}
else
{
lean_object* v_val_1009_; uint8_t v___x_1010_; uint8_t v___x_1011_; uint8_t v___x_1012_; uint8_t v___x_1013_; uint8_t v___x_1014_; lean_object* v___x_1015_; 
v_val_1009_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_val_1009_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1010_ = 4;
v___x_1011_ = lean_unbox(v_val_991_);
lean_dec(v_val_991_);
v___x_1012_ = lean_uint8_shift_left(v___x_1011_, v___x_1010_);
v___x_1013_ = lean_unbox(v_val_1009_);
lean_dec(v_val_1009_);
v___x_1014_ = lean_uint8_add(v___x_1012_, v___x_1013_);
lean_inc(v_snd_948_);
v___x_1015_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___lam__0(v_key_941_, v_snd_948_, v___x_1014_);
if (lean_obj_tag(v___x_1015_) == 0)
{
goto v___jp_952_;
}
else
{
lean_object* v_val_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_del_object(v___x_950_);
lean_dec(v_snd_948_);
lean_del_object(v___x_945_);
v_val_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_val_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = lean_unsigned_to_nat(3u);
v___x_1018_ = lean_nat_add(v_fst_947_, v___x_1017_);
lean_dec(v_fst_947_);
v_fst_962_ = v_val_1016_;
v_snd_963_ = v___x_1018_;
goto v___jp_961_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = 32;
lean_inc(v_snd_948_);
v___x_1020_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___lam__0(v_key_941_, v_snd_948_, v___x_1019_);
if (lean_obj_tag(v___x_1020_) == 0)
{
goto v___jp_952_;
}
else
{
lean_object* v_val_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_del_object(v___x_950_);
lean_dec(v_snd_948_);
lean_del_object(v___x_945_);
v_val_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_val_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = lean_unsigned_to_nat(1u);
v___x_1023_ = lean_nat_add(v_fst_947_, v___x_1022_);
lean_dec(v_fst_947_);
v_fst_962_ = v_val_1021_;
v_snd_963_ = v___x_1023_;
goto v___jp_961_;
}
}
v___jp_972_:
{
lean_object* v___x_973_; 
lean_inc(v_snd_948_);
v___x_973_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___lam__0(v_key_941_, v_snd_948_, v___x_971_);
if (lean_obj_tag(v___x_973_) == 0)
{
goto v___jp_952_;
}
else
{
lean_object* v_val_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
lean_del_object(v___x_950_);
lean_dec(v_snd_948_);
lean_del_object(v___x_945_);
v_val_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_val_974_);
lean_dec_ref_known(v___x_973_, 1);
v___x_975_ = lean_unsigned_to_nat(1u);
v___x_976_ = lean_nat_add(v_fst_947_, v___x_975_);
lean_dec(v_fst_947_);
v_fst_962_ = v_val_974_;
v_snd_963_ = v___x_976_;
goto v___jp_961_;
}
}
}
v___jp_952_:
{
lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_953_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___closed__0));
if (v_isShared_951_ == 0)
{
v___x_955_ = v___x_950_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_fst_947_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_snd_948_);
v___x_955_ = v_reuseFailAlloc_959_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_957_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v___x_955_);
lean_ctor_set(v___x_945_, 0, v___x_953_);
v___x_957_ = v___x_945_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
v___jp_961_:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v_snd_963_);
lean_ctor_set(v___x_964_, 1, v_fst_962_);
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_960_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v_a_942_ = v___x_965_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg___boxed(lean_object* v_len_1027_, lean_object* v_rawBytes_1028_, lean_object* v_key_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg(v_len_1027_, v_rawBytes_1028_, v_key_1029_, v_a_1030_);
lean_dec_ref(v_key_1029_);
lean_dec_ref(v_rawBytes_1028_);
lean_dec(v_len_1027_);
return v_res_1031_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryString_decodesTo___redArg(lean_object* v_es_1037_, lean_object* v_key_1038_){
_start:
{
lean_object* v_len_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v_fst_1042_; 
v_len_1039_ = lean_byte_array_size(v_es_1037_);
v___x_1040_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_decodesTo___redArg___closed__1));
v___x_1041_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg(v_len_1039_, v_es_1037_, v_key_1038_, v___x_1040_);
v_fst_1042_ = lean_ctor_get(v___x_1041_, 0);
if (lean_obj_tag(v_fst_1042_) == 0)
{
lean_object* v_snd_1043_; lean_object* v_snd_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_snd_1043_ = lean_ctor_get(v___x_1041_, 1);
lean_inc(v_snd_1043_);
lean_dec_ref(v___x_1041_);
v_snd_1044_ = lean_ctor_get(v_snd_1043_, 1);
lean_inc(v_snd_1044_);
lean_dec(v_snd_1043_);
v___x_1045_ = lean_string_utf8_byte_size(v_key_1038_);
v___x_1046_ = lean_nat_dec_eq(v_snd_1044_, v___x_1045_);
lean_dec(v_snd_1044_);
return v___x_1046_;
}
else
{
lean_object* v_val_1047_; uint8_t v___x_1048_; 
lean_inc_ref(v_fst_1042_);
lean_dec_ref(v___x_1041_);
v_val_1047_ = lean_ctor_get(v_fst_1042_, 0);
lean_inc(v_val_1047_);
lean_dec_ref_known(v_fst_1042_, 1);
v___x_1048_ = lean_unbox(v_val_1047_);
lean_dec(v_val_1047_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decodesTo___redArg___boxed(lean_object* v_es_1049_, lean_object* v_key_1050_){
_start:
{
uint8_t v_res_1051_; lean_object* v_r_1052_; 
v_res_1051_ = l_Std_Http_URI_EncodedQueryString_decodesTo___redArg(v_es_1049_, v_key_1050_);
lean_dec_ref(v_key_1050_);
lean_dec_ref(v_es_1049_);
v_r_1052_ = lean_box(v_res_1051_);
return v_r_1052_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryString_decodesTo(lean_object* v_r_1053_, lean_object* v_es_1054_, lean_object* v_key_1055_){
_start:
{
uint8_t v___x_1056_; 
v___x_1056_ = l_Std_Http_URI_EncodedQueryString_decodesTo___redArg(v_es_1054_, v_key_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decodesTo___boxed(lean_object* v_r_1057_, lean_object* v_es_1058_, lean_object* v_key_1059_){
_start:
{
uint8_t v_res_1060_; lean_object* v_r_1061_; 
v_res_1060_ = l_Std_Http_URI_EncodedQueryString_decodesTo(v_r_1057_, v_es_1058_, v_key_1059_);
lean_dec_ref(v_key_1059_);
lean_dec_ref(v_es_1058_);
lean_dec_ref(v_r_1057_);
v_r_1061_ = lean_box(v_res_1060_);
return v_r_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0(lean_object* v_len_1062_, lean_object* v_rawBytes_1063_, lean_object* v_key_1064_, lean_object* v_inst_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___redArg(v_len_1062_, v_rawBytes_1063_, v_key_1064_, v_a_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0___boxed(lean_object* v_len_1068_, lean_object* v_rawBytes_1069_, lean_object* v_key_1070_, lean_object* v_inst_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decodesTo_spec__0(v_len_1068_, v_rawBytes_1069_, v_key_1070_, v_inst_1071_, v_a_1072_);
lean_dec_ref(v_key_1070_);
lean_dec_ref(v_rawBytes_1069_);
lean_dec(v_len_1068_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringEncodedQueryString(lean_object* v_r_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_alloc_closure((void*)(l_Std_Http_URI_EncodedQueryString_toString___boxed), 2, 1);
lean_closure_set(v___x_1075_, 0, v_r_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_1077_; 
v___f_1077_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___redArg___boxed(lean_object* v___dummy_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Std_Http_URI_instReprEncodedQueryString___redArg();
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString(lean_object* v_r_1080_){
_start:
{
lean_object* v___f_1081_; 
v___f_1081_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___boxed(lean_object* v_r_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Std_Http_URI_instReprEncodedQueryString(v_r_1082_);
lean_dec_ref(v_r_1082_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_1085_; 
v___f_1085_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___redArg___boxed(lean_object* v___dummy_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Std_Http_URI_instBEqEncodedQueryString___redArg();
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString(lean_object* v_r_1088_){
_start:
{
lean_object* v___f_1089_; 
v___f_1089_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___boxed(lean_object* v_r_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Std_Http_URI_instBEqEncodedQueryString(v_r_1090_);
lean_dec_ref(v_r_1090_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_1093_; 
v___f_1093_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___redArg___boxed(lean_object* v___dummy_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Std_Http_URI_instHashableEncodedQueryString___redArg();
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString(lean_object* v_r_1096_){
_start:
{
lean_object* v___f_1097_; 
v___f_1097_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___boxed(lean_object* v_r_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Std_Http_URI_instHashableEncodedQueryString(v_r_1098_);
lean_dec_ref(v_r_1098_);
return v_res_1099_;
}
}
static uint64_t _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1106_; uint64_t v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__0));
v___x_1107_ = lean_byte_array_hash(v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__2));
v___x_1115_ = lean_byte_array_size(v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT uint64_t l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0(lean_object* v_x_1116_){
_start:
{
if (lean_obj_tag(v_x_1116_) == 0)
{
uint64_t v___x_1117_; 
v___x_1117_ = lean_uint64_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1, &l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1);
return v___x_1117_;
}
else
{
lean_object* v_val_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; uint64_t v___x_1125_; 
v_val_1118_ = lean_ctor_get(v_x_1116_, 0);
v___x_1119_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__2));
v___x_1120_ = lean_unsigned_to_nat(0u);
v___x_1121_ = lean_obj_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3, &l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3);
v___x_1122_ = lean_byte_array_size(v_val_1118_);
v___x_1123_ = 0;
v___x_1124_ = lean_byte_array_copy_slice(v_val_1118_, v___x_1120_, v___x_1119_, v___x_1121_, v___x_1122_, v___x_1123_);
v___x_1125_ = lean_byte_array_hash(v___x_1124_);
lean_dec_ref(v___x_1124_);
return v___x_1125_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___boxed(lean_object* v_x_1126_){
_start:
{
uint64_t v_res_1127_; lean_object* v_r_1128_; 
v_res_1127_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0(v_x_1126_);
lean_dec(v_x_1126_);
v_r_1128_ = lean_box_uint64(v_res_1127_);
return v_r_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_1131_; 
v___f_1131_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___closed__0));
return v___f_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___boxed(lean_object* v___dummy_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg();
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString(lean_object* v_r_1134_){
_start:
{
lean_object* v___f_1135_; 
v___f_1135_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___closed__0));
return v___f_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___boxed(lean_object* v_r_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Std_Http_URI_instHashableOptionEncodedQueryString(v_r_1136_);
lean_dec_ref(v_r_1136_);
return v_res_1137_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0(uint8_t v___y_1138_){
_start:
{
uint8_t v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = 48;
v___x_1185_ = lean_uint8_dec_le(v___x_1184_, v___y_1138_);
if (v___x_1185_ == 0)
{
goto v___jp_1179_;
}
else
{
uint8_t v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = 57;
v___x_1187_ = lean_uint8_dec_le(v___y_1138_, v___x_1186_);
if (v___x_1187_ == 0)
{
goto v___jp_1179_;
}
else
{
return v___x_1187_;
}
}
v___jp_1139_:
{
uint8_t v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = 45;
v___x_1141_ = lean_uint8_dec_eq(v___y_1138_, v___x_1140_);
if (v___x_1141_ == 0)
{
uint8_t v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = 46;
v___x_1143_ = lean_uint8_dec_eq(v___y_1138_, v___x_1142_);
if (v___x_1143_ == 0)
{
uint8_t v___x_1144_; uint8_t v___x_1145_; 
v___x_1144_ = 95;
v___x_1145_ = lean_uint8_dec_eq(v___y_1138_, v___x_1144_);
if (v___x_1145_ == 0)
{
uint8_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = 126;
v___x_1147_ = lean_uint8_dec_eq(v___y_1138_, v___x_1146_);
if (v___x_1147_ == 0)
{
uint8_t v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = 33;
v___x_1149_ = lean_uint8_dec_eq(v___y_1138_, v___x_1148_);
if (v___x_1149_ == 0)
{
uint8_t v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = 36;
v___x_1151_ = lean_uint8_dec_eq(v___y_1138_, v___x_1150_);
if (v___x_1151_ == 0)
{
uint8_t v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = 38;
v___x_1153_ = lean_uint8_dec_eq(v___y_1138_, v___x_1152_);
if (v___x_1153_ == 0)
{
uint8_t v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = 39;
v___x_1155_ = lean_uint8_dec_eq(v___y_1138_, v___x_1154_);
if (v___x_1155_ == 0)
{
uint8_t v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = 40;
v___x_1157_ = lean_uint8_dec_eq(v___y_1138_, v___x_1156_);
if (v___x_1157_ == 0)
{
uint8_t v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = 41;
v___x_1159_ = lean_uint8_dec_eq(v___y_1138_, v___x_1158_);
if (v___x_1159_ == 0)
{
uint8_t v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = 42;
v___x_1161_ = lean_uint8_dec_eq(v___y_1138_, v___x_1160_);
if (v___x_1161_ == 0)
{
uint8_t v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = 43;
v___x_1163_ = lean_uint8_dec_eq(v___y_1138_, v___x_1162_);
if (v___x_1163_ == 0)
{
uint8_t v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = 44;
v___x_1165_ = lean_uint8_dec_eq(v___y_1138_, v___x_1164_);
if (v___x_1165_ == 0)
{
uint8_t v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = 59;
v___x_1167_ = lean_uint8_dec_eq(v___y_1138_, v___x_1166_);
if (v___x_1167_ == 0)
{
uint8_t v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = 61;
v___x_1169_ = lean_uint8_dec_eq(v___y_1138_, v___x_1168_);
if (v___x_1169_ == 0)
{
uint8_t v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = 58;
v___x_1171_ = lean_uint8_dec_eq(v___y_1138_, v___x_1170_);
if (v___x_1171_ == 0)
{
uint8_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = 64;
v___x_1173_ = lean_uint8_dec_eq(v___y_1138_, v___x_1172_);
return v___x_1173_;
}
else
{
return v___x_1171_;
}
}
else
{
return v___x_1169_;
}
}
else
{
return v___x_1167_;
}
}
else
{
return v___x_1165_;
}
}
else
{
return v___x_1163_;
}
}
else
{
return v___x_1161_;
}
}
else
{
return v___x_1159_;
}
}
else
{
return v___x_1157_;
}
}
else
{
return v___x_1155_;
}
}
else
{
return v___x_1153_;
}
}
else
{
return v___x_1151_;
}
}
else
{
return v___x_1149_;
}
}
else
{
return v___x_1147_;
}
}
else
{
return v___x_1145_;
}
}
else
{
return v___x_1143_;
}
}
else
{
return v___x_1141_;
}
}
v___jp_1174_:
{
uint8_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = 65;
v___x_1176_ = lean_uint8_dec_le(v___x_1175_, v___y_1138_);
if (v___x_1176_ == 0)
{
goto v___jp_1139_;
}
else
{
uint8_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = 90;
v___x_1178_ = lean_uint8_dec_le(v___y_1138_, v___x_1177_);
if (v___x_1178_ == 0)
{
goto v___jp_1139_;
}
else
{
return v___x_1178_;
}
}
}
v___jp_1179_:
{
uint8_t v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = 97;
v___x_1181_ = lean_uint8_dec_le(v___x_1180_, v___y_1138_);
if (v___x_1181_ == 0)
{
goto v___jp_1174_;
}
else
{
uint8_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = 122;
v___x_1183_ = lean_uint8_dec_le(v___y_1138_, v___x_1182_);
if (v___x_1183_ == 0)
{
goto v___jp_1174_;
}
else
{
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___lam__0___boxed(lean_object* v___y_1188_){
_start:
{
uint8_t v___y_265__boxed_1189_; uint8_t v_res_1190_; lean_object* v_r_1191_; 
v___y_265__boxed_1189_ = lean_unbox(v___y_1188_);
v_res_1190_ = l_Std_Http_URI_EncodedSegment_encode___lam__0(v___y_265__boxed_1189_);
v_r_1191_ = lean_box(v_res_1190_);
return v_r_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode(lean_object* v_s_1193_){
_start:
{
lean_object* v___f_1194_; lean_object* v___x_1195_; 
v___f_1194_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_1195_ = l_Std_Http_URI_EncodedString_encode(v___f_1194_, v_s_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object* v_ba_1196_){
_start:
{
lean_object* v___f_1197_; lean_object* v___x_1198_; 
v___f_1197_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_1198_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1197_, v_ba_1196_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x21(lean_object* v_ba_1199_){
_start:
{
lean_object* v___f_1200_; lean_object* v___x_1201_; 
v___f_1200_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_1201_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1200_, v_ba_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object* v_segment_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Std_Http_URI_EncodedString_decode___redArg(v_segment_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode___boxed(lean_object* v_segment_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Std_Http_URI_EncodedSegment_decode(v_segment_1204_);
lean_dec_ref(v_segment_1204_);
return v_res_1205_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedFragment_encode___lam__0(uint8_t v___y_1206_){
_start:
{
uint8_t v___x_1256_; uint8_t v___x_1257_; 
v___x_1256_ = 48;
v___x_1257_ = lean_uint8_dec_le(v___x_1256_, v___y_1206_);
if (v___x_1257_ == 0)
{
goto v___jp_1251_;
}
else
{
uint8_t v___x_1258_; uint8_t v___x_1259_; 
v___x_1258_ = 57;
v___x_1259_ = lean_uint8_dec_le(v___y_1206_, v___x_1258_);
if (v___x_1259_ == 0)
{
goto v___jp_1251_;
}
else
{
return v___x_1259_;
}
}
v___jp_1207_:
{
uint8_t v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = 45;
v___x_1209_ = lean_uint8_dec_eq(v___y_1206_, v___x_1208_);
if (v___x_1209_ == 0)
{
uint8_t v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = 46;
v___x_1211_ = lean_uint8_dec_eq(v___y_1206_, v___x_1210_);
if (v___x_1211_ == 0)
{
uint8_t v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = 95;
v___x_1213_ = lean_uint8_dec_eq(v___y_1206_, v___x_1212_);
if (v___x_1213_ == 0)
{
uint8_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = 126;
v___x_1215_ = lean_uint8_dec_eq(v___y_1206_, v___x_1214_);
if (v___x_1215_ == 0)
{
uint8_t v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = 33;
v___x_1217_ = lean_uint8_dec_eq(v___y_1206_, v___x_1216_);
if (v___x_1217_ == 0)
{
uint8_t v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = 36;
v___x_1219_ = lean_uint8_dec_eq(v___y_1206_, v___x_1218_);
if (v___x_1219_ == 0)
{
uint8_t v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = 38;
v___x_1221_ = lean_uint8_dec_eq(v___y_1206_, v___x_1220_);
if (v___x_1221_ == 0)
{
uint8_t v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = 39;
v___x_1223_ = lean_uint8_dec_eq(v___y_1206_, v___x_1222_);
if (v___x_1223_ == 0)
{
uint8_t v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = 40;
v___x_1225_ = lean_uint8_dec_eq(v___y_1206_, v___x_1224_);
if (v___x_1225_ == 0)
{
uint8_t v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = 41;
v___x_1227_ = lean_uint8_dec_eq(v___y_1206_, v___x_1226_);
if (v___x_1227_ == 0)
{
uint8_t v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = 42;
v___x_1229_ = lean_uint8_dec_eq(v___y_1206_, v___x_1228_);
if (v___x_1229_ == 0)
{
uint8_t v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = 43;
v___x_1231_ = lean_uint8_dec_eq(v___y_1206_, v___x_1230_);
if (v___x_1231_ == 0)
{
uint8_t v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = 44;
v___x_1233_ = lean_uint8_dec_eq(v___y_1206_, v___x_1232_);
if (v___x_1233_ == 0)
{
uint8_t v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = 59;
v___x_1235_ = lean_uint8_dec_eq(v___y_1206_, v___x_1234_);
if (v___x_1235_ == 0)
{
uint8_t v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = 61;
v___x_1237_ = lean_uint8_dec_eq(v___y_1206_, v___x_1236_);
if (v___x_1237_ == 0)
{
uint8_t v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = 58;
v___x_1239_ = lean_uint8_dec_eq(v___y_1206_, v___x_1238_);
if (v___x_1239_ == 0)
{
uint8_t v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = 64;
v___x_1241_ = lean_uint8_dec_eq(v___y_1206_, v___x_1240_);
if (v___x_1241_ == 0)
{
uint8_t v___x_1242_; uint8_t v___x_1243_; 
v___x_1242_ = 47;
v___x_1243_ = lean_uint8_dec_eq(v___y_1206_, v___x_1242_);
if (v___x_1243_ == 0)
{
uint8_t v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = 63;
v___x_1245_ = lean_uint8_dec_eq(v___y_1206_, v___x_1244_);
return v___x_1245_;
}
else
{
return v___x_1243_;
}
}
else
{
return v___x_1241_;
}
}
else
{
return v___x_1239_;
}
}
else
{
return v___x_1237_;
}
}
else
{
return v___x_1235_;
}
}
else
{
return v___x_1233_;
}
}
else
{
return v___x_1231_;
}
}
else
{
return v___x_1229_;
}
}
else
{
return v___x_1227_;
}
}
else
{
return v___x_1225_;
}
}
else
{
return v___x_1223_;
}
}
else
{
return v___x_1221_;
}
}
else
{
return v___x_1219_;
}
}
else
{
return v___x_1217_;
}
}
else
{
return v___x_1215_;
}
}
else
{
return v___x_1213_;
}
}
else
{
return v___x_1211_;
}
}
else
{
return v___x_1209_;
}
}
v___jp_1246_:
{
uint8_t v___x_1247_; uint8_t v___x_1248_; 
v___x_1247_ = 65;
v___x_1248_ = lean_uint8_dec_le(v___x_1247_, v___y_1206_);
if (v___x_1248_ == 0)
{
goto v___jp_1207_;
}
else
{
uint8_t v___x_1249_; uint8_t v___x_1250_; 
v___x_1249_ = 90;
v___x_1250_ = lean_uint8_dec_le(v___y_1206_, v___x_1249_);
if (v___x_1250_ == 0)
{
goto v___jp_1207_;
}
else
{
return v___x_1250_;
}
}
}
v___jp_1251_:
{
uint8_t v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = 97;
v___x_1253_ = lean_uint8_dec_le(v___x_1252_, v___y_1206_);
if (v___x_1253_ == 0)
{
goto v___jp_1246_;
}
else
{
uint8_t v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = 122;
v___x_1255_ = lean_uint8_dec_le(v___y_1206_, v___x_1254_);
if (v___x_1255_ == 0)
{
goto v___jp_1246_;
}
else
{
return v___x_1255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed(lean_object* v___y_1260_){
_start:
{
uint8_t v___y_289__boxed_1261_; uint8_t v_res_1262_; lean_object* v_r_1263_; 
v___y_289__boxed_1261_ = lean_unbox(v___y_1260_);
v_res_1262_ = l_Std_Http_URI_EncodedFragment_encode___lam__0(v___y_289__boxed_1261_);
v_r_1263_ = lean_box(v_res_1262_);
return v_r_1263_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object* v_s_1265_){
_start:
{
lean_object* v___f_1266_; lean_object* v___x_1267_; 
v___f_1266_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1267_ = l_Std_Http_URI_EncodedString_encode(v___f_1266_, v_s_1265_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object* v_ba_1268_){
_start:
{
lean_object* v___f_1269_; lean_object* v___x_1270_; 
v___f_1269_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1270_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1269_, v_ba_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x21(lean_object* v_ba_1271_){
_start:
{
lean_object* v___f_1272_; lean_object* v___x_1273_; 
v___f_1272_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1273_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1272_, v_ba_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object* v_fragment_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Std_Http_URI_EncodedString_decode___redArg(v_fragment_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode___boxed(lean_object* v_fragment_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Std_Http_URI_EncodedFragment_decode(v_fragment_1276_);
lean_dec_ref(v_fragment_1276_);
return v_res_1277_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedUserInfo_encode___lam__0(uint8_t v___y_1278_){
_start:
{
uint8_t v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = 48;
v___x_1323_ = lean_uint8_dec_le(v___x_1322_, v___y_1278_);
if (v___x_1323_ == 0)
{
goto v___jp_1317_;
}
else
{
uint8_t v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = 57;
v___x_1325_ = lean_uint8_dec_le(v___y_1278_, v___x_1324_);
if (v___x_1325_ == 0)
{
goto v___jp_1317_;
}
else
{
return v___x_1325_;
}
}
v___jp_1279_:
{
uint8_t v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = 45;
v___x_1281_ = lean_uint8_dec_eq(v___y_1278_, v___x_1280_);
if (v___x_1281_ == 0)
{
uint8_t v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = 46;
v___x_1283_ = lean_uint8_dec_eq(v___y_1278_, v___x_1282_);
if (v___x_1283_ == 0)
{
uint8_t v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = 95;
v___x_1285_ = lean_uint8_dec_eq(v___y_1278_, v___x_1284_);
if (v___x_1285_ == 0)
{
uint8_t v___x_1286_; uint8_t v___x_1287_; 
v___x_1286_ = 126;
v___x_1287_ = lean_uint8_dec_eq(v___y_1278_, v___x_1286_);
if (v___x_1287_ == 0)
{
uint8_t v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = 33;
v___x_1289_ = lean_uint8_dec_eq(v___y_1278_, v___x_1288_);
if (v___x_1289_ == 0)
{
uint8_t v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = 36;
v___x_1291_ = lean_uint8_dec_eq(v___y_1278_, v___x_1290_);
if (v___x_1291_ == 0)
{
uint8_t v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = 38;
v___x_1293_ = lean_uint8_dec_eq(v___y_1278_, v___x_1292_);
if (v___x_1293_ == 0)
{
uint8_t v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = 39;
v___x_1295_ = lean_uint8_dec_eq(v___y_1278_, v___x_1294_);
if (v___x_1295_ == 0)
{
uint8_t v___x_1296_; uint8_t v___x_1297_; 
v___x_1296_ = 40;
v___x_1297_ = lean_uint8_dec_eq(v___y_1278_, v___x_1296_);
if (v___x_1297_ == 0)
{
uint8_t v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = 41;
v___x_1299_ = lean_uint8_dec_eq(v___y_1278_, v___x_1298_);
if (v___x_1299_ == 0)
{
uint8_t v___x_1300_; uint8_t v___x_1301_; 
v___x_1300_ = 42;
v___x_1301_ = lean_uint8_dec_eq(v___y_1278_, v___x_1300_);
if (v___x_1301_ == 0)
{
uint8_t v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = 43;
v___x_1303_ = lean_uint8_dec_eq(v___y_1278_, v___x_1302_);
if (v___x_1303_ == 0)
{
uint8_t v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = 44;
v___x_1305_ = lean_uint8_dec_eq(v___y_1278_, v___x_1304_);
if (v___x_1305_ == 0)
{
uint8_t v___x_1306_; uint8_t v___x_1307_; 
v___x_1306_ = 59;
v___x_1307_ = lean_uint8_dec_eq(v___y_1278_, v___x_1306_);
if (v___x_1307_ == 0)
{
uint8_t v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = 61;
v___x_1309_ = lean_uint8_dec_eq(v___y_1278_, v___x_1308_);
if (v___x_1309_ == 0)
{
uint8_t v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = 58;
v___x_1311_ = lean_uint8_dec_eq(v___y_1278_, v___x_1310_);
return v___x_1311_;
}
else
{
return v___x_1309_;
}
}
else
{
return v___x_1307_;
}
}
else
{
return v___x_1305_;
}
}
else
{
return v___x_1303_;
}
}
else
{
return v___x_1301_;
}
}
else
{
return v___x_1299_;
}
}
else
{
return v___x_1297_;
}
}
else
{
return v___x_1295_;
}
}
else
{
return v___x_1293_;
}
}
else
{
return v___x_1291_;
}
}
else
{
return v___x_1289_;
}
}
else
{
return v___x_1287_;
}
}
else
{
return v___x_1285_;
}
}
else
{
return v___x_1283_;
}
}
else
{
return v___x_1281_;
}
}
v___jp_1312_:
{
uint8_t v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = 65;
v___x_1314_ = lean_uint8_dec_le(v___x_1313_, v___y_1278_);
if (v___x_1314_ == 0)
{
goto v___jp_1279_;
}
else
{
uint8_t v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = 90;
v___x_1316_ = lean_uint8_dec_le(v___y_1278_, v___x_1315_);
if (v___x_1316_ == 0)
{
goto v___jp_1279_;
}
else
{
return v___x_1316_;
}
}
}
v___jp_1317_:
{
uint8_t v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = 97;
v___x_1319_ = lean_uint8_dec_le(v___x_1318_, v___y_1278_);
if (v___x_1319_ == 0)
{
goto v___jp_1312_;
}
else
{
uint8_t v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = 122;
v___x_1321_ = lean_uint8_dec_le(v___y_1278_, v___x_1320_);
if (v___x_1321_ == 0)
{
goto v___jp_1312_;
}
else
{
return v___x_1321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed(lean_object* v___y_1326_){
_start:
{
uint8_t v___y_253__boxed_1327_; uint8_t v_res_1328_; lean_object* v_r_1329_; 
v___y_253__boxed_1327_ = lean_unbox(v___y_1326_);
v_res_1328_ = l_Std_Http_URI_EncodedUserInfo_encode___lam__0(v___y_253__boxed_1327_);
v_r_1329_ = lean_box(v_res_1328_);
return v_r_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object* v_s_1331_){
_start:
{
lean_object* v___f_1332_; lean_object* v___x_1333_; 
v___f_1332_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1333_ = l_Std_Http_URI_EncodedString_encode(v___f_1332_, v_s_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object* v_ba_1334_){
_start:
{
lean_object* v___f_1335_; lean_object* v___x_1336_; 
v___f_1335_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1336_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1335_, v_ba_1334_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x21(lean_object* v_ba_1337_){
_start:
{
lean_object* v___f_1338_; lean_object* v___x_1339_; 
v___f_1338_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1339_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1338_, v_ba_1337_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode(lean_object* v_userInfo_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Std_Http_URI_EncodedString_decode___redArg(v_userInfo_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode___boxed(lean_object* v_userInfo_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Std_Http_URI_EncodedUserInfo_decode(v_userInfo_1342_);
lean_dec_ref(v_userInfo_1342_);
return v_res_1343_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryParam_encode___lam__0(uint8_t v___y_1344_){
_start:
{
uint8_t v___x_1401_; uint8_t v___x_1402_; 
v___x_1401_ = 48;
v___x_1402_ = lean_uint8_dec_le(v___x_1401_, v___y_1344_);
if (v___x_1402_ == 0)
{
goto v___jp_1396_;
}
else
{
uint8_t v___x_1403_; uint8_t v___x_1404_; 
v___x_1403_ = 57;
v___x_1404_ = lean_uint8_dec_le(v___y_1344_, v___x_1403_);
if (v___x_1404_ == 0)
{
goto v___jp_1396_;
}
else
{
goto v___jp_1345_;
}
}
v___jp_1345_:
{
uint8_t v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = 38;
v___x_1347_ = lean_uint8_dec_eq(v___y_1344_, v___x_1346_);
if (v___x_1347_ == 0)
{
uint8_t v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = 61;
v___x_1349_ = lean_uint8_dec_eq(v___y_1344_, v___x_1348_);
if (v___x_1349_ == 0)
{
uint8_t v___x_1350_; 
v___x_1350_ = 1;
return v___x_1350_;
}
else
{
return v___x_1347_;
}
}
else
{
uint8_t v___x_1351_; 
v___x_1351_ = 0;
return v___x_1351_;
}
}
v___jp_1352_:
{
uint8_t v___x_1353_; uint8_t v___x_1354_; 
v___x_1353_ = 45;
v___x_1354_ = lean_uint8_dec_eq(v___y_1344_, v___x_1353_);
if (v___x_1354_ == 0)
{
uint8_t v___x_1355_; uint8_t v___x_1356_; 
v___x_1355_ = 46;
v___x_1356_ = lean_uint8_dec_eq(v___y_1344_, v___x_1355_);
if (v___x_1356_ == 0)
{
uint8_t v___x_1357_; uint8_t v___x_1358_; 
v___x_1357_ = 95;
v___x_1358_ = lean_uint8_dec_eq(v___y_1344_, v___x_1357_);
if (v___x_1358_ == 0)
{
uint8_t v___x_1359_; uint8_t v___x_1360_; 
v___x_1359_ = 126;
v___x_1360_ = lean_uint8_dec_eq(v___y_1344_, v___x_1359_);
if (v___x_1360_ == 0)
{
uint8_t v___x_1361_; uint8_t v___x_1362_; 
v___x_1361_ = 33;
v___x_1362_ = lean_uint8_dec_eq(v___y_1344_, v___x_1361_);
if (v___x_1362_ == 0)
{
uint8_t v___x_1363_; uint8_t v___x_1364_; 
v___x_1363_ = 36;
v___x_1364_ = lean_uint8_dec_eq(v___y_1344_, v___x_1363_);
if (v___x_1364_ == 0)
{
uint8_t v___x_1365_; uint8_t v___x_1366_; 
v___x_1365_ = 38;
v___x_1366_ = lean_uint8_dec_eq(v___y_1344_, v___x_1365_);
if (v___x_1366_ == 0)
{
uint8_t v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = 39;
v___x_1368_ = lean_uint8_dec_eq(v___y_1344_, v___x_1367_);
if (v___x_1368_ == 0)
{
uint8_t v___x_1369_; uint8_t v___x_1370_; 
v___x_1369_ = 40;
v___x_1370_ = lean_uint8_dec_eq(v___y_1344_, v___x_1369_);
if (v___x_1370_ == 0)
{
uint8_t v___x_1371_; uint8_t v___x_1372_; 
v___x_1371_ = 41;
v___x_1372_ = lean_uint8_dec_eq(v___y_1344_, v___x_1371_);
if (v___x_1372_ == 0)
{
uint8_t v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = 42;
v___x_1374_ = lean_uint8_dec_eq(v___y_1344_, v___x_1373_);
if (v___x_1374_ == 0)
{
uint8_t v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = 43;
v___x_1376_ = lean_uint8_dec_eq(v___y_1344_, v___x_1375_);
if (v___x_1376_ == 0)
{
uint8_t v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = 44;
v___x_1378_ = lean_uint8_dec_eq(v___y_1344_, v___x_1377_);
if (v___x_1378_ == 0)
{
uint8_t v___x_1379_; uint8_t v___x_1380_; 
v___x_1379_ = 59;
v___x_1380_ = lean_uint8_dec_eq(v___y_1344_, v___x_1379_);
if (v___x_1380_ == 0)
{
uint8_t v___x_1381_; uint8_t v___x_1382_; 
v___x_1381_ = 61;
v___x_1382_ = lean_uint8_dec_eq(v___y_1344_, v___x_1381_);
if (v___x_1382_ == 0)
{
uint8_t v___x_1383_; uint8_t v___x_1384_; 
v___x_1383_ = 58;
v___x_1384_ = lean_uint8_dec_eq(v___y_1344_, v___x_1383_);
if (v___x_1384_ == 0)
{
uint8_t v___x_1385_; uint8_t v___x_1386_; 
v___x_1385_ = 64;
v___x_1386_ = lean_uint8_dec_eq(v___y_1344_, v___x_1385_);
if (v___x_1386_ == 0)
{
uint8_t v___x_1387_; uint8_t v___x_1388_; 
v___x_1387_ = 47;
v___x_1388_ = lean_uint8_dec_eq(v___y_1344_, v___x_1387_);
if (v___x_1388_ == 0)
{
uint8_t v___x_1389_; uint8_t v___x_1390_; 
v___x_1389_ = 63;
v___x_1390_ = lean_uint8_dec_eq(v___y_1344_, v___x_1389_);
if (v___x_1390_ == 0)
{
return v___x_1390_;
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
else
{
goto v___jp_1345_;
}
}
v___jp_1391_:
{
uint8_t v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = 65;
v___x_1393_ = lean_uint8_dec_le(v___x_1392_, v___y_1344_);
if (v___x_1393_ == 0)
{
goto v___jp_1352_;
}
else
{
uint8_t v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = 90;
v___x_1395_ = lean_uint8_dec_le(v___y_1344_, v___x_1394_);
if (v___x_1395_ == 0)
{
goto v___jp_1352_;
}
else
{
goto v___jp_1345_;
}
}
}
v___jp_1396_:
{
uint8_t v___x_1397_; uint8_t v___x_1398_; 
v___x_1397_ = 97;
v___x_1398_ = lean_uint8_dec_le(v___x_1397_, v___y_1344_);
if (v___x_1398_ == 0)
{
goto v___jp_1391_;
}
else
{
uint8_t v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = 122;
v___x_1400_ = lean_uint8_dec_le(v___y_1344_, v___x_1399_);
if (v___x_1400_ == 0)
{
goto v___jp_1391_;
}
else
{
goto v___jp_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed(lean_object* v___y_1405_){
_start:
{
uint8_t v___y_625__boxed_1406_; uint8_t v_res_1407_; lean_object* v_r_1408_; 
v___y_625__boxed_1406_ = lean_unbox(v___y_1405_);
v_res_1407_ = l_Std_Http_URI_EncodedQueryParam_encode___lam__0(v___y_625__boxed_1406_);
v_r_1408_ = lean_box(v_res_1407_);
return v_r_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode(lean_object* v_s_1410_){
_start:
{
lean_object* v___f_1411_; lean_object* v_encoded_1412_; 
v___f_1411_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v_encoded_1412_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_1410_, v___f_1411_);
return v_encoded_1412_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f___lam__0(uint8_t v___y_1413_){
_start:
{
uint8_t v___x_1468_; uint8_t v___x_1469_; 
v___x_1468_ = 48;
v___x_1469_ = lean_uint8_dec_le(v___x_1468_, v___y_1413_);
if (v___x_1469_ == 0)
{
goto v___jp_1463_;
}
else
{
uint8_t v___x_1470_; uint8_t v___x_1471_; 
v___x_1470_ = 57;
v___x_1471_ = lean_uint8_dec_le(v___y_1413_, v___x_1470_);
if (v___x_1471_ == 0)
{
goto v___jp_1463_;
}
else
{
goto v___jp_1414_;
}
}
v___jp_1414_:
{
uint8_t v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = 38;
v___x_1416_ = lean_uint8_dec_eq(v___y_1413_, v___x_1415_);
if (v___x_1416_ == 0)
{
uint8_t v___x_1417_; 
v___x_1417_ = 1;
return v___x_1417_;
}
else
{
uint8_t v___x_1418_; 
v___x_1418_ = 0;
return v___x_1418_;
}
}
v___jp_1419_:
{
uint8_t v___x_1420_; uint8_t v___x_1421_; 
v___x_1420_ = 45;
v___x_1421_ = lean_uint8_dec_eq(v___y_1413_, v___x_1420_);
if (v___x_1421_ == 0)
{
uint8_t v___x_1422_; uint8_t v___x_1423_; 
v___x_1422_ = 46;
v___x_1423_ = lean_uint8_dec_eq(v___y_1413_, v___x_1422_);
if (v___x_1423_ == 0)
{
uint8_t v___x_1424_; uint8_t v___x_1425_; 
v___x_1424_ = 95;
v___x_1425_ = lean_uint8_dec_eq(v___y_1413_, v___x_1424_);
if (v___x_1425_ == 0)
{
uint8_t v___x_1426_; uint8_t v___x_1427_; 
v___x_1426_ = 126;
v___x_1427_ = lean_uint8_dec_eq(v___y_1413_, v___x_1426_);
if (v___x_1427_ == 0)
{
uint8_t v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = 33;
v___x_1429_ = lean_uint8_dec_eq(v___y_1413_, v___x_1428_);
if (v___x_1429_ == 0)
{
uint8_t v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = 36;
v___x_1431_ = lean_uint8_dec_eq(v___y_1413_, v___x_1430_);
if (v___x_1431_ == 0)
{
uint8_t v___x_1432_; uint8_t v___x_1433_; 
v___x_1432_ = 38;
v___x_1433_ = lean_uint8_dec_eq(v___y_1413_, v___x_1432_);
if (v___x_1433_ == 0)
{
uint8_t v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = 39;
v___x_1435_ = lean_uint8_dec_eq(v___y_1413_, v___x_1434_);
if (v___x_1435_ == 0)
{
uint8_t v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = 40;
v___x_1437_ = lean_uint8_dec_eq(v___y_1413_, v___x_1436_);
if (v___x_1437_ == 0)
{
uint8_t v___x_1438_; uint8_t v___x_1439_; 
v___x_1438_ = 41;
v___x_1439_ = lean_uint8_dec_eq(v___y_1413_, v___x_1438_);
if (v___x_1439_ == 0)
{
uint8_t v___x_1440_; uint8_t v___x_1441_; 
v___x_1440_ = 42;
v___x_1441_ = lean_uint8_dec_eq(v___y_1413_, v___x_1440_);
if (v___x_1441_ == 0)
{
uint8_t v___x_1442_; uint8_t v___x_1443_; 
v___x_1442_ = 43;
v___x_1443_ = lean_uint8_dec_eq(v___y_1413_, v___x_1442_);
if (v___x_1443_ == 0)
{
uint8_t v___x_1444_; uint8_t v___x_1445_; 
v___x_1444_ = 44;
v___x_1445_ = lean_uint8_dec_eq(v___y_1413_, v___x_1444_);
if (v___x_1445_ == 0)
{
uint8_t v___x_1446_; uint8_t v___x_1447_; 
v___x_1446_ = 59;
v___x_1447_ = lean_uint8_dec_eq(v___y_1413_, v___x_1446_);
if (v___x_1447_ == 0)
{
uint8_t v___x_1448_; uint8_t v___x_1449_; 
v___x_1448_ = 61;
v___x_1449_ = lean_uint8_dec_eq(v___y_1413_, v___x_1448_);
if (v___x_1449_ == 0)
{
uint8_t v___x_1450_; uint8_t v___x_1451_; 
v___x_1450_ = 58;
v___x_1451_ = lean_uint8_dec_eq(v___y_1413_, v___x_1450_);
if (v___x_1451_ == 0)
{
uint8_t v___x_1452_; uint8_t v___x_1453_; 
v___x_1452_ = 64;
v___x_1453_ = lean_uint8_dec_eq(v___y_1413_, v___x_1452_);
if (v___x_1453_ == 0)
{
uint8_t v___x_1454_; uint8_t v___x_1455_; 
v___x_1454_ = 47;
v___x_1455_ = lean_uint8_dec_eq(v___y_1413_, v___x_1454_);
if (v___x_1455_ == 0)
{
uint8_t v___x_1456_; uint8_t v___x_1457_; 
v___x_1456_ = 63;
v___x_1457_ = lean_uint8_dec_eq(v___y_1413_, v___x_1456_);
if (v___x_1457_ == 0)
{
return v___x_1457_;
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
else
{
goto v___jp_1414_;
}
}
v___jp_1458_:
{
uint8_t v___x_1459_; uint8_t v___x_1460_; 
v___x_1459_ = 65;
v___x_1460_ = lean_uint8_dec_le(v___x_1459_, v___y_1413_);
if (v___x_1460_ == 0)
{
goto v___jp_1419_;
}
else
{
uint8_t v___x_1461_; uint8_t v___x_1462_; 
v___x_1461_ = 90;
v___x_1462_ = lean_uint8_dec_le(v___y_1413_, v___x_1461_);
if (v___x_1462_ == 0)
{
goto v___jp_1419_;
}
else
{
goto v___jp_1414_;
}
}
}
v___jp_1463_:
{
uint8_t v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = 97;
v___x_1465_ = lean_uint8_dec_le(v___x_1464_, v___y_1413_);
if (v___x_1465_ == 0)
{
goto v___jp_1458_;
}
else
{
uint8_t v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = 122;
v___x_1467_ = lean_uint8_dec_le(v___y_1413_, v___x_1466_);
if (v___x_1467_ == 0)
{
goto v___jp_1458_;
}
else
{
goto v___jp_1414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f___lam__0___boxed(lean_object* v___y_1472_){
_start:
{
uint8_t v___y_322__boxed_1473_; uint8_t v_res_1474_; lean_object* v_r_1475_; 
v___y_322__boxed_1473_ = lean_unbox(v___y_1472_);
v_res_1474_ = l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f___lam__0(v___y_322__boxed_1473_);
v_r_1475_ = lean_box(v_res_1474_);
return v_r_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f(lean_object* v_ba_1477_){
_start:
{
lean_object* v___f_1478_; lean_object* v___x_1479_; 
v___f_1478_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f___closed__0));
v___x_1479_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_1477_, v___f_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x21(lean_object* v_ba_1480_){
_start:
{
lean_object* v___f_1481_; lean_object* v___x_1482_; 
v___f_1481_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f___closed__0));
v___x_1482_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v_ba_1480_, v___f_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object* v_s_1483_){
_start:
{
lean_object* v___f_1484_; lean_object* v___x_1485_; 
v___f_1484_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f___closed__0));
v___x_1485_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_1483_, v___f_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object* v_param_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_param_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode___boxed(lean_object* v_param_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Std_Http_URI_EncodedQueryParam_decode(v_param_1488_);
lean_dec_ref(v_param_1488_);
return v_res_1489_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Bitwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lossy(uint8_t builtin);
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
res = runtime_initialize_Init_Data_String_Lossy(builtin);
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
lean_object* initialize_Init_Data_String_Lossy(uint8_t builtin);
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
res = initialize_Init_Data_String_Lossy(builtin);
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
