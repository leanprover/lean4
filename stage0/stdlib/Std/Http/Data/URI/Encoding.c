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
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___redArg(){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_ByteArray_empty;
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___redArg___boxed(lean_object* v___dummy_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Std_Http_URI_EncodedString_empty___redArg();
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty(lean_object* v_r_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_ByteArray_empty;
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___boxed(lean_object* v_r_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Std_Http_URI_EncodedString_empty(v_r_294_);
lean_dec_ref(v_r_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___redArg(){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_ByteArray_empty;
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___redArg___boxed(lean_object* v___dummy_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Std_Http_URI_EncodedString_instInhabited___redArg();
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited(lean_object* v_r_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_ByteArray_empty;
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___boxed(lean_object* v_r_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Std_Http_URI_EncodedString_instInhabited(v_r_302_);
lean_dec_ref(v_r_302_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(lean_object* v_s_304_, uint8_t v_c_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = lean_byte_array_push(v_s_304_, v_c_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg___boxed(lean_object* v_s_307_, lean_object* v_c_308_){
_start:
{
uint8_t v_c_boxed_309_; lean_object* v_res_310_; 
v_c_boxed_309_ = lean_unbox(v_c_308_);
v_res_310_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(v_s_307_, v_c_boxed_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(lean_object* v_r_311_, lean_object* v_s_312_, uint8_t v_c_313_, lean_object* v_h_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = lean_byte_array_push(v_s_312_, v_c_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___boxed(lean_object* v_r_316_, lean_object* v_s_317_, lean_object* v_c_318_, lean_object* v_h_319_){
_start:
{
uint8_t v_c_boxed_320_; lean_object* v_res_321_; 
v_c_boxed_320_ = lean_unbox(v_c_318_);
v_res_321_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(v_r_316_, v_s_317_, v_c_boxed_320_, v_h_319_);
lean_dec_ref(v_r_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(uint8_t v_b_322_, lean_object* v_s_323_){
_start:
{
uint8_t v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; uint8_t v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; uint8_t v___x_331_; uint8_t v___x_332_; lean_object* v_ba_333_; 
v___x_324_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__0, &l_Std_Http_URI_isEncodedChar___closed__0_once, _init_l_Std_Http_URI_isEncodedChar___closed__0);
v___x_325_ = lean_byte_array_push(v_s_323_, v___x_324_);
v___x_326_ = 4;
v___x_327_ = lean_uint8_shift_right(v_b_322_, v___x_326_);
v___x_328_ = l_Std_Http_URI_hexDigit(v___x_327_);
v___x_329_ = lean_byte_array_push(v___x_325_, v___x_328_);
v___x_330_ = 15;
v___x_331_ = lean_uint8_land(v_b_322_, v___x_330_);
v___x_332_ = l_Std_Http_URI_hexDigit(v___x_331_);
v_ba_333_ = lean_byte_array_push(v___x_329_, v___x_332_);
return v_ba_333_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg___boxed(lean_object* v_b_334_, lean_object* v_s_335_){
_start:
{
uint8_t v_b_boxed_336_; lean_object* v_res_337_; 
v_b_boxed_336_ = lean_unbox(v_b_334_);
v_res_337_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_boxed_336_, v_s_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(lean_object* v_r_338_, uint8_t v_b_339_, lean_object* v_s_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_339_, v_s_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___boxed(lean_object* v_r_342_, lean_object* v_b_343_, lean_object* v_s_344_){
_start:
{
uint8_t v_b_boxed_345_; lean_object* v_res_346_; 
v_b_boxed_345_ = lean_unbox(v_b_343_);
v_res_346_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(v_r_342_, v_b_boxed_345_, v_s_344_);
lean_dec_ref(v_r_342_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(lean_object* v_r_347_, lean_object* v_as_348_, size_t v_i_349_, size_t v_stop_350_, lean_object* v_b_351_){
_start:
{
lean_object* v___y_353_; uint8_t v___x_357_; 
v___x_357_ = lean_usize_dec_eq(v_i_349_, v_stop_350_);
if (v___x_357_ == 0)
{
uint8_t v___x_358_; uint8_t v___y_360_; uint8_t v___x_363_; uint8_t v___x_364_; 
v___x_358_ = lean_byte_array_uget(v_as_348_, v_i_349_);
v___x_363_ = 128;
v___x_364_ = lean_uint8_dec_lt(v___x_358_, v___x_363_);
if (v___x_364_ == 0)
{
v___y_360_ = v___x_364_;
goto v___jp_359_;
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_365_ = lean_box(v___x_358_);
lean_inc_ref(v_r_347_);
v___x_366_ = lean_apply_1(v_r_347_, v___x_365_);
v___x_367_ = lean_unbox(v___x_366_);
v___y_360_ = v___x_367_;
goto v___jp_359_;
}
v___jp_359_:
{
if (v___y_360_ == 0)
{
lean_object* v___x_361_; 
v___x_361_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_358_, v_b_351_);
v___y_353_ = v___x_361_;
goto v___jp_352_;
}
else
{
lean_object* v___x_362_; 
v___x_362_ = lean_byte_array_push(v_b_351_, v___x_358_);
v___y_353_ = v___x_362_;
goto v___jp_352_;
}
}
}
else
{
lean_dec_ref(v_r_347_);
return v_b_351_;
}
v___jp_352_:
{
size_t v___x_354_; size_t v___x_355_; 
v___x_354_ = ((size_t)1ULL);
v___x_355_ = lean_usize_add(v_i_349_, v___x_354_);
v_i_349_ = v___x_355_;
v_b_351_ = v___y_353_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0___boxed(lean_object* v_r_368_, lean_object* v_as_369_, lean_object* v_i_370_, lean_object* v_stop_371_, lean_object* v_b_372_){
_start:
{
size_t v_i_boxed_373_; size_t v_stop_boxed_374_; lean_object* v_res_375_; 
v_i_boxed_373_ = lean_unbox_usize(v_i_370_);
lean_dec(v_i_370_);
v_stop_boxed_374_ = lean_unbox_usize(v_stop_371_);
lean_dec(v_stop_371_);
v_res_375_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_368_, v_as_369_, v_i_boxed_373_, v_stop_boxed_374_, v_b_372_);
lean_dec_ref(v_as_369_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode(lean_object* v_r_376_, lean_object* v_s_377_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_378_ = l_ByteArray_empty;
v___x_379_ = lean_string_to_utf8(v_s_377_);
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_byte_array_size(v___x_379_);
v___x_382_ = lean_nat_dec_lt(v___x_380_, v___x_381_);
if (v___x_382_ == 0)
{
lean_dec_ref(v___x_379_);
lean_dec_ref(v_r_376_);
return v___x_378_;
}
else
{
uint8_t v___x_383_; 
v___x_383_ = lean_nat_dec_le(v___x_381_, v___x_381_);
if (v___x_383_ == 0)
{
if (v___x_382_ == 0)
{
lean_dec_ref(v___x_379_);
lean_dec_ref(v_r_376_);
return v___x_378_;
}
else
{
size_t v___x_384_; size_t v___x_385_; lean_object* v___x_386_; 
v___x_384_ = ((size_t)0ULL);
v___x_385_ = lean_usize_of_nat(v___x_381_);
v___x_386_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_376_, v___x_379_, v___x_384_, v___x_385_, v___x_378_);
lean_dec_ref(v___x_379_);
return v___x_386_;
}
}
else
{
size_t v___x_387_; size_t v___x_388_; lean_object* v___x_389_; 
v___x_387_ = ((size_t)0ULL);
v___x_388_ = lean_usize_of_nat(v___x_381_);
v___x_389_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_376_, v___x_379_, v___x_387_, v___x_388_, v___x_378_);
lean_dec_ref(v___x_379_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode___boxed(lean_object* v_r_390_, lean_object* v_s_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_Http_URI_EncodedString_encode(v_r_390_, v_s_391_);
lean_dec_ref(v_s_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x3f(lean_object* v_r_393_, lean_object* v_ba_394_){
_start:
{
uint8_t v___x_395_; 
lean_inc_ref(v_ba_394_);
v___x_395_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_393_, v_ba_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; 
lean_dec_ref(v_ba_394_);
v___x_396_ = lean_box(0);
return v___x_396_;
}
else
{
uint8_t v___x_397_; 
v___x_397_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_394_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
lean_dec_ref(v_ba_394_);
v___x_398_ = lean_box(0);
return v___x_398_;
}
else
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v_ba_394_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = l_ByteArray_empty;
v___x_402_ = lean_panic_fn_borrowed(v___x_401_, v_msg_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(lean_object* v_r_403_, lean_object* v_msg_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v_msg_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_406_, lean_object* v_msg_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(v_r_406_, v_msg_407_);
lean_dec_ref(v_r_406_);
return v_res_408_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_412_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2));
v___x_413_ = lean_unsigned_to_nat(12u);
v___x_414_ = lean_unsigned_to_nat(320u);
v___x_415_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1));
v___x_416_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_417_ = l_mkPanicMessageWithDecl(v___x_416_, v___x_415_, v___x_414_, v___x_413_, v___x_412_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x21(lean_object* v_r_418_, lean_object* v_ba_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_418_, v_ba_419_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_obj_once(&l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3, &l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3_once, _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3);
v___x_422_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v___x_421_);
return v___x_422_;
}
else
{
lean_object* v_val_423_; 
v_val_423_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_val_423_);
lean_dec_ref_known(v___x_420_, 1);
return v_val_423_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f(lean_object* v_r_424_, lean_object* v_s_425_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_string_to_utf8(v_s_425_);
v___x_427_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_424_, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f___boxed(lean_object* v_r_428_, lean_object* v_s_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Std_Http_URI_EncodedString_ofString_x3f(v_r_428_, v_s_429_);
lean_dec_ref(v_s_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21(lean_object* v_r_431_, lean_object* v_s_432_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_string_to_utf8(v_s_432_);
v___x_434_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v_r_431_, v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21___boxed(lean_object* v_r_435_, lean_object* v_s_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_Http_URI_EncodedString_ofString_x21(v_r_435_, v_s_436_);
lean_dec_ref(v_s_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg(lean_object* v_ba_438_){
_start:
{
lean_inc_ref(v_ba_438_);
return v_ba_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg___boxed(lean_object* v_ba_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Std_Http_URI_EncodedString_new___redArg(v_ba_439_);
lean_dec_ref(v_ba_439_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new(lean_object* v_r_441_, lean_object* v_ba_442_, lean_object* v_valid_443_, lean_object* v___validEncoding_444_){
_start:
{
lean_inc_ref(v_ba_442_);
return v_ba_442_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___boxed(lean_object* v_r_445_, lean_object* v_ba_446_, lean_object* v_valid_447_, lean_object* v___validEncoding_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Std_Http_URI_EncodedString_new(v_r_445_, v_ba_446_, v_valid_447_, v___validEncoding_448_);
lean_dec_ref(v_ba_446_);
lean_dec_ref(v_r_445_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg___lam__0(lean_object* v_es_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = lean_string_from_utf8_unchecked(v_es_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg(){
_start:
{
lean_object* v___f_454_; 
v___f_454_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instToString___redArg___closed__0));
return v___f_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___redArg___boxed(lean_object* v___dummy_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Std_Http_URI_EncodedString_instToString___redArg();
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString(lean_object* v_r_457_){
_start:
{
lean_object* v___f_458_; 
v___f_458_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instToString___redArg___closed__0));
return v___f_458_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___boxed(lean_object* v_r_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_Http_URI_EncodedString_instToString(v_r_459_);
lean_dec_ref(v_r_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(lean_object* v_len_461_, lean_object* v_rawBytes_462_, lean_object* v_a_463_){
_start:
{
lean_object* v_fst_464_; lean_object* v_snd_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_530_; 
v_fst_464_ = lean_ctor_get(v_a_463_, 0);
v_snd_465_ = lean_ctor_get(v_a_463_, 1);
v_isSharedCheck_530_ = !lean_is_exclusive(v_a_463_);
if (v_isSharedCheck_530_ == 0)
{
v___x_467_ = v_a_463_;
v_isShared_468_ = v_isSharedCheck_530_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_snd_465_);
lean_inc(v_fst_464_);
lean_dec(v_a_463_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_530_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
uint8_t v___x_469_; 
v___x_469_ = lean_nat_dec_lt(v_snd_465_, v_len_461_);
if (v___x_469_ == 0)
{
lean_object* v___x_471_; 
if (v_isShared_468_ == 0)
{
v___x_471_ = v___x_467_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_fst_464_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_snd_465_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
else
{
uint8_t v_percent_473_; uint8_t v___x_474_; uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___y_479_; 
v_percent_473_ = 37;
v___x_474_ = lean_byte_array_fget(v_rawBytes_462_, v_snd_465_);
v___x_475_ = lean_uint8_dec_eq(v___x_474_, v_percent_473_);
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_add(v_snd_465_, v___x_476_);
if (v___x_475_ == 0)
{
v___y_479_ = v___x_475_;
goto v___jp_478_;
}
else
{
uint8_t v___x_529_; 
v___x_529_ = lean_nat_dec_lt(v___x_477_, v_len_461_);
v___y_479_ = v___x_529_;
goto v___jp_478_;
}
v___jp_478_:
{
if (v___y_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_482_; 
lean_dec(v_snd_465_);
v___x_480_ = lean_byte_array_push(v_fst_464_, v___x_474_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 1, v___x_477_);
lean_ctor_set(v___x_467_, 0, v___x_480_);
v___x_482_ = v___x_467_;
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
v_a_463_ = v___x_482_;
goto _start;
}
}
else
{
uint8_t v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_byte_array_fget(v_rawBytes_462_, v___x_477_);
lean_dec(v___x_477_);
v___x_486_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_485_);
if (lean_obj_tag(v___x_486_) == 1)
{
lean_object* v_val_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v_val_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_val_487_);
lean_dec_ref_known(v___x_486_, 1);
v___x_488_ = lean_unsigned_to_nat(2u);
v___x_489_ = lean_nat_add(v_snd_465_, v___x_488_);
v___x_490_ = lean_nat_dec_lt(v___x_489_, v_len_461_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_494_; 
lean_dec(v_val_487_);
lean_dec(v_snd_465_);
v___x_491_ = lean_byte_array_push(v_fst_464_, v___x_474_);
v___x_492_ = lean_byte_array_push(v___x_491_, v___x_485_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 1, v___x_489_);
lean_ctor_set(v___x_467_, 0, v___x_492_);
v___x_494_ = v___x_467_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v___x_489_);
v___x_494_ = v_reuseFailAlloc_496_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
v_a_463_ = v___x_494_;
goto _start;
}
}
else
{
uint8_t v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_byte_array_fget(v_rawBytes_462_, v___x_489_);
lean_dec(v___x_489_);
v___x_498_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_497_);
if (lean_obj_tag(v___x_498_) == 1)
{
lean_object* v_val_499_; uint8_t v___x_500_; uint8_t v___x_501_; uint8_t v___x_502_; uint8_t v___x_503_; uint8_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_509_; 
v_val_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_val_499_);
lean_dec_ref_known(v___x_498_, 1);
v___x_500_ = 4;
v___x_501_ = lean_unbox(v_val_487_);
lean_dec(v_val_487_);
v___x_502_ = lean_uint8_shift_left(v___x_501_, v___x_500_);
v___x_503_ = lean_unbox(v_val_499_);
lean_dec(v_val_499_);
v___x_504_ = lean_uint8_add(v___x_502_, v___x_503_);
v___x_505_ = lean_byte_array_push(v_fst_464_, v___x_504_);
v___x_506_ = lean_unsigned_to_nat(3u);
v___x_507_ = lean_nat_add(v_snd_465_, v___x_506_);
lean_dec(v_snd_465_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 1, v___x_507_);
lean_ctor_set(v___x_467_, 0, v___x_505_);
v___x_509_ = v___x_467_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_507_);
v___x_509_ = v_reuseFailAlloc_511_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
v_a_463_ = v___x_509_;
goto _start;
}
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
lean_dec(v___x_498_);
lean_dec(v_val_487_);
v___x_512_ = lean_byte_array_push(v_fst_464_, v___x_474_);
v___x_513_ = lean_byte_array_push(v___x_512_, v___x_485_);
v___x_514_ = lean_byte_array_push(v___x_513_, v___x_497_);
v___x_515_ = lean_unsigned_to_nat(3u);
v___x_516_ = lean_nat_add(v_snd_465_, v___x_515_);
lean_dec(v_snd_465_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 1, v___x_516_);
lean_ctor_set(v___x_467_, 0, v___x_514_);
v___x_518_ = v___x_467_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v___x_516_);
v___x_518_ = v_reuseFailAlloc_520_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
v_a_463_ = v___x_518_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec(v___x_486_);
v___x_521_ = lean_byte_array_push(v_fst_464_, v___x_474_);
v___x_522_ = lean_byte_array_push(v___x_521_, v___x_485_);
v___x_523_ = lean_unsigned_to_nat(2u);
v___x_524_ = lean_nat_add(v_snd_465_, v___x_523_);
lean_dec(v_snd_465_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 1, v___x_524_);
lean_ctor_set(v___x_467_, 0, v___x_522_);
v___x_526_ = v___x_467_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___x_524_);
v___x_526_ = v_reuseFailAlloc_528_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
v_a_463_ = v___x_526_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg___boxed(lean_object* v_len_531_, lean_object* v_rawBytes_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_531_, v_rawBytes_532_, v_a_533_);
lean_dec_ref(v_rawBytes_532_);
lean_dec(v_len_531_);
return v_res_534_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0(void){
_start:
{
lean_object* v_i_535_; lean_object* v_decoded_536_; lean_object* v___x_537_; 
v_i_535_ = lean_unsigned_to_nat(0u);
v_decoded_536_ = l_ByteArray_empty;
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v_decoded_536_);
lean_ctor_set(v___x_537_, 1, v_i_535_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg(lean_object* v_es_538_){
_start:
{
lean_object* v_len_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v_fst_542_; uint8_t v___x_543_; 
v_len_539_ = lean_byte_array_size(v_es_538_);
v___x_540_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_541_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_539_, v_es_538_, v___x_540_);
v_fst_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_fst_542_);
lean_dec_ref(v___x_541_);
v___x_543_ = lean_string_validate_utf8(v_fst_542_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; 
lean_dec(v_fst_542_);
v___x_544_ = lean_box(0);
return v___x_544_;
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_string_from_utf8_unchecked(v_fst_542_);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg___boxed(lean_object* v_es_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_547_);
lean_dec_ref(v_es_547_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode(lean_object* v_r_549_, lean_object* v_es_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___boxed(lean_object* v_r_552_, lean_object* v_es_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Std_Http_URI_EncodedString_decode(v_r_552_, v_es_553_);
lean_dec_ref(v_es_553_);
lean_dec_ref(v_r_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(lean_object* v_len_555_, lean_object* v_rawBytes_556_, lean_object* v_inst_557_, lean_object* v_a_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___redArg(v_len_555_, v_rawBytes_556_, v_a_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0___boxed(lean_object* v_len_560_, lean_object* v_rawBytes_561_, lean_object* v_inst_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedString_decode_spec__0(v_len_560_, v_rawBytes_561_, v_inst_562_, v_a_563_);
lean_dec_ref(v_rawBytes_561_);
lean_dec(v_len_560_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0(lean_object* v_es_565_, lean_object* v_n_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_string_from_utf8_unchecked(v_es_565_);
v___x_568_ = l_String_quote(v___x_567_);
v___x_569_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0___boxed(lean_object* v_es_570_, lean_object* v_n_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0(v_es_570_, v_n_571_);
lean_dec(v_n_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg(){
_start:
{
lean_object* v___f_575_; 
v___f_575_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___boxed(lean_object* v___dummy_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Std_Http_URI_EncodedString_instRepr___redArg();
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr(lean_object* v_r_578_){
_start:
{
lean_object* v___f_579_; 
v___f_579_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___boxed(lean_object* v_r_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_Http_URI_EncodedString_instRepr(v_r_580_);
lean_dec_ref(v_r_580_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___redArg(){
_start:
{
lean_object* v___f_584_; 
v___f_584_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_584_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___redArg___boxed(lean_object* v___dummy_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Std_Http_URI_EncodedString_instBEq___redArg();
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq(lean_object* v_r_587_){
_start:
{
lean_object* v___f_588_; 
v___f_588_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_588_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___boxed(lean_object* v_r_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_Http_URI_EncodedString_instBEq(v_r_589_);
lean_dec_ref(v_r_589_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___redArg(){
_start:
{
lean_object* v___f_593_; 
v___f_593_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___redArg___boxed(lean_object* v___dummy_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_Http_URI_EncodedString_instHashable___redArg();
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable(lean_object* v_r_596_){
_start:
{
lean_object* v___f_597_; 
v___f_597_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___boxed(lean_object* v_r_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Std_Http_URI_EncodedString_instHashable(v_r_598_);
lean_dec_ref(v_r_598_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___redArg(){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_ByteArray_empty;
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___redArg___boxed(lean_object* v___dummy_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Std_Http_URI_EncodedQueryString_empty___redArg();
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty(lean_object* v_r_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_ByteArray_empty;
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___boxed(lean_object* v_r_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_Http_URI_EncodedQueryString_empty(v_r_606_);
lean_dec_ref(v_r_606_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___redArg(){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_ByteArray_empty;
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___redArg___boxed(lean_object* v___dummy_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_Http_URI_EncodedQueryString_instInhabited___redArg();
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited(lean_object* v_r_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_ByteArray_empty;
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___boxed(lean_object* v_r_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Std_Http_URI_EncodedQueryString_instInhabited(v_r_614_);
lean_dec_ref(v_r_614_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(lean_object* v_s_616_, uint8_t v_c_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_byte_array_push(v_s_616_, v_c_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg___boxed(lean_object* v_s_619_, lean_object* v_c_620_){
_start:
{
uint8_t v_c_boxed_621_; lean_object* v_res_622_; 
v_c_boxed_621_ = lean_unbox(v_c_620_);
v_res_622_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(v_s_619_, v_c_boxed_621_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(lean_object* v_r_623_, lean_object* v_s_624_, uint8_t v_c_625_, lean_object* v_h_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = lean_byte_array_push(v_s_624_, v_c_625_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___boxed(lean_object* v_r_628_, lean_object* v_s_629_, lean_object* v_c_630_, lean_object* v_h_631_){
_start:
{
uint8_t v_c_boxed_632_; lean_object* v_res_633_; 
v_c_boxed_632_ = lean_unbox(v_c_630_);
v_res_633_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(v_r_628_, v_s_629_, v_c_boxed_632_, v_h_631_);
lean_dec_ref(v_r_628_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(lean_object* v_ba_634_, lean_object* v_r_635_){
_start:
{
uint8_t v___x_636_; 
lean_inc_ref(v_ba_634_);
v___x_636_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_635_, v_ba_634_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
lean_dec_ref(v_ba_634_);
v___x_637_ = lean_box(0);
return v___x_637_;
}
else
{
uint8_t v___x_638_; 
v___x_638_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_634_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
lean_dec_ref(v_ba_634_);
v___x_639_ = lean_box(0);
return v___x_639_;
}
else
{
lean_object* v___x_640_; 
v___x_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_640_, 0, v_ba_634_);
return v___x_640_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_641_){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = l_ByteArray_empty;
v___x_643_ = lean_panic_fn_borrowed(v___x_642_, v_msg_641_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(lean_object* v_r_644_, lean_object* v_msg_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v_msg_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_647_, lean_object* v_msg_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(v_r_647_, v_msg_648_);
lean_dec_ref(v_r_647_);
return v_res_649_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_652_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1));
v___x_653_ = lean_unsigned_to_nat(12u);
v___x_654_ = lean_unsigned_to_nat(438u);
v___x_655_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0));
v___x_656_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_657_ = l_mkPanicMessageWithDecl(v___x_656_, v___x_655_, v___x_654_, v___x_653_, v___x_652_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(lean_object* v_ba_658_, lean_object* v_r_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_658_, v_r_659_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_obj_once(&l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2, &l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2_once, _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2);
v___x_662_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v___x_661_);
return v___x_662_;
}
else
{
lean_object* v_val_663_; 
v_val_663_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_val_663_);
lean_dec_ref_known(v___x_660_, 1);
return v_val_663_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f(lean_object* v_s_664_, lean_object* v_r_665_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_string_to_utf8(v_s_664_);
v___x_667_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v___x_666_, v_r_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f___boxed(lean_object* v_s_668_, lean_object* v_r_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_668_, v_r_669_);
lean_dec_ref(v_s_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21(lean_object* v_s_671_, lean_object* v_r_672_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_string_to_utf8(v_s_671_);
v___x_674_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v___x_673_, v_r_672_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21___boxed(lean_object* v_s_675_, lean_object* v_r_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_Http_URI_EncodedQueryString_ofString_x21(v_s_675_, v_r_676_);
lean_dec_ref(v_s_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg(lean_object* v_ba_678_){
_start:
{
lean_inc_ref(v_ba_678_);
return v_ba_678_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg___boxed(lean_object* v_ba_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Std_Http_URI_EncodedQueryString_new___redArg(v_ba_679_);
lean_dec_ref(v_ba_679_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new(lean_object* v_r_681_, lean_object* v_ba_682_, lean_object* v_valid_683_, lean_object* v___validEncoding_684_){
_start:
{
lean_inc_ref(v_ba_682_);
return v_ba_682_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___boxed(lean_object* v_r_685_, lean_object* v_ba_686_, lean_object* v_valid_687_, lean_object* v___validEncoding_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Std_Http_URI_EncodedQueryString_new(v_r_685_, v_ba_686_, v_valid_687_, v___validEncoding_688_);
lean_dec_ref(v_ba_686_);
lean_dec_ref(v_r_685_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(uint8_t v_b_690_, lean_object* v_s_691_){
_start:
{
uint8_t v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; uint8_t v___x_695_; uint8_t v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; uint8_t v___x_699_; uint8_t v___x_700_; lean_object* v_ba_701_; 
v___x_692_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__0, &l_Std_Http_URI_isEncodedChar___closed__0_once, _init_l_Std_Http_URI_isEncodedChar___closed__0);
v___x_693_ = lean_byte_array_push(v_s_691_, v___x_692_);
v___x_694_ = 4;
v___x_695_ = lean_uint8_shift_right(v_b_690_, v___x_694_);
v___x_696_ = l_Std_Http_URI_hexDigit(v___x_695_);
v___x_697_ = lean_byte_array_push(v___x_693_, v___x_696_);
v___x_698_ = 15;
v___x_699_ = lean_uint8_land(v_b_690_, v___x_698_);
v___x_700_ = l_Std_Http_URI_hexDigit(v___x_699_);
v_ba_701_ = lean_byte_array_push(v___x_697_, v___x_700_);
return v_ba_701_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg___boxed(lean_object* v_b_702_, lean_object* v_s_703_){
_start:
{
uint8_t v_b_boxed_704_; lean_object* v_res_705_; 
v_b_boxed_704_ = lean_unbox(v_b_702_);
v_res_705_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_boxed_704_, v_s_703_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(lean_object* v_r_706_, uint8_t v_b_707_, lean_object* v_s_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_707_, v_s_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___boxed(lean_object* v_r_710_, lean_object* v_b_711_, lean_object* v_s_712_){
_start:
{
uint8_t v_b_boxed_713_; lean_object* v_res_714_; 
v_b_boxed_713_ = lean_unbox(v_b_711_);
v_res_714_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(v_r_710_, v_b_boxed_713_, v_s_712_);
lean_dec_ref(v_r_710_);
return v_res_714_;
}
}
static uint8_t _init_l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0(void){
_start:
{
uint32_t v___x_715_; uint8_t v___x_716_; 
v___x_715_ = 32;
v___x_716_ = lean_uint32_to_uint8(v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(lean_object* v_r_717_, lean_object* v_as_718_, size_t v_i_719_, size_t v_stop_720_, lean_object* v_b_721_){
_start:
{
lean_object* v___y_723_; uint8_t v___x_727_; 
v___x_727_ = lean_usize_dec_eq(v_i_719_, v_stop_720_);
if (v___x_727_ == 0)
{
uint8_t v___x_728_; uint8_t v___y_730_; uint8_t v___x_737_; uint8_t v___x_738_; 
v___x_728_ = lean_byte_array_uget(v_as_718_, v_i_719_);
v___x_737_ = 128;
v___x_738_ = lean_uint8_dec_lt(v___x_728_, v___x_737_);
if (v___x_738_ == 0)
{
v___y_730_ = v___x_738_;
goto v___jp_729_;
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_739_ = lean_box(v___x_728_);
lean_inc_ref(v_r_717_);
v___x_740_ = lean_apply_1(v_r_717_, v___x_739_);
v___x_741_ = lean_unbox(v___x_740_);
v___y_730_ = v___x_741_;
goto v___jp_729_;
}
v___jp_729_:
{
if (v___y_730_ == 0)
{
uint8_t v___x_731_; uint8_t v___x_732_; 
v___x_731_ = lean_uint8_once(&l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0, &l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0_once, _init_l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0);
v___x_732_ = lean_uint8_dec_eq(v___x_728_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
v___x_733_ = l___private_Std_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v___x_728_, v_b_721_);
v___y_723_ = v___x_733_;
goto v___jp_722_;
}
else
{
uint8_t v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_735_ = lean_byte_array_push(v_b_721_, v___x_734_);
v___y_723_ = v___x_735_;
goto v___jp_722_;
}
}
else
{
lean_object* v___x_736_; 
v___x_736_ = lean_byte_array_push(v_b_721_, v___x_728_);
v___y_723_ = v___x_736_;
goto v___jp_722_;
}
}
}
else
{
lean_dec_ref(v_r_717_);
return v_b_721_;
}
v___jp_722_:
{
size_t v___x_724_; size_t v___x_725_; 
v___x_724_ = ((size_t)1ULL);
v___x_725_ = lean_usize_add(v_i_719_, v___x_724_);
v_i_719_ = v___x_725_;
v_b_721_ = v___y_723_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___boxed(lean_object* v_r_742_, lean_object* v_as_743_, lean_object* v_i_744_, lean_object* v_stop_745_, lean_object* v_b_746_){
_start:
{
size_t v_i_boxed_747_; size_t v_stop_boxed_748_; lean_object* v_res_749_; 
v_i_boxed_747_ = lean_unbox_usize(v_i_744_);
lean_dec(v_i_744_);
v_stop_boxed_748_ = lean_unbox_usize(v_stop_745_);
lean_dec(v_stop_745_);
v_res_749_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_742_, v_as_743_, v_i_boxed_747_, v_stop_boxed_748_, v_b_746_);
lean_dec_ref(v_as_743_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode(lean_object* v_s_750_, lean_object* v_r_751_){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_752_ = l_ByteArray_empty;
v___x_753_ = lean_string_to_utf8(v_s_750_);
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = lean_byte_array_size(v___x_753_);
v___x_756_ = lean_nat_dec_lt(v___x_754_, v___x_755_);
if (v___x_756_ == 0)
{
lean_dec_ref(v___x_753_);
lean_dec_ref(v_r_751_);
return v___x_752_;
}
else
{
uint8_t v___x_757_; 
v___x_757_ = lean_nat_dec_le(v___x_755_, v___x_755_);
if (v___x_757_ == 0)
{
if (v___x_756_ == 0)
{
lean_dec_ref(v___x_753_);
lean_dec_ref(v_r_751_);
return v___x_752_;
}
else
{
size_t v___x_758_; size_t v___x_759_; lean_object* v___x_760_; 
v___x_758_ = ((size_t)0ULL);
v___x_759_ = lean_usize_of_nat(v___x_755_);
v___x_760_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_751_, v___x_753_, v___x_758_, v___x_759_, v___x_752_);
lean_dec_ref(v___x_753_);
return v___x_760_;
}
}
else
{
size_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; 
v___x_761_ = ((size_t)0ULL);
v___x_762_ = lean_usize_of_nat(v___x_755_);
v___x_763_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_751_, v___x_753_, v___x_761_, v___x_762_, v___x_752_);
lean_dec_ref(v___x_753_);
return v___x_763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode___boxed(lean_object* v_s_764_, lean_object* v_r_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_764_, v_r_765_);
lean_dec_ref(v_s_764_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___redArg(lean_object* v_es_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = lean_string_from_utf8_unchecked(v_es_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString(lean_object* v_r_769_, lean_object* v_es_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = lean_string_from_utf8_unchecked(v_es_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___boxed(lean_object* v_r_772_, lean_object* v_es_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_Http_URI_EncodedQueryString_toString(v_r_772_, v_es_773_);
lean_dec_ref(v_r_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(lean_object* v_len_775_, lean_object* v_rawBytes_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_fst_778_; lean_object* v_snd_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_854_; 
v_fst_778_ = lean_ctor_get(v_a_777_, 0);
v_snd_779_ = lean_ctor_get(v_a_777_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v_a_777_);
if (v_isSharedCheck_854_ == 0)
{
v___x_781_ = v_a_777_;
v_isShared_782_ = v_isSharedCheck_854_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_snd_779_);
lean_inc(v_fst_778_);
lean_dec(v_a_777_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_854_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
uint8_t v___x_783_; 
v___x_783_ = lean_nat_dec_lt(v_snd_779_, v_len_775_);
if (v___x_783_ == 0)
{
lean_object* v___x_785_; 
if (v_isShared_782_ == 0)
{
v___x_785_ = v___x_781_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_fst_778_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_snd_779_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
else
{
uint8_t v_plus_787_; uint8_t v___x_788_; uint8_t v___x_789_; 
v_plus_787_ = 43;
v___x_788_ = lean_byte_array_fget(v_rawBytes_776_, v_snd_779_);
v___x_789_ = lean_uint8_dec_eq(v___x_788_, v_plus_787_);
if (v___x_789_ == 0)
{
uint8_t v_percent_790_; uint8_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___y_795_; 
v_percent_790_ = 37;
v___x_791_ = lean_uint8_dec_eq(v___x_788_, v_percent_790_);
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = lean_nat_add(v_snd_779_, v___x_792_);
if (v___x_791_ == 0)
{
v___y_795_ = v___x_791_;
goto v___jp_794_;
}
else
{
uint8_t v___x_845_; 
v___x_845_ = lean_nat_dec_lt(v___x_793_, v_len_775_);
v___y_795_ = v___x_845_;
goto v___jp_794_;
}
v___jp_794_:
{
if (v___y_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_798_; 
lean_dec(v_snd_779_);
v___x_796_ = lean_byte_array_push(v_fst_778_, v___x_788_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v___x_793_);
lean_ctor_set(v___x_781_, 0, v___x_796_);
v___x_798_ = v___x_781_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_793_);
v___x_798_ = v_reuseFailAlloc_800_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
v_a_777_ = v___x_798_;
goto _start;
}
}
else
{
uint8_t v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_byte_array_fget(v_rawBytes_776_, v___x_793_);
lean_dec(v___x_793_);
v___x_802_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_801_);
if (lean_obj_tag(v___x_802_) == 1)
{
lean_object* v_val_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_val_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_val_803_);
lean_dec_ref_known(v___x_802_, 1);
v___x_804_ = lean_unsigned_to_nat(2u);
v___x_805_ = lean_nat_add(v_snd_779_, v___x_804_);
v___x_806_ = lean_nat_dec_lt(v___x_805_, v_len_775_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
lean_dec(v_val_803_);
lean_dec(v_snd_779_);
v___x_807_ = lean_byte_array_push(v_fst_778_, v___x_788_);
v___x_808_ = lean_byte_array_push(v___x_807_, v___x_801_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v___x_805_);
lean_ctor_set(v___x_781_, 0, v___x_808_);
v___x_810_ = v___x_781_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_805_);
v___x_810_ = v_reuseFailAlloc_812_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
v_a_777_ = v___x_810_;
goto _start;
}
}
else
{
uint8_t v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_byte_array_fget(v_rawBytes_776_, v___x_805_);
lean_dec(v___x_805_);
v___x_814_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v___x_813_);
if (lean_obj_tag(v___x_814_) == 1)
{
lean_object* v_val_815_; uint8_t v___x_816_; uint8_t v___x_817_; uint8_t v___x_818_; uint8_t v___x_819_; uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
v_val_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_val_815_);
lean_dec_ref_known(v___x_814_, 1);
v___x_816_ = 4;
v___x_817_ = lean_unbox(v_val_803_);
lean_dec(v_val_803_);
v___x_818_ = lean_uint8_shift_left(v___x_817_, v___x_816_);
v___x_819_ = lean_unbox(v_val_815_);
lean_dec(v_val_815_);
v___x_820_ = lean_uint8_add(v___x_818_, v___x_819_);
v___x_821_ = lean_byte_array_push(v_fst_778_, v___x_820_);
v___x_822_ = lean_unsigned_to_nat(3u);
v___x_823_ = lean_nat_add(v_snd_779_, v___x_822_);
lean_dec(v_snd_779_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v___x_823_);
lean_ctor_set(v___x_781_, 0, v___x_821_);
v___x_825_ = v___x_781_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_821_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v___x_823_);
v___x_825_ = v_reuseFailAlloc_827_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
v_a_777_ = v___x_825_;
goto _start;
}
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
lean_dec(v___x_814_);
lean_dec(v_val_803_);
v___x_828_ = lean_byte_array_push(v_fst_778_, v___x_788_);
v___x_829_ = lean_byte_array_push(v___x_828_, v___x_801_);
v___x_830_ = lean_byte_array_push(v___x_829_, v___x_813_);
v___x_831_ = lean_unsigned_to_nat(3u);
v___x_832_ = lean_nat_add(v_snd_779_, v___x_831_);
lean_dec(v_snd_779_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v___x_832_);
lean_ctor_set(v___x_781_, 0, v___x_830_);
v___x_834_ = v___x_781_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v___x_832_);
v___x_834_ = v_reuseFailAlloc_836_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
v_a_777_ = v___x_834_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
lean_dec(v___x_802_);
v___x_837_ = lean_byte_array_push(v_fst_778_, v___x_788_);
v___x_838_ = lean_byte_array_push(v___x_837_, v___x_801_);
v___x_839_ = lean_unsigned_to_nat(2u);
v___x_840_ = lean_nat_add(v_snd_779_, v___x_839_);
lean_dec(v_snd_779_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v___x_840_);
lean_ctor_set(v___x_781_, 0, v___x_838_);
v___x_842_ = v___x_781_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_840_);
v___x_842_ = v_reuseFailAlloc_844_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
v_a_777_ = v___x_842_;
goto _start;
}
}
}
}
}
else
{
uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_846_ = 32;
v___x_847_ = lean_byte_array_push(v_fst_778_, v___x_846_);
v___x_848_ = lean_unsigned_to_nat(1u);
v___x_849_ = lean_nat_add(v_snd_779_, v___x_848_);
lean_dec(v_snd_779_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v___x_849_);
lean_ctor_set(v___x_781_, 0, v___x_847_);
v___x_851_ = v___x_781_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_849_);
v___x_851_ = v_reuseFailAlloc_853_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
v_a_777_ = v___x_851_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg___boxed(lean_object* v_len_855_, lean_object* v_rawBytes_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_855_, v_rawBytes_856_, v_a_857_);
lean_dec_ref(v_rawBytes_856_);
lean_dec(v_len_855_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg(lean_object* v_es_859_){
_start:
{
lean_object* v_len_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_fst_863_; uint8_t v___x_864_; 
v_len_860_ = lean_byte_array_size(v_es_859_);
v___x_861_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_862_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_860_, v_es_859_, v___x_861_);
v_fst_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_fst_863_);
lean_dec_ref(v___x_862_);
v___x_864_ = lean_string_validate_utf8(v_fst_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; 
lean_dec(v_fst_863_);
v___x_865_ = lean_box(0);
return v___x_865_;
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_string_from_utf8_unchecked(v_fst_863_);
v___x_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
return v___x_867_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg___boxed(lean_object* v_es_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_868_);
lean_dec_ref(v_es_868_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode(lean_object* v_r_870_, lean_object* v_es_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___boxed(lean_object* v_r_873_, lean_object* v_es_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Std_Http_URI_EncodedQueryString_decode(v_r_873_, v_es_874_);
lean_dec_ref(v_es_874_);
lean_dec_ref(v_r_873_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(lean_object* v_len_876_, lean_object* v_rawBytes_877_, lean_object* v_inst_878_, lean_object* v_a_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___redArg(v_len_876_, v_rawBytes_877_, v_a_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___boxed(lean_object* v_len_881_, lean_object* v_rawBytes_882_, lean_object* v_inst_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(v_len_881_, v_rawBytes_882_, v_inst_883_, v_a_884_);
lean_dec_ref(v_rawBytes_882_);
lean_dec(v_len_881_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringEncodedQueryString(lean_object* v_r_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_closure((void*)(l_Std_Http_URI_EncodedQueryString_toString___boxed), 2, 1);
lean_closure_set(v___x_887_, 0, v_r_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_889_; 
v___f_889_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_889_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___redArg___boxed(lean_object* v___dummy_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Std_Http_URI_instReprEncodedQueryString___redArg();
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString(lean_object* v_r_892_){
_start:
{
lean_object* v___f_893_; 
v___f_893_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___redArg___closed__0));
return v___f_893_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___boxed(lean_object* v_r_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_Http_URI_instReprEncodedQueryString(v_r_894_);
lean_dec_ref(v_r_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_897_; 
v___f_897_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_897_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___redArg___boxed(lean_object* v___dummy_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Std_Http_URI_instBEqEncodedQueryString___redArg();
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString(lean_object* v_r_900_){
_start:
{
lean_object* v___f_901_; 
v___f_901_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instBEq___redArg___closed__0));
return v___f_901_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___boxed(lean_object* v_r_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Std_Http_URI_instBEqEncodedQueryString(v_r_902_);
lean_dec_ref(v_r_902_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_905_; 
v___f_905_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_905_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___redArg___boxed(lean_object* v___dummy_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Std_Http_URI_instHashableEncodedQueryString___redArg();
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString(lean_object* v_r_908_){
_start:
{
lean_object* v___f_909_; 
v___f_909_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___redArg___closed__0));
return v___f_909_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___boxed(lean_object* v_r_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Std_Http_URI_instHashableEncodedQueryString(v_r_910_);
lean_dec_ref(v_r_910_);
return v_res_911_;
}
}
static uint64_t _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_918_; uint64_t v___x_919_; 
v___x_918_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__0));
v___x_919_ = lean_byte_array_hash(v___x_918_);
return v___x_919_;
}
}
static lean_object* _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__2));
v___x_927_ = lean_byte_array_size(v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT uint64_t l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0(lean_object* v_x_928_){
_start:
{
if (lean_obj_tag(v_x_928_) == 0)
{
uint64_t v___x_929_; 
v___x_929_ = lean_uint64_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1, &l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__1);
return v___x_929_;
}
else
{
lean_object* v_val_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; lean_object* v___x_936_; uint64_t v___x_937_; 
v_val_930_ = lean_ctor_get(v_x_928_, 0);
v___x_931_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__2));
v___x_932_ = lean_unsigned_to_nat(0u);
v___x_933_ = lean_obj_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3, &l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___closed__3);
v___x_934_ = lean_byte_array_size(v_val_930_);
v___x_935_ = 0;
v___x_936_ = lean_byte_array_copy_slice(v_val_930_, v___x_932_, v___x_931_, v___x_933_, v___x_934_, v___x_935_);
v___x_937_ = lean_byte_array_hash(v___x_936_);
lean_dec_ref(v___x_936_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0___boxed(lean_object* v_x_938_){
_start:
{
uint64_t v_res_939_; lean_object* v_r_940_; 
v_res_939_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___lam__0(v_x_938_);
lean_dec(v_x_938_);
v_r_940_ = lean_box_uint64(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg(){
_start:
{
lean_object* v___f_943_; 
v___f_943_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___closed__0));
return v___f_943_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___boxed(lean_object* v___dummy_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg();
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString(lean_object* v_r_946_){
_start:
{
lean_object* v___f_947_; 
v___f_947_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___redArg___closed__0));
return v___f_947_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___boxed(lean_object* v_r_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_Http_URI_instHashableOptionEncodedQueryString(v_r_948_);
lean_dec_ref(v_r_948_);
return v_res_949_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0(void){
_start:
{
uint32_t v___x_950_; uint8_t v___x_951_; 
v___x_950_ = 45;
v___x_951_ = lean_uint32_to_uint8(v___x_950_);
return v___x_951_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1(void){
_start:
{
uint32_t v___x_952_; uint8_t v___x_953_; 
v___x_952_ = 46;
v___x_953_ = lean_uint32_to_uint8(v___x_952_);
return v___x_953_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2(void){
_start:
{
uint32_t v___x_954_; uint8_t v___x_955_; 
v___x_954_ = 95;
v___x_955_ = lean_uint32_to_uint8(v___x_954_);
return v___x_955_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3(void){
_start:
{
uint32_t v___x_956_; uint8_t v___x_957_; 
v___x_956_ = 126;
v___x_957_ = lean_uint32_to_uint8(v___x_956_);
return v___x_957_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4(void){
_start:
{
uint32_t v___x_958_; uint8_t v___x_959_; 
v___x_958_ = 33;
v___x_959_ = lean_uint32_to_uint8(v___x_958_);
return v___x_959_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5(void){
_start:
{
uint32_t v___x_960_; uint8_t v___x_961_; 
v___x_960_ = 36;
v___x_961_ = lean_uint32_to_uint8(v___x_960_);
return v___x_961_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6(void){
_start:
{
uint32_t v___x_962_; uint8_t v___x_963_; 
v___x_962_ = 38;
v___x_963_ = lean_uint32_to_uint8(v___x_962_);
return v___x_963_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7(void){
_start:
{
uint32_t v___x_964_; uint8_t v___x_965_; 
v___x_964_ = 39;
v___x_965_ = lean_uint32_to_uint8(v___x_964_);
return v___x_965_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8(void){
_start:
{
uint32_t v___x_966_; uint8_t v___x_967_; 
v___x_966_ = 40;
v___x_967_ = lean_uint32_to_uint8(v___x_966_);
return v___x_967_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9(void){
_start:
{
uint32_t v___x_968_; uint8_t v___x_969_; 
v___x_968_ = 41;
v___x_969_ = lean_uint32_to_uint8(v___x_968_);
return v___x_969_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10(void){
_start:
{
uint32_t v___x_970_; uint8_t v___x_971_; 
v___x_970_ = 42;
v___x_971_ = lean_uint32_to_uint8(v___x_970_);
return v___x_971_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11(void){
_start:
{
uint32_t v___x_972_; uint8_t v___x_973_; 
v___x_972_ = 44;
v___x_973_ = lean_uint32_to_uint8(v___x_972_);
return v___x_973_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12(void){
_start:
{
uint32_t v___x_974_; uint8_t v___x_975_; 
v___x_974_ = 59;
v___x_975_ = lean_uint32_to_uint8(v___x_974_);
return v___x_975_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13(void){
_start:
{
uint32_t v___x_976_; uint8_t v___x_977_; 
v___x_976_ = 61;
v___x_977_ = lean_uint32_to_uint8(v___x_976_);
return v___x_977_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14(void){
_start:
{
uint32_t v___x_978_; uint8_t v___x_979_; 
v___x_978_ = 58;
v___x_979_ = lean_uint32_to_uint8(v___x_978_);
return v___x_979_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15(void){
_start:
{
uint32_t v___x_980_; uint8_t v___x_981_; 
v___x_980_ = 64;
v___x_981_ = lean_uint32_to_uint8(v___x_980_);
return v___x_981_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16(void){
_start:
{
uint32_t v___x_982_; uint8_t v___x_983_; 
v___x_982_ = 90;
v___x_983_ = lean_uint32_to_uint8(v___x_982_);
return v___x_983_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17(void){
_start:
{
uint32_t v___x_984_; uint8_t v___x_985_; 
v___x_984_ = 122;
v___x_985_ = lean_uint32_to_uint8(v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0(uint8_t v___y_986_){
_start:
{
uint8_t v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1033_ = lean_uint8_dec_le(v___x_1032_, v___y_986_);
if (v___x_1033_ == 0)
{
goto v___jp_1027_;
}
else
{
uint8_t v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1035_ = lean_uint8_dec_le(v___y_986_, v___x_1034_);
if (v___x_1035_ == 0)
{
goto v___jp_1027_;
}
else
{
return v___x_1035_;
}
}
v___jp_987_:
{
uint8_t v___x_988_; uint8_t v___x_989_; 
v___x_988_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_989_ = lean_uint8_dec_eq(v___y_986_, v___x_988_);
if (v___x_989_ == 0)
{
uint8_t v___x_990_; uint8_t v___x_991_; 
v___x_990_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_991_ = lean_uint8_dec_eq(v___y_986_, v___x_990_);
if (v___x_991_ == 0)
{
uint8_t v___x_992_; uint8_t v___x_993_; 
v___x_992_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_993_ = lean_uint8_dec_eq(v___y_986_, v___x_992_);
if (v___x_993_ == 0)
{
uint8_t v___x_994_; uint8_t v___x_995_; 
v___x_994_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_995_ = lean_uint8_dec_eq(v___y_986_, v___x_994_);
if (v___x_995_ == 0)
{
uint8_t v___x_996_; uint8_t v___x_997_; 
v___x_996_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_997_ = lean_uint8_dec_eq(v___y_986_, v___x_996_);
if (v___x_997_ == 0)
{
uint8_t v___x_998_; uint8_t v___x_999_; 
v___x_998_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_999_ = lean_uint8_dec_eq(v___y_986_, v___x_998_);
if (v___x_999_ == 0)
{
uint8_t v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1001_ = lean_uint8_dec_eq(v___y_986_, v___x_1000_);
if (v___x_1001_ == 0)
{
uint8_t v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1003_ = lean_uint8_dec_eq(v___y_986_, v___x_1002_);
if (v___x_1003_ == 0)
{
uint8_t v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1005_ = lean_uint8_dec_eq(v___y_986_, v___x_1004_);
if (v___x_1005_ == 0)
{
uint8_t v___x_1006_; uint8_t v___x_1007_; 
v___x_1006_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1007_ = lean_uint8_dec_eq(v___y_986_, v___x_1006_);
if (v___x_1007_ == 0)
{
uint8_t v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1009_ = lean_uint8_dec_eq(v___y_986_, v___x_1008_);
if (v___x_1009_ == 0)
{
uint8_t v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1011_ = lean_uint8_dec_eq(v___y_986_, v___x_1010_);
if (v___x_1011_ == 0)
{
uint8_t v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1013_ = lean_uint8_dec_eq(v___y_986_, v___x_1012_);
if (v___x_1013_ == 0)
{
uint8_t v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1015_ = lean_uint8_dec_eq(v___y_986_, v___x_1014_);
if (v___x_1015_ == 0)
{
uint8_t v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1017_ = lean_uint8_dec_eq(v___y_986_, v___x_1016_);
if (v___x_1017_ == 0)
{
uint8_t v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1019_ = lean_uint8_dec_eq(v___y_986_, v___x_1018_);
if (v___x_1019_ == 0)
{
uint8_t v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1021_ = lean_uint8_dec_eq(v___y_986_, v___x_1020_);
return v___x_1021_;
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
v___jp_1022_:
{
uint8_t v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1024_ = lean_uint8_dec_le(v___x_1023_, v___y_986_);
if (v___x_1024_ == 0)
{
goto v___jp_987_;
}
else
{
uint8_t v___x_1025_; uint8_t v___x_1026_; 
v___x_1025_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1026_ = lean_uint8_dec_le(v___y_986_, v___x_1025_);
if (v___x_1026_ == 0)
{
goto v___jp_987_;
}
else
{
return v___x_1026_;
}
}
}
v___jp_1027_:
{
uint8_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1029_ = lean_uint8_dec_le(v___x_1028_, v___y_986_);
if (v___x_1029_ == 0)
{
goto v___jp_1022_;
}
else
{
uint8_t v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1031_ = lean_uint8_dec_le(v___y_986_, v___x_1030_);
if (v___x_1031_ == 0)
{
goto v___jp_1022_;
}
else
{
return v___x_1031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___lam__0___boxed(lean_object* v___y_1036_){
_start:
{
uint8_t v___y_347__boxed_1037_; uint8_t v_res_1038_; lean_object* v_r_1039_; 
v___y_347__boxed_1037_ = lean_unbox(v___y_1036_);
v_res_1038_ = l_Std_Http_URI_EncodedSegment_encode___lam__0(v___y_347__boxed_1037_);
v_r_1039_ = lean_box(v_res_1038_);
return v_r_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode(lean_object* v_s_1041_){
_start:
{
lean_object* v___f_1042_; lean_object* v___x_1043_; 
v___f_1042_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_1043_ = l_Std_Http_URI_EncodedString_encode(v___f_1042_, v_s_1041_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___boxed(lean_object* v_s_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Std_Http_URI_EncodedSegment_encode(v_s_1044_);
lean_dec_ref(v_s_1044_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object* v_ba_1046_){
_start:
{
lean_object* v___f_1047_; lean_object* v___x_1048_; 
v___f_1047_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_1048_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1047_, v_ba_1046_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x21(lean_object* v_ba_1049_){
_start:
{
lean_object* v___f_1050_; lean_object* v___x_1051_; 
v___f_1050_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_1051_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1050_, v_ba_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object* v_segment_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Std_Http_URI_EncodedString_decode___redArg(v_segment_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode___boxed(lean_object* v_segment_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Std_Http_URI_EncodedSegment_decode(v_segment_1054_);
lean_dec_ref(v_segment_1054_);
return v_res_1055_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0(void){
_start:
{
uint32_t v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = 47;
v___x_1057_ = lean_uint32_to_uint8(v___x_1056_);
return v___x_1057_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1(void){
_start:
{
uint32_t v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = 63;
v___x_1059_ = lean_uint32_to_uint8(v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedFragment_encode___lam__0(uint8_t v___y_1060_){
_start:
{
uint8_t v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1111_ = lean_uint8_dec_le(v___x_1110_, v___y_1060_);
if (v___x_1111_ == 0)
{
goto v___jp_1105_;
}
else
{
uint8_t v___x_1112_; uint8_t v___x_1113_; 
v___x_1112_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1113_ = lean_uint8_dec_le(v___y_1060_, v___x_1112_);
if (v___x_1113_ == 0)
{
goto v___jp_1105_;
}
else
{
return v___x_1113_;
}
}
v___jp_1061_:
{
uint8_t v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_1063_ = lean_uint8_dec_eq(v___y_1060_, v___x_1062_);
if (v___x_1063_ == 0)
{
uint8_t v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_1065_ = lean_uint8_dec_eq(v___y_1060_, v___x_1064_);
if (v___x_1065_ == 0)
{
uint8_t v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1067_ = lean_uint8_dec_eq(v___y_1060_, v___x_1066_);
if (v___x_1067_ == 0)
{
uint8_t v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_1069_ = lean_uint8_dec_eq(v___y_1060_, v___x_1068_);
if (v___x_1069_ == 0)
{
uint8_t v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1071_ = lean_uint8_dec_eq(v___y_1060_, v___x_1070_);
if (v___x_1071_ == 0)
{
uint8_t v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1073_ = lean_uint8_dec_eq(v___y_1060_, v___x_1072_);
if (v___x_1073_ == 0)
{
uint8_t v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1075_ = lean_uint8_dec_eq(v___y_1060_, v___x_1074_);
if (v___x_1075_ == 0)
{
uint8_t v___x_1076_; uint8_t v___x_1077_; 
v___x_1076_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1077_ = lean_uint8_dec_eq(v___y_1060_, v___x_1076_);
if (v___x_1077_ == 0)
{
uint8_t v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1079_ = lean_uint8_dec_eq(v___y_1060_, v___x_1078_);
if (v___x_1079_ == 0)
{
uint8_t v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1081_ = lean_uint8_dec_eq(v___y_1060_, v___x_1080_);
if (v___x_1081_ == 0)
{
uint8_t v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1083_ = lean_uint8_dec_eq(v___y_1060_, v___x_1082_);
if (v___x_1083_ == 0)
{
uint8_t v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1085_ = lean_uint8_dec_eq(v___y_1060_, v___x_1084_);
if (v___x_1085_ == 0)
{
uint8_t v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1087_ = lean_uint8_dec_eq(v___y_1060_, v___x_1086_);
if (v___x_1087_ == 0)
{
uint8_t v___x_1088_; uint8_t v___x_1089_; 
v___x_1088_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1089_ = lean_uint8_dec_eq(v___y_1060_, v___x_1088_);
if (v___x_1089_ == 0)
{
uint8_t v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1091_ = lean_uint8_dec_eq(v___y_1060_, v___x_1090_);
if (v___x_1091_ == 0)
{
uint8_t v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1093_ = lean_uint8_dec_eq(v___y_1060_, v___x_1092_);
if (v___x_1093_ == 0)
{
uint8_t v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1095_ = lean_uint8_dec_eq(v___y_1060_, v___x_1094_);
if (v___x_1095_ == 0)
{
uint8_t v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0);
v___x_1097_ = lean_uint8_dec_eq(v___y_1060_, v___x_1096_);
if (v___x_1097_ == 0)
{
uint8_t v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1);
v___x_1099_ = lean_uint8_dec_eq(v___y_1060_, v___x_1098_);
return v___x_1099_;
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
else
{
return v___x_1077_;
}
}
else
{
return v___x_1075_;
}
}
else
{
return v___x_1073_;
}
}
else
{
return v___x_1071_;
}
}
else
{
return v___x_1069_;
}
}
else
{
return v___x_1067_;
}
}
else
{
return v___x_1065_;
}
}
else
{
return v___x_1063_;
}
}
v___jp_1100_:
{
uint8_t v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1102_ = lean_uint8_dec_le(v___x_1101_, v___y_1060_);
if (v___x_1102_ == 0)
{
goto v___jp_1061_;
}
else
{
uint8_t v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1104_ = lean_uint8_dec_le(v___y_1060_, v___x_1103_);
if (v___x_1104_ == 0)
{
goto v___jp_1061_;
}
else
{
return v___x_1104_;
}
}
}
v___jp_1105_:
{
uint8_t v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1107_ = lean_uint8_dec_le(v___x_1106_, v___y_1060_);
if (v___x_1107_ == 0)
{
goto v___jp_1100_;
}
else
{
uint8_t v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1109_ = lean_uint8_dec_le(v___y_1060_, v___x_1108_);
if (v___x_1109_ == 0)
{
goto v___jp_1100_;
}
else
{
return v___x_1109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed(lean_object* v___y_1114_){
_start:
{
uint8_t v___y_343__boxed_1115_; uint8_t v_res_1116_; lean_object* v_r_1117_; 
v___y_343__boxed_1115_ = lean_unbox(v___y_1114_);
v_res_1116_ = l_Std_Http_URI_EncodedFragment_encode___lam__0(v___y_343__boxed_1115_);
v_r_1117_ = lean_box(v_res_1116_);
return v_r_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object* v_s_1119_){
_start:
{
lean_object* v___f_1120_; lean_object* v___x_1121_; 
v___f_1120_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1121_ = l_Std_Http_URI_EncodedString_encode(v___f_1120_, v_s_1119_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___boxed(lean_object* v_s_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Std_Http_URI_EncodedFragment_encode(v_s_1122_);
lean_dec_ref(v_s_1122_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object* v_ba_1124_){
_start:
{
lean_object* v___f_1125_; lean_object* v___x_1126_; 
v___f_1125_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1126_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1125_, v_ba_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x21(lean_object* v_ba_1127_){
_start:
{
lean_object* v___f_1128_; lean_object* v___x_1129_; 
v___f_1128_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1129_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1128_, v_ba_1127_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object* v_fragment_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Std_Http_URI_EncodedString_decode___redArg(v_fragment_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode___boxed(lean_object* v_fragment_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Std_Http_URI_EncodedFragment_decode(v_fragment_1132_);
lean_dec_ref(v_fragment_1132_);
return v_res_1133_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedUserInfo_encode___lam__0(uint8_t v___y_1134_){
_start:
{
uint8_t v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1179_ = lean_uint8_dec_le(v___x_1178_, v___y_1134_);
if (v___x_1179_ == 0)
{
goto v___jp_1173_;
}
else
{
uint8_t v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1181_ = lean_uint8_dec_le(v___y_1134_, v___x_1180_);
if (v___x_1181_ == 0)
{
goto v___jp_1173_;
}
else
{
return v___x_1181_;
}
}
v___jp_1135_:
{
uint8_t v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_1137_ = lean_uint8_dec_eq(v___y_1134_, v___x_1136_);
if (v___x_1137_ == 0)
{
uint8_t v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_1139_ = lean_uint8_dec_eq(v___y_1134_, v___x_1138_);
if (v___x_1139_ == 0)
{
uint8_t v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1141_ = lean_uint8_dec_eq(v___y_1134_, v___x_1140_);
if (v___x_1141_ == 0)
{
uint8_t v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_1143_ = lean_uint8_dec_eq(v___y_1134_, v___x_1142_);
if (v___x_1143_ == 0)
{
uint8_t v___x_1144_; uint8_t v___x_1145_; 
v___x_1144_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1145_ = lean_uint8_dec_eq(v___y_1134_, v___x_1144_);
if (v___x_1145_ == 0)
{
uint8_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1147_ = lean_uint8_dec_eq(v___y_1134_, v___x_1146_);
if (v___x_1147_ == 0)
{
uint8_t v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1149_ = lean_uint8_dec_eq(v___y_1134_, v___x_1148_);
if (v___x_1149_ == 0)
{
uint8_t v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1151_ = lean_uint8_dec_eq(v___y_1134_, v___x_1150_);
if (v___x_1151_ == 0)
{
uint8_t v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1153_ = lean_uint8_dec_eq(v___y_1134_, v___x_1152_);
if (v___x_1153_ == 0)
{
uint8_t v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1155_ = lean_uint8_dec_eq(v___y_1134_, v___x_1154_);
if (v___x_1155_ == 0)
{
uint8_t v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1157_ = lean_uint8_dec_eq(v___y_1134_, v___x_1156_);
if (v___x_1157_ == 0)
{
uint8_t v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1159_ = lean_uint8_dec_eq(v___y_1134_, v___x_1158_);
if (v___x_1159_ == 0)
{
uint8_t v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1161_ = lean_uint8_dec_eq(v___y_1134_, v___x_1160_);
if (v___x_1161_ == 0)
{
uint8_t v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1163_ = lean_uint8_dec_eq(v___y_1134_, v___x_1162_);
if (v___x_1163_ == 0)
{
uint8_t v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1165_ = lean_uint8_dec_eq(v___y_1134_, v___x_1164_);
if (v___x_1165_ == 0)
{
uint8_t v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1167_ = lean_uint8_dec_eq(v___y_1134_, v___x_1166_);
return v___x_1167_;
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
else
{
return v___x_1139_;
}
}
else
{
return v___x_1137_;
}
}
v___jp_1168_:
{
uint8_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1170_ = lean_uint8_dec_le(v___x_1169_, v___y_1134_);
if (v___x_1170_ == 0)
{
goto v___jp_1135_;
}
else
{
uint8_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1172_ = lean_uint8_dec_le(v___y_1134_, v___x_1171_);
if (v___x_1172_ == 0)
{
goto v___jp_1135_;
}
else
{
return v___x_1172_;
}
}
}
v___jp_1173_:
{
uint8_t v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1175_ = lean_uint8_dec_le(v___x_1174_, v___y_1134_);
if (v___x_1175_ == 0)
{
goto v___jp_1168_;
}
else
{
uint8_t v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1177_ = lean_uint8_dec_le(v___y_1134_, v___x_1176_);
if (v___x_1177_ == 0)
{
goto v___jp_1168_;
}
else
{
return v___x_1177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed(lean_object* v___y_1182_){
_start:
{
uint8_t v___y_297__boxed_1183_; uint8_t v_res_1184_; lean_object* v_r_1185_; 
v___y_297__boxed_1183_ = lean_unbox(v___y_1182_);
v_res_1184_ = l_Std_Http_URI_EncodedUserInfo_encode___lam__0(v___y_297__boxed_1183_);
v_r_1185_ = lean_box(v_res_1184_);
return v_r_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object* v_s_1187_){
_start:
{
lean_object* v___f_1188_; lean_object* v___x_1189_; 
v___f_1188_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1189_ = l_Std_Http_URI_EncodedString_encode(v___f_1188_, v_s_1187_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___boxed(lean_object* v_s_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Std_Http_URI_EncodedUserInfo_encode(v_s_1190_);
lean_dec_ref(v_s_1190_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object* v_ba_1192_){
_start:
{
lean_object* v___f_1193_; lean_object* v___x_1194_; 
v___f_1193_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1194_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1193_, v_ba_1192_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x21(lean_object* v_ba_1195_){
_start:
{
lean_object* v___f_1196_; lean_object* v___x_1197_; 
v___f_1196_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1197_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1196_, v_ba_1195_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode(lean_object* v_userInfo_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Std_Http_URI_EncodedString_decode___redArg(v_userInfo_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode___boxed(lean_object* v_userInfo_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Std_Http_URI_EncodedUserInfo_decode(v_userInfo_1200_);
lean_dec_ref(v_userInfo_1200_);
return v_res_1201_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryParam_encode___lam__0(uint8_t v___y_1202_){
_start:
{
uint8_t v___x_1259_; uint8_t v___x_1260_; 
v___x_1259_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1260_ = lean_uint8_dec_le(v___x_1259_, v___y_1202_);
if (v___x_1260_ == 0)
{
goto v___jp_1254_;
}
else
{
uint8_t v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1262_ = lean_uint8_dec_le(v___y_1202_, v___x_1261_);
if (v___x_1262_ == 0)
{
goto v___jp_1254_;
}
else
{
goto v___jp_1203_;
}
}
v___jp_1203_:
{
uint8_t v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1205_ = lean_uint8_dec_eq(v___y_1202_, v___x_1204_);
if (v___x_1205_ == 0)
{
uint8_t v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1207_ = lean_uint8_dec_eq(v___y_1202_, v___x_1206_);
if (v___x_1207_ == 0)
{
uint8_t v___x_1208_; 
v___x_1208_ = 1;
return v___x_1208_;
}
else
{
return v___x_1205_;
}
}
else
{
uint8_t v___x_1209_; 
v___x_1209_ = 0;
return v___x_1209_;
}
}
v___jp_1210_:
{
uint8_t v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_1212_ = lean_uint8_dec_eq(v___y_1202_, v___x_1211_);
if (v___x_1212_ == 0)
{
uint8_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_1214_ = lean_uint8_dec_eq(v___y_1202_, v___x_1213_);
if (v___x_1214_ == 0)
{
uint8_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1216_ = lean_uint8_dec_eq(v___y_1202_, v___x_1215_);
if (v___x_1216_ == 0)
{
uint8_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_1218_ = lean_uint8_dec_eq(v___y_1202_, v___x_1217_);
if (v___x_1218_ == 0)
{
uint8_t v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1220_ = lean_uint8_dec_eq(v___y_1202_, v___x_1219_);
if (v___x_1220_ == 0)
{
uint8_t v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1222_ = lean_uint8_dec_eq(v___y_1202_, v___x_1221_);
if (v___x_1222_ == 0)
{
uint8_t v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1224_ = lean_uint8_dec_eq(v___y_1202_, v___x_1223_);
if (v___x_1224_ == 0)
{
uint8_t v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1226_ = lean_uint8_dec_eq(v___y_1202_, v___x_1225_);
if (v___x_1226_ == 0)
{
uint8_t v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1228_ = lean_uint8_dec_eq(v___y_1202_, v___x_1227_);
if (v___x_1228_ == 0)
{
uint8_t v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1230_ = lean_uint8_dec_eq(v___y_1202_, v___x_1229_);
if (v___x_1230_ == 0)
{
uint8_t v___x_1231_; uint8_t v___x_1232_; 
v___x_1231_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1232_ = lean_uint8_dec_eq(v___y_1202_, v___x_1231_);
if (v___x_1232_ == 0)
{
uint8_t v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1234_ = lean_uint8_dec_eq(v___y_1202_, v___x_1233_);
if (v___x_1234_ == 0)
{
uint8_t v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1236_ = lean_uint8_dec_eq(v___y_1202_, v___x_1235_);
if (v___x_1236_ == 0)
{
uint8_t v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1238_ = lean_uint8_dec_eq(v___y_1202_, v___x_1237_);
if (v___x_1238_ == 0)
{
uint8_t v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1240_ = lean_uint8_dec_eq(v___y_1202_, v___x_1239_);
if (v___x_1240_ == 0)
{
uint8_t v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1242_ = lean_uint8_dec_eq(v___y_1202_, v___x_1241_);
if (v___x_1242_ == 0)
{
uint8_t v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1244_ = lean_uint8_dec_eq(v___y_1202_, v___x_1243_);
if (v___x_1244_ == 0)
{
uint8_t v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0);
v___x_1246_ = lean_uint8_dec_eq(v___y_1202_, v___x_1245_);
if (v___x_1246_ == 0)
{
uint8_t v___x_1247_; uint8_t v___x_1248_; 
v___x_1247_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1);
v___x_1248_ = lean_uint8_dec_eq(v___y_1202_, v___x_1247_);
if (v___x_1248_ == 0)
{
return v___x_1248_;
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
else
{
goto v___jp_1203_;
}
}
v___jp_1249_:
{
uint8_t v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1251_ = lean_uint8_dec_le(v___x_1250_, v___y_1202_);
if (v___x_1251_ == 0)
{
goto v___jp_1210_;
}
else
{
uint8_t v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1253_ = lean_uint8_dec_le(v___y_1202_, v___x_1252_);
if (v___x_1253_ == 0)
{
goto v___jp_1210_;
}
else
{
goto v___jp_1203_;
}
}
}
v___jp_1254_:
{
uint8_t v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1256_ = lean_uint8_dec_le(v___x_1255_, v___y_1202_);
if (v___x_1256_ == 0)
{
goto v___jp_1249_;
}
else
{
uint8_t v___x_1257_; uint8_t v___x_1258_; 
v___x_1257_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1258_ = lean_uint8_dec_le(v___y_1202_, v___x_1257_);
if (v___x_1258_ == 0)
{
goto v___jp_1249_;
}
else
{
goto v___jp_1203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed(lean_object* v___y_1263_){
_start:
{
uint8_t v___y_419__boxed_1264_; uint8_t v_res_1265_; lean_object* v_r_1266_; 
v___y_419__boxed_1264_ = lean_unbox(v___y_1263_);
v_res_1265_ = l_Std_Http_URI_EncodedQueryParam_encode___lam__0(v___y_419__boxed_1264_);
v_r_1266_ = lean_box(v_res_1265_);
return v_r_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode(lean_object* v_s_1268_){
_start:
{
lean_object* v___f_1269_; lean_object* v___x_1270_; 
v___f_1269_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1270_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_1268_, v___f_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___boxed(lean_object* v_s_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Std_Http_URI_EncodedQueryParam_encode(v_s_1271_);
lean_dec_ref(v_s_1271_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f(lean_object* v_ba_1273_){
_start:
{
lean_object* v___f_1274_; lean_object* v___x_1275_; 
v___f_1274_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1275_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_1273_, v___f_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x21(lean_object* v_ba_1276_){
_start:
{
lean_object* v___f_1277_; lean_object* v___x_1278_; 
v___f_1277_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1278_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v_ba_1276_, v___f_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object* v_s_1279_){
_start:
{
lean_object* v___f_1280_; lean_object* v___x_1281_; 
v___f_1280_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1281_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_1279_, v___f_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f___boxed(lean_object* v_s_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_s_1282_);
lean_dec_ref(v_s_1282_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object* v_param_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_param_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode___boxed(lean_object* v_param_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Std_Http_URI_EncodedQueryParam_decode(v_param_1286_);
lean_dec_ref(v_param_1286_);
return v_res_1287_;
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
