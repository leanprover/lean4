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
uint8_t v___x_74__boxed_67_; uint8_t v_v_boxed_68_; uint8_t v_res_69_; lean_object* v_r_70_; 
v___x_74__boxed_67_ = lean_unbox(v___x_65_);
v_v_boxed_68_ = lean_unbox(v_v_66_);
v_res_69_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars___lam__0(v_r_64_, v___x_74__boxed_67_, v_v_boxed_68_);
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
uint8_t v___x_74__boxed_117_; uint8_t v_v_boxed_118_; uint8_t v_res_119_; lean_object* v_r_120_; 
v___x_74__boxed_117_ = lean_unbox(v___x_115_);
v_v_boxed_118_ = lean_unbox(v_v_116_);
v_res_119_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars___lam__0(v_r_114_, v___x_74__boxed_117_, v_v_boxed_118_);
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
uint8_t v_x_15__boxed_268_; lean_object* v_res_269_; 
v_x_15__boxed_268_ = lean_unbox(v_x_266_);
v_res_269_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(v_x_265_, v_x_15__boxed_268_, v_h__1_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(lean_object* v_motive_270_, lean_object* v_x_271_, uint8_t v_x_272_, lean_object* v_h__1_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___redArg(v_x_271_, v_x_272_, v_h__1_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter___boxed(lean_object* v_motive_275_, lean_object* v_x_276_, lean_object* v_x_277_, lean_object* v_h__1_278_){
_start:
{
uint8_t v_x_27__boxed_279_; lean_object* v_res_280_; 
v_x_27__boxed_279_ = lean_unbox(v_x_277_);
v_res_280_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__ByteArray_push_match__1_splitter(v_motive_275_, v_x_276_, v_x_27__boxed_279_, v_h__1_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter___redArg(lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_h__1_283_, lean_object* v_h__2_284_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v___x_285_; 
lean_dec(v_h__2_284_);
v___x_285_ = lean_apply_1(v_h__1_283_, v_x_282_);
return v___x_285_;
}
else
{
lean_object* v_head_286_; lean_object* v_tail_287_; lean_object* v___x_288_; 
lean_dec(v_h__1_283_);
v_head_286_ = lean_ctor_get(v_x_281_, 0);
lean_inc(v_head_286_);
v_tail_287_ = lean_ctor_get(v_x_281_, 1);
lean_inc(v_tail_287_);
lean_dec_ref(v_x_281_);
v___x_288_ = lean_apply_3(v_h__2_284_, v_head_286_, v_tail_287_, v_x_282_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter(lean_object* v_motive_289_, lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v_h__1_292_, lean_object* v_h__2_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__List_toByteArray_match__1_splitter___redArg(v_x_290_, v_x_291_, v_h__1_292_, v_h__2_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty(lean_object* v_r_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_ByteArray_empty;
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_empty___boxed(lean_object* v_r_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_Http_URI_EncodedString_empty(v_r_297_);
lean_dec_ref(v_r_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited(lean_object* v_r_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_ByteArray_empty;
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instInhabited___boxed(lean_object* v_r_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_Http_URI_EncodedString_instInhabited(v_r_301_);
lean_dec_ref(v_r_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(lean_object* v_s_303_, uint8_t v_c_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = lean_byte_array_push(v_s_303_, v_c_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg___boxed(lean_object* v_s_306_, lean_object* v_c_307_){
_start:
{
uint8_t v_c_boxed_308_; lean_object* v_res_309_; 
v_c_boxed_308_ = lean_unbox(v_c_307_);
v_res_309_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___redArg(v_s_306_, v_c_boxed_308_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(lean_object* v_r_310_, lean_object* v_s_311_, uint8_t v_c_312_, lean_object* v_h_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = lean_byte_array_push(v_s_311_, v_c_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push___boxed(lean_object* v_r_315_, lean_object* v_s_316_, lean_object* v_c_317_, lean_object* v_h_318_){
_start:
{
uint8_t v_c_boxed_319_; lean_object* v_res_320_; 
v_c_boxed_319_ = lean_unbox(v_c_317_);
v_res_320_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_push(v_r_315_, v_s_316_, v_c_boxed_319_, v_h_318_);
lean_dec_ref(v_r_315_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(uint8_t v_b_321_, lean_object* v_s_322_){
_start:
{
uint8_t v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; uint8_t v___x_326_; uint8_t v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; uint8_t v___x_330_; uint8_t v___x_331_; lean_object* v_ba_332_; 
v___x_323_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__0, &l_Std_Http_URI_isEncodedChar___closed__0_once, _init_l_Std_Http_URI_isEncodedChar___closed__0);
v___x_324_ = lean_byte_array_push(v_s_322_, v___x_323_);
v___x_325_ = 4;
v___x_326_ = lean_uint8_shift_right(v_b_321_, v___x_325_);
v___x_327_ = l_Std_Http_URI_hexDigit(v___x_326_);
v___x_328_ = lean_byte_array_push(v___x_324_, v___x_327_);
v___x_329_ = 15;
v___x_330_ = lean_uint8_land(v_b_321_, v___x_329_);
v___x_331_ = l_Std_Http_URI_hexDigit(v___x_330_);
v_ba_332_ = lean_byte_array_push(v___x_328_, v___x_331_);
return v_ba_332_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg___boxed(lean_object* v_b_333_, lean_object* v_s_334_){
_start:
{
uint8_t v_b_boxed_335_; lean_object* v_res_336_; 
v_b_boxed_335_ = lean_unbox(v_b_333_);
v_res_336_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_boxed_335_, v_s_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(lean_object* v_r_337_, uint8_t v_b_338_, lean_object* v_s_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v_b_338_, v_s_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___boxed(lean_object* v_r_341_, lean_object* v_b_342_, lean_object* v_s_343_){
_start:
{
uint8_t v_b_boxed_344_; lean_object* v_res_345_; 
v_b_boxed_344_ = lean_unbox(v_b_342_);
v_res_345_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex(v_r_341_, v_b_boxed_344_, v_s_343_);
lean_dec_ref(v_r_341_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(lean_object* v_r_346_, lean_object* v_as_347_, size_t v_i_348_, size_t v_stop_349_, lean_object* v_b_350_){
_start:
{
lean_object* v___y_352_; uint8_t v___x_356_; 
v___x_356_ = lean_usize_dec_eq(v_i_348_, v_stop_349_);
if (v___x_356_ == 0)
{
uint8_t v___x_357_; uint8_t v___x_358_; uint8_t v___x_359_; 
v___x_357_ = lean_byte_array_uget(v_as_347_, v_i_348_);
v___x_358_ = 128;
v___x_359_ = lean_uint8_dec_lt(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
v___x_360_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_357_, v_b_350_);
v___y_352_ = v___x_360_;
goto v___jp_351_;
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_361_ = lean_box(v___x_357_);
lean_inc_ref(v_r_346_);
v___x_362_ = lean_apply_1(v_r_346_, v___x_361_);
v___x_363_ = lean_unbox(v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
v___x_364_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedString_byteToHex___redArg(v___x_357_, v_b_350_);
v___y_352_ = v___x_364_;
goto v___jp_351_;
}
else
{
lean_object* v___x_365_; 
v___x_365_ = lean_byte_array_push(v_b_350_, v___x_357_);
v___y_352_ = v___x_365_;
goto v___jp_351_;
}
}
}
else
{
lean_dec_ref(v_r_346_);
return v_b_350_;
}
v___jp_351_:
{
size_t v___x_353_; size_t v___x_354_; 
v___x_353_ = ((size_t)1ULL);
v___x_354_ = lean_usize_add(v_i_348_, v___x_353_);
v_i_348_ = v___x_354_;
v_b_350_ = v___y_352_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0___boxed(lean_object* v_r_366_, lean_object* v_as_367_, lean_object* v_i_368_, lean_object* v_stop_369_, lean_object* v_b_370_){
_start:
{
size_t v_i_boxed_371_; size_t v_stop_boxed_372_; lean_object* v_res_373_; 
v_i_boxed_371_ = lean_unbox_usize(v_i_368_);
lean_dec(v_i_368_);
v_stop_boxed_372_ = lean_unbox_usize(v_stop_369_);
lean_dec(v_stop_369_);
v_res_373_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_366_, v_as_367_, v_i_boxed_371_, v_stop_boxed_372_, v_b_370_);
lean_dec_ref(v_as_367_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode(lean_object* v_r_374_, lean_object* v_s_375_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_376_ = l_ByteArray_empty;
v___x_377_ = lean_string_to_utf8(v_s_375_);
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = lean_byte_array_size(v___x_377_);
v___x_380_ = lean_nat_dec_lt(v___x_378_, v___x_379_);
if (v___x_380_ == 0)
{
lean_dec_ref(v___x_377_);
lean_dec_ref(v_r_374_);
return v___x_376_;
}
else
{
uint8_t v___x_381_; 
v___x_381_ = lean_nat_dec_le(v___x_379_, v___x_379_);
if (v___x_381_ == 0)
{
if (v___x_380_ == 0)
{
lean_dec_ref(v___x_377_);
lean_dec_ref(v_r_374_);
return v___x_376_;
}
else
{
size_t v___x_382_; size_t v___x_383_; lean_object* v___x_384_; 
v___x_382_ = ((size_t)0ULL);
v___x_383_ = lean_usize_of_nat(v___x_379_);
v___x_384_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_374_, v___x_377_, v___x_382_, v___x_383_, v___x_376_);
lean_dec_ref(v___x_377_);
return v___x_384_;
}
}
else
{
size_t v___x_385_; size_t v___x_386_; lean_object* v___x_387_; 
v___x_385_ = ((size_t)0ULL);
v___x_386_ = lean_usize_of_nat(v___x_379_);
v___x_387_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedString_encode_spec__0(v_r_374_, v___x_377_, v___x_385_, v___x_386_, v___x_376_);
lean_dec_ref(v___x_377_);
return v___x_387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_encode___boxed(lean_object* v_r_388_, lean_object* v_s_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_Http_URI_EncodedString_encode(v_r_388_, v_s_389_);
lean_dec_ref(v_s_389_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x3f(lean_object* v_r_391_, lean_object* v_ba_392_){
_start:
{
uint8_t v___x_393_; 
lean_inc_ref(v_ba_392_);
v___x_393_ = l_Std_Http_URI_instDecidableIsAllowedEncodedChars(v_r_391_, v_ba_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
lean_dec_ref(v_ba_392_);
v___x_394_ = lean_box(0);
return v___x_394_;
}
else
{
uint8_t v___x_395_; 
v___x_395_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_392_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; 
lean_dec_ref(v_ba_392_);
v___x_396_ = lean_box(0);
return v___x_396_;
}
else
{
lean_object* v___x_397_; 
v___x_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_397_, 0, v_ba_392_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = l_ByteArray_empty;
v___x_400_ = lean_panic_fn(v___x_399_, v_msg_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(lean_object* v_r_401_, lean_object* v_msg_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v_msg_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_404_, lean_object* v_msg_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0(v_r_404_, v_msg_405_);
lean_dec_ref(v_r_404_);
return v_res_406_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_410_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__2));
v___x_411_ = lean_unsigned_to_nat(12u);
v___x_412_ = lean_unsigned_to_nat(320u);
v___x_413_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__1));
v___x_414_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_415_ = l_mkPanicMessageWithDecl(v___x_414_, v___x_413_, v___x_412_, v___x_411_, v___x_410_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofByteArray_x21(lean_object* v_r_416_, lean_object* v_ba_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_416_, v_ba_417_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_obj_once(&l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3, &l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3_once, _init_l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__3);
v___x_420_ = l_panic___at___00Std_Http_URI_EncodedString_ofByteArray_x21_spec__0___redArg(v___x_419_);
return v___x_420_;
}
else
{
lean_object* v_val_421_; 
v_val_421_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_val_421_);
lean_dec_ref(v___x_418_);
return v_val_421_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f(lean_object* v_r_422_, lean_object* v_s_423_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_string_to_utf8(v_s_423_);
v___x_425_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v_r_422_, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x3f___boxed(lean_object* v_r_426_, lean_object* v_s_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Std_Http_URI_EncodedString_ofString_x3f(v_r_426_, v_s_427_);
lean_dec_ref(v_s_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21(lean_object* v_r_429_, lean_object* v_s_430_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_string_to_utf8(v_s_430_);
v___x_432_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v_r_429_, v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_ofString_x21___boxed(lean_object* v_r_433_, lean_object* v_s_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Std_Http_URI_EncodedString_ofString_x21(v_r_433_, v_s_434_);
lean_dec_ref(v_s_434_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg(lean_object* v_ba_436_){
_start:
{
lean_inc_ref(v_ba_436_);
return v_ba_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___redArg___boxed(lean_object* v_ba_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Std_Http_URI_EncodedString_new___redArg(v_ba_437_);
lean_dec_ref(v_ba_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new(lean_object* v_r_439_, lean_object* v_ba_440_, lean_object* v_valid_441_, lean_object* v___validEncoding_442_){
_start:
{
lean_inc_ref(v_ba_440_);
return v_ba_440_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_new___boxed(lean_object* v_r_443_, lean_object* v_ba_444_, lean_object* v_valid_445_, lean_object* v___validEncoding_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_Http_URI_EncodedString_new(v_r_443_, v_ba_444_, v_valid_445_, v___validEncoding_446_);
lean_dec_ref(v_ba_444_);
lean_dec_ref(v_r_443_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___lam__0(lean_object* v_es_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = lean_string_from_utf8_unchecked(v_es_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString(lean_object* v_r_451_){
_start:
{
lean_object* v___f_452_; 
v___f_452_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instToString___closed__0));
return v___f_452_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instToString___boxed(lean_object* v_r_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_Http_URI_EncodedString_instToString(v_r_453_);
lean_dec_ref(v_r_453_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedString_decode_spec__0(lean_object* v_len_455_, lean_object* v_rawBytes_456_, lean_object* v_b_457_){
_start:
{
lean_object* v_fst_459_; lean_object* v_snd_460_; lean_object* v_fst_463_; lean_object* v_snd_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_510_; 
v_fst_463_ = lean_ctor_get(v_b_457_, 0);
v_snd_464_ = lean_ctor_get(v_b_457_, 1);
v_isSharedCheck_510_ = !lean_is_exclusive(v_b_457_);
if (v_isSharedCheck_510_ == 0)
{
v___x_466_ = v_b_457_;
v_isShared_467_ = v_isSharedCheck_510_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_snd_464_);
lean_inc(v_fst_463_);
lean_dec(v_b_457_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_510_;
goto v_resetjp_465_;
}
v___jp_458_:
{
lean_object* v___x_461_; 
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v_fst_459_);
lean_ctor_set(v___x_461_, 1, v_snd_460_);
v_b_457_ = v___x_461_;
goto _start;
}
v_resetjp_465_:
{
uint8_t v___x_468_; 
v___x_468_ = lean_nat_dec_lt(v_snd_464_, v_len_455_);
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
uint8_t v_percent_472_; uint8_t v_c_473_; uint8_t v___x_478_; 
lean_del_object(v___x_466_);
v_percent_472_ = 37;
v_c_473_ = lean_byte_array_fget(v_rawBytes_456_, v_snd_464_);
v___x_478_ = lean_uint8_dec_eq(v_c_473_, v_percent_472_);
if (v___x_478_ == 0)
{
goto v___jp_474_;
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = lean_nat_add(v_snd_464_, v___x_479_);
v___x_481_ = lean_nat_dec_lt(v___x_480_, v_len_455_);
if (v___x_481_ == 0)
{
lean_dec(v___x_480_);
goto v___jp_474_;
}
else
{
uint8_t v_h1_482_; lean_object* v___x_483_; 
v_h1_482_ = lean_byte_array_fget(v_rawBytes_456_, v___x_480_);
lean_dec(v___x_480_);
v___x_483_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_h1_482_);
if (lean_obj_tag(v___x_483_) == 1)
{
lean_object* v_val_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_val_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_val_484_);
lean_dec_ref(v___x_483_);
v___x_485_ = lean_unsigned_to_nat(2u);
v___x_486_ = lean_nat_add(v_snd_464_, v___x_485_);
v___x_487_ = lean_nat_dec_lt(v___x_486_, v_len_455_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec(v_val_484_);
lean_dec(v_snd_464_);
v___x_488_ = lean_byte_array_push(v_fst_463_, v_c_473_);
v___x_489_ = lean_byte_array_push(v___x_488_, v_h1_482_);
v_fst_459_ = v___x_489_;
v_snd_460_ = v___x_486_;
goto v___jp_458_;
}
else
{
uint8_t v_h2_490_; lean_object* v___x_491_; 
v_h2_490_ = lean_byte_array_fget(v_rawBytes_456_, v___x_486_);
lean_dec(v___x_486_);
v___x_491_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_h2_490_);
if (lean_obj_tag(v___x_491_) == 1)
{
lean_object* v_val_492_; uint8_t v___x_493_; uint8_t v___x_494_; uint8_t v___x_495_; uint8_t v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_val_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_val_492_);
lean_dec_ref(v___x_491_);
v___x_493_ = 4;
v___x_494_ = lean_unbox(v_val_484_);
lean_dec(v_val_484_);
v___x_495_ = lean_uint8_shift_left(v___x_494_, v___x_493_);
v___x_496_ = lean_unbox(v_val_492_);
lean_dec(v_val_492_);
v___x_497_ = lean_uint8_add(v___x_495_, v___x_496_);
v___x_498_ = lean_byte_array_push(v_fst_463_, v___x_497_);
v___x_499_ = lean_unsigned_to_nat(3u);
v___x_500_ = lean_nat_add(v_snd_464_, v___x_499_);
lean_dec(v_snd_464_);
v_fst_459_ = v___x_498_;
v_snd_460_ = v___x_500_;
goto v___jp_458_;
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec(v___x_491_);
lean_dec(v_val_484_);
v___x_501_ = lean_byte_array_push(v_fst_463_, v_c_473_);
v___x_502_ = lean_byte_array_push(v___x_501_, v_h1_482_);
v___x_503_ = lean_byte_array_push(v___x_502_, v_h2_490_);
v___x_504_ = lean_unsigned_to_nat(3u);
v___x_505_ = lean_nat_add(v_snd_464_, v___x_504_);
lean_dec(v_snd_464_);
v_fst_459_ = v___x_503_;
v_snd_460_ = v___x_505_;
goto v___jp_458_;
}
}
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v___x_483_);
v___x_506_ = lean_byte_array_push(v_fst_463_, v_c_473_);
v___x_507_ = lean_byte_array_push(v___x_506_, v_h1_482_);
v___x_508_ = lean_unsigned_to_nat(2u);
v___x_509_ = lean_nat_add(v_snd_464_, v___x_508_);
lean_dec(v_snd_464_);
v_fst_459_ = v___x_507_;
v_snd_460_ = v___x_509_;
goto v___jp_458_;
}
}
}
v___jp_474_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_byte_array_push(v_fst_463_, v_c_473_);
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_add(v_snd_464_, v___x_476_);
lean_dec(v_snd_464_);
v_fst_459_ = v___x_475_;
v_snd_460_ = v___x_477_;
goto v___jp_458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedString_decode_spec__0___boxed(lean_object* v_len_511_, lean_object* v_rawBytes_512_, lean_object* v_b_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedString_decode_spec__0(v_len_511_, v_rawBytes_512_, v_b_513_);
lean_dec_ref(v_rawBytes_512_);
lean_dec(v_len_511_);
return v_res_514_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0(void){
_start:
{
lean_object* v_i_515_; lean_object* v_decoded_516_; lean_object* v___x_517_; 
v_i_515_ = lean_unsigned_to_nat(0u);
v_decoded_516_ = l_ByteArray_empty;
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v_decoded_516_);
lean_ctor_set(v___x_517_, 1, v_i_515_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg(lean_object* v_es_518_){
_start:
{
lean_object* v_len_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_fst_522_; uint8_t v___x_523_; 
v_len_519_ = lean_byte_array_size(v_es_518_);
v___x_520_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_521_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedString_decode_spec__0(v_len_519_, v_es_518_, v___x_520_);
v_fst_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_fst_522_);
lean_dec_ref(v___x_521_);
v___x_523_ = lean_string_validate_utf8(v_fst_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; 
lean_dec(v_fst_522_);
v___x_524_ = lean_box(0);
return v___x_524_;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_string_from_utf8_unchecked(v_fst_522_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___redArg___boxed(lean_object* v_es_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_527_);
lean_dec_ref(v_es_527_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode(lean_object* v_r_529_, lean_object* v_es_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_Http_URI_EncodedString_decode___redArg(v_es_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_decode___boxed(lean_object* v_r_532_, lean_object* v_es_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_Http_URI_EncodedString_decode(v_r_532_, v_es_533_);
lean_dec_ref(v_es_533_);
lean_dec_ref(v_r_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___lam__0(lean_object* v_es_535_, lean_object* v_n_536_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = lean_string_from_utf8_unchecked(v_es_535_);
v___x_538_ = l_String_quote(v___x_537_);
v___x_539_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed(lean_object* v_es_540_, lean_object* v_n_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_Http_URI_EncodedString_instRepr___lam__0(v_es_540_, v_n_541_);
lean_dec(v_n_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr(lean_object* v_r_544_){
_start:
{
lean_object* v___f_545_; 
v___f_545_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___closed__0));
return v___f_545_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instRepr___boxed(lean_object* v_r_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_Http_URI_EncodedString_instRepr(v_r_546_);
lean_dec_ref(v_r_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq(lean_object* v_r_548_){
_start:
{
lean_object* v___f_549_; 
v___f_549_ = lean_alloc_closure((void*)(l_ByteArray_instDecidableEq___boxed), 2, 0);
return v___f_549_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instBEq___boxed(lean_object* v_r_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Std_Http_URI_EncodedString_instBEq(v_r_550_);
lean_dec_ref(v_r_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable(lean_object* v_r_553_){
_start:
{
lean_object* v___f_554_; 
v___f_554_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___closed__0));
return v___f_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedString_instHashable___boxed(lean_object* v_r_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_Http_URI_EncodedString_instHashable(v_r_555_);
lean_dec_ref(v_r_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty(lean_object* v_r_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_ByteArray_empty;
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_empty___boxed(lean_object* v_r_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_Http_URI_EncodedQueryString_empty(v_r_559_);
lean_dec_ref(v_r_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited(lean_object* v_r_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_ByteArray_empty;
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_instInhabited___boxed(lean_object* v_r_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Std_Http_URI_EncodedQueryString_instInhabited(v_r_563_);
lean_dec_ref(v_r_563_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(lean_object* v_s_565_, uint8_t v_c_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = lean_byte_array_push(v_s_565_, v_c_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg___boxed(lean_object* v_s_568_, lean_object* v_c_569_){
_start:
{
uint8_t v_c_boxed_570_; lean_object* v_res_571_; 
v_c_boxed_570_ = lean_unbox(v_c_569_);
v_res_571_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___redArg(v_s_568_, v_c_boxed_570_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(lean_object* v_r_572_, lean_object* v_s_573_, uint8_t v_c_574_, lean_object* v_h_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = lean_byte_array_push(v_s_573_, v_c_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push___boxed(lean_object* v_r_577_, lean_object* v_s_578_, lean_object* v_c_579_, lean_object* v_h_580_){
_start:
{
uint8_t v_c_boxed_581_; lean_object* v_res_582_; 
v_c_boxed_581_ = lean_unbox(v_c_579_);
v_res_582_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_push(v_r_577_, v_s_578_, v_c_boxed_581_, v_h_580_);
lean_dec_ref(v_r_577_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(lean_object* v_ba_583_, lean_object* v_r_584_){
_start:
{
uint8_t v___x_585_; 
lean_inc_ref(v_ba_583_);
v___x_585_ = l_Std_Http_URI_instDecidableIsAllowedEncodedQueryChars(v_r_584_, v_ba_583_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
lean_dec_ref(v_ba_583_);
v___x_586_ = lean_box(0);
return v___x_586_;
}
else
{
uint8_t v___x_587_; 
v___x_587_ = l_Std_Http_URI_isValidPercentEncoding(v_ba_583_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
lean_dec_ref(v_ba_583_);
v___x_588_ = lean_box(0);
return v___x_588_;
}
else
{
lean_object* v___x_589_; 
v___x_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_589_, 0, v_ba_583_);
return v___x_589_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(lean_object* v_msg_590_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = l_ByteArray_empty;
v___x_592_ = lean_panic_fn(v___x_591_, v_msg_590_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(lean_object* v_r_593_, lean_object* v_msg_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v_msg_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___boxed(lean_object* v_r_596_, lean_object* v_msg_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0(v_r_596_, v_msg_597_);
lean_dec_ref(v_r_596_);
return v_res_598_;
}
}
static lean_object* _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_601_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__1));
v___x_602_ = lean_unsigned_to_nat(12u);
v___x_603_ = lean_unsigned_to_nat(438u);
v___x_604_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__0));
v___x_605_ = ((lean_object*)(l_Std_Http_URI_EncodedString_ofByteArray_x21___closed__0));
v___x_606_ = l_mkPanicMessageWithDecl(v___x_605_, v___x_604_, v___x_603_, v___x_602_, v___x_601_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(lean_object* v_ba_607_, lean_object* v_r_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_607_, v_r_608_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_obj_once(&l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2, &l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2_once, _init_l_Std_Http_URI_EncodedQueryString_ofByteArray_x21___closed__2);
v___x_611_ = l_panic___at___00Std_Http_URI_EncodedQueryString_ofByteArray_x21_spec__0___redArg(v___x_610_);
return v___x_611_;
}
else
{
lean_object* v_val_612_; 
v_val_612_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_val_612_);
lean_dec_ref(v___x_609_);
return v_val_612_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f(lean_object* v_s_613_, lean_object* v_r_614_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_string_to_utf8(v_s_613_);
v___x_616_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v___x_615_, v_r_614_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x3f___boxed(lean_object* v_s_617_, lean_object* v_r_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_617_, v_r_618_);
lean_dec_ref(v_s_617_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21(lean_object* v_s_620_, lean_object* v_r_621_){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_string_to_utf8(v_s_620_);
v___x_623_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v___x_622_, v_r_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_ofString_x21___boxed(lean_object* v_s_624_, lean_object* v_r_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_Http_URI_EncodedQueryString_ofString_x21(v_s_624_, v_r_625_);
lean_dec_ref(v_s_624_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg(lean_object* v_ba_627_){
_start:
{
lean_inc_ref(v_ba_627_);
return v_ba_627_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___redArg___boxed(lean_object* v_ba_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Std_Http_URI_EncodedQueryString_new___redArg(v_ba_628_);
lean_dec_ref(v_ba_628_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new(lean_object* v_r_630_, lean_object* v_ba_631_, lean_object* v_valid_632_, lean_object* v___validEncoding_633_){
_start:
{
lean_inc_ref(v_ba_631_);
return v_ba_631_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_new___boxed(lean_object* v_r_634_, lean_object* v_ba_635_, lean_object* v_valid_636_, lean_object* v___validEncoding_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_Http_URI_EncodedQueryString_new(v_r_634_, v_ba_635_, v_valid_636_, v___validEncoding_637_);
lean_dec_ref(v_ba_635_);
lean_dec_ref(v_r_634_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(uint8_t v_b_639_, lean_object* v_s_640_){
_start:
{
uint8_t v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; uint8_t v___x_644_; uint8_t v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; uint8_t v___x_648_; uint8_t v___x_649_; lean_object* v_ba_650_; 
v___x_641_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__0, &l_Std_Http_URI_isEncodedChar___closed__0_once, _init_l_Std_Http_URI_isEncodedChar___closed__0);
v___x_642_ = lean_byte_array_push(v_s_640_, v___x_641_);
v___x_643_ = 4;
v___x_644_ = lean_uint8_shift_right(v_b_639_, v___x_643_);
v___x_645_ = l_Std_Http_URI_hexDigit(v___x_644_);
v___x_646_ = lean_byte_array_push(v___x_642_, v___x_645_);
v___x_647_ = 15;
v___x_648_ = lean_uint8_land(v_b_639_, v___x_647_);
v___x_649_ = l_Std_Http_URI_hexDigit(v___x_648_);
v_ba_650_ = lean_byte_array_push(v___x_646_, v___x_649_);
return v_ba_650_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg___boxed(lean_object* v_b_651_, lean_object* v_s_652_){
_start:
{
uint8_t v_b_boxed_653_; lean_object* v_res_654_; 
v_b_boxed_653_ = lean_unbox(v_b_651_);
v_res_654_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_boxed_653_, v_s_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(lean_object* v_r_655_, uint8_t v_b_656_, lean_object* v_s_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v_b_656_, v_s_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___boxed(lean_object* v_r_659_, lean_object* v_b_660_, lean_object* v_s_661_){
_start:
{
uint8_t v_b_boxed_662_; lean_object* v_res_663_; 
v_b_boxed_662_ = lean_unbox(v_b_660_);
v_res_663_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex(v_r_659_, v_b_boxed_662_, v_s_661_);
lean_dec_ref(v_r_659_);
return v_res_663_;
}
}
static uint8_t _init_l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0(void){
_start:
{
uint32_t v___x_664_; uint8_t v___x_665_; 
v___x_664_ = 32;
v___x_665_ = lean_uint32_to_uint8(v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(lean_object* v_r_666_, lean_object* v_as_667_, size_t v_i_668_, size_t v_stop_669_, lean_object* v_b_670_){
_start:
{
lean_object* v___y_672_; uint8_t v___x_676_; 
v___x_676_ = lean_usize_dec_eq(v_i_668_, v_stop_669_);
if (v___x_676_ == 0)
{
uint8_t v___x_677_; uint8_t v___x_684_; uint8_t v___x_685_; 
v___x_677_ = lean_byte_array_uget(v_as_667_, v_i_668_);
v___x_684_ = 128;
v___x_685_ = lean_uint8_dec_lt(v___x_677_, v___x_684_);
if (v___x_685_ == 0)
{
goto v___jp_678_;
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_686_ = lean_box(v___x_677_);
lean_inc_ref(v_r_666_);
v___x_687_ = lean_apply_1(v_r_666_, v___x_686_);
v___x_688_ = lean_unbox(v___x_687_);
if (v___x_688_ == 0)
{
goto v___jp_678_;
}
else
{
lean_object* v___x_689_; 
v___x_689_ = lean_byte_array_push(v_b_670_, v___x_677_);
v___y_672_ = v___x_689_;
goto v___jp_671_;
}
}
v___jp_678_:
{
uint8_t v___x_679_; uint8_t v___x_680_; 
v___x_679_ = lean_uint8_once(&l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0, &l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0_once, _init_l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___closed__0);
v___x_680_ = lean_uint8_dec_eq(v___x_677_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
v___x_681_ = l___private_Std_Internal_Http_Data_URI_Encoding_0__Std_Http_URI_EncodedQueryString_byteToHex___redArg(v___x_677_, v_b_670_);
v___y_672_ = v___x_681_;
goto v___jp_671_;
}
else
{
uint8_t v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_683_ = lean_byte_array_push(v_b_670_, v___x_682_);
v___y_672_ = v___x_683_;
goto v___jp_671_;
}
}
}
else
{
lean_dec_ref(v_r_666_);
return v_b_670_;
}
v___jp_671_:
{
size_t v___x_673_; size_t v___x_674_; 
v___x_673_ = ((size_t)1ULL);
v___x_674_ = lean_usize_add(v_i_668_, v___x_673_);
v_i_668_ = v___x_674_;
v_b_670_ = v___y_672_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0___boxed(lean_object* v_r_690_, lean_object* v_as_691_, lean_object* v_i_692_, lean_object* v_stop_693_, lean_object* v_b_694_){
_start:
{
size_t v_i_boxed_695_; size_t v_stop_boxed_696_; lean_object* v_res_697_; 
v_i_boxed_695_ = lean_unbox_usize(v_i_692_);
lean_dec(v_i_692_);
v_stop_boxed_696_ = lean_unbox_usize(v_stop_693_);
lean_dec(v_stop_693_);
v_res_697_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_690_, v_as_691_, v_i_boxed_695_, v_stop_boxed_696_, v_b_694_);
lean_dec_ref(v_as_691_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode(lean_object* v_s_698_, lean_object* v_r_699_){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_700_ = l_ByteArray_empty;
v___x_701_ = lean_string_to_utf8(v_s_698_);
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_byte_array_size(v___x_701_);
v___x_704_ = lean_nat_dec_lt(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
lean_dec_ref(v___x_701_);
lean_dec_ref(v_r_699_);
return v___x_700_;
}
else
{
uint8_t v___x_705_; 
v___x_705_ = lean_nat_dec_le(v___x_703_, v___x_703_);
if (v___x_705_ == 0)
{
if (v___x_704_ == 0)
{
lean_dec_ref(v___x_701_);
lean_dec_ref(v_r_699_);
return v___x_700_;
}
else
{
size_t v___x_706_; size_t v___x_707_; lean_object* v___x_708_; 
v___x_706_ = ((size_t)0ULL);
v___x_707_ = lean_usize_of_nat(v___x_703_);
v___x_708_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_699_, v___x_701_, v___x_706_, v___x_707_, v___x_700_);
lean_dec_ref(v___x_701_);
return v___x_708_;
}
}
else
{
size_t v___x_709_; size_t v___x_710_; lean_object* v___x_711_; 
v___x_709_ = ((size_t)0ULL);
v___x_710_ = lean_usize_of_nat(v___x_703_);
v___x_711_ = l_ByteArray_foldlMUnsafe_fold___at___00Std_Http_URI_EncodedQueryString_encode_spec__0(v_r_699_, v___x_701_, v___x_709_, v___x_710_, v___x_700_);
lean_dec_ref(v___x_701_);
return v___x_711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_encode___boxed(lean_object* v_s_712_, lean_object* v_r_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_712_, v_r_713_);
lean_dec_ref(v_s_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___redArg(lean_object* v_es_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = lean_string_from_utf8_unchecked(v_es_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString(lean_object* v_r_717_, lean_object* v_es_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = lean_string_from_utf8_unchecked(v_es_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_toString___boxed(lean_object* v_r_720_, lean_object* v_es_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Std_Http_URI_EncodedQueryString_toString(v_r_720_, v_es_721_);
lean_dec_ref(v_r_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(lean_object* v_len_723_, lean_object* v_rawBytes_724_, lean_object* v_b_725_){
_start:
{
lean_object* v_fst_727_; lean_object* v_snd_728_; lean_object* v_fst_731_; lean_object* v_snd_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_784_; 
v_fst_731_ = lean_ctor_get(v_b_725_, 0);
v_snd_732_ = lean_ctor_get(v_b_725_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v_b_725_);
if (v_isSharedCheck_784_ == 0)
{
v___x_734_ = v_b_725_;
v_isShared_735_ = v_isSharedCheck_784_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_snd_732_);
lean_inc(v_fst_731_);
lean_dec(v_b_725_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_784_;
goto v_resetjp_733_;
}
v___jp_726_:
{
lean_object* v___x_729_; 
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v_fst_727_);
lean_ctor_set(v___x_729_, 1, v_snd_728_);
v_b_725_ = v___x_729_;
goto _start;
}
v_resetjp_733_:
{
uint8_t v___x_736_; 
v___x_736_ = lean_nat_dec_lt(v_snd_732_, v_len_723_);
if (v___x_736_ == 0)
{
lean_object* v___x_738_; 
if (v_isShared_735_ == 0)
{
v___x_738_ = v___x_734_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_fst_731_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_snd_732_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
else
{
uint8_t v_plus_740_; uint8_t v_c_741_; uint8_t v___x_746_; 
lean_del_object(v___x_734_);
v_plus_740_ = 43;
v_c_741_ = lean_byte_array_fget(v_rawBytes_724_, v_snd_732_);
v___x_746_ = lean_uint8_dec_eq(v_c_741_, v_plus_740_);
if (v___x_746_ == 0)
{
uint8_t v_percent_747_; uint8_t v___x_748_; 
v_percent_747_ = 37;
v___x_748_ = lean_uint8_dec_eq(v_c_741_, v_percent_747_);
if (v___x_748_ == 0)
{
goto v___jp_742_;
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_nat_add(v_snd_732_, v___x_749_);
v___x_751_ = lean_nat_dec_lt(v___x_750_, v_len_723_);
if (v___x_751_ == 0)
{
lean_dec(v___x_750_);
goto v___jp_742_;
}
else
{
uint8_t v_h1_752_; lean_object* v___x_753_; 
v_h1_752_ = lean_byte_array_fget(v_rawBytes_724_, v___x_750_);
lean_dec(v___x_750_);
v___x_753_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_h1_752_);
if (lean_obj_tag(v___x_753_) == 1)
{
lean_object* v_val_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_val_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_val_754_);
lean_dec_ref(v___x_753_);
v___x_755_ = lean_unsigned_to_nat(2u);
v___x_756_ = lean_nat_add(v_snd_732_, v___x_755_);
v___x_757_ = lean_nat_dec_lt(v___x_756_, v_len_723_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec(v_val_754_);
lean_dec(v_snd_732_);
v___x_758_ = lean_byte_array_push(v_fst_731_, v_c_741_);
v___x_759_ = lean_byte_array_push(v___x_758_, v_h1_752_);
v_fst_727_ = v___x_759_;
v_snd_728_ = v___x_756_;
goto v___jp_726_;
}
else
{
uint8_t v_h2_760_; lean_object* v___x_761_; 
v_h2_760_ = lean_byte_array_fget(v_rawBytes_724_, v___x_756_);
lean_dec(v___x_756_);
v___x_761_ = l_Std_Http_URI_hexDigitToUInt8_x3f(v_h2_760_);
if (lean_obj_tag(v___x_761_) == 1)
{
lean_object* v_val_762_; uint8_t v___x_763_; uint8_t v___x_764_; uint8_t v___x_765_; uint8_t v___x_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_val_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_val_762_);
lean_dec_ref(v___x_761_);
v___x_763_ = 4;
v___x_764_ = lean_unbox(v_val_754_);
lean_dec(v_val_754_);
v___x_765_ = lean_uint8_shift_left(v___x_764_, v___x_763_);
v___x_766_ = lean_unbox(v_val_762_);
lean_dec(v_val_762_);
v___x_767_ = lean_uint8_add(v___x_765_, v___x_766_);
v___x_768_ = lean_byte_array_push(v_fst_731_, v___x_767_);
v___x_769_ = lean_unsigned_to_nat(3u);
v___x_770_ = lean_nat_add(v_snd_732_, v___x_769_);
lean_dec(v_snd_732_);
v_fst_727_ = v___x_768_;
v_snd_728_ = v___x_770_;
goto v___jp_726_;
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec(v___x_761_);
lean_dec(v_val_754_);
v___x_771_ = lean_byte_array_push(v_fst_731_, v_c_741_);
v___x_772_ = lean_byte_array_push(v___x_771_, v_h1_752_);
v___x_773_ = lean_byte_array_push(v___x_772_, v_h2_760_);
v___x_774_ = lean_unsigned_to_nat(3u);
v___x_775_ = lean_nat_add(v_snd_732_, v___x_774_);
lean_dec(v_snd_732_);
v_fst_727_ = v___x_773_;
v_snd_728_ = v___x_775_;
goto v___jp_726_;
}
}
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec(v___x_753_);
v___x_776_ = lean_byte_array_push(v_fst_731_, v_c_741_);
v___x_777_ = lean_byte_array_push(v___x_776_, v_h1_752_);
v___x_778_ = lean_unsigned_to_nat(2u);
v___x_779_ = lean_nat_add(v_snd_732_, v___x_778_);
lean_dec(v_snd_732_);
v_fst_727_ = v___x_777_;
v_snd_728_ = v___x_779_;
goto v___jp_726_;
}
}
}
}
else
{
uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_780_ = 32;
v___x_781_ = lean_byte_array_push(v_fst_731_, v___x_780_);
v___x_782_ = lean_unsigned_to_nat(1u);
v___x_783_ = lean_nat_add(v_snd_732_, v___x_782_);
lean_dec(v_snd_732_);
v_fst_727_ = v___x_781_;
v_snd_728_ = v___x_783_;
goto v___jp_726_;
}
v___jp_742_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = lean_byte_array_push(v_fst_731_, v_c_741_);
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = lean_nat_add(v_snd_732_, v___x_744_);
lean_dec(v_snd_732_);
v_fst_727_ = v___x_743_;
v_snd_728_ = v___x_745_;
goto v___jp_726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedQueryString_decode_spec__0___boxed(lean_object* v_len_785_, lean_object* v_rawBytes_786_, lean_object* v_b_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(v_len_785_, v_rawBytes_786_, v_b_787_);
lean_dec_ref(v_rawBytes_786_);
lean_dec(v_len_785_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg(lean_object* v_es_789_){
_start:
{
lean_object* v_len_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v_fst_793_; uint8_t v___x_794_; 
v_len_790_ = lean_byte_array_size(v_es_789_);
v___x_791_ = lean_obj_once(&l_Std_Http_URI_EncodedString_decode___redArg___closed__0, &l_Std_Http_URI_EncodedString_decode___redArg___closed__0_once, _init_l_Std_Http_URI_EncodedString_decode___redArg___closed__0);
v___x_792_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_EncodedQueryString_decode_spec__0(v_len_790_, v_es_789_, v___x_791_);
v_fst_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_fst_793_);
lean_dec_ref(v___x_792_);
v___x_794_ = lean_string_validate_utf8(v_fst_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
lean_dec(v_fst_793_);
v___x_795_ = lean_box(0);
return v___x_795_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_string_from_utf8_unchecked(v_fst_793_);
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___redArg___boxed(lean_object* v_es_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_798_);
lean_dec_ref(v_es_798_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode(lean_object* v_r_800_, lean_object* v_es_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_es_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryString_decode___boxed(lean_object* v_r_803_, lean_object* v_es_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Std_Http_URI_EncodedQueryString_decode(v_r_803_, v_es_804_);
lean_dec_ref(v_es_804_);
lean_dec_ref(v_r_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringEncodedQueryString(lean_object* v_r_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = lean_alloc_closure((void*)(l_Std_Http_URI_EncodedQueryString_toString___boxed), 2, 1);
lean_closure_set(v___x_807_, 0, v_r_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString(lean_object* v_r_808_){
_start:
{
lean_object* v___f_809_; 
v___f_809_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instRepr___closed__0));
return v___f_809_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprEncodedQueryString___boxed(lean_object* v_r_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Std_Http_URI_instReprEncodedQueryString(v_r_810_);
lean_dec_ref(v_r_810_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString(lean_object* v_r_812_){
_start:
{
lean_object* v___f_813_; 
v___f_813_ = lean_alloc_closure((void*)(l_ByteArray_instDecidableEq___boxed), 2, 0);
return v___f_813_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqEncodedQueryString___boxed(lean_object* v_r_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Std_Http_URI_instBEqEncodedQueryString(v_r_814_);
lean_dec_ref(v_r_814_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString(lean_object* v_r_816_){
_start:
{
lean_object* v___f_817_; 
v___f_817_ = ((lean_object*)(l_Std_Http_URI_EncodedString_instHashable___closed__0));
return v___f_817_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableEncodedQueryString___boxed(lean_object* v_r_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Std_Http_URI_instHashableEncodedQueryString(v_r_818_);
lean_dec_ref(v_r_818_);
return v_res_819_;
}
}
static uint64_t _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1(void){
_start:
{
lean_object* v___x_826_; uint64_t v___x_827_; 
v___x_826_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__0));
v___x_827_ = lean_byte_array_hash(v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2));
v___x_835_ = lean_byte_array_size(v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT uint64_t l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0(lean_object* v_x_836_){
_start:
{
if (lean_obj_tag(v_x_836_) == 0)
{
uint64_t v___x_837_; 
v___x_837_ = lean_uint64_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1, &l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__1);
return v___x_837_;
}
else
{
lean_object* v_val_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; lean_object* v___x_844_; uint64_t v___x_845_; 
v_val_838_ = lean_ctor_get(v_x_836_, 0);
v___x_839_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__2));
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = lean_obj_once(&l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3, &l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3_once, _init_l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___closed__3);
v___x_842_ = lean_byte_array_size(v_val_838_);
v___x_843_ = 0;
v___x_844_ = lean_byte_array_copy_slice(v_val_838_, v___x_840_, v___x_839_, v___x_841_, v___x_842_, v___x_843_);
v___x_845_ = lean_byte_array_hash(v___x_844_);
lean_dec_ref(v___x_844_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0___boxed(lean_object* v_x_846_){
_start:
{
uint64_t v_res_847_; lean_object* v_r_848_; 
v_res_847_ = l_Std_Http_URI_instHashableOptionEncodedQueryString___lam__0(v_x_846_);
lean_dec(v_x_846_);
v_r_848_ = lean_box_uint64(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString(lean_object* v_r_850_){
_start:
{
lean_object* v___f_851_; 
v___f_851_ = ((lean_object*)(l_Std_Http_URI_instHashableOptionEncodedQueryString___closed__0));
return v___f_851_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instHashableOptionEncodedQueryString___boxed(lean_object* v_r_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Std_Http_URI_instHashableOptionEncodedQueryString(v_r_852_);
lean_dec_ref(v_r_852_);
return v_res_853_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0(void){
_start:
{
uint32_t v___x_854_; uint8_t v___x_855_; 
v___x_854_ = 58;
v___x_855_ = lean_uint32_to_uint8(v___x_854_);
return v___x_855_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1(void){
_start:
{
uint32_t v___x_856_; uint8_t v___x_857_; 
v___x_856_ = 64;
v___x_857_ = lean_uint32_to_uint8(v___x_856_);
return v___x_857_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2(void){
_start:
{
uint32_t v___x_858_; uint8_t v___x_859_; 
v___x_858_ = 38;
v___x_859_ = lean_uint32_to_uint8(v___x_858_);
return v___x_859_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3(void){
_start:
{
uint32_t v___x_860_; uint8_t v___x_861_; 
v___x_860_ = 39;
v___x_861_ = lean_uint32_to_uint8(v___x_860_);
return v___x_861_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4(void){
_start:
{
uint32_t v___x_862_; uint8_t v___x_863_; 
v___x_862_ = 40;
v___x_863_ = lean_uint32_to_uint8(v___x_862_);
return v___x_863_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5(void){
_start:
{
uint32_t v___x_864_; uint8_t v___x_865_; 
v___x_864_ = 41;
v___x_865_ = lean_uint32_to_uint8(v___x_864_);
return v___x_865_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6(void){
_start:
{
uint32_t v___x_866_; uint8_t v___x_867_; 
v___x_866_ = 42;
v___x_867_ = lean_uint32_to_uint8(v___x_866_);
return v___x_867_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7(void){
_start:
{
uint32_t v___x_868_; uint8_t v___x_869_; 
v___x_868_ = 44;
v___x_869_ = lean_uint32_to_uint8(v___x_868_);
return v___x_869_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8(void){
_start:
{
uint32_t v___x_870_; uint8_t v___x_871_; 
v___x_870_ = 59;
v___x_871_ = lean_uint32_to_uint8(v___x_870_);
return v___x_871_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9(void){
_start:
{
uint32_t v___x_872_; uint8_t v___x_873_; 
v___x_872_ = 61;
v___x_873_ = lean_uint32_to_uint8(v___x_872_);
return v___x_873_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10(void){
_start:
{
uint32_t v___x_874_; uint8_t v___x_875_; 
v___x_874_ = 33;
v___x_875_ = lean_uint32_to_uint8(v___x_874_);
return v___x_875_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11(void){
_start:
{
uint32_t v___x_876_; uint8_t v___x_877_; 
v___x_876_ = 36;
v___x_877_ = lean_uint32_to_uint8(v___x_876_);
return v___x_877_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12(void){
_start:
{
uint32_t v___x_878_; uint8_t v___x_879_; 
v___x_878_ = 95;
v___x_879_ = lean_uint32_to_uint8(v___x_878_);
return v___x_879_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13(void){
_start:
{
uint32_t v___x_880_; uint8_t v___x_881_; 
v___x_880_ = 126;
v___x_881_ = lean_uint32_to_uint8(v___x_880_);
return v___x_881_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14(void){
_start:
{
uint32_t v___x_882_; uint8_t v___x_883_; 
v___x_882_ = 45;
v___x_883_ = lean_uint32_to_uint8(v___x_882_);
return v___x_883_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15(void){
_start:
{
uint32_t v___x_884_; uint8_t v___x_885_; 
v___x_884_ = 46;
v___x_885_ = lean_uint32_to_uint8(v___x_884_);
return v___x_885_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16(void){
_start:
{
uint32_t v___x_886_; uint8_t v___x_887_; 
v___x_886_ = 90;
v___x_887_ = lean_uint32_to_uint8(v___x_886_);
return v___x_887_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17(void){
_start:
{
uint32_t v___x_888_; uint8_t v___x_889_; 
v___x_888_ = 122;
v___x_889_ = lean_uint32_to_uint8(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedSegment_encode___lam__0(uint8_t v___y_890_){
_start:
{
uint8_t v___y_892_; uint8_t v___y_898_; uint8_t v___y_918_; uint8_t v___y_924_; uint8_t v___y_930_; uint8_t v___y_936_; uint8_t v___y_942_; uint8_t v___x_947_; uint8_t v___x_948_; 
v___x_947_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_948_ = lean_uint8_dec_le(v___x_947_, v___y_890_);
if (v___x_948_ == 0)
{
v___y_942_ = v___x_948_;
goto v___jp_941_;
}
else
{
uint8_t v___x_949_; uint8_t v___x_950_; 
v___x_949_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_950_ = lean_uint8_dec_le(v___y_890_, v___x_949_);
v___y_942_ = v___x_950_;
goto v___jp_941_;
}
v___jp_891_:
{
if (v___y_892_ == 0)
{
uint8_t v___x_893_; uint8_t v___x_894_; 
v___x_893_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_894_ = lean_uint8_dec_eq(v___y_890_, v___x_893_);
if (v___x_894_ == 0)
{
uint8_t v___x_895_; uint8_t v___x_896_; 
v___x_895_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_896_ = lean_uint8_dec_eq(v___y_890_, v___x_895_);
return v___x_896_;
}
else
{
return v___x_894_;
}
}
else
{
return v___y_892_;
}
}
v___jp_897_:
{
if (v___y_898_ == 0)
{
uint8_t v___x_899_; uint8_t v___x_900_; 
v___x_899_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_900_ = lean_uint8_dec_eq(v___y_890_, v___x_899_);
if (v___x_900_ == 0)
{
uint8_t v___x_901_; uint8_t v___x_902_; 
v___x_901_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_902_ = lean_uint8_dec_eq(v___y_890_, v___x_901_);
if (v___x_902_ == 0)
{
uint8_t v___x_903_; uint8_t v___x_904_; 
v___x_903_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_904_ = lean_uint8_dec_eq(v___y_890_, v___x_903_);
if (v___x_904_ == 0)
{
uint8_t v___x_905_; uint8_t v___x_906_; 
v___x_905_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_906_ = lean_uint8_dec_eq(v___y_890_, v___x_905_);
if (v___x_906_ == 0)
{
uint8_t v___x_907_; uint8_t v___x_908_; 
v___x_907_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_908_ = lean_uint8_dec_eq(v___y_890_, v___x_907_);
if (v___x_908_ == 0)
{
uint8_t v___x_909_; uint8_t v___x_910_; 
v___x_909_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_910_ = lean_uint8_dec_eq(v___y_890_, v___x_909_);
if (v___x_910_ == 0)
{
uint8_t v___x_911_; uint8_t v___x_912_; 
v___x_911_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_912_ = lean_uint8_dec_eq(v___y_890_, v___x_911_);
if (v___x_912_ == 0)
{
uint8_t v___x_913_; uint8_t v___x_914_; 
v___x_913_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_914_ = lean_uint8_dec_eq(v___y_890_, v___x_913_);
if (v___x_914_ == 0)
{
uint8_t v___x_915_; uint8_t v___x_916_; 
v___x_915_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_916_ = lean_uint8_dec_eq(v___y_890_, v___x_915_);
v___y_892_ = v___x_916_;
goto v___jp_891_;
}
else
{
v___y_892_ = v___x_914_;
goto v___jp_891_;
}
}
else
{
v___y_892_ = v___x_912_;
goto v___jp_891_;
}
}
else
{
v___y_892_ = v___x_910_;
goto v___jp_891_;
}
}
else
{
v___y_892_ = v___x_908_;
goto v___jp_891_;
}
}
else
{
v___y_892_ = v___x_906_;
goto v___jp_891_;
}
}
else
{
v___y_892_ = v___x_904_;
goto v___jp_891_;
}
}
else
{
v___y_892_ = v___x_902_;
goto v___jp_891_;
}
}
else
{
v___y_892_ = v___x_900_;
goto v___jp_891_;
}
}
else
{
return v___y_898_;
}
}
v___jp_917_:
{
if (v___y_918_ == 0)
{
uint8_t v___x_919_; uint8_t v___x_920_; 
v___x_919_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_920_ = lean_uint8_dec_eq(v___y_890_, v___x_919_);
if (v___x_920_ == 0)
{
uint8_t v___x_921_; uint8_t v___x_922_; 
v___x_921_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_922_ = lean_uint8_dec_eq(v___y_890_, v___x_921_);
v___y_898_ = v___x_922_;
goto v___jp_897_;
}
else
{
v___y_898_ = v___x_920_;
goto v___jp_897_;
}
}
else
{
return v___y_918_;
}
}
v___jp_923_:
{
if (v___y_924_ == 0)
{
uint8_t v___x_925_; uint8_t v___x_926_; 
v___x_925_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_926_ = lean_uint8_dec_eq(v___y_890_, v___x_925_);
if (v___x_926_ == 0)
{
uint8_t v___x_927_; uint8_t v___x_928_; 
v___x_927_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_928_ = lean_uint8_dec_eq(v___y_890_, v___x_927_);
v___y_918_ = v___x_928_;
goto v___jp_917_;
}
else
{
v___y_918_ = v___x_926_;
goto v___jp_917_;
}
}
else
{
return v___y_924_;
}
}
v___jp_929_:
{
if (v___y_930_ == 0)
{
uint8_t v___x_931_; uint8_t v___x_932_; 
v___x_931_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_932_ = lean_uint8_dec_eq(v___y_890_, v___x_931_);
if (v___x_932_ == 0)
{
uint8_t v___x_933_; uint8_t v___x_934_; 
v___x_933_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_934_ = lean_uint8_dec_eq(v___y_890_, v___x_933_);
v___y_924_ = v___x_934_;
goto v___jp_923_;
}
else
{
v___y_924_ = v___x_932_;
goto v___jp_923_;
}
}
else
{
return v___y_930_;
}
}
v___jp_935_:
{
if (v___y_936_ == 0)
{
uint8_t v___x_937_; uint8_t v___x_938_; 
v___x_937_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_938_ = lean_uint8_dec_le(v___x_937_, v___y_890_);
if (v___x_938_ == 0)
{
v___y_930_ = v___x_938_;
goto v___jp_929_;
}
else
{
uint8_t v___x_939_; uint8_t v___x_940_; 
v___x_939_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_940_ = lean_uint8_dec_le(v___y_890_, v___x_939_);
v___y_930_ = v___x_940_;
goto v___jp_929_;
}
}
else
{
return v___y_936_;
}
}
v___jp_941_:
{
if (v___y_942_ == 0)
{
uint8_t v___x_943_; uint8_t v___x_944_; 
v___x_943_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_944_ = lean_uint8_dec_le(v___x_943_, v___y_890_);
if (v___x_944_ == 0)
{
v___y_936_ = v___x_944_;
goto v___jp_935_;
}
else
{
uint8_t v___x_945_; uint8_t v___x_946_; 
v___x_945_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_946_ = lean_uint8_dec_le(v___y_890_, v___x_945_);
v___y_936_ = v___x_946_;
goto v___jp_935_;
}
}
else
{
return v___y_942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___lam__0___boxed(lean_object* v___y_951_){
_start:
{
uint8_t v___y_318__boxed_952_; uint8_t v_res_953_; lean_object* v_r_954_; 
v___y_318__boxed_952_ = lean_unbox(v___y_951_);
v_res_953_ = l_Std_Http_URI_EncodedSegment_encode___lam__0(v___y_318__boxed_952_);
v_r_954_ = lean_box(v_res_953_);
return v_r_954_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode(lean_object* v_s_956_){
_start:
{
lean_object* v___f_957_; lean_object* v___x_958_; 
v___f_957_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_958_ = l_Std_Http_URI_EncodedString_encode(v___f_957_, v_s_956_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_encode___boxed(lean_object* v_s_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Std_Http_URI_EncodedSegment_encode(v_s_959_);
lean_dec_ref(v_s_959_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object* v_ba_961_){
_start:
{
lean_object* v___f_962_; lean_object* v___x_963_; 
v___f_962_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_963_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_962_, v_ba_961_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x21(lean_object* v_ba_964_){
_start:
{
lean_object* v___f_965_; lean_object* v___x_966_; 
v___f_965_ = ((lean_object*)(l_Std_Http_URI_EncodedSegment_encode___closed__0));
v___x_966_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_965_, v_ba_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object* v_segment_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Std_Http_URI_EncodedString_decode___redArg(v_segment_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedSegment_decode___boxed(lean_object* v_segment_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_Http_URI_EncodedSegment_decode(v_segment_969_);
lean_dec_ref(v_segment_969_);
return v_res_970_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0(void){
_start:
{
uint32_t v___x_971_; uint8_t v___x_972_; 
v___x_971_ = 47;
v___x_972_ = lean_uint32_to_uint8(v___x_971_);
return v___x_972_;
}
}
static uint8_t _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1(void){
_start:
{
uint32_t v___x_973_; uint8_t v___x_974_; 
v___x_973_ = 63;
v___x_974_ = lean_uint32_to_uint8(v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedFragment_encode___lam__0(uint8_t v___y_975_){
_start:
{
uint8_t v___y_977_; uint8_t v___y_983_; uint8_t v___y_989_; uint8_t v___y_1009_; uint8_t v___y_1015_; uint8_t v___y_1021_; uint8_t v___y_1027_; uint8_t v___y_1033_; uint8_t v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1039_ = lean_uint8_dec_le(v___x_1038_, v___y_975_);
if (v___x_1039_ == 0)
{
v___y_1033_ = v___x_1039_;
goto v___jp_1032_;
}
else
{
uint8_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1041_ = lean_uint8_dec_le(v___y_975_, v___x_1040_);
v___y_1033_ = v___x_1041_;
goto v___jp_1032_;
}
v___jp_976_:
{
if (v___y_977_ == 0)
{
uint8_t v___x_978_; uint8_t v___x_979_; 
v___x_978_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0);
v___x_979_ = lean_uint8_dec_eq(v___y_975_, v___x_978_);
if (v___x_979_ == 0)
{
uint8_t v___x_980_; uint8_t v___x_981_; 
v___x_980_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1);
v___x_981_ = lean_uint8_dec_eq(v___y_975_, v___x_980_);
return v___x_981_;
}
else
{
return v___x_979_;
}
}
else
{
return v___y_977_;
}
}
v___jp_982_:
{
if (v___y_983_ == 0)
{
uint8_t v___x_984_; uint8_t v___x_985_; 
v___x_984_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_985_ = lean_uint8_dec_eq(v___y_975_, v___x_984_);
if (v___x_985_ == 0)
{
uint8_t v___x_986_; uint8_t v___x_987_; 
v___x_986_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_987_ = lean_uint8_dec_eq(v___y_975_, v___x_986_);
v___y_977_ = v___x_987_;
goto v___jp_976_;
}
else
{
v___y_977_ = v___x_985_;
goto v___jp_976_;
}
}
else
{
return v___y_983_;
}
}
v___jp_988_:
{
if (v___y_989_ == 0)
{
uint8_t v___x_990_; uint8_t v___x_991_; 
v___x_990_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_991_ = lean_uint8_dec_eq(v___y_975_, v___x_990_);
if (v___x_991_ == 0)
{
uint8_t v___x_992_; uint8_t v___x_993_; 
v___x_992_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_993_ = lean_uint8_dec_eq(v___y_975_, v___x_992_);
if (v___x_993_ == 0)
{
uint8_t v___x_994_; uint8_t v___x_995_; 
v___x_994_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_995_ = lean_uint8_dec_eq(v___y_975_, v___x_994_);
if (v___x_995_ == 0)
{
uint8_t v___x_996_; uint8_t v___x_997_; 
v___x_996_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_997_ = lean_uint8_dec_eq(v___y_975_, v___x_996_);
if (v___x_997_ == 0)
{
uint8_t v___x_998_; uint8_t v___x_999_; 
v___x_998_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_999_ = lean_uint8_dec_eq(v___y_975_, v___x_998_);
if (v___x_999_ == 0)
{
uint8_t v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1001_ = lean_uint8_dec_eq(v___y_975_, v___x_1000_);
if (v___x_1001_ == 0)
{
uint8_t v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1003_ = lean_uint8_dec_eq(v___y_975_, v___x_1002_);
if (v___x_1003_ == 0)
{
uint8_t v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1005_ = lean_uint8_dec_eq(v___y_975_, v___x_1004_);
if (v___x_1005_ == 0)
{
uint8_t v___x_1006_; uint8_t v___x_1007_; 
v___x_1006_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1007_ = lean_uint8_dec_eq(v___y_975_, v___x_1006_);
v___y_983_ = v___x_1007_;
goto v___jp_982_;
}
else
{
v___y_983_ = v___x_1005_;
goto v___jp_982_;
}
}
else
{
v___y_983_ = v___x_1003_;
goto v___jp_982_;
}
}
else
{
v___y_983_ = v___x_1001_;
goto v___jp_982_;
}
}
else
{
v___y_983_ = v___x_999_;
goto v___jp_982_;
}
}
else
{
v___y_983_ = v___x_997_;
goto v___jp_982_;
}
}
else
{
v___y_983_ = v___x_995_;
goto v___jp_982_;
}
}
else
{
v___y_983_ = v___x_993_;
goto v___jp_982_;
}
}
else
{
v___y_983_ = v___x_991_;
goto v___jp_982_;
}
}
else
{
return v___y_989_;
}
}
v___jp_1008_:
{
if (v___y_1009_ == 0)
{
uint8_t v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1011_ = lean_uint8_dec_eq(v___y_975_, v___x_1010_);
if (v___x_1011_ == 0)
{
uint8_t v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1013_ = lean_uint8_dec_eq(v___y_975_, v___x_1012_);
v___y_989_ = v___x_1013_;
goto v___jp_988_;
}
else
{
v___y_989_ = v___x_1011_;
goto v___jp_988_;
}
}
else
{
return v___y_1009_;
}
}
v___jp_1014_:
{
if (v___y_1015_ == 0)
{
uint8_t v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1017_ = lean_uint8_dec_eq(v___y_975_, v___x_1016_);
if (v___x_1017_ == 0)
{
uint8_t v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1019_ = lean_uint8_dec_eq(v___y_975_, v___x_1018_);
v___y_1009_ = v___x_1019_;
goto v___jp_1008_;
}
else
{
v___y_1009_ = v___x_1017_;
goto v___jp_1008_;
}
}
else
{
return v___y_1015_;
}
}
v___jp_1020_:
{
if (v___y_1021_ == 0)
{
uint8_t v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1023_ = lean_uint8_dec_eq(v___y_975_, v___x_1022_);
if (v___x_1023_ == 0)
{
uint8_t v___x_1024_; uint8_t v___x_1025_; 
v___x_1024_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1025_ = lean_uint8_dec_eq(v___y_975_, v___x_1024_);
v___y_1015_ = v___x_1025_;
goto v___jp_1014_;
}
else
{
v___y_1015_ = v___x_1023_;
goto v___jp_1014_;
}
}
else
{
return v___y_1021_;
}
}
v___jp_1026_:
{
if (v___y_1027_ == 0)
{
uint8_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1029_ = lean_uint8_dec_le(v___x_1028_, v___y_975_);
if (v___x_1029_ == 0)
{
v___y_1021_ = v___x_1029_;
goto v___jp_1020_;
}
else
{
uint8_t v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1031_ = lean_uint8_dec_le(v___y_975_, v___x_1030_);
v___y_1021_ = v___x_1031_;
goto v___jp_1020_;
}
}
else
{
return v___y_1027_;
}
}
v___jp_1032_:
{
if (v___y_1033_ == 0)
{
uint8_t v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1035_ = lean_uint8_dec_le(v___x_1034_, v___y_975_);
if (v___x_1035_ == 0)
{
v___y_1027_ = v___x_1035_;
goto v___jp_1026_;
}
else
{
uint8_t v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1037_ = lean_uint8_dec_le(v___y_975_, v___x_1036_);
v___y_1027_ = v___x_1037_;
goto v___jp_1026_;
}
}
else
{
return v___y_1033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___lam__0___boxed(lean_object* v___y_1042_){
_start:
{
uint8_t v___y_312__boxed_1043_; uint8_t v_res_1044_; lean_object* v_r_1045_; 
v___y_312__boxed_1043_ = lean_unbox(v___y_1042_);
v_res_1044_ = l_Std_Http_URI_EncodedFragment_encode___lam__0(v___y_312__boxed_1043_);
v_r_1045_ = lean_box(v_res_1044_);
return v_r_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object* v_s_1047_){
_start:
{
lean_object* v___f_1048_; lean_object* v___x_1049_; 
v___f_1048_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1049_ = l_Std_Http_URI_EncodedString_encode(v___f_1048_, v_s_1047_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_encode___boxed(lean_object* v_s_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Std_Http_URI_EncodedFragment_encode(v_s_1050_);
lean_dec_ref(v_s_1050_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object* v_ba_1052_){
_start:
{
lean_object* v___f_1053_; lean_object* v___x_1054_; 
v___f_1053_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1054_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1053_, v_ba_1052_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x21(lean_object* v_ba_1055_){
_start:
{
lean_object* v___f_1056_; lean_object* v___x_1057_; 
v___f_1056_ = ((lean_object*)(l_Std_Http_URI_EncodedFragment_encode___closed__0));
v___x_1057_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1056_, v_ba_1055_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object* v_fragment_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Std_Http_URI_EncodedString_decode___redArg(v_fragment_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedFragment_decode___boxed(lean_object* v_fragment_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Std_Http_URI_EncodedFragment_decode(v_fragment_1060_);
lean_dec_ref(v_fragment_1060_);
return v_res_1061_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedUserInfo_encode___lam__0(uint8_t v___y_1062_){
_start:
{
uint8_t v___y_1064_; uint8_t v___y_1068_; uint8_t v___y_1088_; uint8_t v___y_1094_; uint8_t v___y_1100_; uint8_t v___y_1106_; uint8_t v___y_1112_; uint8_t v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1118_ = lean_uint8_dec_le(v___x_1117_, v___y_1062_);
if (v___x_1118_ == 0)
{
v___y_1112_ = v___x_1118_;
goto v___jp_1111_;
}
else
{
uint8_t v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1120_ = lean_uint8_dec_le(v___y_1062_, v___x_1119_);
v___y_1112_ = v___x_1120_;
goto v___jp_1111_;
}
v___jp_1063_:
{
if (v___y_1064_ == 0)
{
uint8_t v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_1066_ = lean_uint8_dec_eq(v___y_1062_, v___x_1065_);
return v___x_1066_;
}
else
{
return v___y_1064_;
}
}
v___jp_1067_:
{
if (v___y_1068_ == 0)
{
uint8_t v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1070_ = lean_uint8_dec_eq(v___y_1062_, v___x_1069_);
if (v___x_1070_ == 0)
{
uint8_t v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_1072_ = lean_uint8_dec_eq(v___y_1062_, v___x_1071_);
if (v___x_1072_ == 0)
{
uint8_t v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1074_ = lean_uint8_dec_eq(v___y_1062_, v___x_1073_);
if (v___x_1074_ == 0)
{
uint8_t v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1076_ = lean_uint8_dec_eq(v___y_1062_, v___x_1075_);
if (v___x_1076_ == 0)
{
uint8_t v___x_1077_; uint8_t v___x_1078_; 
v___x_1077_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1078_ = lean_uint8_dec_eq(v___y_1062_, v___x_1077_);
if (v___x_1078_ == 0)
{
uint8_t v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1080_ = lean_uint8_dec_eq(v___y_1062_, v___x_1079_);
if (v___x_1080_ == 0)
{
uint8_t v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1082_ = lean_uint8_dec_eq(v___y_1062_, v___x_1081_);
if (v___x_1082_ == 0)
{
uint8_t v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1084_ = lean_uint8_dec_eq(v___y_1062_, v___x_1083_);
if (v___x_1084_ == 0)
{
uint8_t v___x_1085_; uint8_t v___x_1086_; 
v___x_1085_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1086_ = lean_uint8_dec_eq(v___y_1062_, v___x_1085_);
v___y_1064_ = v___x_1086_;
goto v___jp_1063_;
}
else
{
v___y_1064_ = v___x_1084_;
goto v___jp_1063_;
}
}
else
{
v___y_1064_ = v___x_1082_;
goto v___jp_1063_;
}
}
else
{
v___y_1064_ = v___x_1080_;
goto v___jp_1063_;
}
}
else
{
v___y_1064_ = v___x_1078_;
goto v___jp_1063_;
}
}
else
{
v___y_1064_ = v___x_1076_;
goto v___jp_1063_;
}
}
else
{
v___y_1064_ = v___x_1074_;
goto v___jp_1063_;
}
}
else
{
v___y_1064_ = v___x_1072_;
goto v___jp_1063_;
}
}
else
{
v___y_1064_ = v___x_1070_;
goto v___jp_1063_;
}
}
else
{
return v___y_1068_;
}
}
v___jp_1087_:
{
if (v___y_1088_ == 0)
{
uint8_t v___x_1089_; uint8_t v___x_1090_; 
v___x_1089_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1090_ = lean_uint8_dec_eq(v___y_1062_, v___x_1089_);
if (v___x_1090_ == 0)
{
uint8_t v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1092_ = lean_uint8_dec_eq(v___y_1062_, v___x_1091_);
v___y_1068_ = v___x_1092_;
goto v___jp_1067_;
}
else
{
v___y_1068_ = v___x_1090_;
goto v___jp_1067_;
}
}
else
{
return v___y_1088_;
}
}
v___jp_1093_:
{
if (v___y_1094_ == 0)
{
uint8_t v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1096_ = lean_uint8_dec_eq(v___y_1062_, v___x_1095_);
if (v___x_1096_ == 0)
{
uint8_t v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1098_ = lean_uint8_dec_eq(v___y_1062_, v___x_1097_);
v___y_1088_ = v___x_1098_;
goto v___jp_1087_;
}
else
{
v___y_1088_ = v___x_1096_;
goto v___jp_1087_;
}
}
else
{
return v___y_1094_;
}
}
v___jp_1099_:
{
if (v___y_1100_ == 0)
{
uint8_t v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1102_ = lean_uint8_dec_eq(v___y_1062_, v___x_1101_);
if (v___x_1102_ == 0)
{
uint8_t v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1104_ = lean_uint8_dec_eq(v___y_1062_, v___x_1103_);
v___y_1094_ = v___x_1104_;
goto v___jp_1093_;
}
else
{
v___y_1094_ = v___x_1102_;
goto v___jp_1093_;
}
}
else
{
return v___y_1100_;
}
}
v___jp_1105_:
{
if (v___y_1106_ == 0)
{
uint8_t v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1108_ = lean_uint8_dec_le(v___x_1107_, v___y_1062_);
if (v___x_1108_ == 0)
{
v___y_1100_ = v___x_1108_;
goto v___jp_1099_;
}
else
{
uint8_t v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1110_ = lean_uint8_dec_le(v___y_1062_, v___x_1109_);
v___y_1100_ = v___x_1110_;
goto v___jp_1099_;
}
}
else
{
return v___y_1106_;
}
}
v___jp_1111_:
{
if (v___y_1112_ == 0)
{
uint8_t v___x_1113_; uint8_t v___x_1114_; 
v___x_1113_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1114_ = lean_uint8_dec_le(v___x_1113_, v___y_1062_);
if (v___x_1114_ == 0)
{
v___y_1106_ = v___x_1114_;
goto v___jp_1105_;
}
else
{
uint8_t v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1116_ = lean_uint8_dec_le(v___y_1062_, v___x_1115_);
v___y_1106_ = v___x_1116_;
goto v___jp_1105_;
}
}
else
{
return v___y_1112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___lam__0___boxed(lean_object* v___y_1121_){
_start:
{
uint8_t v___y_271__boxed_1122_; uint8_t v_res_1123_; lean_object* v_r_1124_; 
v___y_271__boxed_1122_ = lean_unbox(v___y_1121_);
v_res_1123_ = l_Std_Http_URI_EncodedUserInfo_encode___lam__0(v___y_271__boxed_1122_);
v_r_1124_ = lean_box(v_res_1123_);
return v_r_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object* v_s_1126_){
_start:
{
lean_object* v___f_1127_; lean_object* v___x_1128_; 
v___f_1127_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1128_ = l_Std_Http_URI_EncodedString_encode(v___f_1127_, v_s_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_encode___boxed(lean_object* v_s_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Std_Http_URI_EncodedUserInfo_encode(v_s_1129_);
lean_dec_ref(v_s_1129_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object* v_ba_1131_){
_start:
{
lean_object* v___f_1132_; lean_object* v___x_1133_; 
v___f_1132_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1133_ = l_Std_Http_URI_EncodedString_ofByteArray_x3f(v___f_1132_, v_ba_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x21(lean_object* v_ba_1134_){
_start:
{
lean_object* v___f_1135_; lean_object* v___x_1136_; 
v___f_1135_ = ((lean_object*)(l_Std_Http_URI_EncodedUserInfo_encode___closed__0));
v___x_1136_ = l_Std_Http_URI_EncodedString_ofByteArray_x21(v___f_1135_, v_ba_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode(lean_object* v_userInfo_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Std_Http_URI_EncodedString_decode___redArg(v_userInfo_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedUserInfo_decode___boxed(lean_object* v_userInfo_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Std_Http_URI_EncodedUserInfo_decode(v_userInfo_1139_);
lean_dec_ref(v_userInfo_1139_);
return v_res_1140_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_EncodedQueryParam_encode___lam__0(uint8_t v___y_1141_){
_start:
{
uint8_t v___y_1150_; uint8_t v___y_1152_; uint8_t v___y_1158_; uint8_t v___y_1164_; uint8_t v___y_1184_; uint8_t v___y_1190_; uint8_t v___y_1196_; uint8_t v___y_1202_; uint8_t v___y_1208_; uint8_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__5, &l_Std_Http_URI_isEncodedChar___closed__5_once, _init_l_Std_Http_URI_isEncodedChar___closed__5);
v___x_1214_ = lean_uint8_dec_le(v___x_1213_, v___y_1141_);
if (v___x_1214_ == 0)
{
v___y_1208_ = v___x_1214_;
goto v___jp_1207_;
}
else
{
uint8_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__6, &l_Std_Http_URI_isEncodedChar___closed__6_once, _init_l_Std_Http_URI_isEncodedChar___closed__6);
v___x_1216_ = lean_uint8_dec_le(v___y_1141_, v___x_1215_);
v___y_1208_ = v___x_1216_;
goto v___jp_1207_;
}
v___jp_1142_:
{
uint8_t v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1144_ = lean_uint8_dec_eq(v___y_1141_, v___x_1143_);
if (v___x_1144_ == 0)
{
uint8_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1146_ = lean_uint8_dec_eq(v___y_1141_, v___x_1145_);
if (v___x_1146_ == 0)
{
uint8_t v___x_1147_; 
v___x_1147_ = 1;
return v___x_1147_;
}
else
{
return v___x_1144_;
}
}
else
{
uint8_t v___x_1148_; 
v___x_1148_ = 0;
return v___x_1148_;
}
}
v___jp_1149_:
{
if (v___y_1150_ == 0)
{
return v___y_1150_;
}
else
{
goto v___jp_1142_;
}
}
v___jp_1151_:
{
if (v___y_1152_ == 0)
{
uint8_t v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__0);
v___x_1154_ = lean_uint8_dec_eq(v___y_1141_, v___x_1153_);
if (v___x_1154_ == 0)
{
uint8_t v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_uint8_once(&l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedFragment_encode___lam__0___closed__1);
v___x_1156_ = lean_uint8_dec_eq(v___y_1141_, v___x_1155_);
v___y_1150_ = v___x_1156_;
goto v___jp_1149_;
}
else
{
v___y_1150_ = v___x_1154_;
goto v___jp_1149_;
}
}
else
{
goto v___jp_1142_;
}
}
v___jp_1157_:
{
if (v___y_1158_ == 0)
{
uint8_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__0);
v___x_1160_ = lean_uint8_dec_eq(v___y_1141_, v___x_1159_);
if (v___x_1160_ == 0)
{
uint8_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__1);
v___x_1162_ = lean_uint8_dec_eq(v___y_1141_, v___x_1161_);
v___y_1152_ = v___x_1162_;
goto v___jp_1151_;
}
else
{
v___y_1152_ = v___x_1160_;
goto v___jp_1151_;
}
}
else
{
goto v___jp_1142_;
}
}
v___jp_1163_:
{
if (v___y_1164_ == 0)
{
uint8_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__2);
v___x_1166_ = lean_uint8_dec_eq(v___y_1141_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint8_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__3);
v___x_1168_ = lean_uint8_dec_eq(v___y_1141_, v___x_1167_);
if (v___x_1168_ == 0)
{
uint8_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__4);
v___x_1170_ = lean_uint8_dec_eq(v___y_1141_, v___x_1169_);
if (v___x_1170_ == 0)
{
uint8_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__5);
v___x_1172_ = lean_uint8_dec_eq(v___y_1141_, v___x_1171_);
if (v___x_1172_ == 0)
{
uint8_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__6);
v___x_1174_ = lean_uint8_dec_eq(v___y_1141_, v___x_1173_);
if (v___x_1174_ == 0)
{
uint8_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = lean_uint8_once(&l_Std_Http_URI_isEncodedQueryChar___closed__0, &l_Std_Http_URI_isEncodedQueryChar___closed__0_once, _init_l_Std_Http_URI_isEncodedQueryChar___closed__0);
v___x_1176_ = lean_uint8_dec_eq(v___y_1141_, v___x_1175_);
if (v___x_1176_ == 0)
{
uint8_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__7);
v___x_1178_ = lean_uint8_dec_eq(v___y_1141_, v___x_1177_);
if (v___x_1178_ == 0)
{
uint8_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__8);
v___x_1180_ = lean_uint8_dec_eq(v___y_1141_, v___x_1179_);
if (v___x_1180_ == 0)
{
uint8_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__9);
v___x_1182_ = lean_uint8_dec_eq(v___y_1141_, v___x_1181_);
v___y_1158_ = v___x_1182_;
goto v___jp_1157_;
}
else
{
v___y_1158_ = v___x_1180_;
goto v___jp_1157_;
}
}
else
{
v___y_1158_ = v___x_1178_;
goto v___jp_1157_;
}
}
else
{
v___y_1158_ = v___x_1176_;
goto v___jp_1157_;
}
}
else
{
v___y_1158_ = v___x_1174_;
goto v___jp_1157_;
}
}
else
{
v___y_1158_ = v___x_1172_;
goto v___jp_1157_;
}
}
else
{
v___y_1158_ = v___x_1170_;
goto v___jp_1157_;
}
}
else
{
v___y_1158_ = v___x_1168_;
goto v___jp_1157_;
}
}
else
{
v___y_1158_ = v___x_1166_;
goto v___jp_1157_;
}
}
else
{
goto v___jp_1142_;
}
}
v___jp_1183_:
{
if (v___y_1184_ == 0)
{
uint8_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__10);
v___x_1186_ = lean_uint8_dec_eq(v___y_1141_, v___x_1185_);
if (v___x_1186_ == 0)
{
uint8_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__11);
v___x_1188_ = lean_uint8_dec_eq(v___y_1141_, v___x_1187_);
v___y_1164_ = v___x_1188_;
goto v___jp_1163_;
}
else
{
v___y_1164_ = v___x_1186_;
goto v___jp_1163_;
}
}
else
{
goto v___jp_1142_;
}
}
v___jp_1189_:
{
if (v___y_1190_ == 0)
{
uint8_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__12);
v___x_1192_ = lean_uint8_dec_eq(v___y_1141_, v___x_1191_);
if (v___x_1192_ == 0)
{
uint8_t v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__13);
v___x_1194_ = lean_uint8_dec_eq(v___y_1141_, v___x_1193_);
v___y_1184_ = v___x_1194_;
goto v___jp_1183_;
}
else
{
v___y_1184_ = v___x_1192_;
goto v___jp_1183_;
}
}
else
{
goto v___jp_1142_;
}
}
v___jp_1195_:
{
if (v___y_1196_ == 0)
{
uint8_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__14);
v___x_1198_ = lean_uint8_dec_eq(v___y_1141_, v___x_1197_);
if (v___x_1198_ == 0)
{
uint8_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__15);
v___x_1200_ = lean_uint8_dec_eq(v___y_1141_, v___x_1199_);
v___y_1190_ = v___x_1200_;
goto v___jp_1189_;
}
else
{
v___y_1190_ = v___x_1198_;
goto v___jp_1189_;
}
}
else
{
goto v___jp_1142_;
}
}
v___jp_1201_:
{
if (v___y_1202_ == 0)
{
uint8_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__1, &l_Std_Http_URI_isEncodedChar___closed__1_once, _init_l_Std_Http_URI_isEncodedChar___closed__1);
v___x_1204_ = lean_uint8_dec_le(v___x_1203_, v___y_1141_);
if (v___x_1204_ == 0)
{
v___y_1196_ = v___x_1204_;
goto v___jp_1195_;
}
else
{
uint8_t v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__16);
v___x_1206_ = lean_uint8_dec_le(v___y_1141_, v___x_1205_);
v___y_1196_ = v___x_1206_;
goto v___jp_1195_;
}
}
else
{
goto v___jp_1142_;
}
}
v___jp_1207_:
{
if (v___y_1208_ == 0)
{
uint8_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = lean_uint8_once(&l_Std_Http_URI_isEncodedChar___closed__3, &l_Std_Http_URI_isEncodedChar___closed__3_once, _init_l_Std_Http_URI_isEncodedChar___closed__3);
v___x_1210_ = lean_uint8_dec_le(v___x_1209_, v___y_1141_);
if (v___x_1210_ == 0)
{
v___y_1202_ = v___x_1210_;
goto v___jp_1201_;
}
else
{
uint8_t v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = lean_uint8_once(&l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17, &l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17_once, _init_l_Std_Http_URI_EncodedSegment_encode___lam__0___closed__17);
v___x_1212_ = lean_uint8_dec_le(v___y_1141_, v___x_1211_);
v___y_1202_ = v___x_1212_;
goto v___jp_1201_;
}
}
else
{
goto v___jp_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___lam__0___boxed(lean_object* v___y_1217_){
_start:
{
uint8_t v___y_362__boxed_1218_; uint8_t v_res_1219_; lean_object* v_r_1220_; 
v___y_362__boxed_1218_ = lean_unbox(v___y_1217_);
v_res_1219_ = l_Std_Http_URI_EncodedQueryParam_encode___lam__0(v___y_362__boxed_1218_);
v_r_1220_ = lean_box(v_res_1219_);
return v_r_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode(lean_object* v_s_1222_){
_start:
{
lean_object* v___f_1223_; lean_object* v___x_1224_; 
v___f_1223_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1224_ = l_Std_Http_URI_EncodedQueryString_encode(v_s_1222_, v___f_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_encode___boxed(lean_object* v_s_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Std_Http_URI_EncodedQueryParam_encode(v_s_1225_);
lean_dec_ref(v_s_1225_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x3f(lean_object* v_ba_1227_){
_start:
{
lean_object* v___f_1228_; lean_object* v___x_1229_; 
v___f_1228_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1229_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x3f(v_ba_1227_, v___f_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_ofByteArray_x21(lean_object* v_ba_1230_){
_start:
{
lean_object* v___f_1231_; lean_object* v___x_1232_; 
v___f_1231_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1232_ = l_Std_Http_URI_EncodedQueryString_ofByteArray_x21(v_ba_1230_, v___f_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object* v_s_1233_){
_start:
{
lean_object* v___f_1234_; lean_object* v___x_1235_; 
v___f_1234_ = ((lean_object*)(l_Std_Http_URI_EncodedQueryParam_encode___closed__0));
v___x_1235_ = l_Std_Http_URI_EncodedQueryString_ofString_x3f(v_s_1233_, v___f_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f___boxed(lean_object* v_s_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_s_1236_);
lean_dec_ref(v_s_1236_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object* v_param_1238_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Std_Http_URI_EncodedQueryString_decode___redArg(v_param_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_EncodedQueryParam_decode___boxed(lean_object* v_param_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Std_Http_URI_EncodedQueryParam_decode(v_param_1240_);
lean_dec_ref(v_param_1240_);
return v_res_1241_;
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
