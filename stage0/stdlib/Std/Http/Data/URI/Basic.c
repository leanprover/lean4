// Lean compiler output
// Module: Std.Http.Data.URI.Basic
// Imports: import Init.Data.ToString import Std.Data.HashSet.Basic public import Std.Net public import Std.Http.Internal public import Std.Http.Data.URI.Encoding public import Init.Data.String.Search public import Init.Data.String.Length
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t l_Std_Http_Internal_instDecidableIsLowerCase(lean_object*);
lean_object* l_String_toListImpl(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_sarray_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Std_Net_instDecidableEqIPv4Addr_decEq(lean_object*, lean_object*);
uint8_t l_Std_Net_instDecidableEqIPv6Addr_decEq(lean_object*, lean_object*);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_uv_ntop_v4(lean_object*);
lean_object* lean_uv_ntop_v6(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Std_Http_URI_EncodedSegment_encode(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_ByteArray_empty;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_Http_URI_EncodedQueryParam_encode(lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Std_Http_URI_EncodedQueryString_decodesTo___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_pton_v4(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_getLast_x3f___redArg(lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Http_Internal_Char_isUserInfoChar___boxed(lean_object*);
lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object*);
extern lean_object* l_Std_Net_instInhabitedIPv4Addr_default;
lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Option_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_EncodedUserInfo_decode(lean_object*);
lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object*);
lean_object* l_Std_Http_URI_EncodedString_encodeEscaping(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object*);
lean_object* l_ByteArray_decEq___boxed(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
static const lean_string_object l_Std_Http_URI_instInhabitedScheme___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "http"};
static const lean_object* l_Std_Http_URI_instInhabitedScheme___closed__0 = (const lean_object*)&l_Std_Http_URI_instInhabitedScheme___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instInhabitedScheme = (const lean_object*)&l_Std_Http_URI_instInhabitedScheme___closed__0_value;
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(lean_object*);
static const lean_string_object l_Std_Http_URI_Scheme_ofString_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Http.Data.URI.Basic"};
static const lean_object* l_Std_Http_URI_Scheme_ofString_x21___closed__0 = (const lean_object*)&l_Std_Http_URI_Scheme_ofString_x21___closed__0_value;
static const lean_string_object l_Std_Http_URI_Scheme_ofString_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Std.Http.URI.Scheme.ofString!"};
static const lean_object* l_Std_Http_URI_Scheme_ofString_x21___closed__1 = (const lean_object*)&l_Std_Http_URI_Scheme_ofString_x21___closed__1_value;
static const lean_string_object l_Std_Http_URI_Scheme_ofString_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid URI scheme: "};
static const lean_object* l_Std_Http_URI_Scheme_ofString_x21___closed__2 = (const lean_object*)&l_Std_Http_URI_Scheme_ofString_x21___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x21(lean_object*);
static const lean_string_object l_Std_Http_URI_Scheme_defaultPort___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "https"};
static const lean_object* l_Std_Http_URI_Scheme_defaultPort___closed__0 = (const lean_object*)&l_Std_Http_URI_Scheme_defaultPort___closed__0_value;
LEAN_EXPORT uint16_t l_Std_Http_URI_Scheme_defaultPort(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_defaultPort___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofPort(uint16_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofPort___boxed(lean_object*);
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instInhabitedUserInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_URI_instInhabitedUserInfo_default;
LEAN_EXPORT lean_object* l_Std_Http_URI_instInhabitedUserInfo;
static const lean_string_object l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_URI_instReprUserInfo_repr_spec__1(lean_object*);
static const lean_string_object l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "username"};
static const lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__4 = (const lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__3_value),((lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__6 = (const lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7;
static const lean_string_object l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__8 = (const lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9 = (const lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "password"};
static const lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__10 = (const lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__11 = (const lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__11_value;
static const lean_string_object l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__12 = (const lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__12_value;
static lean_once_cell_t l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13;
static lean_once_cell_t l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14;
static const lean_ctor_object l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15 = (const lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15_value;
static const lean_ctor_object l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__12_value)}};
static const lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16 = (const lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instReprUserInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instReprUserInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instReprUserInfo___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprUserInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instReprUserInfo = (const lean_object*)&l_Std_Http_URI_instReprUserInfo___closed__0_value;
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqUserInfo_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqUserInfo_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instBEqUserInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instBEqUserInfo_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instBEqUserInfo___closed__0 = (const lean_object*)&l_Std_Http_URI_instBEqUserInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instBEqUserInfo = (const lean_object*)&l_Std_Http_URI_instBEqUserInfo___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_URI_UserInfo_ofStrings___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_UserInfo_ofStrings___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_UserInfo_ofStrings___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_UserInfo_ofStrings___closed__0 = (const lean_object*)&l_Std_Http_URI_UserInfo_ofStrings___closed__0_value;
static const lean_closure_object l_Std_Http_URI_UserInfo_ofStrings___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_Char_isUserInfoChar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_UserInfo_ofStrings___closed__1 = (const lean_object*)&l_Std_Http_URI_UserInfo_ofStrings___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidDomainLabel___boxed(lean_object*);
static const lean_string_object l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3___redArg___closed__0 = (const lean_object*)&l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___at___00Std_Http_URI_endsInNumber_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___at___00Std_Http_URI_endsInNumber_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_endsInNumber_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_endsInNumber_spec__2___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_endsInNumber_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_endsInNumber_spec__0___boxed(lean_object*);
static const lean_array_object l_Std_Http_URI_endsInNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_URI_endsInNumber___closed__0 = (const lean_object*)&l_Std_Http_URI_endsInNumber___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_endsInNumber___boxed__const__1;
LEAN_EXPORT uint8_t l_Std_Http_URI_endsInNumber(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_endsInNumber___boxed(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_DomainName_ofString_x3f(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_empty_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_empty_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_URI_instInhabitedHost_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instInhabitedHost_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_URI_instInhabitedHost_default;
LEAN_EXPORT lean_object* l_Std_Http_URI_instInhabitedHost;
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqHost_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqHost_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instBEqHost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instBEqHost_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instBEqHost___closed__0 = (const lean_object*)&l_Std_Http_URI_instBEqHost___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instBEqHost = (const lean_object*)&l_Std_Http_URI_instBEqHost___closed__0_value;
static const lean_string_object l_Std_Http_URI_instReprHost___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Std.Http.URI.Host."};
static const lean_object* l_Std_Http_URI_instReprHost___lam__0___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprHost___lam__0___closed__0_value;
static const lean_string_object l_Std_Http_URI_instReprHost___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Std_Http_URI_instReprHost___lam__0___closed__1 = (const lean_object*)&l_Std_Http_URI_instReprHost___lam__0___closed__1_value;
static const lean_string_object l_Std_Http_URI_instReprHost___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ipv4"};
static const lean_object* l_Std_Http_URI_instReprHost___lam__0___closed__2 = (const lean_object*)&l_Std_Http_URI_instReprHost___lam__0___closed__2_value;
static const lean_string_object l_Std_Http_URI_instReprHost___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ipv6"};
static const lean_object* l_Std_Http_URI_instReprHost___lam__0___closed__3 = (const lean_object*)&l_Std_Http_URI_instReprHost___lam__0___closed__3_value;
static const lean_string_object l_Std_Http_URI_instReprHost___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Http.URI.Host.empty"};
static const lean_object* l_Std_Http_URI_instReprHost___lam__0___closed__4 = (const lean_object*)&l_Std_Http_URI_instReprHost___lam__0___closed__4_value;
static const lean_ctor_object l_Std_Http_URI_instReprHost___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprHost___lam__0___closed__4_value)}};
static const lean_object* l_Std_Http_URI_instReprHost___lam__0___closed__5 = (const lean_object*)&l_Std_Http_URI_instReprHost___lam__0___closed__5_value;
static lean_once_cell_t l_Std_Http_URI_instReprHost___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instReprHost___lam__0___closed__6;
static lean_once_cell_t l_Std_Http_URI_instReprHost___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instReprHost___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instReprHost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instReprHost___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instReprHost___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprHost___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instReprHost = (const lean_object*)&l_Std_Http_URI_instReprHost___closed__0_value;
static const lean_string_object l_Std_Http_URI_instToStringHost___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Http_URI_instToStringHost___lam__0___closed__0 = (const lean_object*)&l_Std_Http_URI_instToStringHost___lam__0___closed__0_value;
static const lean_string_object l_Std_Http_URI_instToStringHost___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Http_URI_instToStringHost___lam__0___closed__1 = (const lean_object*)&l_Std_Http_URI_instToStringHost___lam__0___closed__1_value;
static const lean_string_object l_Std_Http_URI_instToStringHost___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_URI_instToStringHost___lam__0___closed__2 = (const lean_object*)&l_Std_Http_URI_instToStringHost___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_instToStringHost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instToStringHost___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instToStringHost___closed__0 = (const lean_object*)&l_Std_Http_URI_instToStringHost___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instToStringHost = (const lean_object*)&l_Std_Http_URI_instToStringHost___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instInhabitedPort_default;
LEAN_EXPORT lean_object* l_Std_Http_URI_instInhabitedPort;
static const lean_string_object l_Std_Http_URI_instReprPort_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Http.URI.Port.empty"};
static const lean_object* l_Std_Http_URI_instReprPort_repr___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprPort_repr___closed__0_value;
static const lean_ctor_object l_Std_Http_URI_instReprPort_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprPort_repr___closed__0_value)}};
static const lean_object* l_Std_Http_URI_instReprPort_repr___closed__1 = (const lean_object*)&l_Std_Http_URI_instReprPort_repr___closed__1_value;
static const lean_string_object l_Std_Http_URI_instReprPort_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Std.Http.URI.Port.omitted"};
static const lean_object* l_Std_Http_URI_instReprPort_repr___closed__2 = (const lean_object*)&l_Std_Http_URI_instReprPort_repr___closed__2_value;
static const lean_ctor_object l_Std_Http_URI_instReprPort_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprPort_repr___closed__2_value)}};
static const lean_object* l_Std_Http_URI_instReprPort_repr___closed__3 = (const lean_object*)&l_Std_Http_URI_instReprPort_repr___closed__3_value;
static const lean_string_object l_Std_Http_URI_instReprPort_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Http.URI.Port.value"};
static const lean_object* l_Std_Http_URI_instReprPort_repr___closed__4 = (const lean_object*)&l_Std_Http_URI_instReprPort_repr___closed__4_value;
static const lean_ctor_object l_Std_Http_URI_instReprPort_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprPort_repr___closed__4_value)}};
static const lean_object* l_Std_Http_URI_instReprPort_repr___closed__5 = (const lean_object*)&l_Std_Http_URI_instReprPort_repr___closed__5_value;
static const lean_ctor_object l_Std_Http_URI_instReprPort_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprPort_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_URI_instReprPort_repr___closed__6 = (const lean_object*)&l_Std_Http_URI_instReprPort_repr___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instReprPort___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instReprPort_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instReprPort___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprPort___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instReprPort = (const lean_object*)&l_Std_Http_URI_instReprPort___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_URI_instInhabitedAuthority_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instInhabitedAuthority_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_URI_instInhabitedAuthority_default;
LEAN_EXPORT lean_object* l_Std_Http_URI_instInhabitedAuthority;
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_URI_instReprAuthority_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "userInfo"};
static const lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_URI_instReprAuthority_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_URI_instReprAuthority_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__2_value),((lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Http_URI_instReprAuthority_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "host"};
static const lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg___closed__4 = (const lean_object*)&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5_value;
static lean_once_cell_t l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6;
static const lean_string_object l_Std_Http_URI_instReprAuthority_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "port"};
static const lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg___closed__7 = (const lean_object*)&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__7_value;
static const lean_ctor_object l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__7_value)}};
static const lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8 = (const lean_object*)&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instReprAuthority___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instReprAuthority_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instReprAuthority___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprAuthority___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instReprAuthority = (const lean_object*)&l_Std_Http_URI_instReprAuthority___closed__0_value;
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqAuthority_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqAuthority_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instBEqAuthority___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instBEqAuthority_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instBEqAuthority___closed__0 = (const lean_object*)&l_Std_Http_URI_instBEqAuthority___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instBEqAuthority = (const lean_object*)&l_Std_Http_URI_instBEqAuthority___closed__0_value;
static const lean_string_object l_Std_Http_URI_instToStringAuthority___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Http_URI_instToStringAuthority___lam__0___closed__0 = (const lean_object*)&l_Std_Http_URI_instToStringAuthority___lam__0___closed__0_value;
static const lean_string_object l_Std_Http_URI_instToStringAuthority___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_Std_Http_URI_instToStringAuthority___lam__0___closed__1 = (const lean_object*)&l_Std_Http_URI_instToStringAuthority___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringAuthority___lam__0(lean_object*);
static const lean_closure_object l_Std_Http_URI_instToStringAuthority___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instToStringAuthority___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instToStringAuthority___closed__0 = (const lean_object*)&l_Std_Http_URI_instToStringAuthority___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instToStringAuthority = (const lean_object*)&l_Std_Http_URI_instToStringAuthority___closed__0_value;
static const lean_array_object l_Std_Http_URI_instInhabitedPath_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_URI_instInhabitedPath_default___closed__0 = (const lean_object*)&l_Std_Http_URI_instInhabitedPath_default___closed__0_value;
static const lean_ctor_object l_Std_Http_URI_instInhabitedPath_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_URI_instInhabitedPath_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_URI_instInhabitedPath_default___closed__1 = (const lean_object*)&l_Std_Http_URI_instInhabitedPath_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instInhabitedPath_default = (const lean_object*)&l_Std_Http_URI_instInhabitedPath_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instInhabitedPath = (const lean_object*)&l_Std_Http_URI_instInhabitedPath_default___closed__1_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1_value;
static lean_once_cell_t l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2;
static lean_once_cell_t l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3;
static const lean_ctor_object l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4_value;
static const lean_ctor_object l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_URI_instToStringHost___lam__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5_value;
static const lean_string_object l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__6 = (const lean_object*)&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__6_value;
static const lean_ctor_object l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__6_value)}};
static const lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Http_URI_instReprPath_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "segments"};
static const lean_object* l_Std_Http_URI_instReprPath_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprPath_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_URI_instReprPath_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprPath_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_URI_instReprPath_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_URI_instReprPath_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_URI_instReprPath_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_URI_instReprPath_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_URI_instReprPath_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_URI_instReprPath_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_URI_instReprPath_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprPath_repr___redArg___closed__2_value),((lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_URI_instReprPath_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_URI_instReprPath_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Http_URI_instReprPath_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "absolute"};
static const lean_object* l_Std_Http_URI_instReprPath_repr___redArg___closed__4 = (const lean_object*)&l_Std_Http_URI_instReprPath_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Http_URI_instReprPath_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprPath_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_URI_instReprPath_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_URI_instReprPath_repr___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instReprPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instReprPath_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instReprPath___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprPath___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instReprPath = (const lean_object*)&l_Std_Http_URI_instReprPath___closed__0_value;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqPath_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqPath_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instBEqPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instBEqPath_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instBEqPath___closed__0 = (const lean_object*)&l_Std_Http_URI_instBEqPath___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instBEqPath = (const lean_object*)&l_Std_Http_URI_instBEqPath___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__0(lean_object*);
static const lean_string_object l_Std_Http_URI_instToStringPath___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Std_Http_URI_instToStringPath___lam__1___closed__0 = (const lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__0_value;
static const lean_closure_object l_Std_Http_URI_instToStringPath___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instToStringPath___lam__1___closed__1 = (const lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__1_value;
static const lean_closure_object l_Std_Http_URI_instToStringPath___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instToStringPath___lam__1___closed__2 = (const lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__2_value;
static const lean_closure_object l_Std_Http_URI_instToStringPath___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instToStringPath___lam__1___closed__3 = (const lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__3_value;
static const lean_closure_object l_Std_Http_URI_instToStringPath___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instToStringPath___lam__1___closed__4 = (const lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__4_value;
static const lean_closure_object l_Std_Http_URI_instToStringPath___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instToStringPath___lam__1___closed__5 = (const lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__5_value;
static const lean_closure_object l_Std_Http_URI_instToStringPath___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instToStringPath___lam__1___closed__6 = (const lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__6_value;
static const lean_closure_object l_Std_Http_URI_instToStringPath___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instToStringPath___lam__1___closed__7 = (const lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__7_value;
static const lean_ctor_object l_Std_Http_URI_instToStringPath___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__1_value),((lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__2_value)}};
static const lean_object* l_Std_Http_URI_instToStringPath___lam__1___closed__8 = (const lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__8_value;
static const lean_ctor_object l_Std_Http_URI_instToStringPath___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__8_value),((lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__3_value),((lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__4_value),((lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__5_value),((lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__6_value)}};
static const lean_object* l_Std_Http_URI_instToStringPath___lam__1___closed__9 = (const lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__9_value;
static const lean_ctor_object l_Std_Http_URI_instToStringPath___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__9_value),((lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__7_value)}};
static const lean_object* l_Std_Http_URI_instToStringPath___lam__1___closed__10 = (const lean_object*)&l_Std_Http_URI_instToStringPath___lam__1___closed__10_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instToStringPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instToStringPath___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instToStringPath___closed__0 = (const lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value;
static const lean_closure_object l_Std_Http_URI_instToStringPath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instToStringPath___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value)} };
static const lean_object* l_Std_Http_URI_instToStringPath___closed__1 = (const lean_object*)&l_Std_Http_URI_instToStringPath___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instToStringPath = (const lean_object*)&l_Std_Http_URI_instToStringPath___closed__1_value;
LEAN_EXPORT uint8_t l_Std_Http_URI_Path_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Path_render_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Path_render_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_render_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_render_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_URI_Path_render___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "./"};
static const lean_object* l_Std_Http_URI_Path_render___closed__0 = (const lean_object*)&l_Std_Http_URI_Path_render___closed__0_value;
static const lean_string_object l_Std_Http_URI_Path_render___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "/."};
static const lean_object* l_Std_Http_URI_Path_render___closed__1 = (const lean_object*)&l_Std_Http_URI_Path_render___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_render(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_render___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parent(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_appendEncoded(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".."};
static const lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_normalize(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_toDecodedSegments(lean_object*);
static const lean_closure_object l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__0_value;
static const lean_closure_object l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_repr___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__0_value)} };
static const lean_object* l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__1 = (const lean_object*)&l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__1_value;
static const lean_closure_object l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprTupleOfRepr___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__1_value)} };
static const lean_object* l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__2 = (const lean_object*)&l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__2_value;
static const lean_closure_object l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Prod_repr___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__0_value),((lean_object*)&l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__2_value)} };
static const lean_object* l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3 = (const lean_object*)&l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instReprQuery___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instReprQuery___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instReprQuery___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprQuery___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instReprQuery = (const lean_object*)&l_Std_Http_URI_instReprQuery___closed__0_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Std_Http_URI_instInhabitedQuery___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_URI_instInhabitedQuery___aux__1___closed__0 = (const lean_object*)&l_Std_Http_URI_instInhabitedQuery___aux__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instInhabitedQuery___aux__1 = (const lean_object*)&l_Std_Http_URI_instInhabitedQuery___aux__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instInhabitedQuery = (const lean_object*)&l_Std_Http_URI_instInhabitedQuery___aux__1___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instBEqQuery___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteArray_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instBEqQuery___aux__1___closed__0 = (const lean_object*)&l_Std_Http_URI_instBEqQuery___aux__1___closed__0_value;
static const lean_closure_object l_Std_Http_URI_instBEqQuery___aux__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instBEqQuery___aux__1___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_URI_instBEqQuery___aux__1___closed__0_value)} };
static const lean_object* l_Std_Http_URI_instBEqQuery___aux__1___closed__1 = (const lean_object*)&l_Std_Http_URI_instBEqQuery___aux__1___closed__1_value;
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instBEqQuery___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instBEqQuery___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instBEqQuery___closed__0 = (const lean_object*)&l_Std_Http_URI_instBEqQuery___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instBEqQuery = (const lean_object*)&l_Std_Http_URI_instBEqQuery___closed__0_value;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_names_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_names_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Http_URI_Query_names___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_URI_Query_names___closed__0 = (const lean_object*)&l_Std_Http_URI_Query_names___closed__0_value;
static lean_once_cell_t l_Std_Http_URI_Query_names___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Query_names___closed__1;
static lean_once_cell_t l_Std_Http_URI_Query_names___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Query_names___closed__2;
static lean_once_cell_t l_Std_Http_URI_Query_names___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Query_names___closed__3;
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_values(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Query_formatQueryParam_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Query_formatQueryParam_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_URI_Query_formatQueryParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l_Std_Http_URI_Query_formatQueryParam___closed__0 = (const lean_object*)&l_Std_Http_URI_Query_formatQueryParam___closed__0_value;
static const lean_string_object l_Std_Http_URI_Query_formatQueryParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "%3D"};
static const lean_object* l_Std_Http_URI_Query_formatQueryParam___closed__1 = (const lean_object*)&l_Std_Http_URI_Query_formatQueryParam___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_find_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Http_URI_Query_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_URI_Query_empty___closed__0 = (const lean_object*)&l_Std_Http_URI_Query_empty___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_Query_empty = (const lean_object*)&l_Std_Http_URI_Query_empty___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_ofList(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_containsEncoded(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_containsEncoded___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_contains_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_erase_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_URI_Query_get___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_instToStringHost___lam__0___closed__2_value)}};
static const lean_object* l_Std_Http_URI_Query_get___closed__0 = (const lean_object*)&l_Std_Http_URI_Query_get___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_URI_Query_toRawString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "&"};
static const lean_object* l_Std_Http_URI_Query_toRawString___closed__0 = (const lean_object*)&l_Std_Http_URI_Query_toRawString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toRawString(lean_object*);
LEAN_EXPORT const lean_object* l_Std_Http_URI_Query_instEmptyCollection = (const lean_object*)&l_Std_Http_URI_Query_empty___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0(lean_object*);
static const lean_closure_object l_Std_Http_URI_Query_instSingletonProdString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_Query_instSingletonProdString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_Query_instSingletonProdString___closed__0 = (const lean_object*)&l_Std_Http_URI_Query_instSingletonProdString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_Query_instSingletonProdString = (const lean_object*)&l_Std_Http_URI_Query_instSingletonProdString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_Query_instInsertProdString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_Query_instInsertProdString___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_Query_instInsertProdString___closed__0 = (const lean_object*)&l_Std_Http_URI_Query_instInsertProdString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_Query_instInsertProdString = (const lean_object*)&l_Std_Http_URI_Query_instInsertProdString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__0(lean_object*);
static const lean_string_object l_Std_Http_URI_Query_instToString___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Std_Http_URI_Query_instToString___lam__1___closed__0 = (const lean_object*)&l_Std_Http_URI_Query_instToString___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_Query_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_Query_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_Query_instToString___closed__0 = (const lean_object*)&l_Std_Http_URI_Query_instToString___closed__0_value;
static const lean_closure_object l_Std_Http_URI_Query_instToString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_Query_instToString___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_URI_Query_instToString___closed__0_value)} };
static const lean_object* l_Std_Http_URI_Query_instToString___closed__1 = (const lean_object*)&l_Std_Http_URI_Query_instToString___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_Query_instToString = (const lean_object*)&l_Std_Http_URI_Query_instToString___closed__1_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatOption(lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_instReprURI_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scheme"};
static const lean_object* l_Std_Http_instReprURI_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_instReprURI_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_instReprURI_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_instReprURI_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_instReprURI_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_instReprURI_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__2_value),((lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_instReprURI_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__3_value;
static lean_once_cell_t l_Std_Http_instReprURI_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instReprURI_repr___redArg___closed__4;
static const lean_string_object l_Std_Http_instReprURI_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "authority"};
static const lean_object* l_Std_Http_instReprURI_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Http_instReprURI_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_instReprURI_repr___redArg___closed__6 = (const lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Http_instReprURI_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instReprURI_repr___redArg___closed__7;
static const lean_string_object l_Std_Http_instReprURI_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "path"};
static const lean_object* l_Std_Http_instReprURI_repr___redArg___closed__8 = (const lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Http_instReprURI_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Http_instReprURI_repr___redArg___closed__9 = (const lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Http_instReprURI_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "query"};
static const lean_object* l_Std_Http_instReprURI_repr___redArg___closed__10 = (const lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Http_instReprURI_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Http_instReprURI_repr___redArg___closed__11 = (const lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__11_value;
static lean_once_cell_t l_Std_Http_instReprURI_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instReprURI_repr___redArg___closed__12;
static const lean_string_object l_Std_Http_instReprURI_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fragment"};
static const lean_object* l_Std_Http_instReprURI_repr___redArg___closed__13 = (const lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__13_value;
static const lean_ctor_object l_Std_Http_instReprURI_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__13_value)}};
static const lean_object* l_Std_Http_instReprURI_repr___redArg___closed__14 = (const lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__14_value;
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instReprURI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instReprURI_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instReprURI___closed__0 = (const lean_object*)&l_Std_Http_instReprURI___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instReprURI = (const lean_object*)&l_Std_Http_instReprURI___closed__0_value;
static const lean_ctor_object l_Std_Http_instInhabitedURI_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_URI_instInhabitedScheme___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_URI_instInhabitedPath_default___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_instInhabitedURI_default___closed__0 = (const lean_object*)&l_Std_Http_instInhabitedURI_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instInhabitedURI_default = (const lean_object*)&l_Std_Http_instInhabitedURI_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instInhabitedURI = (const lean_object*)&l_Std_Http_instInhabitedURI_default___closed__0_value;
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instBEqURI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instBEqURI_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instBEqURI___closed__0 = (const lean_object*)&l_Std_Http_instBEqURI___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instBEqURI = (const lean_object*)&l_Std_Http_instBEqURI___closed__0_value;
static const lean_string_object l_Std_Http_instToStringURI___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Std_Http_instToStringURI___lam__0___closed__0 = (const lean_object*)&l_Std_Http_instToStringURI___lam__0___closed__0_value;
static const lean_string_object l_Std_Http_instToStringURI___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "//"};
static const lean_object* l_Std_Http_instToStringURI___lam__0___closed__1 = (const lean_object*)&l_Std_Http_instToStringURI___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__0(lean_object*);
static const lean_closure_object l_Std_Http_instToStringURI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instToStringURI___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instToStringURI___closed__0 = (const lean_object*)&l_Std_Http_instToStringURI___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instToStringURI = (const lean_object*)&l_Std_Http_instToStringURI___closed__0_value;
static const lean_array_object l_Std_Http_URI_instInhabitedBuilder_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_URI_instInhabitedBuilder_default___closed__0 = (const lean_object*)&l_Std_Http_URI_instInhabitedBuilder_default___closed__0_value;
static const lean_ctor_object l_Std_Http_URI_instInhabitedBuilder_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_URI_instInhabitedBuilder_default___closed__0_value),((lean_object*)&l_Std_Http_URI_instInhabitedBuilder_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_URI_instInhabitedBuilder_default___closed__1 = (const lean_object*)&l_Std_Http_URI_instInhabitedBuilder_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instInhabitedBuilder_default = (const lean_object*)&l_Std_Http_URI_instInhabitedBuilder_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instInhabitedBuilder = (const lean_object*)&l_Std_Http_URI_instInhabitedBuilder_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_Builder_empty = (const lean_object*)&l_Std_Http_URI_instInhabitedBuilder_default___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(lean_object*);
static const lean_string_object l_Std_Http_URI_Builder_setScheme_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Http.URI.Builder.setScheme!"};
static const lean_object* l_Std_Http_URI_Builder_setScheme_x21___closed__0 = (const lean_object*)&l_Std_Http_URI_Builder_setScheme_x21___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x21(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_Builder_setUserInfo___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_Builder_setUserInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_Builder_setUserInfo___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_Builder_setUserInfo___closed__0 = (const lean_object*)&l_Std_Http_URI_Builder_setUserInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x3f(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_URI_Builder_setHost_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Std.Http.URI.Builder.setHost!"};
static const lean_object* l_Std_Http_URI_Builder_setHost_x21___closed__0 = (const lean_object*)&l_Std_Http_URI_Builder_setHost_x21___closed__0_value;
static const lean_string_object l_Std_Http_URI_Builder_setHost_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "invalid host: "};
static const lean_object* l_Std_Http_URI_Builder_setHost_x21___closed__1 = (const lean_object*)&l_Std_Http_URI_Builder_setHost_x21___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_appendPathSegment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryParam(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryFlag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setQuery(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setFragment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_build(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_withScheme_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_withAuthority(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_withPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_withQuery(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_withFragment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instReprOrigin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instReprOrigin_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instReprOrigin___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprOrigin___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instReprOrigin = (const lean_object*)&l_Std_Http_URI_instReprOrigin___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqOrigin_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqOrigin_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instBEqOrigin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instBEqOrigin_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instBEqOrigin___closed__0 = (const lean_object*)&l_Std_Http_URI_instBEqOrigin___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instBEqOrigin = (const lean_object*)&l_Std_Http_URI_instBEqOrigin___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Origin_hostHeader(lean_object*);
static const lean_ctor_object l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_instReprURI_repr___redArg___closed__6_value)}};
static const lean_object* l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__0_value),((lean_object*)&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instReprRelativeRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instReprRelativeRef_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instReprRelativeRef___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprRelativeRef___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instReprRelativeRef = (const lean_object*)&l_Std_Http_URI_instReprRelativeRef___closed__0_value;
static const lean_ctor_object l_Std_Http_URI_instInhabitedRelativeRef_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_URI_instInhabitedPath_default___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_URI_instInhabitedRelativeRef_default___closed__0 = (const lean_object*)&l_Std_Http_URI_instInhabitedRelativeRef_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instInhabitedRelativeRef_default = (const lean_object*)&l_Std_Http_URI_instInhabitedRelativeRef_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instInhabitedRelativeRef = (const lean_object*)&l_Std_Http_URI_instInhabitedRelativeRef_default___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqRelativeRef_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqRelativeRef_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instBEqRelativeRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instBEqRelativeRef_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instBEqRelativeRef___closed__0 = (const lean_object*)&l_Std_Http_URI_instBEqRelativeRef___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instBEqRelativeRef = (const lean_object*)&l_Std_Http_URI_instBEqRelativeRef___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_instToStringRelativeRef___lam__0(lean_object*);
static const lean_closure_object l_Std_Http_instToStringRelativeRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instToStringRelativeRef___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instToStringRelativeRef___closed__0 = (const lean_object*)&l_Std_Http_instToStringRelativeRef___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instToStringRelativeRef = (const lean_object*)&l_Std_Http_instToStringRelativeRef___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_instReprURIReference_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Std.Http.URIReference.absolute"};
static const lean_object* l_Std_Http_instReprURIReference_repr___closed__0 = (const lean_object*)&l_Std_Http_instReprURIReference_repr___closed__0_value;
static const lean_ctor_object l_Std_Http_instReprURIReference_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprURIReference_repr___closed__0_value)}};
static const lean_object* l_Std_Http_instReprURIReference_repr___closed__1 = (const lean_object*)&l_Std_Http_instReprURIReference_repr___closed__1_value;
static const lean_ctor_object l_Std_Http_instReprURIReference_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_instReprURIReference_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_instReprURIReference_repr___closed__2 = (const lean_object*)&l_Std_Http_instReprURIReference_repr___closed__2_value;
static const lean_string_object l_Std_Http_instReprURIReference_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Std.Http.URIReference.relative"};
static const lean_object* l_Std_Http_instReprURIReference_repr___closed__3 = (const lean_object*)&l_Std_Http_instReprURIReference_repr___closed__3_value;
static const lean_ctor_object l_Std_Http_instReprURIReference_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprURIReference_repr___closed__3_value)}};
static const lean_object* l_Std_Http_instReprURIReference_repr___closed__4 = (const lean_object*)&l_Std_Http_instReprURIReference_repr___closed__4_value;
static const lean_ctor_object l_Std_Http_instReprURIReference_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_instReprURIReference_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_instReprURIReference_repr___closed__5 = (const lean_object*)&l_Std_Http_instReprURIReference_repr___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instReprURIReference___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instReprURIReference_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instReprURIReference___closed__0 = (const lean_object*)&l_Std_Http_instReprURIReference___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instReprURIReference = (const lean_object*)&l_Std_Http_instReprURIReference___closed__0_value;
static const lean_ctor_object l_Std_Http_instInhabitedURIReference_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_instInhabitedURI_default___closed__0_value)}};
static const lean_object* l_Std_Http_instInhabitedURIReference_default___closed__0 = (const lean_object*)&l_Std_Http_instInhabitedURIReference_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instInhabitedURIReference_default = (const lean_object*)&l_Std_Http_instInhabitedURIReference_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instInhabitedURIReference = (const lean_object*)&l_Std_Http_instInhabitedURIReference_default___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_instToStringURIReference___lam__0(lean_object*);
static const lean_closure_object l_Std_Http_instToStringURIReference___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instToStringURIReference___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instToStringURIReference___closed__0 = (const lean_object*)&l_Std_Http_instToStringURIReference___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instToStringURIReference = (const lean_object*)&l_Std_Http_instToStringURIReference___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_instInhabitedRequestTarget_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_URI_instInhabitedPath_default___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_instInhabitedRequestTarget_default___closed__0 = (const lean_object*)&l_Std_Http_instInhabitedRequestTarget_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instInhabitedRequestTarget_default = (const lean_object*)&l_Std_Http_instInhabitedRequestTarget_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instInhabitedRequestTarget = (const lean_object*)&l_Std_Http_instInhabitedRequestTarget_default___closed__0_value;
static const lean_string_object l_Std_Http_instReprRequestTarget_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Std.Http.RequestTarget.asteriskForm"};
static const lean_object* l_Std_Http_instReprRequestTarget_repr___closed__0 = (const lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__0_value;
static const lean_ctor_object l_Std_Http_instReprRequestTarget_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__0_value)}};
static const lean_object* l_Std_Http_instReprRequestTarget_repr___closed__1 = (const lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__1_value;
static const lean_string_object l_Std_Http_instReprRequestTarget_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Std.Http.RequestTarget.originForm"};
static const lean_object* l_Std_Http_instReprRequestTarget_repr___closed__2 = (const lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__2_value;
static const lean_ctor_object l_Std_Http_instReprRequestTarget_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__2_value)}};
static const lean_object* l_Std_Http_instReprRequestTarget_repr___closed__3 = (const lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__3_value;
static const lean_ctor_object l_Std_Http_instReprRequestTarget_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_instReprRequestTarget_repr___closed__4 = (const lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__4_value;
static const lean_string_object l_Std_Http_instReprRequestTarget_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Std.Http.RequestTarget.absoluteForm"};
static const lean_object* l_Std_Http_instReprRequestTarget_repr___closed__5 = (const lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__5_value;
static const lean_ctor_object l_Std_Http_instReprRequestTarget_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__5_value)}};
static const lean_object* l_Std_Http_instReprRequestTarget_repr___closed__6 = (const lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__6_value;
static const lean_ctor_object l_Std_Http_instReprRequestTarget_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_instReprRequestTarget_repr___closed__7 = (const lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__7_value;
static const lean_string_object l_Std_Http_instReprRequestTarget_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Http.RequestTarget.authorityForm"};
static const lean_object* l_Std_Http_instReprRequestTarget_repr___closed__8 = (const lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__8_value;
static const lean_ctor_object l_Std_Http_instReprRequestTarget_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__8_value)}};
static const lean_object* l_Std_Http_instReprRequestTarget_repr___closed__9 = (const lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__9_value;
static const lean_ctor_object l_Std_Http_instReprRequestTarget_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_instReprRequestTarget_repr___closed__10 = (const lean_object*)&l_Std_Http_instReprRequestTarget_repr___closed__10_value;
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instReprRequestTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instReprRequestTarget_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instReprRequestTarget___closed__0 = (const lean_object*)&l_Std_Http_instReprRequestTarget___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instReprRequestTarget = (const lean_object*)&l_Std_Http_instReprRequestTarget___closed__0_value;
static const lean_ctor_object l_Std_Http_RequestTarget_path___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_URI_Query_names___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_RequestTarget_path___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_path___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authority_x3f(lean_object*);
static const lean_string_object l_Std_Http_RequestTarget_instToString___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Std_Http_RequestTarget_instToString___lam__0___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_instToString___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__0(lean_object*);
static const lean_closure_object l_Std_Http_RequestTarget_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_RequestTarget_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_RequestTarget_instToString___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_RequestTarget_instToString = (const lean_object*)&l_Std_Http_RequestTarget_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_RequestTarget_instEncodeV11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_RequestTarget_instEncodeV11___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_RequestTarget_instEncodeV11___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_instEncodeV11___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_RequestTarget_instEncodeV11 = (const lean_object*)&l_Std_Http_RequestTarget_instEncodeV11___closed__0_value;
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(lean_object* v_s_3_, lean_object* v_p_4_){
_start:
{
lean_object* v___y_6_; lean_object* v___y_7_; uint32_t v___y_11_; lean_object* v___x_23_; uint8_t v_decide_24_; 
v___x_23_ = lean_string_utf8_byte_size(v_s_3_);
v_decide_24_ = lean_nat_dec_eq(v_p_4_, v___x_23_);
if (v_decide_24_ == 0)
{
uint32_t v___x_25_; uint32_t v___x_26_; uint8_t v___x_27_; 
v___x_25_ = lean_string_utf8_get_fast(v_s_3_, v_p_4_);
v___x_26_ = 65;
v___x_27_ = lean_uint32_dec_le(v___x_26_, v___x_25_);
if (v___x_27_ == 0)
{
v___y_11_ = v___x_25_;
goto v___jp_10_;
}
else
{
uint32_t v___x_28_; uint8_t v___x_29_; 
v___x_28_ = 90;
v___x_29_ = lean_uint32_dec_le(v___x_25_, v___x_28_);
if (v___x_29_ == 0)
{
v___y_11_ = v___x_25_;
goto v___jp_10_;
}
else
{
uint32_t v___x_30_; uint32_t v___x_31_; 
v___x_30_ = 32;
v___x_31_ = lean_uint32_add(v___x_25_, v___x_30_);
v___y_11_ = v___x_31_;
goto v___jp_10_;
}
}
}
else
{
lean_dec(v_p_4_);
return v_s_3_;
}
v___jp_5_:
{
lean_object* v___x_8_; 
v___x_8_ = lean_nat_add(v_p_4_, v___y_7_);
lean_dec(v_p_4_);
v_s_3_ = v___y_6_;
v_p_4_ = v___x_8_;
goto _start;
}
v___jp_10_:
{
lean_object* v___x_12_; uint32_t v___x_13_; uint8_t v___x_14_; 
lean_inc(v_p_4_);
v___x_12_ = lean_string_utf8_set(v_s_3_, v_p_4_, v___y_11_);
v___x_13_ = 127;
v___x_14_ = lean_uint32_dec_le(v___y_11_, v___x_13_);
if (v___x_14_ == 0)
{
uint32_t v___x_15_; uint8_t v___x_16_; 
v___x_15_ = 2047;
v___x_16_ = lean_uint32_dec_le(v___y_11_, v___x_15_);
if (v___x_16_ == 0)
{
uint32_t v___x_17_; uint8_t v___x_18_; 
v___x_17_ = 65535;
v___x_18_ = lean_uint32_dec_le(v___y_11_, v___x_17_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; 
v___x_19_ = lean_unsigned_to_nat(4u);
v___y_6_ = v___x_12_;
v___y_7_ = v___x_19_;
goto v___jp_5_;
}
else
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(3u);
v___y_6_ = v___x_12_;
v___y_7_ = v___x_20_;
goto v___jp_5_;
}
}
else
{
lean_object* v___x_21_; 
v___x_21_ = lean_unsigned_to_nat(2u);
v___y_6_ = v___x_12_;
v___y_7_ = v___x_21_;
goto v___jp_5_;
}
}
else
{
lean_object* v___x_22_; 
v___x_22_ = lean_unsigned_to_nat(1u);
v___y_6_ = v___x_12_;
v___y_7_ = v___x_22_;
goto v___jp_5_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(lean_object* v_x_32_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
uint8_t v___x_33_; 
v___x_33_ = 1;
return v___x_33_;
}
else
{
lean_object* v_head_34_; lean_object* v_tail_35_; uint32_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v_head_34_ = lean_ctor_get(v_x_32_, 0);
v_tail_35_ = lean_ctor_get(v_x_32_, 1);
v___x_65_ = lean_unbox_uint32(v_head_34_);
v___x_66_ = lean_uint32_to_nat(v___x_65_);
v___x_67_ = lean_unsigned_to_nat(128u);
v___x_68_ = lean_nat_dec_lt(v___x_66_, v___x_67_);
lean_dec(v___x_66_);
if (v___x_68_ == 0)
{
goto v___jp_36_;
}
else
{
uint32_t v___x_69_; uint32_t v___x_70_; uint8_t v___x_71_; 
v___x_69_ = 48;
v___x_70_ = lean_unbox_uint32(v_head_34_);
v___x_71_ = lean_uint32_dec_le(v___x_69_, v___x_70_);
if (v___x_71_ == 0)
{
goto v___jp_57_;
}
else
{
uint32_t v___x_72_; uint32_t v___x_73_; uint8_t v___x_74_; 
v___x_72_ = 57;
v___x_73_ = lean_unbox_uint32(v_head_34_);
v___x_74_ = lean_uint32_dec_le(v___x_73_, v___x_72_);
if (v___x_74_ == 0)
{
goto v___jp_57_;
}
else
{
v_x_32_ = v_tail_35_;
goto _start;
}
}
}
v___jp_36_:
{
uint32_t v___x_37_; uint32_t v___x_38_; uint8_t v___x_39_; 
v___x_37_ = 43;
v___x_38_ = lean_unbox_uint32(v_head_34_);
v___x_39_ = lean_uint32_dec_eq(v___x_38_, v___x_37_);
if (v___x_39_ == 0)
{
uint32_t v___x_40_; uint32_t v___x_41_; uint8_t v___x_42_; 
v___x_40_ = 45;
v___x_41_ = lean_unbox_uint32(v_head_34_);
v___x_42_ = lean_uint32_dec_eq(v___x_41_, v___x_40_);
if (v___x_42_ == 0)
{
uint32_t v___x_43_; uint32_t v___x_44_; uint8_t v___x_45_; 
v___x_43_ = 46;
v___x_44_ = lean_unbox_uint32(v_head_34_);
v___x_45_ = lean_uint32_dec_eq(v___x_44_, v___x_43_);
if (v___x_45_ == 0)
{
return v___x_45_;
}
else
{
v_x_32_ = v_tail_35_;
goto _start;
}
}
else
{
v_x_32_ = v_tail_35_;
goto _start;
}
}
else
{
v_x_32_ = v_tail_35_;
goto _start;
}
}
v___jp_49_:
{
uint32_t v___x_50_; uint32_t v___x_51_; uint8_t v___x_52_; 
v___x_50_ = 97;
v___x_51_ = lean_unbox_uint32(v_head_34_);
v___x_52_ = lean_uint32_dec_le(v___x_50_, v___x_51_);
if (v___x_52_ == 0)
{
goto v___jp_36_;
}
else
{
uint32_t v___x_53_; uint32_t v___x_54_; uint8_t v___x_55_; 
v___x_53_ = 122;
v___x_54_ = lean_unbox_uint32(v_head_34_);
v___x_55_ = lean_uint32_dec_le(v___x_54_, v___x_53_);
if (v___x_55_ == 0)
{
goto v___jp_36_;
}
else
{
v_x_32_ = v_tail_35_;
goto _start;
}
}
}
v___jp_57_:
{
uint32_t v___x_58_; uint32_t v___x_59_; uint8_t v___x_60_; 
v___x_58_ = 65;
v___x_59_ = lean_unbox_uint32(v_head_34_);
v___x_60_ = lean_uint32_dec_le(v___x_58_, v___x_59_);
if (v___x_60_ == 0)
{
goto v___jp_49_;
}
else
{
uint32_t v___x_61_; uint32_t v___x_62_; uint8_t v___x_63_; 
v___x_61_ = 90;
v___x_62_ = lean_unbox_uint32(v_head_34_);
v___x_63_ = lean_uint32_dec_le(v___x_62_, v___x_61_);
if (v___x_63_ == 0)
{
goto v___jp_49_;
}
else
{
v_x_32_ = v_tail_35_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1___boxed(lean_object* v_x_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(v_x_76_);
lean_dec(v_x_76_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x3f(lean_object* v_s_79_){
_start:
{
lean_object* v___x_80_; lean_object* v_lower_81_; uint8_t v___x_82_; 
v___x_80_ = lean_unsigned_to_nat(0u);
v_lower_81_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_79_, v___x_80_);
lean_inc_ref(v_lower_81_);
v___x_82_ = l_Std_Http_Internal_instDecidableIsLowerCase(v_lower_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; 
lean_dec_ref(v_lower_81_);
v___x_83_ = lean_box(0);
return v___x_83_;
}
else
{
lean_object* v___x_84_; uint8_t v___x_85_; 
lean_inc_ref(v_lower_81_);
v___x_84_ = l_String_toListImpl(v_lower_81_);
v___x_85_ = l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; 
lean_dec(v___x_84_);
lean_dec_ref(v_lower_81_);
v___x_86_ = lean_box(0);
return v___x_86_;
}
else
{
lean_object* v___x_87_; 
v___x_87_ = l_List_head_x3f___redArg(v___x_84_);
lean_dec(v___x_84_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v___x_88_; 
lean_dec_ref(v_lower_81_);
v___x_88_ = lean_box(0);
return v___x_88_;
}
else
{
lean_object* v_val_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_112_; 
v_val_89_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_112_ == 0)
{
v___x_91_ = v___x_87_;
v_isShared_92_ = v_isSharedCheck_112_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_val_89_);
lean_dec(v___x_87_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_112_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
uint32_t v___x_105_; uint32_t v___x_106_; uint8_t v___x_107_; 
v___x_105_ = 65;
v___x_106_ = lean_unbox_uint32(v_val_89_);
v___x_107_ = lean_uint32_dec_le(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
goto v___jp_93_;
}
else
{
uint32_t v___x_108_; uint32_t v___x_109_; uint8_t v___x_110_; 
v___x_108_ = 90;
v___x_109_ = lean_unbox_uint32(v_val_89_);
v___x_110_ = lean_uint32_dec_le(v___x_109_, v___x_108_);
if (v___x_110_ == 0)
{
goto v___jp_93_;
}
else
{
lean_object* v___x_111_; 
lean_del_object(v___x_91_);
lean_dec(v_val_89_);
v___x_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_111_, 0, v_lower_81_);
return v___x_111_;
}
}
v___jp_93_:
{
uint32_t v___x_94_; uint32_t v___x_95_; uint8_t v___x_96_; 
v___x_94_ = 97;
v___x_95_ = lean_unbox_uint32(v_val_89_);
v___x_96_ = lean_uint32_dec_le(v___x_94_, v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_del_object(v___x_91_);
lean_dec(v_val_89_);
lean_dec_ref(v_lower_81_);
v___x_97_ = lean_box(0);
return v___x_97_;
}
else
{
uint32_t v___x_98_; uint32_t v___x_99_; uint8_t v___x_100_; 
v___x_98_ = 122;
v___x_99_ = lean_unbox_uint32(v_val_89_);
lean_dec(v_val_89_);
v___x_100_ = lean_uint32_dec_le(v___x_99_, v___x_98_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
lean_del_object(v___x_91_);
lean_dec_ref(v_lower_81_);
v___x_101_ = lean_box(0);
return v___x_101_;
}
else
{
lean_object* v___x_103_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v_lower_81_);
v___x_103_ = v___x_91_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_lower_81_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(lean_object* v_msg_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = ((lean_object*)(l_Std_Http_URI_instInhabitedScheme___closed__0));
v___x_115_ = lean_panic_fn_borrowed(v___x_114_, v_msg_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x21(lean_object* v_s_119_){
_start:
{
lean_object* v___x_120_; 
lean_inc_ref(v_s_119_);
v___x_120_ = l_Std_Http_URI_Scheme_ofString_x3f(v_s_119_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_121_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_122_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__1));
v___x_123_ = lean_unsigned_to_nat(86u);
v___x_124_ = lean_unsigned_to_nat(12u);
v___x_125_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_126_ = l_String_quote(v_s_119_);
v___x_127_ = lean_string_append(v___x_125_, v___x_126_);
lean_dec_ref(v___x_126_);
v___x_128_ = l_mkPanicMessageWithDecl(v___x_121_, v___x_122_, v___x_123_, v___x_124_, v___x_127_);
lean_dec_ref(v___x_127_);
v___x_129_ = l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(v___x_128_);
return v___x_129_;
}
else
{
lean_object* v_val_130_; 
lean_dec_ref(v_s_119_);
v_val_130_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_val_130_);
lean_dec_ref_known(v___x_120_, 1);
return v_val_130_;
}
}
}
LEAN_EXPORT uint16_t l_Std_Http_URI_Scheme_defaultPort(lean_object* v_scheme_132_){
_start:
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___x_134_ = lean_string_dec_eq(v_scheme_132_, v___x_133_);
if (v___x_134_ == 0)
{
uint16_t v___x_135_; 
v___x_135_ = 80;
return v___x_135_;
}
else
{
uint16_t v___x_136_; 
v___x_136_ = 443;
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_defaultPort___boxed(lean_object* v_scheme_137_){
_start:
{
uint16_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_137_);
lean_dec_ref(v_scheme_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofPort(uint16_t v_port_140_){
_start:
{
uint16_t v___x_141_; uint8_t v___x_142_; 
v___x_141_ = 443;
v___x_142_ = lean_uint16_dec_eq(v_port_140_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = ((lean_object*)(l_Std_Http_URI_instInhabitedScheme___closed__0));
return v___x_143_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofPort___boxed(lean_object* v_port_145_){
_start:
{
uint16_t v_port_boxed_146_; lean_object* v_res_147_; 
v_port_boxed_146_ = lean_unbox(v_port_145_);
v_res_147_ = l_Std_Http_URI_Scheme_ofPort(v_port_boxed_146_);
return v_res_147_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__0(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_box(0);
v___x_149_ = l_ByteArray_empty;
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v___x_148_);
return v___x_150_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_obj_once(&l_Std_Http_URI_instInhabitedUserInfo_default___closed__0, &l_Std_Http_URI_instInhabitedUserInfo_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__0);
return v___x_151_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Std_Http_URI_instInhabitedUserInfo_default;
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
if (lean_obj_tag(v_x_159_) == 0)
{
lean_object* v___x_161_; 
v___x_161_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_161_;
}
else
{
lean_object* v_val_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_174_; 
v_val_162_ = lean_ctor_get(v_x_159_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v_x_159_);
if (v_isSharedCheck_174_ == 0)
{
v___x_164_ = v_x_159_;
v_isShared_165_ = v_isSharedCheck_174_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_val_162_);
lean_dec(v_x_159_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_174_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_166_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_167_ = lean_string_from_utf8_unchecked(v_val_162_);
v___x_168_ = l_String_quote(v___x_167_);
if (v_isShared_165_ == 0)
{
lean_ctor_set_tag(v___x_164_, 3);
lean_ctor_set(v___x_164_, 0, v___x_168_);
v___x_170_ = v___x_164_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_173_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_166_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = l_Repr_addAppParen(v___x_171_, v_x_160_);
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___boxed(lean_object* v_x_175_, lean_object* v_x_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_x_175_, v_x_176_);
lean_dec(v_x_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_URI_instReprUserInfo_repr_spec__1(lean_object* v_a_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = lean_nat_to_int(v_a_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(12u);
v___x_194_ = lean_nat_to_int(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0));
v___x_203_ = lean_string_length(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13);
v___x_205_ = lean_nat_to_int(v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg(lean_object* v_x_210_){
_start:
{
lean_object* v_username_211_; lean_object* v_password_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_247_; 
v_username_211_ = lean_ctor_get(v_x_210_, 0);
v_password_212_ = lean_ctor_get(v_x_210_, 1);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_247_ == 0)
{
v___x_214_ = v_x_210_;
v_isShared_215_ = v_isSharedCheck_247_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_password_212_);
lean_inc(v_username_211_);
lean_dec(v_x_210_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_247_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_216_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_217_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__6));
v___x_218_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_219_ = lean_string_from_utf8_unchecked(v_username_211_);
v___x_220_ = l_String_quote(v___x_219_);
v___x_221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 4);
lean_ctor_set(v___x_214_, 1, v___x_221_);
lean_ctor_set(v___x_214_, 0, v___x_218_);
v___x_223_ = v___x_214_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_221_);
v___x_223_ = v_reuseFailAlloc_246_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_224_ = 0;
v___x_225_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v___x_224_);
v___x_226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_217_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lean_box(1);
v___x_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__11));
v___x_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v___x_216_);
v___x_234_ = lean_unsigned_to_nat(0u);
v___x_235_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_password_212_, v___x_234_);
v___x_236_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_218_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*1, v___x_224_);
v___x_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_233_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_240_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_238_);
v___x_242_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_239_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1, v___x_224_);
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr(lean_object* v_x_248_, lean_object* v_prec_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_x_248_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___boxed(lean_object* v_x_251_, lean_object* v_prec_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_Http_URI_instReprUserInfo_repr(v_x_251_, v_prec_252_);
lean_dec(v_prec_252_);
return v_res_253_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
if (lean_obj_tag(v_x_256_) == 0)
{
if (lean_obj_tag(v_x_257_) == 0)
{
uint8_t v___x_258_; 
v___x_258_ = 1;
return v___x_258_;
}
else
{
uint8_t v___x_259_; 
v___x_259_ = 0;
return v___x_259_;
}
}
else
{
if (lean_obj_tag(v_x_257_) == 0)
{
uint8_t v___x_260_; 
v___x_260_ = 0;
return v___x_260_;
}
else
{
lean_object* v_val_261_; lean_object* v_val_262_; uint8_t v___x_263_; 
v_val_261_ = lean_ctor_get(v_x_256_, 0);
v_val_262_ = lean_ctor_get(v_x_257_, 0);
v___x_263_ = lean_sarray_dec_eq(v_val_261_, v_val_262_);
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0___boxed(lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
uint8_t v_res_266_; lean_object* v_r_267_; 
v_res_266_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_x_264_, v_x_265_);
lean_dec(v_x_265_);
lean_dec(v_x_264_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqUserInfo_beq(lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
lean_object* v_username_270_; lean_object* v_password_271_; lean_object* v_username_272_; lean_object* v_password_273_; uint8_t v___x_274_; 
v_username_270_ = lean_ctor_get(v_x_268_, 0);
v_password_271_ = lean_ctor_get(v_x_268_, 1);
v_username_272_ = lean_ctor_get(v_x_269_, 0);
v_password_273_ = lean_ctor_get(v_x_269_, 1);
v___x_274_ = lean_sarray_dec_eq(v_username_270_, v_username_272_);
if (v___x_274_ == 0)
{
return v___x_274_;
}
else
{
uint8_t v___x_275_; 
v___x_275_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_password_271_, v_password_273_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqUserInfo_beq___boxed(lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = l_Std_Http_URI_instBEqUserInfo_beq(v_x_276_, v_x_277_);
lean_dec_ref(v_x_277_);
lean_dec_ref(v_x_276_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_UserInfo_ofStrings___lam__0(uint8_t v_x_282_){
_start:
{
uint8_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = 58;
v___x_284_ = lean_uint8_dec_eq(v_x_282_, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings___lam__0___boxed(lean_object* v_x_285_){
_start:
{
uint8_t v_x_67__boxed_286_; uint8_t v_res_287_; lean_object* v_r_288_; 
v_x_67__boxed_286_ = lean_unbox(v_x_285_);
v_res_287_ = l_Std_Http_URI_UserInfo_ofStrings___lam__0(v_x_67__boxed_286_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings(lean_object* v_username_291_, lean_object* v_password_292_){
_start:
{
lean_object* v___f_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___f_293_ = ((lean_object*)(l_Std_Http_URI_UserInfo_ofStrings___closed__0));
v___x_294_ = ((lean_object*)(l_Std_Http_URI_UserInfo_ofStrings___closed__1));
v___x_295_ = l_Std_Http_URI_EncodedString_encodeEscaping(v___x_294_, v_username_291_, v___f_293_);
if (lean_obj_tag(v_password_292_) == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_box(0);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
return v___x_297_;
}
else
{
lean_object* v_val_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_307_; 
v_val_298_ = lean_ctor_get(v_password_292_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v_password_292_);
if (v_isSharedCheck_307_ == 0)
{
v___x_300_ = v_password_292_;
v_isShared_301_ = v_isSharedCheck_307_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_val_298_);
lean_dec(v_password_292_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_307_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_302_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_298_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_302_);
v___x_304_ = v___x_300_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_306_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_305_; 
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_295_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
return v___x_305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f(lean_object* v_ui_308_){
_start:
{
lean_object* v_username_309_; lean_object* v___x_310_; 
v_username_309_ = lean_ctor_get(v_ui_308_, 0);
v___x_310_ = l_Std_Http_URI_EncodedUserInfo_decode(v_username_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f___boxed(lean_object* v_ui_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_Http_URI_UserInfo_username_x3f(v_ui_311_);
lean_dec_ref(v_ui_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f(lean_object* v_ui_313_){
_start:
{
lean_object* v_password_314_; 
v_password_314_ = lean_ctor_get(v_ui_313_, 1);
if (lean_obj_tag(v_password_314_) == 0)
{
lean_object* v___x_315_; 
v___x_315_ = lean_box(0);
return v___x_315_;
}
else
{
lean_object* v_val_316_; lean_object* v___x_317_; 
v_val_316_ = lean_ctor_get(v_password_314_, 0);
v___x_317_ = l_Std_Http_URI_EncodedUserInfo_decode(v_val_316_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f___boxed(lean_object* v_ui_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Std_Http_URI_UserInfo_password_x3f(v_ui_318_);
lean_dec_ref(v_ui_318_);
return v_res_319_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(lean_object* v_x_320_){
_start:
{
if (lean_obj_tag(v_x_320_) == 0)
{
uint8_t v___x_321_; 
v___x_321_ = 1;
return v___x_321_;
}
else
{
lean_object* v_head_322_; lean_object* v_tail_323_; uint32_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_head_322_ = lean_ctor_get(v_x_320_, 0);
v_tail_323_ = lean_ctor_get(v_x_320_, 1);
v___x_349_ = lean_unbox_uint32(v_head_322_);
v___x_350_ = lean_uint32_to_nat(v___x_349_);
v___x_351_ = lean_unsigned_to_nat(128u);
v___x_352_ = lean_nat_dec_lt(v___x_350_, v___x_351_);
lean_dec(v___x_350_);
if (v___x_352_ == 0)
{
goto v___jp_324_;
}
else
{
uint32_t v___x_353_; uint32_t v___x_354_; uint8_t v___x_355_; 
v___x_353_ = 48;
v___x_354_ = lean_unbox_uint32(v_head_322_);
v___x_355_ = lean_uint32_dec_le(v___x_353_, v___x_354_);
if (v___x_355_ == 0)
{
goto v___jp_341_;
}
else
{
uint32_t v___x_356_; uint32_t v___x_357_; uint8_t v___x_358_; 
v___x_356_ = 57;
v___x_357_ = lean_unbox_uint32(v_head_322_);
v___x_358_ = lean_uint32_dec_le(v___x_357_, v___x_356_);
if (v___x_358_ == 0)
{
goto v___jp_341_;
}
else
{
v_x_320_ = v_tail_323_;
goto _start;
}
}
}
v___jp_324_:
{
uint32_t v___x_325_; uint32_t v___x_326_; uint8_t v___x_327_; 
v___x_325_ = 45;
v___x_326_ = lean_unbox_uint32(v_head_322_);
v___x_327_ = lean_uint32_dec_eq(v___x_326_, v___x_325_);
if (v___x_327_ == 0)
{
uint32_t v___x_328_; uint32_t v___x_329_; uint8_t v___x_330_; 
v___x_328_ = 95;
v___x_329_ = lean_unbox_uint32(v_head_322_);
v___x_330_ = lean_uint32_dec_eq(v___x_329_, v___x_328_);
if (v___x_330_ == 0)
{
return v___x_330_;
}
else
{
v_x_320_ = v_tail_323_;
goto _start;
}
}
else
{
v_x_320_ = v_tail_323_;
goto _start;
}
}
v___jp_333_:
{
uint32_t v___x_334_; uint32_t v___x_335_; uint8_t v___x_336_; 
v___x_334_ = 97;
v___x_335_ = lean_unbox_uint32(v_head_322_);
v___x_336_ = lean_uint32_dec_le(v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
goto v___jp_324_;
}
else
{
uint32_t v___x_337_; uint32_t v___x_338_; uint8_t v___x_339_; 
v___x_337_ = 122;
v___x_338_ = lean_unbox_uint32(v_head_322_);
v___x_339_ = lean_uint32_dec_le(v___x_338_, v___x_337_);
if (v___x_339_ == 0)
{
goto v___jp_324_;
}
else
{
v_x_320_ = v_tail_323_;
goto _start;
}
}
}
v___jp_341_:
{
uint32_t v___x_342_; uint32_t v___x_343_; uint8_t v___x_344_; 
v___x_342_ = 65;
v___x_343_ = lean_unbox_uint32(v_head_322_);
v___x_344_ = lean_uint32_dec_le(v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
goto v___jp_333_;
}
else
{
uint32_t v___x_345_; uint32_t v___x_346_; uint8_t v___x_347_; 
v___x_345_ = 90;
v___x_346_ = lean_unbox_uint32(v_head_322_);
v___x_347_ = lean_uint32_dec_le(v___x_346_, v___x_345_);
if (v___x_347_ == 0)
{
goto v___jp_333_;
}
else
{
v_x_320_ = v_tail_323_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0___boxed(lean_object* v_x_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v_x_360_);
lean_dec(v_x_360_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object* v_s_363_){
_start:
{
lean_object* v_chars_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v_chars_364_ = l_String_toListImpl(v_s_363_);
v___x_365_ = l_List_lengthTR___redArg(v_chars_364_);
v___x_366_ = lean_unsigned_to_nat(63u);
v___x_367_ = lean_nat_dec_le(v___x_365_, v___x_366_);
lean_dec(v___x_365_);
if (v___x_367_ == 0)
{
lean_dec(v_chars_364_);
return v___x_367_;
}
else
{
uint8_t v___x_368_; 
v___x_368_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v_chars_364_);
if (v___x_368_ == 0)
{
lean_dec(v_chars_364_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; 
v___x_369_ = l_List_head_x3f___redArg(v_chars_364_);
if (lean_obj_tag(v___x_369_) == 0)
{
uint8_t v___x_370_; 
lean_dec(v_chars_364_);
v___x_370_ = 0;
return v___x_370_;
}
else
{
lean_object* v_val_371_; uint32_t v___x_372_; uint32_t v___x_373_; uint8_t v___x_374_; 
v_val_371_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_val_371_);
lean_dec_ref_known(v___x_369_, 1);
v___x_372_ = 45;
v___x_373_ = lean_unbox_uint32(v_val_371_);
lean_dec(v_val_371_);
v___x_374_ = lean_uint32_dec_eq(v___x_373_, v___x_372_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; 
v___x_375_ = l_List_getLast_x3f___redArg(v_chars_364_);
lean_dec(v_chars_364_);
if (lean_obj_tag(v___x_375_) == 0)
{
return v___x_374_;
}
else
{
lean_object* v_val_376_; uint32_t v___x_377_; uint8_t v___x_378_; 
v_val_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_val_376_);
lean_dec_ref_known(v___x_375_, 1);
v___x_377_ = lean_unbox_uint32(v_val_376_);
lean_dec(v_val_376_);
v___x_378_ = lean_uint32_dec_eq(v___x_377_, v___x_372_);
if (v___x_378_ == 0)
{
return v___x_368_;
}
else
{
return v___x_374_;
}
}
}
else
{
uint8_t v___x_379_; 
lean_dec(v_chars_364_);
v___x_379_ = 0;
return v___x_379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidDomainLabel___boxed(lean_object* v_s_380_){
_start:
{
uint8_t v_res_381_; lean_object* v_r_382_; 
v_res_381_ = l_Std_Http_URI_isValidDomainLabel(v_s_380_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3___redArg(lean_object* v_s_384_){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_385_ = lean_string_utf8_byte_size(v_s_384_);
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_dec_le(v___x_386_, v___x_385_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
lean_dec_ref(v_s_384_);
v___x_388_ = lean_box(0);
return v___x_388_;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_389_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3___redArg___closed__0));
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_nat_sub(v___x_385_, v___x_386_);
v___x_392_ = lean_string_memcmp(v_s_384_, v___x_389_, v___x_391_, v___x_390_, v___x_386_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
lean_dec(v___x_391_);
lean_dec_ref(v_s_384_);
v___x_393_ = lean_box(0);
return v___x_393_;
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
lean_inc_ref(v_s_384_);
v___x_394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_394_, 0, v_s_384_);
lean_ctor_set(v___x_394_, 1, v___x_390_);
lean_ctor_set(v___x_394_, 2, v___x_385_);
v___x_395_ = l_String_Slice_pos_x21(v___x_394_, v___x_391_);
lean_dec(v___x_391_);
lean_dec_ref_known(v___x_394_, 3);
v___x_396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_396_, 0, v_s_384_);
lean_ctor_set(v___x_396_, 1, v___x_390_);
lean_ctor_set(v___x_396_, 2, v___x_395_);
v___x_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3(lean_object* v_s_398_, lean_object* v_pat_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3___redArg(v_s_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3___boxed(lean_object* v_s_401_, lean_object* v_pat_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3(v_s_401_, v_pat_402_);
lean_dec_ref(v_pat_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___at___00Std_Http_URI_endsInNumber_spec__1(lean_object* v_l_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
if (lean_obj_tag(v_a_405_) == 0)
{
lean_dec_ref(v_a_406_);
lean_inc(v_l_404_);
return v_l_404_;
}
else
{
lean_object* v_head_407_; lean_object* v_tail_408_; uint32_t v___x_409_; uint32_t v___x_410_; uint8_t v___x_411_; 
v_head_407_ = lean_ctor_get(v_a_405_, 0);
lean_inc(v_head_407_);
v_tail_408_ = lean_ctor_get(v_a_405_, 1);
lean_inc(v_tail_408_);
lean_dec_ref_known(v_a_405_, 2);
v___x_409_ = 46;
v___x_410_ = lean_unbox_uint32(v_head_407_);
v___x_411_ = lean_uint32_dec_eq(v___x_410_, v___x_409_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
v___x_412_ = lean_array_push(v_a_406_, v_head_407_);
v_a_405_ = v_tail_408_;
v_a_406_ = v___x_412_;
goto _start;
}
else
{
lean_object* v___x_414_; 
lean_dec(v_tail_408_);
lean_dec(v_head_407_);
v___x_414_ = lean_array_to_list(v_a_406_);
return v___x_414_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___at___00Std_Http_URI_endsInNumber_spec__1___boxed(lean_object* v_l_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___at___00Std_Http_URI_endsInNumber_spec__1(v_l_415_, v_a_416_, v_a_417_);
lean_dec(v_l_415_);
return v_res_418_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_endsInNumber_spec__2(lean_object* v_x_419_){
_start:
{
if (lean_obj_tag(v_x_419_) == 0)
{
uint8_t v___x_420_; 
v___x_420_ = 1;
return v___x_420_;
}
else
{
lean_object* v_head_421_; lean_object* v_tail_422_; uint32_t v___x_439_; uint32_t v___x_440_; uint8_t v___x_441_; 
v_head_421_ = lean_ctor_get(v_x_419_, 0);
v_tail_422_ = lean_ctor_get(v_x_419_, 1);
v___x_439_ = 48;
v___x_440_ = lean_unbox_uint32(v_head_421_);
v___x_441_ = lean_uint32_dec_le(v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
goto v___jp_431_;
}
else
{
uint32_t v___x_442_; uint32_t v___x_443_; uint8_t v___x_444_; 
v___x_442_ = 57;
v___x_443_ = lean_unbox_uint32(v_head_421_);
v___x_444_ = lean_uint32_dec_le(v___x_443_, v___x_442_);
if (v___x_444_ == 0)
{
goto v___jp_431_;
}
else
{
v_x_419_ = v_tail_422_;
goto _start;
}
}
v___jp_423_:
{
uint32_t v___x_424_; uint32_t v___x_425_; uint8_t v___x_426_; 
v___x_424_ = 65;
v___x_425_ = lean_unbox_uint32(v_head_421_);
v___x_426_ = lean_uint32_dec_le(v___x_424_, v___x_425_);
if (v___x_426_ == 0)
{
return v___x_426_;
}
else
{
uint32_t v___x_427_; uint32_t v___x_428_; uint8_t v___x_429_; 
v___x_427_ = 70;
v___x_428_ = lean_unbox_uint32(v_head_421_);
v___x_429_ = lean_uint32_dec_le(v___x_428_, v___x_427_);
if (v___x_429_ == 0)
{
return v___x_429_;
}
else
{
v_x_419_ = v_tail_422_;
goto _start;
}
}
}
v___jp_431_:
{
uint32_t v___x_432_; uint32_t v___x_433_; uint8_t v___x_434_; 
v___x_432_ = 97;
v___x_433_ = lean_unbox_uint32(v_head_421_);
v___x_434_ = lean_uint32_dec_le(v___x_432_, v___x_433_);
if (v___x_434_ == 0)
{
goto v___jp_423_;
}
else
{
uint32_t v___x_435_; uint32_t v___x_436_; uint8_t v___x_437_; 
v___x_435_ = 102;
v___x_436_ = lean_unbox_uint32(v_head_421_);
v___x_437_ = lean_uint32_dec_le(v___x_436_, v___x_435_);
if (v___x_437_ == 0)
{
goto v___jp_423_;
}
else
{
v_x_419_ = v_tail_422_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_endsInNumber_spec__2___boxed(lean_object* v_x_446_){
_start:
{
uint8_t v_res_447_; lean_object* v_r_448_; 
v_res_447_ = l_List_all___at___00Std_Http_URI_endsInNumber_spec__2(v_x_446_);
lean_dec(v_x_446_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_endsInNumber_spec__0(lean_object* v_x_449_){
_start:
{
if (lean_obj_tag(v_x_449_) == 0)
{
uint8_t v___x_450_; 
v___x_450_ = 1;
return v___x_450_;
}
else
{
lean_object* v_head_451_; lean_object* v_tail_452_; uint32_t v___x_453_; uint32_t v___x_454_; uint8_t v___x_455_; 
v_head_451_ = lean_ctor_get(v_x_449_, 0);
v_tail_452_ = lean_ctor_get(v_x_449_, 1);
v___x_453_ = 48;
v___x_454_ = lean_unbox_uint32(v_head_451_);
v___x_455_ = lean_uint32_dec_le(v___x_453_, v___x_454_);
if (v___x_455_ == 0)
{
return v___x_455_;
}
else
{
uint32_t v___x_456_; uint32_t v___x_457_; uint8_t v___x_458_; 
v___x_456_ = 57;
v___x_457_ = lean_unbox_uint32(v_head_451_);
v___x_458_ = lean_uint32_dec_le(v___x_457_, v___x_456_);
if (v___x_458_ == 0)
{
return v___x_458_;
}
else
{
v_x_449_ = v_tail_452_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_endsInNumber_spec__0___boxed(lean_object* v_x_460_){
_start:
{
uint8_t v_res_461_; lean_object* v_r_462_; 
v_res_461_ = l_List_all___at___00Std_Http_URI_endsInNumber_spec__0(v_x_460_);
lean_dec(v_x_460_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
static lean_object* _init_l_Std_Http_URI_endsInNumber___boxed__const__1(void){
_start:
{
uint32_t v___x_465_; lean_object* v___x_466_; 
v___x_465_ = 48;
v___x_466_ = lean_box_uint32(v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_endsInNumber(lean_object* v_s_467_){
_start:
{
lean_object* v_digits_469_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_479_; lean_object* v___x_509_; 
lean_inc_ref(v_s_467_);
v___x_509_ = l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3___redArg(v_s_467_);
if (lean_obj_tag(v___x_509_) == 0)
{
v___y_479_ = v_s_467_;
goto v___jp_478_;
}
else
{
lean_object* v_val_510_; lean_object* v_str_511_; lean_object* v_endExclusive_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec_ref(v_s_467_);
v_val_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_val_510_);
lean_dec_ref_known(v___x_509_, 1);
v_str_511_ = lean_ctor_get(v_val_510_, 0);
lean_inc_ref(v_str_511_);
v_endExclusive_512_ = lean_ctor_get(v_val_510_, 2);
lean_inc(v_endExclusive_512_);
lean_dec(v_val_510_);
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = lean_string_utf8_extract_fast(v_str_511_, v___x_513_, v_endExclusive_512_);
lean_dec(v_endExclusive_512_);
lean_dec_ref(v_str_511_);
v___y_479_ = v___x_514_;
goto v___jp_478_;
}
v___jp_468_:
{
uint8_t v___x_470_; 
v___x_470_ = l_List_isEmpty___redArg(v_digits_469_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; 
v___x_471_ = l_List_all___at___00Std_Http_URI_endsInNumber_spec__0(v_digits_469_);
lean_dec(v_digits_469_);
return v___x_471_;
}
else
{
uint8_t v___x_472_; 
lean_dec(v_digits_469_);
v___x_472_ = 0;
return v___x_472_;
}
}
v___jp_473_:
{
uint8_t v___x_476_; 
v___x_476_ = l_List_all___at___00Std_Http_URI_endsInNumber_spec__2(v___y_474_);
lean_dec(v___y_474_);
if (v___x_476_ == 0)
{
uint8_t v___x_477_; 
v___x_477_ = l_List_all___at___00Std_Http_URI_endsInNumber_spec__0(v___y_475_);
lean_dec(v___y_475_);
return v___x_477_;
}
else
{
lean_dec(v___y_475_);
return v___x_476_;
}
}
v___jp_478_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v_last_484_; 
v___x_480_ = l_String_toListImpl(v___y_479_);
v___x_481_ = l_List_reverse___redArg(v___x_480_);
v___x_482_ = ((lean_object*)(l_Std_Http_URI_endsInNumber___closed__0));
lean_inc(v___x_481_);
v___x_483_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___at___00Std_Http_URI_endsInNumber_spec__1(v___x_481_, v___x_481_, v___x_482_);
lean_dec(v___x_481_);
v_last_484_ = l_List_reverse___redArg(v___x_483_);
if (lean_obj_tag(v_last_484_) == 1)
{
lean_object* v_head_485_; lean_object* v_tail_486_; uint32_t v___x_487_; uint32_t v___x_488_; uint8_t v___x_489_; 
v_head_485_ = lean_ctor_get(v_last_484_, 0);
v_tail_486_ = lean_ctor_get(v_last_484_, 1);
v___x_487_ = 48;
v___x_488_ = lean_unbox_uint32(v_head_485_);
v___x_489_ = lean_uint32_dec_eq(v___x_488_, v___x_487_);
if (v___x_489_ == 0)
{
v_digits_469_ = v_last_484_;
goto v___jp_468_;
}
else
{
lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_506_; 
lean_inc(v_tail_486_);
v_isSharedCheck_506_ = !lean_is_exclusive(v_last_484_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; lean_object* v_unused_508_; 
v_unused_507_ = lean_ctor_get(v_last_484_, 1);
lean_dec(v_unused_507_);
v_unused_508_ = lean_ctor_get(v_last_484_, 0);
lean_dec(v_unused_508_);
v___x_491_ = v_last_484_;
v_isShared_492_ = v_isSharedCheck_506_;
goto v_resetjp_490_;
}
else
{
lean_dec(v_last_484_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_506_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
if (lean_obj_tag(v_tail_486_) == 1)
{
lean_object* v_head_493_; lean_object* v_tail_494_; uint32_t v___x_495_; uint32_t v___x_496_; uint8_t v___x_497_; 
lean_del_object(v___x_491_);
v_head_493_ = lean_ctor_get(v_tail_486_, 0);
v_tail_494_ = lean_ctor_get(v_tail_486_, 1);
v___x_495_ = 120;
v___x_496_ = lean_unbox_uint32(v_head_493_);
v___x_497_ = lean_uint32_dec_eq(v___x_496_, v___x_495_);
if (v___x_497_ == 0)
{
uint32_t v___x_498_; uint32_t v___x_499_; uint8_t v___x_500_; 
v___x_498_ = 88;
v___x_499_ = lean_unbox_uint32(v_head_493_);
v___x_500_ = lean_uint32_dec_eq(v___x_499_, v___x_498_);
if (v___x_500_ == 0)
{
uint8_t v___x_501_; 
v___x_501_ = l_List_all___at___00Std_Http_URI_endsInNumber_spec__0(v_tail_486_);
lean_dec_ref_known(v_tail_486_, 2);
return v___x_501_;
}
else
{
lean_inc(v_tail_494_);
v___y_474_ = v_tail_494_;
v___y_475_ = v_tail_486_;
goto v___jp_473_;
}
}
else
{
lean_inc(v_tail_494_);
v___y_474_ = v_tail_494_;
v___y_475_ = v_tail_486_;
goto v___jp_473_;
}
}
else
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = l_Std_Http_URI_endsInNumber___boxed__const__1;
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_502_);
v___x_504_ = v___x_491_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_tail_486_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
v_digits_469_ = v___x_504_;
goto v___jp_468_;
}
}
}
}
}
else
{
v_digits_469_ = v_last_484_;
goto v___jp_468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_endsInNumber___boxed(lean_object* v_s_515_){
_start:
{
uint8_t v_res_516_; lean_object* v_r_517_; 
v_res_516_ = l_Std_Http_URI_endsInNumber(v_s_515_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg(){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___closed__0));
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___boxed(lean_object* v___dummy_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg();
return v_res_523_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg();
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(lean_object* v_s_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___boxed(lean_object* v_s_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(v_s_527_);
lean_dec_ref(v_s_527_);
return v_res_528_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(uint8_t v___x_529_, lean_object* v___y_530_, lean_object* v___x_531_, lean_object* v___x_532_, lean_object* v_a_533_, uint8_t v_b_534_){
_start:
{
uint8_t v___y_536_; lean_object* v_it_537_; lean_object* v_startInclusive_538_; lean_object* v_endExclusive_539_; uint8_t v___y_544_; 
if (v___x_529_ == 0)
{
uint8_t v___x_570_; 
v___x_570_ = 1;
v___y_544_ = v___x_570_;
goto v___jp_543_;
}
else
{
uint8_t v___x_571_; 
v___x_571_ = 0;
v___y_544_ = v___x_571_;
goto v___jp_543_;
}
v___jp_535_:
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = lean_string_utf8_extract_fast(v___y_530_, v_startInclusive_538_, v_endExclusive_539_);
lean_dec(v_endExclusive_539_);
lean_dec(v_startInclusive_538_);
v___x_541_ = l_Std_Http_URI_isValidDomainLabel(v___x_540_);
if (v___x_541_ == 0)
{
lean_dec(v_it_537_);
lean_dec(v___x_532_);
return v___x_541_;
}
else
{
v_a_533_ = v_it_537_;
v_b_534_ = v___y_536_;
goto _start;
}
}
v___jp_543_:
{
if (lean_obj_tag(v_a_533_) == 0)
{
lean_object* v_currPos_545_; lean_object* v_searcher_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_569_; 
v_currPos_545_ = lean_ctor_get(v_a_533_, 0);
v_searcher_546_ = lean_ctor_get(v_a_533_, 1);
v_isSharedCheck_569_ = !lean_is_exclusive(v_a_533_);
if (v_isSharedCheck_569_ == 0)
{
v___x_548_ = v_a_533_;
v_isShared_549_ = v_isSharedCheck_569_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_searcher_546_);
lean_inc(v_currPos_545_);
lean_dec(v_a_533_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_569_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
uint8_t v_decide_550_; 
v_decide_550_ = lean_nat_dec_eq(v_searcher_546_, v___x_532_);
if (v_decide_550_ == 0)
{
uint32_t v___x_551_; uint32_t v___x_552_; uint8_t v___x_553_; 
v___x_551_ = 46;
v___x_552_ = lean_string_utf8_get_fast(v___y_530_, v_searcher_546_);
v___x_553_ = lean_uint32_dec_eq(v___x_552_, v___x_551_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_string_utf8_next_fast(v___y_530_, v_searcher_546_);
lean_dec(v_searcher_546_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v___x_554_);
v___x_556_ = v___x_548_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_currPos_545_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_554_);
v___x_556_ = v_reuseFailAlloc_558_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
v_a_533_ = v___x_556_;
goto _start;
}
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v_slice_562_; lean_object* v_nextIt_564_; 
v___x_559_ = lean_string_utf8_next_fast(v___y_530_, v_searcher_546_);
v___x_560_ = lean_nat_sub(v___x_559_, v_searcher_546_);
v___x_561_ = lean_nat_add(v_searcher_546_, v___x_560_);
lean_dec(v___x_560_);
v_slice_562_ = l_String_Slice_subslice_x21(v___x_531_, v_currPos_545_, v_searcher_546_);
lean_inc(v___x_561_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v___x_561_);
lean_ctor_set(v___x_548_, 0, v___x_561_);
v_nextIt_564_ = v___x_548_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v___x_561_);
v_nextIt_564_ = v_reuseFailAlloc_567_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v_startInclusive_565_; lean_object* v_endExclusive_566_; 
v_startInclusive_565_ = lean_ctor_get(v_slice_562_, 0);
lean_inc(v_startInclusive_565_);
v_endExclusive_566_ = lean_ctor_get(v_slice_562_, 1);
lean_inc(v_endExclusive_566_);
lean_dec_ref(v_slice_562_);
v___y_536_ = v___y_544_;
v_it_537_ = v_nextIt_564_;
v_startInclusive_538_ = v_startInclusive_565_;
v_endExclusive_539_ = v_endExclusive_566_;
goto v___jp_535_;
}
}
}
else
{
lean_object* v___x_568_; 
lean_del_object(v___x_548_);
lean_dec(v_searcher_546_);
v___x_568_ = lean_box(1);
lean_inc(v___x_532_);
v___y_536_ = v___y_544_;
v_it_537_ = v___x_568_;
v_startInclusive_538_ = v_currPos_545_;
v_endExclusive_539_ = v___x_532_;
goto v___jp_535_;
}
}
}
else
{
lean_dec(v___x_532_);
return v_b_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg___boxed(lean_object* v___x_572_, lean_object* v___y_573_, lean_object* v___x_574_, lean_object* v___x_575_, lean_object* v_a_576_, lean_object* v_b_577_){
_start:
{
uint8_t v___x_4049__boxed_578_; uint8_t v_b_boxed_579_; uint8_t v_res_580_; lean_object* v_r_581_; 
v___x_4049__boxed_578_ = lean_unbox(v___x_572_);
v_b_boxed_579_ = lean_unbox(v_b_577_);
v_res_580_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_4049__boxed_578_, v___y_573_, v___x_574_, v___x_575_, v_a_576_, v_b_boxed_579_);
lean_dec_ref(v___x_574_);
lean_dec_ref(v___y_573_);
v_r_581_ = lean_box(v_res_580_);
return v_r_581_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(lean_object* v___x_582_, lean_object* v___y_583_, lean_object* v___x_584_, lean_object* v_a_585_, uint8_t v_b_586_){
_start:
{
if (lean_obj_tag(v_a_585_) == 0)
{
lean_object* v_currPos_587_; lean_object* v_searcher_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_603_; 
v_currPos_587_ = lean_ctor_get(v_a_585_, 0);
v_searcher_588_ = lean_ctor_get(v_a_585_, 1);
v_isSharedCheck_603_ = !lean_is_exclusive(v_a_585_);
if (v_isSharedCheck_603_ == 0)
{
v___x_590_ = v_a_585_;
v_isShared_591_ = v_isSharedCheck_603_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_searcher_588_);
lean_inc(v_currPos_587_);
lean_dec(v_a_585_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_603_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; uint8_t v___x_593_; uint8_t v_decide_594_; 
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_nat_dec_eq(v___x_582_, v___x_592_);
v_decide_594_ = lean_nat_dec_eq(v_searcher_588_, v___x_584_);
if (v_decide_594_ == 0)
{
uint32_t v___x_595_; uint32_t v___x_596_; uint8_t v___x_597_; 
v___x_595_ = 46;
v___x_596_ = lean_string_utf8_get_fast(v___y_583_, v_searcher_588_);
v___x_597_ = lean_uint32_dec_eq(v___x_596_, v___x_595_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = lean_string_utf8_next_fast(v___y_583_, v_searcher_588_);
lean_dec(v_searcher_588_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___x_598_);
v___x_600_ = v___x_590_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_currPos_587_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v___x_598_);
v___x_600_ = v_reuseFailAlloc_602_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
v_a_585_ = v___x_600_;
goto _start;
}
}
else
{
lean_del_object(v___x_590_);
lean_dec(v_searcher_588_);
lean_dec(v_currPos_587_);
return v___x_593_;
}
}
else
{
lean_del_object(v___x_590_);
lean_dec(v_searcher_588_);
lean_dec(v_currPos_587_);
return v___x_593_;
}
}
}
else
{
return v_b_586_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg___boxed(lean_object* v___x_604_, lean_object* v___y_605_, lean_object* v___x_606_, lean_object* v_a_607_, lean_object* v_b_608_){
_start:
{
uint8_t v_b_boxed_609_; uint8_t v_res_610_; lean_object* v_r_611_; 
v_b_boxed_609_ = lean_unbox(v_b_608_);
v_res_610_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_604_, v___y_605_, v___x_606_, v_a_607_, v_b_boxed_609_);
lean_dec(v___x_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___x_604_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_DomainName_ofString_x3f(lean_object* v_s_612_){
_start:
{
lean_object* v___x_613_; lean_object* v_lower_614_; uint8_t v___y_616_; uint8_t v___y_617_; lean_object* v___y_618_; lean_object* v___x_631_; lean_object* v___y_633_; uint8_t v___x_644_; 
v___x_613_ = lean_unsigned_to_nat(0u);
v_lower_614_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_612_, v___x_613_);
v___x_631_ = lean_string_utf8_byte_size(v_lower_614_);
v___x_644_ = lean_nat_dec_eq(v___x_631_, v___x_613_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_inc_ref(v_lower_614_);
v___x_645_ = l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3___redArg(v_lower_614_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_inc_ref(v_lower_614_);
v___y_633_ = v_lower_614_;
goto v___jp_632_;
}
else
{
lean_object* v_val_646_; lean_object* v_str_647_; lean_object* v_endExclusive_648_; lean_object* v___x_649_; 
v_val_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v___x_645_, 1);
v_str_647_ = lean_ctor_get(v_val_646_, 0);
lean_inc_ref(v_str_647_);
v_endExclusive_648_ = lean_ctor_get(v_val_646_, 2);
lean_inc(v_endExclusive_648_);
lean_dec(v_val_646_);
v___x_649_ = lean_string_utf8_extract_fast(v_str_647_, v___x_613_, v_endExclusive_648_);
lean_dec(v_endExclusive_648_);
lean_dec_ref(v_str_647_);
v___y_633_ = v___x_649_;
goto v___jp_632_;
}
}
else
{
lean_object* v___x_650_; 
lean_dec_ref(v_lower_614_);
v___x_650_ = lean_box(0);
return v___x_650_;
}
v___jp_615_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_619_ = lean_string_utf8_byte_size(v___y_618_);
lean_inc_ref(v___y_618_);
v___x_620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_620_, 0, v___y_618_);
lean_ctor_set(v___x_620_, 1, v___x_613_);
lean_ctor_set(v___x_620_, 2, v___x_619_);
v___x_621_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0);
v___x_622_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___y_616_, v___y_618_, v___x_620_, v___x_619_, v___x_621_, v___y_617_);
lean_dec_ref_known(v___x_620_, 3);
lean_dec_ref(v___y_618_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
lean_dec_ref(v_lower_614_);
v___x_623_ = lean_box(0);
return v___x_623_;
}
else
{
uint8_t v___x_624_; 
lean_inc_ref(v_lower_614_);
v___x_624_ = l_Std_Http_URI_endsInNumber(v_lower_614_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = lean_string_length(v_lower_614_);
v___x_626_ = lean_unsigned_to_nat(255u);
v___x_627_ = lean_nat_dec_le(v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
lean_dec_ref(v_lower_614_);
v___x_628_ = lean_box(0);
return v___x_628_;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_629_, 0, v_lower_614_);
return v___x_629_;
}
}
else
{
lean_object* v___x_630_; 
lean_dec_ref(v_lower_614_);
v___x_630_ = lean_box(0);
return v___x_630_;
}
}
}
v___jp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; uint8_t v___x_637_; 
v___x_634_ = lean_string_utf8_byte_size(v___y_633_);
v___x_635_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0);
v___x_636_ = 1;
v___x_637_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_631_, v___y_633_, v___x_634_, v___x_635_, v___x_636_);
lean_dec_ref(v___y_633_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
lean_inc_ref(v_lower_614_);
v___x_638_ = l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3___redArg(v_lower_614_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_inc_ref(v_lower_614_);
v___y_616_ = v___x_637_;
v___y_617_ = v___x_636_;
v___y_618_ = v_lower_614_;
goto v___jp_615_;
}
else
{
lean_object* v_val_639_; lean_object* v_str_640_; lean_object* v_endExclusive_641_; lean_object* v___x_642_; 
v_val_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_val_639_);
lean_dec_ref_known(v___x_638_, 1);
v_str_640_ = lean_ctor_get(v_val_639_, 0);
lean_inc_ref(v_str_640_);
v_endExclusive_641_ = lean_ctor_get(v_val_639_, 2);
lean_inc(v_endExclusive_641_);
lean_dec(v_val_639_);
v___x_642_ = lean_string_utf8_extract_fast(v_str_640_, v___x_613_, v_endExclusive_641_);
lean_dec(v_endExclusive_641_);
lean_dec_ref(v_str_640_);
v___y_616_ = v___x_637_;
v___y_617_ = v___x_636_;
v___y_618_ = v___x_642_;
goto v___jp_615_;
}
}
else
{
lean_object* v___x_643_; 
lean_dec_ref(v_lower_614_);
v___x_643_ = lean_box(0);
return v___x_643_;
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(lean_object* v___x_651_, lean_object* v___y_652_, lean_object* v___x_653_, lean_object* v___x_654_, lean_object* v_inst_655_, lean_object* v_R_656_, lean_object* v_a_657_, uint8_t v_b_658_, lean_object* v_c_659_){
_start:
{
uint8_t v___x_660_; 
v___x_660_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_651_, v___y_652_, v___x_654_, v_a_657_, v_b_658_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___boxed(lean_object* v___x_661_, lean_object* v___y_662_, lean_object* v___x_663_, lean_object* v___x_664_, lean_object* v_inst_665_, lean_object* v_R_666_, lean_object* v_a_667_, lean_object* v_b_668_, lean_object* v_c_669_){
_start:
{
uint8_t v_b_boxed_670_; uint8_t v_res_671_; lean_object* v_r_672_; 
v_b_boxed_670_ = lean_unbox(v_b_668_);
v_res_671_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(v___x_661_, v___y_662_, v___x_663_, v___x_664_, v_inst_665_, v_R_666_, v_a_667_, v_b_boxed_670_, v_c_669_);
lean_dec(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___x_661_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(uint8_t v___x_673_, lean_object* v___y_674_, lean_object* v___x_675_, lean_object* v___x_676_, lean_object* v_inst_677_, lean_object* v_R_678_, lean_object* v_a_679_, uint8_t v_b_680_, lean_object* v_c_681_){
_start:
{
uint8_t v___x_682_; 
v___x_682_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_673_, v___y_674_, v___x_675_, v___x_676_, v_a_679_, v_b_680_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___boxed(lean_object* v___x_683_, lean_object* v___y_684_, lean_object* v___x_685_, lean_object* v___x_686_, lean_object* v_inst_687_, lean_object* v_R_688_, lean_object* v_a_689_, lean_object* v_b_690_, lean_object* v_c_691_){
_start:
{
uint8_t v___x_4253__boxed_692_; uint8_t v_b_boxed_693_; uint8_t v_res_694_; lean_object* v_r_695_; 
v___x_4253__boxed_692_ = lean_unbox(v___x_683_);
v_b_boxed_693_ = lean_unbox(v_b_690_);
v_res_694_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(v___x_4253__boxed_692_, v___y_684_, v___x_685_, v___x_686_, v_inst_687_, v_R_688_, v_a_689_, v_b_boxed_693_, v_c_691_);
lean_dec_ref(v___x_685_);
lean_dec_ref(v___y_684_);
v_r_695_ = lean_box(v_res_694_);
return v_r_695_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx___impl(lean_object* v_x_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = lean_obj_tag_nat(v_x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx___impl___boxed(lean_object* v_x_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std_Http_URI_Host_ctorIdx___impl(v_x_698_);
lean_dec(v_x_698_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___redArg(lean_object* v_t_700_, lean_object* v_k_701_){
_start:
{
if (lean_obj_tag(v_t_700_) == 3)
{
return v_k_701_;
}
else
{
lean_object* v_name_702_; lean_object* v___x_703_; 
v_name_702_ = lean_ctor_get(v_t_700_, 0);
lean_inc_ref(v_name_702_);
lean_dec(v_t_700_);
v___x_703_ = lean_apply_1(v_k_701_, v_name_702_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim(lean_object* v_motive_704_, lean_object* v_ctorIdx_705_, lean_object* v_t_706_, lean_object* v_h_707_, lean_object* v_k_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_706_, v_k_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___boxed(lean_object* v_motive_710_, lean_object* v_ctorIdx_711_, lean_object* v_t_712_, lean_object* v_h_713_, lean_object* v_k_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Std_Http_URI_Host_ctorElim(v_motive_710_, v_ctorIdx_711_, v_t_712_, v_h_713_, v_k_714_);
lean_dec(v_ctorIdx_711_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim___redArg(lean_object* v_t_716_, lean_object* v_name_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_716_, v_name_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim(lean_object* v_motive_719_, lean_object* v_t_720_, lean_object* v_h_721_, lean_object* v_name_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_720_, v_name_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim___redArg(lean_object* v_t_724_, lean_object* v_ipv4_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_724_, v_ipv4_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim(lean_object* v_motive_727_, lean_object* v_t_728_, lean_object* v_h_729_, lean_object* v_ipv4_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_728_, v_ipv4_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim___redArg(lean_object* v_t_732_, lean_object* v_ipv6_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_732_, v_ipv6_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim(lean_object* v_motive_735_, lean_object* v_t_736_, lean_object* v_h_737_, lean_object* v_ipv6_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_736_, v_ipv6_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_empty_elim___redArg(lean_object* v_t_740_, lean_object* v_empty_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_740_, v_empty_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_empty_elim(lean_object* v_motive_743_, lean_object* v_t_744_, lean_object* v_h_745_, lean_object* v_empty_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_744_, v_empty_746_);
return v___x_747_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default___closed__0(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default(void){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = lean_obj_once(&l_Std_Http_URI_instInhabitedHost_default___closed__0, &l_Std_Http_URI_instInhabitedHost_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedHost_default___closed__0);
return v___x_750_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost(void){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_Http_URI_instInhabitedHost_default;
return v___x_751_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqHost_beq(lean_object* v_x_752_, lean_object* v_x_753_){
_start:
{
switch(lean_obj_tag(v_x_752_))
{
case 0:
{
if (lean_obj_tag(v_x_753_) == 0)
{
lean_object* v_name_754_; lean_object* v_name_755_; uint8_t v___x_756_; 
v_name_754_ = lean_ctor_get(v_x_752_, 0);
v_name_755_ = lean_ctor_get(v_x_753_, 0);
v___x_756_ = lean_string_dec_eq(v_name_754_, v_name_755_);
return v___x_756_;
}
else
{
uint8_t v___x_757_; 
v___x_757_ = 0;
return v___x_757_;
}
}
case 1:
{
if (lean_obj_tag(v_x_753_) == 1)
{
lean_object* v_ipv4_758_; lean_object* v_ipv4_759_; uint8_t v___x_760_; 
v_ipv4_758_ = lean_ctor_get(v_x_752_, 0);
v_ipv4_759_ = lean_ctor_get(v_x_753_, 0);
v___x_760_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_ipv4_758_, v_ipv4_759_);
return v___x_760_;
}
else
{
uint8_t v___x_761_; 
v___x_761_ = 0;
return v___x_761_;
}
}
case 2:
{
if (lean_obj_tag(v_x_753_) == 2)
{
lean_object* v_ipv6_762_; lean_object* v_ipv6_763_; uint8_t v___x_764_; 
v_ipv6_762_ = lean_ctor_get(v_x_752_, 0);
v_ipv6_763_ = lean_ctor_get(v_x_753_, 0);
v___x_764_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_ipv6_762_, v_ipv6_763_);
return v___x_764_;
}
else
{
uint8_t v___x_765_; 
v___x_765_ = 0;
return v___x_765_;
}
}
default: 
{
if (lean_obj_tag(v_x_753_) == 3)
{
uint8_t v___x_766_; 
v___x_766_ = 1;
return v___x_766_;
}
else
{
uint8_t v___x_767_; 
v___x_767_ = 0;
return v___x_767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqHost_beq___boxed(lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
uint8_t v_res_770_; lean_object* v_r_771_; 
v_res_770_ = l_Std_Http_URI_instBEqHost_beq(v_x_768_, v_x_769_);
lean_dec(v_x_769_);
lean_dec(v_x_768_);
v_r_771_ = lean_box(v_res_770_);
return v_r_771_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__6(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_unsigned_to_nat(2u);
v___x_782_ = lean_nat_to_int(v___x_781_);
return v___x_782_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__7(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_unsigned_to_nat(1u);
v___x_784_ = lean_nat_to_int(v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0(lean_object* v_x_785_, lean_object* v_prec_786_){
_start:
{
lean_object* v___y_788_; lean_object* v_ctr_789_; lean_object* v_a_790_; lean_object* v___y_802_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = lean_unsigned_to_nat(1024u);
v___x_835_ = lean_nat_dec_le(v___x_834_, v_prec_786_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
v___x_836_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__6, &l_Std_Http_URI_instReprHost___lam__0___closed__6_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__6);
v___y_802_ = v___x_836_;
goto v___jp_801_;
}
else
{
lean_object* v___x_837_; 
v___x_837_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__7, &l_Std_Http_URI_instReprHost___lam__0___closed__7_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__7);
v___y_802_ = v___x_837_;
goto v___jp_801_;
}
v___jp_787_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_791_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_792_ = lean_string_append(v___x_791_, v_ctr_789_);
v___x_793_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
v___x_794_ = lean_box(1);
v___x_795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v_a_790_);
lean_inc(v___y_788_);
v___x_797_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_797_, 0, v___y_788_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = 0;
v___x_799_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_799_, 0, v___x_797_);
lean_ctor_set_uint8(v___x_799_, sizeof(void*)*1, v___x_798_);
v___x_800_ = l_Repr_addAppParen(v___x_799_, v_prec_786_);
return v___x_800_;
}
v___jp_801_:
{
switch(lean_obj_tag(v_x_785_))
{
case 0:
{
lean_object* v_name_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_812_; 
v_name_803_ = lean_ctor_get(v_x_785_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v_x_785_);
if (v_isSharedCheck_812_ == 0)
{
v___x_805_ = v_x_785_;
v_isShared_806_ = v_isSharedCheck_812_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_name_803_);
lean_dec(v_x_785_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_812_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_807_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_808_ = l_String_quote(v_name_803_);
if (v_isShared_806_ == 0)
{
lean_ctor_set_tag(v___x_805_, 3);
lean_ctor_set(v___x_805_, 0, v___x_808_);
v___x_810_ = v___x_805_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
v___y_788_ = v___y_802_;
v_ctr_789_ = v___x_807_;
v_a_790_ = v___x_810_;
goto v___jp_787_;
}
}
}
case 1:
{
lean_object* v_ipv4_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_822_; 
v_ipv4_813_ = lean_ctor_get(v_x_785_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v_x_785_);
if (v_isSharedCheck_822_ == 0)
{
v___x_815_ = v_x_785_;
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_ipv4_813_);
lean_dec(v_x_785_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_817_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_818_ = lean_uv_ntop_v4(v_ipv4_813_);
lean_dec_ref(v_ipv4_813_);
if (v_isShared_816_ == 0)
{
lean_ctor_set_tag(v___x_815_, 3);
lean_ctor_set(v___x_815_, 0, v___x_818_);
v___x_820_ = v___x_815_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
v___y_788_ = v___y_802_;
v_ctr_789_ = v___x_817_;
v_a_790_ = v___x_820_;
goto v___jp_787_;
}
}
}
case 2:
{
lean_object* v_ipv6_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_832_; 
v_ipv6_823_ = lean_ctor_get(v_x_785_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v_x_785_);
if (v_isSharedCheck_832_ == 0)
{
v___x_825_ = v_x_785_;
v_isShared_826_ = v_isSharedCheck_832_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_ipv6_823_);
lean_dec(v_x_785_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_832_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_827_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_828_ = lean_uv_ntop_v6(v_ipv6_823_);
lean_dec_ref(v_ipv6_823_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 3);
lean_ctor_set(v___x_825_, 0, v___x_828_);
v___x_830_ = v___x_825_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
v___y_788_ = v___y_802_;
v_ctr_789_ = v___x_827_;
v_a_790_ = v___x_830_;
goto v___jp_787_;
}
}
}
default: 
{
lean_object* v___x_833_; 
v___x_833_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__5));
return v___x_833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0___boxed(lean_object* v_x_838_, lean_object* v_prec_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_Http_URI_instReprHost___lam__0(v_x_838_, v_prec_839_);
lean_dec(v_prec_839_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0(lean_object* v_x_846_){
_start:
{
switch(lean_obj_tag(v_x_846_))
{
case 0:
{
lean_object* v_name_847_; 
v_name_847_ = lean_ctor_get(v_x_846_, 0);
lean_inc_ref(v_name_847_);
return v_name_847_;
}
case 1:
{
lean_object* v_ipv4_848_; lean_object* v___x_849_; 
v_ipv4_848_ = lean_ctor_get(v_x_846_, 0);
v___x_849_ = lean_uv_ntop_v4(v_ipv4_848_);
return v___x_849_;
}
case 2:
{
lean_object* v_ipv6_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_ipv6_850_ = lean_ctor_get(v_x_846_, 0);
v___x_851_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_852_ = lean_uv_ntop_v6(v_ipv6_850_);
v___x_853_ = lean_string_append(v___x_851_, v___x_852_);
lean_dec_ref(v___x_852_);
v___x_854_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_855_ = lean_string_append(v___x_853_, v___x_854_);
return v___x_855_;
}
default: 
{
lean_object* v___x_856_; 
v___x_856_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
return v___x_856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0___boxed(lean_object* v_x_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Std_Http_URI_instToStringHost___lam__0(v_x_857_);
lean_dec(v_x_857_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___impl(lean_object* v_x_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = lean_obj_tag_nat(v_x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___impl___boxed(lean_object* v_x_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Std_Http_URI_Port_ctorIdx___impl(v_x_863_);
lean_dec(v_x_863_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg(lean_object* v_t_865_, lean_object* v_k_866_){
_start:
{
if (lean_obj_tag(v_t_865_) == 2)
{
uint16_t v_port_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_port_867_ = lean_ctor_get_uint16(v_t_865_, 0);
v___x_868_ = lean_box(v_port_867_);
v___x_869_ = lean_apply_1(v_k_866_, v___x_868_);
return v___x_869_;
}
else
{
return v_k_866_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg___boxed(lean_object* v_t_870_, lean_object* v_k_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_870_, v_k_871_);
lean_dec(v_t_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim(lean_object* v_motive_873_, lean_object* v_ctorIdx_874_, lean_object* v_t_875_, lean_object* v_h_876_, lean_object* v_k_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_875_, v_k_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___boxed(lean_object* v_motive_879_, lean_object* v_ctorIdx_880_, lean_object* v_t_881_, lean_object* v_h_882_, lean_object* v_k_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_Http_URI_Port_ctorElim(v_motive_879_, v_ctorIdx_880_, v_t_881_, v_h_882_, v_k_883_);
lean_dec(v_t_881_);
lean_dec(v_ctorIdx_880_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg(lean_object* v_t_885_, lean_object* v_omitted_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_885_, v_omitted_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg___boxed(lean_object* v_t_888_, lean_object* v_omitted_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Std_Http_URI_Port_omitted_elim___redArg(v_t_888_, v_omitted_889_);
lean_dec(v_t_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim(lean_object* v_motive_891_, lean_object* v_t_892_, lean_object* v_h_893_, lean_object* v_omitted_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_892_, v_omitted_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___boxed(lean_object* v_motive_896_, lean_object* v_t_897_, lean_object* v_h_898_, lean_object* v_omitted_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Std_Http_URI_Port_omitted_elim(v_motive_896_, v_t_897_, v_h_898_, v_omitted_899_);
lean_dec(v_t_897_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg(lean_object* v_t_901_, lean_object* v_empty_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_901_, v_empty_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg___boxed(lean_object* v_t_904_, lean_object* v_empty_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_Http_URI_Port_empty_elim___redArg(v_t_904_, v_empty_905_);
lean_dec(v_t_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim(lean_object* v_motive_907_, lean_object* v_t_908_, lean_object* v_h_909_, lean_object* v_empty_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_908_, v_empty_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___boxed(lean_object* v_motive_912_, lean_object* v_t_913_, lean_object* v_h_914_, lean_object* v_empty_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Std_Http_URI_Port_empty_elim(v_motive_912_, v_t_913_, v_h_914_, v_empty_915_);
lean_dec(v_t_913_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg(lean_object* v_t_917_, lean_object* v_value_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_917_, v_value_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg___boxed(lean_object* v_t_920_, lean_object* v_value_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Std_Http_URI_Port_value_elim___redArg(v_t_920_, v_value_921_);
lean_dec(v_t_920_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim(lean_object* v_motive_923_, lean_object* v_t_924_, lean_object* v_h_925_, lean_object* v_value_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_924_, v_value_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___boxed(lean_object* v_motive_928_, lean_object* v_t_929_, lean_object* v_h_930_, lean_object* v_value_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Std_Http_URI_Port_value_elim(v_motive_928_, v_t_929_, v_h_930_, v_value_931_);
lean_dec(v_t_929_);
return v_res_932_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort_default(void){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = lean_box(0);
return v___x_933_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort(void){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = lean_box(0);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr(lean_object* v_x_947_, lean_object* v_prec_948_){
_start:
{
lean_object* v___y_950_; lean_object* v___y_957_; 
switch(lean_obj_tag(v_x_947_))
{
case 0:
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = lean_unsigned_to_nat(1024u);
v___x_964_ = lean_nat_dec_le(v___x_963_, v_prec_948_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; 
v___x_965_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__6, &l_Std_Http_URI_instReprHost___lam__0___closed__6_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__6);
v___y_957_ = v___x_965_;
goto v___jp_956_;
}
else
{
lean_object* v___x_966_; 
v___x_966_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__7, &l_Std_Http_URI_instReprHost___lam__0___closed__7_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__7);
v___y_957_ = v___x_966_;
goto v___jp_956_;
}
}
case 1:
{
lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_967_ = lean_unsigned_to_nat(1024u);
v___x_968_ = lean_nat_dec_le(v___x_967_, v_prec_948_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; 
v___x_969_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__6, &l_Std_Http_URI_instReprHost___lam__0___closed__6_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__6);
v___y_950_ = v___x_969_;
goto v___jp_949_;
}
else
{
lean_object* v___x_970_; 
v___x_970_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__7, &l_Std_Http_URI_instReprHost___lam__0___closed__7_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__7);
v___y_950_ = v___x_970_;
goto v___jp_949_;
}
}
default: 
{
uint16_t v_port_971_; lean_object* v___y_973_; lean_object* v___x_983_; uint8_t v___x_984_; 
v_port_971_ = lean_ctor_get_uint16(v_x_947_, 0);
v___x_983_ = lean_unsigned_to_nat(1024u);
v___x_984_ = lean_nat_dec_le(v___x_983_, v_prec_948_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
v___x_985_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__6, &l_Std_Http_URI_instReprHost___lam__0___closed__6_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__6);
v___y_973_ = v___x_985_;
goto v___jp_972_;
}
else
{
lean_object* v___x_986_; 
v___x_986_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__7, &l_Std_Http_URI_instReprHost___lam__0___closed__7_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__7);
v___y_973_ = v___x_986_;
goto v___jp_972_;
}
v___jp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_974_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__6));
v___x_975_ = lean_uint16_to_nat(v_port_971_);
v___x_976_ = l_Nat_reprFast(v___x_975_);
v___x_977_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_974_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
lean_inc(v___y_973_);
v___x_979_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_979_, 0, v___y_973_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = 0;
v___x_981_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*1, v___x_980_);
v___x_982_ = l_Repr_addAppParen(v___x_981_, v_prec_948_);
return v___x_982_;
}
}
}
v___jp_949_:
{
lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_951_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__1));
lean_inc(v___y_950_);
v___x_952_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_952_, 0, v___y_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = 0;
v___x_954_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set_uint8(v___x_954_, sizeof(void*)*1, v___x_953_);
v___x_955_ = l_Repr_addAppParen(v___x_954_, v_prec_948_);
return v___x_955_;
}
v___jp_956_:
{
lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_958_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__3));
lean_inc(v___y_957_);
v___x_959_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_959_, 0, v___y_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = 0;
v___x_961_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*1, v___x_960_);
v___x_962_ = l_Repr_addAppParen(v___x_961_, v_prec_948_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr___boxed(lean_object* v_x_987_, lean_object* v_prec_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_Http_URI_instReprPort_repr(v_x_987_, v_prec_988_);
lean_dec(v_prec_988_);
lean_dec(v_x_987_);
return v_res_989_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort_decEq(lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
switch(lean_obj_tag(v_x_992_))
{
case 0:
{
if (lean_obj_tag(v_x_993_) == 0)
{
uint8_t v___x_994_; 
v___x_994_ = 1;
return v___x_994_;
}
else
{
uint8_t v___x_995_; 
v___x_995_ = 0;
return v___x_995_;
}
}
case 1:
{
if (lean_obj_tag(v_x_993_) == 1)
{
uint8_t v___x_996_; 
v___x_996_ = 1;
return v___x_996_;
}
else
{
uint8_t v___x_997_; 
v___x_997_ = 0;
return v___x_997_;
}
}
default: 
{
if (lean_obj_tag(v_x_993_) == 2)
{
uint16_t v_port_998_; uint16_t v_port_999_; uint8_t v___x_1000_; 
v_port_998_ = lean_ctor_get_uint16(v_x_992_, 0);
v_port_999_ = lean_ctor_get_uint16(v_x_993_, 0);
v___x_1000_ = lean_uint16_dec_eq(v_port_998_, v_port_999_);
return v___x_1000_;
}
else
{
uint8_t v___x_1001_; 
v___x_1001_ = 0;
return v___x_1001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort_decEq___boxed(lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
uint8_t v_res_1004_; lean_object* v_r_1005_; 
v_res_1004_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_1002_, v_x_1003_);
lean_dec(v_x_1003_);
lean_dec(v_x_1002_);
v_r_1005_ = lean_box(v_res_1004_);
return v_r_1005_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort(lean_object* v_x_1006_, lean_object* v_x_1007_){
_start:
{
uint8_t v___x_1008_; 
v___x_1008_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_1006_, v_x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort___boxed(lean_object* v_x_1009_, lean_object* v_x_1010_){
_start:
{
uint8_t v_res_1011_; lean_object* v_r_1012_; 
v_res_1011_ = l_Std_Http_URI_instDecidableEqPort(v_x_1009_, v_x_1010_);
lean_dec(v_x_1010_);
lean_dec(v_x_1009_);
v_r_1012_ = lean_box(v_res_1011_);
return v_r_1012_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1013_ = lean_box(0);
v___x_1014_ = l_Std_Http_URI_instInhabitedHost_default;
v___x_1015_ = lean_box(0);
v___x_1016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___x_1014_);
lean_ctor_set(v___x_1016_, 2, v___x_1013_);
return v___x_1016_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default(void){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_obj_once(&l_Std_Http_URI_instInhabitedAuthority_default___closed__0, &l_Std_Http_URI_instInhabitedAuthority_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0);
return v___x_1017_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority(void){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Std_Http_URI_instInhabitedAuthority_default;
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(lean_object* v_x_1019_, lean_object* v_x_1020_){
_start:
{
if (lean_obj_tag(v_x_1019_) == 0)
{
lean_object* v___x_1021_; 
v___x_1021_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1021_;
}
else
{
lean_object* v_val_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_val_1022_ = lean_ctor_get(v_x_1019_, 0);
lean_inc(v_val_1022_);
lean_dec_ref_known(v_x_1019_, 1);
v___x_1023_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1024_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_val_1022_);
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = l_Repr_addAppParen(v___x_1025_, v_x_1020_);
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0___boxed(lean_object* v_x_1027_, lean_object* v_x_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_x_1027_, v_x_1028_);
lean_dec(v_x_1028_);
return v_res_1029_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_unsigned_to_nat(8u);
v___x_1043_ = lean_nat_to_int(v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg(lean_object* v_x_1047_){
_start:
{
lean_object* v_userInfo_1048_; lean_object* v_host_1049_; lean_object* v_port_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___y_1069_; lean_object* v___x_1089_; lean_object* v_ctr_1091_; lean_object* v_a_1092_; 
v_userInfo_1048_ = lean_ctor_get(v_x_1047_, 0);
lean_inc(v_userInfo_1048_);
v_host_1049_ = lean_ctor_get(v_x_1047_, 1);
lean_inc(v_host_1049_);
v_port_1050_ = lean_ctor_get(v_x_1047_, 2);
lean_inc(v_port_1050_);
lean_dec_ref(v_x_1047_);
v___x_1051_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1052_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3));
v___x_1053_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_1054_ = lean_unsigned_to_nat(0u);
v___x_1055_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_userInfo_1048_, v___x_1054_);
v___x_1056_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1053_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = 0;
v___x_1058_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set_uint8(v___x_1058_, sizeof(void*)*1, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1052_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = lean_box(1);
v___x_1063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_1065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v___x_1051_);
v___x_1067_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_1089_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__6, &l_Std_Http_URI_instReprHost___lam__0___closed__6_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__6);
switch(lean_obj_tag(v_host_1049_))
{
case 0:
{
lean_object* v_name_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1110_; 
v_name_1101_ = lean_ctor_get(v_host_1049_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_host_1049_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1103_ = v_host_1049_;
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_name_1101_);
lean_dec(v_host_1049_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1105_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_1106_ = l_String_quote(v_name_1101_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set_tag(v___x_1103_, 3);
lean_ctor_set(v___x_1103_, 0, v___x_1106_);
v___x_1108_ = v___x_1103_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
v_ctr_1091_ = v___x_1105_;
v_a_1092_ = v___x_1108_;
goto v___jp_1090_;
}
}
}
case 1:
{
lean_object* v_ipv4_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1120_; 
v_ipv4_1111_ = lean_ctor_get(v_host_1049_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_host_1049_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1113_ = v_host_1049_;
v_isShared_1114_ = v_isSharedCheck_1120_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_ipv4_1111_);
lean_dec(v_host_1049_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1120_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1115_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_1116_ = lean_uv_ntop_v4(v_ipv4_1111_);
lean_dec_ref(v_ipv4_1111_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 3);
lean_ctor_set(v___x_1113_, 0, v___x_1116_);
v___x_1118_ = v___x_1113_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
v_ctr_1091_ = v___x_1115_;
v_a_1092_ = v___x_1118_;
goto v___jp_1090_;
}
}
}
case 2:
{
lean_object* v_ipv6_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1130_; 
v_ipv6_1121_ = lean_ctor_get(v_host_1049_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_host_1049_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1123_ = v_host_1049_;
v_isShared_1124_ = v_isSharedCheck_1130_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_ipv6_1121_);
lean_dec(v_host_1049_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1130_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
v___x_1125_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_1126_ = lean_uv_ntop_v6(v_ipv6_1121_);
lean_dec_ref(v_ipv6_1121_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set_tag(v___x_1123_, 3);
lean_ctor_set(v___x_1123_, 0, v___x_1126_);
v___x_1128_ = v___x_1123_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
v_ctr_1091_ = v___x_1125_;
v_a_1092_ = v___x_1128_;
goto v___jp_1090_;
}
}
}
default: 
{
lean_object* v___x_1131_; 
v___x_1131_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__5));
v___y_1069_ = v___x_1131_;
goto v___jp_1068_;
}
}
v___jp_1068_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1070_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1067_);
lean_ctor_set(v___x_1070_, 1, v___y_1069_);
v___x_1071_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set_uint8(v___x_1071_, sizeof(void*)*1, v___x_1057_);
v___x_1072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1066_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v___x_1060_);
v___x_1074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v___x_1062_);
v___x_1075_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_1076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___x_1051_);
v___x_1078_ = l_Std_Http_URI_instReprPort_repr(v_port_1050_, v___x_1054_);
lean_dec(v_port_1050_);
v___x_1079_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1067_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*1, v___x_1057_);
v___x_1081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1077_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1083_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v___x_1081_);
v___x_1085_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1082_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set_uint8(v___x_1088_, sizeof(void*)*1, v___x_1057_);
return v___x_1088_;
}
v___jp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1093_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_1094_ = lean_string_append(v___x_1093_, v_ctr_1091_);
v___x_1095_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v___x_1062_);
v___x_1097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
lean_ctor_set(v___x_1097_, 1, v_a_1092_);
v___x_1098_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1089_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*1, v___x_1057_);
v___x_1100_ = l_Repr_addAppParen(v___x_1099_, v___x_1054_);
v___y_1069_ = v___x_1100_;
goto v___jp_1068_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr(lean_object* v_x_1132_, lean_object* v_prec_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_x_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___boxed(lean_object* v_x_1135_, lean_object* v_prec_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Std_Http_URI_instReprAuthority_repr(v_x_1135_, v_prec_1136_);
lean_dec(v_prec_1136_);
return v_res_1137_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
if (lean_obj_tag(v_x_1140_) == 0)
{
if (lean_obj_tag(v_x_1141_) == 0)
{
uint8_t v___x_1142_; 
v___x_1142_ = 1;
return v___x_1142_;
}
else
{
uint8_t v___x_1143_; 
v___x_1143_ = 0;
return v___x_1143_;
}
}
else
{
if (lean_obj_tag(v_x_1141_) == 0)
{
uint8_t v___x_1144_; 
v___x_1144_ = 0;
return v___x_1144_;
}
else
{
lean_object* v_val_1145_; lean_object* v_val_1146_; uint8_t v___x_1147_; 
v_val_1145_ = lean_ctor_get(v_x_1140_, 0);
v_val_1146_ = lean_ctor_get(v_x_1141_, 0);
v___x_1147_ = l_Std_Http_URI_instBEqUserInfo_beq(v_val_1145_, v_val_1146_);
return v___x_1147_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0___boxed(lean_object* v_x_1148_, lean_object* v_x_1149_){
_start:
{
uint8_t v_res_1150_; lean_object* v_r_1151_; 
v_res_1150_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_x_1148_, v_x_1149_);
lean_dec(v_x_1149_);
lean_dec(v_x_1148_);
v_r_1151_ = lean_box(v_res_1150_);
return v_r_1151_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqAuthority_beq(lean_object* v_x_1152_, lean_object* v_x_1153_){
_start:
{
lean_object* v_userInfo_1154_; lean_object* v_host_1155_; lean_object* v_port_1156_; lean_object* v_userInfo_1157_; lean_object* v_host_1158_; lean_object* v_port_1159_; uint8_t v___x_1160_; 
v_userInfo_1154_ = lean_ctor_get(v_x_1152_, 0);
v_host_1155_ = lean_ctor_get(v_x_1152_, 1);
v_port_1156_ = lean_ctor_get(v_x_1152_, 2);
v_userInfo_1157_ = lean_ctor_get(v_x_1153_, 0);
v_host_1158_ = lean_ctor_get(v_x_1153_, 1);
v_port_1159_ = lean_ctor_get(v_x_1153_, 2);
v___x_1160_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_userInfo_1154_, v_userInfo_1157_);
if (v___x_1160_ == 0)
{
return v___x_1160_;
}
else
{
uint8_t v___x_1161_; 
v___x_1161_ = l_Std_Http_URI_instBEqHost_beq(v_host_1155_, v_host_1158_);
if (v___x_1161_ == 0)
{
return v___x_1161_;
}
else
{
uint8_t v___x_1162_; 
v___x_1162_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1156_, v_port_1159_);
return v___x_1162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqAuthority_beq___boxed(lean_object* v_x_1163_, lean_object* v_x_1164_){
_start:
{
uint8_t v_res_1165_; lean_object* v_r_1166_; 
v_res_1165_ = l_Std_Http_URI_instBEqAuthority_beq(v_x_1163_, v_x_1164_);
lean_dec_ref(v_x_1164_);
lean_dec_ref(v_x_1163_);
v_r_1166_ = lean_box(v_res_1165_);
return v_r_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringAuthority___lam__0(lean_object* v_auth_1171_){
_start:
{
lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v_userInfo_1178_; lean_object* v_host_1179_; lean_object* v_port_1180_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1192_; 
v_userInfo_1178_ = lean_ctor_get(v_auth_1171_, 0);
lean_inc(v_userInfo_1178_);
v_host_1179_ = lean_ctor_get(v_auth_1171_, 1);
lean_inc(v_host_1179_);
v_port_1180_ = lean_ctor_get(v_auth_1171_, 2);
lean_inc(v_port_1180_);
lean_dec_ref(v_auth_1171_);
if (lean_obj_tag(v_userInfo_1178_) == 0)
{
lean_object* v___x_1203_; 
v___x_1203_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_1192_ = v___x_1203_;
goto v___jp_1191_;
}
else
{
lean_object* v_val_1204_; lean_object* v_password_1205_; 
v_val_1204_ = lean_ctor_get(v_userInfo_1178_, 0);
lean_inc(v_val_1204_);
lean_dec_ref_known(v_userInfo_1178_, 1);
v_password_1205_ = lean_ctor_get(v_val_1204_, 1);
if (lean_obj_tag(v_password_1205_) == 0)
{
lean_object* v_username_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_username_1206_ = lean_ctor_get(v_val_1204_, 0);
lean_inc_ref(v_username_1206_);
lean_dec(v_val_1204_);
v___x_1207_ = lean_string_from_utf8_unchecked(v_username_1206_);
v___x_1208_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1209_ = lean_string_append(v___x_1207_, v___x_1208_);
v___y_1192_ = v___x_1209_;
goto v___jp_1191_;
}
else
{
lean_object* v_username_1210_; lean_object* v_val_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
lean_inc_ref(v_password_1205_);
v_username_1210_ = lean_ctor_get(v_val_1204_, 0);
lean_inc_ref(v_username_1210_);
lean_dec(v_val_1204_);
v_val_1211_ = lean_ctor_get(v_password_1205_, 0);
lean_inc(v_val_1211_);
lean_dec_ref_known(v_password_1205_, 1);
v___x_1212_ = lean_string_from_utf8_unchecked(v_username_1210_);
v___x_1213_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_1214_ = lean_string_append(v___x_1212_, v___x_1213_);
v___x_1215_ = lean_string_from_utf8_unchecked(v_val_1211_);
v___x_1216_ = lean_string_append(v___x_1214_, v___x_1215_);
lean_dec_ref(v___x_1215_);
v___x_1217_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1218_ = lean_string_append(v___x_1216_, v___x_1217_);
v___y_1192_ = v___x_1218_;
goto v___jp_1191_;
}
}
v___jp_1172_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_string_append(v___y_1173_, v___y_1174_);
lean_dec_ref(v___y_1174_);
v___x_1177_ = lean_string_append(v___x_1176_, v___y_1175_);
lean_dec_ref(v___y_1175_);
return v___x_1177_;
}
v___jp_1181_:
{
switch(lean_obj_tag(v_port_1180_))
{
case 0:
{
lean_object* v___x_1184_; 
v___x_1184_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_1173_ = v___y_1182_;
v___y_1174_ = v___y_1183_;
v___y_1175_ = v___x_1184_;
goto v___jp_1172_;
}
case 1:
{
lean_object* v___x_1185_; 
v___x_1185_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1173_ = v___y_1182_;
v___y_1174_ = v___y_1183_;
v___y_1175_ = v___x_1185_;
goto v___jp_1172_;
}
default: 
{
uint16_t v_port_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v_port_1186_ = lean_ctor_get_uint16(v_port_1180_, 0);
lean_dec_ref_known(v_port_1180_, 0);
v___x_1187_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_1188_ = lean_uint16_to_nat(v_port_1186_);
v___x_1189_ = l_Nat_reprFast(v___x_1188_);
v___x_1190_ = lean_string_append(v___x_1187_, v___x_1189_);
lean_dec_ref(v___x_1189_);
v___y_1173_ = v___y_1182_;
v___y_1174_ = v___y_1183_;
v___y_1175_ = v___x_1190_;
goto v___jp_1172_;
}
}
}
v___jp_1191_:
{
switch(lean_obj_tag(v_host_1179_))
{
case 0:
{
lean_object* v_name_1193_; 
v_name_1193_ = lean_ctor_get(v_host_1179_, 0);
lean_inc_ref(v_name_1193_);
lean_dec_ref_known(v_host_1179_, 1);
v___y_1182_ = v___y_1192_;
v___y_1183_ = v_name_1193_;
goto v___jp_1181_;
}
case 1:
{
lean_object* v_ipv4_1194_; lean_object* v___x_1195_; 
v_ipv4_1194_ = lean_ctor_get(v_host_1179_, 0);
lean_inc_ref(v_ipv4_1194_);
lean_dec_ref_known(v_host_1179_, 1);
v___x_1195_ = lean_uv_ntop_v4(v_ipv4_1194_);
lean_dec_ref(v_ipv4_1194_);
v___y_1182_ = v___y_1192_;
v___y_1183_ = v___x_1195_;
goto v___jp_1181_;
}
case 2:
{
lean_object* v_ipv6_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v_ipv6_1196_ = lean_ctor_get(v_host_1179_, 0);
lean_inc_ref(v_ipv6_1196_);
lean_dec_ref_known(v_host_1179_, 1);
v___x_1197_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_1198_ = lean_uv_ntop_v6(v_ipv6_1196_);
lean_dec_ref(v_ipv6_1196_);
v___x_1199_ = lean_string_append(v___x_1197_, v___x_1198_);
lean_dec_ref(v___x_1198_);
v___x_1200_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_1201_ = lean_string_append(v___x_1199_, v___x_1200_);
v___y_1182_ = v___y_1192_;
v___y_1183_ = v___x_1201_;
goto v___jp_1181_;
}
default: 
{
lean_object* v___x_1202_; 
v___x_1202_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_1182_ = v___y_1192_;
v___y_1183_ = v___x_1202_;
goto v___jp_1181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1228_, lean_object* v_x_1229_, lean_object* v_x_1230_){
_start:
{
if (lean_obj_tag(v_x_1230_) == 0)
{
lean_dec(v_x_1228_);
return v_x_1229_;
}
else
{
lean_object* v_head_1231_; lean_object* v_tail_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1244_; 
v_head_1231_ = lean_ctor_get(v_x_1230_, 0);
v_tail_1232_ = lean_ctor_get(v_x_1230_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_x_1230_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1234_ = v_x_1230_;
v_isShared_1235_ = v_isSharedCheck_1244_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_tail_1232_);
lean_inc(v_head_1231_);
lean_dec(v_x_1230_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1244_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
lean_inc(v_x_1228_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set_tag(v___x_1234_, 5);
lean_ctor_set(v___x_1234_, 1, v_x_1228_);
lean_ctor_set(v___x_1234_, 0, v_x_1229_);
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_x_1229_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_x_1228_);
v___x_1237_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1238_ = lean_string_from_utf8_unchecked(v_head_1231_);
v___x_1239_ = l_String_quote(v___x_1238_);
v___x_1240_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
v___x_1241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1237_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v_x_1229_ = v___x_1241_;
v_x_1230_ = v_tail_1232_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(lean_object* v_x_1245_, lean_object* v_x_1246_, lean_object* v_x_1247_){
_start:
{
if (lean_obj_tag(v_x_1247_) == 0)
{
lean_dec(v_x_1245_);
return v_x_1246_;
}
else
{
lean_object* v_head_1248_; lean_object* v_tail_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1261_; 
v_head_1248_ = lean_ctor_get(v_x_1247_, 0);
v_tail_1249_ = lean_ctor_get(v_x_1247_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_x_1247_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1251_ = v_x_1247_;
v_isShared_1252_ = v_isSharedCheck_1261_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_tail_1249_);
lean_inc(v_head_1248_);
lean_dec(v_x_1247_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1261_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
lean_inc(v_x_1245_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set_tag(v___x_1251_, 5);
lean_ctor_set(v___x_1251_, 1, v_x_1245_);
lean_ctor_set(v___x_1251_, 0, v_x_1246_);
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_x_1246_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_x_1245_);
v___x_1254_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1255_ = lean_string_from_utf8_unchecked(v_head_1248_);
v___x_1256_ = l_String_quote(v___x_1255_);
v___x_1257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
v___x_1258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1254_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(v_x_1245_, v___x_1258_, v_tail_1249_);
return v___x_1259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = lean_string_from_utf8_unchecked(v___y_1262_);
v___x_1264_ = l_String_quote(v___x_1263_);
v___x_1265_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(lean_object* v_x_1266_, lean_object* v_x_1267_){
_start:
{
if (lean_obj_tag(v_x_1266_) == 0)
{
lean_object* v___x_1268_; 
lean_dec(v_x_1267_);
v___x_1268_ = lean_box(0);
return v___x_1268_;
}
else
{
lean_object* v_tail_1269_; 
v_tail_1269_ = lean_ctor_get(v_x_1266_, 1);
if (lean_obj_tag(v_tail_1269_) == 0)
{
lean_object* v_head_1270_; lean_object* v___x_1271_; 
lean_dec(v_x_1267_);
v_head_1270_ = lean_ctor_get(v_x_1266_, 0);
lean_inc(v_head_1270_);
lean_dec_ref_known(v_x_1266_, 2);
v___x_1271_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1270_);
return v___x_1271_;
}
else
{
lean_object* v_head_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_inc(v_tail_1269_);
v_head_1272_ = lean_ctor_get(v_x_1266_, 0);
lean_inc(v_head_1272_);
lean_dec_ref_known(v_x_1266_, 2);
v___x_1273_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1272_);
v___x_1274_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(v_x_1267_, v___x_1273_, v_tail_1269_);
return v___x_1274_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0));
v___x_1280_ = lean_string_length(v___x_1279_);
return v___x_1280_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2);
v___x_1282_ = lean_nat_to_int(v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(lean_object* v_xs_1290_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1291_ = lean_array_get_size(v_xs_1290_);
v___x_1292_ = lean_unsigned_to_nat(0u);
v___x_1293_ = lean_nat_dec_eq(v___x_1291_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1294_ = lean_array_to_list(v_xs_1290_);
v___x_1295_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1296_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(v___x_1294_, v___x_1295_);
v___x_1297_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1298_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v___x_1296_);
v___x_1300_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1297_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
v___x_1303_ = l_Std_Format_fill(v___x_1302_);
return v___x_1303_;
}
else
{
lean_object* v___x_1304_; 
lean_dec_ref(v_xs_1290_);
v___x_1304_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___redArg(lean_object* v_x_1317_){
_start:
{
lean_object* v_segments_1318_; uint8_t v_absolute_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1351_; 
v_segments_1318_ = lean_ctor_get(v_x_1317_, 0);
v_absolute_1319_ = lean_ctor_get_uint8(v_x_1317_, sizeof(void*)*1);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_x_1317_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1321_ = v_x_1317_;
v_isShared_1322_ = v_isSharedCheck_1351_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_segments_1318_);
lean_dec(v_x_1317_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1351_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; lean_object* v___x_1330_; 
v___x_1323_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1324_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__3));
v___x_1325_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_1326_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(v_segments_1318_);
v___x_1327_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1325_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = 0;
if (v_isShared_1322_ == 0)
{
lean_ctor_set_tag(v___x_1321_, 6);
lean_ctor_set(v___x_1321_, 0, v___x_1327_);
v___x_1330_ = v___x_1321_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1327_);
v___x_1330_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_ctor_set_uint8(v___x_1330_, sizeof(void*)*1, v___x_1328_);
v___x_1331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1324_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = lean_box(1);
v___x_1335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1333_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__5));
v___x_1337_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1335_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
lean_ctor_set(v___x_1338_, 1, v___x_1323_);
v___x_1339_ = l_Bool_repr___redArg(v_absolute_1319_);
v___x_1340_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1325_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*1, v___x_1328_);
v___x_1342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1338_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1344_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
lean_ctor_set(v___x_1345_, 1, v___x_1342_);
v___x_1346_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1343_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*1, v___x_1328_);
return v___x_1349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr(lean_object* v_x_1352_, lean_object* v_prec_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Std_Http_URI_instReprPath_repr___redArg(v_x_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___boxed(lean_object* v_x_1355_, lean_object* v_prec_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Std_Http_URI_instReprPath_repr(v_x_1355_, v_prec_1356_);
lean_dec(v_prec_1356_);
return v_res_1357_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(lean_object* v_xs_1360_, lean_object* v_ys_1361_, lean_object* v_x_1362_){
_start:
{
lean_object* v_zero_1363_; uint8_t v_isZero_1364_; 
v_zero_1363_ = lean_unsigned_to_nat(0u);
v_isZero_1364_ = lean_nat_dec_eq(v_x_1362_, v_zero_1363_);
if (v_isZero_1364_ == 1)
{
lean_dec(v_x_1362_);
return v_isZero_1364_;
}
else
{
lean_object* v_one_1365_; lean_object* v_n_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_one_1365_ = lean_unsigned_to_nat(1u);
v_n_1366_ = lean_nat_sub(v_x_1362_, v_one_1365_);
lean_dec(v_x_1362_);
v___x_1367_ = lean_array_fget_borrowed(v_xs_1360_, v_n_1366_);
v___x_1368_ = lean_array_fget_borrowed(v_ys_1361_, v_n_1366_);
v___x_1369_ = lean_sarray_dec_eq(v___x_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_dec(v_n_1366_);
return v___x_1369_;
}
else
{
v_x_1362_ = v_n_1366_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg___boxed(lean_object* v_xs_1371_, lean_object* v_ys_1372_, lean_object* v_x_1373_){
_start:
{
uint8_t v_res_1374_; lean_object* v_r_1375_; 
v_res_1374_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1371_, v_ys_1372_, v_x_1373_);
lean_dec_ref(v_ys_1372_);
lean_dec_ref(v_xs_1371_);
v_r_1375_ = lean_box(v_res_1374_);
return v_r_1375_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqPath_beq(lean_object* v_x_1376_, lean_object* v_x_1377_){
_start:
{
lean_object* v_segments_1378_; uint8_t v_absolute_1379_; lean_object* v_segments_1380_; uint8_t v_absolute_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; 
v_segments_1378_ = lean_ctor_get(v_x_1376_, 0);
v_absolute_1379_ = lean_ctor_get_uint8(v_x_1376_, sizeof(void*)*1);
v_segments_1380_ = lean_ctor_get(v_x_1377_, 0);
v_absolute_1381_ = lean_ctor_get_uint8(v_x_1377_, sizeof(void*)*1);
v___x_1382_ = lean_array_get_size(v_segments_1378_);
v___x_1383_ = lean_array_get_size(v_segments_1380_);
v___x_1384_ = lean_nat_dec_eq(v___x_1382_, v___x_1383_);
if (v___x_1384_ == 0)
{
return v___x_1384_;
}
else
{
uint8_t v___x_1385_; 
v___x_1385_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_segments_1378_, v_segments_1380_, v___x_1382_);
if (v___x_1385_ == 0)
{
return v___x_1385_;
}
else
{
if (v_absolute_1381_ == 0)
{
if (v_absolute_1379_ == 0)
{
return v___x_1385_;
}
else
{
return v_absolute_1381_;
}
}
else
{
return v_absolute_1379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqPath_beq___boxed(lean_object* v_x_1386_, lean_object* v_x_1387_){
_start:
{
uint8_t v_res_1388_; lean_object* v_r_1389_; 
v_res_1388_ = l_Std_Http_URI_instBEqPath_beq(v_x_1386_, v_x_1387_);
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
v_r_1389_ = lean_box(v_res_1388_);
return v_r_1389_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(lean_object* v_xs_1390_, lean_object* v_ys_1391_, lean_object* v_hsz_1392_, lean_object* v_x_1393_, lean_object* v_x_1394_){
_start:
{
uint8_t v___x_1395_; 
v___x_1395_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1390_, v_ys_1391_, v_x_1393_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___boxed(lean_object* v_xs_1396_, lean_object* v_ys_1397_, lean_object* v_hsz_1398_, lean_object* v_x_1399_, lean_object* v_x_1400_){
_start:
{
uint8_t v_res_1401_; lean_object* v_r_1402_; 
v_res_1401_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(v_xs_1396_, v_ys_1397_, v_hsz_1398_, v_x_1399_, v_x_1400_);
lean_dec_ref(v_ys_1397_);
lean_dec_ref(v_xs_1396_);
v_r_1402_ = lean_box(v_res_1401_);
return v_r_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__0(lean_object* v_x_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_string_from_utf8_unchecked(v_x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__1(lean_object* v___f_1427_, lean_object* v_path_1428_){
_start:
{
lean_object* v_segments_1429_; uint8_t v_absolute_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; size_t v_sz_1433_; size_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_result_1437_; 
v_segments_1429_ = lean_ctor_get(v_path_1428_, 0);
lean_inc_ref(v_segments_1429_);
v_absolute_1430_ = lean_ctor_get_uint8(v_path_1428_, sizeof(void*)*1);
lean_dec_ref(v_path_1428_);
v___x_1431_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_1432_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_1433_ = lean_array_size(v_segments_1429_);
v___x_1434_ = ((size_t)0ULL);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1432_, v___f_1427_, v_sz_1433_, v___x_1434_, v_segments_1429_);
v___x_1436_ = lean_array_to_list(v___x_1435_);
v_result_1437_ = l_String_intercalate(v___x_1431_, v___x_1436_);
if (v_absolute_1430_ == 0)
{
return v_result_1437_;
}
else
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_string_append(v___x_1431_, v_result_1437_);
lean_dec_ref(v_result_1437_);
return v___x_1438_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Path_isEmpty(lean_object* v_p_1443_){
_start:
{
lean_object* v_segments_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v_segments_1444_ = lean_ctor_get(v_p_1443_, 0);
v___x_1445_ = lean_array_get_size(v_segments_1444_);
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = lean_nat_dec_eq(v___x_1445_, v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_isEmpty___boxed(lean_object* v_p_1448_){
_start:
{
uint8_t v_res_1449_; lean_object* v_r_1450_; 
v_res_1449_ = l_Std_Http_URI_Path_isEmpty(v_p_1448_);
lean_dec_ref(v_p_1448_);
v_r_1450_ = lean_box(v_res_1449_);
return v_r_1450_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Path_render_spec__0(lean_object* v_a_1451_, lean_object* v_i_1452_){
_start:
{
lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1453_ = lean_byte_array_size(v_a_1451_);
v___x_1454_ = lean_nat_dec_lt(v_i_1452_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; 
lean_dec(v_i_1452_);
v___x_1455_ = lean_box(0);
return v___x_1455_;
}
else
{
uint8_t v___x_1456_; uint8_t v___x_1457_; uint8_t v___x_1458_; 
v___x_1456_ = lean_byte_array_fget(v_a_1451_, v_i_1452_);
v___x_1457_ = 58;
v___x_1458_ = lean_uint8_dec_eq(v___x_1456_, v___x_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_unsigned_to_nat(1u);
v___x_1460_ = lean_nat_add(v_i_1452_, v___x_1459_);
lean_dec(v_i_1452_);
v_i_1452_ = v___x_1460_;
goto _start;
}
else
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1462_, 0, v_i_1452_);
return v___x_1462_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Path_render_spec__0___boxed(lean_object* v_a_1463_, lean_object* v_i_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Path_render_spec__0(v_a_1463_, v_i_1464_);
lean_dec_ref(v_a_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_render_spec__1(size_t v_sz_1466_, size_t v_i_1467_, lean_object* v_bs_1468_){
_start:
{
uint8_t v___x_1469_; 
v___x_1469_ = lean_usize_dec_lt(v_i_1467_, v_sz_1466_);
if (v___x_1469_ == 0)
{
return v_bs_1468_;
}
else
{
lean_object* v_v_1470_; lean_object* v___x_1471_; lean_object* v_bs_x27_1472_; lean_object* v___x_1473_; size_t v___x_1474_; size_t v___x_1475_; lean_object* v___x_1476_; 
v_v_1470_ = lean_array_uget(v_bs_1468_, v_i_1467_);
v___x_1471_ = lean_unsigned_to_nat(0u);
v_bs_x27_1472_ = lean_array_uset(v_bs_1468_, v_i_1467_, v___x_1471_);
v___x_1473_ = lean_string_from_utf8_unchecked(v_v_1470_);
v___x_1474_ = ((size_t)1ULL);
v___x_1475_ = lean_usize_add(v_i_1467_, v___x_1474_);
v___x_1476_ = lean_array_uset(v_bs_x27_1472_, v_i_1467_, v___x_1473_);
v_i_1467_ = v___x_1475_;
v_bs_1468_ = v___x_1476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_render_spec__1___boxed(lean_object* v_sz_1478_, lean_object* v_i_1479_, lean_object* v_bs_1480_){
_start:
{
size_t v_sz_boxed_1481_; size_t v_i_boxed_1482_; lean_object* v_res_1483_; 
v_sz_boxed_1481_ = lean_unbox_usize(v_sz_1478_);
lean_dec(v_sz_1478_);
v_i_boxed_1482_ = lean_unbox_usize(v_i_1479_);
lean_dec(v_i_1479_);
v_res_1483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_render_spec__1(v_sz_boxed_1481_, v_i_boxed_1482_, v_bs_1480_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_render(lean_object* v_p_1486_, uint8_t v_hasAuthority_1487_, uint8_t v_hasScheme_1488_){
_start:
{
lean_object* v___y_1490_; lean_object* v___y_1494_; uint8_t v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; uint8_t v___y_1498_; uint8_t v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v_segments_1520_; uint8_t v_absolute_1521_; lean_object* v___y_1523_; lean_object* v___x_1530_; size_t v_sz_1531_; size_t v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v_result_1535_; 
v_segments_1520_ = lean_ctor_get(v_p_1486_, 0);
lean_inc_ref_n(v_segments_1520_, 2);
v_absolute_1521_ = lean_ctor_get_uint8(v_p_1486_, sizeof(void*)*1);
lean_dec_ref(v_p_1486_);
v___x_1530_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v_sz_1531_ = lean_array_size(v_segments_1520_);
v___x_1532_ = ((size_t)0ULL);
v___x_1533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_render_spec__1(v_sz_1531_, v___x_1532_, v_segments_1520_);
v___x_1534_ = lean_array_to_list(v___x_1533_);
v_result_1535_ = l_String_intercalate(v___x_1530_, v___x_1534_);
if (v_absolute_1521_ == 0)
{
v___y_1523_ = v_result_1535_;
goto v___jp_1522_;
}
else
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_string_append(v___x_1530_, v_result_1535_);
lean_dec_ref(v_result_1535_);
v___y_1523_ = v___x_1536_;
goto v___jp_1522_;
}
v___jp_1489_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = ((lean_object*)(l_Std_Http_URI_Path_render___closed__0));
v___x_1492_ = lean_string_append(v___x_1491_, v___y_1490_);
lean_dec_ref(v___y_1490_);
return v___x_1492_;
}
v___jp_1493_:
{
if (v_hasAuthority_1487_ == 0)
{
if (v___y_1495_ == 0)
{
if (v___y_1498_ == 0)
{
if (v_hasScheme_1488_ == 0)
{
if (lean_obj_tag(v___y_1494_) == 0)
{
lean_dec(v___y_1496_);
return v___y_1497_;
}
else
{
lean_object* v_val_1499_; lean_object* v___x_1500_; 
v_val_1499_ = lean_ctor_get(v___y_1494_, 0);
lean_inc(v_val_1499_);
lean_dec_ref_known(v___y_1494_, 1);
v___x_1500_ = l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Path_render_spec__0(v_val_1499_, v___y_1496_);
lean_dec(v_val_1499_);
if (lean_obj_tag(v___x_1500_) == 0)
{
return v___y_1497_;
}
else
{
lean_dec_ref_known(v___x_1500_, 1);
v___y_1490_ = v___y_1497_;
goto v___jp_1489_;
}
}
}
else
{
lean_dec(v___y_1496_);
lean_dec(v___y_1494_);
return v___y_1497_;
}
}
else
{
lean_dec(v___y_1496_);
lean_dec(v___y_1494_);
v___y_1490_ = v___y_1497_;
goto v___jp_1489_;
}
}
else
{
lean_dec(v___y_1496_);
lean_dec(v___y_1494_);
if (v___y_1498_ == 0)
{
return v___y_1497_;
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = ((lean_object*)(l_Std_Http_URI_Path_render___closed__1));
v___x_1502_ = lean_string_append(v___x_1501_, v___y_1497_);
lean_dec_ref(v___y_1497_);
return v___x_1502_;
}
}
}
else
{
lean_dec(v___y_1494_);
if (v___y_1495_ == 0)
{
lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1503_ = lean_string_utf8_byte_size(v___y_1497_);
v___x_1504_ = lean_nat_dec_eq(v___x_1503_, v___y_1496_);
lean_dec(v___y_1496_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_1506_ = lean_string_append(v___x_1505_, v___y_1497_);
lean_dec_ref(v___y_1497_);
return v___x_1506_;
}
else
{
return v___y_1497_;
}
}
else
{
lean_dec(v___y_1496_);
return v___y_1497_;
}
}
}
v___jp_1507_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1513_ = lean_unsigned_to_nat(1u);
v___x_1514_ = lean_array_get_size(v___y_1511_);
lean_dec_ref(v___y_1511_);
v___x_1515_ = lean_nat_dec_lt(v___x_1513_, v___x_1514_);
if (v___x_1515_ == 0)
{
v___y_1494_ = v___y_1512_;
v___y_1495_ = v___y_1508_;
v___y_1496_ = v___y_1509_;
v___y_1497_ = v___y_1510_;
v___y_1498_ = v___x_1515_;
goto v___jp_1493_;
}
else
{
if (lean_obj_tag(v___y_1512_) == 0)
{
uint8_t v___x_1516_; 
v___x_1516_ = 0;
v___y_1494_ = v___y_1512_;
v___y_1495_ = v___y_1508_;
v___y_1496_ = v___y_1509_;
v___y_1497_ = v___y_1510_;
v___y_1498_ = v___x_1516_;
goto v___jp_1493_;
}
else
{
lean_object* v_val_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v_val_1517_ = lean_ctor_get(v___y_1512_, 0);
v___x_1518_ = lean_byte_array_size(v_val_1517_);
v___x_1519_ = lean_nat_dec_eq(v___x_1518_, v___y_1509_);
v___y_1494_ = v___y_1512_;
v___y_1495_ = v___y_1508_;
v___y_1496_ = v___y_1509_;
v___y_1497_ = v___y_1510_;
v___y_1498_ = v___x_1519_;
goto v___jp_1493_;
}
}
}
v___jp_1522_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = lean_array_get_size(v_segments_1520_);
v___x_1526_ = lean_nat_dec_lt(v___x_1524_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_box(0);
v___y_1508_ = v_absolute_1521_;
v___y_1509_ = v___x_1524_;
v___y_1510_ = v___y_1523_;
v___y_1511_ = v_segments_1520_;
v___y_1512_ = v___x_1527_;
goto v___jp_1507_;
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = lean_array_fget_borrowed(v_segments_1520_, v___x_1524_);
lean_inc(v___x_1528_);
v___x_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
v___y_1508_ = v_absolute_1521_;
v___y_1509_ = v___x_1524_;
v___y_1510_ = v___y_1523_;
v___y_1511_ = v_segments_1520_;
v___y_1512_ = v___x_1529_;
goto v___jp_1507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_render___boxed(lean_object* v_p_1537_, lean_object* v_hasAuthority_1538_, lean_object* v_hasScheme_1539_){
_start:
{
uint8_t v_hasAuthority_boxed_1540_; uint8_t v_hasScheme_boxed_1541_; lean_object* v_res_1542_; 
v_hasAuthority_boxed_1540_ = lean_unbox(v_hasAuthority_1538_);
v_hasScheme_boxed_1541_ = lean_unbox(v_hasScheme_1539_);
v_res_1542_ = l_Std_Http_URI_Path_render(v_p_1537_, v_hasAuthority_boxed_1540_, v_hasScheme_boxed_1541_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parent(lean_object* v_p_1543_){
_start:
{
lean_object* v_segments_1544_; uint8_t v_absolute_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_segments_1544_ = lean_ctor_get(v_p_1543_, 0);
v_absolute_1545_ = lean_ctor_get_uint8(v_p_1543_, sizeof(void*)*1);
v___x_1546_ = lean_array_get_size(v_segments_1544_);
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = lean_nat_dec_eq(v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1556_; 
lean_inc_ref(v_segments_1544_);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_p_1543_);
if (v_isSharedCheck_1556_ == 0)
{
lean_object* v_unused_1557_; 
v_unused_1557_ = lean_ctor_get(v_p_1543_, 0);
lean_dec(v_unused_1557_);
v___x_1550_ = v_p_1543_;
v_isShared_1551_ = v_isSharedCheck_1556_;
goto v_resetjp_1549_;
}
else
{
lean_dec(v_p_1543_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1556_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1552_ = lean_array_pop(v_segments_1544_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1552_);
v___x_1554_ = v___x_1550_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
lean_ctor_set_uint8(v_reuseFailAlloc_1555_, sizeof(void*)*1, v_absolute_1545_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
else
{
return v_p_1543_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join(lean_object* v_p1_1558_, lean_object* v_p2_1559_){
_start:
{
uint8_t v_absolute_1560_; 
v_absolute_1560_ = lean_ctor_get_uint8(v_p2_1559_, sizeof(void*)*1);
if (v_absolute_1560_ == 0)
{
lean_object* v_segments_1561_; lean_object* v_segments_1562_; uint8_t v_absolute_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1571_; 
v_segments_1561_ = lean_ctor_get(v_p2_1559_, 0);
v_segments_1562_ = lean_ctor_get(v_p1_1558_, 0);
v_absolute_1563_ = lean_ctor_get_uint8(v_p1_1558_, sizeof(void*)*1);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_p1_1558_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1565_ = v_p1_1558_;
v_isShared_1566_ = v_isSharedCheck_1571_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_segments_1562_);
lean_dec(v_p1_1558_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1571_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1567_ = l_Array_append___redArg(v_segments_1562_, v_segments_1561_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1567_);
v___x_1569_ = v___x_1565_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
lean_ctor_set_uint8(v_reuseFailAlloc_1570_, sizeof(void*)*1, v_absolute_1563_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
else
{
lean_dec_ref(v_p1_1558_);
lean_inc_ref(v_p2_1559_);
return v_p2_1559_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join___boxed(lean_object* v_p1_1572_, lean_object* v_p2_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Std_Http_URI_Path_join(v_p1_1572_, v_p2_1573_);
lean_dec_ref(v_p2_1573_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append(lean_object* v_p_1575_, lean_object* v_segment_1576_){
_start:
{
lean_object* v_segments_1577_; uint8_t v_absolute_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1587_; 
v_segments_1577_ = lean_ctor_get(v_p_1575_, 0);
v_absolute_1578_ = lean_ctor_get_uint8(v_p_1575_, sizeof(void*)*1);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_p_1575_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1580_ = v_p_1575_;
v_isShared_1581_ = v_isSharedCheck_1587_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_segments_1577_);
lean_dec(v_p_1575_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1587_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1582_ = l_Std_Http_URI_EncodedSegment_encode(v_segment_1576_);
v___x_1583_ = lean_array_push(v_segments_1577_, v___x_1582_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1583_);
v___x_1585_ = v___x_1580_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
lean_ctor_set_uint8(v_reuseFailAlloc_1586_, sizeof(void*)*1, v_absolute_1578_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_appendEncoded(lean_object* v_p_1588_, lean_object* v_segment_1589_){
_start:
{
lean_object* v_segments_1590_; uint8_t v_absolute_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1599_; 
v_segments_1590_ = lean_ctor_get(v_p_1588_, 0);
v_absolute_1591_ = lean_ctor_get_uint8(v_p_1588_, sizeof(void*)*1);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_p_1588_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1593_ = v_p_1588_;
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_segments_1590_);
lean_dec(v_p_1588_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1595_ = lean_array_push(v_segments_1590_, v_segment_1589_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1595_);
v___x_1597_ = v___x_1593_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, sizeof(void*)*1, v_absolute_1591_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___x_1601_ = l_Std_Http_URI_EncodedSegment_encode(v___x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0(lean_object* v_tail_1602_, lean_object* v_output_1603_){
_start:
{
uint8_t v___x_1604_; 
v___x_1604_ = l_List_isEmpty___redArg(v_tail_1602_);
if (v___x_1604_ == 0)
{
return v_output_1603_;
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_obj_once(&l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0___closed__0, &l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0___closed__0);
v___x_1606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set(v___x_1606_, 1, v_output_1603_);
return v___x_1606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0___boxed(lean_object* v_tail_1607_, lean_object* v_output_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0(v_tail_1607_, v_output_1608_);
lean_dec(v_tail_1607_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(lean_object* v_input_1611_, lean_object* v_output_1612_){
_start:
{
if (lean_obj_tag(v_input_1611_) == 0)
{
lean_object* v___x_1613_; 
v___x_1613_ = l_List_reverse___redArg(v_output_1612_);
return v___x_1613_;
}
else
{
lean_object* v_head_1614_; lean_object* v_tail_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1635_; 
v_head_1614_ = lean_ctor_get(v_input_1611_, 0);
v_tail_1615_ = lean_ctor_get(v_input_1611_, 1);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_input_1611_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1617_ = v_input_1611_;
v_isShared_1618_ = v_isSharedCheck_1635_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_tail_1615_);
lean_inc(v_head_1614_);
lean_dec(v_input_1611_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1635_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
lean_inc(v_head_1614_);
v___x_1619_ = lean_string_from_utf8_unchecked(v_head_1614_);
v___x_1620_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3___redArg___closed__0));
v___x_1621_ = lean_string_dec_eq(v___x_1619_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = ((lean_object*)(l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0));
v___x_1623_ = lean_string_dec_eq(v___x_1619_, v___x_1622_);
lean_dec_ref(v___x_1619_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1625_; 
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 1, v_output_1612_);
v___x_1625_ = v___x_1617_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_head_1614_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_output_1612_);
v___x_1625_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
v_input_1611_ = v_tail_1615_;
v_output_1612_ = v___x_1625_;
goto _start;
}
}
else
{
lean_del_object(v___x_1617_);
lean_dec(v_head_1614_);
if (lean_obj_tag(v_output_1612_) == 0)
{
lean_object* v___x_1628_; 
v___x_1628_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0(v_tail_1615_, v_output_1612_);
v_input_1611_ = v_tail_1615_;
v_output_1612_ = v___x_1628_;
goto _start;
}
else
{
lean_object* v_tail_1630_; lean_object* v___x_1631_; 
v_tail_1630_ = lean_ctor_get(v_output_1612_, 1);
lean_inc(v_tail_1630_);
lean_dec_ref_known(v_output_1612_, 2);
v___x_1631_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0(v_tail_1615_, v_tail_1630_);
v_input_1611_ = v_tail_1615_;
v_output_1612_ = v___x_1631_;
goto _start;
}
}
}
else
{
lean_object* v___x_1633_; 
lean_dec_ref(v___x_1619_);
lean_del_object(v___x_1617_);
lean_dec(v_head_1614_);
v___x_1633_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0(v_tail_1615_, v_output_1612_);
v_input_1611_ = v_tail_1615_;
v_output_1612_ = v___x_1633_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_normalize(lean_object* v_p_1636_){
_start:
{
lean_object* v_segments_1637_; uint8_t v_absolute_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1649_; 
v_segments_1637_ = lean_ctor_get(v_p_1636_, 0);
v_absolute_1638_ = lean_ctor_get_uint8(v_p_1636_, sizeof(void*)*1);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_p_1636_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1640_ = v_p_1636_;
v_isShared_1641_ = v_isSharedCheck_1649_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_segments_1637_);
lean_dec(v_p_1636_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1649_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1642_ = lean_array_to_list(v_segments_1637_);
v___x_1643_ = lean_box(0);
v___x_1644_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(v___x_1642_, v___x_1643_);
v___x_1645_ = lean_array_mk(v___x_1644_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1645_);
v___x_1647_ = v___x_1640_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1645_);
lean_ctor_set_uint8(v_reuseFailAlloc_1648_, sizeof(void*)*1, v_absolute_1638_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(size_t v_sz_1650_, size_t v_i_1651_, lean_object* v_bs_1652_){
_start:
{
uint8_t v___x_1653_; 
v___x_1653_ = lean_usize_dec_lt(v_i_1651_, v_sz_1650_);
if (v___x_1653_ == 0)
{
return v_bs_1652_;
}
else
{
lean_object* v_v_1654_; lean_object* v___x_1655_; lean_object* v_bs_x27_1656_; lean_object* v___y_1658_; lean_object* v___x_1663_; 
v_v_1654_ = lean_array_uget(v_bs_1652_, v_i_1651_);
v___x_1655_ = lean_unsigned_to_nat(0u);
v_bs_x27_1656_ = lean_array_uset(v_bs_1652_, v_i_1651_, v___x_1655_);
v___x_1663_ = l_Std_Http_URI_EncodedSegment_decode(v_v_1654_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_string_from_utf8_unchecked(v_v_1654_);
v___y_1658_ = v___x_1664_;
goto v___jp_1657_;
}
else
{
lean_object* v_val_1665_; 
lean_dec(v_v_1654_);
v_val_1665_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_val_1665_);
lean_dec_ref_known(v___x_1663_, 1);
v___y_1658_ = v_val_1665_;
goto v___jp_1657_;
}
v___jp_1657_:
{
size_t v___x_1659_; size_t v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = ((size_t)1ULL);
v___x_1660_ = lean_usize_add(v_i_1651_, v___x_1659_);
v___x_1661_ = lean_array_uset(v_bs_x27_1656_, v_i_1651_, v___y_1658_);
v_i_1651_ = v___x_1660_;
v_bs_1652_ = v___x_1661_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0___boxed(lean_object* v_sz_1666_, lean_object* v_i_1667_, lean_object* v_bs_1668_){
_start:
{
size_t v_sz_boxed_1669_; size_t v_i_boxed_1670_; lean_object* v_res_1671_; 
v_sz_boxed_1669_ = lean_unbox_usize(v_sz_1666_);
lean_dec(v_sz_1666_);
v_i_boxed_1670_ = lean_unbox_usize(v_i_1667_);
lean_dec(v_i_1667_);
v_res_1671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_boxed_1669_, v_i_boxed_1670_, v_bs_1668_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_toDecodedSegments(lean_object* v_p_1672_){
_start:
{
lean_object* v_segments_1673_; size_t v_sz_1674_; size_t v___x_1675_; lean_object* v___x_1676_; 
v_segments_1673_ = lean_ctor_get(v_p_1672_, 0);
lean_inc_ref(v_segments_1673_);
lean_dec_ref(v_p_1672_);
v_sz_1674_ = lean_array_size(v_segments_1673_);
v___x_1675_ = ((size_t)0ULL);
v___x_1676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_1674_, v___x_1675_, v_segments_1673_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___redArg(lean_object* v_xs_1685_){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1687_ = l_Array_repr___redArg(v___x_1686_, v_xs_1685_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1(lean_object* v_xs_1688_, lean_object* v_x_1689_){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1691_ = l_Array_repr___redArg(v___x_1690_, v_xs_1688_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___boxed(lean_object* v_xs_1692_, lean_object* v_x_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Std_Http_URI_instReprQuery___aux__1(v_xs_1692_, v_x_1693_);
lean_dec(v_x_1693_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_1695_, lean_object* v_x_1696_, lean_object* v_x_1697_){
_start:
{
if (lean_obj_tag(v_x_1697_) == 0)
{
lean_dec(v_x_1695_);
return v_x_1696_;
}
else
{
lean_object* v_head_1698_; lean_object* v_tail_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1708_; 
v_head_1698_ = lean_ctor_get(v_x_1697_, 0);
v_tail_1699_ = lean_ctor_get(v_x_1697_, 1);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_x_1697_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1701_ = v_x_1697_;
v_isShared_1702_ = v_isSharedCheck_1708_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_tail_1699_);
lean_inc(v_head_1698_);
lean_dec(v_x_1697_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1708_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
lean_inc(v_x_1695_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set_tag(v___x_1701_, 5);
lean_ctor_set(v___x_1701_, 1, v_x_1695_);
lean_ctor_set(v___x_1701_, 0, v_x_1696_);
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_x_1696_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_x_1695_);
v___x_1704_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
lean_ctor_set(v___x_1705_, 1, v_head_1698_);
v_x_1696_ = v___x_1705_;
v_x_1697_ = v_tail_1699_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(lean_object* v_x_1709_, lean_object* v_x_1710_){
_start:
{
if (lean_obj_tag(v_x_1709_) == 0)
{
lean_object* v___x_1711_; 
lean_dec(v_x_1710_);
v___x_1711_ = lean_box(0);
return v___x_1711_;
}
else
{
lean_object* v_tail_1712_; 
v_tail_1712_ = lean_ctor_get(v_x_1709_, 1);
if (lean_obj_tag(v_tail_1712_) == 0)
{
lean_object* v_head_1713_; 
lean_dec(v_x_1710_);
v_head_1713_ = lean_ctor_get(v_x_1709_, 0);
lean_inc(v_head_1713_);
lean_dec_ref_known(v_x_1709_, 2);
return v_head_1713_;
}
else
{
lean_object* v_head_1714_; lean_object* v___x_1715_; 
lean_inc(v_tail_1712_);
v_head_1714_ = lean_ctor_get(v_x_1709_, 0);
lean_inc(v_head_1714_);
lean_dec_ref_known(v_x_1709_, 2);
v___x_1715_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(v_x_1710_, v_head_1714_, v_tail_1712_);
return v___x_1715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(lean_object* v_x_1716_, lean_object* v_x_1717_){
_start:
{
if (lean_obj_tag(v_x_1716_) == 0)
{
lean_object* v___x_1718_; 
v___x_1718_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1718_;
}
else
{
lean_object* v_val_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1731_; 
v_val_1719_ = lean_ctor_get(v_x_1716_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_x_1716_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1721_ = v_x_1716_;
v_isShared_1722_ = v_isSharedCheck_1731_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_val_1719_);
lean_dec(v_x_1716_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1731_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1723_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1724_ = lean_string_from_utf8_unchecked(v_val_1719_);
v___x_1725_ = l_String_quote(v___x_1724_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set_tag(v___x_1721_, 3);
lean_ctor_set(v___x_1721_, 0, v___x_1725_);
v___x_1727_ = v___x_1721_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1723_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = l_Repr_addAppParen(v___x_1728_, v_x_1717_);
return v___x_1729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1732_, lean_object* v_x_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_x_1732_, v_x_1733_);
lean_dec(v_x_1733_);
return v_res_1734_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0));
v___x_1738_ = lean_string_length(v___x_1737_);
return v___x_1738_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2);
v___x_1740_ = lean_nat_to_int(v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(lean_object* v_x_1745_){
_start:
{
lean_object* v_fst_1746_; lean_object* v_snd_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1772_; 
v_fst_1746_ = lean_ctor_get(v_x_1745_, 0);
v_snd_1747_ = lean_ctor_get(v_x_1745_, 1);
v_isSharedCheck_1772_ = !lean_is_exclusive(v_x_1745_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1749_ = v_x_1745_;
v_isShared_1750_ = v_isSharedCheck_1772_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_snd_1747_);
lean_inc(v_fst_1746_);
lean_dec(v_x_1745_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1772_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1751_ = lean_string_from_utf8_unchecked(v_fst_1746_);
v___x_1752_ = l_String_quote(v___x_1751_);
v___x_1753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
v___x_1754_ = lean_box(0);
if (v_isShared_1750_ == 0)
{
lean_ctor_set_tag(v___x_1749_, 1);
lean_ctor_set(v___x_1749_, 1, v___x_1754_);
lean_ctor_set(v___x_1749_, 0, v___x_1753_);
v___x_1756_ = v___x_1749_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; lean_object* v___x_1770_; 
v___x_1757_ = lean_unsigned_to_nat(0u);
v___x_1758_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_snd_1747_, v___x_1757_);
v___x_1759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v___x_1756_);
v___x_1760_ = l_List_reverse___redArg(v___x_1759_);
v___x_1761_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1762_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(v___x_1760_, v___x_1761_);
v___x_1763_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3);
v___x_1764_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4));
v___x_1765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
lean_ctor_set(v___x_1765_, 1, v___x_1762_);
v___x_1766_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5));
v___x_1767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1763_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = 0;
v___x_1770_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set_uint8(v___x_1770_, sizeof(void*)*1, v___x_1769_);
return v___x_1770_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(lean_object* v_x_1773_, lean_object* v_x_1774_, lean_object* v_x_1775_){
_start:
{
if (lean_obj_tag(v_x_1775_) == 0)
{
lean_dec(v_x_1773_);
return v_x_1774_;
}
else
{
lean_object* v_head_1776_; lean_object* v_tail_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1787_; 
v_head_1776_ = lean_ctor_get(v_x_1775_, 0);
v_tail_1777_ = lean_ctor_get(v_x_1775_, 1);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_x_1775_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1779_ = v_x_1775_;
v_isShared_1780_ = v_isSharedCheck_1787_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_tail_1777_);
lean_inc(v_head_1776_);
lean_dec(v_x_1775_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1787_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
lean_inc(v_x_1773_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set_tag(v___x_1779_, 5);
lean_ctor_set(v___x_1779_, 1, v_x_1773_);
lean_ctor_set(v___x_1779_, 0, v_x_1774_);
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_x_1774_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_x_1773_);
v___x_1782_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1776_);
v___x_1784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v_x_1774_ = v___x_1784_;
v_x_1775_ = v_tail_1777_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(lean_object* v_x_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_){
_start:
{
if (lean_obj_tag(v_x_1790_) == 0)
{
lean_dec(v_x_1788_);
return v_x_1789_;
}
else
{
lean_object* v_head_1791_; lean_object* v_tail_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1802_; 
v_head_1791_ = lean_ctor_get(v_x_1790_, 0);
v_tail_1792_ = lean_ctor_get(v_x_1790_, 1);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_x_1790_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1794_ = v_x_1790_;
v_isShared_1795_ = v_isSharedCheck_1802_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_tail_1792_);
lean_inc(v_head_1791_);
lean_dec(v_x_1790_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1802_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
lean_inc(v_x_1788_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set_tag(v___x_1794_, 5);
lean_ctor_set(v___x_1794_, 1, v_x_1788_);
lean_ctor_set(v___x_1794_, 0, v_x_1789_);
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_x_1789_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_x_1788_);
v___x_1797_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1791_);
v___x_1799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(v_x_1788_, v___x_1799_, v_tail_1792_);
return v___x_1800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(lean_object* v_x_1803_, lean_object* v_x_1804_){
_start:
{
if (lean_obj_tag(v_x_1803_) == 0)
{
lean_object* v___x_1805_; 
lean_dec(v_x_1804_);
v___x_1805_ = lean_box(0);
return v___x_1805_;
}
else
{
lean_object* v_tail_1806_; 
v_tail_1806_ = lean_ctor_get(v_x_1803_, 1);
if (lean_obj_tag(v_tail_1806_) == 0)
{
lean_object* v_head_1807_; lean_object* v___x_1808_; 
lean_dec(v_x_1804_);
v_head_1807_ = lean_ctor_get(v_x_1803_, 0);
lean_inc(v_head_1807_);
lean_dec_ref_known(v_x_1803_, 2);
v___x_1808_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1807_);
return v___x_1808_;
}
else
{
lean_object* v_head_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_inc(v_tail_1806_);
v_head_1809_ = lean_ctor_get(v_x_1803_, 0);
lean_inc(v_head_1809_);
lean_dec_ref_known(v_x_1803_, 2);
v___x_1810_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1809_);
v___x_1811_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(v_x_1804_, v___x_1810_, v_tail_1806_);
return v___x_1811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(lean_object* v_xs_1812_){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1813_ = lean_array_get_size(v_xs_1812_);
v___x_1814_ = lean_unsigned_to_nat(0u);
v___x_1815_ = lean_nat_dec_eq(v___x_1813_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1816_ = lean_array_to_list(v_xs_1812_);
v___x_1817_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1818_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(v___x_1816_, v___x_1817_);
v___x_1819_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1820_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
lean_ctor_set(v___x_1821_, 1, v___x_1818_);
v___x_1822_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1821_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1819_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = l_Std_Format_fill(v___x_1824_);
return v___x_1825_;
}
else
{
lean_object* v___x_1826_; 
lean_dec_ref(v_xs_1812_);
v___x_1826_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1826_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0(lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v___y_1827_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0___boxed(lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Std_Http_URI_instReprQuery___lam__0(v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_x_1835_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___boxed(lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(v_x_1838_, v_x_1839_);
lean_dec(v_x_1839_);
return v_res_1840_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1___lam__0(lean_object* v___f_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_){
_start:
{
lean_object* v_fst_1848_; lean_object* v_snd_1849_; lean_object* v_fst_1850_; lean_object* v_snd_1851_; uint8_t v___x_1852_; 
v_fst_1848_ = lean_ctor_get(v_x_1846_, 0);
lean_inc(v_fst_1848_);
v_snd_1849_ = lean_ctor_get(v_x_1846_, 1);
lean_inc(v_snd_1849_);
lean_dec_ref(v_x_1846_);
v_fst_1850_ = lean_ctor_get(v_x_1847_, 0);
lean_inc(v_fst_1850_);
v_snd_1851_ = lean_ctor_get(v_x_1847_, 1);
lean_inc(v_snd_1851_);
lean_dec_ref(v_x_1847_);
v___x_1852_ = lean_sarray_dec_eq(v_fst_1848_, v_fst_1850_);
lean_dec(v_fst_1850_);
lean_dec(v_fst_1848_);
if (v___x_1852_ == 0)
{
lean_dec(v_snd_1851_);
lean_dec(v_snd_1849_);
lean_dec_ref(v___f_1845_);
return v___x_1852_;
}
else
{
uint8_t v___x_1853_; 
v___x_1853_ = l_instBEqOption_beq___redArg(v___f_1845_, v_snd_1849_, v_snd_1851_);
return v___x_1853_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___lam__0___boxed(lean_object* v___f_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_){
_start:
{
uint8_t v_res_1857_; lean_object* v_r_1858_; 
v_res_1857_ = l_Std_Http_URI_instBEqQuery___aux__1___lam__0(v___f_1854_, v_x_1855_, v_x_1856_);
v_r_1858_ = lean_box(v_res_1857_);
return v_r_1858_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1(lean_object* v_xs_1862_, lean_object* v_ys_1863_){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1864_ = lean_array_get_size(v_xs_1862_);
v___x_1865_ = lean_array_get_size(v_ys_1863_);
v___x_1866_ = lean_nat_dec_eq(v___x_1864_, v___x_1865_);
if (v___x_1866_ == 0)
{
return v___x_1866_;
}
else
{
lean_object* v___f_1867_; uint8_t v___x_1868_; 
v___f_1867_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__1));
v___x_1868_ = l_Array_isEqvAux___redArg(v_xs_1862_, v_ys_1863_, v___f_1867_, v___x_1864_);
return v___x_1868_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___boxed(lean_object* v_xs_1869_, lean_object* v_ys_1870_){
_start:
{
uint8_t v_res_1871_; lean_object* v_r_1872_; 
v_res_1871_ = l_Std_Http_URI_instBEqQuery___aux__1(v_xs_1869_, v_ys_1870_);
lean_dec_ref(v_ys_1870_);
lean_dec_ref(v_xs_1869_);
v_r_1872_ = lean_box(v_res_1871_);
return v_r_1872_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(lean_object* v_x_1873_, lean_object* v_x_1874_){
_start:
{
if (lean_obj_tag(v_x_1873_) == 0)
{
if (lean_obj_tag(v_x_1874_) == 0)
{
uint8_t v___x_1875_; 
v___x_1875_ = 1;
return v___x_1875_;
}
else
{
uint8_t v___x_1876_; 
v___x_1876_ = 0;
return v___x_1876_;
}
}
else
{
if (lean_obj_tag(v_x_1874_) == 0)
{
uint8_t v___x_1877_; 
v___x_1877_ = 0;
return v___x_1877_;
}
else
{
lean_object* v_val_1878_; lean_object* v_val_1879_; uint8_t v___x_1880_; 
v_val_1878_ = lean_ctor_get(v_x_1873_, 0);
v_val_1879_ = lean_ctor_get(v_x_1874_, 0);
v___x_1880_ = lean_sarray_dec_eq(v_val_1878_, v_val_1879_);
return v___x_1880_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0___boxed(lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
uint8_t v_res_1883_; lean_object* v_r_1884_; 
v_res_1883_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_x_1881_, v_x_1882_);
lean_dec(v_x_1882_);
lean_dec(v_x_1881_);
v_r_1884_ = lean_box(v_res_1883_);
return v_r_1884_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(lean_object* v_xs_1885_, lean_object* v_ys_1886_, lean_object* v_x_1887_){
_start:
{
lean_object* v_zero_1888_; uint8_t v_isZero_1889_; 
v_zero_1888_ = lean_unsigned_to_nat(0u);
v_isZero_1889_ = lean_nat_dec_eq(v_x_1887_, v_zero_1888_);
if (v_isZero_1889_ == 1)
{
lean_dec(v_x_1887_);
return v_isZero_1889_;
}
else
{
lean_object* v_one_1890_; lean_object* v_n_1891_; lean_object* v___x_1892_; lean_object* v_fst_1893_; lean_object* v_snd_1894_; lean_object* v___x_1895_; lean_object* v_fst_1896_; lean_object* v_snd_1897_; uint8_t v___x_1898_; 
v_one_1890_ = lean_unsigned_to_nat(1u);
v_n_1891_ = lean_nat_sub(v_x_1887_, v_one_1890_);
lean_dec(v_x_1887_);
v___x_1892_ = lean_array_fget_borrowed(v_xs_1885_, v_n_1891_);
v_fst_1893_ = lean_ctor_get(v___x_1892_, 0);
v_snd_1894_ = lean_ctor_get(v___x_1892_, 1);
v___x_1895_ = lean_array_fget_borrowed(v_ys_1886_, v_n_1891_);
v_fst_1896_ = lean_ctor_get(v___x_1895_, 0);
v_snd_1897_ = lean_ctor_get(v___x_1895_, 1);
v___x_1898_ = lean_sarray_dec_eq(v_fst_1893_, v_fst_1896_);
if (v___x_1898_ == 0)
{
lean_dec(v_n_1891_);
return v___x_1898_;
}
else
{
uint8_t v___x_1899_; 
v___x_1899_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_snd_1894_, v_snd_1897_);
if (v___x_1899_ == 0)
{
lean_dec(v_n_1891_);
return v___x_1899_;
}
else
{
v_x_1887_ = v_n_1891_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg___boxed(lean_object* v_xs_1901_, lean_object* v_ys_1902_, lean_object* v_x_1903_){
_start:
{
uint8_t v_res_1904_; lean_object* v_r_1905_; 
v_res_1904_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1901_, v_ys_1902_, v_x_1903_);
lean_dec_ref(v_ys_1902_);
lean_dec_ref(v_xs_1901_);
v_r_1905_ = lean_box(v_res_1904_);
return v_r_1905_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___lam__0(lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1908_ = lean_array_get_size(v___y_1906_);
v___x_1909_ = lean_array_get_size(v___y_1907_);
v___x_1910_ = lean_nat_dec_eq(v___x_1908_, v___x_1909_);
if (v___x_1910_ == 0)
{
return v___x_1910_;
}
else
{
uint8_t v___x_1911_; 
v___x_1911_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v___y_1906_, v___y_1907_, v___x_1908_);
return v___x_1911_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___lam__0___boxed(lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
uint8_t v_res_1914_; lean_object* v_r_1915_; 
v_res_1914_ = l_Std_Http_URI_instBEqQuery___lam__0(v___y_1912_, v___y_1913_);
lean_dec_ref(v___y_1913_);
lean_dec_ref(v___y_1912_);
v_r_1915_ = lean_box(v_res_1914_);
return v_r_1915_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(lean_object* v_xs_1918_, lean_object* v_ys_1919_, lean_object* v_hsz_1920_, lean_object* v_x_1921_, lean_object* v_x_1922_){
_start:
{
uint8_t v___x_1923_; 
v___x_1923_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1918_, v_ys_1919_, v_x_1921_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___boxed(lean_object* v_xs_1924_, lean_object* v_ys_1925_, lean_object* v_hsz_1926_, lean_object* v_x_1927_, lean_object* v_x_1928_){
_start:
{
uint8_t v_res_1929_; lean_object* v_r_1930_; 
v_res_1929_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(v_xs_1924_, v_ys_1925_, v_hsz_1926_, v_x_1927_, v_x_1928_);
lean_dec_ref(v_ys_1925_);
lean_dec_ref(v_xs_1924_);
v_r_1930_ = lean_box(v_res_1929_);
return v_r_1930_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___redArg(lean_object* v_a_1931_, lean_object* v_x_1932_){
_start:
{
if (lean_obj_tag(v_x_1932_) == 0)
{
uint8_t v___x_1933_; 
v___x_1933_ = 0;
return v___x_1933_;
}
else
{
lean_object* v_key_1934_; lean_object* v_tail_1935_; uint8_t v___x_1936_; 
v_key_1934_ = lean_ctor_get(v_x_1932_, 0);
v_tail_1935_ = lean_ctor_get(v_x_1932_, 2);
v___x_1936_ = lean_sarray_dec_eq(v_key_1934_, v_a_1931_);
if (v___x_1936_ == 0)
{
v_x_1932_ = v_tail_1935_;
goto _start;
}
else
{
return v___x_1936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___redArg___boxed(lean_object* v_a_1938_, lean_object* v_x_1939_){
_start:
{
uint8_t v_res_1940_; lean_object* v_r_1941_; 
v_res_1940_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___redArg(v_a_1938_, v_x_1939_);
lean_dec(v_x_1939_);
lean_dec_ref(v_a_1938_);
v_r_1941_ = lean_box(v_res_1940_);
return v_r_1941_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0___redArg(lean_object* v_m_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v_buckets_1944_; lean_object* v___x_1945_; uint64_t v___x_1946_; uint64_t v___x_1947_; uint64_t v___x_1948_; uint64_t v_fold_1949_; uint64_t v___x_1950_; uint64_t v___x_1951_; uint64_t v___x_1952_; size_t v___x_1953_; size_t v___x_1954_; size_t v___x_1955_; size_t v___x_1956_; size_t v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v_buckets_1944_ = lean_ctor_get(v_m_1942_, 1);
v___x_1945_ = lean_array_get_size(v_buckets_1944_);
v___x_1946_ = lean_byte_array_hash(v_a_1943_);
v___x_1947_ = 32ULL;
v___x_1948_ = lean_uint64_shift_right(v___x_1946_, v___x_1947_);
v_fold_1949_ = lean_uint64_xor(v___x_1946_, v___x_1948_);
v___x_1950_ = 16ULL;
v___x_1951_ = lean_uint64_shift_right(v_fold_1949_, v___x_1950_);
v___x_1952_ = lean_uint64_xor(v_fold_1949_, v___x_1951_);
v___x_1953_ = lean_uint64_to_usize(v___x_1952_);
v___x_1954_ = lean_usize_of_nat(v___x_1945_);
v___x_1955_ = ((size_t)1ULL);
v___x_1956_ = lean_usize_sub(v___x_1954_, v___x_1955_);
v___x_1957_ = lean_usize_land(v___x_1953_, v___x_1956_);
v___x_1958_ = lean_array_uget_borrowed(v_buckets_1944_, v___x_1957_);
v___x_1959_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___redArg(v_a_1943_, v___x_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0___redArg___boxed(lean_object* v_m_1960_, lean_object* v_a_1961_){
_start:
{
uint8_t v_res_1962_; lean_object* v_r_1963_; 
v_res_1962_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0___redArg(v_m_1960_, v_a_1961_);
lean_dec_ref(v_a_1961_);
lean_dec_ref(v_m_1960_);
v_r_1963_ = lean_box(v_res_1962_);
return v_r_1963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_1964_, lean_object* v_x_1965_){
_start:
{
if (lean_obj_tag(v_x_1965_) == 0)
{
return v_x_1964_;
}
else
{
lean_object* v_key_1966_; lean_object* v_value_1967_; lean_object* v_tail_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1991_; 
v_key_1966_ = lean_ctor_get(v_x_1965_, 0);
v_value_1967_ = lean_ctor_get(v_x_1965_, 1);
v_tail_1968_ = lean_ctor_get(v_x_1965_, 2);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_x_1965_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1970_ = v_x_1965_;
v_isShared_1971_ = v_isSharedCheck_1991_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_tail_1968_);
lean_inc(v_value_1967_);
lean_inc(v_key_1966_);
lean_dec(v_x_1965_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1991_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; uint64_t v___x_1973_; uint64_t v___x_1974_; uint64_t v___x_1975_; uint64_t v_fold_1976_; uint64_t v___x_1977_; uint64_t v___x_1978_; uint64_t v___x_1979_; size_t v___x_1980_; size_t v___x_1981_; size_t v___x_1982_; size_t v___x_1983_; size_t v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1972_ = lean_array_get_size(v_x_1964_);
v___x_1973_ = lean_byte_array_hash(v_key_1966_);
v___x_1974_ = 32ULL;
v___x_1975_ = lean_uint64_shift_right(v___x_1973_, v___x_1974_);
v_fold_1976_ = lean_uint64_xor(v___x_1973_, v___x_1975_);
v___x_1977_ = 16ULL;
v___x_1978_ = lean_uint64_shift_right(v_fold_1976_, v___x_1977_);
v___x_1979_ = lean_uint64_xor(v_fold_1976_, v___x_1978_);
v___x_1980_ = lean_uint64_to_usize(v___x_1979_);
v___x_1981_ = lean_usize_of_nat(v___x_1972_);
v___x_1982_ = ((size_t)1ULL);
v___x_1983_ = lean_usize_sub(v___x_1981_, v___x_1982_);
v___x_1984_ = lean_usize_land(v___x_1980_, v___x_1983_);
v___x_1985_ = lean_array_uget_borrowed(v_x_1964_, v___x_1984_);
lean_inc(v___x_1985_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 2, v___x_1985_);
v___x_1987_ = v___x_1970_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_key_1966_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_value_1967_);
lean_ctor_set(v_reuseFailAlloc_1990_, 2, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1988_; 
v___x_1988_ = lean_array_uset(v_x_1964_, v___x_1984_, v___x_1987_);
v_x_1964_ = v___x_1988_;
v_x_1965_ = v_tail_1968_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3___redArg(lean_object* v_i_1992_, lean_object* v_source_1993_, lean_object* v_target_1994_){
_start:
{
lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = lean_array_get_size(v_source_1993_);
v___x_1996_ = lean_nat_dec_lt(v_i_1992_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_dec_ref(v_source_1993_);
lean_dec(v_i_1992_);
return v_target_1994_;
}
else
{
lean_object* v_es_1997_; lean_object* v___x_1998_; lean_object* v_source_1999_; lean_object* v_target_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v_es_1997_ = lean_array_fget(v_source_1993_, v_i_1992_);
v___x_1998_ = lean_box(0);
v_source_1999_ = lean_array_fset(v_source_1993_, v_i_1992_, v___x_1998_);
v_target_2000_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3_spec__5___redArg(v_target_1994_, v_es_1997_);
v___x_2001_ = lean_unsigned_to_nat(1u);
v___x_2002_ = lean_nat_add(v_i_1992_, v___x_2001_);
lean_dec(v_i_1992_);
v_i_1992_ = v___x_2002_;
v_source_1993_ = v_source_1999_;
v_target_1994_ = v_target_2000_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2___redArg(lean_object* v_data_2004_){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v_nbuckets_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2005_ = lean_array_get_size(v_data_2004_);
v___x_2006_ = lean_unsigned_to_nat(2u);
v_nbuckets_2007_ = lean_nat_mul(v___x_2005_, v___x_2006_);
v___x_2008_ = lean_unsigned_to_nat(0u);
v___x_2009_ = lean_box(0);
v___x_2010_ = lean_mk_array(v_nbuckets_2007_, v___x_2009_);
v___x_2011_ = lean_array_propagate_mark(v_data_2004_, v___x_2010_);
v___x_2012_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3___redArg(v___x_2008_, v_data_2004_, v___x_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1___redArg(lean_object* v_m_2013_, lean_object* v_a_2014_, lean_object* v_b_2015_){
_start:
{
lean_object* v_size_2016_; lean_object* v_buckets_2017_; lean_object* v___x_2018_; uint64_t v___x_2019_; uint64_t v___x_2020_; uint64_t v___x_2021_; uint64_t v_fold_2022_; uint64_t v___x_2023_; uint64_t v___x_2024_; uint64_t v___x_2025_; size_t v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; size_t v___x_2029_; size_t v___x_2030_; lean_object* v_bkt_2031_; uint8_t v___x_2032_; 
v_size_2016_ = lean_ctor_get(v_m_2013_, 0);
v_buckets_2017_ = lean_ctor_get(v_m_2013_, 1);
v___x_2018_ = lean_array_get_size(v_buckets_2017_);
v___x_2019_ = lean_byte_array_hash(v_a_2014_);
v___x_2020_ = 32ULL;
v___x_2021_ = lean_uint64_shift_right(v___x_2019_, v___x_2020_);
v_fold_2022_ = lean_uint64_xor(v___x_2019_, v___x_2021_);
v___x_2023_ = 16ULL;
v___x_2024_ = lean_uint64_shift_right(v_fold_2022_, v___x_2023_);
v___x_2025_ = lean_uint64_xor(v_fold_2022_, v___x_2024_);
v___x_2026_ = lean_uint64_to_usize(v___x_2025_);
v___x_2027_ = lean_usize_of_nat(v___x_2018_);
v___x_2028_ = ((size_t)1ULL);
v___x_2029_ = lean_usize_sub(v___x_2027_, v___x_2028_);
v___x_2030_ = lean_usize_land(v___x_2026_, v___x_2029_);
v_bkt_2031_ = lean_array_uget_borrowed(v_buckets_2017_, v___x_2030_);
v___x_2032_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___redArg(v_a_2014_, v_bkt_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2053_; 
lean_inc_ref(v_buckets_2017_);
lean_inc(v_size_2016_);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_m_2013_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; lean_object* v_unused_2055_; 
v_unused_2054_ = lean_ctor_get(v_m_2013_, 1);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_m_2013_, 0);
lean_dec(v_unused_2055_);
v___x_2034_ = v_m_2013_;
v_isShared_2035_ = v_isSharedCheck_2053_;
goto v_resetjp_2033_;
}
else
{
lean_dec(v_m_2013_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2053_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v_size_x27_2037_; lean_object* v___x_2038_; lean_object* v_buckets_x27_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; 
v___x_2036_ = lean_unsigned_to_nat(1u);
v_size_x27_2037_ = lean_nat_add(v_size_2016_, v___x_2036_);
lean_dec(v_size_2016_);
lean_inc(v_bkt_2031_);
v___x_2038_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2038_, 0, v_a_2014_);
lean_ctor_set(v___x_2038_, 1, v_b_2015_);
lean_ctor_set(v___x_2038_, 2, v_bkt_2031_);
v_buckets_x27_2039_ = lean_array_uset(v_buckets_2017_, v___x_2030_, v___x_2038_);
v___x_2040_ = lean_unsigned_to_nat(4u);
v___x_2041_ = lean_nat_mul(v_size_x27_2037_, v___x_2040_);
v___x_2042_ = lean_unsigned_to_nat(3u);
v___x_2043_ = lean_nat_div(v___x_2041_, v___x_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_array_get_size(v_buckets_x27_2039_);
v___x_2045_ = lean_nat_dec_le(v___x_2043_, v___x_2044_);
lean_dec(v___x_2043_);
if (v___x_2045_ == 0)
{
lean_object* v_val_2046_; lean_object* v___x_2048_; 
v_val_2046_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2___redArg(v_buckets_x27_2039_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 1, v_val_2046_);
lean_ctor_set(v___x_2034_, 0, v_size_x27_2037_);
v___x_2048_ = v___x_2034_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_size_x27_2037_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_val_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
else
{
lean_object* v___x_2051_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 1, v_buckets_x27_2039_);
lean_ctor_set(v___x_2034_, 0, v_size_x27_2037_);
v___x_2051_ = v___x_2034_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_size_x27_2037_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_buckets_x27_2039_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
else
{
lean_dec(v_b_2015_);
lean_dec_ref(v_a_2014_);
return v_m_2013_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_names_spec__2(lean_object* v_as_2056_, size_t v_i_2057_, size_t v_stop_2058_, lean_object* v_b_2059_){
_start:
{
lean_object* v___y_2061_; uint8_t v___x_2065_; 
v___x_2065_ = lean_usize_dec_eq(v_i_2057_, v_stop_2058_);
if (v___x_2065_ == 0)
{
lean_object* v_fst_2066_; lean_object* v_snd_2067_; lean_object* v___x_2068_; lean_object* v_fst_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2080_; 
v_fst_2066_ = lean_ctor_get(v_b_2059_, 0);
v_snd_2067_ = lean_ctor_get(v_b_2059_, 1);
v___x_2068_ = lean_array_uget(v_as_2056_, v_i_2057_);
v_fst_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; 
v_unused_2081_ = lean_ctor_get(v___x_2068_, 1);
lean_dec(v_unused_2081_);
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2080_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_fst_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2080_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
uint8_t v___x_2073_; 
v___x_2073_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0___redArg(v_fst_2066_, v_fst_2069_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
lean_inc(v_snd_2067_);
lean_inc(v_fst_2066_);
lean_dec_ref(v_b_2059_);
v___x_2074_ = lean_box(0);
lean_inc(v_fst_2069_);
v___x_2075_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1___redArg(v_fst_2066_, v_fst_2069_, v___x_2074_);
v___x_2076_ = lean_array_push(v_snd_2067_, v_fst_2069_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v___x_2076_);
lean_ctor_set(v___x_2071_, 0, v___x_2075_);
v___x_2078_ = v___x_2071_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
v___y_2061_ = v___x_2078_;
goto v___jp_2060_;
}
}
else
{
lean_del_object(v___x_2071_);
lean_dec(v_fst_2069_);
v___y_2061_ = v_b_2059_;
goto v___jp_2060_;
}
}
}
else
{
return v_b_2059_;
}
v___jp_2060_:
{
size_t v___x_2062_; size_t v___x_2063_; 
v___x_2062_ = ((size_t)1ULL);
v___x_2063_ = lean_usize_add(v_i_2057_, v___x_2062_);
v_i_2057_ = v___x_2063_;
v_b_2059_ = v___y_2061_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_names_spec__2___boxed(lean_object* v_as_2082_, lean_object* v_i_2083_, lean_object* v_stop_2084_, lean_object* v_b_2085_){
_start:
{
size_t v_i_boxed_2086_; size_t v_stop_boxed_2087_; lean_object* v_res_2088_; 
v_i_boxed_2086_ = lean_unbox_usize(v_i_2083_);
lean_dec(v_i_2083_);
v_stop_boxed_2087_ = lean_unbox_usize(v_stop_2084_);
lean_dec(v_stop_2084_);
v_res_2088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_names_spec__2(v_as_2082_, v_i_boxed_2086_, v_stop_boxed_2087_, v_b_2085_);
lean_dec_ref(v_as_2082_);
return v_res_2088_;
}
}
static lean_object* _init_l_Std_Http_URI_Query_names___closed__1(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = lean_unsigned_to_nat(16u);
v___x_2093_ = lean_mk_array(v___x_2092_, v___x_2091_);
return v___x_2093_;
}
}
static lean_object* _init_l_Std_Http_URI_Query_names___closed__2(void){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2094_ = lean_obj_once(&l_Std_Http_URI_Query_names___closed__1, &l_Std_Http_URI_Query_names___closed__1_once, _init_l_Std_Http_URI_Query_names___closed__1);
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
lean_ctor_set(v___x_2096_, 1, v___x_2094_);
return v___x_2096_;
}
}
static lean_object* _init_l_Std_Http_URI_Query_names___closed__3(void){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v_init_2099_; 
v___x_2097_ = ((lean_object*)(l_Std_Http_URI_Query_names___closed__0));
v___x_2098_ = lean_obj_once(&l_Std_Http_URI_Query_names___closed__2, &l_Std_Http_URI_Query_names___closed__2_once, _init_l_Std_Http_URI_Query_names___closed__2);
v_init_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_init_2099_, 0, v___x_2098_);
lean_ctor_set(v_init_2099_, 1, v___x_2097_);
return v_init_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names(lean_object* v_query_2100_){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = ((lean_object*)(l_Std_Http_URI_Query_names___closed__0));
v___x_2103_ = lean_array_get_size(v_query_2100_);
v___x_2104_ = lean_nat_dec_lt(v___x_2101_, v___x_2103_);
if (v___x_2104_ == 0)
{
return v___x_2102_;
}
else
{
lean_object* v_init_2105_; size_t v___x_2106_; size_t v___x_2107_; lean_object* v___x_2108_; lean_object* v_snd_2109_; 
v_init_2105_ = lean_obj_once(&l_Std_Http_URI_Query_names___closed__3, &l_Std_Http_URI_Query_names___closed__3_once, _init_l_Std_Http_URI_Query_names___closed__3);
v___x_2106_ = ((size_t)0ULL);
v___x_2107_ = lean_usize_of_nat(v___x_2103_);
v___x_2108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_names_spec__2(v_query_2100_, v___x_2106_, v___x_2107_, v_init_2105_);
v_snd_2109_ = lean_ctor_get(v___x_2108_, 1);
lean_inc(v_snd_2109_);
lean_dec_ref(v___x_2108_);
return v_snd_2109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names___boxed(lean_object* v_query_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Std_Http_URI_Query_names(v_query_2110_);
lean_dec_ref(v_query_2110_);
return v_res_2111_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0(lean_object* v_00_u03b2_2112_, lean_object* v_m_2113_, lean_object* v_a_2114_){
_start:
{
uint8_t v___x_2115_; 
v___x_2115_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0___redArg(v_m_2113_, v_a_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0___boxed(lean_object* v_00_u03b2_2116_, lean_object* v_m_2117_, lean_object* v_a_2118_){
_start:
{
uint8_t v_res_2119_; lean_object* v_r_2120_; 
v_res_2119_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0(v_00_u03b2_2116_, v_m_2117_, v_a_2118_);
lean_dec_ref(v_a_2118_);
lean_dec_ref(v_m_2117_);
v_r_2120_ = lean_box(v_res_2119_);
return v_r_2120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1(lean_object* v_00_u03b2_2121_, lean_object* v_m_2122_, lean_object* v_a_2123_, lean_object* v_b_2124_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1___redArg(v_m_2122_, v_a_2123_, v_b_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0(lean_object* v_00_u03b2_2126_, lean_object* v_a_2127_, lean_object* v_x_2128_){
_start:
{
uint8_t v___x_2129_; 
v___x_2129_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___redArg(v_a_2127_, v_x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2130_, lean_object* v_a_2131_, lean_object* v_x_2132_){
_start:
{
uint8_t v_res_2133_; lean_object* v_r_2134_; 
v_res_2133_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0(v_00_u03b2_2130_, v_a_2131_, v_x_2132_);
lean_dec(v_x_2132_);
lean_dec_ref(v_a_2131_);
v_r_2134_ = lean_box(v_res_2133_);
return v_r_2134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2(lean_object* v_00_u03b2_2135_, lean_object* v_data_2136_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2___redArg(v_data_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2138_, lean_object* v_i_2139_, lean_object* v_source_2140_, lean_object* v_target_2141_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3___redArg(v_i_2139_, v_source_2140_, v_target_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_2143_, lean_object* v_x_2144_, lean_object* v_x_2145_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3_spec__5___redArg(v_x_2144_, v_x_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(size_t v_sz_2147_, size_t v_i_2148_, lean_object* v_bs_2149_){
_start:
{
uint8_t v___x_2150_; 
v___x_2150_ = lean_usize_dec_lt(v_i_2148_, v_sz_2147_);
if (v___x_2150_ == 0)
{
return v_bs_2149_;
}
else
{
lean_object* v_v_2151_; lean_object* v_snd_2152_; lean_object* v___x_2153_; lean_object* v_bs_x27_2154_; size_t v___x_2155_; size_t v___x_2156_; lean_object* v___x_2157_; 
v_v_2151_ = lean_array_uget_borrowed(v_bs_2149_, v_i_2148_);
v_snd_2152_ = lean_ctor_get(v_v_2151_, 1);
lean_inc(v_snd_2152_);
v___x_2153_ = lean_unsigned_to_nat(0u);
v_bs_x27_2154_ = lean_array_uset(v_bs_2149_, v_i_2148_, v___x_2153_);
v___x_2155_ = ((size_t)1ULL);
v___x_2156_ = lean_usize_add(v_i_2148_, v___x_2155_);
v___x_2157_ = lean_array_uset(v_bs_x27_2154_, v_i_2148_, v_snd_2152_);
v_i_2148_ = v___x_2156_;
v_bs_2149_ = v___x_2157_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0___boxed(lean_object* v_sz_2159_, lean_object* v_i_2160_, lean_object* v_bs_2161_){
_start:
{
size_t v_sz_boxed_2162_; size_t v_i_boxed_2163_; lean_object* v_res_2164_; 
v_sz_boxed_2162_ = lean_unbox_usize(v_sz_2159_);
lean_dec(v_sz_2159_);
v_i_boxed_2163_ = lean_unbox_usize(v_i_2160_);
lean_dec(v_i_2160_);
v_res_2164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_boxed_2162_, v_i_boxed_2163_, v_bs_2161_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_values(lean_object* v_query_2165_){
_start:
{
size_t v_sz_2166_; size_t v___x_2167_; lean_object* v___x_2168_; 
v_sz_2166_ = lean_array_size(v_query_2165_);
v___x_2167_ = ((size_t)0ULL);
v___x_2168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_2166_, v___x_2167_, v_query_2165_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray(lean_object* v_query_2169_){
_start:
{
lean_inc_ref(v_query_2169_);
return v_query_2169_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray___boxed(lean_object* v_query_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Std_Http_URI_Query_toArray(v_query_2170_);
lean_dec_ref(v_query_2170_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1___redArg(lean_object* v_s_2172_, lean_object* v_replacement_2173_, lean_object* v_a_2174_, lean_object* v_b_2175_){
_start:
{
lean_object* v_str_2176_; lean_object* v_startInclusive_2177_; lean_object* v_endExclusive_2178_; lean_object* v___x_2179_; uint8_t v_decide_2180_; 
v_str_2176_ = lean_ctor_get(v_s_2172_, 0);
v_startInclusive_2177_ = lean_ctor_get(v_s_2172_, 1);
v_endExclusive_2178_ = lean_ctor_get(v_s_2172_, 2);
v___x_2179_ = lean_nat_sub(v_endExclusive_2178_, v_startInclusive_2177_);
v_decide_2180_ = lean_nat_dec_eq(v_a_2174_, v___x_2179_);
lean_dec(v___x_2179_);
if (v_decide_2180_ == 0)
{
lean_object* v___x_2181_; uint32_t v___x_2182_; uint32_t v___x_2183_; uint8_t v___x_2184_; 
v___x_2181_ = lean_nat_add(v_startInclusive_2177_, v_a_2174_);
v___x_2182_ = lean_string_utf8_get_fast(v_str_2176_, v___x_2181_);
v___x_2183_ = 61;
v___x_2184_ = lean_uint32_dec_eq(v___x_2182_, v___x_2183_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v_str_2188_; lean_object* v_startInclusive_2189_; lean_object* v_endExclusive_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2185_ = lean_string_utf8_next_fast(v_str_2176_, v___x_2181_);
lean_dec(v___x_2181_);
v___x_2186_ = lean_nat_sub(v___x_2185_, v_startInclusive_2177_);
lean_inc_ref(v_s_2172_);
v___x_2187_ = l_String_Slice_slice_x21(v_s_2172_, v_a_2174_, v___x_2186_);
lean_dec(v_a_2174_);
v_str_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc_ref(v_str_2188_);
v_startInclusive_2189_ = lean_ctor_get(v___x_2187_, 1);
lean_inc(v_startInclusive_2189_);
v_endExclusive_2190_ = lean_ctor_get(v___x_2187_, 2);
lean_inc(v_endExclusive_2190_);
lean_dec_ref(v___x_2187_);
v___x_2191_ = lean_string_utf8_extract_fast(v_str_2188_, v_startInclusive_2189_, v_endExclusive_2190_);
lean_dec(v_endExclusive_2190_);
lean_dec(v_startInclusive_2189_);
lean_dec_ref(v_str_2188_);
v___x_2192_ = lean_string_append(v_b_2175_, v___x_2191_);
lean_dec_ref(v___x_2191_);
v_a_2174_ = v___x_2186_;
v_b_2175_ = v___x_2192_;
goto _start;
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2194_ = lean_string_utf8_next_fast(v_str_2176_, v___x_2181_);
v___x_2195_ = lean_nat_sub(v___x_2194_, v___x_2181_);
lean_dec(v___x_2181_);
v___x_2196_ = lean_nat_add(v_a_2174_, v___x_2195_);
lean_dec(v___x_2195_);
lean_dec(v_a_2174_);
v___x_2197_ = lean_unsigned_to_nat(0u);
v___x_2198_ = lean_string_utf8_byte_size(v_replacement_2173_);
v___x_2199_ = lean_string_utf8_extract_fast(v_replacement_2173_, v___x_2197_, v___x_2198_);
v___x_2200_ = lean_string_append(v_b_2175_, v___x_2199_);
lean_dec_ref(v___x_2199_);
v_a_2174_ = v___x_2196_;
v_b_2175_ = v___x_2200_;
goto _start;
}
}
else
{
lean_dec(v_a_2174_);
lean_dec_ref(v_s_2172_);
return v_b_2175_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1___redArg___boxed(lean_object* v_s_2202_, lean_object* v_replacement_2203_, lean_object* v_a_2204_, lean_object* v_b_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1___redArg(v_s_2202_, v_replacement_2203_, v_a_2204_, v_b_2205_);
lean_dec_ref(v_replacement_2203_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1___redArg(lean_object* v_s_2207_, lean_object* v_replacement_2208_){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___x_2210_ = lean_unsigned_to_nat(0u);
v___x_2211_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1___redArg(v_s_2207_, v_replacement_2208_, v___x_2210_, v___x_2209_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1___redArg___boxed(lean_object* v_s_2212_, lean_object* v_replacement_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1___redArg(v_s_2212_, v_replacement_2213_);
lean_dec_ref(v_replacement_2213_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Query_formatQueryParam_spec__0(lean_object* v_a_2215_, lean_object* v_i_2216_){
_start:
{
lean_object* v___x_2217_; uint8_t v___x_2218_; 
v___x_2217_ = lean_byte_array_size(v_a_2215_);
v___x_2218_ = lean_nat_dec_lt(v_i_2216_, v___x_2217_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; 
lean_dec(v_i_2216_);
v___x_2219_ = lean_box(0);
return v___x_2219_;
}
else
{
uint8_t v___x_2220_; uint8_t v___x_2221_; uint8_t v___x_2222_; 
v___x_2220_ = lean_byte_array_fget(v_a_2215_, v_i_2216_);
v___x_2221_ = 61;
v___x_2222_ = lean_uint8_dec_eq(v___x_2220_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = lean_unsigned_to_nat(1u);
v___x_2224_ = lean_nat_add(v_i_2216_, v___x_2223_);
lean_dec(v_i_2216_);
v_i_2216_ = v___x_2224_;
goto _start;
}
else
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_i_2216_);
return v___x_2226_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Query_formatQueryParam_spec__0___boxed(lean_object* v_a_2227_, lean_object* v_i_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Query_formatQueryParam_spec__0(v_a_2227_, v_i_2228_);
lean_dec_ref(v_a_2227_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object* v_key_2232_, lean_object* v_value_2233_){
_start:
{
lean_object* v___y_2235_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_unsigned_to_nat(0u);
v___x_2242_ = l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Query_formatQueryParam_spec__0(v_key_2232_, v___x_2241_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v___x_2243_; 
v___x_2243_ = lean_string_from_utf8_unchecked(v_key_2232_);
v___y_2235_ = v___x_2243_;
goto v___jp_2234_;
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
lean_dec_ref_known(v___x_2242_, 1);
v___x_2244_ = lean_string_from_utf8_unchecked(v_key_2232_);
v___x_2245_ = ((lean_object*)(l_Std_Http_URI_Query_formatQueryParam___closed__1));
v___x_2246_ = lean_string_utf8_byte_size(v___x_2244_);
v___x_2247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2244_);
lean_ctor_set(v___x_2247_, 1, v___x_2241_);
lean_ctor_set(v___x_2247_, 2, v___x_2246_);
v___x_2248_ = l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1___redArg(v___x_2247_, v___x_2245_);
v___y_2235_ = v___x_2248_;
goto v___jp_2234_;
}
v___jp_2234_:
{
if (lean_obj_tag(v_value_2233_) == 0)
{
return v___y_2235_;
}
else
{
lean_object* v_val_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v_val_2236_ = lean_ctor_get(v_value_2233_, 0);
lean_inc(v_val_2236_);
lean_dec_ref_known(v_value_2233_, 1);
v___x_2237_ = ((lean_object*)(l_Std_Http_URI_Query_formatQueryParam___closed__0));
v___x_2238_ = lean_string_append(v___y_2235_, v___x_2237_);
v___x_2239_ = lean_string_from_utf8_unchecked(v_val_2236_);
v___x_2240_ = lean_string_append(v___x_2238_, v___x_2239_);
lean_dec_ref(v___x_2239_);
return v___x_2240_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1(lean_object* v_s_2249_, uint32_t v_pattern_2250_, lean_object* v_replacement_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1___redArg(v_s_2249_, v_replacement_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1___boxed(lean_object* v_s_2253_, lean_object* v_pattern_2254_, lean_object* v_replacement_2255_){
_start:
{
uint32_t v_pattern_boxed_2256_; lean_object* v_res_2257_; 
v_pattern_boxed_2256_ = lean_unbox_uint32(v_pattern_2254_);
lean_dec(v_pattern_2254_);
v_res_2257_ = l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1(v_s_2253_, v_pattern_boxed_2256_, v_replacement_2255_);
lean_dec_ref(v_replacement_2255_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1(lean_object* v_s_2258_, lean_object* v_replacement_2259_, lean_object* v_inst_2260_, lean_object* v_R_2261_, lean_object* v_a_2262_, lean_object* v_b_2263_, lean_object* v_c_2264_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1___redArg(v_s_2258_, v_replacement_2259_, v_a_2262_, v_b_2263_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1___boxed(lean_object* v_s_2266_, lean_object* v_replacement_2267_, lean_object* v_inst_2268_, lean_object* v_R_2269_, lean_object* v_a_2270_, lean_object* v_b_2271_, lean_object* v_c_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1(v_s_2266_, v_replacement_2267_, v_inst_2268_, v_R_2269_, v_a_2270_, v_b_2271_, v_c_2272_);
lean_dec_ref(v_replacement_2267_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(lean_object* v_key_2277_, lean_object* v_as_2278_, size_t v_sz_2279_, size_t v_i_2280_, lean_object* v_b_2281_){
_start:
{
uint8_t v___x_2282_; 
v___x_2282_ = lean_usize_dec_lt(v_i_2280_, v_sz_2279_);
if (v___x_2282_ == 0)
{
lean_inc_ref(v_b_2281_);
return v_b_2281_;
}
else
{
lean_object* v_a_2283_; lean_object* v_fst_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; 
v_a_2283_ = lean_array_uget_borrowed(v_as_2278_, v_i_2280_);
v_fst_2284_ = lean_ctor_get(v_a_2283_, 0);
v___x_2285_ = lean_box(0);
v___x_2286_ = lean_sarray_dec_eq(v_fst_2284_, v_key_2277_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; size_t v___x_2288_; size_t v___x_2289_; 
v___x_2287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v___x_2288_ = ((size_t)1ULL);
v___x_2289_ = lean_usize_add(v_i_2280_, v___x_2288_);
v_i_2280_ = v___x_2289_;
v_b_2281_ = v___x_2287_;
goto _start;
}
else
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_inc(v_a_2283_);
v___x_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2291_, 0, v_a_2283_);
v___x_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
v___x_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
lean_ctor_set(v___x_2293_, 1, v___x_2285_);
return v___x_2293_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___boxed(lean_object* v_key_2294_, lean_object* v_as_2295_, lean_object* v_sz_2296_, lean_object* v_i_2297_, lean_object* v_b_2298_){
_start:
{
size_t v_sz_boxed_2299_; size_t v_i_boxed_2300_; lean_object* v_res_2301_; 
v_sz_boxed_2299_ = lean_unbox_usize(v_sz_2296_);
lean_dec(v_sz_2296_);
v_i_boxed_2300_ = lean_unbox_usize(v_i_2297_);
lean_dec(v_i_2297_);
v_res_2301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_2294_, v_as_2295_, v_sz_boxed_2299_, v_i_boxed_2300_, v_b_2298_);
lean_dec_ref(v_b_2298_);
lean_dec_ref(v_as_2295_);
lean_dec_ref(v_key_2294_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f(lean_object* v_query_2302_, lean_object* v_key_2303_){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; size_t v_sz_2306_; size_t v___x_2307_; lean_object* v___x_2308_; lean_object* v_fst_2309_; 
v___x_2304_ = lean_box(0);
v___x_2305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v_sz_2306_ = lean_array_size(v_query_2302_);
v___x_2307_ = ((size_t)0ULL);
v___x_2308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_2303_, v_query_2302_, v_sz_2306_, v___x_2307_, v___x_2305_);
v_fst_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_fst_2309_);
lean_dec_ref(v___x_2308_);
if (lean_obj_tag(v_fst_2309_) == 0)
{
return v___x_2304_;
}
else
{
lean_object* v_val_2310_; 
v_val_2310_ = lean_ctor_get(v_fst_2309_, 0);
lean_inc(v_val_2310_);
lean_dec_ref_known(v_fst_2309_, 1);
if (lean_obj_tag(v_val_2310_) == 0)
{
return v___x_2304_;
}
else
{
lean_object* v_val_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2319_; 
v_val_2311_ = lean_ctor_get(v_val_2310_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_val_2310_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2313_ = v_val_2310_;
v_isShared_2314_ = v_isSharedCheck_2319_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_val_2311_);
lean_dec(v_val_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2319_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v_snd_2315_; lean_object* v___x_2317_; 
v_snd_2315_ = lean_ctor_get(v_val_2311_, 1);
lean_inc(v_snd_2315_);
lean_dec(v_val_2311_);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v_snd_2315_);
v___x_2317_ = v___x_2313_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_snd_2315_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f___boxed(lean_object* v_query_2320_, lean_object* v_key_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_2320_, v_key_2321_);
lean_dec_ref(v_key_2321_);
lean_dec_ref(v_query_2320_);
return v_res_2322_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs(lean_object* v_key_2323_, lean_object* v_name_2324_){
_start:
{
uint8_t v___x_2325_; 
v___x_2325_ = l_Std_Http_URI_EncodedQueryString_decodesTo___redArg(v_name_2324_, v_key_2323_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs___boxed(lean_object* v_key_2326_, lean_object* v_name_2327_){
_start:
{
uint8_t v_res_2328_; lean_object* v_r_2329_; 
v_res_2328_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs(v_key_2326_, v_name_2327_);
lean_dec_ref(v_name_2327_);
lean_dec_ref(v_key_2326_);
v_r_2329_ = lean_box(v_res_2328_);
return v_r_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_find_x3f_spec__0(lean_object* v_key_2330_, lean_object* v_as_2331_, size_t v_sz_2332_, size_t v_i_2333_, lean_object* v_b_2334_){
_start:
{
uint8_t v___x_2335_; 
v___x_2335_ = lean_usize_dec_lt(v_i_2333_, v_sz_2332_);
if (v___x_2335_ == 0)
{
lean_inc_ref(v_b_2334_);
return v_b_2334_;
}
else
{
lean_object* v_a_2336_; lean_object* v_fst_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v_a_2336_ = lean_array_uget_borrowed(v_as_2331_, v_i_2333_);
v_fst_2337_ = lean_ctor_get(v_a_2336_, 0);
v___x_2338_ = lean_box(0);
v___x_2339_ = l_Std_Http_URI_EncodedQueryString_decodesTo___redArg(v_fst_2337_, v_key_2330_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; size_t v___x_2341_; size_t v___x_2342_; 
v___x_2340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v___x_2341_ = ((size_t)1ULL);
v___x_2342_ = lean_usize_add(v_i_2333_, v___x_2341_);
v_i_2333_ = v___x_2342_;
v_b_2334_ = v___x_2340_;
goto _start;
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
lean_inc(v_a_2336_);
v___x_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2344_, 0, v_a_2336_);
v___x_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
v___x_2346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
lean_ctor_set(v___x_2346_, 1, v___x_2338_);
return v___x_2346_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_find_x3f_spec__0___boxed(lean_object* v_key_2347_, lean_object* v_as_2348_, lean_object* v_sz_2349_, lean_object* v_i_2350_, lean_object* v_b_2351_){
_start:
{
size_t v_sz_boxed_2352_; size_t v_i_boxed_2353_; lean_object* v_res_2354_; 
v_sz_boxed_2352_ = lean_unbox_usize(v_sz_2349_);
lean_dec(v_sz_2349_);
v_i_boxed_2353_ = lean_unbox_usize(v_i_2350_);
lean_dec(v_i_2350_);
v_res_2354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_find_x3f_spec__0(v_key_2347_, v_as_2348_, v_sz_boxed_2352_, v_i_boxed_2353_, v_b_2351_);
lean_dec_ref(v_b_2351_);
lean_dec_ref(v_as_2348_);
lean_dec_ref(v_key_2347_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f(lean_object* v_query_2355_, lean_object* v_key_2356_){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; size_t v_sz_2359_; size_t v___x_2360_; lean_object* v___x_2361_; lean_object* v_fst_2362_; 
v___x_2357_ = lean_box(0);
v___x_2358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v_sz_2359_ = lean_array_size(v_query_2355_);
v___x_2360_ = ((size_t)0ULL);
v___x_2361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_find_x3f_spec__0(v_key_2356_, v_query_2355_, v_sz_2359_, v___x_2360_, v___x_2358_);
v_fst_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_fst_2362_);
lean_dec_ref(v___x_2361_);
if (lean_obj_tag(v_fst_2362_) == 0)
{
return v___x_2357_;
}
else
{
lean_object* v_val_2363_; 
v_val_2363_ = lean_ctor_get(v_fst_2362_, 0);
lean_inc(v_val_2363_);
lean_dec_ref_known(v_fst_2362_, 1);
if (lean_obj_tag(v_val_2363_) == 0)
{
return v___x_2357_;
}
else
{
lean_object* v_val_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2372_; 
v_val_2364_ = lean_ctor_get(v_val_2363_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_val_2363_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2366_ = v_val_2363_;
v_isShared_2367_ = v_isSharedCheck_2372_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_val_2364_);
lean_dec(v_val_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2372_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v_snd_2368_; lean_object* v___x_2370_; 
v_snd_2368_ = lean_ctor_get(v_val_2364_, 1);
lean_inc(v_snd_2368_);
lean_dec(v_val_2364_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v_snd_2368_);
v___x_2370_ = v___x_2366_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_snd_2368_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f___boxed(lean_object* v_query_2373_, lean_object* v_key_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Std_Http_URI_Query_find_x3f(v_query_2373_, v_key_2374_);
lean_dec_ref(v_key_2374_);
lean_dec_ref(v_query_2373_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(lean_object* v_key_2376_, lean_object* v_as_2377_, size_t v_i_2378_, size_t v_stop_2379_, lean_object* v_b_2380_){
_start:
{
lean_object* v___y_2382_; uint8_t v___x_2386_; 
v___x_2386_ = lean_usize_dec_eq(v_i_2378_, v_stop_2379_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; lean_object* v_fst_2388_; lean_object* v_snd_2389_; uint8_t v___x_2390_; 
v___x_2387_ = lean_array_uget_borrowed(v_as_2377_, v_i_2378_);
v_fst_2388_ = lean_ctor_get(v___x_2387_, 0);
v_snd_2389_ = lean_ctor_get(v___x_2387_, 1);
v___x_2390_ = lean_sarray_dec_eq(v_fst_2388_, v_key_2376_);
if (v___x_2390_ == 0)
{
v___y_2382_ = v_b_2380_;
goto v___jp_2381_;
}
else
{
lean_object* v___x_2391_; 
lean_inc(v_snd_2389_);
v___x_2391_ = lean_array_push(v_b_2380_, v_snd_2389_);
v___y_2382_ = v___x_2391_;
goto v___jp_2381_;
}
}
else
{
return v_b_2380_;
}
v___jp_2381_:
{
size_t v___x_2383_; size_t v___x_2384_; 
v___x_2383_ = ((size_t)1ULL);
v___x_2384_ = lean_usize_add(v_i_2378_, v___x_2383_);
v_i_2378_ = v___x_2384_;
v_b_2380_ = v___y_2382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0___boxed(lean_object* v_key_2392_, lean_object* v_as_2393_, lean_object* v_i_2394_, lean_object* v_stop_2395_, lean_object* v_b_2396_){
_start:
{
size_t v_i_boxed_2397_; size_t v_stop_boxed_2398_; lean_object* v_res_2399_; 
v_i_boxed_2397_ = lean_unbox_usize(v_i_2394_);
lean_dec(v_i_2394_);
v_stop_boxed_2398_ = lean_unbox_usize(v_stop_2395_);
lean_dec(v_stop_2395_);
v_res_2399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_2392_, v_as_2393_, v_i_boxed_2397_, v_stop_boxed_2398_, v_b_2396_);
lean_dec_ref(v_as_2393_);
lean_dec_ref(v_key_2392_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(lean_object* v_key_2402_, lean_object* v_as_2403_, lean_object* v_start_2404_, lean_object* v_stop_2405_){
_start:
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_2407_ = lean_nat_dec_lt(v_start_2404_, v_stop_2405_);
if (v___x_2407_ == 0)
{
return v___x_2406_;
}
else
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = lean_array_get_size(v_as_2403_);
v___x_2409_ = lean_nat_dec_le(v_stop_2405_, v___x_2408_);
if (v___x_2409_ == 0)
{
uint8_t v___x_2410_; 
v___x_2410_ = lean_nat_dec_lt(v_start_2404_, v___x_2408_);
if (v___x_2410_ == 0)
{
return v___x_2406_;
}
else
{
size_t v___x_2411_; size_t v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = lean_usize_of_nat(v_start_2404_);
v___x_2412_ = lean_usize_of_nat(v___x_2408_);
v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_2402_, v_as_2403_, v___x_2411_, v___x_2412_, v___x_2406_);
return v___x_2413_;
}
}
else
{
size_t v___x_2414_; size_t v___x_2415_; lean_object* v___x_2416_; 
v___x_2414_ = lean_usize_of_nat(v_start_2404_);
v___x_2415_ = lean_usize_of_nat(v_stop_2405_);
v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_2402_, v_as_2403_, v___x_2414_, v___x_2415_, v___x_2406_);
return v___x_2416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___boxed(lean_object* v_key_2417_, lean_object* v_as_2418_, lean_object* v_start_2419_, lean_object* v_stop_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_2417_, v_as_2418_, v_start_2419_, v_stop_2420_);
lean_dec(v_stop_2420_);
lean_dec(v_start_2419_);
lean_dec_ref(v_as_2418_);
lean_dec_ref(v_key_2417_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded(lean_object* v_query_2422_, lean_object* v_key_2423_){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2424_ = lean_unsigned_to_nat(0u);
v___x_2425_ = lean_array_get_size(v_query_2422_);
v___x_2426_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_2423_, v_query_2422_, v___x_2424_, v___x_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded___boxed(lean_object* v_query_2427_, lean_object* v_key_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Std_Http_URI_Query_findAllEncoded(v_query_2427_, v_key_2428_);
lean_dec_ref(v_key_2428_);
lean_dec_ref(v_query_2427_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0(lean_object* v_key_2430_, lean_object* v_as_2431_, size_t v_i_2432_, size_t v_stop_2433_, lean_object* v_b_2434_){
_start:
{
lean_object* v___y_2436_; uint8_t v___x_2440_; 
v___x_2440_ = lean_usize_dec_eq(v_i_2432_, v_stop_2433_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; lean_object* v_fst_2442_; lean_object* v_snd_2443_; uint8_t v___x_2444_; 
v___x_2441_ = lean_array_uget_borrowed(v_as_2431_, v_i_2432_);
v_fst_2442_ = lean_ctor_get(v___x_2441_, 0);
v_snd_2443_ = lean_ctor_get(v___x_2441_, 1);
v___x_2444_ = l_Std_Http_URI_EncodedQueryString_decodesTo___redArg(v_fst_2442_, v_key_2430_);
if (v___x_2444_ == 0)
{
v___y_2436_ = v_b_2434_;
goto v___jp_2435_;
}
else
{
lean_object* v___x_2445_; 
lean_inc(v_snd_2443_);
v___x_2445_ = lean_array_push(v_b_2434_, v_snd_2443_);
v___y_2436_ = v___x_2445_;
goto v___jp_2435_;
}
}
else
{
return v_b_2434_;
}
v___jp_2435_:
{
size_t v___x_2437_; size_t v___x_2438_; 
v___x_2437_ = ((size_t)1ULL);
v___x_2438_ = lean_usize_add(v_i_2432_, v___x_2437_);
v_i_2432_ = v___x_2438_;
v_b_2434_ = v___y_2436_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0___boxed(lean_object* v_key_2446_, lean_object* v_as_2447_, lean_object* v_i_2448_, lean_object* v_stop_2449_, lean_object* v_b_2450_){
_start:
{
size_t v_i_boxed_2451_; size_t v_stop_boxed_2452_; lean_object* v_res_2453_; 
v_i_boxed_2451_ = lean_unbox_usize(v_i_2448_);
lean_dec(v_i_2448_);
v_stop_boxed_2452_ = lean_unbox_usize(v_stop_2449_);
lean_dec(v_stop_2449_);
v_res_2453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0(v_key_2446_, v_as_2447_, v_i_boxed_2451_, v_stop_boxed_2452_, v_b_2450_);
lean_dec_ref(v_as_2447_);
lean_dec_ref(v_key_2446_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0(lean_object* v_key_2454_, lean_object* v_as_2455_, lean_object* v_start_2456_, lean_object* v_stop_2457_){
_start:
{
lean_object* v___x_2458_; uint8_t v___x_2459_; 
v___x_2458_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_2459_ = lean_nat_dec_lt(v_start_2456_, v_stop_2457_);
if (v___x_2459_ == 0)
{
return v___x_2458_;
}
else
{
lean_object* v___x_2460_; uint8_t v___x_2461_; 
v___x_2460_ = lean_array_get_size(v_as_2455_);
v___x_2461_ = lean_nat_dec_le(v_stop_2457_, v___x_2460_);
if (v___x_2461_ == 0)
{
uint8_t v___x_2462_; 
v___x_2462_ = lean_nat_dec_lt(v_start_2456_, v___x_2460_);
if (v___x_2462_ == 0)
{
return v___x_2458_;
}
else
{
size_t v___x_2463_; size_t v___x_2464_; lean_object* v___x_2465_; 
v___x_2463_ = lean_usize_of_nat(v_start_2456_);
v___x_2464_ = lean_usize_of_nat(v___x_2460_);
v___x_2465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0(v_key_2454_, v_as_2455_, v___x_2463_, v___x_2464_, v___x_2458_);
return v___x_2465_;
}
}
else
{
size_t v___x_2466_; size_t v___x_2467_; lean_object* v___x_2468_; 
v___x_2466_ = lean_usize_of_nat(v_start_2456_);
v___x_2467_ = lean_usize_of_nat(v_stop_2457_);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0(v_key_2454_, v_as_2455_, v___x_2466_, v___x_2467_, v___x_2458_);
return v___x_2468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0___boxed(lean_object* v_key_2469_, lean_object* v_as_2470_, lean_object* v_start_2471_, lean_object* v_stop_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0(v_key_2469_, v_as_2470_, v_start_2471_, v_stop_2472_);
lean_dec(v_stop_2472_);
lean_dec(v_start_2471_);
lean_dec_ref(v_as_2470_);
lean_dec_ref(v_key_2469_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll(lean_object* v_query_2474_, lean_object* v_key_2475_){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = lean_unsigned_to_nat(0u);
v___x_2477_ = lean_array_get_size(v_query_2474_);
v___x_2478_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0(v_key_2475_, v_query_2474_, v___x_2476_, v___x_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll___boxed(lean_object* v_query_2479_, lean_object* v_key_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Std_Http_URI_Query_findAll(v_query_2479_, v_key_2480_);
lean_dec_ref(v_key_2480_);
lean_dec_ref(v_query_2479_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert(lean_object* v_query_2482_, lean_object* v_key_2483_, lean_object* v_value_2484_){
_start:
{
lean_object* v_encodedKey_2485_; lean_object* v_encodedValue_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v_encodedKey_2485_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_2483_);
v_encodedValue_2486_ = l_Std_Http_URI_EncodedQueryParam_encode(v_value_2484_);
v___x_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2487_, 0, v_encodedValue_2486_);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v_encodedKey_2485_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = lean_array_push(v_query_2482_, v___x_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object* v_query_2490_, lean_object* v_key_2491_, lean_object* v_value_2492_){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v_key_2491_);
lean_ctor_set(v___x_2493_, 1, v_value_2492_);
v___x_2494_ = lean_array_push(v_query_2490_, v___x_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_ofList(lean_object* v_pairs_2498_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = lean_array_mk(v_pairs_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(lean_object* v_key_2500_, lean_object* v_as_2501_, size_t v_i_2502_, size_t v_stop_2503_){
_start:
{
uint8_t v___x_2504_; 
v___x_2504_ = lean_usize_dec_eq(v_i_2502_, v_stop_2503_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; lean_object* v_fst_2506_; uint8_t v___x_2507_; 
v___x_2505_ = lean_array_uget_borrowed(v_as_2501_, v_i_2502_);
v_fst_2506_ = lean_ctor_get(v___x_2505_, 0);
v___x_2507_ = lean_sarray_dec_eq(v_fst_2506_, v_key_2500_);
if (v___x_2507_ == 0)
{
size_t v___x_2508_; size_t v___x_2509_; 
v___x_2508_ = ((size_t)1ULL);
v___x_2509_ = lean_usize_add(v_i_2502_, v___x_2508_);
v_i_2502_ = v___x_2509_;
goto _start;
}
else
{
return v___x_2507_;
}
}
else
{
uint8_t v___x_2511_; 
v___x_2511_ = 0;
return v___x_2511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(lean_object* v_key_2512_, lean_object* v_as_2513_, lean_object* v_i_2514_, lean_object* v_stop_2515_){
_start:
{
size_t v_i_boxed_2516_; size_t v_stop_boxed_2517_; uint8_t v_res_2518_; lean_object* v_r_2519_; 
v_i_boxed_2516_ = lean_unbox_usize(v_i_2514_);
lean_dec(v_i_2514_);
v_stop_boxed_2517_ = lean_unbox_usize(v_stop_2515_);
lean_dec(v_stop_2515_);
v_res_2518_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_2512_, v_as_2513_, v_i_boxed_2516_, v_stop_boxed_2517_);
lean_dec_ref(v_as_2513_);
lean_dec_ref(v_key_2512_);
v_r_2519_ = lean_box(v_res_2518_);
return v_r_2519_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_containsEncoded(lean_object* v_query_2520_, lean_object* v_key_2521_){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___x_2522_ = lean_unsigned_to_nat(0u);
v___x_2523_ = lean_array_get_size(v_query_2520_);
v___x_2524_ = lean_nat_dec_lt(v___x_2522_, v___x_2523_);
if (v___x_2524_ == 0)
{
return v___x_2524_;
}
else
{
if (v___x_2524_ == 0)
{
return v___x_2524_;
}
else
{
size_t v___x_2525_; size_t v___x_2526_; uint8_t v___x_2527_; 
v___x_2525_ = ((size_t)0ULL);
v___x_2526_ = lean_usize_of_nat(v___x_2523_);
v___x_2527_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_2521_, v_query_2520_, v___x_2525_, v___x_2526_);
return v___x_2527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_containsEncoded___boxed(lean_object* v_query_2528_, lean_object* v_key_2529_){
_start:
{
uint8_t v_res_2530_; lean_object* v_r_2531_; 
v_res_2530_ = l_Std_Http_URI_Query_containsEncoded(v_query_2528_, v_key_2529_);
lean_dec_ref(v_key_2529_);
lean_dec_ref(v_query_2528_);
v_r_2531_ = lean_box(v_res_2530_);
return v_r_2531_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_contains_spec__0(lean_object* v_key_2532_, lean_object* v_as_2533_, size_t v_i_2534_, size_t v_stop_2535_){
_start:
{
uint8_t v___x_2536_; 
v___x_2536_ = lean_usize_dec_eq(v_i_2534_, v_stop_2535_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; lean_object* v_fst_2538_; uint8_t v___x_2539_; 
v___x_2537_ = lean_array_uget_borrowed(v_as_2533_, v_i_2534_);
v_fst_2538_ = lean_ctor_get(v___x_2537_, 0);
v___x_2539_ = l_Std_Http_URI_EncodedQueryString_decodesTo___redArg(v_fst_2538_, v_key_2532_);
if (v___x_2539_ == 0)
{
size_t v___x_2540_; size_t v___x_2541_; 
v___x_2540_ = ((size_t)1ULL);
v___x_2541_ = lean_usize_add(v_i_2534_, v___x_2540_);
v_i_2534_ = v___x_2541_;
goto _start;
}
else
{
return v___x_2539_;
}
}
else
{
uint8_t v___x_2543_; 
v___x_2543_ = 0;
return v___x_2543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_contains_spec__0___boxed(lean_object* v_key_2544_, lean_object* v_as_2545_, lean_object* v_i_2546_, lean_object* v_stop_2547_){
_start:
{
size_t v_i_boxed_2548_; size_t v_stop_boxed_2549_; uint8_t v_res_2550_; lean_object* v_r_2551_; 
v_i_boxed_2548_ = lean_unbox_usize(v_i_2546_);
lean_dec(v_i_2546_);
v_stop_boxed_2549_ = lean_unbox_usize(v_stop_2547_);
lean_dec(v_stop_2547_);
v_res_2550_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_contains_spec__0(v_key_2544_, v_as_2545_, v_i_boxed_2548_, v_stop_boxed_2549_);
lean_dec_ref(v_as_2545_);
lean_dec_ref(v_key_2544_);
v_r_2551_ = lean_box(v_res_2550_);
return v_r_2551_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_contains(lean_object* v_query_2552_, lean_object* v_key_2553_){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
v___x_2554_ = lean_unsigned_to_nat(0u);
v___x_2555_ = lean_array_get_size(v_query_2552_);
v___x_2556_ = lean_nat_dec_lt(v___x_2554_, v___x_2555_);
if (v___x_2556_ == 0)
{
return v___x_2556_;
}
else
{
if (v___x_2556_ == 0)
{
return v___x_2556_;
}
else
{
size_t v___x_2557_; size_t v___x_2558_; uint8_t v___x_2559_; 
v___x_2557_ = ((size_t)0ULL);
v___x_2558_ = lean_usize_of_nat(v___x_2555_);
v___x_2559_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_contains_spec__0(v_key_2553_, v_query_2552_, v___x_2557_, v___x_2558_);
return v___x_2559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_contains___boxed(lean_object* v_query_2560_, lean_object* v_key_2561_){
_start:
{
uint8_t v_res_2562_; lean_object* v_r_2563_; 
v_res_2562_ = l_Std_Http_URI_Query_contains(v_query_2560_, v_key_2561_);
lean_dec_ref(v_key_2561_);
lean_dec_ref(v_query_2560_);
v_r_2563_ = lean_box(v_res_2562_);
return v_r_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(lean_object* v_key_2564_, lean_object* v_as_2565_, size_t v_i_2566_, size_t v_stop_2567_, lean_object* v_b_2568_){
_start:
{
lean_object* v___y_2570_; uint8_t v___x_2574_; 
v___x_2574_ = lean_usize_dec_eq(v_i_2566_, v_stop_2567_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; lean_object* v_fst_2576_; uint8_t v___x_2577_; 
v___x_2575_ = lean_array_uget_borrowed(v_as_2565_, v_i_2566_);
v_fst_2576_ = lean_ctor_get(v___x_2575_, 0);
v___x_2577_ = lean_sarray_dec_eq(v_fst_2576_, v_key_2564_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; 
lean_inc(v___x_2575_);
v___x_2578_ = lean_array_push(v_b_2568_, v___x_2575_);
v___y_2570_ = v___x_2578_;
goto v___jp_2569_;
}
else
{
v___y_2570_ = v_b_2568_;
goto v___jp_2569_;
}
}
else
{
return v_b_2568_;
}
v___jp_2569_:
{
size_t v___x_2571_; size_t v___x_2572_; 
v___x_2571_ = ((size_t)1ULL);
v___x_2572_ = lean_usize_add(v_i_2566_, v___x_2571_);
v_i_2566_ = v___x_2572_;
v_b_2568_ = v___y_2570_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(lean_object* v_key_2579_, lean_object* v_as_2580_, lean_object* v_i_2581_, lean_object* v_stop_2582_, lean_object* v_b_2583_){
_start:
{
size_t v_i_boxed_2584_; size_t v_stop_boxed_2585_; lean_object* v_res_2586_; 
v_i_boxed_2584_ = lean_unbox_usize(v_i_2581_);
lean_dec(v_i_2581_);
v_stop_boxed_2585_ = lean_unbox_usize(v_stop_2582_);
lean_dec(v_stop_2582_);
v_res_2586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2579_, v_as_2580_, v_i_boxed_2584_, v_stop_boxed_2585_, v_b_2583_);
lean_dec_ref(v_as_2580_);
lean_dec_ref(v_key_2579_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded(lean_object* v_query_2587_, lean_object* v_key_2588_){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; 
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = lean_array_get_size(v_query_2587_);
v___x_2591_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_2592_ = lean_nat_dec_lt(v___x_2589_, v___x_2590_);
if (v___x_2592_ == 0)
{
return v___x_2591_;
}
else
{
size_t v___x_2593_; size_t v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = ((size_t)0ULL);
v___x_2594_ = lean_usize_of_nat(v___x_2590_);
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2588_, v_query_2587_, v___x_2593_, v___x_2594_, v___x_2591_);
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded___boxed(lean_object* v_query_2596_, lean_object* v_key_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Std_Http_URI_Query_eraseEncoded(v_query_2596_, v_key_2597_);
lean_dec_ref(v_key_2597_);
lean_dec_ref(v_query_2596_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_erase_spec__0(lean_object* v_key_2599_, lean_object* v_as_2600_, size_t v_i_2601_, size_t v_stop_2602_, lean_object* v_b_2603_){
_start:
{
lean_object* v___y_2605_; uint8_t v___x_2609_; 
v___x_2609_ = lean_usize_dec_eq(v_i_2601_, v_stop_2602_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; lean_object* v_fst_2611_; uint8_t v___x_2612_; 
v___x_2610_ = lean_array_uget_borrowed(v_as_2600_, v_i_2601_);
v_fst_2611_ = lean_ctor_get(v___x_2610_, 0);
v___x_2612_ = l_Std_Http_URI_EncodedQueryString_decodesTo___redArg(v_fst_2611_, v_key_2599_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; 
lean_inc(v___x_2610_);
v___x_2613_ = lean_array_push(v_b_2603_, v___x_2610_);
v___y_2605_ = v___x_2613_;
goto v___jp_2604_;
}
else
{
v___y_2605_ = v_b_2603_;
goto v___jp_2604_;
}
}
else
{
return v_b_2603_;
}
v___jp_2604_:
{
size_t v___x_2606_; size_t v___x_2607_; 
v___x_2606_ = ((size_t)1ULL);
v___x_2607_ = lean_usize_add(v_i_2601_, v___x_2606_);
v_i_2601_ = v___x_2607_;
v_b_2603_ = v___y_2605_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_erase_spec__0___boxed(lean_object* v_key_2614_, lean_object* v_as_2615_, lean_object* v_i_2616_, lean_object* v_stop_2617_, lean_object* v_b_2618_){
_start:
{
size_t v_i_boxed_2619_; size_t v_stop_boxed_2620_; lean_object* v_res_2621_; 
v_i_boxed_2619_ = lean_unbox_usize(v_i_2616_);
lean_dec(v_i_2616_);
v_stop_boxed_2620_ = lean_unbox_usize(v_stop_2617_);
lean_dec(v_stop_2617_);
v_res_2621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_erase_spec__0(v_key_2614_, v_as_2615_, v_i_boxed_2619_, v_stop_boxed_2620_, v_b_2618_);
lean_dec_ref(v_as_2615_);
lean_dec_ref(v_key_2614_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase(lean_object* v_query_2622_, lean_object* v_key_2623_){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; uint8_t v___x_2627_; 
v___x_2624_ = lean_unsigned_to_nat(0u);
v___x_2625_ = lean_array_get_size(v_query_2622_);
v___x_2626_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_2627_ = lean_nat_dec_lt(v___x_2624_, v___x_2625_);
if (v___x_2627_ == 0)
{
return v___x_2626_;
}
else
{
size_t v___x_2628_; size_t v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = ((size_t)0ULL);
v___x_2629_ = lean_usize_of_nat(v___x_2625_);
v___x_2630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_erase_spec__0(v_key_2623_, v_query_2622_, v___x_2628_, v___x_2629_, v___x_2626_);
return v___x_2630_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase___boxed(lean_object* v_query_2631_, lean_object* v_key_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Std_Http_URI_Query_erase(v_query_2631_, v_key_2632_);
lean_dec_ref(v_key_2632_);
lean_dec_ref(v_query_2631_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get(lean_object* v_query_2636_, lean_object* v_key_2637_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Std_Http_URI_Query_find_x3f(v_query_2636_, v_key_2637_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_box(0);
return v___x_2639_;
}
else
{
lean_object* v_val_2640_; 
v_val_2640_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_val_2640_);
lean_dec_ref_known(v___x_2638_, 1);
if (lean_obj_tag(v_val_2640_) == 0)
{
lean_object* v___x_2641_; 
v___x_2641_ = ((lean_object*)(l_Std_Http_URI_Query_get___closed__0));
return v___x_2641_;
}
else
{
lean_object* v_val_2642_; lean_object* v___x_2643_; 
v_val_2642_ = lean_ctor_get(v_val_2640_, 0);
lean_inc(v_val_2642_);
lean_dec_ref_known(v_val_2640_, 1);
v___x_2643_ = l_Std_Http_URI_EncodedQueryParam_decode(v_val_2642_);
lean_dec(v_val_2642_);
return v___x_2643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get___boxed(lean_object* v_query_2644_, lean_object* v_key_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Std_Http_URI_Query_get(v_query_2644_, v_key_2645_);
lean_dec_ref(v_key_2645_);
lean_dec_ref(v_query_2644_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD(lean_object* v_query_2647_, lean_object* v_key_2648_, lean_object* v_default_2649_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Std_Http_URI_Query_get(v_query_2647_, v_key_2648_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_inc_ref(v_default_2649_);
return v_default_2649_;
}
else
{
lean_object* v_val_2651_; 
v_val_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_val_2651_);
lean_dec_ref_known(v___x_2650_, 1);
return v_val_2651_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD___boxed(lean_object* v_query_2652_, lean_object* v_key_2653_, lean_object* v_default_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Std_Http_URI_Query_getD(v_query_2652_, v_key_2653_, v_default_2654_);
lean_dec_ref(v_default_2654_);
lean_dec_ref(v_key_2653_);
lean_dec_ref(v_query_2652_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set(lean_object* v_query_2656_, lean_object* v_key_2657_, lean_object* v_value_2658_){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = l_Std_Http_URI_Query_erase(v_query_2656_, v_key_2657_);
v___x_2660_ = l_Std_Http_URI_Query_insert(v___x_2659_, v_key_2657_, v_value_2658_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set___boxed(lean_object* v_query_2661_, lean_object* v_key_2662_, lean_object* v_value_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Std_Http_URI_Query_set(v_query_2661_, v_key_2662_, v_value_2663_);
lean_dec_ref(v_query_2661_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(size_t v_sz_2665_, size_t v_i_2666_, lean_object* v_bs_2667_){
_start:
{
uint8_t v___x_2668_; 
v___x_2668_ = lean_usize_dec_lt(v_i_2666_, v_sz_2665_);
if (v___x_2668_ == 0)
{
return v_bs_2667_;
}
else
{
lean_object* v_v_2669_; lean_object* v_fst_2670_; lean_object* v_snd_2671_; lean_object* v___x_2672_; lean_object* v_bs_x27_2673_; lean_object* v___x_2674_; size_t v___x_2675_; size_t v___x_2676_; lean_object* v___x_2677_; 
v_v_2669_ = lean_array_uget_borrowed(v_bs_2667_, v_i_2666_);
v_fst_2670_ = lean_ctor_get(v_v_2669_, 0);
lean_inc(v_fst_2670_);
v_snd_2671_ = lean_ctor_get(v_v_2669_, 1);
lean_inc(v_snd_2671_);
v___x_2672_ = lean_unsigned_to_nat(0u);
v_bs_x27_2673_ = lean_array_uset(v_bs_2667_, v_i_2666_, v___x_2672_);
v___x_2674_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2670_, v_snd_2671_);
v___x_2675_ = ((size_t)1ULL);
v___x_2676_ = lean_usize_add(v_i_2666_, v___x_2675_);
v___x_2677_ = lean_array_uset(v_bs_x27_2673_, v_i_2666_, v___x_2674_);
v_i_2666_ = v___x_2676_;
v_bs_2667_ = v___x_2677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0___boxed(lean_object* v_sz_2679_, lean_object* v_i_2680_, lean_object* v_bs_2681_){
_start:
{
size_t v_sz_boxed_2682_; size_t v_i_boxed_2683_; lean_object* v_res_2684_; 
v_sz_boxed_2682_ = lean_unbox_usize(v_sz_2679_);
lean_dec(v_sz_2679_);
v_i_boxed_2683_ = lean_unbox_usize(v_i_2680_);
lean_dec(v_i_2680_);
v_res_2684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_boxed_2682_, v_i_boxed_2683_, v_bs_2681_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toRawString(lean_object* v_query_2686_){
_start:
{
size_t v_sz_2687_; size_t v___x_2688_; lean_object* v_params_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_sz_2687_ = lean_array_size(v_query_2686_);
v___x_2688_ = ((size_t)0ULL);
v_params_2689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_2687_, v___x_2688_, v_query_2686_);
v___x_2690_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2691_ = lean_array_to_list(v_params_2689_);
v___x_2692_ = l_String_intercalate(v___x_2690_, v___x_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0(lean_object* v_x_2694_){
_start:
{
lean_object* v_fst_2695_; lean_object* v_snd_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_fst_2695_ = lean_ctor_get(v_x_2694_, 0);
lean_inc(v_fst_2695_);
v_snd_2696_ = lean_ctor_get(v_x_2694_, 1);
lean_inc(v_snd_2696_);
lean_dec_ref(v_x_2694_);
v___x_2697_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
v___x_2698_ = l_Std_Http_URI_Query_insert(v___x_2697_, v_fst_2695_, v_snd_2696_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0(lean_object* v_x_2701_, lean_object* v_q_2702_){
_start:
{
lean_object* v_fst_2703_; lean_object* v_snd_2704_; lean_object* v___x_2705_; 
v_fst_2703_ = lean_ctor_get(v_x_2701_, 0);
lean_inc(v_fst_2703_);
v_snd_2704_ = lean_ctor_get(v_x_2701_, 1);
lean_inc(v_snd_2704_);
lean_dec_ref(v_x_2701_);
v___x_2705_ = l_Std_Http_URI_Query_insert(v_q_2702_, v_fst_2703_, v_snd_2704_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__0(lean_object* v_x_2708_){
_start:
{
lean_object* v_fst_2709_; lean_object* v_snd_2710_; lean_object* v___x_2711_; 
v_fst_2709_ = lean_ctor_get(v_x_2708_, 0);
lean_inc(v_fst_2709_);
v_snd_2710_ = lean_ctor_get(v_x_2708_, 1);
lean_inc(v_snd_2710_);
lean_dec_ref(v_x_2708_);
v___x_2711_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2709_, v_snd_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__1(lean_object* v___f_2713_, lean_object* v_q_2714_){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; uint8_t v___x_2717_; 
v___x_2715_ = lean_array_get_size(v_q_2714_);
v___x_2716_ = lean_unsigned_to_nat(0u);
v___x_2717_ = lean_nat_dec_eq(v___x_2715_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v_encodedParams_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2718_ = lean_array_to_list(v_q_2714_);
v___x_2719_ = lean_box(0);
v_encodedParams_2720_ = l_List_mapTR_loop___redArg(v___f_2713_, v___x_2718_, v___x_2719_);
v___x_2721_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2722_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2723_ = l_String_intercalate(v___x_2722_, v_encodedParams_2720_);
v___x_2724_ = lean_string_append(v___x_2721_, v___x_2723_);
lean_dec_ref(v___x_2723_);
return v___x_2724_;
}
else
{
lean_object* v___x_2725_; 
lean_dec_ref(v_q_2714_);
lean_dec_ref(v___f_2713_);
v___x_2725_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
return v___x_2725_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(lean_object* v_a_2730_, lean_object* v_a_2731_){
_start:
{
if (lean_obj_tag(v_a_2730_) == 0)
{
lean_object* v___x_2732_; 
v___x_2732_ = l_List_reverse___redArg(v_a_2731_);
return v___x_2732_;
}
else
{
lean_object* v_head_2733_; lean_object* v_tail_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2745_; 
v_head_2733_ = lean_ctor_get(v_a_2730_, 0);
v_tail_2734_ = lean_ctor_get(v_a_2730_, 1);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_a_2730_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2736_ = v_a_2730_;
v_isShared_2737_ = v_isSharedCheck_2745_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_tail_2734_);
lean_inc(v_head_2733_);
lean_dec(v_a_2730_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2745_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v_fst_2738_; lean_object* v_snd_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
v_fst_2738_ = lean_ctor_get(v_head_2733_, 0);
lean_inc(v_fst_2738_);
v_snd_2739_ = lean_ctor_get(v_head_2733_, 1);
lean_inc(v_snd_2739_);
lean_dec(v_head_2733_);
v___x_2740_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2738_, v_snd_2739_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 1, v_a_2731_);
lean_ctor_set(v___x_2736_, 0, v___x_2740_);
v___x_2742_ = v___x_2736_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2740_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_a_2731_);
v___x_2742_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
v_a_2730_ = v_tail_2734_;
v_a_2731_ = v___x_2742_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatOption(lean_object* v_x_2746_){
_start:
{
if (lean_obj_tag(v_x_2746_) == 0)
{
lean_object* v___x_2747_; 
v___x_2747_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
return v___x_2747_;
}
else
{
lean_object* v_val_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v_val_2748_ = lean_ctor_get(v_x_2746_, 0);
lean_inc(v_val_2748_);
lean_dec_ref_known(v_x_2746_, 1);
v___x_2749_ = lean_array_get_size(v_val_2748_);
v___x_2750_ = lean_unsigned_to_nat(0u);
v___x_2751_ = lean_nat_dec_eq(v___x_2749_, v___x_2750_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v_encodedParams_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2752_ = lean_array_to_list(v_val_2748_);
v___x_2753_ = lean_box(0);
v_encodedParams_2754_ = l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(v___x_2752_, v___x_2753_);
v___x_2755_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2756_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2757_ = l_String_intercalate(v___x_2756_, v_encodedParams_2754_);
v___x_2758_ = lean_string_append(v___x_2755_, v___x_2757_);
lean_dec_ref(v___x_2757_);
return v___x_2758_;
}
else
{
lean_object* v___x_2759_; 
lean_dec(v_val_2748_);
v___x_2759_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
return v___x_2759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(lean_object* v_x_2760_, lean_object* v_x_2761_){
_start:
{
if (lean_obj_tag(v_x_2760_) == 0)
{
lean_object* v___x_2762_; 
v___x_2762_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2762_;
}
else
{
lean_object* v_val_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_val_2763_ = lean_ctor_get(v_x_2760_, 0);
lean_inc(v_val_2763_);
lean_dec_ref_known(v_x_2760_, 1);
v___x_2764_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2765_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_val_2763_);
v___x_2766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2764_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = l_Repr_addAppParen(v___x_2766_, v_x_2761_);
return v___x_2767_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(lean_object* v_x_2768_, lean_object* v_x_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_x_2768_, v_x_2769_);
lean_dec(v_x_2769_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object* v_x_2771_, lean_object* v_x_2772_){
_start:
{
if (lean_obj_tag(v_x_2771_) == 0)
{
lean_object* v___x_2773_; 
v___x_2773_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2773_;
}
else
{
lean_object* v_val_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_val_2774_ = lean_ctor_get(v_x_2771_, 0);
lean_inc(v_val_2774_);
lean_dec_ref_known(v_x_2771_, 1);
v___x_2775_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2776_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_val_2774_);
v___x_2777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2775_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
v___x_2778_ = l_Repr_addAppParen(v___x_2777_, v_x_2772_);
return v___x_2778_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1___boxed(lean_object* v_x_2779_, lean_object* v_x_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_x_2779_, v_x_2780_);
lean_dec(v_x_2780_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(lean_object* v_x_2782_, lean_object* v_x_2783_){
_start:
{
if (lean_obj_tag(v_x_2782_) == 0)
{
lean_object* v___x_2784_; 
v___x_2784_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2784_;
}
else
{
lean_object* v_val_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2796_; 
v_val_2785_ = lean_ctor_get(v_x_2782_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_x_2782_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2787_ = v_x_2782_;
v_isShared_2788_ = v_isSharedCheck_2796_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_val_2785_);
lean_dec(v_x_2782_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2796_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2792_; 
v___x_2789_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2790_ = l_String_quote(v_val_2785_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set_tag(v___x_2787_, 3);
lean_ctor_set(v___x_2787_, 0, v___x_2790_);
v___x_2792_ = v___x_2787_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2790_);
v___x_2792_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2789_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = l_Repr_addAppParen(v___x_2793_, v_x_2783_);
return v___x_2794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2___boxed(lean_object* v_x_2797_, lean_object* v_x_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_x_2797_, v_x_2798_);
lean_dec(v_x_2798_);
return v_res_2799_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = lean_unsigned_to_nat(10u);
v___x_2810_ = lean_nat_to_int(v___x_2809_);
return v___x_2810_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = lean_unsigned_to_nat(13u);
v___x_2815_ = lean_nat_to_int(v___x_2814_);
return v___x_2815_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = lean_unsigned_to_nat(9u);
v___x_2823_ = lean_nat_to_int(v___x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___redArg(lean_object* v_x_2827_){
_start:
{
lean_object* v_scheme_2828_; lean_object* v_authority_2829_; lean_object* v_path_2830_; lean_object* v_query_2831_; lean_object* v_fragment_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; uint8_t v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_scheme_2828_ = lean_ctor_get(v_x_2827_, 0);
lean_inc_ref(v_scheme_2828_);
v_authority_2829_ = lean_ctor_get(v_x_2827_, 1);
lean_inc(v_authority_2829_);
v_path_2830_ = lean_ctor_get(v_x_2827_, 2);
lean_inc_ref(v_path_2830_);
v_query_2831_ = lean_ctor_get(v_x_2827_, 3);
lean_inc(v_query_2831_);
v_fragment_2832_ = lean_ctor_get(v_x_2827_, 4);
lean_inc(v_fragment_2832_);
lean_dec_ref(v_x_2827_);
v___x_2833_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2834_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2835_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2836_ = l_String_quote(v_scheme_2828_);
v___x_2837_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
v___x_2838_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2835_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = 0;
v___x_2840_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2840_, 0, v___x_2838_);
lean_ctor_set_uint8(v___x_2840_, sizeof(void*)*1, v___x_2839_);
v___x_2841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2834_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2841_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
v___x_2844_ = lean_box(1);
v___x_2845_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2843_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
v___x_2846_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__6));
v___x_2847_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2845_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
v___x_2848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
lean_ctor_set(v___x_2848_, 1, v___x_2833_);
v___x_2849_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_2850_ = lean_unsigned_to_nat(0u);
v___x_2851_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_2829_, v___x_2850_);
v___x_2852_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2849_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
v___x_2853_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
lean_ctor_set_uint8(v___x_2853_, sizeof(void*)*1, v___x_2839_);
v___x_2854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2848_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v___x_2842_);
v___x_2856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
lean_ctor_set(v___x_2856_, 1, v___x_2844_);
v___x_2857_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_2858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2856_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
lean_ctor_set(v___x_2859_, 1, v___x_2833_);
v___x_2860_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2861_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_2830_);
v___x_2862_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2863_, 0, v___x_2862_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*1, v___x_2839_);
v___x_2864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2859_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
lean_ctor_set(v___x_2865_, 1, v___x_2842_);
v___x_2866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
lean_ctor_set(v___x_2866_, 1, v___x_2844_);
v___x_2867_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_2868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
lean_ctor_set(v___x_2869_, 1, v___x_2833_);
v___x_2870_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_2871_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_2831_, v___x_2850_);
v___x_2872_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2870_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
lean_ctor_set_uint8(v___x_2873_, sizeof(void*)*1, v___x_2839_);
v___x_2874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2869_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2874_);
lean_ctor_set(v___x_2875_, 1, v___x_2842_);
v___x_2876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set(v___x_2876_, 1, v___x_2844_);
v___x_2877_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_2878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2876_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
v___x_2879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
lean_ctor_set(v___x_2879_, 1, v___x_2833_);
v___x_2880_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_2881_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_2832_, v___x_2850_);
v___x_2882_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2880_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
v___x_2883_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2883_, 0, v___x_2882_);
lean_ctor_set_uint8(v___x_2883_, sizeof(void*)*1, v___x_2839_);
v___x_2884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2879_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2886_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
lean_ctor_set(v___x_2887_, 1, v___x_2884_);
v___x_2888_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2887_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2885_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
v___x_2891_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
lean_ctor_set_uint8(v___x_2891_, sizeof(void*)*1, v___x_2839_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr(lean_object* v_x_2892_, lean_object* v_prec_2893_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Std_Http_instReprURI_repr___redArg(v_x_2892_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___boxed(lean_object* v_x_2895_, lean_object* v_prec_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Std_Http_instReprURI_repr(v_x_2895_, v_prec_2896_);
lean_dec(v_prec_2896_);
return v_res_2897_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object* v_x_2906_, lean_object* v_x_2907_){
_start:
{
if (lean_obj_tag(v_x_2906_) == 0)
{
if (lean_obj_tag(v_x_2907_) == 0)
{
uint8_t v___x_2908_; 
v___x_2908_ = 1;
return v___x_2908_;
}
else
{
uint8_t v___x_2909_; 
v___x_2909_ = 0;
return v___x_2909_;
}
}
else
{
if (lean_obj_tag(v_x_2907_) == 0)
{
uint8_t v___x_2910_; 
v___x_2910_ = 0;
return v___x_2910_;
}
else
{
lean_object* v_val_2911_; lean_object* v_val_2912_; uint8_t v___x_2913_; 
v_val_2911_ = lean_ctor_get(v_x_2906_, 0);
v_val_2912_ = lean_ctor_get(v_x_2907_, 0);
v___x_2913_ = l_Std_Http_URI_instBEqAuthority_beq(v_val_2911_, v_val_2912_);
return v___x_2913_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object* v_x_2914_, lean_object* v_x_2915_){
_start:
{
uint8_t v_res_2916_; lean_object* v_r_2917_; 
v_res_2916_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_x_2914_, v_x_2915_);
lean_dec(v_x_2915_);
lean_dec(v_x_2914_);
v_r_2917_ = lean_box(v_res_2916_);
return v_r_2917_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object* v_x_2918_, lean_object* v_x_2919_){
_start:
{
if (lean_obj_tag(v_x_2918_) == 0)
{
if (lean_obj_tag(v_x_2919_) == 0)
{
uint8_t v___x_2920_; 
v___x_2920_ = 1;
return v___x_2920_;
}
else
{
uint8_t v___x_2921_; 
v___x_2921_ = 0;
return v___x_2921_;
}
}
else
{
if (lean_obj_tag(v_x_2919_) == 0)
{
uint8_t v___x_2922_; 
v___x_2922_ = 0;
return v___x_2922_;
}
else
{
lean_object* v_val_2923_; lean_object* v_val_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; 
v_val_2923_ = lean_ctor_get(v_x_2918_, 0);
v_val_2924_ = lean_ctor_get(v_x_2919_, 0);
v___x_2925_ = lean_array_get_size(v_val_2923_);
v___x_2926_ = lean_array_get_size(v_val_2924_);
v___x_2927_ = lean_nat_dec_eq(v___x_2925_, v___x_2926_);
if (v___x_2927_ == 0)
{
return v___x_2927_;
}
else
{
uint8_t v___x_2928_; 
v___x_2928_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_val_2923_, v_val_2924_, v___x_2925_);
return v___x_2928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object* v_x_2929_, lean_object* v_x_2930_){
_start:
{
uint8_t v_res_2931_; lean_object* v_r_2932_; 
v_res_2931_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_x_2929_, v_x_2930_);
lean_dec(v_x_2930_);
lean_dec(v_x_2929_);
v_r_2932_ = lean_box(v_res_2931_);
return v_r_2932_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(lean_object* v_x_2933_, lean_object* v_x_2934_){
_start:
{
if (lean_obj_tag(v_x_2933_) == 0)
{
if (lean_obj_tag(v_x_2934_) == 0)
{
uint8_t v___x_2935_; 
v___x_2935_ = 1;
return v___x_2935_;
}
else
{
uint8_t v___x_2936_; 
v___x_2936_ = 0;
return v___x_2936_;
}
}
else
{
if (lean_obj_tag(v_x_2934_) == 0)
{
uint8_t v___x_2937_; 
v___x_2937_ = 0;
return v___x_2937_;
}
else
{
lean_object* v_val_2938_; lean_object* v_val_2939_; uint8_t v___x_2940_; 
v_val_2938_ = lean_ctor_get(v_x_2933_, 0);
v_val_2939_ = lean_ctor_get(v_x_2934_, 0);
v___x_2940_ = lean_string_dec_eq(v_val_2938_, v_val_2939_);
return v___x_2940_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2___boxed(lean_object* v_x_2941_, lean_object* v_x_2942_){
_start:
{
uint8_t v_res_2943_; lean_object* v_r_2944_; 
v_res_2943_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_x_2941_, v_x_2942_);
lean_dec(v_x_2942_);
lean_dec(v_x_2941_);
v_r_2944_ = lean_box(v_res_2943_);
return v_r_2944_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object* v_x_2945_, lean_object* v_x_2946_){
_start:
{
lean_object* v_scheme_2947_; lean_object* v_authority_2948_; lean_object* v_path_2949_; lean_object* v_query_2950_; lean_object* v_fragment_2951_; lean_object* v_scheme_2952_; lean_object* v_authority_2953_; lean_object* v_path_2954_; lean_object* v_query_2955_; lean_object* v_fragment_2956_; uint8_t v___x_2957_; 
v_scheme_2947_ = lean_ctor_get(v_x_2945_, 0);
v_authority_2948_ = lean_ctor_get(v_x_2945_, 1);
v_path_2949_ = lean_ctor_get(v_x_2945_, 2);
v_query_2950_ = lean_ctor_get(v_x_2945_, 3);
v_fragment_2951_ = lean_ctor_get(v_x_2945_, 4);
v_scheme_2952_ = lean_ctor_get(v_x_2946_, 0);
v_authority_2953_ = lean_ctor_get(v_x_2946_, 1);
v_path_2954_ = lean_ctor_get(v_x_2946_, 2);
v_query_2955_ = lean_ctor_get(v_x_2946_, 3);
v_fragment_2956_ = lean_ctor_get(v_x_2946_, 4);
v___x_2957_ = lean_string_dec_eq(v_scheme_2947_, v_scheme_2952_);
if (v___x_2957_ == 0)
{
return v___x_2957_;
}
else
{
uint8_t v___x_2958_; 
v___x_2958_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_2948_, v_authority_2953_);
if (v___x_2958_ == 0)
{
return v___x_2958_;
}
else
{
uint8_t v___x_2959_; 
v___x_2959_ = l_Std_Http_URI_instBEqPath_beq(v_path_2949_, v_path_2954_);
if (v___x_2959_ == 0)
{
return v___x_2959_;
}
else
{
uint8_t v___x_2960_; 
v___x_2960_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_2950_, v_query_2955_);
if (v___x_2960_ == 0)
{
return v___x_2960_;
}
else
{
uint8_t v___x_2961_; 
v___x_2961_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_2951_, v_fragment_2956_);
return v___x_2961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object* v_x_2962_, lean_object* v_x_2963_){
_start:
{
uint8_t v_res_2964_; lean_object* v_r_2965_; 
v_res_2964_ = l_Std_Http_instBEqURI_beq(v_x_2962_, v_x_2963_);
lean_dec_ref(v_x_2963_);
lean_dec_ref(v_x_2962_);
v_r_2965_ = lean_box(v_res_2964_);
return v_r_2965_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__0(lean_object* v_uri_2970_){
_start:
{
lean_object* v_scheme_2971_; lean_object* v_authority_2972_; lean_object* v_path_2973_; lean_object* v_query_2974_; lean_object* v_fragment_2975_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2988_; uint8_t v___y_2989_; lean_object* v___y_3000_; 
v_scheme_2971_ = lean_ctor_get(v_uri_2970_, 0);
lean_inc_ref(v_scheme_2971_);
v_authority_2972_ = lean_ctor_get(v_uri_2970_, 1);
lean_inc(v_authority_2972_);
v_path_2973_ = lean_ctor_get(v_uri_2970_, 2);
lean_inc_ref(v_path_2973_);
v_query_2974_ = lean_ctor_get(v_uri_2970_, 3);
lean_inc(v_query_2974_);
v_fragment_2975_ = lean_ctor_get(v_uri_2970_, 4);
lean_inc(v_fragment_2975_);
lean_dec_ref(v_uri_2970_);
if (lean_obj_tag(v_authority_2972_) == 0)
{
lean_object* v___x_3003_; 
v___x_3003_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_3000_ = v___x_3003_;
goto v___jp_2999_;
}
else
{
lean_object* v_val_3004_; lean_object* v_userInfo_3005_; lean_object* v_host_3006_; lean_object* v_port_3007_; lean_object* v___x_3008_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3027_; 
v_val_3004_ = lean_ctor_get(v_authority_2972_, 0);
v_userInfo_3005_ = lean_ctor_get(v_val_3004_, 0);
v_host_3006_ = lean_ctor_get(v_val_3004_, 1);
v_port_3007_ = lean_ctor_get(v_val_3004_, 2);
v___x_3008_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__1));
if (lean_obj_tag(v_userInfo_3005_) == 0)
{
lean_object* v___x_3038_; 
v___x_3038_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_3027_ = v___x_3038_;
goto v___jp_3026_;
}
else
{
lean_object* v_val_3039_; lean_object* v_password_3040_; 
v_val_3039_ = lean_ctor_get(v_userInfo_3005_, 0);
v_password_3040_ = lean_ctor_get(v_val_3039_, 1);
if (lean_obj_tag(v_password_3040_) == 0)
{
lean_object* v_username_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v_username_3041_ = lean_ctor_get(v_val_3039_, 0);
lean_inc_ref(v_username_3041_);
v___x_3042_ = lean_string_from_utf8_unchecked(v_username_3041_);
v___x_3043_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3044_ = lean_string_append(v___x_3042_, v___x_3043_);
v___y_3027_ = v___x_3044_;
goto v___jp_3026_;
}
else
{
lean_object* v_username_3045_; lean_object* v_val_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v_username_3045_ = lean_ctor_get(v_val_3039_, 0);
v_val_3046_ = lean_ctor_get(v_password_3040_, 0);
lean_inc_ref(v_username_3045_);
v___x_3047_ = lean_string_from_utf8_unchecked(v_username_3045_);
v___x_3048_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_3049_ = lean_string_append(v___x_3047_, v___x_3048_);
lean_inc(v_val_3046_);
v___x_3050_ = lean_string_from_utf8_unchecked(v_val_3046_);
v___x_3051_ = lean_string_append(v___x_3049_, v___x_3050_);
lean_dec_ref(v___x_3050_);
v___x_3052_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3053_ = lean_string_append(v___x_3051_, v___x_3052_);
v___y_3027_ = v___x_3053_;
goto v___jp_3026_;
}
}
v___jp_3009_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_string_append(v___y_3010_, v___y_3011_);
lean_dec_ref(v___y_3011_);
v___x_3014_ = lean_string_append(v___x_3013_, v___y_3012_);
lean_dec_ref(v___y_3012_);
v___x_3015_ = lean_string_append(v___x_3008_, v___x_3014_);
lean_dec_ref(v___x_3014_);
v___y_3000_ = v___x_3015_;
goto v___jp_2999_;
}
v___jp_3016_:
{
switch(lean_obj_tag(v_port_3007_))
{
case 0:
{
lean_object* v___x_3019_; 
v___x_3019_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_3010_ = v___y_3017_;
v___y_3011_ = v___y_3018_;
v___y_3012_ = v___x_3019_;
goto v___jp_3009_;
}
case 1:
{
lean_object* v___x_3020_; 
v___x_3020_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3010_ = v___y_3017_;
v___y_3011_ = v___y_3018_;
v___y_3012_ = v___x_3020_;
goto v___jp_3009_;
}
default: 
{
uint16_t v_port_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v_port_3021_ = lean_ctor_get_uint16(v_port_3007_, 0);
v___x_3022_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_3023_ = lean_uint16_to_nat(v_port_3021_);
v___x_3024_ = l_Nat_reprFast(v___x_3023_);
v___x_3025_ = lean_string_append(v___x_3022_, v___x_3024_);
lean_dec_ref(v___x_3024_);
v___y_3010_ = v___y_3017_;
v___y_3011_ = v___y_3018_;
v___y_3012_ = v___x_3025_;
goto v___jp_3009_;
}
}
}
v___jp_3026_:
{
switch(lean_obj_tag(v_host_3006_))
{
case 0:
{
lean_object* v_name_3028_; 
v_name_3028_ = lean_ctor_get(v_host_3006_, 0);
lean_inc_ref(v_name_3028_);
v___y_3017_ = v___y_3027_;
v___y_3018_ = v_name_3028_;
goto v___jp_3016_;
}
case 1:
{
lean_object* v_ipv4_3029_; lean_object* v___x_3030_; 
v_ipv4_3029_ = lean_ctor_get(v_host_3006_, 0);
v___x_3030_ = lean_uv_ntop_v4(v_ipv4_3029_);
v___y_3017_ = v___y_3027_;
v___y_3018_ = v___x_3030_;
goto v___jp_3016_;
}
case 2:
{
lean_object* v_ipv6_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v_ipv6_3031_ = lean_ctor_get(v_host_3006_, 0);
v___x_3032_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3033_ = lean_uv_ntop_v6(v_ipv6_3031_);
v___x_3034_ = lean_string_append(v___x_3032_, v___x_3033_);
lean_dec_ref(v___x_3033_);
v___x_3035_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3036_ = lean_string_append(v___x_3034_, v___x_3035_);
v___y_3017_ = v___y_3027_;
v___y_3018_ = v___x_3036_;
goto v___jp_3016_;
}
default: 
{
lean_object* v___x_3037_; 
v___x_3037_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_3017_ = v___y_3027_;
v___y_3018_ = v___x_3037_;
goto v___jp_3016_;
}
}
}
}
v___jp_2976_:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2981_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_2982_ = lean_string_append(v_scheme_2971_, v___x_2981_);
v___x_2983_ = lean_string_append(v___x_2982_, v___y_2979_);
lean_dec_ref(v___y_2979_);
v___x_2984_ = lean_string_append(v___x_2983_, v___y_2978_);
lean_dec_ref(v___y_2978_);
v___x_2985_ = lean_string_append(v___x_2984_, v___y_2977_);
lean_dec_ref(v___y_2977_);
v___x_2986_ = lean_string_append(v___x_2985_, v___y_2980_);
lean_dec_ref(v___y_2980_);
return v___x_2986_;
}
v___jp_2987_:
{
uint8_t v___x_2990_; lean_object* v_pathPart_2991_; lean_object* v_queryPart_2992_; 
v___x_2990_ = 1;
v_pathPart_2991_ = l_Std_Http_URI_Path_render(v_path_2973_, v___y_2989_, v___x_2990_);
v_queryPart_2992_ = l_Std_Http_URI_Query_formatOption(v_query_2974_);
if (lean_obj_tag(v_fragment_2975_) == 0)
{
lean_object* v___x_2993_; 
v___x_2993_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_2977_ = v_queryPart_2992_;
v___y_2978_ = v_pathPart_2991_;
v___y_2979_ = v___y_2988_;
v___y_2980_ = v___x_2993_;
goto v___jp_2976_;
}
else
{
lean_object* v_val_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v_val_2994_ = lean_ctor_get(v_fragment_2975_, 0);
lean_inc(v_val_2994_);
lean_dec_ref_known(v_fragment_2975_, 1);
v___x_2995_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__0));
v___x_2996_ = l_Std_Http_URI_EncodedFragment_encode(v_val_2994_);
v___x_2997_ = lean_string_from_utf8_unchecked(v___x_2996_);
v___x_2998_ = lean_string_append(v___x_2995_, v___x_2997_);
lean_dec_ref(v___x_2997_);
v___y_2977_ = v_queryPart_2992_;
v___y_2978_ = v_pathPart_2991_;
v___y_2979_ = v___y_2988_;
v___y_2980_ = v___x_2998_;
goto v___jp_2976_;
}
}
v___jp_2999_:
{
if (lean_obj_tag(v_authority_2972_) == 0)
{
uint8_t v___x_3001_; 
v___x_3001_ = 0;
v___y_2988_ = v___y_3000_;
v___y_2989_ = v___x_3001_;
goto v___jp_2987_;
}
else
{
uint8_t v___x_3002_; 
lean_dec_ref_known(v_authority_2972_, 1);
v___x_3002_ = 1;
v___y_2988_ = v___y_3000_;
v___y_2989_ = v___x_3002_;
goto v___jp_2987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x3f(lean_object* v_b_3065_, lean_object* v_scheme_3066_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l_Std_Http_URI_Scheme_ofString_x3f(v_scheme_3066_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v___x_3068_; 
lean_dec_ref(v_b_3065_);
v___x_3068_ = lean_box(0);
return v___x_3068_;
}
else
{
lean_object* v_userInfo_3069_; lean_object* v_host_3070_; lean_object* v_port_3071_; lean_object* v_pathSegments_3072_; lean_object* v_query_3073_; lean_object* v_fragment_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3089_; 
v_userInfo_3069_ = lean_ctor_get(v_b_3065_, 1);
v_host_3070_ = lean_ctor_get(v_b_3065_, 2);
v_port_3071_ = lean_ctor_get(v_b_3065_, 3);
v_pathSegments_3072_ = lean_ctor_get(v_b_3065_, 4);
v_query_3073_ = lean_ctor_get(v_b_3065_, 5);
v_fragment_3074_ = lean_ctor_get(v_b_3065_, 6);
v_isSharedCheck_3089_ = !lean_is_exclusive(v_b_3065_);
if (v_isSharedCheck_3089_ == 0)
{
lean_object* v_unused_3090_; 
v_unused_3090_ = lean_ctor_get(v_b_3065_, 0);
lean_dec(v_unused_3090_);
v___x_3076_ = v_b_3065_;
v_isShared_3077_ = v_isSharedCheck_3089_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_fragment_3074_);
lean_inc(v_query_3073_);
lean_inc(v_pathSegments_3072_);
lean_inc(v_port_3071_);
lean_inc(v_host_3070_);
lean_inc(v_userInfo_3069_);
lean_dec(v_b_3065_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3089_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
lean_inc_ref(v___x_3067_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 0, v___x_3067_);
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3067_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_userInfo_3069_);
lean_ctor_set(v_reuseFailAlloc_3088_, 2, v_host_3070_);
lean_ctor_set(v_reuseFailAlloc_3088_, 3, v_port_3071_);
lean_ctor_set(v_reuseFailAlloc_3088_, 4, v_pathSegments_3072_);
lean_ctor_set(v_reuseFailAlloc_3088_, 5, v_query_3073_);
lean_ctor_set(v_reuseFailAlloc_3088_, 6, v_fragment_3074_);
v___x_3079_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3086_ == 0)
{
lean_object* v_unused_3087_; 
v_unused_3087_ = lean_ctor_get(v___x_3067_, 0);
lean_dec(v_unused_3087_);
v___x_3081_ = v___x_3067_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_dec(v___x_3067_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 0, v___x_3079_);
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(lean_object* v_msg_3091_){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = ((lean_object*)(l_Std_Http_URI_instInhabitedBuilder_default));
v___x_3093_ = lean_panic_fn_borrowed(v___x_3092_, v_msg_3091_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x21(lean_object* v_b_3095_, lean_object* v_scheme_3096_){
_start:
{
lean_object* v___x_3097_; 
lean_inc_ref(v_scheme_3096_);
v___x_3097_ = l_Std_Http_URI_Builder_setScheme_x3f(v_b_3095_, v_scheme_3096_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3098_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_3099_ = ((lean_object*)(l_Std_Http_URI_Builder_setScheme_x21___closed__0));
v___x_3100_ = lean_unsigned_to_nat(757u);
v___x_3101_ = lean_unsigned_to_nat(14u);
v___x_3102_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_3103_ = l_String_quote(v_scheme_3096_);
v___x_3104_ = lean_string_append(v___x_3102_, v___x_3103_);
lean_dec_ref(v___x_3103_);
v___x_3105_ = l_mkPanicMessageWithDecl(v___x_3098_, v___x_3099_, v___x_3100_, v___x_3101_, v___x_3104_);
lean_dec_ref(v___x_3104_);
v___x_3106_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_3105_);
return v___x_3106_;
}
else
{
lean_object* v_val_3107_; 
lean_dec_ref(v_scheme_3096_);
v_val_3107_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_val_3107_);
lean_dec_ref_known(v___x_3097_, 1);
return v_val_3107_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Builder_setUserInfo___lam__0(uint8_t v___y_3108_){
_start:
{
uint8_t v___x_3152_; uint8_t v___x_3153_; 
v___x_3152_ = 48;
v___x_3153_ = lean_uint8_dec_le(v___x_3152_, v___y_3108_);
if (v___x_3153_ == 0)
{
goto v___jp_3147_;
}
else
{
uint8_t v___x_3154_; uint8_t v___x_3155_; 
v___x_3154_ = 57;
v___x_3155_ = lean_uint8_dec_le(v___y_3108_, v___x_3154_);
if (v___x_3155_ == 0)
{
goto v___jp_3147_;
}
else
{
return v___x_3155_;
}
}
v___jp_3109_:
{
uint8_t v___x_3110_; uint8_t v___x_3111_; 
v___x_3110_ = 45;
v___x_3111_ = lean_uint8_dec_eq(v___y_3108_, v___x_3110_);
if (v___x_3111_ == 0)
{
uint8_t v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = 46;
v___x_3113_ = lean_uint8_dec_eq(v___y_3108_, v___x_3112_);
if (v___x_3113_ == 0)
{
uint8_t v___x_3114_; uint8_t v___x_3115_; 
v___x_3114_ = 95;
v___x_3115_ = lean_uint8_dec_eq(v___y_3108_, v___x_3114_);
if (v___x_3115_ == 0)
{
uint8_t v___x_3116_; uint8_t v___x_3117_; 
v___x_3116_ = 126;
v___x_3117_ = lean_uint8_dec_eq(v___y_3108_, v___x_3116_);
if (v___x_3117_ == 0)
{
uint8_t v___x_3118_; uint8_t v___x_3119_; 
v___x_3118_ = 33;
v___x_3119_ = lean_uint8_dec_eq(v___y_3108_, v___x_3118_);
if (v___x_3119_ == 0)
{
uint8_t v___x_3120_; uint8_t v___x_3121_; 
v___x_3120_ = 36;
v___x_3121_ = lean_uint8_dec_eq(v___y_3108_, v___x_3120_);
if (v___x_3121_ == 0)
{
uint8_t v___x_3122_; uint8_t v___x_3123_; 
v___x_3122_ = 38;
v___x_3123_ = lean_uint8_dec_eq(v___y_3108_, v___x_3122_);
if (v___x_3123_ == 0)
{
uint8_t v___x_3124_; uint8_t v___x_3125_; 
v___x_3124_ = 39;
v___x_3125_ = lean_uint8_dec_eq(v___y_3108_, v___x_3124_);
if (v___x_3125_ == 0)
{
uint8_t v___x_3126_; uint8_t v___x_3127_; 
v___x_3126_ = 40;
v___x_3127_ = lean_uint8_dec_eq(v___y_3108_, v___x_3126_);
if (v___x_3127_ == 0)
{
uint8_t v___x_3128_; uint8_t v___x_3129_; 
v___x_3128_ = 41;
v___x_3129_ = lean_uint8_dec_eq(v___y_3108_, v___x_3128_);
if (v___x_3129_ == 0)
{
uint8_t v___x_3130_; uint8_t v___x_3131_; 
v___x_3130_ = 42;
v___x_3131_ = lean_uint8_dec_eq(v___y_3108_, v___x_3130_);
if (v___x_3131_ == 0)
{
uint8_t v___x_3132_; uint8_t v___x_3133_; 
v___x_3132_ = 43;
v___x_3133_ = lean_uint8_dec_eq(v___y_3108_, v___x_3132_);
if (v___x_3133_ == 0)
{
uint8_t v___x_3134_; uint8_t v___x_3135_; 
v___x_3134_ = 44;
v___x_3135_ = lean_uint8_dec_eq(v___y_3108_, v___x_3134_);
if (v___x_3135_ == 0)
{
uint8_t v___x_3136_; uint8_t v___x_3137_; 
v___x_3136_ = 59;
v___x_3137_ = lean_uint8_dec_eq(v___y_3108_, v___x_3136_);
if (v___x_3137_ == 0)
{
uint8_t v___x_3138_; uint8_t v___x_3139_; 
v___x_3138_ = 61;
v___x_3139_ = lean_uint8_dec_eq(v___y_3108_, v___x_3138_);
if (v___x_3139_ == 0)
{
uint8_t v___x_3140_; uint8_t v___x_3141_; 
v___x_3140_ = 58;
v___x_3141_ = lean_uint8_dec_eq(v___y_3108_, v___x_3140_);
return v___x_3141_;
}
else
{
return v___x_3139_;
}
}
else
{
return v___x_3137_;
}
}
else
{
return v___x_3135_;
}
}
else
{
return v___x_3133_;
}
}
else
{
return v___x_3131_;
}
}
else
{
return v___x_3129_;
}
}
else
{
return v___x_3127_;
}
}
else
{
return v___x_3125_;
}
}
else
{
return v___x_3123_;
}
}
else
{
return v___x_3121_;
}
}
else
{
return v___x_3119_;
}
}
else
{
return v___x_3117_;
}
}
else
{
return v___x_3115_;
}
}
else
{
return v___x_3113_;
}
}
else
{
return v___x_3111_;
}
}
v___jp_3142_:
{
uint8_t v___x_3143_; uint8_t v___x_3144_; 
v___x_3143_ = 65;
v___x_3144_ = lean_uint8_dec_le(v___x_3143_, v___y_3108_);
if (v___x_3144_ == 0)
{
goto v___jp_3109_;
}
else
{
uint8_t v___x_3145_; uint8_t v___x_3146_; 
v___x_3145_ = 90;
v___x_3146_ = lean_uint8_dec_le(v___y_3108_, v___x_3145_);
if (v___x_3146_ == 0)
{
goto v___jp_3109_;
}
else
{
return v___x_3146_;
}
}
}
v___jp_3147_:
{
uint8_t v___x_3148_; uint8_t v___x_3149_; 
v___x_3148_ = 97;
v___x_3149_ = lean_uint8_dec_le(v___x_3148_, v___y_3108_);
if (v___x_3149_ == 0)
{
goto v___jp_3142_;
}
else
{
uint8_t v___x_3150_; uint8_t v___x_3151_; 
v___x_3150_ = 122;
v___x_3151_ = lean_uint8_dec_le(v___y_3108_, v___x_3150_);
if (v___x_3151_ == 0)
{
goto v___jp_3142_;
}
else
{
return v___x_3151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo___lam__0___boxed(lean_object* v___y_3156_){
_start:
{
uint8_t v___y_287__boxed_3157_; uint8_t v_res_3158_; lean_object* v_r_3159_; 
v___y_287__boxed_3157_ = lean_unbox(v___y_3156_);
v_res_3158_ = l_Std_Http_URI_Builder_setUserInfo___lam__0(v___y_287__boxed_3157_);
v_r_3159_ = lean_box(v_res_3158_);
return v_r_3159_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo(lean_object* v_b_3161_, lean_object* v_username_3162_, lean_object* v_password_3163_){
_start:
{
lean_object* v_scheme_3164_; lean_object* v_host_3165_; lean_object* v_port_3166_; lean_object* v_pathSegments_3167_; lean_object* v_query_3168_; lean_object* v_fragment_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3194_; 
v_scheme_3164_ = lean_ctor_get(v_b_3161_, 0);
v_host_3165_ = lean_ctor_get(v_b_3161_, 2);
v_port_3166_ = lean_ctor_get(v_b_3161_, 3);
v_pathSegments_3167_ = lean_ctor_get(v_b_3161_, 4);
v_query_3168_ = lean_ctor_get(v_b_3161_, 5);
v_fragment_3169_ = lean_ctor_get(v_b_3161_, 6);
v_isSharedCheck_3194_ = !lean_is_exclusive(v_b_3161_);
if (v_isSharedCheck_3194_ == 0)
{
lean_object* v_unused_3195_; 
v_unused_3195_ = lean_ctor_get(v_b_3161_, 1);
lean_dec(v_unused_3195_);
v___x_3171_ = v_b_3161_;
v_isShared_3172_ = v_isSharedCheck_3194_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_fragment_3169_);
lean_inc(v_query_3168_);
lean_inc(v_pathSegments_3167_);
lean_inc(v_port_3166_);
lean_inc(v_host_3165_);
lean_inc(v_scheme_3164_);
lean_dec(v_b_3161_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3194_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___y_3174_; lean_object* v___f_3179_; lean_object* v___f_3180_; lean_object* v___x_3181_; 
v___f_3179_ = ((lean_object*)(l_Std_Http_URI_Builder_setUserInfo___closed__0));
v___f_3180_ = ((lean_object*)(l_Std_Http_URI_UserInfo_ofStrings___closed__0));
v___x_3181_ = l_Std_Http_URI_EncodedString_encodeEscaping(v___f_3179_, v_username_3162_, v___f_3180_);
if (lean_obj_tag(v_password_3163_) == 0)
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = lean_box(0);
v___x_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3181_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___y_3174_ = v___x_3183_;
goto v___jp_3173_;
}
else
{
lean_object* v_val_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3193_; 
v_val_3184_ = lean_ctor_get(v_password_3163_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v_password_3163_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3186_ = v_password_3163_;
v_isShared_3187_ = v_isSharedCheck_3193_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_val_3184_);
lean_dec(v_password_3163_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3193_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3188_; lean_object* v___x_3190_; 
v___x_3188_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_3184_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 0, v___x_3188_);
v___x_3190_ = v___x_3186_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3188_);
v___x_3190_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3191_; 
v___x_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3181_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v___y_3174_ = v___x_3191_;
goto v___jp_3173_;
}
}
}
v___jp_3173_:
{
lean_object* v___x_3175_; lean_object* v___x_3177_; 
v___x_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3175_, 0, v___y_3174_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 1, v___x_3175_);
v___x_3177_ = v___x_3171_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_scheme_3164_);
lean_ctor_set(v_reuseFailAlloc_3178_, 1, v___x_3175_);
lean_ctor_set(v_reuseFailAlloc_3178_, 2, v_host_3165_);
lean_ctor_set(v_reuseFailAlloc_3178_, 3, v_port_3166_);
lean_ctor_set(v_reuseFailAlloc_3178_, 4, v_pathSegments_3167_);
lean_ctor_set(v_reuseFailAlloc_3178_, 5, v_query_3168_);
lean_ctor_set(v_reuseFailAlloc_3178_, 6, v_fragment_3169_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x3f(lean_object* v_b_3196_, lean_object* v_name_3197_){
_start:
{
lean_object* v___x_3198_; 
v___x_3198_ = lean_uv_pton_v4(v_name_3197_);
if (lean_obj_tag(v___x_3198_) == 1)
{
lean_object* v_val_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3222_; 
lean_dec_ref(v_name_3197_);
v_val_3199_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3222_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_val_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3222_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v_scheme_3203_; lean_object* v_userInfo_3204_; lean_object* v_port_3205_; lean_object* v_pathSegments_3206_; lean_object* v_query_3207_; lean_object* v_fragment_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3220_; 
v_scheme_3203_ = lean_ctor_get(v_b_3196_, 0);
v_userInfo_3204_ = lean_ctor_get(v_b_3196_, 1);
v_port_3205_ = lean_ctor_get(v_b_3196_, 3);
v_pathSegments_3206_ = lean_ctor_get(v_b_3196_, 4);
v_query_3207_ = lean_ctor_get(v_b_3196_, 5);
v_fragment_3208_ = lean_ctor_get(v_b_3196_, 6);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_b_3196_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; 
v_unused_3221_ = lean_ctor_get(v_b_3196_, 2);
lean_dec(v_unused_3221_);
v___x_3210_ = v_b_3196_;
v_isShared_3211_ = v_isSharedCheck_3220_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_fragment_3208_);
lean_inc(v_query_3207_);
lean_inc(v_pathSegments_3206_);
lean_inc(v_port_3205_);
lean_inc(v_userInfo_3204_);
lean_inc(v_scheme_3203_);
lean_dec(v_b_3196_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3220_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3212_, 0, v_val_3199_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3212_);
v___x_3214_ = v___x_3201_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3212_);
v___x_3214_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3216_; 
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 2, v___x_3214_);
v___x_3216_ = v___x_3210_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_scheme_3203_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_userInfo_3204_);
lean_ctor_set(v_reuseFailAlloc_3218_, 2, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3218_, 3, v_port_3205_);
lean_ctor_set(v_reuseFailAlloc_3218_, 4, v_pathSegments_3206_);
lean_ctor_set(v_reuseFailAlloc_3218_, 5, v_query_3207_);
lean_ctor_set(v_reuseFailAlloc_3218_, 6, v_fragment_3208_);
v___x_3216_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
return v___x_3217_;
}
}
}
}
}
else
{
lean_object* v___x_3223_; 
lean_dec(v___x_3198_);
v___x_3223_ = l_Std_Http_URI_DomainName_ofString_x3f(v_name_3197_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v___x_3224_; 
lean_dec_ref(v_b_3196_);
v___x_3224_ = lean_box(0);
return v___x_3224_;
}
else
{
lean_object* v_val_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3248_; 
v_val_3225_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3227_ = v___x_3223_;
v_isShared_3228_ = v_isSharedCheck_3248_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_val_3225_);
lean_dec(v___x_3223_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3248_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v_scheme_3229_; lean_object* v_userInfo_3230_; lean_object* v_port_3231_; lean_object* v_pathSegments_3232_; lean_object* v_query_3233_; lean_object* v_fragment_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3246_; 
v_scheme_3229_ = lean_ctor_get(v_b_3196_, 0);
v_userInfo_3230_ = lean_ctor_get(v_b_3196_, 1);
v_port_3231_ = lean_ctor_get(v_b_3196_, 3);
v_pathSegments_3232_ = lean_ctor_get(v_b_3196_, 4);
v_query_3233_ = lean_ctor_get(v_b_3196_, 5);
v_fragment_3234_ = lean_ctor_get(v_b_3196_, 6);
v_isSharedCheck_3246_ = !lean_is_exclusive(v_b_3196_);
if (v_isSharedCheck_3246_ == 0)
{
lean_object* v_unused_3247_; 
v_unused_3247_ = lean_ctor_get(v_b_3196_, 2);
lean_dec(v_unused_3247_);
v___x_3236_ = v_b_3196_;
v_isShared_3237_ = v_isSharedCheck_3246_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_fragment_3234_);
lean_inc(v_query_3233_);
lean_inc(v_pathSegments_3232_);
lean_inc(v_port_3231_);
lean_inc(v_userInfo_3230_);
lean_inc(v_scheme_3229_);
lean_dec(v_b_3196_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3246_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3238_; lean_object* v___x_3240_; 
v___x_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3238_, 0, v_val_3225_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3238_);
v___x_3240_ = v___x_3227_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3242_; 
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 2, v___x_3240_);
v___x_3242_ = v___x_3236_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_scheme_3229_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_userInfo_3230_);
lean_ctor_set(v_reuseFailAlloc_3244_, 2, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3244_, 3, v_port_3231_);
lean_ctor_set(v_reuseFailAlloc_3244_, 4, v_pathSegments_3232_);
lean_ctor_set(v_reuseFailAlloc_3244_, 5, v_query_3233_);
lean_ctor_set(v_reuseFailAlloc_3244_, 6, v_fragment_3234_);
v___x_3242_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3243_; 
v___x_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3242_);
return v___x_3243_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x21(lean_object* v_b_3251_, lean_object* v_name_3252_){
_start:
{
lean_object* v___x_3253_; 
lean_inc_ref(v_name_3252_);
v___x_3253_ = l_Std_Http_URI_Builder_setHost_x3f(v_b_3251_, v_name_3252_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3254_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_3255_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__0));
v___x_3256_ = lean_unsigned_to_nat(788u);
v___x_3257_ = lean_unsigned_to_nat(14u);
v___x_3258_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__1));
v___x_3259_ = l_String_quote(v_name_3252_);
v___x_3260_ = lean_string_append(v___x_3258_, v___x_3259_);
lean_dec_ref(v___x_3259_);
v___x_3261_ = l_mkPanicMessageWithDecl(v___x_3254_, v___x_3255_, v___x_3256_, v___x_3257_, v___x_3260_);
lean_dec_ref(v___x_3260_);
v___x_3262_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_3261_);
return v___x_3262_;
}
else
{
lean_object* v_val_3263_; 
lean_dec_ref(v_name_3252_);
v_val_3263_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_val_3263_);
lean_dec_ref_known(v___x_3253_, 1);
return v_val_3263_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv4(lean_object* v_b_3264_, lean_object* v_addr_3265_){
_start:
{
lean_object* v_scheme_3266_; lean_object* v_userInfo_3267_; lean_object* v_port_3268_; lean_object* v_pathSegments_3269_; lean_object* v_query_3270_; lean_object* v_fragment_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3280_; 
v_scheme_3266_ = lean_ctor_get(v_b_3264_, 0);
v_userInfo_3267_ = lean_ctor_get(v_b_3264_, 1);
v_port_3268_ = lean_ctor_get(v_b_3264_, 3);
v_pathSegments_3269_ = lean_ctor_get(v_b_3264_, 4);
v_query_3270_ = lean_ctor_get(v_b_3264_, 5);
v_fragment_3271_ = lean_ctor_get(v_b_3264_, 6);
v_isSharedCheck_3280_ = !lean_is_exclusive(v_b_3264_);
if (v_isSharedCheck_3280_ == 0)
{
lean_object* v_unused_3281_; 
v_unused_3281_ = lean_ctor_get(v_b_3264_, 2);
lean_dec(v_unused_3281_);
v___x_3273_ = v_b_3264_;
v_isShared_3274_ = v_isSharedCheck_3280_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_fragment_3271_);
lean_inc(v_query_3270_);
lean_inc(v_pathSegments_3269_);
lean_inc(v_port_3268_);
lean_inc(v_userInfo_3267_);
lean_inc(v_scheme_3266_);
lean_dec(v_b_3264_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3280_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3275_, 0, v_addr_3265_);
v___x_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 2, v___x_3276_);
v___x_3278_ = v___x_3273_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_scheme_3266_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v_userInfo_3267_);
lean_ctor_set(v_reuseFailAlloc_3279_, 2, v___x_3276_);
lean_ctor_set(v_reuseFailAlloc_3279_, 3, v_port_3268_);
lean_ctor_set(v_reuseFailAlloc_3279_, 4, v_pathSegments_3269_);
lean_ctor_set(v_reuseFailAlloc_3279_, 5, v_query_3270_);
lean_ctor_set(v_reuseFailAlloc_3279_, 6, v_fragment_3271_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv6(lean_object* v_b_3282_, lean_object* v_addr_3283_){
_start:
{
lean_object* v_scheme_3284_; lean_object* v_userInfo_3285_; lean_object* v_port_3286_; lean_object* v_pathSegments_3287_; lean_object* v_query_3288_; lean_object* v_fragment_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3298_; 
v_scheme_3284_ = lean_ctor_get(v_b_3282_, 0);
v_userInfo_3285_ = lean_ctor_get(v_b_3282_, 1);
v_port_3286_ = lean_ctor_get(v_b_3282_, 3);
v_pathSegments_3287_ = lean_ctor_get(v_b_3282_, 4);
v_query_3288_ = lean_ctor_get(v_b_3282_, 5);
v_fragment_3289_ = lean_ctor_get(v_b_3282_, 6);
v_isSharedCheck_3298_ = !lean_is_exclusive(v_b_3282_);
if (v_isSharedCheck_3298_ == 0)
{
lean_object* v_unused_3299_; 
v_unused_3299_ = lean_ctor_get(v_b_3282_, 2);
lean_dec(v_unused_3299_);
v___x_3291_ = v_b_3282_;
v_isShared_3292_ = v_isSharedCheck_3298_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_fragment_3289_);
lean_inc(v_query_3288_);
lean_inc(v_pathSegments_3287_);
lean_inc(v_port_3286_);
lean_inc(v_userInfo_3285_);
lean_inc(v_scheme_3284_);
lean_dec(v_b_3282_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3298_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3293_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3293_, 0, v_addr_3283_);
v___x_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 2, v___x_3294_);
v___x_3296_ = v___x_3291_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_scheme_3284_);
lean_ctor_set(v_reuseFailAlloc_3297_, 1, v_userInfo_3285_);
lean_ctor_set(v_reuseFailAlloc_3297_, 2, v___x_3294_);
lean_ctor_set(v_reuseFailAlloc_3297_, 3, v_port_3286_);
lean_ctor_set(v_reuseFailAlloc_3297_, 4, v_pathSegments_3287_);
lean_ctor_set(v_reuseFailAlloc_3297_, 5, v_query_3288_);
lean_ctor_set(v_reuseFailAlloc_3297_, 6, v_fragment_3289_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort(lean_object* v_b_3300_, uint16_t v_port_3301_){
_start:
{
lean_object* v_scheme_3302_; lean_object* v_userInfo_3303_; lean_object* v_host_3304_; lean_object* v_pathSegments_3305_; lean_object* v_query_3306_; lean_object* v_fragment_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3315_; 
v_scheme_3302_ = lean_ctor_get(v_b_3300_, 0);
v_userInfo_3303_ = lean_ctor_get(v_b_3300_, 1);
v_host_3304_ = lean_ctor_get(v_b_3300_, 2);
v_pathSegments_3305_ = lean_ctor_get(v_b_3300_, 4);
v_query_3306_ = lean_ctor_get(v_b_3300_, 5);
v_fragment_3307_ = lean_ctor_get(v_b_3300_, 6);
v_isSharedCheck_3315_ = !lean_is_exclusive(v_b_3300_);
if (v_isSharedCheck_3315_ == 0)
{
lean_object* v_unused_3316_; 
v_unused_3316_ = lean_ctor_get(v_b_3300_, 3);
lean_dec(v_unused_3316_);
v___x_3309_ = v_b_3300_;
v_isShared_3310_ = v_isSharedCheck_3315_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_fragment_3307_);
lean_inc(v_query_3306_);
lean_inc(v_pathSegments_3305_);
lean_inc(v_host_3304_);
lean_inc(v_userInfo_3303_);
lean_inc(v_scheme_3302_);
lean_dec(v_b_3300_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3315_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3311_ = lean_alloc_ctor(2, 0, 2);
lean_ctor_set_uint16(v___x_3311_, 0, v_port_3301_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 3, v___x_3311_);
v___x_3313_ = v___x_3309_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_scheme_3302_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_userInfo_3303_);
lean_ctor_set(v_reuseFailAlloc_3314_, 2, v_host_3304_);
lean_ctor_set(v_reuseFailAlloc_3314_, 3, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3314_, 4, v_pathSegments_3305_);
lean_ctor_set(v_reuseFailAlloc_3314_, 5, v_query_3306_);
lean_ctor_set(v_reuseFailAlloc_3314_, 6, v_fragment_3307_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort___boxed(lean_object* v_b_3317_, lean_object* v_port_3318_){
_start:
{
uint16_t v_port_boxed_3319_; lean_object* v_res_3320_; 
v_port_boxed_3319_ = lean_unbox(v_port_3318_);
v_res_3320_ = l_Std_Http_URI_Builder_setPort(v_b_3317_, v_port_boxed_3319_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPath(lean_object* v_b_3321_, lean_object* v_segments_3322_){
_start:
{
lean_object* v_scheme_3323_; lean_object* v_userInfo_3324_; lean_object* v_host_3325_; lean_object* v_port_3326_; lean_object* v_query_3327_; lean_object* v_fragment_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
v_scheme_3323_ = lean_ctor_get(v_b_3321_, 0);
v_userInfo_3324_ = lean_ctor_get(v_b_3321_, 1);
v_host_3325_ = lean_ctor_get(v_b_3321_, 2);
v_port_3326_ = lean_ctor_get(v_b_3321_, 3);
v_query_3327_ = lean_ctor_get(v_b_3321_, 5);
v_fragment_3328_ = lean_ctor_get(v_b_3321_, 6);
v_isSharedCheck_3335_ = !lean_is_exclusive(v_b_3321_);
if (v_isSharedCheck_3335_ == 0)
{
lean_object* v_unused_3336_; 
v_unused_3336_ = lean_ctor_get(v_b_3321_, 4);
lean_dec(v_unused_3336_);
v___x_3330_ = v_b_3321_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_fragment_3328_);
lean_inc(v_query_3327_);
lean_inc(v_port_3326_);
lean_inc(v_host_3325_);
lean_inc(v_userInfo_3324_);
lean_inc(v_scheme_3323_);
lean_dec(v_b_3321_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 4, v_segments_3322_);
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_scheme_3323_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_userInfo_3324_);
lean_ctor_set(v_reuseFailAlloc_3334_, 2, v_host_3325_);
lean_ctor_set(v_reuseFailAlloc_3334_, 3, v_port_3326_);
lean_ctor_set(v_reuseFailAlloc_3334_, 4, v_segments_3322_);
lean_ctor_set(v_reuseFailAlloc_3334_, 5, v_query_3327_);
lean_ctor_set(v_reuseFailAlloc_3334_, 6, v_fragment_3328_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_appendPathSegment(lean_object* v_b_3337_, lean_object* v_segment_3338_){
_start:
{
lean_object* v_scheme_3339_; lean_object* v_userInfo_3340_; lean_object* v_host_3341_; lean_object* v_port_3342_; lean_object* v_pathSegments_3343_; lean_object* v_query_3344_; lean_object* v_fragment_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3353_; 
v_scheme_3339_ = lean_ctor_get(v_b_3337_, 0);
v_userInfo_3340_ = lean_ctor_get(v_b_3337_, 1);
v_host_3341_ = lean_ctor_get(v_b_3337_, 2);
v_port_3342_ = lean_ctor_get(v_b_3337_, 3);
v_pathSegments_3343_ = lean_ctor_get(v_b_3337_, 4);
v_query_3344_ = lean_ctor_get(v_b_3337_, 5);
v_fragment_3345_ = lean_ctor_get(v_b_3337_, 6);
v_isSharedCheck_3353_ = !lean_is_exclusive(v_b_3337_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3347_ = v_b_3337_;
v_isShared_3348_ = v_isSharedCheck_3353_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_fragment_3345_);
lean_inc(v_query_3344_);
lean_inc(v_pathSegments_3343_);
lean_inc(v_port_3342_);
lean_inc(v_host_3341_);
lean_inc(v_userInfo_3340_);
lean_inc(v_scheme_3339_);
lean_dec(v_b_3337_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3353_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; lean_object* v___x_3351_; 
v___x_3349_ = lean_array_push(v_pathSegments_3343_, v_segment_3338_);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 4, v___x_3349_);
v___x_3351_ = v___x_3347_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_scheme_3339_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v_userInfo_3340_);
lean_ctor_set(v_reuseFailAlloc_3352_, 2, v_host_3341_);
lean_ctor_set(v_reuseFailAlloc_3352_, 3, v_port_3342_);
lean_ctor_set(v_reuseFailAlloc_3352_, 4, v___x_3349_);
lean_ctor_set(v_reuseFailAlloc_3352_, 5, v_query_3344_);
lean_ctor_set(v_reuseFailAlloc_3352_, 6, v_fragment_3345_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryParam(lean_object* v_b_3354_, lean_object* v_key_3355_, lean_object* v_value_3356_){
_start:
{
lean_object* v_scheme_3357_; lean_object* v_userInfo_3358_; lean_object* v_host_3359_; lean_object* v_port_3360_; lean_object* v_pathSegments_3361_; lean_object* v_query_3362_; lean_object* v_fragment_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3373_; 
v_scheme_3357_ = lean_ctor_get(v_b_3354_, 0);
v_userInfo_3358_ = lean_ctor_get(v_b_3354_, 1);
v_host_3359_ = lean_ctor_get(v_b_3354_, 2);
v_port_3360_ = lean_ctor_get(v_b_3354_, 3);
v_pathSegments_3361_ = lean_ctor_get(v_b_3354_, 4);
v_query_3362_ = lean_ctor_get(v_b_3354_, 5);
v_fragment_3363_ = lean_ctor_get(v_b_3354_, 6);
v_isSharedCheck_3373_ = !lean_is_exclusive(v_b_3354_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3365_ = v_b_3354_;
v_isShared_3366_ = v_isSharedCheck_3373_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_fragment_3363_);
lean_inc(v_query_3362_);
lean_inc(v_pathSegments_3361_);
lean_inc(v_port_3360_);
lean_inc(v_host_3359_);
lean_inc(v_userInfo_3358_);
lean_inc(v_scheme_3357_);
lean_dec(v_b_3354_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3373_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3371_; 
v___x_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3367_, 0, v_value_3356_);
v___x_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3368_, 0, v_key_3355_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = lean_array_push(v_query_3362_, v___x_3368_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 5, v___x_3369_);
v___x_3371_ = v___x_3365_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_scheme_3357_);
lean_ctor_set(v_reuseFailAlloc_3372_, 1, v_userInfo_3358_);
lean_ctor_set(v_reuseFailAlloc_3372_, 2, v_host_3359_);
lean_ctor_set(v_reuseFailAlloc_3372_, 3, v_port_3360_);
lean_ctor_set(v_reuseFailAlloc_3372_, 4, v_pathSegments_3361_);
lean_ctor_set(v_reuseFailAlloc_3372_, 5, v___x_3369_);
lean_ctor_set(v_reuseFailAlloc_3372_, 6, v_fragment_3363_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryFlag(lean_object* v_b_3374_, lean_object* v_key_3375_){
_start:
{
lean_object* v_scheme_3376_; lean_object* v_userInfo_3377_; lean_object* v_host_3378_; lean_object* v_port_3379_; lean_object* v_pathSegments_3380_; lean_object* v_query_3381_; lean_object* v_fragment_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3392_; 
v_scheme_3376_ = lean_ctor_get(v_b_3374_, 0);
v_userInfo_3377_ = lean_ctor_get(v_b_3374_, 1);
v_host_3378_ = lean_ctor_get(v_b_3374_, 2);
v_port_3379_ = lean_ctor_get(v_b_3374_, 3);
v_pathSegments_3380_ = lean_ctor_get(v_b_3374_, 4);
v_query_3381_ = lean_ctor_get(v_b_3374_, 5);
v_fragment_3382_ = lean_ctor_get(v_b_3374_, 6);
v_isSharedCheck_3392_ = !lean_is_exclusive(v_b_3374_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3384_ = v_b_3374_;
v_isShared_3385_ = v_isSharedCheck_3392_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_fragment_3382_);
lean_inc(v_query_3381_);
lean_inc(v_pathSegments_3380_);
lean_inc(v_port_3379_);
lean_inc(v_host_3378_);
lean_inc(v_userInfo_3377_);
lean_inc(v_scheme_3376_);
lean_dec(v_b_3374_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3392_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3390_; 
v___x_3386_ = lean_box(0);
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v_key_3375_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = lean_array_push(v_query_3381_, v___x_3387_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 5, v___x_3388_);
v___x_3390_ = v___x_3384_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_scheme_3376_);
lean_ctor_set(v_reuseFailAlloc_3391_, 1, v_userInfo_3377_);
lean_ctor_set(v_reuseFailAlloc_3391_, 2, v_host_3378_);
lean_ctor_set(v_reuseFailAlloc_3391_, 3, v_port_3379_);
lean_ctor_set(v_reuseFailAlloc_3391_, 4, v_pathSegments_3380_);
lean_ctor_set(v_reuseFailAlloc_3391_, 5, v___x_3388_);
lean_ctor_set(v_reuseFailAlloc_3391_, 6, v_fragment_3382_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setQuery(lean_object* v_b_3393_, lean_object* v_query_3394_){
_start:
{
lean_object* v_scheme_3395_; lean_object* v_userInfo_3396_; lean_object* v_host_3397_; lean_object* v_port_3398_; lean_object* v_pathSegments_3399_; lean_object* v_fragment_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
v_scheme_3395_ = lean_ctor_get(v_b_3393_, 0);
v_userInfo_3396_ = lean_ctor_get(v_b_3393_, 1);
v_host_3397_ = lean_ctor_get(v_b_3393_, 2);
v_port_3398_ = lean_ctor_get(v_b_3393_, 3);
v_pathSegments_3399_ = lean_ctor_get(v_b_3393_, 4);
v_fragment_3400_ = lean_ctor_get(v_b_3393_, 6);
v_isSharedCheck_3407_ = !lean_is_exclusive(v_b_3393_);
if (v_isSharedCheck_3407_ == 0)
{
lean_object* v_unused_3408_; 
v_unused_3408_ = lean_ctor_get(v_b_3393_, 5);
lean_dec(v_unused_3408_);
v___x_3402_ = v_b_3393_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_fragment_3400_);
lean_inc(v_pathSegments_3399_);
lean_inc(v_port_3398_);
lean_inc(v_host_3397_);
lean_inc(v_userInfo_3396_);
lean_inc(v_scheme_3395_);
lean_dec(v_b_3393_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 5, v_query_3394_);
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_scheme_3395_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_userInfo_3396_);
lean_ctor_set(v_reuseFailAlloc_3406_, 2, v_host_3397_);
lean_ctor_set(v_reuseFailAlloc_3406_, 3, v_port_3398_);
lean_ctor_set(v_reuseFailAlloc_3406_, 4, v_pathSegments_3399_);
lean_ctor_set(v_reuseFailAlloc_3406_, 5, v_query_3394_);
lean_ctor_set(v_reuseFailAlloc_3406_, 6, v_fragment_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setFragment(lean_object* v_b_3409_, lean_object* v_fragment_3410_){
_start:
{
lean_object* v_scheme_3411_; lean_object* v_userInfo_3412_; lean_object* v_host_3413_; lean_object* v_port_3414_; lean_object* v_pathSegments_3415_; lean_object* v_query_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3424_; 
v_scheme_3411_ = lean_ctor_get(v_b_3409_, 0);
v_userInfo_3412_ = lean_ctor_get(v_b_3409_, 1);
v_host_3413_ = lean_ctor_get(v_b_3409_, 2);
v_port_3414_ = lean_ctor_get(v_b_3409_, 3);
v_pathSegments_3415_ = lean_ctor_get(v_b_3409_, 4);
v_query_3416_ = lean_ctor_get(v_b_3409_, 5);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_b_3409_);
if (v_isSharedCheck_3424_ == 0)
{
lean_object* v_unused_3425_; 
v_unused_3425_ = lean_ctor_get(v_b_3409_, 6);
lean_dec(v_unused_3425_);
v___x_3418_ = v_b_3409_;
v_isShared_3419_ = v_isSharedCheck_3424_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_query_3416_);
lean_inc(v_pathSegments_3415_);
lean_inc(v_port_3414_);
lean_inc(v_host_3413_);
lean_inc(v_userInfo_3412_);
lean_inc(v_scheme_3411_);
lean_dec(v_b_3409_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3424_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3420_, 0, v_fragment_3410_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 6, v___x_3420_);
v___x_3422_ = v___x_3418_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_scheme_3411_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_userInfo_3412_);
lean_ctor_set(v_reuseFailAlloc_3423_, 2, v_host_3413_);
lean_ctor_set(v_reuseFailAlloc_3423_, 3, v_port_3414_);
lean_ctor_set(v_reuseFailAlloc_3423_, 4, v_pathSegments_3415_);
lean_ctor_set(v_reuseFailAlloc_3423_, 5, v_query_3416_);
lean_ctor_set(v_reuseFailAlloc_3423_, 6, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(size_t v_sz_3426_, size_t v_i_3427_, lean_object* v_bs_3428_){
_start:
{
uint8_t v___x_3429_; 
v___x_3429_ = lean_usize_dec_lt(v_i_3427_, v_sz_3426_);
if (v___x_3429_ == 0)
{
return v_bs_3428_;
}
else
{
lean_object* v_v_3430_; lean_object* v___x_3431_; lean_object* v_bs_x27_3432_; lean_object* v___x_3433_; size_t v___x_3434_; size_t v___x_3435_; lean_object* v___x_3436_; 
v_v_3430_ = lean_array_uget(v_bs_3428_, v_i_3427_);
v___x_3431_ = lean_unsigned_to_nat(0u);
v_bs_x27_3432_ = lean_array_uset(v_bs_3428_, v_i_3427_, v___x_3431_);
v___x_3433_ = l_Std_Http_URI_EncodedSegment_encode(v_v_3430_);
v___x_3434_ = ((size_t)1ULL);
v___x_3435_ = lean_usize_add(v_i_3427_, v___x_3434_);
v___x_3436_ = lean_array_uset(v_bs_x27_3432_, v_i_3427_, v___x_3433_);
v_i_3427_ = v___x_3435_;
v_bs_3428_ = v___x_3436_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0___boxed(lean_object* v_sz_3438_, lean_object* v_i_3439_, lean_object* v_bs_3440_){
_start:
{
size_t v_sz_boxed_3441_; size_t v_i_boxed_3442_; lean_object* v_res_3443_; 
v_sz_boxed_3441_ = lean_unbox_usize(v_sz_3438_);
lean_dec(v_sz_3438_);
v_i_boxed_3442_ = lean_unbox_usize(v_i_3439_);
lean_dec(v_i_3439_);
v_res_3443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_boxed_3441_, v_i_boxed_3442_, v_bs_3440_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(size_t v_sz_3444_, size_t v_i_3445_, lean_object* v_bs_3446_){
_start:
{
uint8_t v___x_3447_; 
v___x_3447_ = lean_usize_dec_lt(v_i_3445_, v_sz_3444_);
if (v___x_3447_ == 0)
{
return v_bs_3446_;
}
else
{
lean_object* v_v_3448_; lean_object* v_fst_3449_; lean_object* v_snd_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3479_; 
v_v_3448_ = lean_array_uget(v_bs_3446_, v_i_3445_);
v_fst_3449_ = lean_ctor_get(v_v_3448_, 0);
v_snd_3450_ = lean_ctor_get(v_v_3448_, 1);
v_isSharedCheck_3479_ = !lean_is_exclusive(v_v_3448_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3452_ = v_v_3448_;
v_isShared_3453_ = v_isSharedCheck_3479_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_snd_3450_);
lean_inc(v_fst_3449_);
lean_dec(v_v_3448_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3479_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3454_; lean_object* v_bs_x27_3455_; lean_object* v___y_3457_; lean_object* v___x_3462_; 
v___x_3454_ = lean_unsigned_to_nat(0u);
v_bs_x27_3455_ = lean_array_uset(v_bs_3446_, v_i_3445_, v___x_3454_);
v___x_3462_ = l_Std_Http_URI_EncodedQueryParam_encode(v_fst_3449_);
if (lean_obj_tag(v_snd_3450_) == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3463_ = lean_box(0);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 1, v___x_3463_);
lean_ctor_set(v___x_3452_, 0, v___x_3462_);
v___x_3465_ = v___x_3452_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3462_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
v___y_3457_ = v___x_3465_;
goto v___jp_3456_;
}
}
else
{
lean_object* v_val_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3478_; 
v_val_3467_ = lean_ctor_get(v_snd_3450_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v_snd_3450_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3469_ = v_snd_3450_;
v_isShared_3470_ = v_isSharedCheck_3478_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_val_3467_);
lean_dec(v_snd_3450_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3478_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = l_Std_Http_URI_EncodedQueryParam_encode(v_val_3467_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3471_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3475_; 
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 1, v___x_3473_);
lean_ctor_set(v___x_3452_, 0, v___x_3462_);
v___x_3475_ = v___x_3452_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3462_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
v___y_3457_ = v___x_3475_;
goto v___jp_3456_;
}
}
}
}
v___jp_3456_:
{
size_t v___x_3458_; size_t v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = ((size_t)1ULL);
v___x_3459_ = lean_usize_add(v_i_3445_, v___x_3458_);
v___x_3460_ = lean_array_uset(v_bs_x27_3455_, v_i_3445_, v___y_3457_);
v_i_3445_ = v___x_3459_;
v_bs_3446_ = v___x_3460_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1___boxed(lean_object* v_sz_3480_, lean_object* v_i_3481_, lean_object* v_bs_3482_){
_start:
{
size_t v_sz_boxed_3483_; size_t v_i_boxed_3484_; lean_object* v_res_3485_; 
v_sz_boxed_3483_ = lean_unbox_usize(v_sz_3480_);
lean_dec(v_sz_3480_);
v_i_boxed_3484_ = lean_unbox_usize(v_i_3481_);
lean_dec(v_i_3481_);
v_res_3485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_boxed_3483_, v_i_boxed_3484_, v_bs_3482_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_build(lean_object* v_b_3486_){
_start:
{
lean_object* v___y_3488_; lean_object* v___y_3489_; uint8_t v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v_scheme_3509_; lean_object* v_userInfo_3510_; lean_object* v_host_3511_; lean_object* v_port_3512_; lean_object* v_pathSegments_3513_; lean_object* v_query_3514_; lean_object* v_fragment_3515_; lean_object* v___y_3517_; 
v_scheme_3509_ = lean_ctor_get(v_b_3486_, 0);
lean_inc(v_scheme_3509_);
v_userInfo_3510_ = lean_ctor_get(v_b_3486_, 1);
lean_inc(v_userInfo_3510_);
v_host_3511_ = lean_ctor_get(v_b_3486_, 2);
lean_inc(v_host_3511_);
v_port_3512_ = lean_ctor_get(v_b_3486_, 3);
lean_inc(v_port_3512_);
v_pathSegments_3513_ = lean_ctor_get(v_b_3486_, 4);
lean_inc_ref(v_pathSegments_3513_);
v_query_3514_ = lean_ctor_get(v_b_3486_, 5);
lean_inc_ref(v_query_3514_);
v_fragment_3515_ = lean_ctor_get(v_b_3486_, 6);
lean_inc(v_fragment_3515_);
lean_dec_ref(v_b_3486_);
if (lean_obj_tag(v_scheme_3509_) == 0)
{
lean_object* v___x_3530_; 
v___x_3530_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___y_3517_ = v___x_3530_;
goto v___jp_3516_;
}
else
{
lean_object* v_val_3531_; 
v_val_3531_ = lean_ctor_get(v_scheme_3509_, 0);
lean_inc(v_val_3531_);
lean_dec_ref_known(v_scheme_3509_, 1);
v___y_3517_ = v_val_3531_;
goto v___jp_3516_;
}
v___jp_3487_:
{
size_t v_sz_3494_; size_t v___x_3495_; lean_object* v___x_3496_; lean_object* v_path_3497_; size_t v_sz_3498_; lean_object* v_query_3499_; lean_object* v___x_3500_; lean_object* v_query_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v_sz_3494_ = lean_array_size(v___y_3489_);
v___x_3495_ = ((size_t)0ULL);
v___x_3496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_3494_, v___x_3495_, v___y_3489_);
v_path_3497_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_path_3497_, 0, v___x_3496_);
lean_ctor_set_uint8(v_path_3497_, sizeof(void*)*1, v___y_3490_);
v_sz_3498_ = lean_array_size(v___y_3491_);
v_query_3499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_3498_, v___x_3495_, v___y_3491_);
v___x_3500_ = lean_array_to_list(v_query_3499_);
v_query_3501_ = lean_array_mk(v___x_3500_);
v___x_3502_ = lean_array_get_size(v_query_3501_);
v___x_3503_ = lean_unsigned_to_nat(0u);
v___x_3504_ = lean_nat_dec_eq(v___x_3502_, v___x_3503_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3505_, 0, v_query_3501_);
v___x_3506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3506_, 0, v___y_3488_);
lean_ctor_set(v___x_3506_, 1, v___y_3493_);
lean_ctor_set(v___x_3506_, 2, v_path_3497_);
lean_ctor_set(v___x_3506_, 3, v___x_3505_);
lean_ctor_set(v___x_3506_, 4, v___y_3492_);
return v___x_3506_;
}
else
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
lean_dec_ref(v_query_3501_);
v___x_3507_ = lean_box(0);
v___x_3508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3508_, 0, v___y_3488_);
lean_ctor_set(v___x_3508_, 1, v___y_3493_);
lean_ctor_set(v___x_3508_, 2, v_path_3497_);
lean_ctor_set(v___x_3508_, 3, v___x_3507_);
lean_ctor_set(v___x_3508_, 4, v___y_3492_);
return v___x_3508_;
}
}
v___jp_3516_:
{
if (lean_obj_tag(v_host_3511_) == 0)
{
uint8_t v___x_3518_; lean_object* v___x_3519_; 
lean_dec(v_port_3512_);
lean_dec(v_userInfo_3510_);
v___x_3518_ = 1;
v___x_3519_ = lean_box(0);
v___y_3488_ = v___y_3517_;
v___y_3489_ = v_pathSegments_3513_;
v___y_3490_ = v___x_3518_;
v___y_3491_ = v_query_3514_;
v___y_3492_ = v_fragment_3515_;
v___y_3493_ = v___x_3519_;
goto v___jp_3487_;
}
else
{
lean_object* v_val_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3529_; 
v_val_3520_ = lean_ctor_get(v_host_3511_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v_host_3511_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3522_ = v_host_3511_;
v_isShared_3523_ = v_isSharedCheck_3529_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_val_3520_);
lean_dec(v_host_3511_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3529_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
uint8_t v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3527_; 
v___x_3524_ = 1;
v___x_3525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3525_, 0, v_userInfo_3510_);
lean_ctor_set(v___x_3525_, 1, v_val_3520_);
lean_ctor_set(v___x_3525_, 2, v_port_3512_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3525_);
v___x_3527_ = v___x_3522_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
v___y_3488_ = v___y_3517_;
v___y_3489_ = v_pathSegments_3513_;
v___y_3490_ = v___x_3524_;
v___y_3491_ = v_query_3514_;
v___y_3492_ = v_fragment_3515_;
v___y_3493_ = v___x_3527_;
goto v___jp_3487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withScheme_x21(lean_object* v_uri_3532_, lean_object* v_scheme_3533_){
_start:
{
lean_object* v_authority_3534_; lean_object* v_path_3535_; lean_object* v_query_3536_; lean_object* v_fragment_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3545_; 
v_authority_3534_ = lean_ctor_get(v_uri_3532_, 1);
v_path_3535_ = lean_ctor_get(v_uri_3532_, 2);
v_query_3536_ = lean_ctor_get(v_uri_3532_, 3);
v_fragment_3537_ = lean_ctor_get(v_uri_3532_, 4);
v_isSharedCheck_3545_ = !lean_is_exclusive(v_uri_3532_);
if (v_isSharedCheck_3545_ == 0)
{
lean_object* v_unused_3546_; 
v_unused_3546_ = lean_ctor_get(v_uri_3532_, 0);
lean_dec(v_unused_3546_);
v___x_3539_ = v_uri_3532_;
v_isShared_3540_ = v_isSharedCheck_3545_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_fragment_3537_);
lean_inc(v_query_3536_);
lean_inc(v_path_3535_);
lean_inc(v_authority_3534_);
lean_dec(v_uri_3532_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3545_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; lean_object* v___x_3543_; 
v___x_3541_ = l_Std_Http_URI_Scheme_ofString_x21(v_scheme_3533_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v___x_3541_);
v___x_3543_ = v___x_3539_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3541_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v_authority_3534_);
lean_ctor_set(v_reuseFailAlloc_3544_, 2, v_path_3535_);
lean_ctor_set(v_reuseFailAlloc_3544_, 3, v_query_3536_);
lean_ctor_set(v_reuseFailAlloc_3544_, 4, v_fragment_3537_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withAuthority(lean_object* v_uri_3547_, lean_object* v_authority_3548_){
_start:
{
lean_object* v_scheme_3549_; lean_object* v_path_3550_; lean_object* v_query_3551_; lean_object* v_fragment_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
v_scheme_3549_ = lean_ctor_get(v_uri_3547_, 0);
v_path_3550_ = lean_ctor_get(v_uri_3547_, 2);
v_query_3551_ = lean_ctor_get(v_uri_3547_, 3);
v_fragment_3552_ = lean_ctor_get(v_uri_3547_, 4);
v_isSharedCheck_3559_ = !lean_is_exclusive(v_uri_3547_);
if (v_isSharedCheck_3559_ == 0)
{
lean_object* v_unused_3560_; 
v_unused_3560_ = lean_ctor_get(v_uri_3547_, 1);
lean_dec(v_unused_3560_);
v___x_3554_ = v_uri_3547_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_fragment_3552_);
lean_inc(v_query_3551_);
lean_inc(v_path_3550_);
lean_inc(v_scheme_3549_);
lean_dec(v_uri_3547_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 1, v_authority_3548_);
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_scheme_3549_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v_authority_3548_);
lean_ctor_set(v_reuseFailAlloc_3558_, 2, v_path_3550_);
lean_ctor_set(v_reuseFailAlloc_3558_, 3, v_query_3551_);
lean_ctor_set(v_reuseFailAlloc_3558_, 4, v_fragment_3552_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withPath(lean_object* v_uri_3561_, lean_object* v_path_3562_){
_start:
{
lean_object* v_scheme_3563_; lean_object* v_authority_3564_; lean_object* v_query_3565_; lean_object* v_fragment_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
v_scheme_3563_ = lean_ctor_get(v_uri_3561_, 0);
v_authority_3564_ = lean_ctor_get(v_uri_3561_, 1);
v_query_3565_ = lean_ctor_get(v_uri_3561_, 3);
v_fragment_3566_ = lean_ctor_get(v_uri_3561_, 4);
v_isSharedCheck_3573_ = !lean_is_exclusive(v_uri_3561_);
if (v_isSharedCheck_3573_ == 0)
{
lean_object* v_unused_3574_; 
v_unused_3574_ = lean_ctor_get(v_uri_3561_, 2);
lean_dec(v_unused_3574_);
v___x_3568_ = v_uri_3561_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_fragment_3566_);
lean_inc(v_query_3565_);
lean_inc(v_authority_3564_);
lean_inc(v_scheme_3563_);
lean_dec(v_uri_3561_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
lean_ctor_set(v___x_3568_, 2, v_path_3562_);
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_scheme_3563_);
lean_ctor_set(v_reuseFailAlloc_3572_, 1, v_authority_3564_);
lean_ctor_set(v_reuseFailAlloc_3572_, 2, v_path_3562_);
lean_ctor_set(v_reuseFailAlloc_3572_, 3, v_query_3565_);
lean_ctor_set(v_reuseFailAlloc_3572_, 4, v_fragment_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withQuery(lean_object* v_uri_3575_, lean_object* v_query_3576_){
_start:
{
lean_object* v_scheme_3577_; lean_object* v_authority_3578_; lean_object* v_path_3579_; lean_object* v_fragment_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3588_; 
v_scheme_3577_ = lean_ctor_get(v_uri_3575_, 0);
v_authority_3578_ = lean_ctor_get(v_uri_3575_, 1);
v_path_3579_ = lean_ctor_get(v_uri_3575_, 2);
v_fragment_3580_ = lean_ctor_get(v_uri_3575_, 4);
v_isSharedCheck_3588_ = !lean_is_exclusive(v_uri_3575_);
if (v_isSharedCheck_3588_ == 0)
{
lean_object* v_unused_3589_; 
v_unused_3589_ = lean_ctor_get(v_uri_3575_, 3);
lean_dec(v_unused_3589_);
v___x_3582_ = v_uri_3575_;
v_isShared_3583_ = v_isSharedCheck_3588_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_fragment_3580_);
lean_inc(v_path_3579_);
lean_inc(v_authority_3578_);
lean_inc(v_scheme_3577_);
lean_dec(v_uri_3575_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3588_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3584_; lean_object* v___x_3586_; 
v___x_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3584_, 0, v_query_3576_);
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 3, v___x_3584_);
v___x_3586_ = v___x_3582_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_scheme_3577_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_authority_3578_);
lean_ctor_set(v_reuseFailAlloc_3587_, 2, v_path_3579_);
lean_ctor_set(v_reuseFailAlloc_3587_, 3, v___x_3584_);
lean_ctor_set(v_reuseFailAlloc_3587_, 4, v_fragment_3580_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withFragment(lean_object* v_uri_3590_, lean_object* v_fragment_3591_){
_start:
{
lean_object* v_scheme_3592_; lean_object* v_authority_3593_; lean_object* v_path_3594_; lean_object* v_query_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
v_scheme_3592_ = lean_ctor_get(v_uri_3590_, 0);
v_authority_3593_ = lean_ctor_get(v_uri_3590_, 1);
v_path_3594_ = lean_ctor_get(v_uri_3590_, 2);
v_query_3595_ = lean_ctor_get(v_uri_3590_, 3);
v_isSharedCheck_3602_ = !lean_is_exclusive(v_uri_3590_);
if (v_isSharedCheck_3602_ == 0)
{
lean_object* v_unused_3603_; 
v_unused_3603_ = lean_ctor_get(v_uri_3590_, 4);
lean_dec(v_unused_3603_);
v___x_3597_ = v_uri_3590_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_query_3595_);
lean_inc(v_path_3594_);
lean_inc(v_authority_3593_);
lean_inc(v_scheme_3592_);
lean_dec(v_uri_3590_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 4, v_fragment_3591_);
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_scheme_3592_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_authority_3593_);
lean_ctor_set(v_reuseFailAlloc_3601_, 2, v_path_3594_);
lean_ctor_set(v_reuseFailAlloc_3601_, 3, v_query_3595_);
lean_ctor_set(v_reuseFailAlloc_3601_, 4, v_fragment_3591_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_normalize(lean_object* v_uri_3604_){
_start:
{
lean_object* v_scheme_3605_; lean_object* v_authority_3606_; lean_object* v_path_3607_; lean_object* v_query_3608_; lean_object* v_fragment_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3617_; 
v_scheme_3605_ = lean_ctor_get(v_uri_3604_, 0);
v_authority_3606_ = lean_ctor_get(v_uri_3604_, 1);
v_path_3607_ = lean_ctor_get(v_uri_3604_, 2);
v_query_3608_ = lean_ctor_get(v_uri_3604_, 3);
v_fragment_3609_ = lean_ctor_get(v_uri_3604_, 4);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_uri_3604_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3611_ = v_uri_3604_;
v_isShared_3612_ = v_isSharedCheck_3617_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_fragment_3609_);
lean_inc(v_query_3608_);
lean_inc(v_path_3607_);
lean_inc(v_authority_3606_);
lean_inc(v_scheme_3605_);
lean_dec(v_uri_3604_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3617_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3613_; lean_object* v___x_3615_; 
v___x_3613_ = l_Std_Http_URI_Path_normalize(v_path_3607_);
if (v_isShared_3612_ == 0)
{
lean_ctor_set(v___x_3611_, 2, v___x_3613_);
v___x_3615_ = v___x_3611_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_scheme_3605_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v_authority_3606_);
lean_ctor_set(v_reuseFailAlloc_3616_, 2, v___x_3613_);
lean_ctor_set(v_reuseFailAlloc_3616_, 3, v_query_3608_);
lean_ctor_set(v_reuseFailAlloc_3616_, 4, v_fragment_3609_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___redArg(lean_object* v_x_3618_){
_start:
{
lean_object* v_scheme_3619_; lean_object* v_host_3620_; uint16_t v_port_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; uint8_t v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___y_3640_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v_ctr_3665_; lean_object* v_a_3666_; 
v_scheme_3619_ = lean_ctor_get(v_x_3618_, 0);
lean_inc_ref(v_scheme_3619_);
v_host_3620_ = lean_ctor_get(v_x_3618_, 1);
lean_inc(v_host_3620_);
v_port_3621_ = lean_ctor_get_uint16(v_x_3618_, sizeof(void*)*2);
lean_dec_ref(v_x_3618_);
v___x_3622_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_3623_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_3624_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_3625_ = l_String_quote(v_scheme_3619_);
v___x_3626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3625_);
v___x_3627_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3624_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
v___x_3628_ = 0;
v___x_3629_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3629_, 0, v___x_3627_);
lean_ctor_set_uint8(v___x_3629_, sizeof(void*)*1, v___x_3628_);
v___x_3630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3623_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_3632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3630_);
lean_ctor_set(v___x_3632_, 1, v___x_3631_);
v___x_3633_ = lean_box(1);
v___x_3634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3632_);
lean_ctor_set(v___x_3634_, 1, v___x_3633_);
v___x_3635_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_3636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3634_);
lean_ctor_set(v___x_3636_, 1, v___x_3635_);
v___x_3637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3637_, 0, v___x_3636_);
lean_ctor_set(v___x_3637_, 1, v___x_3622_);
v___x_3638_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_3662_ = lean_unsigned_to_nat(0u);
v___x_3663_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__6, &l_Std_Http_URI_instReprHost___lam__0___closed__6_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__6);
switch(lean_obj_tag(v_host_3620_))
{
case 0:
{
lean_object* v_name_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3684_; 
v_name_3675_ = lean_ctor_get(v_host_3620_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v_host_3620_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3677_ = v_host_3620_;
v_isShared_3678_ = v_isSharedCheck_3684_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_name_3675_);
lean_dec(v_host_3620_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3684_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3682_; 
v___x_3679_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_3680_ = l_String_quote(v_name_3675_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set_tag(v___x_3677_, 3);
lean_ctor_set(v___x_3677_, 0, v___x_3680_);
v___x_3682_ = v___x_3677_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
v_ctr_3665_ = v___x_3679_;
v_a_3666_ = v___x_3682_;
goto v___jp_3664_;
}
}
}
case 1:
{
lean_object* v_ipv4_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3694_; 
v_ipv4_3685_ = lean_ctor_get(v_host_3620_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v_host_3620_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3687_ = v_host_3620_;
v_isShared_3688_ = v_isSharedCheck_3694_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_ipv4_3685_);
lean_dec(v_host_3620_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3694_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3692_; 
v___x_3689_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_3690_ = lean_uv_ntop_v4(v_ipv4_3685_);
lean_dec_ref(v_ipv4_3685_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set_tag(v___x_3687_, 3);
lean_ctor_set(v___x_3687_, 0, v___x_3690_);
v___x_3692_ = v___x_3687_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3690_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
v_ctr_3665_ = v___x_3689_;
v_a_3666_ = v___x_3692_;
goto v___jp_3664_;
}
}
}
case 2:
{
lean_object* v_ipv6_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3704_; 
v_ipv6_3695_ = lean_ctor_get(v_host_3620_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v_host_3620_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3697_ = v_host_3620_;
v_isShared_3698_ = v_isSharedCheck_3704_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_ipv6_3695_);
lean_dec(v_host_3620_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3704_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3702_; 
v___x_3699_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_3700_ = lean_uv_ntop_v6(v_ipv6_3695_);
lean_dec_ref(v_ipv6_3695_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set_tag(v___x_3697_, 3);
lean_ctor_set(v___x_3697_, 0, v___x_3700_);
v___x_3702_ = v___x_3697_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
v_ctr_3665_ = v___x_3699_;
v_a_3666_ = v___x_3702_;
goto v___jp_3664_;
}
}
}
default: 
{
lean_object* v___x_3705_; 
v___x_3705_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__5));
v___y_3640_ = v___x_3705_;
goto v___jp_3639_;
}
}
v___jp_3639_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3641_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3638_);
lean_ctor_set(v___x_3641_, 1, v___y_3640_);
v___x_3642_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
lean_ctor_set_uint8(v___x_3642_, sizeof(void*)*1, v___x_3628_);
v___x_3643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3637_);
lean_ctor_set(v___x_3643_, 1, v___x_3642_);
v___x_3644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
lean_ctor_set(v___x_3644_, 1, v___x_3631_);
v___x_3645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3644_);
lean_ctor_set(v___x_3645_, 1, v___x_3633_);
v___x_3646_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_3647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3645_);
lean_ctor_set(v___x_3647_, 1, v___x_3646_);
v___x_3648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3647_);
lean_ctor_set(v___x_3648_, 1, v___x_3622_);
v___x_3649_ = lean_uint16_to_nat(v_port_3621_);
v___x_3650_ = l_Nat_reprFast(v___x_3649_);
v___x_3651_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3650_);
v___x_3652_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3638_);
lean_ctor_set(v___x_3652_, 1, v___x_3651_);
v___x_3653_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
lean_ctor_set_uint8(v___x_3653_, sizeof(void*)*1, v___x_3628_);
v___x_3654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3648_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
v___x_3655_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_3656_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_3657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
lean_ctor_set(v___x_3657_, 1, v___x_3654_);
v___x_3658_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_3659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3657_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3655_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
lean_ctor_set_uint8(v___x_3661_, sizeof(void*)*1, v___x_3628_);
return v___x_3661_;
}
v___jp_3664_:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3667_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_3668_ = lean_string_append(v___x_3667_, v_ctr_3665_);
v___x_3669_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
v___x_3670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
lean_ctor_set(v___x_3670_, 1, v___x_3633_);
v___x_3671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3670_);
lean_ctor_set(v___x_3671_, 1, v_a_3666_);
v___x_3672_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3663_);
lean_ctor_set(v___x_3672_, 1, v___x_3671_);
v___x_3673_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3673_, 0, v___x_3672_);
lean_ctor_set_uint8(v___x_3673_, sizeof(void*)*1, v___x_3628_);
v___x_3674_ = l_Repr_addAppParen(v___x_3673_, v___x_3662_);
v___y_3640_ = v___x_3674_;
goto v___jp_3639_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr(lean_object* v_x_3706_, lean_object* v_prec_3707_){
_start:
{
lean_object* v___x_3708_; 
v___x_3708_ = l_Std_Http_URI_instReprOrigin_repr___redArg(v_x_3706_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___boxed(lean_object* v_x_3709_, lean_object* v_prec_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Std_Http_URI_instReprOrigin_repr(v_x_3709_, v_prec_3710_);
lean_dec(v_prec_3710_);
return v_res_3711_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqOrigin_beq(lean_object* v_x_3714_, lean_object* v_x_3715_){
_start:
{
lean_object* v_scheme_3716_; lean_object* v_host_3717_; uint16_t v_port_3718_; lean_object* v_scheme_3719_; lean_object* v_host_3720_; uint16_t v_port_3721_; uint8_t v___x_3722_; 
v_scheme_3716_ = lean_ctor_get(v_x_3714_, 0);
v_host_3717_ = lean_ctor_get(v_x_3714_, 1);
v_port_3718_ = lean_ctor_get_uint16(v_x_3714_, sizeof(void*)*2);
v_scheme_3719_ = lean_ctor_get(v_x_3715_, 0);
v_host_3720_ = lean_ctor_get(v_x_3715_, 1);
v_port_3721_ = lean_ctor_get_uint16(v_x_3715_, sizeof(void*)*2);
v___x_3722_ = lean_string_dec_eq(v_scheme_3716_, v_scheme_3719_);
if (v___x_3722_ == 0)
{
return v___x_3722_;
}
else
{
uint8_t v___x_3723_; 
v___x_3723_ = l_Std_Http_URI_instBEqHost_beq(v_host_3717_, v_host_3720_);
if (v___x_3723_ == 0)
{
return v___x_3723_;
}
else
{
uint8_t v___x_3724_; 
v___x_3724_ = lean_uint16_dec_eq(v_port_3718_, v_port_3721_);
return v___x_3724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqOrigin_beq___boxed(lean_object* v_x_3725_, lean_object* v_x_3726_){
_start:
{
uint8_t v_res_3727_; lean_object* v_r_3728_; 
v_res_3727_ = l_Std_Http_URI_instBEqOrigin_beq(v_x_3725_, v_x_3726_);
lean_dec_ref(v_x_3726_);
lean_dec_ref(v_x_3725_);
v_r_3728_ = lean_box(v_res_3727_);
return v_r_3728_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Origin_hostHeader(lean_object* v_o_3731_){
_start:
{
lean_object* v_scheme_3732_; lean_object* v_host_3733_; uint16_t v_port_3734_; lean_object* v___y_3736_; uint16_t v_defaultPort_3742_; uint8_t v___x_3743_; 
v_scheme_3732_ = lean_ctor_get(v_o_3731_, 0);
lean_inc_ref(v_scheme_3732_);
v_host_3733_ = lean_ctor_get(v_o_3731_, 1);
lean_inc(v_host_3733_);
v_port_3734_ = lean_ctor_get_uint16(v_o_3731_, sizeof(void*)*2);
lean_dec_ref(v_o_3731_);
v_defaultPort_3742_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_3732_);
lean_dec_ref(v_scheme_3732_);
v___x_3743_ = lean_uint16_dec_eq(v_port_3734_, v_defaultPort_3742_);
if (v___x_3743_ == 0)
{
switch(lean_obj_tag(v_host_3733_))
{
case 0:
{
lean_object* v_name_3744_; 
v_name_3744_ = lean_ctor_get(v_host_3733_, 0);
lean_inc_ref(v_name_3744_);
lean_dec_ref_known(v_host_3733_, 1);
v___y_3736_ = v_name_3744_;
goto v___jp_3735_;
}
case 1:
{
lean_object* v_ipv4_3745_; lean_object* v___x_3746_; 
v_ipv4_3745_ = lean_ctor_get(v_host_3733_, 0);
lean_inc_ref(v_ipv4_3745_);
lean_dec_ref_known(v_host_3733_, 1);
v___x_3746_ = lean_uv_ntop_v4(v_ipv4_3745_);
lean_dec_ref(v_ipv4_3745_);
v___y_3736_ = v___x_3746_;
goto v___jp_3735_;
}
case 2:
{
lean_object* v_ipv6_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v_ipv6_3747_ = lean_ctor_get(v_host_3733_, 0);
lean_inc_ref(v_ipv6_3747_);
lean_dec_ref_known(v_host_3733_, 1);
v___x_3748_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3749_ = lean_uv_ntop_v6(v_ipv6_3747_);
lean_dec_ref(v_ipv6_3747_);
v___x_3750_ = lean_string_append(v___x_3748_, v___x_3749_);
lean_dec_ref(v___x_3749_);
v___x_3751_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3752_ = lean_string_append(v___x_3750_, v___x_3751_);
v___y_3736_ = v___x_3752_;
goto v___jp_3735_;
}
default: 
{
lean_object* v___x_3753_; 
v___x_3753_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_3736_ = v___x_3753_;
goto v___jp_3735_;
}
}
}
else
{
switch(lean_obj_tag(v_host_3733_))
{
case 0:
{
lean_object* v_name_3754_; 
v_name_3754_ = lean_ctor_get(v_host_3733_, 0);
lean_inc_ref(v_name_3754_);
lean_dec_ref_known(v_host_3733_, 1);
return v_name_3754_;
}
case 1:
{
lean_object* v_ipv4_3755_; lean_object* v___x_3756_; 
v_ipv4_3755_ = lean_ctor_get(v_host_3733_, 0);
lean_inc_ref(v_ipv4_3755_);
lean_dec_ref_known(v_host_3733_, 1);
v___x_3756_ = lean_uv_ntop_v4(v_ipv4_3755_);
lean_dec_ref(v_ipv4_3755_);
return v___x_3756_;
}
case 2:
{
lean_object* v_ipv6_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v_ipv6_3757_ = lean_ctor_get(v_host_3733_, 0);
lean_inc_ref(v_ipv6_3757_);
lean_dec_ref_known(v_host_3733_, 1);
v___x_3758_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3759_ = lean_uv_ntop_v6(v_ipv6_3757_);
lean_dec_ref(v_ipv6_3757_);
v___x_3760_ = lean_string_append(v___x_3758_, v___x_3759_);
lean_dec_ref(v___x_3759_);
v___x_3761_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3762_ = lean_string_append(v___x_3760_, v___x_3761_);
return v___x_3762_;
}
default: 
{
lean_object* v___x_3763_; 
v___x_3763_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
return v___x_3763_;
}
}
}
v___jp_3735_:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3737_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_3738_ = lean_string_append(v___y_3736_, v___x_3737_);
v___x_3739_ = lean_uint16_to_nat(v_port_3734_);
v___x_3740_ = l_Nat_reprFast(v___x_3739_);
v___x_3741_ = lean_string_append(v___x_3738_, v___x_3740_);
lean_dec_ref(v___x_3740_);
return v___x_3741_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___redArg(lean_object* v_x_3770_){
_start:
{
lean_object* v_authority_3771_; lean_object* v_path_3772_; lean_object* v_query_3773_; lean_object* v_fragment_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; uint8_t v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v_authority_3771_ = lean_ctor_get(v_x_3770_, 0);
lean_inc(v_authority_3771_);
v_path_3772_ = lean_ctor_get(v_x_3770_, 1);
lean_inc_ref(v_path_3772_);
v_query_3773_ = lean_ctor_get(v_x_3770_, 2);
lean_inc(v_query_3773_);
v_fragment_3774_ = lean_ctor_get(v_x_3770_, 3);
lean_inc(v_fragment_3774_);
lean_dec_ref(v_x_3770_);
v___x_3775_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_3776_ = ((lean_object*)(l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__1));
v___x_3777_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_3778_ = lean_unsigned_to_nat(0u);
v___x_3779_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_3771_, v___x_3778_);
v___x_3780_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3777_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
v___x_3781_ = 0;
v___x_3782_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3782_, 0, v___x_3780_);
lean_ctor_set_uint8(v___x_3782_, sizeof(void*)*1, v___x_3781_);
v___x_3783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3776_);
lean_ctor_set(v___x_3783_, 1, v___x_3782_);
v___x_3784_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_3785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3783_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = lean_box(1);
v___x_3787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3785_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_3789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3787_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
v___x_3790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
lean_ctor_set(v___x_3790_, 1, v___x_3775_);
v___x_3791_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_3792_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3772_);
v___x_3793_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3791_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
v___x_3794_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
lean_ctor_set_uint8(v___x_3794_, sizeof(void*)*1, v___x_3781_);
v___x_3795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3790_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v___x_3796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
lean_ctor_set(v___x_3796_, 1, v___x_3784_);
v___x_3797_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
lean_ctor_set(v___x_3797_, 1, v___x_3786_);
v___x_3798_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_3799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3797_);
lean_ctor_set(v___x_3799_, 1, v___x_3798_);
v___x_3800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3799_);
lean_ctor_set(v___x_3800_, 1, v___x_3775_);
v___x_3801_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_3802_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3773_, v___x_3778_);
v___x_3803_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3801_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
v___x_3804_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3804_, 0, v___x_3803_);
lean_ctor_set_uint8(v___x_3804_, sizeof(void*)*1, v___x_3781_);
v___x_3805_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3800_);
lean_ctor_set(v___x_3805_, 1, v___x_3804_);
v___x_3806_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
lean_ctor_set(v___x_3806_, 1, v___x_3784_);
v___x_3807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3806_);
lean_ctor_set(v___x_3807_, 1, v___x_3786_);
v___x_3808_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_3809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
lean_ctor_set(v___x_3810_, 1, v___x_3775_);
v___x_3811_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_3812_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_3774_, v___x_3778_);
v___x_3813_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3811_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___x_3814_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
lean_ctor_set_uint8(v___x_3814_, sizeof(void*)*1, v___x_3781_);
v___x_3815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3810_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___x_3816_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_3817_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_3818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3817_);
lean_ctor_set(v___x_3818_, 1, v___x_3815_);
v___x_3819_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_3820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3818_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___x_3821_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3816_);
lean_ctor_set(v___x_3821_, 1, v___x_3820_);
v___x_3822_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
lean_ctor_set_uint8(v___x_3822_, sizeof(void*)*1, v___x_3781_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr(lean_object* v_x_3823_, lean_object* v_prec_3824_){
_start:
{
lean_object* v___x_3825_; 
v___x_3825_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_x_3823_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___boxed(lean_object* v_x_3826_, lean_object* v_prec_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l_Std_Http_URI_instReprRelativeRef_repr(v_x_3826_, v_prec_3827_);
lean_dec(v_prec_3827_);
return v_res_3828_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqRelativeRef_beq(lean_object* v_x_3836_, lean_object* v_x_3837_){
_start:
{
lean_object* v_authority_3838_; lean_object* v_path_3839_; lean_object* v_query_3840_; lean_object* v_fragment_3841_; lean_object* v_authority_3842_; lean_object* v_path_3843_; lean_object* v_query_3844_; lean_object* v_fragment_3845_; uint8_t v___x_3846_; 
v_authority_3838_ = lean_ctor_get(v_x_3836_, 0);
v_path_3839_ = lean_ctor_get(v_x_3836_, 1);
v_query_3840_ = lean_ctor_get(v_x_3836_, 2);
v_fragment_3841_ = lean_ctor_get(v_x_3836_, 3);
v_authority_3842_ = lean_ctor_get(v_x_3837_, 0);
v_path_3843_ = lean_ctor_get(v_x_3837_, 1);
v_query_3844_ = lean_ctor_get(v_x_3837_, 2);
v_fragment_3845_ = lean_ctor_get(v_x_3837_, 3);
v___x_3846_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_3838_, v_authority_3842_);
if (v___x_3846_ == 0)
{
return v___x_3846_;
}
else
{
uint8_t v___x_3847_; 
v___x_3847_ = l_Std_Http_URI_instBEqPath_beq(v_path_3839_, v_path_3843_);
if (v___x_3847_ == 0)
{
return v___x_3847_;
}
else
{
uint8_t v___x_3848_; 
v___x_3848_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_3840_, v_query_3844_);
if (v___x_3848_ == 0)
{
return v___x_3848_;
}
else
{
uint8_t v___x_3849_; 
v___x_3849_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_3841_, v_fragment_3845_);
return v___x_3849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqRelativeRef_beq___boxed(lean_object* v_x_3850_, lean_object* v_x_3851_){
_start:
{
uint8_t v_res_3852_; lean_object* v_r_3853_; 
v_res_3852_ = l_Std_Http_URI_instBEqRelativeRef_beq(v_x_3850_, v_x_3851_);
lean_dec_ref(v_x_3851_);
lean_dec_ref(v_x_3850_);
v_r_3853_ = lean_box(v_res_3852_);
return v_r_3853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringRelativeRef___lam__0(lean_object* v_ref_3856_){
_start:
{
lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v_authority_3865_; lean_object* v_path_3866_; lean_object* v_query_3867_; lean_object* v_fragment_3868_; lean_object* v___y_3870_; uint8_t v___y_3871_; lean_object* v___y_3882_; 
v_authority_3865_ = lean_ctor_get(v_ref_3856_, 0);
lean_inc(v_authority_3865_);
v_path_3866_ = lean_ctor_get(v_ref_3856_, 1);
lean_inc_ref(v_path_3866_);
v_query_3867_ = lean_ctor_get(v_ref_3856_, 2);
lean_inc(v_query_3867_);
v_fragment_3868_ = lean_ctor_get(v_ref_3856_, 3);
lean_inc(v_fragment_3868_);
lean_dec_ref(v_ref_3856_);
if (lean_obj_tag(v_authority_3865_) == 0)
{
lean_object* v___x_3885_; 
v___x_3885_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_3882_ = v___x_3885_;
goto v___jp_3881_;
}
else
{
lean_object* v_val_3886_; lean_object* v_userInfo_3887_; lean_object* v_host_3888_; lean_object* v_port_3889_; lean_object* v___x_3890_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3909_; 
v_val_3886_ = lean_ctor_get(v_authority_3865_, 0);
v_userInfo_3887_ = lean_ctor_get(v_val_3886_, 0);
v_host_3888_ = lean_ctor_get(v_val_3886_, 1);
v_port_3889_ = lean_ctor_get(v_val_3886_, 2);
v___x_3890_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__1));
if (lean_obj_tag(v_userInfo_3887_) == 0)
{
lean_object* v___x_3920_; 
v___x_3920_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_3909_ = v___x_3920_;
goto v___jp_3908_;
}
else
{
lean_object* v_val_3921_; lean_object* v_password_3922_; 
v_val_3921_ = lean_ctor_get(v_userInfo_3887_, 0);
v_password_3922_ = lean_ctor_get(v_val_3921_, 1);
if (lean_obj_tag(v_password_3922_) == 0)
{
lean_object* v_username_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v_username_3923_ = lean_ctor_get(v_val_3921_, 0);
lean_inc_ref(v_username_3923_);
v___x_3924_ = lean_string_from_utf8_unchecked(v_username_3923_);
v___x_3925_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3926_ = lean_string_append(v___x_3924_, v___x_3925_);
v___y_3909_ = v___x_3926_;
goto v___jp_3908_;
}
else
{
lean_object* v_username_3927_; lean_object* v_val_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v_username_3927_ = lean_ctor_get(v_val_3921_, 0);
v_val_3928_ = lean_ctor_get(v_password_3922_, 0);
lean_inc_ref(v_username_3927_);
v___x_3929_ = lean_string_from_utf8_unchecked(v_username_3927_);
v___x_3930_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_3931_ = lean_string_append(v___x_3929_, v___x_3930_);
lean_inc(v_val_3928_);
v___x_3932_ = lean_string_from_utf8_unchecked(v_val_3928_);
v___x_3933_ = lean_string_append(v___x_3931_, v___x_3932_);
lean_dec_ref(v___x_3932_);
v___x_3934_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3935_ = lean_string_append(v___x_3933_, v___x_3934_);
v___y_3909_ = v___x_3935_;
goto v___jp_3908_;
}
}
v___jp_3891_:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3895_ = lean_string_append(v___y_3892_, v___y_3893_);
lean_dec_ref(v___y_3893_);
v___x_3896_ = lean_string_append(v___x_3895_, v___y_3894_);
lean_dec_ref(v___y_3894_);
v___x_3897_ = lean_string_append(v___x_3890_, v___x_3896_);
lean_dec_ref(v___x_3896_);
v___y_3882_ = v___x_3897_;
goto v___jp_3881_;
}
v___jp_3898_:
{
switch(lean_obj_tag(v_port_3889_))
{
case 0:
{
lean_object* v___x_3901_; 
v___x_3901_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_3892_ = v___y_3899_;
v___y_3893_ = v___y_3900_;
v___y_3894_ = v___x_3901_;
goto v___jp_3891_;
}
case 1:
{
lean_object* v___x_3902_; 
v___x_3902_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3892_ = v___y_3899_;
v___y_3893_ = v___y_3900_;
v___y_3894_ = v___x_3902_;
goto v___jp_3891_;
}
default: 
{
uint16_t v_port_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_port_3903_ = lean_ctor_get_uint16(v_port_3889_, 0);
v___x_3904_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_3905_ = lean_uint16_to_nat(v_port_3903_);
v___x_3906_ = l_Nat_reprFast(v___x_3905_);
v___x_3907_ = lean_string_append(v___x_3904_, v___x_3906_);
lean_dec_ref(v___x_3906_);
v___y_3892_ = v___y_3899_;
v___y_3893_ = v___y_3900_;
v___y_3894_ = v___x_3907_;
goto v___jp_3891_;
}
}
}
v___jp_3908_:
{
switch(lean_obj_tag(v_host_3888_))
{
case 0:
{
lean_object* v_name_3910_; 
v_name_3910_ = lean_ctor_get(v_host_3888_, 0);
lean_inc_ref(v_name_3910_);
v___y_3899_ = v___y_3909_;
v___y_3900_ = v_name_3910_;
goto v___jp_3898_;
}
case 1:
{
lean_object* v_ipv4_3911_; lean_object* v___x_3912_; 
v_ipv4_3911_ = lean_ctor_get(v_host_3888_, 0);
v___x_3912_ = lean_uv_ntop_v4(v_ipv4_3911_);
v___y_3899_ = v___y_3909_;
v___y_3900_ = v___x_3912_;
goto v___jp_3898_;
}
case 2:
{
lean_object* v_ipv6_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v_ipv6_3913_ = lean_ctor_get(v_host_3888_, 0);
v___x_3914_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3915_ = lean_uv_ntop_v6(v_ipv6_3913_);
v___x_3916_ = lean_string_append(v___x_3914_, v___x_3915_);
lean_dec_ref(v___x_3915_);
v___x_3917_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3918_ = lean_string_append(v___x_3916_, v___x_3917_);
v___y_3899_ = v___y_3909_;
v___y_3900_ = v___x_3918_;
goto v___jp_3898_;
}
default: 
{
lean_object* v___x_3919_; 
v___x_3919_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_3899_ = v___y_3909_;
v___y_3900_ = v___x_3919_;
goto v___jp_3898_;
}
}
}
}
v___jp_3857_:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3862_ = lean_string_append(v___y_3859_, v___y_3858_);
lean_dec_ref(v___y_3858_);
v___x_3863_ = lean_string_append(v___x_3862_, v___y_3860_);
lean_dec_ref(v___y_3860_);
v___x_3864_ = lean_string_append(v___x_3863_, v___y_3861_);
lean_dec_ref(v___y_3861_);
return v___x_3864_;
}
v___jp_3869_:
{
uint8_t v___x_3872_; lean_object* v_pathPart_3873_; lean_object* v_queryPart_3874_; 
v___x_3872_ = 0;
v_pathPart_3873_ = l_Std_Http_URI_Path_render(v_path_3866_, v___y_3871_, v___x_3872_);
v_queryPart_3874_ = l_Std_Http_URI_Query_formatOption(v_query_3867_);
if (lean_obj_tag(v_fragment_3868_) == 0)
{
lean_object* v___x_3875_; 
v___x_3875_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_3858_ = v_pathPart_3873_;
v___y_3859_ = v___y_3870_;
v___y_3860_ = v_queryPart_3874_;
v___y_3861_ = v___x_3875_;
goto v___jp_3857_;
}
else
{
lean_object* v_val_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v_val_3876_ = lean_ctor_get(v_fragment_3868_, 0);
lean_inc(v_val_3876_);
lean_dec_ref_known(v_fragment_3868_, 1);
v___x_3877_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__0));
v___x_3878_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3876_);
v___x_3879_ = lean_string_from_utf8_unchecked(v___x_3878_);
v___x_3880_ = lean_string_append(v___x_3877_, v___x_3879_);
lean_dec_ref(v___x_3879_);
v___y_3858_ = v_pathPart_3873_;
v___y_3859_ = v___y_3870_;
v___y_3860_ = v_queryPart_3874_;
v___y_3861_ = v___x_3880_;
goto v___jp_3857_;
}
}
v___jp_3881_:
{
if (lean_obj_tag(v_authority_3865_) == 0)
{
uint8_t v___x_3883_; 
v___x_3883_ = 0;
v___y_3870_ = v___y_3882_;
v___y_3871_ = v___x_3883_;
goto v___jp_3869_;
}
else
{
uint8_t v___x_3884_; 
lean_dec_ref_known(v_authority_3865_, 1);
v___x_3884_ = 1;
v___y_3870_ = v___y_3882_;
v___y_3871_ = v___x_3884_;
goto v___jp_3869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___impl(lean_object* v_x_3938_){
_start:
{
lean_object* v___x_3939_; 
v___x_3939_ = lean_obj_tag_nat(v_x_3938_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___impl___boxed(lean_object* v_x_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l_Std_Http_URIReference_ctorIdx___impl(v_x_3940_);
lean_dec_ref(v_x_3940_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___redArg(lean_object* v_t_3942_, lean_object* v_k_3943_){
_start:
{
lean_object* v_uri_3944_; lean_object* v___x_3945_; 
v_uri_3944_ = lean_ctor_get(v_t_3942_, 0);
lean_inc_ref(v_uri_3944_);
lean_dec_ref(v_t_3942_);
v___x_3945_ = lean_apply_1(v_k_3943_, v_uri_3944_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim(lean_object* v_motive_3946_, lean_object* v_ctorIdx_3947_, lean_object* v_t_3948_, lean_object* v_h_3949_, lean_object* v_k_3950_){
_start:
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3948_, v_k_3950_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___boxed(lean_object* v_motive_3952_, lean_object* v_ctorIdx_3953_, lean_object* v_t_3954_, lean_object* v_h_3955_, lean_object* v_k_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l_Std_Http_URIReference_ctorElim(v_motive_3952_, v_ctorIdx_3953_, v_t_3954_, v_h_3955_, v_k_3956_);
lean_dec(v_ctorIdx_3953_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim___redArg(lean_object* v_t_3958_, lean_object* v_absolute_3959_){
_start:
{
lean_object* v___x_3960_; 
v___x_3960_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3958_, v_absolute_3959_);
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim(lean_object* v_motive_3961_, lean_object* v_t_3962_, lean_object* v_h_3963_, lean_object* v_absolute_3964_){
_start:
{
lean_object* v___x_3965_; 
v___x_3965_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3962_, v_absolute_3964_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim___redArg(lean_object* v_t_3966_, lean_object* v_relative_3967_){
_start:
{
lean_object* v___x_3968_; 
v___x_3968_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3966_, v_relative_3967_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim(lean_object* v_motive_3969_, lean_object* v_t_3970_, lean_object* v_h_3971_, lean_object* v_relative_3972_){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3970_, v_relative_3972_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr(lean_object* v_x_3986_, lean_object* v_prec_3987_){
_start:
{
if (lean_obj_tag(v_x_3986_) == 0)
{
lean_object* v_uri_3988_; lean_object* v___y_3990_; lean_object* v___x_3998_; uint8_t v___x_3999_; 
v_uri_3988_ = lean_ctor_get(v_x_3986_, 0);
lean_inc_ref(v_uri_3988_);
lean_dec_ref_known(v_x_3986_, 1);
v___x_3998_ = lean_unsigned_to_nat(1024u);
v___x_3999_ = lean_nat_dec_le(v___x_3998_, v_prec_3987_);
if (v___x_3999_ == 0)
{
lean_object* v___x_4000_; 
v___x_4000_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__6, &l_Std_Http_URI_instReprHost___lam__0___closed__6_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__6);
v___y_3990_ = v___x_4000_;
goto v___jp_3989_;
}
else
{
lean_object* v___x_4001_; 
v___x_4001_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__7, &l_Std_Http_URI_instReprHost___lam__0___closed__7_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__7);
v___y_3990_ = v___x_4001_;
goto v___jp_3989_;
}
v___jp_3989_:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; uint8_t v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3991_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__2));
v___x_3992_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3988_);
v___x_3993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3991_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
lean_inc(v___y_3990_);
v___x_3994_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___y_3990_);
lean_ctor_set(v___x_3994_, 1, v___x_3993_);
v___x_3995_ = 0;
v___x_3996_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3996_, 0, v___x_3994_);
lean_ctor_set_uint8(v___x_3996_, sizeof(void*)*1, v___x_3995_);
v___x_3997_ = l_Repr_addAppParen(v___x_3996_, v_prec_3987_);
return v___x_3997_;
}
}
else
{
lean_object* v_ref_4002_; lean_object* v___y_4004_; lean_object* v___x_4012_; uint8_t v___x_4013_; 
v_ref_4002_ = lean_ctor_get(v_x_3986_, 0);
lean_inc_ref(v_ref_4002_);
lean_dec_ref_known(v_x_3986_, 1);
v___x_4012_ = lean_unsigned_to_nat(1024u);
v___x_4013_ = lean_nat_dec_le(v___x_4012_, v_prec_3987_);
if (v___x_4013_ == 0)
{
lean_object* v___x_4014_; 
v___x_4014_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__6, &l_Std_Http_URI_instReprHost___lam__0___closed__6_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__6);
v___y_4004_ = v___x_4014_;
goto v___jp_4003_;
}
else
{
lean_object* v___x_4015_; 
v___x_4015_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__7, &l_Std_Http_URI_instReprHost___lam__0___closed__7_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__7);
v___y_4004_ = v___x_4015_;
goto v___jp_4003_;
}
v___jp_4003_:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; uint8_t v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4005_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__5));
v___x_4006_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_ref_4002_);
v___x_4007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4005_);
lean_ctor_set(v___x_4007_, 1, v___x_4006_);
lean_inc(v___y_4004_);
v___x_4008_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4008_, 0, v___y_4004_);
lean_ctor_set(v___x_4008_, 1, v___x_4007_);
v___x_4009_ = 0;
v___x_4010_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4010_, 0, v___x_4008_);
lean_ctor_set_uint8(v___x_4010_, sizeof(void*)*1, v___x_4009_);
v___x_4011_ = l_Repr_addAppParen(v___x_4010_, v_prec_3987_);
return v___x_4011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr___boxed(lean_object* v_x_4016_, lean_object* v_prec_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Std_Http_instReprURIReference_repr(v_x_4016_, v_prec_4017_);
lean_dec(v_prec_4017_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURIReference___lam__0(lean_object* v_x_4025_){
_start:
{
lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; 
if (lean_obj_tag(v_x_4025_) == 0)
{
lean_object* v_uri_4034_; lean_object* v_scheme_4035_; lean_object* v_authority_4036_; lean_object* v_path_4037_; lean_object* v_query_4038_; lean_object* v_fragment_4039_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4052_; uint8_t v___y_4053_; lean_object* v___y_4064_; 
v_uri_4034_ = lean_ctor_get(v_x_4025_, 0);
lean_inc_ref(v_uri_4034_);
lean_dec_ref_known(v_x_4025_, 1);
v_scheme_4035_ = lean_ctor_get(v_uri_4034_, 0);
lean_inc_ref(v_scheme_4035_);
v_authority_4036_ = lean_ctor_get(v_uri_4034_, 1);
lean_inc(v_authority_4036_);
v_path_4037_ = lean_ctor_get(v_uri_4034_, 2);
lean_inc_ref(v_path_4037_);
v_query_4038_ = lean_ctor_get(v_uri_4034_, 3);
lean_inc(v_query_4038_);
v_fragment_4039_ = lean_ctor_get(v_uri_4034_, 4);
lean_inc(v_fragment_4039_);
lean_dec_ref(v_uri_4034_);
if (lean_obj_tag(v_authority_4036_) == 0)
{
lean_object* v___x_4067_; 
v___x_4067_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_4064_ = v___x_4067_;
goto v___jp_4063_;
}
else
{
lean_object* v_val_4068_; lean_object* v_userInfo_4069_; lean_object* v_host_4070_; lean_object* v_port_4071_; lean_object* v___x_4072_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4091_; 
v_val_4068_ = lean_ctor_get(v_authority_4036_, 0);
v_userInfo_4069_ = lean_ctor_get(v_val_4068_, 0);
v_host_4070_ = lean_ctor_get(v_val_4068_, 1);
v_port_4071_ = lean_ctor_get(v_val_4068_, 2);
v___x_4072_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__1));
if (lean_obj_tag(v_userInfo_4069_) == 0)
{
lean_object* v___x_4102_; 
v___x_4102_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_4091_ = v___x_4102_;
goto v___jp_4090_;
}
else
{
lean_object* v_val_4103_; lean_object* v_password_4104_; 
v_val_4103_ = lean_ctor_get(v_userInfo_4069_, 0);
v_password_4104_ = lean_ctor_get(v_val_4103_, 1);
if (lean_obj_tag(v_password_4104_) == 0)
{
lean_object* v_username_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v_username_4105_ = lean_ctor_get(v_val_4103_, 0);
lean_inc_ref(v_username_4105_);
v___x_4106_ = lean_string_from_utf8_unchecked(v_username_4105_);
v___x_4107_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4108_ = lean_string_append(v___x_4106_, v___x_4107_);
v___y_4091_ = v___x_4108_;
goto v___jp_4090_;
}
else
{
lean_object* v_username_4109_; lean_object* v_val_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v_username_4109_ = lean_ctor_get(v_val_4103_, 0);
v_val_4110_ = lean_ctor_get(v_password_4104_, 0);
lean_inc_ref(v_username_4109_);
v___x_4111_ = lean_string_from_utf8_unchecked(v_username_4109_);
v___x_4112_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_4113_ = lean_string_append(v___x_4111_, v___x_4112_);
lean_inc(v_val_4110_);
v___x_4114_ = lean_string_from_utf8_unchecked(v_val_4110_);
v___x_4115_ = lean_string_append(v___x_4113_, v___x_4114_);
lean_dec_ref(v___x_4114_);
v___x_4116_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4117_ = lean_string_append(v___x_4115_, v___x_4116_);
v___y_4091_ = v___x_4117_;
goto v___jp_4090_;
}
}
v___jp_4073_:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4077_ = lean_string_append(v___y_4074_, v___y_4075_);
lean_dec_ref(v___y_4075_);
v___x_4078_ = lean_string_append(v___x_4077_, v___y_4076_);
lean_dec_ref(v___y_4076_);
v___x_4079_ = lean_string_append(v___x_4072_, v___x_4078_);
lean_dec_ref(v___x_4078_);
v___y_4064_ = v___x_4079_;
goto v___jp_4063_;
}
v___jp_4080_:
{
switch(lean_obj_tag(v_port_4071_))
{
case 0:
{
lean_object* v___x_4083_; 
v___x_4083_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_4074_ = v___y_4081_;
v___y_4075_ = v___y_4082_;
v___y_4076_ = v___x_4083_;
goto v___jp_4073_;
}
case 1:
{
lean_object* v___x_4084_; 
v___x_4084_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4074_ = v___y_4081_;
v___y_4075_ = v___y_4082_;
v___y_4076_ = v___x_4084_;
goto v___jp_4073_;
}
default: 
{
uint16_t v_port_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v_port_4085_ = lean_ctor_get_uint16(v_port_4071_, 0);
v___x_4086_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_4087_ = lean_uint16_to_nat(v_port_4085_);
v___x_4088_ = l_Nat_reprFast(v___x_4087_);
v___x_4089_ = lean_string_append(v___x_4086_, v___x_4088_);
lean_dec_ref(v___x_4088_);
v___y_4074_ = v___y_4081_;
v___y_4075_ = v___y_4082_;
v___y_4076_ = v___x_4089_;
goto v___jp_4073_;
}
}
}
v___jp_4090_:
{
switch(lean_obj_tag(v_host_4070_))
{
case 0:
{
lean_object* v_name_4092_; 
v_name_4092_ = lean_ctor_get(v_host_4070_, 0);
lean_inc_ref(v_name_4092_);
v___y_4081_ = v___y_4091_;
v___y_4082_ = v_name_4092_;
goto v___jp_4080_;
}
case 1:
{
lean_object* v_ipv4_4093_; lean_object* v___x_4094_; 
v_ipv4_4093_ = lean_ctor_get(v_host_4070_, 0);
v___x_4094_ = lean_uv_ntop_v4(v_ipv4_4093_);
v___y_4081_ = v___y_4091_;
v___y_4082_ = v___x_4094_;
goto v___jp_4080_;
}
case 2:
{
lean_object* v_ipv6_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v_ipv6_4095_ = lean_ctor_get(v_host_4070_, 0);
v___x_4096_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4097_ = lean_uv_ntop_v6(v_ipv6_4095_);
v___x_4098_ = lean_string_append(v___x_4096_, v___x_4097_);
lean_dec_ref(v___x_4097_);
v___x_4099_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4100_ = lean_string_append(v___x_4098_, v___x_4099_);
v___y_4081_ = v___y_4091_;
v___y_4082_ = v___x_4100_;
goto v___jp_4080_;
}
default: 
{
lean_object* v___x_4101_; 
v___x_4101_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_4081_ = v___y_4091_;
v___y_4082_ = v___x_4101_;
goto v___jp_4080_;
}
}
}
}
v___jp_4040_:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4045_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_4046_ = lean_string_append(v_scheme_4035_, v___x_4045_);
v___x_4047_ = lean_string_append(v___x_4046_, v___y_4042_);
lean_dec_ref(v___y_4042_);
v___x_4048_ = lean_string_append(v___x_4047_, v___y_4043_);
lean_dec_ref(v___y_4043_);
v___x_4049_ = lean_string_append(v___x_4048_, v___y_4041_);
lean_dec_ref(v___y_4041_);
v___x_4050_ = lean_string_append(v___x_4049_, v___y_4044_);
lean_dec_ref(v___y_4044_);
return v___x_4050_;
}
v___jp_4051_:
{
uint8_t v___x_4054_; lean_object* v_pathPart_4055_; lean_object* v_queryPart_4056_; 
v___x_4054_ = 1;
v_pathPart_4055_ = l_Std_Http_URI_Path_render(v_path_4037_, v___y_4053_, v___x_4054_);
v_queryPart_4056_ = l_Std_Http_URI_Query_formatOption(v_query_4038_);
if (lean_obj_tag(v_fragment_4039_) == 0)
{
lean_object* v___x_4057_; 
v___x_4057_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_4041_ = v_queryPart_4056_;
v___y_4042_ = v___y_4052_;
v___y_4043_ = v_pathPart_4055_;
v___y_4044_ = v___x_4057_;
goto v___jp_4040_;
}
else
{
lean_object* v_val_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v_val_4058_ = lean_ctor_get(v_fragment_4039_, 0);
lean_inc(v_val_4058_);
lean_dec_ref_known(v_fragment_4039_, 1);
v___x_4059_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__0));
v___x_4060_ = l_Std_Http_URI_EncodedFragment_encode(v_val_4058_);
v___x_4061_ = lean_string_from_utf8_unchecked(v___x_4060_);
v___x_4062_ = lean_string_append(v___x_4059_, v___x_4061_);
lean_dec_ref(v___x_4061_);
v___y_4041_ = v_queryPart_4056_;
v___y_4042_ = v___y_4052_;
v___y_4043_ = v_pathPart_4055_;
v___y_4044_ = v___x_4062_;
goto v___jp_4040_;
}
}
v___jp_4063_:
{
if (lean_obj_tag(v_authority_4036_) == 0)
{
uint8_t v___x_4065_; 
v___x_4065_ = 0;
v___y_4052_ = v___y_4064_;
v___y_4053_ = v___x_4065_;
goto v___jp_4051_;
}
else
{
uint8_t v___x_4066_; 
lean_dec_ref_known(v_authority_4036_, 1);
v___x_4066_ = 1;
v___y_4052_ = v___y_4064_;
v___y_4053_ = v___x_4066_;
goto v___jp_4051_;
}
}
}
else
{
lean_object* v_ref_4118_; lean_object* v_authority_4119_; lean_object* v_path_4120_; lean_object* v_query_4121_; lean_object* v_fragment_4122_; lean_object* v___y_4124_; uint8_t v___y_4125_; lean_object* v___y_4136_; 
v_ref_4118_ = lean_ctor_get(v_x_4025_, 0);
lean_inc_ref(v_ref_4118_);
lean_dec_ref_known(v_x_4025_, 1);
v_authority_4119_ = lean_ctor_get(v_ref_4118_, 0);
lean_inc(v_authority_4119_);
v_path_4120_ = lean_ctor_get(v_ref_4118_, 1);
lean_inc_ref(v_path_4120_);
v_query_4121_ = lean_ctor_get(v_ref_4118_, 2);
lean_inc(v_query_4121_);
v_fragment_4122_ = lean_ctor_get(v_ref_4118_, 3);
lean_inc(v_fragment_4122_);
lean_dec_ref(v_ref_4118_);
if (lean_obj_tag(v_authority_4119_) == 0)
{
lean_object* v___x_4139_; 
v___x_4139_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_4136_ = v___x_4139_;
goto v___jp_4135_;
}
else
{
lean_object* v_val_4140_; lean_object* v_userInfo_4141_; lean_object* v_host_4142_; lean_object* v_port_4143_; lean_object* v___x_4144_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4163_; 
v_val_4140_ = lean_ctor_get(v_authority_4119_, 0);
v_userInfo_4141_ = lean_ctor_get(v_val_4140_, 0);
v_host_4142_ = lean_ctor_get(v_val_4140_, 1);
v_port_4143_ = lean_ctor_get(v_val_4140_, 2);
v___x_4144_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__1));
if (lean_obj_tag(v_userInfo_4141_) == 0)
{
lean_object* v___x_4174_; 
v___x_4174_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_4163_ = v___x_4174_;
goto v___jp_4162_;
}
else
{
lean_object* v_val_4175_; lean_object* v_password_4176_; 
v_val_4175_ = lean_ctor_get(v_userInfo_4141_, 0);
v_password_4176_ = lean_ctor_get(v_val_4175_, 1);
if (lean_obj_tag(v_password_4176_) == 0)
{
lean_object* v_username_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v_username_4177_ = lean_ctor_get(v_val_4175_, 0);
lean_inc_ref(v_username_4177_);
v___x_4178_ = lean_string_from_utf8_unchecked(v_username_4177_);
v___x_4179_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4180_ = lean_string_append(v___x_4178_, v___x_4179_);
v___y_4163_ = v___x_4180_;
goto v___jp_4162_;
}
else
{
lean_object* v_username_4181_; lean_object* v_val_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v_username_4181_ = lean_ctor_get(v_val_4175_, 0);
v_val_4182_ = lean_ctor_get(v_password_4176_, 0);
lean_inc_ref(v_username_4181_);
v___x_4183_ = lean_string_from_utf8_unchecked(v_username_4181_);
v___x_4184_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_4185_ = lean_string_append(v___x_4183_, v___x_4184_);
lean_inc(v_val_4182_);
v___x_4186_ = lean_string_from_utf8_unchecked(v_val_4182_);
v___x_4187_ = lean_string_append(v___x_4185_, v___x_4186_);
lean_dec_ref(v___x_4186_);
v___x_4188_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4189_ = lean_string_append(v___x_4187_, v___x_4188_);
v___y_4163_ = v___x_4189_;
goto v___jp_4162_;
}
}
v___jp_4145_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4149_ = lean_string_append(v___y_4146_, v___y_4147_);
lean_dec_ref(v___y_4147_);
v___x_4150_ = lean_string_append(v___x_4149_, v___y_4148_);
lean_dec_ref(v___y_4148_);
v___x_4151_ = lean_string_append(v___x_4144_, v___x_4150_);
lean_dec_ref(v___x_4150_);
v___y_4136_ = v___x_4151_;
goto v___jp_4135_;
}
v___jp_4152_:
{
switch(lean_obj_tag(v_port_4143_))
{
case 0:
{
lean_object* v___x_4155_; 
v___x_4155_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_4146_ = v___y_4153_;
v___y_4147_ = v___y_4154_;
v___y_4148_ = v___x_4155_;
goto v___jp_4145_;
}
case 1:
{
lean_object* v___x_4156_; 
v___x_4156_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4146_ = v___y_4153_;
v___y_4147_ = v___y_4154_;
v___y_4148_ = v___x_4156_;
goto v___jp_4145_;
}
default: 
{
uint16_t v_port_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v_port_4157_ = lean_ctor_get_uint16(v_port_4143_, 0);
v___x_4158_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_4159_ = lean_uint16_to_nat(v_port_4157_);
v___x_4160_ = l_Nat_reprFast(v___x_4159_);
v___x_4161_ = lean_string_append(v___x_4158_, v___x_4160_);
lean_dec_ref(v___x_4160_);
v___y_4146_ = v___y_4153_;
v___y_4147_ = v___y_4154_;
v___y_4148_ = v___x_4161_;
goto v___jp_4145_;
}
}
}
v___jp_4162_:
{
switch(lean_obj_tag(v_host_4142_))
{
case 0:
{
lean_object* v_name_4164_; 
v_name_4164_ = lean_ctor_get(v_host_4142_, 0);
lean_inc_ref(v_name_4164_);
v___y_4153_ = v___y_4163_;
v___y_4154_ = v_name_4164_;
goto v___jp_4152_;
}
case 1:
{
lean_object* v_ipv4_4165_; lean_object* v___x_4166_; 
v_ipv4_4165_ = lean_ctor_get(v_host_4142_, 0);
v___x_4166_ = lean_uv_ntop_v4(v_ipv4_4165_);
v___y_4153_ = v___y_4163_;
v___y_4154_ = v___x_4166_;
goto v___jp_4152_;
}
case 2:
{
lean_object* v_ipv6_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v_ipv6_4167_ = lean_ctor_get(v_host_4142_, 0);
v___x_4168_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4169_ = lean_uv_ntop_v6(v_ipv6_4167_);
v___x_4170_ = lean_string_append(v___x_4168_, v___x_4169_);
lean_dec_ref(v___x_4169_);
v___x_4171_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4172_ = lean_string_append(v___x_4170_, v___x_4171_);
v___y_4153_ = v___y_4163_;
v___y_4154_ = v___x_4172_;
goto v___jp_4152_;
}
default: 
{
lean_object* v___x_4173_; 
v___x_4173_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_4153_ = v___y_4163_;
v___y_4154_ = v___x_4173_;
goto v___jp_4152_;
}
}
}
}
v___jp_4123_:
{
uint8_t v___x_4126_; lean_object* v_pathPart_4127_; lean_object* v_queryPart_4128_; 
v___x_4126_ = 0;
v_pathPart_4127_ = l_Std_Http_URI_Path_render(v_path_4120_, v___y_4125_, v___x_4126_);
v_queryPart_4128_ = l_Std_Http_URI_Query_formatOption(v_query_4121_);
if (lean_obj_tag(v_fragment_4122_) == 0)
{
lean_object* v___x_4129_; 
v___x_4129_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_4027_ = v_pathPart_4127_;
v___y_4028_ = v_queryPart_4128_;
v___y_4029_ = v___y_4124_;
v___y_4030_ = v___x_4129_;
goto v___jp_4026_;
}
else
{
lean_object* v_val_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v_val_4130_ = lean_ctor_get(v_fragment_4122_, 0);
lean_inc(v_val_4130_);
lean_dec_ref_known(v_fragment_4122_, 1);
v___x_4131_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__0));
v___x_4132_ = l_Std_Http_URI_EncodedFragment_encode(v_val_4130_);
v___x_4133_ = lean_string_from_utf8_unchecked(v___x_4132_);
v___x_4134_ = lean_string_append(v___x_4131_, v___x_4133_);
lean_dec_ref(v___x_4133_);
v___y_4027_ = v_pathPart_4127_;
v___y_4028_ = v_queryPart_4128_;
v___y_4029_ = v___y_4124_;
v___y_4030_ = v___x_4134_;
goto v___jp_4026_;
}
}
v___jp_4135_:
{
if (lean_obj_tag(v_authority_4119_) == 0)
{
uint8_t v___x_4137_; 
v___x_4137_ = 0;
v___y_4124_ = v___y_4136_;
v___y_4125_ = v___x_4137_;
goto v___jp_4123_;
}
else
{
uint8_t v___x_4138_; 
lean_dec_ref_known(v_authority_4119_, 1);
v___x_4138_ = 1;
v___y_4124_ = v___y_4136_;
v___y_4125_ = v___x_4138_;
goto v___jp_4123_;
}
}
}
v___jp_4026_:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4031_ = lean_string_append(v___y_4029_, v___y_4027_);
lean_dec_ref(v___y_4027_);
v___x_4032_ = lean_string_append(v___x_4031_, v___y_4028_);
lean_dec_ref(v___y_4028_);
v___x_4033_ = lean_string_append(v___x_4032_, v___y_4030_);
lean_dec_ref(v___y_4030_);
return v___x_4033_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___impl(lean_object* v_x_4192_){
_start:
{
lean_object* v___x_4193_; 
v___x_4193_ = lean_obj_tag_nat(v_x_4192_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___impl___boxed(lean_object* v_x_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Std_Http_RequestTarget_ctorIdx___impl(v_x_4194_);
lean_dec(v_x_4194_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___redArg(lean_object* v_t_4196_, lean_object* v_k_4197_){
_start:
{
switch(lean_obj_tag(v_t_4196_))
{
case 0:
{
lean_object* v_path_4198_; lean_object* v_query_4199_; lean_object* v___x_4200_; 
v_path_4198_ = lean_ctor_get(v_t_4196_, 0);
lean_inc_ref(v_path_4198_);
v_query_4199_ = lean_ctor_get(v_t_4196_, 1);
lean_inc(v_query_4199_);
lean_dec_ref_known(v_t_4196_, 2);
v___x_4200_ = lean_apply_2(v_k_4197_, v_path_4198_, v_query_4199_);
return v___x_4200_;
}
case 3:
{
return v_k_4197_;
}
default: 
{
lean_object* v_uri_4201_; lean_object* v___x_4202_; 
v_uri_4201_ = lean_ctor_get(v_t_4196_, 0);
lean_inc_ref(v_uri_4201_);
lean_dec(v_t_4196_);
v___x_4202_ = lean_apply_1(v_k_4197_, v_uri_4201_);
return v___x_4202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim(lean_object* v_motive_4203_, lean_object* v_ctorIdx_4204_, lean_object* v_t_4205_, lean_object* v_h_4206_, lean_object* v_k_4207_){
_start:
{
lean_object* v___x_4208_; 
v___x_4208_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4205_, v_k_4207_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___boxed(lean_object* v_motive_4209_, lean_object* v_ctorIdx_4210_, lean_object* v_t_4211_, lean_object* v_h_4212_, lean_object* v_k_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l_Std_Http_RequestTarget_ctorElim(v_motive_4209_, v_ctorIdx_4210_, v_t_4211_, v_h_4212_, v_k_4213_);
lean_dec(v_ctorIdx_4210_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim___redArg(lean_object* v_t_4215_, lean_object* v_originForm_4216_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4215_, v_originForm_4216_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim(lean_object* v_motive_4218_, lean_object* v_t_4219_, lean_object* v_h_4220_, lean_object* v_originForm_4221_){
_start:
{
lean_object* v___x_4222_; 
v___x_4222_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4219_, v_originForm_4221_);
return v___x_4222_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim___redArg(lean_object* v_t_4223_, lean_object* v_absoluteForm_4224_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4223_, v_absoluteForm_4224_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim(lean_object* v_motive_4226_, lean_object* v_t_4227_, lean_object* v_h_4228_, lean_object* v_absoluteForm_4229_){
_start:
{
lean_object* v___x_4230_; 
v___x_4230_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4227_, v_absoluteForm_4229_);
return v___x_4230_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim___redArg(lean_object* v_t_4231_, lean_object* v_authorityForm_4232_){
_start:
{
lean_object* v___x_4233_; 
v___x_4233_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4231_, v_authorityForm_4232_);
return v___x_4233_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim(lean_object* v_motive_4234_, lean_object* v_t_4235_, lean_object* v_h_4236_, lean_object* v_authorityForm_4237_){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4235_, v_authorityForm_4237_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim___redArg(lean_object* v_t_4239_, lean_object* v_asteriskForm_4240_){
_start:
{
lean_object* v___x_4241_; 
v___x_4241_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4239_, v_asteriskForm_4240_);
return v___x_4241_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim(lean_object* v_motive_4242_, lean_object* v_t_4243_, lean_object* v_h_4244_, lean_object* v_asteriskForm_4245_){
_start:
{
lean_object* v___x_4246_; 
v___x_4246_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4243_, v_asteriskForm_4245_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object* v_x_4273_, lean_object* v_prec_4274_){
_start:
{
lean_object* v___y_4276_; 
switch(lean_obj_tag(v_x_4273_))
{
case 0:
{
lean_object* v_path_4282_; lean_object* v_query_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4307_; 
v_path_4282_ = lean_ctor_get(v_x_4273_, 0);
v_query_4283_ = lean_ctor_get(v_x_4273_, 1);
v_isSharedCheck_4307_ = !lean_is_exclusive(v_x_4273_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4285_ = v_x_4273_;
v_isShared_4286_ = v_isSharedCheck_4307_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_query_4283_);
lean_inc(v_path_4282_);
lean_dec(v_x_4273_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4307_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___y_4288_; lean_object* v___x_4303_; uint8_t v___x_4304_; 
v___x_4303_ = lean_unsigned_to_nat(1024u);
v___x_4304_ = lean_nat_dec_le(v___x_4303_, v_prec_4274_);
if (v___x_4304_ == 0)
{
lean_object* v___x_4305_; 
v___x_4305_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__6, &l_Std_Http_URI_instReprHost___lam__0___closed__6_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__6);
v___y_4288_ = v___x_4305_;
goto v___jp_4287_;
}
else
{
lean_object* v___x_4306_; 
v___x_4306_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__7, &l_Std_Http_URI_instReprHost___lam__0___closed__7_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__7);
v___y_4288_ = v___x_4306_;
goto v___jp_4287_;
}
v___jp_4287_:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4294_; 
v___x_4289_ = lean_box(1);
v___x_4290_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__4));
v___x_4291_ = lean_unsigned_to_nat(1024u);
v___x_4292_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_4282_);
if (v_isShared_4286_ == 0)
{
lean_ctor_set_tag(v___x_4285_, 5);
lean_ctor_set(v___x_4285_, 1, v___x_4292_);
lean_ctor_set(v___x_4285_, 0, v___x_4290_);
v___x_4294_ = v___x_4285_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4290_);
lean_ctor_set(v_reuseFailAlloc_4302_, 1, v___x_4292_);
v___x_4294_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; uint8_t v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4294_);
lean_ctor_set(v___x_4295_, 1, v___x_4289_);
v___x_4296_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_4283_, v___x_4291_);
v___x_4297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4295_);
lean_ctor_set(v___x_4297_, 1, v___x_4296_);
lean_inc(v___y_4288_);
v___x_4298_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___y_4288_);
lean_ctor_set(v___x_4298_, 1, v___x_4297_);
v___x_4299_ = 0;
v___x_4300_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4300_, 0, v___x_4298_);
lean_ctor_set_uint8(v___x_4300_, sizeof(void*)*1, v___x_4299_);
v___x_4301_ = l_Repr_addAppParen(v___x_4300_, v_prec_4274_);
return v___x_4301_;
}
}
}
}
case 1:
{
lean_object* v_uri_4308_; lean_object* v___y_4310_; lean_object* v___x_4318_; uint8_t v___x_4319_; 
v_uri_4308_ = lean_ctor_get(v_x_4273_, 0);
lean_inc_ref(v_uri_4308_);
lean_dec_ref_known(v_x_4273_, 1);
v___x_4318_ = lean_unsigned_to_nat(1024u);
v___x_4319_ = lean_nat_dec_le(v___x_4318_, v_prec_4274_);
if (v___x_4319_ == 0)
{
lean_object* v___x_4320_; 
v___x_4320_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__6, &l_Std_Http_URI_instReprHost___lam__0___closed__6_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__6);
v___y_4310_ = v___x_4320_;
goto v___jp_4309_;
}
else
{
lean_object* v___x_4321_; 
v___x_4321_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__7, &l_Std_Http_URI_instReprHost___lam__0___closed__7_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__7);
v___y_4310_ = v___x_4321_;
goto v___jp_4309_;
}
v___jp_4309_:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; uint8_t v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4311_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__7));
v___x_4312_ = l_Std_Http_instReprURI_repr___redArg(v_uri_4308_);
v___x_4313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4311_);
lean_ctor_set(v___x_4313_, 1, v___x_4312_);
lean_inc(v___y_4310_);
v___x_4314_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4314_, 0, v___y_4310_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
v___x_4315_ = 0;
v___x_4316_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4316_, 0, v___x_4314_);
lean_ctor_set_uint8(v___x_4316_, sizeof(void*)*1, v___x_4315_);
v___x_4317_ = l_Repr_addAppParen(v___x_4316_, v_prec_4274_);
return v___x_4317_;
}
}
case 2:
{
lean_object* v_authority_4322_; lean_object* v___y_4324_; lean_object* v___x_4332_; uint8_t v___x_4333_; 
v_authority_4322_ = lean_ctor_get(v_x_4273_, 0);
lean_inc_ref(v_authority_4322_);
lean_dec_ref_known(v_x_4273_, 1);
v___x_4332_ = lean_unsigned_to_nat(1024u);
v___x_4333_ = lean_nat_dec_le(v___x_4332_, v_prec_4274_);
if (v___x_4333_ == 0)
{
lean_object* v___x_4334_; 
v___x_4334_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__6, &l_Std_Http_URI_instReprHost___lam__0___closed__6_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__6);
v___y_4324_ = v___x_4334_;
goto v___jp_4323_;
}
else
{
lean_object* v___x_4335_; 
v___x_4335_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__7, &l_Std_Http_URI_instReprHost___lam__0___closed__7_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__7);
v___y_4324_ = v___x_4335_;
goto v___jp_4323_;
}
v___jp_4323_:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; uint8_t v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4325_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__10));
v___x_4326_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_authority_4322_);
v___x_4327_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4325_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
lean_inc(v___y_4324_);
v___x_4328_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4328_, 0, v___y_4324_);
lean_ctor_set(v___x_4328_, 1, v___x_4327_);
v___x_4329_ = 0;
v___x_4330_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4330_, 0, v___x_4328_);
lean_ctor_set_uint8(v___x_4330_, sizeof(void*)*1, v___x_4329_);
v___x_4331_ = l_Repr_addAppParen(v___x_4330_, v_prec_4274_);
return v___x_4331_;
}
}
default: 
{
lean_object* v___x_4336_; uint8_t v___x_4337_; 
v___x_4336_ = lean_unsigned_to_nat(1024u);
v___x_4337_ = lean_nat_dec_le(v___x_4336_, v_prec_4274_);
if (v___x_4337_ == 0)
{
lean_object* v___x_4338_; 
v___x_4338_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__6, &l_Std_Http_URI_instReprHost___lam__0___closed__6_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__6);
v___y_4276_ = v___x_4338_;
goto v___jp_4275_;
}
else
{
lean_object* v___x_4339_; 
v___x_4339_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__7, &l_Std_Http_URI_instReprHost___lam__0___closed__7_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__7);
v___y_4276_ = v___x_4339_;
goto v___jp_4275_;
}
}
}
v___jp_4275_:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; uint8_t v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4277_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__1));
lean_inc(v___y_4276_);
v___x_4278_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4278_, 0, v___y_4276_);
lean_ctor_set(v___x_4278_, 1, v___x_4277_);
v___x_4279_ = 0;
v___x_4280_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4280_, 0, v___x_4278_);
lean_ctor_set_uint8(v___x_4280_, sizeof(void*)*1, v___x_4279_);
v___x_4281_ = l_Repr_addAppParen(v___x_4280_, v_prec_4274_);
return v___x_4281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr___boxed(lean_object* v_x_4340_, lean_object* v_prec_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_Std_Http_instReprRequestTarget_repr(v_x_4340_, v_prec_4341_);
lean_dec(v_prec_4341_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path(lean_object* v_x_4348_){
_start:
{
switch(lean_obj_tag(v_x_4348_))
{
case 0:
{
lean_object* v_path_4349_; 
v_path_4349_ = lean_ctor_get(v_x_4348_, 0);
lean_inc_ref(v_path_4349_);
return v_path_4349_;
}
case 1:
{
lean_object* v_uri_4350_; lean_object* v_path_4351_; 
v_uri_4350_ = lean_ctor_get(v_x_4348_, 0);
v_path_4351_ = lean_ctor_get(v_uri_4350_, 2);
lean_inc_ref(v_path_4351_);
return v_path_4351_;
}
default: 
{
lean_object* v___x_4352_; 
v___x_4352_ = ((lean_object*)(l_Std_Http_RequestTarget_path___closed__0));
return v___x_4352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path___boxed(lean_object* v_x_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l_Std_Http_RequestTarget_path(v_x_4353_);
lean_dec(v_x_4353_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query(lean_object* v_x_4355_){
_start:
{
switch(lean_obj_tag(v_x_4355_))
{
case 0:
{
lean_object* v_query_4356_; 
v_query_4356_ = lean_ctor_get(v_x_4355_, 1);
if (lean_obj_tag(v_query_4356_) == 0)
{
lean_object* v___x_4357_; 
v___x_4357_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_4357_;
}
else
{
lean_object* v_val_4358_; 
v_val_4358_ = lean_ctor_get(v_query_4356_, 0);
lean_inc(v_val_4358_);
return v_val_4358_;
}
}
case 1:
{
lean_object* v_uri_4359_; lean_object* v_query_4360_; 
v_uri_4359_ = lean_ctor_get(v_x_4355_, 0);
v_query_4360_ = lean_ctor_get(v_uri_4359_, 3);
if (lean_obj_tag(v_query_4360_) == 0)
{
lean_object* v___x_4361_; 
v___x_4361_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_4361_;
}
else
{
lean_object* v_val_4362_; 
v_val_4362_ = lean_ctor_get(v_query_4360_, 0);
lean_inc(v_val_4362_);
return v_val_4362_;
}
}
default: 
{
lean_object* v___x_4363_; 
v___x_4363_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_4363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query___boxed(lean_object* v_x_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Std_Http_RequestTarget_query(v_x_4364_);
lean_dec(v_x_4364_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authority_x3f(lean_object* v_x_4366_){
_start:
{
switch(lean_obj_tag(v_x_4366_))
{
case 2:
{
lean_object* v_authority_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4374_; 
v_authority_4367_ = lean_ctor_get(v_x_4366_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v_x_4366_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4369_ = v_x_4366_;
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_authority_4367_);
lean_dec(v_x_4366_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4372_; 
if (v_isShared_4370_ == 0)
{
lean_ctor_set_tag(v___x_4369_, 1);
v___x_4372_ = v___x_4369_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_authority_4367_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
return v___x_4372_;
}
}
}
case 1:
{
lean_object* v_uri_4375_; lean_object* v_authority_4376_; 
v_uri_4375_ = lean_ctor_get(v_x_4366_, 0);
lean_inc_ref(v_uri_4375_);
lean_dec_ref_known(v_x_4366_, 1);
v_authority_4376_ = lean_ctor_get(v_uri_4375_, 1);
lean_inc(v_authority_4376_);
lean_dec_ref(v_uri_4375_);
return v_authority_4376_;
}
default: 
{
lean_object* v___x_4377_; 
lean_dec(v_x_4366_);
v___x_4377_ = lean_box(0);
return v___x_4377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__0(lean_object* v_x_4379_){
_start:
{
switch(lean_obj_tag(v_x_4379_))
{
case 0:
{
lean_object* v_path_4380_; lean_object* v_query_4381_; lean_object* v___y_4383_; uint8_t v___x_4386_; lean_object* v_pathStr_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; uint8_t v___x_4390_; 
v_path_4380_ = lean_ctor_get(v_x_4379_, 0);
lean_inc_ref(v_path_4380_);
v_query_4381_ = lean_ctor_get(v_x_4379_, 1);
lean_inc(v_query_4381_);
lean_dec_ref_known(v_x_4379_, 2);
v___x_4386_ = 1;
v_pathStr_4387_ = l_Std_Http_URI_Path_render(v_path_4380_, v___x_4386_, v___x_4386_);
v___x_4388_ = lean_string_utf8_byte_size(v_pathStr_4387_);
v___x_4389_ = lean_unsigned_to_nat(0u);
v___x_4390_ = lean_nat_dec_eq(v___x_4388_, v___x_4389_);
if (v___x_4390_ == 0)
{
v___y_4383_ = v_pathStr_4387_;
goto v___jp_4382_;
}
else
{
lean_object* v___x_4391_; 
lean_dec_ref(v_pathStr_4387_);
v___x_4391_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___y_4383_ = v___x_4391_;
goto v___jp_4382_;
}
v___jp_4382_:
{
lean_object* v_queryStr_4384_; lean_object* v___x_4385_; 
v_queryStr_4384_ = l_Std_Http_URI_Query_formatOption(v_query_4381_);
v___x_4385_ = lean_string_append(v___y_4383_, v_queryStr_4384_);
lean_dec_ref(v_queryStr_4384_);
return v___x_4385_;
}
}
case 1:
{
lean_object* v_uri_4392_; lean_object* v_scheme_4393_; lean_object* v_authority_4394_; lean_object* v_path_4395_; lean_object* v_query_4396_; lean_object* v___y_4398_; uint8_t v___y_4399_; lean_object* v___y_4409_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v_port_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; 
v_uri_4392_ = lean_ctor_get(v_x_4379_, 0);
lean_inc_ref(v_uri_4392_);
lean_dec_ref_known(v_x_4379_, 1);
v_scheme_4393_ = lean_ctor_get(v_uri_4392_, 0);
lean_inc_ref(v_scheme_4393_);
v_authority_4394_ = lean_ctor_get(v_uri_4392_, 1);
lean_inc(v_authority_4394_);
v_path_4395_ = lean_ctor_get(v_uri_4392_, 2);
lean_inc_ref(v_path_4395_);
v_query_4396_ = lean_ctor_get(v_uri_4392_, 3);
lean_inc(v_query_4396_);
lean_dec_ref(v_uri_4392_);
if (lean_obj_tag(v_authority_4394_) == 0)
{
lean_object* v___x_4434_; 
v___x_4434_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_4409_ = v___x_4434_;
goto v___jp_4408_;
}
else
{
lean_object* v_val_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4464_; 
v_val_4435_ = lean_ctor_get(v_authority_4394_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v_authority_4394_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4437_ = v_authority_4394_;
v_isShared_4438_ = v_isSharedCheck_4464_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_val_4435_);
lean_dec(v_authority_4394_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4464_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v_host_4439_; lean_object* v_port_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4462_; 
v_host_4439_ = lean_ctor_get(v_val_4435_, 1);
v_port_4440_ = lean_ctor_get(v_val_4435_, 2);
v_isSharedCheck_4462_ = !lean_is_exclusive(v_val_4435_);
if (v_isSharedCheck_4462_ == 0)
{
lean_object* v_unused_4463_; 
v_unused_4463_ = lean_ctor_get(v_val_4435_, 0);
lean_dec(v_unused_4463_);
v___x_4442_ = v_val_4435_;
v_isShared_4443_ = v_isSharedCheck_4462_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_port_4440_);
lean_inc(v_host_4439_);
lean_dec(v_val_4435_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4462_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4444_; lean_object* v___x_4446_; 
v___x_4444_ = lean_box(0);
lean_inc(v_port_4440_);
lean_inc(v_host_4439_);
if (v_isShared_4443_ == 0)
{
lean_ctor_set(v___x_4442_, 0, v___x_4444_);
v___x_4446_ = v___x_4442_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4444_);
lean_ctor_set(v_reuseFailAlloc_4461_, 1, v_host_4439_);
lean_ctor_set(v_reuseFailAlloc_4461_, 2, v_port_4440_);
v___x_4446_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
lean_object* v___x_4448_; 
if (v_isShared_4438_ == 0)
{
lean_ctor_set(v___x_4437_, 0, v___x_4446_);
v___x_4448_ = v___x_4437_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v___x_4446_);
v___x_4448_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4449_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__1));
v___x_4450_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
switch(lean_obj_tag(v_host_4439_))
{
case 0:
{
lean_object* v_name_4451_; 
v_name_4451_ = lean_ctor_get(v_host_4439_, 0);
lean_inc_ref(v_name_4451_);
lean_dec_ref_known(v_host_4439_, 1);
v___y_4422_ = v___x_4449_;
v___y_4423_ = v___x_4450_;
v_port_4424_ = v_port_4440_;
v___y_4425_ = v___x_4448_;
v___y_4426_ = v_name_4451_;
goto v___jp_4421_;
}
case 1:
{
lean_object* v_ipv4_4452_; lean_object* v___x_4453_; 
v_ipv4_4452_ = lean_ctor_get(v_host_4439_, 0);
lean_inc_ref(v_ipv4_4452_);
lean_dec_ref_known(v_host_4439_, 1);
v___x_4453_ = lean_uv_ntop_v4(v_ipv4_4452_);
lean_dec_ref(v_ipv4_4452_);
v___y_4422_ = v___x_4449_;
v___y_4423_ = v___x_4450_;
v_port_4424_ = v_port_4440_;
v___y_4425_ = v___x_4448_;
v___y_4426_ = v___x_4453_;
goto v___jp_4421_;
}
case 2:
{
lean_object* v_ipv6_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
v_ipv6_4454_ = lean_ctor_get(v_host_4439_, 0);
lean_inc_ref(v_ipv6_4454_);
lean_dec_ref_known(v_host_4439_, 1);
v___x_4455_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4456_ = lean_uv_ntop_v6(v_ipv6_4454_);
lean_dec_ref(v_ipv6_4454_);
v___x_4457_ = lean_string_append(v___x_4455_, v___x_4456_);
lean_dec_ref(v___x_4456_);
v___x_4458_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4459_ = lean_string_append(v___x_4457_, v___x_4458_);
v___y_4422_ = v___x_4449_;
v___y_4423_ = v___x_4450_;
v_port_4424_ = v_port_4440_;
v___y_4425_ = v___x_4448_;
v___y_4426_ = v___x_4459_;
goto v___jp_4421_;
}
default: 
{
v___y_4422_ = v___x_4449_;
v___y_4423_ = v___x_4450_;
v_port_4424_ = v_port_4440_;
v___y_4425_ = v___x_4448_;
v___y_4426_ = v___x_4450_;
goto v___jp_4421_;
}
}
}
}
}
}
}
v___jp_4397_:
{
uint8_t v___x_4400_; lean_object* v_pathPart_4401_; lean_object* v_queryPart_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4400_ = 1;
v_pathPart_4401_ = l_Std_Http_URI_Path_render(v_path_4395_, v___y_4399_, v___x_4400_);
v_queryPart_4402_ = l_Std_Http_URI_Query_formatOption(v_query_4396_);
v___x_4403_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_4404_ = lean_string_append(v_scheme_4393_, v___x_4403_);
v___x_4405_ = lean_string_append(v___x_4404_, v___y_4398_);
lean_dec_ref(v___y_4398_);
v___x_4406_ = lean_string_append(v___x_4405_, v_pathPart_4401_);
lean_dec_ref(v_pathPart_4401_);
v___x_4407_ = lean_string_append(v___x_4406_, v_queryPart_4402_);
lean_dec_ref(v_queryPart_4402_);
return v___x_4407_;
}
v___jp_4408_:
{
uint8_t v___x_4410_; 
v___x_4410_ = 0;
lean_inc_ref(v___y_4409_);
v___y_4398_ = v___y_4409_;
v___y_4399_ = v___x_4410_;
goto v___jp_4397_;
}
v___jp_4411_:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; uint8_t v___x_4420_; 
lean_dec(v___y_4415_);
v___x_4417_ = lean_string_append(v___y_4414_, v___y_4413_);
lean_dec_ref(v___y_4413_);
v___x_4418_ = lean_string_append(v___x_4417_, v___y_4416_);
lean_dec_ref(v___y_4416_);
lean_inc_ref(v___y_4412_);
v___x_4419_ = lean_string_append(v___y_4412_, v___x_4418_);
lean_dec_ref(v___x_4418_);
v___x_4420_ = 1;
v___y_4398_ = v___x_4419_;
v___y_4399_ = v___x_4420_;
goto v___jp_4397_;
}
v___jp_4421_:
{
switch(lean_obj_tag(v_port_4424_))
{
case 0:
{
lean_object* v___x_4427_; 
v___x_4427_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_4412_ = v___y_4422_;
v___y_4413_ = v___y_4426_;
v___y_4414_ = v___y_4423_;
v___y_4415_ = v___y_4425_;
v___y_4416_ = v___x_4427_;
goto v___jp_4411_;
}
case 1:
{
lean_object* v___x_4428_; 
v___x_4428_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4412_ = v___y_4422_;
v___y_4413_ = v___y_4426_;
v___y_4414_ = v___y_4423_;
v___y_4415_ = v___y_4425_;
v___y_4416_ = v___x_4428_;
goto v___jp_4411_;
}
default: 
{
uint16_t v_port_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v_port_4429_ = lean_ctor_get_uint16(v_port_4424_, 0);
lean_dec_ref_known(v_port_4424_, 0);
v___x_4430_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_4431_ = lean_uint16_to_nat(v_port_4429_);
v___x_4432_ = l_Nat_reprFast(v___x_4431_);
v___x_4433_ = lean_string_append(v___x_4430_, v___x_4432_);
lean_dec_ref(v___x_4432_);
v___y_4412_ = v___y_4422_;
v___y_4413_ = v___y_4426_;
v___y_4414_ = v___y_4423_;
v___y_4415_ = v___y_4425_;
v___y_4416_ = v___x_4433_;
goto v___jp_4411_;
}
}
}
}
case 2:
{
lean_object* v_authority_4465_; lean_object* v_host_4466_; lean_object* v_port_4467_; lean_object* v___y_4469_; 
v_authority_4465_ = lean_ctor_get(v_x_4379_, 0);
lean_inc_ref(v_authority_4465_);
lean_dec_ref_known(v_x_4379_, 1);
v_host_4466_ = lean_ctor_get(v_authority_4465_, 1);
lean_inc(v_host_4466_);
v_port_4467_ = lean_ctor_get(v_authority_4465_, 2);
lean_inc(v_port_4467_);
lean_dec_ref(v_authority_4465_);
switch(lean_obj_tag(v_host_4466_))
{
case 0:
{
lean_object* v_name_4478_; 
v_name_4478_ = lean_ctor_get(v_host_4466_, 0);
lean_inc_ref(v_name_4478_);
lean_dec_ref_known(v_host_4466_, 1);
v___y_4469_ = v_name_4478_;
goto v___jp_4468_;
}
case 1:
{
lean_object* v_ipv4_4479_; lean_object* v___x_4480_; 
v_ipv4_4479_ = lean_ctor_get(v_host_4466_, 0);
lean_inc_ref(v_ipv4_4479_);
lean_dec_ref_known(v_host_4466_, 1);
v___x_4480_ = lean_uv_ntop_v4(v_ipv4_4479_);
lean_dec_ref(v_ipv4_4479_);
v___y_4469_ = v___x_4480_;
goto v___jp_4468_;
}
case 2:
{
lean_object* v_ipv6_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; 
v_ipv6_4481_ = lean_ctor_get(v_host_4466_, 0);
lean_inc_ref(v_ipv6_4481_);
lean_dec_ref_known(v_host_4466_, 1);
v___x_4482_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4483_ = lean_uv_ntop_v6(v_ipv6_4481_);
lean_dec_ref(v_ipv6_4481_);
v___x_4484_ = lean_string_append(v___x_4482_, v___x_4483_);
lean_dec_ref(v___x_4483_);
v___x_4485_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4486_ = lean_string_append(v___x_4484_, v___x_4485_);
v___y_4469_ = v___x_4486_;
goto v___jp_4468_;
}
default: 
{
lean_object* v___x_4487_; 
v___x_4487_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_4469_ = v___x_4487_;
goto v___jp_4468_;
}
}
v___jp_4468_:
{
switch(lean_obj_tag(v_port_4467_))
{
case 0:
{
return v___y_4469_;
}
case 1:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4470_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_4471_ = lean_string_append(v___y_4469_, v___x_4470_);
return v___x_4471_;
}
default: 
{
uint16_t v_port_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v_port_4472_ = lean_ctor_get_uint16(v_port_4467_, 0);
lean_dec_ref_known(v_port_4467_, 0);
v___x_4473_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_4474_ = lean_uint16_to_nat(v_port_4472_);
v___x_4475_ = l_Nat_reprFast(v___x_4474_);
v___x_4476_ = lean_string_append(v___x_4473_, v___x_4475_);
lean_dec_ref(v___x_4475_);
v___x_4477_ = lean_string_append(v___y_4469_, v___x_4476_);
lean_dec_ref(v___x_4476_);
return v___x_4477_;
}
}
}
}
default: 
{
lean_object* v___x_4488_; 
v___x_4488_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__0___closed__0));
return v___x_4488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__0(lean_object* v_out_4491_, lean_object* v_target_4492_){
_start:
{
lean_object* v___y_4494_; 
switch(lean_obj_tag(v_target_4492_))
{
case 0:
{
lean_object* v_path_4501_; lean_object* v_query_4502_; lean_object* v___y_4504_; uint8_t v___x_4507_; lean_object* v_pathStr_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; uint8_t v___x_4511_; 
v_path_4501_ = lean_ctor_get(v_target_4492_, 0);
lean_inc_ref(v_path_4501_);
v_query_4502_ = lean_ctor_get(v_target_4492_, 1);
lean_inc(v_query_4502_);
lean_dec_ref_known(v_target_4492_, 2);
v___x_4507_ = 1;
v_pathStr_4508_ = l_Std_Http_URI_Path_render(v_path_4501_, v___x_4507_, v___x_4507_);
v___x_4509_ = lean_string_utf8_byte_size(v_pathStr_4508_);
v___x_4510_ = lean_unsigned_to_nat(0u);
v___x_4511_ = lean_nat_dec_eq(v___x_4509_, v___x_4510_);
if (v___x_4511_ == 0)
{
v___y_4504_ = v_pathStr_4508_;
goto v___jp_4503_;
}
else
{
lean_object* v___x_4512_; 
lean_dec_ref(v_pathStr_4508_);
v___x_4512_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___y_4504_ = v___x_4512_;
goto v___jp_4503_;
}
v___jp_4503_:
{
lean_object* v_queryStr_4505_; lean_object* v___x_4506_; 
v_queryStr_4505_ = l_Std_Http_URI_Query_formatOption(v_query_4502_);
v___x_4506_ = lean_string_append(v___y_4504_, v_queryStr_4505_);
lean_dec_ref(v_queryStr_4505_);
v___y_4494_ = v___x_4506_;
goto v___jp_4493_;
}
}
case 1:
{
lean_object* v_uri_4513_; lean_object* v_scheme_4514_; lean_object* v_authority_4515_; lean_object* v_path_4516_; lean_object* v_query_4517_; lean_object* v___y_4519_; uint8_t v___y_4520_; lean_object* v___y_4530_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4545_; lean_object* v_port_4546_; lean_object* v___y_4547_; 
v_uri_4513_ = lean_ctor_get(v_target_4492_, 0);
lean_inc_ref(v_uri_4513_);
lean_dec_ref_known(v_target_4492_, 1);
v_scheme_4514_ = lean_ctor_get(v_uri_4513_, 0);
lean_inc_ref(v_scheme_4514_);
v_authority_4515_ = lean_ctor_get(v_uri_4513_, 1);
lean_inc(v_authority_4515_);
v_path_4516_ = lean_ctor_get(v_uri_4513_, 2);
lean_inc_ref(v_path_4516_);
v_query_4517_ = lean_ctor_get(v_uri_4513_, 3);
lean_inc(v_query_4517_);
lean_dec_ref(v_uri_4513_);
if (lean_obj_tag(v_authority_4515_) == 0)
{
lean_object* v___x_4555_; 
v___x_4555_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_4530_ = v___x_4555_;
goto v___jp_4529_;
}
else
{
lean_object* v_val_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4585_; 
v_val_4556_ = lean_ctor_get(v_authority_4515_, 0);
v_isSharedCheck_4585_ = !lean_is_exclusive(v_authority_4515_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4558_ = v_authority_4515_;
v_isShared_4559_ = v_isSharedCheck_4585_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_val_4556_);
lean_dec(v_authority_4515_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4585_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v_host_4560_; lean_object* v_port_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4583_; 
v_host_4560_ = lean_ctor_get(v_val_4556_, 1);
v_port_4561_ = lean_ctor_get(v_val_4556_, 2);
v_isSharedCheck_4583_ = !lean_is_exclusive(v_val_4556_);
if (v_isSharedCheck_4583_ == 0)
{
lean_object* v_unused_4584_; 
v_unused_4584_ = lean_ctor_get(v_val_4556_, 0);
lean_dec(v_unused_4584_);
v___x_4563_ = v_val_4556_;
v_isShared_4564_ = v_isSharedCheck_4583_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_port_4561_);
lean_inc(v_host_4560_);
lean_dec(v_val_4556_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4583_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4565_; lean_object* v___x_4567_; 
v___x_4565_ = lean_box(0);
lean_inc(v_port_4561_);
lean_inc(v_host_4560_);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 0, v___x_4565_);
v___x_4567_ = v___x_4563_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v___x_4565_);
lean_ctor_set(v_reuseFailAlloc_4582_, 1, v_host_4560_);
lean_ctor_set(v_reuseFailAlloc_4582_, 2, v_port_4561_);
v___x_4567_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
lean_object* v___x_4569_; 
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 0, v___x_4567_);
v___x_4569_ = v___x_4558_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v___x_4567_);
v___x_4569_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4570_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__1));
v___x_4571_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
switch(lean_obj_tag(v_host_4560_))
{
case 0:
{
lean_object* v_name_4572_; 
v_name_4572_ = lean_ctor_get(v_host_4560_, 0);
lean_inc_ref(v_name_4572_);
lean_dec_ref_known(v_host_4560_, 1);
v___y_4543_ = v___x_4570_;
v___y_4544_ = v___x_4571_;
v___y_4545_ = v___x_4569_;
v_port_4546_ = v_port_4561_;
v___y_4547_ = v_name_4572_;
goto v___jp_4542_;
}
case 1:
{
lean_object* v_ipv4_4573_; lean_object* v___x_4574_; 
v_ipv4_4573_ = lean_ctor_get(v_host_4560_, 0);
lean_inc_ref(v_ipv4_4573_);
lean_dec_ref_known(v_host_4560_, 1);
v___x_4574_ = lean_uv_ntop_v4(v_ipv4_4573_);
lean_dec_ref(v_ipv4_4573_);
v___y_4543_ = v___x_4570_;
v___y_4544_ = v___x_4571_;
v___y_4545_ = v___x_4569_;
v_port_4546_ = v_port_4561_;
v___y_4547_ = v___x_4574_;
goto v___jp_4542_;
}
case 2:
{
lean_object* v_ipv6_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v_ipv6_4575_ = lean_ctor_get(v_host_4560_, 0);
lean_inc_ref(v_ipv6_4575_);
lean_dec_ref_known(v_host_4560_, 1);
v___x_4576_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4577_ = lean_uv_ntop_v6(v_ipv6_4575_);
lean_dec_ref(v_ipv6_4575_);
v___x_4578_ = lean_string_append(v___x_4576_, v___x_4577_);
lean_dec_ref(v___x_4577_);
v___x_4579_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4580_ = lean_string_append(v___x_4578_, v___x_4579_);
v___y_4543_ = v___x_4570_;
v___y_4544_ = v___x_4571_;
v___y_4545_ = v___x_4569_;
v_port_4546_ = v_port_4561_;
v___y_4547_ = v___x_4580_;
goto v___jp_4542_;
}
default: 
{
v___y_4543_ = v___x_4570_;
v___y_4544_ = v___x_4571_;
v___y_4545_ = v___x_4569_;
v_port_4546_ = v_port_4561_;
v___y_4547_ = v___x_4571_;
goto v___jp_4542_;
}
}
}
}
}
}
}
v___jp_4518_:
{
uint8_t v___x_4521_; lean_object* v_pathPart_4522_; lean_object* v_queryPart_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4521_ = 1;
v_pathPart_4522_ = l_Std_Http_URI_Path_render(v_path_4516_, v___y_4520_, v___x_4521_);
v_queryPart_4523_ = l_Std_Http_URI_Query_formatOption(v_query_4517_);
v___x_4524_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_4525_ = lean_string_append(v_scheme_4514_, v___x_4524_);
v___x_4526_ = lean_string_append(v___x_4525_, v___y_4519_);
lean_dec_ref(v___y_4519_);
v___x_4527_ = lean_string_append(v___x_4526_, v_pathPart_4522_);
lean_dec_ref(v_pathPart_4522_);
v___x_4528_ = lean_string_append(v___x_4527_, v_queryPart_4523_);
lean_dec_ref(v_queryPart_4523_);
v___y_4494_ = v___x_4528_;
goto v___jp_4493_;
}
v___jp_4529_:
{
uint8_t v___x_4531_; 
v___x_4531_ = 0;
lean_inc_ref(v___y_4530_);
v___y_4519_ = v___y_4530_;
v___y_4520_ = v___x_4531_;
goto v___jp_4518_;
}
v___jp_4532_:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; uint8_t v___x_4541_; 
lean_dec(v___y_4536_);
v___x_4538_ = lean_string_append(v___y_4534_, v___y_4535_);
lean_dec_ref(v___y_4535_);
v___x_4539_ = lean_string_append(v___x_4538_, v___y_4537_);
lean_dec_ref(v___y_4537_);
lean_inc_ref(v___y_4533_);
v___x_4540_ = lean_string_append(v___y_4533_, v___x_4539_);
lean_dec_ref(v___x_4539_);
v___x_4541_ = 1;
v___y_4519_ = v___x_4540_;
v___y_4520_ = v___x_4541_;
goto v___jp_4518_;
}
v___jp_4542_:
{
switch(lean_obj_tag(v_port_4546_))
{
case 0:
{
lean_object* v___x_4548_; 
v___x_4548_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_4533_ = v___y_4543_;
v___y_4534_ = v___y_4544_;
v___y_4535_ = v___y_4547_;
v___y_4536_ = v___y_4545_;
v___y_4537_ = v___x_4548_;
goto v___jp_4532_;
}
case 1:
{
lean_object* v___x_4549_; 
v___x_4549_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4533_ = v___y_4543_;
v___y_4534_ = v___y_4544_;
v___y_4535_ = v___y_4547_;
v___y_4536_ = v___y_4545_;
v___y_4537_ = v___x_4549_;
goto v___jp_4532_;
}
default: 
{
uint16_t v_port_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v_port_4550_ = lean_ctor_get_uint16(v_port_4546_, 0);
lean_dec_ref_known(v_port_4546_, 0);
v___x_4551_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_4552_ = lean_uint16_to_nat(v_port_4550_);
v___x_4553_ = l_Nat_reprFast(v___x_4552_);
v___x_4554_ = lean_string_append(v___x_4551_, v___x_4553_);
lean_dec_ref(v___x_4553_);
v___y_4533_ = v___y_4543_;
v___y_4534_ = v___y_4544_;
v___y_4535_ = v___y_4547_;
v___y_4536_ = v___y_4545_;
v___y_4537_ = v___x_4554_;
goto v___jp_4532_;
}
}
}
}
case 2:
{
lean_object* v_authority_4586_; lean_object* v_host_4587_; lean_object* v_port_4588_; lean_object* v___y_4590_; 
v_authority_4586_ = lean_ctor_get(v_target_4492_, 0);
lean_inc_ref(v_authority_4586_);
lean_dec_ref_known(v_target_4492_, 1);
v_host_4587_ = lean_ctor_get(v_authority_4586_, 1);
lean_inc(v_host_4587_);
v_port_4588_ = lean_ctor_get(v_authority_4586_, 2);
lean_inc(v_port_4588_);
lean_dec_ref(v_authority_4586_);
switch(lean_obj_tag(v_host_4587_))
{
case 0:
{
lean_object* v_name_4599_; 
v_name_4599_ = lean_ctor_get(v_host_4587_, 0);
lean_inc_ref(v_name_4599_);
lean_dec_ref_known(v_host_4587_, 1);
v___y_4590_ = v_name_4599_;
goto v___jp_4589_;
}
case 1:
{
lean_object* v_ipv4_4600_; lean_object* v___x_4601_; 
v_ipv4_4600_ = lean_ctor_get(v_host_4587_, 0);
lean_inc_ref(v_ipv4_4600_);
lean_dec_ref_known(v_host_4587_, 1);
v___x_4601_ = lean_uv_ntop_v4(v_ipv4_4600_);
lean_dec_ref(v_ipv4_4600_);
v___y_4590_ = v___x_4601_;
goto v___jp_4589_;
}
case 2:
{
lean_object* v_ipv6_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; 
v_ipv6_4602_ = lean_ctor_get(v_host_4587_, 0);
lean_inc_ref(v_ipv6_4602_);
lean_dec_ref_known(v_host_4587_, 1);
v___x_4603_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4604_ = lean_uv_ntop_v6(v_ipv6_4602_);
lean_dec_ref(v_ipv6_4602_);
v___x_4605_ = lean_string_append(v___x_4603_, v___x_4604_);
lean_dec_ref(v___x_4604_);
v___x_4606_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4607_ = lean_string_append(v___x_4605_, v___x_4606_);
v___y_4590_ = v___x_4607_;
goto v___jp_4589_;
}
default: 
{
lean_object* v___x_4608_; 
v___x_4608_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__2));
v___y_4590_ = v___x_4608_;
goto v___jp_4589_;
}
}
v___jp_4589_:
{
switch(lean_obj_tag(v_port_4588_))
{
case 0:
{
v___y_4494_ = v___y_4590_;
goto v___jp_4493_;
}
case 1:
{
lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4591_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_4592_ = lean_string_append(v___y_4590_, v___x_4591_);
v___y_4494_ = v___x_4592_;
goto v___jp_4493_;
}
default: 
{
uint16_t v_port_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; 
v_port_4593_ = lean_ctor_get_uint16(v_port_4588_, 0);
lean_dec_ref_known(v_port_4588_, 0);
v___x_4594_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_4595_ = lean_uint16_to_nat(v_port_4593_);
v___x_4596_ = l_Nat_reprFast(v___x_4595_);
v___x_4597_ = lean_string_append(v___x_4594_, v___x_4596_);
lean_dec_ref(v___x_4596_);
v___x_4598_ = lean_string_append(v___y_4590_, v___x_4597_);
lean_dec_ref(v___x_4597_);
v___y_4494_ = v___x_4598_;
goto v___jp_4493_;
}
}
}
}
default: 
{
lean_object* v___x_4609_; 
v___x_4609_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__0___closed__0));
v___y_4494_ = v___x_4609_;
goto v___jp_4493_;
}
}
v___jp_4493_:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; uint8_t v___x_4499_; lean_object* v___x_4500_; 
v___x_4495_ = lean_string_to_utf8(v___y_4494_);
v___x_4496_ = lean_unsigned_to_nat(0u);
v___x_4497_ = lean_byte_array_size(v_out_4491_);
v___x_4498_ = lean_byte_array_size(v___x_4495_);
v___x_4499_ = 0;
v___x_4500_ = lean_byte_array_copy_slice(v___x_4495_, v___x_4496_, v_out_4491_, v___x_4497_, v___x_4498_, v___x_4499_);
lean_dec_ref(v___x_4495_);
return v___x_4500_;
}
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Net(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_URI_Encoding(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_URI_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Net(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_URI_Encoding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_URI_instInhabitedUserInfo_default = _init_l_Std_Http_URI_instInhabitedUserInfo_default();
lean_mark_persistent(l_Std_Http_URI_instInhabitedUserInfo_default);
l_Std_Http_URI_instInhabitedUserInfo = _init_l_Std_Http_URI_instInhabitedUserInfo();
lean_mark_persistent(l_Std_Http_URI_instInhabitedUserInfo);
l_Std_Http_URI_endsInNumber___boxed__const__1 = _init_l_Std_Http_URI_endsInNumber___boxed__const__1();
lean_mark_persistent(l_Std_Http_URI_endsInNumber___boxed__const__1);
l_Std_Http_URI_instInhabitedHost_default = _init_l_Std_Http_URI_instInhabitedHost_default();
lean_mark_persistent(l_Std_Http_URI_instInhabitedHost_default);
l_Std_Http_URI_instInhabitedHost = _init_l_Std_Http_URI_instInhabitedHost();
lean_mark_persistent(l_Std_Http_URI_instInhabitedHost);
l_Std_Http_URI_instInhabitedPort_default = _init_l_Std_Http_URI_instInhabitedPort_default();
lean_mark_persistent(l_Std_Http_URI_instInhabitedPort_default);
l_Std_Http_URI_instInhabitedPort = _init_l_Std_Http_URI_instInhabitedPort();
lean_mark_persistent(l_Std_Http_URI_instInhabitedPort);
l_Std_Http_URI_instInhabitedAuthority_default = _init_l_Std_Http_URI_instInhabitedAuthority_default();
lean_mark_persistent(l_Std_Http_URI_instInhabitedAuthority_default);
l_Std_Http_URI_instInhabitedAuthority = _init_l_Std_Http_URI_instInhabitedAuthority();
lean_mark_persistent(l_Std_Http_URI_instInhabitedAuthority);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_URI_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* initialize_Std_Net(uint8_t builtin);
lean_object* initialize_Std_Http_Internal(uint8_t builtin);
lean_object* initialize_Std_Http_Data_URI_Encoding(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_URI_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Net(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_URI_Encoding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_URI_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_URI_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_URI_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
