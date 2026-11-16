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
static lean_once_cell_t l_Std_Http_URI_instReprHost___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instReprHost___lam__0___closed__4;
static lean_once_cell_t l_Std_Http_URI_instReprHost___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instReprHost___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instReprHost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instReprHost___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instReprHost___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprHost___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instReprHost = (const lean_object*)&l_Std_Http_URI_instReprHost___closed__0_value;
static const lean_string_object l_Std_Http_URI_instToStringHost___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Http_URI_instToStringHost___lam__0___closed__0 = (const lean_object*)&l_Std_Http_URI_instToStringHost___lam__0___closed__0_value;
static const lean_string_object l_Std_Http_URI_instToStringHost___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Http_URI_instToStringHost___lam__0___closed__1 = (const lean_object*)&l_Std_Http_URI_instToStringHost___lam__0___closed__1_value;
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
static const lean_string_object l_Std_Http_URI_instToStringAuthority___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_URI_instToStringAuthority___lam__0___closed__0 = (const lean_object*)&l_Std_Http_URI_instToStringAuthority___lam__0___closed__0_value;
static const lean_string_object l_Std_Http_URI_instToStringAuthority___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Http_URI_instToStringAuthority___lam__0___closed__1 = (const lean_object*)&l_Std_Http_URI_instToStringAuthority___lam__0___closed__1_value;
static const lean_string_object l_Std_Http_URI_instToStringAuthority___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_Std_Http_URI_instToStringAuthority___lam__0___closed__2 = (const lean_object*)&l_Std_Http_URI_instToStringAuthority___lam__0___closed__2_value;
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
static const lean_ctor_object l_Std_Http_URI_Query_get___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_instToStringAuthority___lam__0___closed__0_value)}};
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
lean_dec_ref(v_x_698_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___redArg(lean_object* v_t_700_, lean_object* v_k_701_){
_start:
{
lean_object* v_name_702_; lean_object* v___x_703_; 
v_name_702_ = lean_ctor_get(v_t_700_, 0);
lean_inc_ref(v_name_702_);
lean_dec_ref(v_t_700_);
v___x_703_ = lean_apply_1(v_k_701_, v_name_702_);
return v___x_703_;
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
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default___closed__0(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
return v___x_741_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default(void){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = lean_obj_once(&l_Std_Http_URI_instInhabitedHost_default___closed__0, &l_Std_Http_URI_instInhabitedHost_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedHost_default___closed__0);
return v___x_742_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost(void){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Std_Http_URI_instInhabitedHost_default;
return v___x_743_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqHost_beq(lean_object* v_x_744_, lean_object* v_x_745_){
_start:
{
switch(lean_obj_tag(v_x_744_))
{
case 0:
{
if (lean_obj_tag(v_x_745_) == 0)
{
lean_object* v_name_746_; lean_object* v_name_747_; uint8_t v___x_748_; 
v_name_746_ = lean_ctor_get(v_x_744_, 0);
v_name_747_ = lean_ctor_get(v_x_745_, 0);
v___x_748_ = lean_string_dec_eq(v_name_746_, v_name_747_);
return v___x_748_;
}
else
{
uint8_t v___x_749_; 
v___x_749_ = 0;
return v___x_749_;
}
}
case 1:
{
if (lean_obj_tag(v_x_745_) == 1)
{
lean_object* v_ipv4_750_; lean_object* v_ipv4_751_; uint8_t v___x_752_; 
v_ipv4_750_ = lean_ctor_get(v_x_744_, 0);
v_ipv4_751_ = lean_ctor_get(v_x_745_, 0);
v___x_752_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_ipv4_750_, v_ipv4_751_);
return v___x_752_;
}
else
{
uint8_t v___x_753_; 
v___x_753_ = 0;
return v___x_753_;
}
}
default: 
{
if (lean_obj_tag(v_x_745_) == 2)
{
lean_object* v_ipv6_754_; lean_object* v_ipv6_755_; uint8_t v___x_756_; 
v_ipv6_754_ = lean_ctor_get(v_x_744_, 0);
v_ipv6_755_ = lean_ctor_get(v_x_745_, 0);
v___x_756_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_ipv6_754_, v_ipv6_755_);
return v___x_756_;
}
else
{
uint8_t v___x_757_; 
v___x_757_ = 0;
return v___x_757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqHost_beq___boxed(lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
uint8_t v_res_760_; lean_object* v_r_761_; 
v_res_760_ = l_Std_Http_URI_instBEqHost_beq(v_x_758_, v_x_759_);
lean_dec_ref(v_x_759_);
lean_dec_ref(v_x_758_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__4(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(2u);
v___x_769_ = lean_nat_to_int(v___x_768_);
return v___x_769_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__5(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_unsigned_to_nat(1u);
v___x_771_ = lean_nat_to_int(v___x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0(lean_object* v_x_772_, lean_object* v_prec_773_){
_start:
{
lean_object* v___y_775_; lean_object* v_ctr_776_; lean_object* v_a_777_; lean_object* v___y_789_; lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = lean_unsigned_to_nat(1024u);
v___x_821_ = lean_nat_dec_le(v___x_820_, v_prec_773_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; 
v___x_822_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_789_ = v___x_822_;
goto v___jp_788_;
}
else
{
lean_object* v___x_823_; 
v___x_823_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_789_ = v___x_823_;
goto v___jp_788_;
}
v___jp_774_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_778_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_779_ = lean_string_append(v___x_778_, v_ctr_776_);
v___x_780_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
v___x_781_ = lean_box(1);
v___x_782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v_a_777_);
lean_inc(v___y_775_);
v___x_784_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_784_, 0, v___y_775_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = 0;
v___x_786_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*1, v___x_785_);
v___x_787_ = l_Repr_addAppParen(v___x_786_, v_prec_773_);
return v___x_787_;
}
v___jp_788_:
{
switch(lean_obj_tag(v_x_772_))
{
case 0:
{
lean_object* v_name_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_799_; 
v_name_790_ = lean_ctor_get(v_x_772_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v_x_772_);
if (v_isSharedCheck_799_ == 0)
{
v___x_792_ = v_x_772_;
v_isShared_793_ = v_isSharedCheck_799_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_name_790_);
lean_dec(v_x_772_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_799_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_794_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_795_ = l_String_quote(v_name_790_);
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 3);
lean_ctor_set(v___x_792_, 0, v___x_795_);
v___x_797_ = v___x_792_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
v___y_775_ = v___y_789_;
v_ctr_776_ = v___x_794_;
v_a_777_ = v___x_797_;
goto v___jp_774_;
}
}
}
case 1:
{
lean_object* v_ipv4_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_809_; 
v_ipv4_800_ = lean_ctor_get(v_x_772_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v_x_772_);
if (v_isSharedCheck_809_ == 0)
{
v___x_802_ = v_x_772_;
v_isShared_803_ = v_isSharedCheck_809_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_ipv4_800_);
lean_dec(v_x_772_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_809_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_804_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_805_ = lean_uv_ntop_v4(v_ipv4_800_);
lean_dec_ref(v_ipv4_800_);
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 3);
lean_ctor_set(v___x_802_, 0, v___x_805_);
v___x_807_ = v___x_802_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
v___y_775_ = v___y_789_;
v_ctr_776_ = v___x_804_;
v_a_777_ = v___x_807_;
goto v___jp_774_;
}
}
}
default: 
{
lean_object* v_ipv6_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_819_; 
v_ipv6_810_ = lean_ctor_get(v_x_772_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_x_772_);
if (v_isSharedCheck_819_ == 0)
{
v___x_812_ = v_x_772_;
v_isShared_813_ = v_isSharedCheck_819_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_ipv6_810_);
lean_dec(v_x_772_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_819_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_814_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_815_ = lean_uv_ntop_v6(v_ipv6_810_);
lean_dec_ref(v_ipv6_810_);
if (v_isShared_813_ == 0)
{
lean_ctor_set_tag(v___x_812_, 3);
lean_ctor_set(v___x_812_, 0, v___x_815_);
v___x_817_ = v___x_812_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
v___y_775_ = v___y_789_;
v_ctr_776_ = v___x_814_;
v_a_777_ = v___x_817_;
goto v___jp_774_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0___boxed(lean_object* v_x_824_, lean_object* v_prec_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_Http_URI_instReprHost___lam__0(v_x_824_, v_prec_825_);
lean_dec(v_prec_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0(lean_object* v_x_831_){
_start:
{
switch(lean_obj_tag(v_x_831_))
{
case 0:
{
lean_object* v_name_832_; 
v_name_832_ = lean_ctor_get(v_x_831_, 0);
lean_inc_ref(v_name_832_);
return v_name_832_;
}
case 1:
{
lean_object* v_ipv4_833_; lean_object* v___x_834_; 
v_ipv4_833_ = lean_ctor_get(v_x_831_, 0);
v___x_834_ = lean_uv_ntop_v4(v_ipv4_833_);
return v___x_834_;
}
default: 
{
lean_object* v_ipv6_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_ipv6_835_ = lean_ctor_get(v_x_831_, 0);
v___x_836_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_837_ = lean_uv_ntop_v6(v_ipv6_835_);
v___x_838_ = lean_string_append(v___x_836_, v___x_837_);
lean_dec_ref(v___x_837_);
v___x_839_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_840_ = lean_string_append(v___x_838_, v___x_839_);
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0___boxed(lean_object* v_x_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_Http_URI_instToStringHost___lam__0(v_x_841_);
lean_dec_ref(v_x_841_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___impl(lean_object* v_x_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = lean_obj_tag_nat(v_x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___impl___boxed(lean_object* v_x_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_Http_URI_Port_ctorIdx___impl(v_x_847_);
lean_dec(v_x_847_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg(lean_object* v_t_849_, lean_object* v_k_850_){
_start:
{
if (lean_obj_tag(v_t_849_) == 2)
{
uint16_t v_port_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_port_851_ = lean_ctor_get_uint16(v_t_849_, 0);
v___x_852_ = lean_box(v_port_851_);
v___x_853_ = lean_apply_1(v_k_850_, v___x_852_);
return v___x_853_;
}
else
{
return v_k_850_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg___boxed(lean_object* v_t_854_, lean_object* v_k_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_854_, v_k_855_);
lean_dec(v_t_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim(lean_object* v_motive_857_, lean_object* v_ctorIdx_858_, lean_object* v_t_859_, lean_object* v_h_860_, lean_object* v_k_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_859_, v_k_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___boxed(lean_object* v_motive_863_, lean_object* v_ctorIdx_864_, lean_object* v_t_865_, lean_object* v_h_866_, lean_object* v_k_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_Http_URI_Port_ctorElim(v_motive_863_, v_ctorIdx_864_, v_t_865_, v_h_866_, v_k_867_);
lean_dec(v_t_865_);
lean_dec(v_ctorIdx_864_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg(lean_object* v_t_869_, lean_object* v_omitted_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_869_, v_omitted_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg___boxed(lean_object* v_t_872_, lean_object* v_omitted_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Std_Http_URI_Port_omitted_elim___redArg(v_t_872_, v_omitted_873_);
lean_dec(v_t_872_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim(lean_object* v_motive_875_, lean_object* v_t_876_, lean_object* v_h_877_, lean_object* v_omitted_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_876_, v_omitted_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___boxed(lean_object* v_motive_880_, lean_object* v_t_881_, lean_object* v_h_882_, lean_object* v_omitted_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_Http_URI_Port_omitted_elim(v_motive_880_, v_t_881_, v_h_882_, v_omitted_883_);
lean_dec(v_t_881_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg(lean_object* v_t_885_, lean_object* v_empty_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_885_, v_empty_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg___boxed(lean_object* v_t_888_, lean_object* v_empty_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Std_Http_URI_Port_empty_elim___redArg(v_t_888_, v_empty_889_);
lean_dec(v_t_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim(lean_object* v_motive_891_, lean_object* v_t_892_, lean_object* v_h_893_, lean_object* v_empty_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_892_, v_empty_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___boxed(lean_object* v_motive_896_, lean_object* v_t_897_, lean_object* v_h_898_, lean_object* v_empty_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Std_Http_URI_Port_empty_elim(v_motive_896_, v_t_897_, v_h_898_, v_empty_899_);
lean_dec(v_t_897_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg(lean_object* v_t_901_, lean_object* v_value_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_901_, v_value_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg___boxed(lean_object* v_t_904_, lean_object* v_value_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_Http_URI_Port_value_elim___redArg(v_t_904_, v_value_905_);
lean_dec(v_t_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim(lean_object* v_motive_907_, lean_object* v_t_908_, lean_object* v_h_909_, lean_object* v_value_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_908_, v_value_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___boxed(lean_object* v_motive_912_, lean_object* v_t_913_, lean_object* v_h_914_, lean_object* v_value_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Std_Http_URI_Port_value_elim(v_motive_912_, v_t_913_, v_h_914_, v_value_915_);
lean_dec(v_t_913_);
return v_res_916_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort_default(void){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = lean_box(0);
return v___x_917_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort(void){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = lean_box(0);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr(lean_object* v_x_931_, lean_object* v_prec_932_){
_start:
{
lean_object* v___y_934_; lean_object* v___y_941_; 
switch(lean_obj_tag(v_x_931_))
{
case 0:
{
lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_947_ = lean_unsigned_to_nat(1024u);
v___x_948_ = lean_nat_dec_le(v___x_947_, v_prec_932_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
v___x_949_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_941_ = v___x_949_;
goto v___jp_940_;
}
else
{
lean_object* v___x_950_; 
v___x_950_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_941_ = v___x_950_;
goto v___jp_940_;
}
}
case 1:
{
lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_951_ = lean_unsigned_to_nat(1024u);
v___x_952_ = lean_nat_dec_le(v___x_951_, v_prec_932_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
v___x_953_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_934_ = v___x_953_;
goto v___jp_933_;
}
else
{
lean_object* v___x_954_; 
v___x_954_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_934_ = v___x_954_;
goto v___jp_933_;
}
}
default: 
{
uint16_t v_port_955_; lean_object* v___y_957_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_port_955_ = lean_ctor_get_uint16(v_x_931_, 0);
v___x_967_ = lean_unsigned_to_nat(1024u);
v___x_968_ = lean_nat_dec_le(v___x_967_, v_prec_932_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; 
v___x_969_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_957_ = v___x_969_;
goto v___jp_956_;
}
else
{
lean_object* v___x_970_; 
v___x_970_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_957_ = v___x_970_;
goto v___jp_956_;
}
v___jp_956_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_958_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__6));
v___x_959_ = lean_uint16_to_nat(v_port_955_);
v___x_960_ = l_Nat_reprFast(v___x_959_);
v___x_961_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_958_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
lean_inc(v___y_957_);
v___x_963_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_963_, 0, v___y_957_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = 0;
v___x_965_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*1, v___x_964_);
v___x_966_ = l_Repr_addAppParen(v___x_965_, v_prec_932_);
return v___x_966_;
}
}
}
v___jp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_935_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__1));
lean_inc(v___y_934_);
v___x_936_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_936_, 0, v___y_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = 0;
v___x_938_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set_uint8(v___x_938_, sizeof(void*)*1, v___x_937_);
v___x_939_ = l_Repr_addAppParen(v___x_938_, v_prec_932_);
return v___x_939_;
}
v___jp_940_:
{
lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_942_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__3));
lean_inc(v___y_941_);
v___x_943_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_943_, 0, v___y_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = 0;
v___x_945_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*1, v___x_944_);
v___x_946_ = l_Repr_addAppParen(v___x_945_, v_prec_932_);
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr___boxed(lean_object* v_x_971_, lean_object* v_prec_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Std_Http_URI_instReprPort_repr(v_x_971_, v_prec_972_);
lean_dec(v_prec_972_);
lean_dec(v_x_971_);
return v_res_973_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort_decEq(lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
switch(lean_obj_tag(v_x_976_))
{
case 0:
{
if (lean_obj_tag(v_x_977_) == 0)
{
uint8_t v___x_978_; 
v___x_978_ = 1;
return v___x_978_;
}
else
{
uint8_t v___x_979_; 
v___x_979_ = 0;
return v___x_979_;
}
}
case 1:
{
if (lean_obj_tag(v_x_977_) == 1)
{
uint8_t v___x_980_; 
v___x_980_ = 1;
return v___x_980_;
}
else
{
uint8_t v___x_981_; 
v___x_981_ = 0;
return v___x_981_;
}
}
default: 
{
if (lean_obj_tag(v_x_977_) == 2)
{
uint16_t v_port_982_; uint16_t v_port_983_; uint8_t v___x_984_; 
v_port_982_ = lean_ctor_get_uint16(v_x_976_, 0);
v_port_983_ = lean_ctor_get_uint16(v_x_977_, 0);
v___x_984_ = lean_uint16_dec_eq(v_port_982_, v_port_983_);
return v___x_984_;
}
else
{
uint8_t v___x_985_; 
v___x_985_ = 0;
return v___x_985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort_decEq___boxed(lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
uint8_t v_res_988_; lean_object* v_r_989_; 
v_res_988_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_986_, v_x_987_);
lean_dec(v_x_987_);
lean_dec(v_x_986_);
v_r_989_ = lean_box(v_res_988_);
return v_r_989_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort(lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
uint8_t v___x_992_; 
v___x_992_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_990_, v_x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort___boxed(lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
uint8_t v_res_995_; lean_object* v_r_996_; 
v_res_995_ = l_Std_Http_URI_instDecidableEqPort(v_x_993_, v_x_994_);
lean_dec(v_x_994_);
lean_dec(v_x_993_);
v_r_996_ = lean_box(v_res_995_);
return v_r_996_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_997_ = lean_box(0);
v___x_998_ = l_Std_Http_URI_instInhabitedHost_default;
v___x_999_ = lean_box(0);
v___x_1000_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_998_);
lean_ctor_set(v___x_1000_, 2, v___x_997_);
return v___x_1000_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default(void){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_obj_once(&l_Std_Http_URI_instInhabitedAuthority_default___closed__0, &l_Std_Http_URI_instInhabitedAuthority_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0);
return v___x_1001_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority(void){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Std_Http_URI_instInhabitedAuthority_default;
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
if (lean_obj_tag(v_x_1003_) == 0)
{
lean_object* v___x_1005_; 
v___x_1005_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1005_;
}
else
{
lean_object* v_val_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_val_1006_ = lean_ctor_get(v_x_1003_, 0);
lean_inc(v_val_1006_);
lean_dec_ref_known(v_x_1003_, 1);
v___x_1007_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1008_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_val_1006_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_Repr_addAppParen(v___x_1009_, v_x_1004_);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0___boxed(lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_x_1011_, v_x_1012_);
lean_dec(v_x_1012_);
return v_res_1013_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_unsigned_to_nat(8u);
v___x_1027_ = lean_nat_to_int(v___x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg(lean_object* v_x_1031_){
_start:
{
lean_object* v_userInfo_1032_; lean_object* v_host_1033_; lean_object* v_port_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v_ctr_1054_; lean_object* v_a_1055_; 
v_userInfo_1032_ = lean_ctor_get(v_x_1031_, 0);
lean_inc(v_userInfo_1032_);
v_host_1033_ = lean_ctor_get(v_x_1031_, 1);
lean_inc_ref(v_host_1033_);
v_port_1034_ = lean_ctor_get(v_x_1031_, 2);
lean_inc(v_port_1034_);
lean_dec_ref(v_x_1031_);
v___x_1035_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1036_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3));
v___x_1037_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_1038_ = lean_unsigned_to_nat(0u);
v___x_1039_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_userInfo_1032_, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1037_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = 0;
v___x_1042_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set_uint8(v___x_1042_, sizeof(void*)*1, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1036_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_box(1);
v___x_1047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_1049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v___x_1035_);
v___x_1051_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_1052_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_1033_))
{
case 0:
{
lean_object* v_name_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1092_; 
v_name_1083_ = lean_ctor_get(v_host_1033_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_host_1033_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1085_ = v_host_1033_;
v_isShared_1086_ = v_isSharedCheck_1092_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_name_1083_);
lean_dec(v_host_1033_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1092_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1087_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_1088_ = l_String_quote(v_name_1083_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 3);
lean_ctor_set(v___x_1085_, 0, v___x_1088_);
v___x_1090_ = v___x_1085_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
v_ctr_1054_ = v___x_1087_;
v_a_1055_ = v___x_1090_;
goto v___jp_1053_;
}
}
}
case 1:
{
lean_object* v_ipv4_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1102_; 
v_ipv4_1093_ = lean_ctor_get(v_host_1033_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_host_1033_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1095_ = v_host_1033_;
v_isShared_1096_ = v_isSharedCheck_1102_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_ipv4_1093_);
lean_dec(v_host_1033_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1102_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1097_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_1098_ = lean_uv_ntop_v4(v_ipv4_1093_);
lean_dec_ref(v_ipv4_1093_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 3);
lean_ctor_set(v___x_1095_, 0, v___x_1098_);
v___x_1100_ = v___x_1095_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
v_ctr_1054_ = v___x_1097_;
v_a_1055_ = v___x_1100_;
goto v___jp_1053_;
}
}
}
default: 
{
lean_object* v_ipv6_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1112_; 
v_ipv6_1103_ = lean_ctor_get(v_host_1033_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_host_1033_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1105_ = v_host_1033_;
v_isShared_1106_ = v_isSharedCheck_1112_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_ipv6_1103_);
lean_dec(v_host_1033_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1112_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1107_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_1108_ = lean_uv_ntop_v6(v_ipv6_1103_);
lean_dec_ref(v_ipv6_1103_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set_tag(v___x_1105_, 3);
lean_ctor_set(v___x_1105_, 0, v___x_1108_);
v___x_1110_ = v___x_1105_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
v_ctr_1054_ = v___x_1107_;
v_a_1055_ = v___x_1110_;
goto v___jp_1053_;
}
}
}
}
v___jp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1056_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_1057_ = lean_string_append(v___x_1056_, v_ctr_1054_);
v___x_1058_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v___x_1046_);
v___x_1060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v_a_1055_);
v___x_1061_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1052_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set_uint8(v___x_1062_, sizeof(void*)*1, v___x_1041_);
v___x_1063_ = l_Repr_addAppParen(v___x_1062_, v___x_1038_);
v___x_1064_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1051_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*1, v___x_1041_);
v___x_1066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1050_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___x_1044_);
v___x_1068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set(v___x_1068_, 1, v___x_1046_);
v___x_1069_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_1070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v___x_1035_);
v___x_1072_ = l_Std_Http_URI_instReprPort_repr(v_port_1034_, v___x_1038_);
lean_dec(v_port_1034_);
v___x_1073_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1051_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*1, v___x_1041_);
v___x_1075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1071_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1077_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_1075_);
v___x_1079_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1076_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*1, v___x_1041_);
return v___x_1082_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr(lean_object* v_x_1113_, lean_object* v_prec_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_x_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___boxed(lean_object* v_x_1116_, lean_object* v_prec_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Std_Http_URI_instReprAuthority_repr(v_x_1116_, v_prec_1117_);
lean_dec(v_prec_1117_);
return v_res_1118_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
if (lean_obj_tag(v_x_1121_) == 0)
{
if (lean_obj_tag(v_x_1122_) == 0)
{
uint8_t v___x_1123_; 
v___x_1123_ = 1;
return v___x_1123_;
}
else
{
uint8_t v___x_1124_; 
v___x_1124_ = 0;
return v___x_1124_;
}
}
else
{
if (lean_obj_tag(v_x_1122_) == 0)
{
uint8_t v___x_1125_; 
v___x_1125_ = 0;
return v___x_1125_;
}
else
{
lean_object* v_val_1126_; lean_object* v_val_1127_; uint8_t v___x_1128_; 
v_val_1126_ = lean_ctor_get(v_x_1121_, 0);
v_val_1127_ = lean_ctor_get(v_x_1122_, 0);
v___x_1128_ = l_Std_Http_URI_instBEqUserInfo_beq(v_val_1126_, v_val_1127_);
return v___x_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0___boxed(lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
uint8_t v_res_1131_; lean_object* v_r_1132_; 
v_res_1131_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_x_1129_, v_x_1130_);
lean_dec(v_x_1130_);
lean_dec(v_x_1129_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqAuthority_beq(lean_object* v_x_1133_, lean_object* v_x_1134_){
_start:
{
lean_object* v_userInfo_1135_; lean_object* v_host_1136_; lean_object* v_port_1137_; lean_object* v_userInfo_1138_; lean_object* v_host_1139_; lean_object* v_port_1140_; uint8_t v___x_1141_; 
v_userInfo_1135_ = lean_ctor_get(v_x_1133_, 0);
v_host_1136_ = lean_ctor_get(v_x_1133_, 1);
v_port_1137_ = lean_ctor_get(v_x_1133_, 2);
v_userInfo_1138_ = lean_ctor_get(v_x_1134_, 0);
v_host_1139_ = lean_ctor_get(v_x_1134_, 1);
v_port_1140_ = lean_ctor_get(v_x_1134_, 2);
v___x_1141_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_userInfo_1135_, v_userInfo_1138_);
if (v___x_1141_ == 0)
{
return v___x_1141_;
}
else
{
uint8_t v___x_1142_; 
v___x_1142_ = l_Std_Http_URI_instBEqHost_beq(v_host_1136_, v_host_1139_);
if (v___x_1142_ == 0)
{
return v___x_1142_;
}
else
{
uint8_t v___x_1143_; 
v___x_1143_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1137_, v_port_1140_);
return v___x_1143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqAuthority_beq___boxed(lean_object* v_x_1144_, lean_object* v_x_1145_){
_start:
{
uint8_t v_res_1146_; lean_object* v_r_1147_; 
v_res_1146_ = l_Std_Http_URI_instBEqAuthority_beq(v_x_1144_, v_x_1145_);
lean_dec_ref(v_x_1145_);
lean_dec_ref(v_x_1144_);
v_r_1147_ = lean_box(v_res_1146_);
return v_r_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringAuthority___lam__0(lean_object* v_auth_1153_){
_start:
{
lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v_userInfo_1160_; lean_object* v_host_1161_; lean_object* v_port_1162_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1174_; 
v_userInfo_1160_ = lean_ctor_get(v_auth_1153_, 0);
lean_inc(v_userInfo_1160_);
v_host_1161_ = lean_ctor_get(v_auth_1153_, 1);
lean_inc_ref(v_host_1161_);
v_port_1162_ = lean_ctor_get(v_auth_1153_, 2);
lean_inc(v_port_1162_);
lean_dec_ref(v_auth_1153_);
if (lean_obj_tag(v_userInfo_1160_) == 0)
{
lean_object* v___x_1184_; 
v___x_1184_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1174_ = v___x_1184_;
goto v___jp_1173_;
}
else
{
lean_object* v_val_1185_; lean_object* v_password_1186_; 
v_val_1185_ = lean_ctor_get(v_userInfo_1160_, 0);
lean_inc(v_val_1185_);
lean_dec_ref_known(v_userInfo_1160_, 1);
v_password_1186_ = lean_ctor_get(v_val_1185_, 1);
if (lean_obj_tag(v_password_1186_) == 0)
{
lean_object* v_username_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v_username_1187_ = lean_ctor_get(v_val_1185_, 0);
lean_inc_ref(v_username_1187_);
lean_dec(v_val_1185_);
v___x_1188_ = lean_string_from_utf8_unchecked(v_username_1187_);
v___x_1189_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1190_ = lean_string_append(v___x_1188_, v___x_1189_);
v___y_1174_ = v___x_1190_;
goto v___jp_1173_;
}
else
{
lean_object* v_username_1191_; lean_object* v_val_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_inc_ref(v_password_1186_);
v_username_1191_ = lean_ctor_get(v_val_1185_, 0);
lean_inc_ref(v_username_1191_);
lean_dec(v_val_1185_);
v_val_1192_ = lean_ctor_get(v_password_1186_, 0);
lean_inc(v_val_1192_);
lean_dec_ref_known(v_password_1186_, 1);
v___x_1193_ = lean_string_from_utf8_unchecked(v_username_1191_);
v___x_1194_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1195_ = lean_string_append(v___x_1193_, v___x_1194_);
v___x_1196_ = lean_string_from_utf8_unchecked(v_val_1192_);
v___x_1197_ = lean_string_append(v___x_1195_, v___x_1196_);
lean_dec_ref(v___x_1196_);
v___x_1198_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1199_ = lean_string_append(v___x_1197_, v___x_1198_);
v___y_1174_ = v___x_1199_;
goto v___jp_1173_;
}
}
v___jp_1154_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_string_append(v___y_1155_, v___y_1156_);
lean_dec_ref(v___y_1156_);
v___x_1159_ = lean_string_append(v___x_1158_, v___y_1157_);
lean_dec_ref(v___y_1157_);
return v___x_1159_;
}
v___jp_1163_:
{
switch(lean_obj_tag(v_port_1162_))
{
case 0:
{
lean_object* v___x_1166_; 
v___x_1166_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1155_ = v___y_1164_;
v___y_1156_ = v___y_1165_;
v___y_1157_ = v___x_1166_;
goto v___jp_1154_;
}
case 1:
{
lean_object* v___x_1167_; 
v___x_1167_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_1155_ = v___y_1164_;
v___y_1156_ = v___y_1165_;
v___y_1157_ = v___x_1167_;
goto v___jp_1154_;
}
default: 
{
uint16_t v_port_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_port_1168_ = lean_ctor_get_uint16(v_port_1162_, 0);
lean_dec_ref_known(v_port_1162_, 0);
v___x_1169_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1170_ = lean_uint16_to_nat(v_port_1168_);
v___x_1171_ = l_Nat_reprFast(v___x_1170_);
v___x_1172_ = lean_string_append(v___x_1169_, v___x_1171_);
lean_dec_ref(v___x_1171_);
v___y_1155_ = v___y_1164_;
v___y_1156_ = v___y_1165_;
v___y_1157_ = v___x_1172_;
goto v___jp_1154_;
}
}
}
v___jp_1173_:
{
switch(lean_obj_tag(v_host_1161_))
{
case 0:
{
lean_object* v_name_1175_; 
v_name_1175_ = lean_ctor_get(v_host_1161_, 0);
lean_inc_ref(v_name_1175_);
lean_dec_ref_known(v_host_1161_, 1);
v___y_1164_ = v___y_1174_;
v___y_1165_ = v_name_1175_;
goto v___jp_1163_;
}
case 1:
{
lean_object* v_ipv4_1176_; lean_object* v___x_1177_; 
v_ipv4_1176_ = lean_ctor_get(v_host_1161_, 0);
lean_inc_ref(v_ipv4_1176_);
lean_dec_ref_known(v_host_1161_, 1);
v___x_1177_ = lean_uv_ntop_v4(v_ipv4_1176_);
lean_dec_ref(v_ipv4_1176_);
v___y_1164_ = v___y_1174_;
v___y_1165_ = v___x_1177_;
goto v___jp_1163_;
}
default: 
{
lean_object* v_ipv6_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_ipv6_1178_ = lean_ctor_get(v_host_1161_, 0);
lean_inc_ref(v_ipv6_1178_);
lean_dec_ref_known(v_host_1161_, 1);
v___x_1179_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_1180_ = lean_uv_ntop_v6(v_ipv6_1178_);
lean_dec_ref(v_ipv6_1178_);
v___x_1181_ = lean_string_append(v___x_1179_, v___x_1180_);
lean_dec_ref(v___x_1180_);
v___x_1182_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_1183_ = lean_string_append(v___x_1181_, v___x_1182_);
v___y_1164_ = v___y_1174_;
v___y_1165_ = v___x_1183_;
goto v___jp_1163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1209_, lean_object* v_x_1210_, lean_object* v_x_1211_){
_start:
{
if (lean_obj_tag(v_x_1211_) == 0)
{
lean_dec(v_x_1209_);
return v_x_1210_;
}
else
{
lean_object* v_head_1212_; lean_object* v_tail_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1225_; 
v_head_1212_ = lean_ctor_get(v_x_1211_, 0);
v_tail_1213_ = lean_ctor_get(v_x_1211_, 1);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_x_1211_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1215_ = v_x_1211_;
v_isShared_1216_ = v_isSharedCheck_1225_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_tail_1213_);
lean_inc(v_head_1212_);
lean_dec(v_x_1211_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1225_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
lean_inc(v_x_1209_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set_tag(v___x_1215_, 5);
lean_ctor_set(v___x_1215_, 1, v_x_1209_);
lean_ctor_set(v___x_1215_, 0, v_x_1210_);
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_x_1210_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_x_1209_);
v___x_1218_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1219_ = lean_string_from_utf8_unchecked(v_head_1212_);
v___x_1220_ = l_String_quote(v___x_1219_);
v___x_1221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1218_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v_x_1210_ = v___x_1222_;
v_x_1211_ = v_tail_1213_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(lean_object* v_x_1226_, lean_object* v_x_1227_, lean_object* v_x_1228_){
_start:
{
if (lean_obj_tag(v_x_1228_) == 0)
{
lean_dec(v_x_1226_);
return v_x_1227_;
}
else
{
lean_object* v_head_1229_; lean_object* v_tail_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1242_; 
v_head_1229_ = lean_ctor_get(v_x_1228_, 0);
v_tail_1230_ = lean_ctor_get(v_x_1228_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_x_1228_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1232_ = v_x_1228_;
v_isShared_1233_ = v_isSharedCheck_1242_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_tail_1230_);
lean_inc(v_head_1229_);
lean_dec(v_x_1228_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1242_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
lean_inc(v_x_1226_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set_tag(v___x_1232_, 5);
lean_ctor_set(v___x_1232_, 1, v_x_1226_);
lean_ctor_set(v___x_1232_, 0, v_x_1227_);
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_x_1227_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_x_1226_);
v___x_1235_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1236_ = lean_string_from_utf8_unchecked(v_head_1229_);
v___x_1237_ = l_String_quote(v___x_1236_);
v___x_1238_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
v___x_1239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1235_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(v_x_1226_, v___x_1239_, v_tail_1230_);
return v___x_1240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = lean_string_from_utf8_unchecked(v___y_1243_);
v___x_1245_ = l_String_quote(v___x_1244_);
v___x_1246_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
if (lean_obj_tag(v_x_1247_) == 0)
{
lean_object* v___x_1249_; 
lean_dec(v_x_1248_);
v___x_1249_ = lean_box(0);
return v___x_1249_;
}
else
{
lean_object* v_tail_1250_; 
v_tail_1250_ = lean_ctor_get(v_x_1247_, 1);
if (lean_obj_tag(v_tail_1250_) == 0)
{
lean_object* v_head_1251_; lean_object* v___x_1252_; 
lean_dec(v_x_1248_);
v_head_1251_ = lean_ctor_get(v_x_1247_, 0);
lean_inc(v_head_1251_);
lean_dec_ref_known(v_x_1247_, 2);
v___x_1252_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1251_);
return v___x_1252_;
}
else
{
lean_object* v_head_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_inc(v_tail_1250_);
v_head_1253_ = lean_ctor_get(v_x_1247_, 0);
lean_inc(v_head_1253_);
lean_dec_ref_known(v_x_1247_, 2);
v___x_1254_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1253_);
v___x_1255_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(v_x_1248_, v___x_1254_, v_tail_1250_);
return v___x_1255_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0));
v___x_1261_ = lean_string_length(v___x_1260_);
return v___x_1261_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2);
v___x_1263_ = lean_nat_to_int(v___x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(lean_object* v_xs_1271_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1272_ = lean_array_get_size(v_xs_1271_);
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = lean_nat_dec_eq(v___x_1272_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1275_ = lean_array_to_list(v_xs_1271_);
v___x_1276_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1277_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(v___x_1275_, v___x_1276_);
v___x_1278_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1279_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
lean_ctor_set(v___x_1280_, 1, v___x_1277_);
v___x_1281_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1280_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1278_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = l_Std_Format_fill(v___x_1283_);
return v___x_1284_;
}
else
{
lean_object* v___x_1285_; 
lean_dec_ref(v_xs_1271_);
v___x_1285_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___redArg(lean_object* v_x_1298_){
_start:
{
lean_object* v_segments_1299_; uint8_t v_absolute_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1332_; 
v_segments_1299_ = lean_ctor_get(v_x_1298_, 0);
v_absolute_1300_ = lean_ctor_get_uint8(v_x_1298_, sizeof(void*)*1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_x_1298_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1302_ = v_x_1298_;
v_isShared_1303_ = v_isSharedCheck_1332_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_segments_1299_);
lean_dec(v_x_1298_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1332_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; lean_object* v___x_1311_; 
v___x_1304_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1305_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__3));
v___x_1306_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_1307_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(v_segments_1299_);
v___x_1308_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = 0;
if (v_isShared_1303_ == 0)
{
lean_ctor_set_tag(v___x_1302_, 6);
lean_ctor_set(v___x_1302_, 0, v___x_1308_);
v___x_1311_ = v___x_1302_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1308_);
v___x_1311_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*1, v___x_1309_);
v___x_1312_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1305_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1313_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = lean_box(1);
v___x_1316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1314_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__5));
v___x_1318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1316_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
v___x_1319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v___x_1304_);
v___x_1320_ = l_Bool_repr___redArg(v_absolute_1300_);
v___x_1321_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1306_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
v___x_1322_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
lean_ctor_set_uint8(v___x_1322_, sizeof(void*)*1, v___x_1309_);
v___x_1323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1319_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1325_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set(v___x_1326_, 1, v___x_1323_);
v___x_1327_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1324_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
lean_ctor_set_uint8(v___x_1330_, sizeof(void*)*1, v___x_1309_);
return v___x_1330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr(lean_object* v_x_1333_, lean_object* v_prec_1334_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Std_Http_URI_instReprPath_repr___redArg(v_x_1333_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___boxed(lean_object* v_x_1336_, lean_object* v_prec_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Std_Http_URI_instReprPath_repr(v_x_1336_, v_prec_1337_);
lean_dec(v_prec_1337_);
return v_res_1338_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(lean_object* v_xs_1341_, lean_object* v_ys_1342_, lean_object* v_x_1343_){
_start:
{
lean_object* v_zero_1344_; uint8_t v_isZero_1345_; 
v_zero_1344_ = lean_unsigned_to_nat(0u);
v_isZero_1345_ = lean_nat_dec_eq(v_x_1343_, v_zero_1344_);
if (v_isZero_1345_ == 1)
{
lean_dec(v_x_1343_);
return v_isZero_1345_;
}
else
{
lean_object* v_one_1346_; lean_object* v_n_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v_one_1346_ = lean_unsigned_to_nat(1u);
v_n_1347_ = lean_nat_sub(v_x_1343_, v_one_1346_);
lean_dec(v_x_1343_);
v___x_1348_ = lean_array_fget_borrowed(v_xs_1341_, v_n_1347_);
v___x_1349_ = lean_array_fget_borrowed(v_ys_1342_, v_n_1347_);
v___x_1350_ = lean_sarray_dec_eq(v___x_1348_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_dec(v_n_1347_);
return v___x_1350_;
}
else
{
v_x_1343_ = v_n_1347_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg___boxed(lean_object* v_xs_1352_, lean_object* v_ys_1353_, lean_object* v_x_1354_){
_start:
{
uint8_t v_res_1355_; lean_object* v_r_1356_; 
v_res_1355_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1352_, v_ys_1353_, v_x_1354_);
lean_dec_ref(v_ys_1353_);
lean_dec_ref(v_xs_1352_);
v_r_1356_ = lean_box(v_res_1355_);
return v_r_1356_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqPath_beq(lean_object* v_x_1357_, lean_object* v_x_1358_){
_start:
{
lean_object* v_segments_1359_; uint8_t v_absolute_1360_; lean_object* v_segments_1361_; uint8_t v_absolute_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_segments_1359_ = lean_ctor_get(v_x_1357_, 0);
v_absolute_1360_ = lean_ctor_get_uint8(v_x_1357_, sizeof(void*)*1);
v_segments_1361_ = lean_ctor_get(v_x_1358_, 0);
v_absolute_1362_ = lean_ctor_get_uint8(v_x_1358_, sizeof(void*)*1);
v___x_1363_ = lean_array_get_size(v_segments_1359_);
v___x_1364_ = lean_array_get_size(v_segments_1361_);
v___x_1365_ = lean_nat_dec_eq(v___x_1363_, v___x_1364_);
if (v___x_1365_ == 0)
{
return v___x_1365_;
}
else
{
uint8_t v___x_1366_; 
v___x_1366_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_segments_1359_, v_segments_1361_, v___x_1363_);
if (v___x_1366_ == 0)
{
return v___x_1366_;
}
else
{
if (v_absolute_1362_ == 0)
{
if (v_absolute_1360_ == 0)
{
return v___x_1366_;
}
else
{
return v_absolute_1362_;
}
}
else
{
return v_absolute_1360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqPath_beq___boxed(lean_object* v_x_1367_, lean_object* v_x_1368_){
_start:
{
uint8_t v_res_1369_; lean_object* v_r_1370_; 
v_res_1369_ = l_Std_Http_URI_instBEqPath_beq(v_x_1367_, v_x_1368_);
lean_dec_ref(v_x_1368_);
lean_dec_ref(v_x_1367_);
v_r_1370_ = lean_box(v_res_1369_);
return v_r_1370_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(lean_object* v_xs_1371_, lean_object* v_ys_1372_, lean_object* v_hsz_1373_, lean_object* v_x_1374_, lean_object* v_x_1375_){
_start:
{
uint8_t v___x_1376_; 
v___x_1376_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1371_, v_ys_1372_, v_x_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___boxed(lean_object* v_xs_1377_, lean_object* v_ys_1378_, lean_object* v_hsz_1379_, lean_object* v_x_1380_, lean_object* v_x_1381_){
_start:
{
uint8_t v_res_1382_; lean_object* v_r_1383_; 
v_res_1382_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(v_xs_1377_, v_ys_1378_, v_hsz_1379_, v_x_1380_, v_x_1381_);
lean_dec_ref(v_ys_1378_);
lean_dec_ref(v_xs_1377_);
v_r_1383_ = lean_box(v_res_1382_);
return v_r_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__0(lean_object* v_x_1386_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_string_from_utf8_unchecked(v_x_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__1(lean_object* v___f_1408_, lean_object* v_path_1409_){
_start:
{
lean_object* v_segments_1410_; uint8_t v_absolute_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; size_t v_sz_1414_; size_t v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v_result_1418_; 
v_segments_1410_ = lean_ctor_get(v_path_1409_, 0);
lean_inc_ref(v_segments_1410_);
v_absolute_1411_ = lean_ctor_get_uint8(v_path_1409_, sizeof(void*)*1);
lean_dec_ref(v_path_1409_);
v___x_1412_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_1413_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_1414_ = lean_array_size(v_segments_1410_);
v___x_1415_ = ((size_t)0ULL);
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1413_, v___f_1408_, v_sz_1414_, v___x_1415_, v_segments_1410_);
v___x_1417_ = lean_array_to_list(v___x_1416_);
v_result_1418_ = l_String_intercalate(v___x_1412_, v___x_1417_);
if (v_absolute_1411_ == 0)
{
return v_result_1418_;
}
else
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_string_append(v___x_1412_, v_result_1418_);
lean_dec_ref(v_result_1418_);
return v___x_1419_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Path_isEmpty(lean_object* v_p_1424_){
_start:
{
lean_object* v_segments_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v_segments_1425_ = lean_ctor_get(v_p_1424_, 0);
v___x_1426_ = lean_array_get_size(v_segments_1425_);
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_nat_dec_eq(v___x_1426_, v___x_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_isEmpty___boxed(lean_object* v_p_1429_){
_start:
{
uint8_t v_res_1430_; lean_object* v_r_1431_; 
v_res_1430_ = l_Std_Http_URI_Path_isEmpty(v_p_1429_);
lean_dec_ref(v_p_1429_);
v_r_1431_ = lean_box(v_res_1430_);
return v_r_1431_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Path_render_spec__0(lean_object* v_a_1432_, lean_object* v_i_1433_){
_start:
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = lean_byte_array_size(v_a_1432_);
v___x_1435_ = lean_nat_dec_lt(v_i_1433_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; 
lean_dec(v_i_1433_);
v___x_1436_ = lean_box(0);
return v___x_1436_;
}
else
{
uint8_t v___x_1437_; uint8_t v___x_1438_; uint8_t v___x_1439_; 
v___x_1437_ = lean_byte_array_fget(v_a_1432_, v_i_1433_);
v___x_1438_ = 58;
v___x_1439_ = lean_uint8_dec_eq(v___x_1437_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_unsigned_to_nat(1u);
v___x_1441_ = lean_nat_add(v_i_1433_, v___x_1440_);
lean_dec(v_i_1433_);
v_i_1433_ = v___x_1441_;
goto _start;
}
else
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1443_, 0, v_i_1433_);
return v___x_1443_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Path_render_spec__0___boxed(lean_object* v_a_1444_, lean_object* v_i_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Path_render_spec__0(v_a_1444_, v_i_1445_);
lean_dec_ref(v_a_1444_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_render_spec__1(size_t v_sz_1447_, size_t v_i_1448_, lean_object* v_bs_1449_){
_start:
{
uint8_t v___x_1450_; 
v___x_1450_ = lean_usize_dec_lt(v_i_1448_, v_sz_1447_);
if (v___x_1450_ == 0)
{
return v_bs_1449_;
}
else
{
lean_object* v_v_1451_; lean_object* v___x_1452_; lean_object* v_bs_x27_1453_; lean_object* v___x_1454_; size_t v___x_1455_; size_t v___x_1456_; lean_object* v___x_1457_; 
v_v_1451_ = lean_array_uget(v_bs_1449_, v_i_1448_);
v___x_1452_ = lean_unsigned_to_nat(0u);
v_bs_x27_1453_ = lean_array_uset(v_bs_1449_, v_i_1448_, v___x_1452_);
v___x_1454_ = lean_string_from_utf8_unchecked(v_v_1451_);
v___x_1455_ = ((size_t)1ULL);
v___x_1456_ = lean_usize_add(v_i_1448_, v___x_1455_);
v___x_1457_ = lean_array_uset(v_bs_x27_1453_, v_i_1448_, v___x_1454_);
v_i_1448_ = v___x_1456_;
v_bs_1449_ = v___x_1457_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_render_spec__1___boxed(lean_object* v_sz_1459_, lean_object* v_i_1460_, lean_object* v_bs_1461_){
_start:
{
size_t v_sz_boxed_1462_; size_t v_i_boxed_1463_; lean_object* v_res_1464_; 
v_sz_boxed_1462_ = lean_unbox_usize(v_sz_1459_);
lean_dec(v_sz_1459_);
v_i_boxed_1463_ = lean_unbox_usize(v_i_1460_);
lean_dec(v_i_1460_);
v_res_1464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_render_spec__1(v_sz_boxed_1462_, v_i_boxed_1463_, v_bs_1461_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_render(lean_object* v_p_1467_, uint8_t v_hasAuthority_1468_, uint8_t v_hasScheme_1469_){
_start:
{
lean_object* v___y_1471_; lean_object* v___y_1475_; uint8_t v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; uint8_t v___y_1479_; lean_object* v___y_1489_; uint8_t v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v_segments_1501_; uint8_t v_absolute_1502_; lean_object* v___y_1504_; lean_object* v___x_1511_; size_t v_sz_1512_; size_t v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v_result_1516_; 
v_segments_1501_ = lean_ctor_get(v_p_1467_, 0);
lean_inc_ref_n(v_segments_1501_, 2);
v_absolute_1502_ = lean_ctor_get_uint8(v_p_1467_, sizeof(void*)*1);
lean_dec_ref(v_p_1467_);
v___x_1511_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v_sz_1512_ = lean_array_size(v_segments_1501_);
v___x_1513_ = ((size_t)0ULL);
v___x_1514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_render_spec__1(v_sz_1512_, v___x_1513_, v_segments_1501_);
v___x_1515_ = lean_array_to_list(v___x_1514_);
v_result_1516_ = l_String_intercalate(v___x_1511_, v___x_1515_);
if (v_absolute_1502_ == 0)
{
v___y_1504_ = v_result_1516_;
goto v___jp_1503_;
}
else
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_string_append(v___x_1511_, v_result_1516_);
lean_dec_ref(v_result_1516_);
v___y_1504_ = v___x_1517_;
goto v___jp_1503_;
}
v___jp_1470_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = ((lean_object*)(l_Std_Http_URI_Path_render___closed__0));
v___x_1473_ = lean_string_append(v___x_1472_, v___y_1471_);
lean_dec_ref(v___y_1471_);
return v___x_1473_;
}
v___jp_1474_:
{
if (v_hasAuthority_1468_ == 0)
{
if (v___y_1476_ == 0)
{
if (v___y_1479_ == 0)
{
if (v_hasScheme_1469_ == 0)
{
if (lean_obj_tag(v___y_1478_) == 0)
{
lean_dec(v___y_1475_);
return v___y_1477_;
}
else
{
lean_object* v_val_1480_; lean_object* v___x_1481_; 
v_val_1480_ = lean_ctor_get(v___y_1478_, 0);
lean_inc(v_val_1480_);
lean_dec_ref_known(v___y_1478_, 1);
v___x_1481_ = l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Path_render_spec__0(v_val_1480_, v___y_1475_);
lean_dec(v_val_1480_);
if (lean_obj_tag(v___x_1481_) == 0)
{
return v___y_1477_;
}
else
{
lean_dec_ref_known(v___x_1481_, 1);
v___y_1471_ = v___y_1477_;
goto v___jp_1470_;
}
}
}
else
{
lean_dec(v___y_1478_);
lean_dec(v___y_1475_);
return v___y_1477_;
}
}
else
{
lean_dec(v___y_1478_);
lean_dec(v___y_1475_);
v___y_1471_ = v___y_1477_;
goto v___jp_1470_;
}
}
else
{
lean_dec(v___y_1478_);
lean_dec(v___y_1475_);
if (v___y_1479_ == 0)
{
return v___y_1477_;
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = ((lean_object*)(l_Std_Http_URI_Path_render___closed__1));
v___x_1483_ = lean_string_append(v___x_1482_, v___y_1477_);
lean_dec_ref(v___y_1477_);
return v___x_1483_;
}
}
}
else
{
lean_dec(v___y_1478_);
if (v___y_1476_ == 0)
{
lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___x_1484_ = lean_string_utf8_byte_size(v___y_1477_);
v___x_1485_ = lean_nat_dec_eq(v___x_1484_, v___y_1475_);
lean_dec(v___y_1475_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_1487_ = lean_string_append(v___x_1486_, v___y_1477_);
lean_dec_ref(v___y_1477_);
return v___x_1487_;
}
else
{
return v___y_1477_;
}
}
else
{
lean_dec(v___y_1475_);
return v___y_1477_;
}
}
}
v___jp_1488_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1494_ = lean_unsigned_to_nat(1u);
v___x_1495_ = lean_array_get_size(v___y_1492_);
lean_dec_ref(v___y_1492_);
v___x_1496_ = lean_nat_dec_lt(v___x_1494_, v___x_1495_);
if (v___x_1496_ == 0)
{
v___y_1475_ = v___y_1489_;
v___y_1476_ = v___y_1490_;
v___y_1477_ = v___y_1491_;
v___y_1478_ = v___y_1493_;
v___y_1479_ = v___x_1496_;
goto v___jp_1474_;
}
else
{
if (lean_obj_tag(v___y_1493_) == 0)
{
uint8_t v___x_1497_; 
v___x_1497_ = 0;
v___y_1475_ = v___y_1489_;
v___y_1476_ = v___y_1490_;
v___y_1477_ = v___y_1491_;
v___y_1478_ = v___y_1493_;
v___y_1479_ = v___x_1497_;
goto v___jp_1474_;
}
else
{
lean_object* v_val_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v_val_1498_ = lean_ctor_get(v___y_1493_, 0);
v___x_1499_ = lean_byte_array_size(v_val_1498_);
v___x_1500_ = lean_nat_dec_eq(v___x_1499_, v___y_1489_);
v___y_1475_ = v___y_1489_;
v___y_1476_ = v___y_1490_;
v___y_1477_ = v___y_1491_;
v___y_1478_ = v___y_1493_;
v___y_1479_ = v___x_1500_;
goto v___jp_1474_;
}
}
}
v___jp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1505_ = lean_unsigned_to_nat(0u);
v___x_1506_ = lean_array_get_size(v_segments_1501_);
v___x_1507_ = lean_nat_dec_lt(v___x_1505_, v___x_1506_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_box(0);
v___y_1489_ = v___x_1505_;
v___y_1490_ = v_absolute_1502_;
v___y_1491_ = v___y_1504_;
v___y_1492_ = v_segments_1501_;
v___y_1493_ = v___x_1508_;
goto v___jp_1488_;
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = lean_array_fget_borrowed(v_segments_1501_, v___x_1505_);
lean_inc(v___x_1509_);
v___x_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
v___y_1489_ = v___x_1505_;
v___y_1490_ = v_absolute_1502_;
v___y_1491_ = v___y_1504_;
v___y_1492_ = v_segments_1501_;
v___y_1493_ = v___x_1510_;
goto v___jp_1488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_render___boxed(lean_object* v_p_1518_, lean_object* v_hasAuthority_1519_, lean_object* v_hasScheme_1520_){
_start:
{
uint8_t v_hasAuthority_boxed_1521_; uint8_t v_hasScheme_boxed_1522_; lean_object* v_res_1523_; 
v_hasAuthority_boxed_1521_ = lean_unbox(v_hasAuthority_1519_);
v_hasScheme_boxed_1522_ = lean_unbox(v_hasScheme_1520_);
v_res_1523_ = l_Std_Http_URI_Path_render(v_p_1518_, v_hasAuthority_boxed_1521_, v_hasScheme_boxed_1522_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parent(lean_object* v_p_1524_){
_start:
{
lean_object* v_segments_1525_; uint8_t v_absolute_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
v_segments_1525_ = lean_ctor_get(v_p_1524_, 0);
v_absolute_1526_ = lean_ctor_get_uint8(v_p_1524_, sizeof(void*)*1);
v___x_1527_ = lean_array_get_size(v_segments_1525_);
v___x_1528_ = lean_unsigned_to_nat(0u);
v___x_1529_ = lean_nat_dec_eq(v___x_1527_, v___x_1528_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1537_; 
lean_inc_ref(v_segments_1525_);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_p_1524_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v_p_1524_, 0);
lean_dec(v_unused_1538_);
v___x_1531_ = v_p_1524_;
v_isShared_1532_ = v_isSharedCheck_1537_;
goto v_resetjp_1530_;
}
else
{
lean_dec(v_p_1524_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1537_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1533_ = lean_array_pop(v_segments_1525_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1533_);
v___x_1535_ = v___x_1531_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
lean_ctor_set_uint8(v_reuseFailAlloc_1536_, sizeof(void*)*1, v_absolute_1526_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
else
{
return v_p_1524_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join(lean_object* v_p1_1539_, lean_object* v_p2_1540_){
_start:
{
uint8_t v_absolute_1541_; 
v_absolute_1541_ = lean_ctor_get_uint8(v_p2_1540_, sizeof(void*)*1);
if (v_absolute_1541_ == 0)
{
lean_object* v_segments_1542_; lean_object* v_segments_1543_; uint8_t v_absolute_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1552_; 
v_segments_1542_ = lean_ctor_get(v_p2_1540_, 0);
v_segments_1543_ = lean_ctor_get(v_p1_1539_, 0);
v_absolute_1544_ = lean_ctor_get_uint8(v_p1_1539_, sizeof(void*)*1);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_p1_1539_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1546_ = v_p1_1539_;
v_isShared_1547_ = v_isSharedCheck_1552_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_segments_1543_);
lean_dec(v_p1_1539_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1552_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1548_ = l_Array_append___redArg(v_segments_1543_, v_segments_1542_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1548_);
v___x_1550_ = v___x_1546_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
lean_ctor_set_uint8(v_reuseFailAlloc_1551_, sizeof(void*)*1, v_absolute_1544_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
else
{
lean_dec_ref(v_p1_1539_);
lean_inc_ref(v_p2_1540_);
return v_p2_1540_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join___boxed(lean_object* v_p1_1553_, lean_object* v_p2_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Std_Http_URI_Path_join(v_p1_1553_, v_p2_1554_);
lean_dec_ref(v_p2_1554_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append(lean_object* v_p_1556_, lean_object* v_segment_1557_){
_start:
{
lean_object* v_segments_1558_; uint8_t v_absolute_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1568_; 
v_segments_1558_ = lean_ctor_get(v_p_1556_, 0);
v_absolute_1559_ = lean_ctor_get_uint8(v_p_1556_, sizeof(void*)*1);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_p_1556_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1561_ = v_p_1556_;
v_isShared_1562_ = v_isSharedCheck_1568_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_segments_1558_);
lean_dec(v_p_1556_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1568_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1563_ = l_Std_Http_URI_EncodedSegment_encode(v_segment_1557_);
v___x_1564_ = lean_array_push(v_segments_1558_, v___x_1563_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1564_);
v___x_1566_ = v___x_1561_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
lean_ctor_set_uint8(v_reuseFailAlloc_1567_, sizeof(void*)*1, v_absolute_1559_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_appendEncoded(lean_object* v_p_1569_, lean_object* v_segment_1570_){
_start:
{
lean_object* v_segments_1571_; uint8_t v_absolute_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1580_; 
v_segments_1571_ = lean_ctor_get(v_p_1569_, 0);
v_absolute_1572_ = lean_ctor_get_uint8(v_p_1569_, sizeof(void*)*1);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_p_1569_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1574_ = v_p_1569_;
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_segments_1571_);
lean_dec(v_p_1569_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1576_ = lean_array_push(v_segments_1571_, v_segment_1570_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1576_);
v___x_1578_ = v___x_1574_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
lean_ctor_set_uint8(v_reuseFailAlloc_1579_, sizeof(void*)*1, v_absolute_1572_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_1582_ = l_Std_Http_URI_EncodedSegment_encode(v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0(lean_object* v_tail_1583_, lean_object* v_output_1584_){
_start:
{
uint8_t v___x_1585_; 
v___x_1585_ = l_List_isEmpty___redArg(v_tail_1583_);
if (v___x_1585_ == 0)
{
return v_output_1584_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_obj_once(&l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0___closed__0, &l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0___closed__0);
v___x_1587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
lean_ctor_set(v___x_1587_, 1, v_output_1584_);
return v___x_1587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0___boxed(lean_object* v_tail_1588_, lean_object* v_output_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0(v_tail_1588_, v_output_1589_);
lean_dec(v_tail_1588_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(lean_object* v_input_1592_, lean_object* v_output_1593_){
_start:
{
if (lean_obj_tag(v_input_1592_) == 0)
{
lean_object* v___x_1594_; 
v___x_1594_ = l_List_reverse___redArg(v_output_1593_);
return v___x_1594_;
}
else
{
lean_object* v_head_1595_; lean_object* v_tail_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1616_; 
v_head_1595_ = lean_ctor_get(v_input_1592_, 0);
v_tail_1596_ = lean_ctor_get(v_input_1592_, 1);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_input_1592_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1598_ = v_input_1592_;
v_isShared_1599_ = v_isSharedCheck_1616_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_tail_1596_);
lean_inc(v_head_1595_);
lean_dec(v_input_1592_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1616_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
lean_inc(v_head_1595_);
v___x_1600_ = lean_string_from_utf8_unchecked(v_head_1595_);
v___x_1601_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Std_Http_URI_endsInNumber_spec__3___redArg___closed__0));
v___x_1602_ = lean_string_dec_eq(v___x_1600_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = ((lean_object*)(l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0));
v___x_1604_ = lean_string_dec_eq(v___x_1600_, v___x_1603_);
lean_dec_ref(v___x_1600_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1606_; 
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 1, v_output_1593_);
v___x_1606_ = v___x_1598_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_head_1595_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_output_1593_);
v___x_1606_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
v_input_1592_ = v_tail_1596_;
v_output_1593_ = v___x_1606_;
goto _start;
}
}
else
{
lean_del_object(v___x_1598_);
lean_dec(v_head_1595_);
if (lean_obj_tag(v_output_1593_) == 0)
{
lean_object* v___x_1609_; 
v___x_1609_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0(v_tail_1596_, v_output_1593_);
v_input_1592_ = v_tail_1596_;
v_output_1593_ = v___x_1609_;
goto _start;
}
else
{
lean_object* v_tail_1611_; lean_object* v___x_1612_; 
v_tail_1611_ = lean_ctor_get(v_output_1593_, 1);
lean_inc(v_tail_1611_);
lean_dec_ref_known(v_output_1593_, 2);
v___x_1612_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0(v_tail_1596_, v_tail_1611_);
v_input_1592_ = v_tail_1596_;
v_output_1593_ = v___x_1612_;
goto _start;
}
}
}
else
{
lean_object* v___x_1614_; 
lean_dec_ref(v___x_1600_);
lean_del_object(v___x_1598_);
lean_dec(v_head_1595_);
v___x_1614_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___lam__0(v_tail_1596_, v_output_1593_);
v_input_1592_ = v_tail_1596_;
v_output_1593_ = v___x_1614_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_normalize(lean_object* v_p_1617_){
_start:
{
lean_object* v_segments_1618_; uint8_t v_absolute_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1630_; 
v_segments_1618_ = lean_ctor_get(v_p_1617_, 0);
v_absolute_1619_ = lean_ctor_get_uint8(v_p_1617_, sizeof(void*)*1);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_p_1617_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1621_ = v_p_1617_;
v_isShared_1622_ = v_isSharedCheck_1630_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_segments_1618_);
lean_dec(v_p_1617_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1630_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1623_ = lean_array_to_list(v_segments_1618_);
v___x_1624_ = lean_box(0);
v___x_1625_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(v___x_1623_, v___x_1624_);
v___x_1626_ = lean_array_mk(v___x_1625_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1626_);
v___x_1628_ = v___x_1621_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
lean_ctor_set_uint8(v_reuseFailAlloc_1629_, sizeof(void*)*1, v_absolute_1619_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(size_t v_sz_1631_, size_t v_i_1632_, lean_object* v_bs_1633_){
_start:
{
uint8_t v___x_1634_; 
v___x_1634_ = lean_usize_dec_lt(v_i_1632_, v_sz_1631_);
if (v___x_1634_ == 0)
{
return v_bs_1633_;
}
else
{
lean_object* v_v_1635_; lean_object* v___x_1636_; lean_object* v_bs_x27_1637_; lean_object* v___y_1639_; lean_object* v___x_1644_; 
v_v_1635_ = lean_array_uget(v_bs_1633_, v_i_1632_);
v___x_1636_ = lean_unsigned_to_nat(0u);
v_bs_x27_1637_ = lean_array_uset(v_bs_1633_, v_i_1632_, v___x_1636_);
v___x_1644_ = l_Std_Http_URI_EncodedSegment_decode(v_v_1635_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_string_from_utf8_unchecked(v_v_1635_);
v___y_1639_ = v___x_1645_;
goto v___jp_1638_;
}
else
{
lean_object* v_val_1646_; 
lean_dec(v_v_1635_);
v_val_1646_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_val_1646_);
lean_dec_ref_known(v___x_1644_, 1);
v___y_1639_ = v_val_1646_;
goto v___jp_1638_;
}
v___jp_1638_:
{
size_t v___x_1640_; size_t v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = ((size_t)1ULL);
v___x_1641_ = lean_usize_add(v_i_1632_, v___x_1640_);
v___x_1642_ = lean_array_uset(v_bs_x27_1637_, v_i_1632_, v___y_1639_);
v_i_1632_ = v___x_1641_;
v_bs_1633_ = v___x_1642_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0___boxed(lean_object* v_sz_1647_, lean_object* v_i_1648_, lean_object* v_bs_1649_){
_start:
{
size_t v_sz_boxed_1650_; size_t v_i_boxed_1651_; lean_object* v_res_1652_; 
v_sz_boxed_1650_ = lean_unbox_usize(v_sz_1647_);
lean_dec(v_sz_1647_);
v_i_boxed_1651_ = lean_unbox_usize(v_i_1648_);
lean_dec(v_i_1648_);
v_res_1652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_boxed_1650_, v_i_boxed_1651_, v_bs_1649_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_toDecodedSegments(lean_object* v_p_1653_){
_start:
{
lean_object* v_segments_1654_; size_t v_sz_1655_; size_t v___x_1656_; lean_object* v___x_1657_; 
v_segments_1654_ = lean_ctor_get(v_p_1653_, 0);
lean_inc_ref(v_segments_1654_);
lean_dec_ref(v_p_1653_);
v_sz_1655_ = lean_array_size(v_segments_1654_);
v___x_1656_ = ((size_t)0ULL);
v___x_1657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_1655_, v___x_1656_, v_segments_1654_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___redArg(lean_object* v_xs_1666_){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1668_ = l_Array_repr___redArg(v___x_1667_, v_xs_1666_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1(lean_object* v_xs_1669_, lean_object* v_x_1670_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1672_ = l_Array_repr___redArg(v___x_1671_, v_xs_1669_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___boxed(lean_object* v_xs_1673_, lean_object* v_x_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Std_Http_URI_instReprQuery___aux__1(v_xs_1673_, v_x_1674_);
lean_dec(v_x_1674_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_1676_, lean_object* v_x_1677_, lean_object* v_x_1678_){
_start:
{
if (lean_obj_tag(v_x_1678_) == 0)
{
lean_dec(v_x_1676_);
return v_x_1677_;
}
else
{
lean_object* v_head_1679_; lean_object* v_tail_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1689_; 
v_head_1679_ = lean_ctor_get(v_x_1678_, 0);
v_tail_1680_ = lean_ctor_get(v_x_1678_, 1);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_x_1678_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1682_ = v_x_1678_;
v_isShared_1683_ = v_isSharedCheck_1689_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_tail_1680_);
lean_inc(v_head_1679_);
lean_dec(v_x_1678_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1689_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
lean_inc(v_x_1676_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set_tag(v___x_1682_, 5);
lean_ctor_set(v___x_1682_, 1, v_x_1676_);
lean_ctor_set(v___x_1682_, 0, v_x_1677_);
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_x_1677_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_x_1676_);
v___x_1685_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
lean_ctor_set(v___x_1686_, 1, v_head_1679_);
v_x_1677_ = v___x_1686_;
v_x_1678_ = v_tail_1680_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(lean_object* v_x_1690_, lean_object* v_x_1691_){
_start:
{
if (lean_obj_tag(v_x_1690_) == 0)
{
lean_object* v___x_1692_; 
lean_dec(v_x_1691_);
v___x_1692_ = lean_box(0);
return v___x_1692_;
}
else
{
lean_object* v_tail_1693_; 
v_tail_1693_ = lean_ctor_get(v_x_1690_, 1);
if (lean_obj_tag(v_tail_1693_) == 0)
{
lean_object* v_head_1694_; 
lean_dec(v_x_1691_);
v_head_1694_ = lean_ctor_get(v_x_1690_, 0);
lean_inc(v_head_1694_);
lean_dec_ref_known(v_x_1690_, 2);
return v_head_1694_;
}
else
{
lean_object* v_head_1695_; lean_object* v___x_1696_; 
lean_inc(v_tail_1693_);
v_head_1695_ = lean_ctor_get(v_x_1690_, 0);
lean_inc(v_head_1695_);
lean_dec_ref_known(v_x_1690_, 2);
v___x_1696_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(v_x_1691_, v_head_1695_, v_tail_1693_);
return v___x_1696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(lean_object* v_x_1697_, lean_object* v_x_1698_){
_start:
{
if (lean_obj_tag(v_x_1697_) == 0)
{
lean_object* v___x_1699_; 
v___x_1699_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1699_;
}
else
{
lean_object* v_val_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1712_; 
v_val_1700_ = lean_ctor_get(v_x_1697_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_x_1697_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1702_ = v_x_1697_;
v_isShared_1703_ = v_isSharedCheck_1712_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_val_1700_);
lean_dec(v_x_1697_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1712_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1704_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1705_ = lean_string_from_utf8_unchecked(v_val_1700_);
v___x_1706_ = l_String_quote(v___x_1705_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set_tag(v___x_1702_, 3);
lean_ctor_set(v___x_1702_, 0, v___x_1706_);
v___x_1708_ = v___x_1702_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1704_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
v___x_1710_ = l_Repr_addAppParen(v___x_1709_, v_x_1698_);
return v___x_1710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1713_, lean_object* v_x_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_x_1713_, v_x_1714_);
lean_dec(v_x_1714_);
return v_res_1715_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0));
v___x_1719_ = lean_string_length(v___x_1718_);
return v___x_1719_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2);
v___x_1721_ = lean_nat_to_int(v___x_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(lean_object* v_x_1726_){
_start:
{
lean_object* v_fst_1727_; lean_object* v_snd_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1753_; 
v_fst_1727_ = lean_ctor_get(v_x_1726_, 0);
v_snd_1728_ = lean_ctor_get(v_x_1726_, 1);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_x_1726_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1730_ = v_x_1726_;
v_isShared_1731_ = v_isSharedCheck_1753_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_snd_1728_);
lean_inc(v_fst_1727_);
lean_dec(v_x_1726_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1753_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1732_ = lean_string_from_utf8_unchecked(v_fst_1727_);
v___x_1733_ = l_String_quote(v___x_1732_);
v___x_1734_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
v___x_1735_ = lean_box(0);
if (v_isShared_1731_ == 0)
{
lean_ctor_set_tag(v___x_1730_, 1);
lean_ctor_set(v___x_1730_, 1, v___x_1735_);
lean_ctor_set(v___x_1730_, 0, v___x_1734_);
v___x_1737_ = v___x_1730_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; lean_object* v___x_1751_; 
v___x_1738_ = lean_unsigned_to_nat(0u);
v___x_1739_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_snd_1728_, v___x_1738_);
v___x_1740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
lean_ctor_set(v___x_1740_, 1, v___x_1737_);
v___x_1741_ = l_List_reverse___redArg(v___x_1740_);
v___x_1742_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1743_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(v___x_1741_, v___x_1742_);
v___x_1744_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3);
v___x_1745_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4));
v___x_1746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
lean_ctor_set(v___x_1746_, 1, v___x_1743_);
v___x_1747_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5));
v___x_1748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1746_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1744_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = 0;
v___x_1751_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1751_, 0, v___x_1749_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*1, v___x_1750_);
return v___x_1751_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(lean_object* v_x_1754_, lean_object* v_x_1755_, lean_object* v_x_1756_){
_start:
{
if (lean_obj_tag(v_x_1756_) == 0)
{
lean_dec(v_x_1754_);
return v_x_1755_;
}
else
{
lean_object* v_head_1757_; lean_object* v_tail_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1768_; 
v_head_1757_ = lean_ctor_get(v_x_1756_, 0);
v_tail_1758_ = lean_ctor_get(v_x_1756_, 1);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_x_1756_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1760_ = v_x_1756_;
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_tail_1758_);
lean_inc(v_head_1757_);
lean_dec(v_x_1756_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
lean_inc(v_x_1754_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set_tag(v___x_1760_, 5);
lean_ctor_set(v___x_1760_, 1, v_x_1754_);
lean_ctor_set(v___x_1760_, 0, v_x_1755_);
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_x_1755_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_x_1754_);
v___x_1763_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1757_);
v___x_1765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v_x_1755_ = v___x_1765_;
v_x_1756_ = v_tail_1758_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(lean_object* v_x_1769_, lean_object* v_x_1770_, lean_object* v_x_1771_){
_start:
{
if (lean_obj_tag(v_x_1771_) == 0)
{
lean_dec(v_x_1769_);
return v_x_1770_;
}
else
{
lean_object* v_head_1772_; lean_object* v_tail_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1783_; 
v_head_1772_ = lean_ctor_get(v_x_1771_, 0);
v_tail_1773_ = lean_ctor_get(v_x_1771_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_x_1771_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1775_ = v_x_1771_;
v_isShared_1776_ = v_isSharedCheck_1783_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_tail_1773_);
lean_inc(v_head_1772_);
lean_dec(v_x_1771_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1783_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
lean_inc(v_x_1769_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set_tag(v___x_1775_, 5);
lean_ctor_set(v___x_1775_, 1, v_x_1769_);
lean_ctor_set(v___x_1775_, 0, v_x_1770_);
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_x_1770_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_x_1769_);
v___x_1778_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1779_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1772_);
v___x_1780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1778_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(v_x_1769_, v___x_1780_, v_tail_1773_);
return v___x_1781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(lean_object* v_x_1784_, lean_object* v_x_1785_){
_start:
{
if (lean_obj_tag(v_x_1784_) == 0)
{
lean_object* v___x_1786_; 
lean_dec(v_x_1785_);
v___x_1786_ = lean_box(0);
return v___x_1786_;
}
else
{
lean_object* v_tail_1787_; 
v_tail_1787_ = lean_ctor_get(v_x_1784_, 1);
if (lean_obj_tag(v_tail_1787_) == 0)
{
lean_object* v_head_1788_; lean_object* v___x_1789_; 
lean_dec(v_x_1785_);
v_head_1788_ = lean_ctor_get(v_x_1784_, 0);
lean_inc(v_head_1788_);
lean_dec_ref_known(v_x_1784_, 2);
v___x_1789_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1788_);
return v___x_1789_;
}
else
{
lean_object* v_head_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_inc(v_tail_1787_);
v_head_1790_ = lean_ctor_get(v_x_1784_, 0);
lean_inc(v_head_1790_);
lean_dec_ref_known(v_x_1784_, 2);
v___x_1791_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1790_);
v___x_1792_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(v_x_1785_, v___x_1791_, v_tail_1787_);
return v___x_1792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(lean_object* v_xs_1793_){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1794_ = lean_array_get_size(v_xs_1793_);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_nat_dec_eq(v___x_1794_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1797_ = lean_array_to_list(v_xs_1793_);
v___x_1798_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1799_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(v___x_1797_, v___x_1798_);
v___x_1800_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1801_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
lean_ctor_set(v___x_1802_, 1, v___x_1799_);
v___x_1803_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1802_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1800_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = l_Std_Format_fill(v___x_1805_);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; 
lean_dec_ref(v_xs_1793_);
v___x_1807_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1807_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0(lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v___y_1808_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0___boxed(lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Std_Http_URI_instReprQuery___lam__0(v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(lean_object* v_x_1816_, lean_object* v_x_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_x_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___boxed(lean_object* v_x_1819_, lean_object* v_x_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(v_x_1819_, v_x_1820_);
lean_dec(v_x_1820_);
return v_res_1821_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1___lam__0(lean_object* v___f_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_){
_start:
{
lean_object* v_fst_1829_; lean_object* v_snd_1830_; lean_object* v_fst_1831_; lean_object* v_snd_1832_; uint8_t v___x_1833_; 
v_fst_1829_ = lean_ctor_get(v_x_1827_, 0);
lean_inc(v_fst_1829_);
v_snd_1830_ = lean_ctor_get(v_x_1827_, 1);
lean_inc(v_snd_1830_);
lean_dec_ref(v_x_1827_);
v_fst_1831_ = lean_ctor_get(v_x_1828_, 0);
lean_inc(v_fst_1831_);
v_snd_1832_ = lean_ctor_get(v_x_1828_, 1);
lean_inc(v_snd_1832_);
lean_dec_ref(v_x_1828_);
v___x_1833_ = lean_sarray_dec_eq(v_fst_1829_, v_fst_1831_);
lean_dec(v_fst_1831_);
lean_dec(v_fst_1829_);
if (v___x_1833_ == 0)
{
lean_dec(v_snd_1832_);
lean_dec(v_snd_1830_);
lean_dec_ref(v___f_1826_);
return v___x_1833_;
}
else
{
uint8_t v___x_1834_; 
v___x_1834_ = l_instBEqOption_beq___redArg(v___f_1826_, v_snd_1830_, v_snd_1832_);
return v___x_1834_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___lam__0___boxed(lean_object* v___f_1835_, lean_object* v_x_1836_, lean_object* v_x_1837_){
_start:
{
uint8_t v_res_1838_; lean_object* v_r_1839_; 
v_res_1838_ = l_Std_Http_URI_instBEqQuery___aux__1___lam__0(v___f_1835_, v_x_1836_, v_x_1837_);
v_r_1839_ = lean_box(v_res_1838_);
return v_r_1839_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1(lean_object* v_xs_1843_, lean_object* v_ys_1844_){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1845_ = lean_array_get_size(v_xs_1843_);
v___x_1846_ = lean_array_get_size(v_ys_1844_);
v___x_1847_ = lean_nat_dec_eq(v___x_1845_, v___x_1846_);
if (v___x_1847_ == 0)
{
return v___x_1847_;
}
else
{
lean_object* v___f_1848_; uint8_t v___x_1849_; 
v___f_1848_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__1));
v___x_1849_ = l_Array_isEqvAux___redArg(v_xs_1843_, v_ys_1844_, v___f_1848_, v___x_1845_);
return v___x_1849_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___boxed(lean_object* v_xs_1850_, lean_object* v_ys_1851_){
_start:
{
uint8_t v_res_1852_; lean_object* v_r_1853_; 
v_res_1852_ = l_Std_Http_URI_instBEqQuery___aux__1(v_xs_1850_, v_ys_1851_);
lean_dec_ref(v_ys_1851_);
lean_dec_ref(v_xs_1850_);
v_r_1853_ = lean_box(v_res_1852_);
return v_r_1853_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
if (lean_obj_tag(v_x_1854_) == 0)
{
if (lean_obj_tag(v_x_1855_) == 0)
{
uint8_t v___x_1856_; 
v___x_1856_ = 1;
return v___x_1856_;
}
else
{
uint8_t v___x_1857_; 
v___x_1857_ = 0;
return v___x_1857_;
}
}
else
{
if (lean_obj_tag(v_x_1855_) == 0)
{
uint8_t v___x_1858_; 
v___x_1858_ = 0;
return v___x_1858_;
}
else
{
lean_object* v_val_1859_; lean_object* v_val_1860_; uint8_t v___x_1861_; 
v_val_1859_ = lean_ctor_get(v_x_1854_, 0);
v_val_1860_ = lean_ctor_get(v_x_1855_, 0);
v___x_1861_ = lean_sarray_dec_eq(v_val_1859_, v_val_1860_);
return v___x_1861_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0___boxed(lean_object* v_x_1862_, lean_object* v_x_1863_){
_start:
{
uint8_t v_res_1864_; lean_object* v_r_1865_; 
v_res_1864_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_x_1862_, v_x_1863_);
lean_dec(v_x_1863_);
lean_dec(v_x_1862_);
v_r_1865_ = lean_box(v_res_1864_);
return v_r_1865_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(lean_object* v_xs_1866_, lean_object* v_ys_1867_, lean_object* v_x_1868_){
_start:
{
lean_object* v_zero_1869_; uint8_t v_isZero_1870_; 
v_zero_1869_ = lean_unsigned_to_nat(0u);
v_isZero_1870_ = lean_nat_dec_eq(v_x_1868_, v_zero_1869_);
if (v_isZero_1870_ == 1)
{
lean_dec(v_x_1868_);
return v_isZero_1870_;
}
else
{
lean_object* v_one_1871_; lean_object* v_n_1872_; lean_object* v___x_1873_; lean_object* v_fst_1874_; lean_object* v_snd_1875_; lean_object* v___x_1876_; lean_object* v_fst_1877_; lean_object* v_snd_1878_; uint8_t v___x_1879_; 
v_one_1871_ = lean_unsigned_to_nat(1u);
v_n_1872_ = lean_nat_sub(v_x_1868_, v_one_1871_);
lean_dec(v_x_1868_);
v___x_1873_ = lean_array_fget_borrowed(v_xs_1866_, v_n_1872_);
v_fst_1874_ = lean_ctor_get(v___x_1873_, 0);
v_snd_1875_ = lean_ctor_get(v___x_1873_, 1);
v___x_1876_ = lean_array_fget_borrowed(v_ys_1867_, v_n_1872_);
v_fst_1877_ = lean_ctor_get(v___x_1876_, 0);
v_snd_1878_ = lean_ctor_get(v___x_1876_, 1);
v___x_1879_ = lean_sarray_dec_eq(v_fst_1874_, v_fst_1877_);
if (v___x_1879_ == 0)
{
lean_dec(v_n_1872_);
return v___x_1879_;
}
else
{
uint8_t v___x_1880_; 
v___x_1880_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_snd_1875_, v_snd_1878_);
if (v___x_1880_ == 0)
{
lean_dec(v_n_1872_);
return v___x_1880_;
}
else
{
v_x_1868_ = v_n_1872_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg___boxed(lean_object* v_xs_1882_, lean_object* v_ys_1883_, lean_object* v_x_1884_){
_start:
{
uint8_t v_res_1885_; lean_object* v_r_1886_; 
v_res_1885_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1882_, v_ys_1883_, v_x_1884_);
lean_dec_ref(v_ys_1883_);
lean_dec_ref(v_xs_1882_);
v_r_1886_ = lean_box(v_res_1885_);
return v_r_1886_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___lam__0(lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1889_ = lean_array_get_size(v___y_1887_);
v___x_1890_ = lean_array_get_size(v___y_1888_);
v___x_1891_ = lean_nat_dec_eq(v___x_1889_, v___x_1890_);
if (v___x_1891_ == 0)
{
return v___x_1891_;
}
else
{
uint8_t v___x_1892_; 
v___x_1892_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v___y_1887_, v___y_1888_, v___x_1889_);
return v___x_1892_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___lam__0___boxed(lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
uint8_t v_res_1895_; lean_object* v_r_1896_; 
v_res_1895_ = l_Std_Http_URI_instBEqQuery___lam__0(v___y_1893_, v___y_1894_);
lean_dec_ref(v___y_1894_);
lean_dec_ref(v___y_1893_);
v_r_1896_ = lean_box(v_res_1895_);
return v_r_1896_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(lean_object* v_xs_1899_, lean_object* v_ys_1900_, lean_object* v_hsz_1901_, lean_object* v_x_1902_, lean_object* v_x_1903_){
_start:
{
uint8_t v___x_1904_; 
v___x_1904_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1899_, v_ys_1900_, v_x_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___boxed(lean_object* v_xs_1905_, lean_object* v_ys_1906_, lean_object* v_hsz_1907_, lean_object* v_x_1908_, lean_object* v_x_1909_){
_start:
{
uint8_t v_res_1910_; lean_object* v_r_1911_; 
v_res_1910_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(v_xs_1905_, v_ys_1906_, v_hsz_1907_, v_x_1908_, v_x_1909_);
lean_dec_ref(v_ys_1906_);
lean_dec_ref(v_xs_1905_);
v_r_1911_ = lean_box(v_res_1910_);
return v_r_1911_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___redArg(lean_object* v_a_1912_, lean_object* v_x_1913_){
_start:
{
if (lean_obj_tag(v_x_1913_) == 0)
{
uint8_t v___x_1914_; 
v___x_1914_ = 0;
return v___x_1914_;
}
else
{
lean_object* v_key_1915_; lean_object* v_tail_1916_; uint8_t v___x_1917_; 
v_key_1915_ = lean_ctor_get(v_x_1913_, 0);
v_tail_1916_ = lean_ctor_get(v_x_1913_, 2);
v___x_1917_ = lean_sarray_dec_eq(v_key_1915_, v_a_1912_);
if (v___x_1917_ == 0)
{
v_x_1913_ = v_tail_1916_;
goto _start;
}
else
{
return v___x_1917_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___redArg___boxed(lean_object* v_a_1919_, lean_object* v_x_1920_){
_start:
{
uint8_t v_res_1921_; lean_object* v_r_1922_; 
v_res_1921_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___redArg(v_a_1919_, v_x_1920_);
lean_dec(v_x_1920_);
lean_dec_ref(v_a_1919_);
v_r_1922_ = lean_box(v_res_1921_);
return v_r_1922_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0___redArg(lean_object* v_m_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v_buckets_1925_; lean_object* v___x_1926_; uint64_t v___x_1927_; uint64_t v___x_1928_; uint64_t v___x_1929_; uint64_t v_fold_1930_; uint64_t v___x_1931_; uint64_t v___x_1932_; uint64_t v___x_1933_; size_t v___x_1934_; size_t v___x_1935_; size_t v___x_1936_; size_t v___x_1937_; size_t v___x_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
v_buckets_1925_ = lean_ctor_get(v_m_1923_, 1);
v___x_1926_ = lean_array_get_size(v_buckets_1925_);
v___x_1927_ = lean_byte_array_hash(v_a_1924_);
v___x_1928_ = 32ULL;
v___x_1929_ = lean_uint64_shift_right(v___x_1927_, v___x_1928_);
v_fold_1930_ = lean_uint64_xor(v___x_1927_, v___x_1929_);
v___x_1931_ = 16ULL;
v___x_1932_ = lean_uint64_shift_right(v_fold_1930_, v___x_1931_);
v___x_1933_ = lean_uint64_xor(v_fold_1930_, v___x_1932_);
v___x_1934_ = lean_uint64_to_usize(v___x_1933_);
v___x_1935_ = lean_usize_of_nat(v___x_1926_);
v___x_1936_ = ((size_t)1ULL);
v___x_1937_ = lean_usize_sub(v___x_1935_, v___x_1936_);
v___x_1938_ = lean_usize_land(v___x_1934_, v___x_1937_);
v___x_1939_ = lean_array_uget_borrowed(v_buckets_1925_, v___x_1938_);
v___x_1940_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___redArg(v_a_1924_, v___x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0___redArg___boxed(lean_object* v_m_1941_, lean_object* v_a_1942_){
_start:
{
uint8_t v_res_1943_; lean_object* v_r_1944_; 
v_res_1943_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0___redArg(v_m_1941_, v_a_1942_);
lean_dec_ref(v_a_1942_);
lean_dec_ref(v_m_1941_);
v_r_1944_ = lean_box(v_res_1943_);
return v_r_1944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_1945_, lean_object* v_x_1946_){
_start:
{
if (lean_obj_tag(v_x_1946_) == 0)
{
return v_x_1945_;
}
else
{
lean_object* v_key_1947_; lean_object* v_value_1948_; lean_object* v_tail_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1972_; 
v_key_1947_ = lean_ctor_get(v_x_1946_, 0);
v_value_1948_ = lean_ctor_get(v_x_1946_, 1);
v_tail_1949_ = lean_ctor_get(v_x_1946_, 2);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_x_1946_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1951_ = v_x_1946_;
v_isShared_1952_ = v_isSharedCheck_1972_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_tail_1949_);
lean_inc(v_value_1948_);
lean_inc(v_key_1947_);
lean_dec(v_x_1946_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1972_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; uint64_t v___x_1954_; uint64_t v___x_1955_; uint64_t v___x_1956_; uint64_t v_fold_1957_; uint64_t v___x_1958_; uint64_t v___x_1959_; uint64_t v___x_1960_; size_t v___x_1961_; size_t v___x_1962_; size_t v___x_1963_; size_t v___x_1964_; size_t v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1953_ = lean_array_get_size(v_x_1945_);
v___x_1954_ = lean_byte_array_hash(v_key_1947_);
v___x_1955_ = 32ULL;
v___x_1956_ = lean_uint64_shift_right(v___x_1954_, v___x_1955_);
v_fold_1957_ = lean_uint64_xor(v___x_1954_, v___x_1956_);
v___x_1958_ = 16ULL;
v___x_1959_ = lean_uint64_shift_right(v_fold_1957_, v___x_1958_);
v___x_1960_ = lean_uint64_xor(v_fold_1957_, v___x_1959_);
v___x_1961_ = lean_uint64_to_usize(v___x_1960_);
v___x_1962_ = lean_usize_of_nat(v___x_1953_);
v___x_1963_ = ((size_t)1ULL);
v___x_1964_ = lean_usize_sub(v___x_1962_, v___x_1963_);
v___x_1965_ = lean_usize_land(v___x_1961_, v___x_1964_);
v___x_1966_ = lean_array_uget_borrowed(v_x_1945_, v___x_1965_);
lean_inc(v___x_1966_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 2, v___x_1966_);
v___x_1968_ = v___x_1951_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_key_1947_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_value_1948_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_array_uset(v_x_1945_, v___x_1965_, v___x_1968_);
v_x_1945_ = v___x_1969_;
v_x_1946_ = v_tail_1949_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3___redArg(lean_object* v_i_1973_, lean_object* v_source_1974_, lean_object* v_target_1975_){
_start:
{
lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1976_ = lean_array_get_size(v_source_1974_);
v___x_1977_ = lean_nat_dec_lt(v_i_1973_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_dec_ref(v_source_1974_);
lean_dec(v_i_1973_);
return v_target_1975_;
}
else
{
lean_object* v_es_1978_; lean_object* v___x_1979_; lean_object* v_source_1980_; lean_object* v_target_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v_es_1978_ = lean_array_fget(v_source_1974_, v_i_1973_);
v___x_1979_ = lean_box(0);
v_source_1980_ = lean_array_fset(v_source_1974_, v_i_1973_, v___x_1979_);
v_target_1981_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3_spec__5___redArg(v_target_1975_, v_es_1978_);
v___x_1982_ = lean_unsigned_to_nat(1u);
v___x_1983_ = lean_nat_add(v_i_1973_, v___x_1982_);
lean_dec(v_i_1973_);
v_i_1973_ = v___x_1983_;
v_source_1974_ = v_source_1980_;
v_target_1975_ = v_target_1981_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2___redArg(lean_object* v_data_1985_){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v_nbuckets_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1986_ = lean_array_get_size(v_data_1985_);
v___x_1987_ = lean_unsigned_to_nat(2u);
v_nbuckets_1988_ = lean_nat_mul(v___x_1986_, v___x_1987_);
v___x_1989_ = lean_unsigned_to_nat(0u);
v___x_1990_ = lean_box(0);
v___x_1991_ = lean_mk_array(v_nbuckets_1988_, v___x_1990_);
v___x_1992_ = lean_array_propagate_mark(v_data_1985_, v___x_1991_);
v___x_1993_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3___redArg(v___x_1989_, v_data_1985_, v___x_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1___redArg(lean_object* v_m_1994_, lean_object* v_a_1995_, lean_object* v_b_1996_){
_start:
{
lean_object* v_size_1997_; lean_object* v_buckets_1998_; lean_object* v___x_1999_; uint64_t v___x_2000_; uint64_t v___x_2001_; uint64_t v___x_2002_; uint64_t v_fold_2003_; uint64_t v___x_2004_; uint64_t v___x_2005_; uint64_t v___x_2006_; size_t v___x_2007_; size_t v___x_2008_; size_t v___x_2009_; size_t v___x_2010_; size_t v___x_2011_; lean_object* v_bkt_2012_; uint8_t v___x_2013_; 
v_size_1997_ = lean_ctor_get(v_m_1994_, 0);
v_buckets_1998_ = lean_ctor_get(v_m_1994_, 1);
v___x_1999_ = lean_array_get_size(v_buckets_1998_);
v___x_2000_ = lean_byte_array_hash(v_a_1995_);
v___x_2001_ = 32ULL;
v___x_2002_ = lean_uint64_shift_right(v___x_2000_, v___x_2001_);
v_fold_2003_ = lean_uint64_xor(v___x_2000_, v___x_2002_);
v___x_2004_ = 16ULL;
v___x_2005_ = lean_uint64_shift_right(v_fold_2003_, v___x_2004_);
v___x_2006_ = lean_uint64_xor(v_fold_2003_, v___x_2005_);
v___x_2007_ = lean_uint64_to_usize(v___x_2006_);
v___x_2008_ = lean_usize_of_nat(v___x_1999_);
v___x_2009_ = ((size_t)1ULL);
v___x_2010_ = lean_usize_sub(v___x_2008_, v___x_2009_);
v___x_2011_ = lean_usize_land(v___x_2007_, v___x_2010_);
v_bkt_2012_ = lean_array_uget_borrowed(v_buckets_1998_, v___x_2011_);
v___x_2013_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___redArg(v_a_1995_, v_bkt_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2034_; 
lean_inc_ref(v_buckets_1998_);
lean_inc(v_size_1997_);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_m_1994_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; lean_object* v_unused_2036_; 
v_unused_2035_ = lean_ctor_get(v_m_1994_, 1);
lean_dec(v_unused_2035_);
v_unused_2036_ = lean_ctor_get(v_m_1994_, 0);
lean_dec(v_unused_2036_);
v___x_2015_ = v_m_1994_;
v_isShared_2016_ = v_isSharedCheck_2034_;
goto v_resetjp_2014_;
}
else
{
lean_dec(v_m_1994_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2034_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2017_; lean_object* v_size_x27_2018_; lean_object* v___x_2019_; lean_object* v_buckets_x27_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2017_ = lean_unsigned_to_nat(1u);
v_size_x27_2018_ = lean_nat_add(v_size_1997_, v___x_2017_);
lean_dec(v_size_1997_);
lean_inc(v_bkt_2012_);
v___x_2019_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2019_, 0, v_a_1995_);
lean_ctor_set(v___x_2019_, 1, v_b_1996_);
lean_ctor_set(v___x_2019_, 2, v_bkt_2012_);
v_buckets_x27_2020_ = lean_array_uset(v_buckets_1998_, v___x_2011_, v___x_2019_);
v___x_2021_ = lean_unsigned_to_nat(4u);
v___x_2022_ = lean_nat_mul(v_size_x27_2018_, v___x_2021_);
v___x_2023_ = lean_unsigned_to_nat(3u);
v___x_2024_ = lean_nat_div(v___x_2022_, v___x_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_array_get_size(v_buckets_x27_2020_);
v___x_2026_ = lean_nat_dec_le(v___x_2024_, v___x_2025_);
lean_dec(v___x_2024_);
if (v___x_2026_ == 0)
{
lean_object* v_val_2027_; lean_object* v___x_2029_; 
v_val_2027_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2___redArg(v_buckets_x27_2020_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 1, v_val_2027_);
lean_ctor_set(v___x_2015_, 0, v_size_x27_2018_);
v___x_2029_ = v___x_2015_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_size_x27_2018_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v_val_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
else
{
lean_object* v___x_2032_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 1, v_buckets_x27_2020_);
lean_ctor_set(v___x_2015_, 0, v_size_x27_2018_);
v___x_2032_ = v___x_2015_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_size_x27_2018_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_buckets_x27_2020_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_dec(v_b_1996_);
lean_dec_ref(v_a_1995_);
return v_m_1994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_names_spec__2(lean_object* v_as_2037_, size_t v_i_2038_, size_t v_stop_2039_, lean_object* v_b_2040_){
_start:
{
lean_object* v___y_2042_; uint8_t v___x_2046_; 
v___x_2046_ = lean_usize_dec_eq(v_i_2038_, v_stop_2039_);
if (v___x_2046_ == 0)
{
lean_object* v_fst_2047_; lean_object* v_snd_2048_; lean_object* v___x_2049_; lean_object* v_fst_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2061_; 
v_fst_2047_ = lean_ctor_get(v_b_2040_, 0);
v_snd_2048_ = lean_ctor_get(v_b_2040_, 1);
v___x_2049_ = lean_array_uget(v_as_2037_, v_i_2038_);
v_fst_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v___x_2049_, 1);
lean_dec(v_unused_2062_);
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2061_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_fst_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2061_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
uint8_t v___x_2054_; 
v___x_2054_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0___redArg(v_fst_2047_, v_fst_2050_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2059_; 
lean_inc(v_snd_2048_);
lean_inc(v_fst_2047_);
lean_dec_ref(v_b_2040_);
v___x_2055_ = lean_box(0);
lean_inc(v_fst_2050_);
v___x_2056_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1___redArg(v_fst_2047_, v_fst_2050_, v___x_2055_);
v___x_2057_ = lean_array_push(v_snd_2048_, v_fst_2050_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 1, v___x_2057_);
lean_ctor_set(v___x_2052_, 0, v___x_2056_);
v___x_2059_ = v___x_2052_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
v___y_2042_ = v___x_2059_;
goto v___jp_2041_;
}
}
else
{
lean_del_object(v___x_2052_);
lean_dec(v_fst_2050_);
v___y_2042_ = v_b_2040_;
goto v___jp_2041_;
}
}
}
else
{
return v_b_2040_;
}
v___jp_2041_:
{
size_t v___x_2043_; size_t v___x_2044_; 
v___x_2043_ = ((size_t)1ULL);
v___x_2044_ = lean_usize_add(v_i_2038_, v___x_2043_);
v_i_2038_ = v___x_2044_;
v_b_2040_ = v___y_2042_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_names_spec__2___boxed(lean_object* v_as_2063_, lean_object* v_i_2064_, lean_object* v_stop_2065_, lean_object* v_b_2066_){
_start:
{
size_t v_i_boxed_2067_; size_t v_stop_boxed_2068_; lean_object* v_res_2069_; 
v_i_boxed_2067_ = lean_unbox_usize(v_i_2064_);
lean_dec(v_i_2064_);
v_stop_boxed_2068_ = lean_unbox_usize(v_stop_2065_);
lean_dec(v_stop_2065_);
v_res_2069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_names_spec__2(v_as_2063_, v_i_boxed_2067_, v_stop_boxed_2068_, v_b_2066_);
lean_dec_ref(v_as_2063_);
return v_res_2069_;
}
}
static lean_object* _init_l_Std_Http_URI_Query_names___closed__1(void){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2072_ = lean_box(0);
v___x_2073_ = lean_unsigned_to_nat(16u);
v___x_2074_ = lean_mk_array(v___x_2073_, v___x_2072_);
return v___x_2074_;
}
}
static lean_object* _init_l_Std_Http_URI_Query_names___closed__2(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = lean_obj_once(&l_Std_Http_URI_Query_names___closed__1, &l_Std_Http_URI_Query_names___closed__1_once, _init_l_Std_Http_URI_Query_names___closed__1);
v___x_2076_ = lean_unsigned_to_nat(0u);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
lean_ctor_set(v___x_2077_, 1, v___x_2075_);
return v___x_2077_;
}
}
static lean_object* _init_l_Std_Http_URI_Query_names___closed__3(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v_init_2080_; 
v___x_2078_ = ((lean_object*)(l_Std_Http_URI_Query_names___closed__0));
v___x_2079_ = lean_obj_once(&l_Std_Http_URI_Query_names___closed__2, &l_Std_Http_URI_Query_names___closed__2_once, _init_l_Std_Http_URI_Query_names___closed__2);
v_init_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_init_2080_, 0, v___x_2079_);
lean_ctor_set(v_init_2080_, 1, v___x_2078_);
return v_init_2080_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names(lean_object* v_query_2081_){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2082_ = lean_unsigned_to_nat(0u);
v___x_2083_ = ((lean_object*)(l_Std_Http_URI_Query_names___closed__0));
v___x_2084_ = lean_array_get_size(v_query_2081_);
v___x_2085_ = lean_nat_dec_lt(v___x_2082_, v___x_2084_);
if (v___x_2085_ == 0)
{
return v___x_2083_;
}
else
{
lean_object* v_init_2086_; size_t v___x_2087_; size_t v___x_2088_; lean_object* v___x_2089_; lean_object* v_snd_2090_; 
v_init_2086_ = lean_obj_once(&l_Std_Http_URI_Query_names___closed__3, &l_Std_Http_URI_Query_names___closed__3_once, _init_l_Std_Http_URI_Query_names___closed__3);
v___x_2087_ = ((size_t)0ULL);
v___x_2088_ = lean_usize_of_nat(v___x_2084_);
v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_names_spec__2(v_query_2081_, v___x_2087_, v___x_2088_, v_init_2086_);
v_snd_2090_ = lean_ctor_get(v___x_2089_, 1);
lean_inc(v_snd_2090_);
lean_dec_ref(v___x_2089_);
return v_snd_2090_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names___boxed(lean_object* v_query_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Std_Http_URI_Query_names(v_query_2091_);
lean_dec_ref(v_query_2091_);
return v_res_2092_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0(lean_object* v_00_u03b2_2093_, lean_object* v_m_2094_, lean_object* v_a_2095_){
_start:
{
uint8_t v___x_2096_; 
v___x_2096_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0___redArg(v_m_2094_, v_a_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0___boxed(lean_object* v_00_u03b2_2097_, lean_object* v_m_2098_, lean_object* v_a_2099_){
_start:
{
uint8_t v_res_2100_; lean_object* v_r_2101_; 
v_res_2100_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0(v_00_u03b2_2097_, v_m_2098_, v_a_2099_);
lean_dec_ref(v_a_2099_);
lean_dec_ref(v_m_2098_);
v_r_2101_ = lean_box(v_res_2100_);
return v_r_2101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1(lean_object* v_00_u03b2_2102_, lean_object* v_m_2103_, lean_object* v_a_2104_, lean_object* v_b_2105_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1___redArg(v_m_2103_, v_a_2104_, v_b_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0(lean_object* v_00_u03b2_2107_, lean_object* v_a_2108_, lean_object* v_x_2109_){
_start:
{
uint8_t v___x_2110_; 
v___x_2110_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___redArg(v_a_2108_, v_x_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2111_, lean_object* v_a_2112_, lean_object* v_x_2113_){
_start:
{
uint8_t v_res_2114_; lean_object* v_r_2115_; 
v_res_2114_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Http_URI_Query_names_spec__0_spec__0(v_00_u03b2_2111_, v_a_2112_, v_x_2113_);
lean_dec(v_x_2113_);
lean_dec_ref(v_a_2112_);
v_r_2115_ = lean_box(v_res_2114_);
return v_r_2115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2(lean_object* v_00_u03b2_2116_, lean_object* v_data_2117_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2___redArg(v_data_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2119_, lean_object* v_i_2120_, lean_object* v_source_2121_, lean_object* v_target_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3___redArg(v_i_2120_, v_source_2121_, v_target_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_2124_, lean_object* v_x_2125_, lean_object* v_x_2126_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Http_URI_Query_names_spec__1_spec__2_spec__3_spec__5___redArg(v_x_2125_, v_x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(size_t v_sz_2128_, size_t v_i_2129_, lean_object* v_bs_2130_){
_start:
{
uint8_t v___x_2131_; 
v___x_2131_ = lean_usize_dec_lt(v_i_2129_, v_sz_2128_);
if (v___x_2131_ == 0)
{
return v_bs_2130_;
}
else
{
lean_object* v_v_2132_; lean_object* v_snd_2133_; lean_object* v___x_2134_; lean_object* v_bs_x27_2135_; size_t v___x_2136_; size_t v___x_2137_; lean_object* v___x_2138_; 
v_v_2132_ = lean_array_uget_borrowed(v_bs_2130_, v_i_2129_);
v_snd_2133_ = lean_ctor_get(v_v_2132_, 1);
lean_inc(v_snd_2133_);
v___x_2134_ = lean_unsigned_to_nat(0u);
v_bs_x27_2135_ = lean_array_uset(v_bs_2130_, v_i_2129_, v___x_2134_);
v___x_2136_ = ((size_t)1ULL);
v___x_2137_ = lean_usize_add(v_i_2129_, v___x_2136_);
v___x_2138_ = lean_array_uset(v_bs_x27_2135_, v_i_2129_, v_snd_2133_);
v_i_2129_ = v___x_2137_;
v_bs_2130_ = v___x_2138_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0___boxed(lean_object* v_sz_2140_, lean_object* v_i_2141_, lean_object* v_bs_2142_){
_start:
{
size_t v_sz_boxed_2143_; size_t v_i_boxed_2144_; lean_object* v_res_2145_; 
v_sz_boxed_2143_ = lean_unbox_usize(v_sz_2140_);
lean_dec(v_sz_2140_);
v_i_boxed_2144_ = lean_unbox_usize(v_i_2141_);
lean_dec(v_i_2141_);
v_res_2145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_boxed_2143_, v_i_boxed_2144_, v_bs_2142_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_values(lean_object* v_query_2146_){
_start:
{
size_t v_sz_2147_; size_t v___x_2148_; lean_object* v___x_2149_; 
v_sz_2147_ = lean_array_size(v_query_2146_);
v___x_2148_ = ((size_t)0ULL);
v___x_2149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_2147_, v___x_2148_, v_query_2146_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray(lean_object* v_query_2150_){
_start:
{
lean_inc_ref(v_query_2150_);
return v_query_2150_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray___boxed(lean_object* v_query_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Std_Http_URI_Query_toArray(v_query_2151_);
lean_dec_ref(v_query_2151_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1___redArg(lean_object* v_s_2153_, lean_object* v_replacement_2154_, lean_object* v_a_2155_, lean_object* v_b_2156_){
_start:
{
lean_object* v_str_2157_; lean_object* v_startInclusive_2158_; lean_object* v_endExclusive_2159_; lean_object* v___x_2160_; uint8_t v_decide_2161_; 
v_str_2157_ = lean_ctor_get(v_s_2153_, 0);
v_startInclusive_2158_ = lean_ctor_get(v_s_2153_, 1);
v_endExclusive_2159_ = lean_ctor_get(v_s_2153_, 2);
v___x_2160_ = lean_nat_sub(v_endExclusive_2159_, v_startInclusive_2158_);
v_decide_2161_ = lean_nat_dec_eq(v_a_2155_, v___x_2160_);
lean_dec(v___x_2160_);
if (v_decide_2161_ == 0)
{
lean_object* v___x_2162_; uint32_t v___x_2163_; uint32_t v___x_2164_; uint8_t v___x_2165_; 
v___x_2162_ = lean_nat_add(v_startInclusive_2158_, v_a_2155_);
v___x_2163_ = lean_string_utf8_get_fast(v_str_2157_, v___x_2162_);
v___x_2164_ = 61;
v___x_2165_ = lean_uint32_dec_eq(v___x_2163_, v___x_2164_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v_str_2169_; lean_object* v_startInclusive_2170_; lean_object* v_endExclusive_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2166_ = lean_string_utf8_next_fast(v_str_2157_, v___x_2162_);
lean_dec(v___x_2162_);
v___x_2167_ = lean_nat_sub(v___x_2166_, v_startInclusive_2158_);
lean_inc_ref(v_s_2153_);
v___x_2168_ = l_String_Slice_slice_x21(v_s_2153_, v_a_2155_, v___x_2167_);
lean_dec(v_a_2155_);
v_str_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc_ref(v_str_2169_);
v_startInclusive_2170_ = lean_ctor_get(v___x_2168_, 1);
lean_inc(v_startInclusive_2170_);
v_endExclusive_2171_ = lean_ctor_get(v___x_2168_, 2);
lean_inc(v_endExclusive_2171_);
lean_dec_ref(v___x_2168_);
v___x_2172_ = lean_string_utf8_extract_fast(v_str_2169_, v_startInclusive_2170_, v_endExclusive_2171_);
lean_dec(v_endExclusive_2171_);
lean_dec(v_startInclusive_2170_);
lean_dec_ref(v_str_2169_);
v___x_2173_ = lean_string_append(v_b_2156_, v___x_2172_);
lean_dec_ref(v___x_2172_);
v_a_2155_ = v___x_2167_;
v_b_2156_ = v___x_2173_;
goto _start;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2175_ = lean_string_utf8_next_fast(v_str_2157_, v___x_2162_);
v___x_2176_ = lean_nat_sub(v___x_2175_, v___x_2162_);
lean_dec(v___x_2162_);
v___x_2177_ = lean_nat_add(v_a_2155_, v___x_2176_);
lean_dec(v___x_2176_);
lean_dec(v_a_2155_);
v___x_2178_ = lean_unsigned_to_nat(0u);
v___x_2179_ = lean_string_utf8_byte_size(v_replacement_2154_);
v___x_2180_ = lean_string_utf8_extract_fast(v_replacement_2154_, v___x_2178_, v___x_2179_);
v___x_2181_ = lean_string_append(v_b_2156_, v___x_2180_);
lean_dec_ref(v___x_2180_);
v_a_2155_ = v___x_2177_;
v_b_2156_ = v___x_2181_;
goto _start;
}
}
else
{
lean_dec(v_a_2155_);
lean_dec_ref(v_s_2153_);
return v_b_2156_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1___redArg___boxed(lean_object* v_s_2183_, lean_object* v_replacement_2184_, lean_object* v_a_2185_, lean_object* v_b_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1___redArg(v_s_2183_, v_replacement_2184_, v_a_2185_, v_b_2186_);
lean_dec_ref(v_replacement_2184_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1___redArg(lean_object* v_s_2188_, lean_object* v_replacement_2189_){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1___redArg(v_s_2188_, v_replacement_2189_, v___x_2191_, v___x_2190_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1___redArg___boxed(lean_object* v_s_2193_, lean_object* v_replacement_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1___redArg(v_s_2193_, v_replacement_2194_);
lean_dec_ref(v_replacement_2194_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Query_formatQueryParam_spec__0(lean_object* v_a_2196_, lean_object* v_i_2197_){
_start:
{
lean_object* v___x_2198_; uint8_t v___x_2199_; 
v___x_2198_ = lean_byte_array_size(v_a_2196_);
v___x_2199_ = lean_nat_dec_lt(v_i_2197_, v___x_2198_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; 
lean_dec(v_i_2197_);
v___x_2200_ = lean_box(0);
return v___x_2200_;
}
else
{
uint8_t v___x_2201_; uint8_t v___x_2202_; uint8_t v___x_2203_; 
v___x_2201_ = lean_byte_array_fget(v_a_2196_, v_i_2197_);
v___x_2202_ = 61;
v___x_2203_ = lean_uint8_dec_eq(v___x_2201_, v___x_2202_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = lean_unsigned_to_nat(1u);
v___x_2205_ = lean_nat_add(v_i_2197_, v___x_2204_);
lean_dec(v_i_2197_);
v_i_2197_ = v___x_2205_;
goto _start;
}
else
{
lean_object* v___x_2207_; 
v___x_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2207_, 0, v_i_2197_);
return v___x_2207_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Query_formatQueryParam_spec__0___boxed(lean_object* v_a_2208_, lean_object* v_i_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Query_formatQueryParam_spec__0(v_a_2208_, v_i_2209_);
lean_dec_ref(v_a_2208_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object* v_key_2213_, lean_object* v_value_2214_){
_start:
{
lean_object* v___y_2216_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = lean_unsigned_to_nat(0u);
v___x_2223_ = l_ByteArray_findIdx_x3f_loop___at___00Std_Http_URI_Query_formatQueryParam_spec__0(v_key_2213_, v___x_2222_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_string_from_utf8_unchecked(v_key_2213_);
v___y_2216_ = v___x_2224_;
goto v___jp_2215_;
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec_ref_known(v___x_2223_, 1);
v___x_2225_ = lean_string_from_utf8_unchecked(v_key_2213_);
v___x_2226_ = ((lean_object*)(l_Std_Http_URI_Query_formatQueryParam___closed__1));
v___x_2227_ = lean_string_utf8_byte_size(v___x_2225_);
v___x_2228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2225_);
lean_ctor_set(v___x_2228_, 1, v___x_2222_);
lean_ctor_set(v___x_2228_, 2, v___x_2227_);
v___x_2229_ = l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1___redArg(v___x_2228_, v___x_2226_);
v___y_2216_ = v___x_2229_;
goto v___jp_2215_;
}
v___jp_2215_:
{
if (lean_obj_tag(v_value_2214_) == 0)
{
return v___y_2216_;
}
else
{
lean_object* v_val_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v_val_2217_ = lean_ctor_get(v_value_2214_, 0);
lean_inc(v_val_2217_);
lean_dec_ref_known(v_value_2214_, 1);
v___x_2218_ = ((lean_object*)(l_Std_Http_URI_Query_formatQueryParam___closed__0));
v___x_2219_ = lean_string_append(v___y_2216_, v___x_2218_);
v___x_2220_ = lean_string_from_utf8_unchecked(v_val_2217_);
v___x_2221_ = lean_string_append(v___x_2219_, v___x_2220_);
lean_dec_ref(v___x_2220_);
return v___x_2221_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1(lean_object* v_s_2230_, uint32_t v_pattern_2231_, lean_object* v_replacement_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1___redArg(v_s_2230_, v_replacement_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1___boxed(lean_object* v_s_2234_, lean_object* v_pattern_2235_, lean_object* v_replacement_2236_){
_start:
{
uint32_t v_pattern_boxed_2237_; lean_object* v_res_2238_; 
v_pattern_boxed_2237_ = lean_unbox_uint32(v_pattern_2235_);
lean_dec(v_pattern_2235_);
v_res_2238_ = l_String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1(v_s_2234_, v_pattern_boxed_2237_, v_replacement_2236_);
lean_dec_ref(v_replacement_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1(lean_object* v_s_2239_, lean_object* v_replacement_2240_, lean_object* v_inst_2241_, lean_object* v_R_2242_, lean_object* v_a_2243_, lean_object* v_b_2244_, lean_object* v_c_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1___redArg(v_s_2239_, v_replacement_2240_, v_a_2243_, v_b_2244_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1___boxed(lean_object* v_s_2247_, lean_object* v_replacement_2248_, lean_object* v_inst_2249_, lean_object* v_R_2250_, lean_object* v_a_2251_, lean_object* v_b_2252_, lean_object* v_c_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Std_Http_URI_Query_formatQueryParam_spec__1_spec__1(v_s_2247_, v_replacement_2248_, v_inst_2249_, v_R_2250_, v_a_2251_, v_b_2252_, v_c_2253_);
lean_dec_ref(v_replacement_2248_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(lean_object* v_key_2258_, lean_object* v_as_2259_, size_t v_sz_2260_, size_t v_i_2261_, lean_object* v_b_2262_){
_start:
{
uint8_t v___x_2263_; 
v___x_2263_ = lean_usize_dec_lt(v_i_2261_, v_sz_2260_);
if (v___x_2263_ == 0)
{
lean_inc_ref(v_b_2262_);
return v_b_2262_;
}
else
{
lean_object* v_a_2264_; lean_object* v_fst_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
v_a_2264_ = lean_array_uget_borrowed(v_as_2259_, v_i_2261_);
v_fst_2265_ = lean_ctor_get(v_a_2264_, 0);
v___x_2266_ = lean_box(0);
v___x_2267_ = lean_sarray_dec_eq(v_fst_2265_, v_key_2258_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; size_t v___x_2269_; size_t v___x_2270_; 
v___x_2268_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v___x_2269_ = ((size_t)1ULL);
v___x_2270_ = lean_usize_add(v_i_2261_, v___x_2269_);
v_i_2261_ = v___x_2270_;
v_b_2262_ = v___x_2268_;
goto _start;
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
lean_inc(v_a_2264_);
v___x_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2272_, 0, v_a_2264_);
v___x_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_ctor_set(v___x_2274_, 1, v___x_2266_);
return v___x_2274_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___boxed(lean_object* v_key_2275_, lean_object* v_as_2276_, lean_object* v_sz_2277_, lean_object* v_i_2278_, lean_object* v_b_2279_){
_start:
{
size_t v_sz_boxed_2280_; size_t v_i_boxed_2281_; lean_object* v_res_2282_; 
v_sz_boxed_2280_ = lean_unbox_usize(v_sz_2277_);
lean_dec(v_sz_2277_);
v_i_boxed_2281_ = lean_unbox_usize(v_i_2278_);
lean_dec(v_i_2278_);
v_res_2282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_2275_, v_as_2276_, v_sz_boxed_2280_, v_i_boxed_2281_, v_b_2279_);
lean_dec_ref(v_b_2279_);
lean_dec_ref(v_as_2276_);
lean_dec_ref(v_key_2275_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f(lean_object* v_query_2283_, lean_object* v_key_2284_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; size_t v_sz_2287_; size_t v___x_2288_; lean_object* v___x_2289_; lean_object* v_fst_2290_; 
v___x_2285_ = lean_box(0);
v___x_2286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v_sz_2287_ = lean_array_size(v_query_2283_);
v___x_2288_ = ((size_t)0ULL);
v___x_2289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_2284_, v_query_2283_, v_sz_2287_, v___x_2288_, v___x_2286_);
v_fst_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_fst_2290_);
lean_dec_ref(v___x_2289_);
if (lean_obj_tag(v_fst_2290_) == 0)
{
return v___x_2285_;
}
else
{
lean_object* v_val_2291_; 
v_val_2291_ = lean_ctor_get(v_fst_2290_, 0);
lean_inc(v_val_2291_);
lean_dec_ref_known(v_fst_2290_, 1);
if (lean_obj_tag(v_val_2291_) == 0)
{
return v___x_2285_;
}
else
{
lean_object* v_val_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2300_; 
v_val_2292_ = lean_ctor_get(v_val_2291_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_val_2291_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2294_ = v_val_2291_;
v_isShared_2295_ = v_isSharedCheck_2300_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_val_2292_);
lean_dec(v_val_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2300_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v_snd_2296_; lean_object* v___x_2298_; 
v_snd_2296_ = lean_ctor_get(v_val_2292_, 1);
lean_inc(v_snd_2296_);
lean_dec(v_val_2292_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v_snd_2296_);
v___x_2298_ = v___x_2294_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_snd_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f___boxed(lean_object* v_query_2301_, lean_object* v_key_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_2301_, v_key_2302_);
lean_dec_ref(v_key_2302_);
lean_dec_ref(v_query_2301_);
return v_res_2303_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs(lean_object* v_key_2304_, lean_object* v_name_2305_){
_start:
{
uint8_t v___x_2306_; 
v___x_2306_ = l_Std_Http_URI_EncodedQueryString_decodesTo___redArg(v_name_2305_, v_key_2304_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs___boxed(lean_object* v_key_2307_, lean_object* v_name_2308_){
_start:
{
uint8_t v_res_2309_; lean_object* v_r_2310_; 
v_res_2309_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs(v_key_2307_, v_name_2308_);
lean_dec_ref(v_name_2308_);
lean_dec_ref(v_key_2307_);
v_r_2310_ = lean_box(v_res_2309_);
return v_r_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_find_x3f_spec__0(lean_object* v_key_2311_, lean_object* v_as_2312_, size_t v_sz_2313_, size_t v_i_2314_, lean_object* v_b_2315_){
_start:
{
uint8_t v___x_2316_; 
v___x_2316_ = lean_usize_dec_lt(v_i_2314_, v_sz_2313_);
if (v___x_2316_ == 0)
{
lean_inc_ref(v_b_2315_);
return v_b_2315_;
}
else
{
lean_object* v_a_2317_; lean_object* v_fst_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v_a_2317_ = lean_array_uget_borrowed(v_as_2312_, v_i_2314_);
v_fst_2318_ = lean_ctor_get(v_a_2317_, 0);
v___x_2319_ = lean_box(0);
v___x_2320_ = l_Std_Http_URI_EncodedQueryString_decodesTo___redArg(v_fst_2318_, v_key_2311_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; size_t v___x_2322_; size_t v___x_2323_; 
v___x_2321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v___x_2322_ = ((size_t)1ULL);
v___x_2323_ = lean_usize_add(v_i_2314_, v___x_2322_);
v_i_2314_ = v___x_2323_;
v_b_2315_ = v___x_2321_;
goto _start;
}
else
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_inc(v_a_2317_);
v___x_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2325_, 0, v_a_2317_);
v___x_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___x_2319_);
return v___x_2327_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_find_x3f_spec__0___boxed(lean_object* v_key_2328_, lean_object* v_as_2329_, lean_object* v_sz_2330_, lean_object* v_i_2331_, lean_object* v_b_2332_){
_start:
{
size_t v_sz_boxed_2333_; size_t v_i_boxed_2334_; lean_object* v_res_2335_; 
v_sz_boxed_2333_ = lean_unbox_usize(v_sz_2330_);
lean_dec(v_sz_2330_);
v_i_boxed_2334_ = lean_unbox_usize(v_i_2331_);
lean_dec(v_i_2331_);
v_res_2335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_find_x3f_spec__0(v_key_2328_, v_as_2329_, v_sz_boxed_2333_, v_i_boxed_2334_, v_b_2332_);
lean_dec_ref(v_b_2332_);
lean_dec_ref(v_as_2329_);
lean_dec_ref(v_key_2328_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f(lean_object* v_query_2336_, lean_object* v_key_2337_){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; size_t v_sz_2340_; size_t v___x_2341_; lean_object* v___x_2342_; lean_object* v_fst_2343_; 
v___x_2338_ = lean_box(0);
v___x_2339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v_sz_2340_ = lean_array_size(v_query_2336_);
v___x_2341_ = ((size_t)0ULL);
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_find_x3f_spec__0(v_key_2337_, v_query_2336_, v_sz_2340_, v___x_2341_, v___x_2339_);
v_fst_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_fst_2343_);
lean_dec_ref(v___x_2342_);
if (lean_obj_tag(v_fst_2343_) == 0)
{
return v___x_2338_;
}
else
{
lean_object* v_val_2344_; 
v_val_2344_ = lean_ctor_get(v_fst_2343_, 0);
lean_inc(v_val_2344_);
lean_dec_ref_known(v_fst_2343_, 1);
if (lean_obj_tag(v_val_2344_) == 0)
{
return v___x_2338_;
}
else
{
lean_object* v_val_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2353_; 
v_val_2345_ = lean_ctor_get(v_val_2344_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v_val_2344_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2347_ = v_val_2344_;
v_isShared_2348_ = v_isSharedCheck_2353_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_val_2345_);
lean_dec(v_val_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2353_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v_snd_2349_; lean_object* v___x_2351_; 
v_snd_2349_ = lean_ctor_get(v_val_2345_, 1);
lean_inc(v_snd_2349_);
lean_dec(v_val_2345_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 0, v_snd_2349_);
v___x_2351_ = v___x_2347_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_snd_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f___boxed(lean_object* v_query_2354_, lean_object* v_key_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Std_Http_URI_Query_find_x3f(v_query_2354_, v_key_2355_);
lean_dec_ref(v_key_2355_);
lean_dec_ref(v_query_2354_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(lean_object* v_key_2357_, lean_object* v_as_2358_, size_t v_i_2359_, size_t v_stop_2360_, lean_object* v_b_2361_){
_start:
{
lean_object* v___y_2363_; uint8_t v___x_2367_; 
v___x_2367_ = lean_usize_dec_eq(v_i_2359_, v_stop_2360_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; lean_object* v_fst_2369_; lean_object* v_snd_2370_; uint8_t v___x_2371_; 
v___x_2368_ = lean_array_uget_borrowed(v_as_2358_, v_i_2359_);
v_fst_2369_ = lean_ctor_get(v___x_2368_, 0);
v_snd_2370_ = lean_ctor_get(v___x_2368_, 1);
v___x_2371_ = lean_sarray_dec_eq(v_fst_2369_, v_key_2357_);
if (v___x_2371_ == 0)
{
v___y_2363_ = v_b_2361_;
goto v___jp_2362_;
}
else
{
lean_object* v___x_2372_; 
lean_inc(v_snd_2370_);
v___x_2372_ = lean_array_push(v_b_2361_, v_snd_2370_);
v___y_2363_ = v___x_2372_;
goto v___jp_2362_;
}
}
else
{
return v_b_2361_;
}
v___jp_2362_:
{
size_t v___x_2364_; size_t v___x_2365_; 
v___x_2364_ = ((size_t)1ULL);
v___x_2365_ = lean_usize_add(v_i_2359_, v___x_2364_);
v_i_2359_ = v___x_2365_;
v_b_2361_ = v___y_2363_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0___boxed(lean_object* v_key_2373_, lean_object* v_as_2374_, lean_object* v_i_2375_, lean_object* v_stop_2376_, lean_object* v_b_2377_){
_start:
{
size_t v_i_boxed_2378_; size_t v_stop_boxed_2379_; lean_object* v_res_2380_; 
v_i_boxed_2378_ = lean_unbox_usize(v_i_2375_);
lean_dec(v_i_2375_);
v_stop_boxed_2379_ = lean_unbox_usize(v_stop_2376_);
lean_dec(v_stop_2376_);
v_res_2380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_2373_, v_as_2374_, v_i_boxed_2378_, v_stop_boxed_2379_, v_b_2377_);
lean_dec_ref(v_as_2374_);
lean_dec_ref(v_key_2373_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(lean_object* v_key_2383_, lean_object* v_as_2384_, lean_object* v_start_2385_, lean_object* v_stop_2386_){
_start:
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_2388_ = lean_nat_dec_lt(v_start_2385_, v_stop_2386_);
if (v___x_2388_ == 0)
{
return v___x_2387_;
}
else
{
lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2389_ = lean_array_get_size(v_as_2384_);
v___x_2390_ = lean_nat_dec_le(v_stop_2386_, v___x_2389_);
if (v___x_2390_ == 0)
{
uint8_t v___x_2391_; 
v___x_2391_ = lean_nat_dec_lt(v_start_2385_, v___x_2389_);
if (v___x_2391_ == 0)
{
return v___x_2387_;
}
else
{
size_t v___x_2392_; size_t v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = lean_usize_of_nat(v_start_2385_);
v___x_2393_ = lean_usize_of_nat(v___x_2389_);
v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_2383_, v_as_2384_, v___x_2392_, v___x_2393_, v___x_2387_);
return v___x_2394_;
}
}
else
{
size_t v___x_2395_; size_t v___x_2396_; lean_object* v___x_2397_; 
v___x_2395_ = lean_usize_of_nat(v_start_2385_);
v___x_2396_ = lean_usize_of_nat(v_stop_2386_);
v___x_2397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_2383_, v_as_2384_, v___x_2395_, v___x_2396_, v___x_2387_);
return v___x_2397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___boxed(lean_object* v_key_2398_, lean_object* v_as_2399_, lean_object* v_start_2400_, lean_object* v_stop_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_2398_, v_as_2399_, v_start_2400_, v_stop_2401_);
lean_dec(v_stop_2401_);
lean_dec(v_start_2400_);
lean_dec_ref(v_as_2399_);
lean_dec_ref(v_key_2398_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded(lean_object* v_query_2403_, lean_object* v_key_2404_){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = lean_unsigned_to_nat(0u);
v___x_2406_ = lean_array_get_size(v_query_2403_);
v___x_2407_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_2404_, v_query_2403_, v___x_2405_, v___x_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded___boxed(lean_object* v_query_2408_, lean_object* v_key_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Std_Http_URI_Query_findAllEncoded(v_query_2408_, v_key_2409_);
lean_dec_ref(v_key_2409_);
lean_dec_ref(v_query_2408_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0(lean_object* v_key_2411_, lean_object* v_as_2412_, size_t v_i_2413_, size_t v_stop_2414_, lean_object* v_b_2415_){
_start:
{
lean_object* v___y_2417_; uint8_t v___x_2421_; 
v___x_2421_ = lean_usize_dec_eq(v_i_2413_, v_stop_2414_);
if (v___x_2421_ == 0)
{
lean_object* v___x_2422_; lean_object* v_fst_2423_; lean_object* v_snd_2424_; uint8_t v___x_2425_; 
v___x_2422_ = lean_array_uget_borrowed(v_as_2412_, v_i_2413_);
v_fst_2423_ = lean_ctor_get(v___x_2422_, 0);
v_snd_2424_ = lean_ctor_get(v___x_2422_, 1);
v___x_2425_ = l_Std_Http_URI_EncodedQueryString_decodesTo___redArg(v_fst_2423_, v_key_2411_);
if (v___x_2425_ == 0)
{
v___y_2417_ = v_b_2415_;
goto v___jp_2416_;
}
else
{
lean_object* v___x_2426_; 
lean_inc(v_snd_2424_);
v___x_2426_ = lean_array_push(v_b_2415_, v_snd_2424_);
v___y_2417_ = v___x_2426_;
goto v___jp_2416_;
}
}
else
{
return v_b_2415_;
}
v___jp_2416_:
{
size_t v___x_2418_; size_t v___x_2419_; 
v___x_2418_ = ((size_t)1ULL);
v___x_2419_ = lean_usize_add(v_i_2413_, v___x_2418_);
v_i_2413_ = v___x_2419_;
v_b_2415_ = v___y_2417_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0___boxed(lean_object* v_key_2427_, lean_object* v_as_2428_, lean_object* v_i_2429_, lean_object* v_stop_2430_, lean_object* v_b_2431_){
_start:
{
size_t v_i_boxed_2432_; size_t v_stop_boxed_2433_; lean_object* v_res_2434_; 
v_i_boxed_2432_ = lean_unbox_usize(v_i_2429_);
lean_dec(v_i_2429_);
v_stop_boxed_2433_ = lean_unbox_usize(v_stop_2430_);
lean_dec(v_stop_2430_);
v_res_2434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0(v_key_2427_, v_as_2428_, v_i_boxed_2432_, v_stop_boxed_2433_, v_b_2431_);
lean_dec_ref(v_as_2428_);
lean_dec_ref(v_key_2427_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0(lean_object* v_key_2435_, lean_object* v_as_2436_, lean_object* v_start_2437_, lean_object* v_stop_2438_){
_start:
{
lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2439_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_2440_ = lean_nat_dec_lt(v_start_2437_, v_stop_2438_);
if (v___x_2440_ == 0)
{
return v___x_2439_;
}
else
{
lean_object* v___x_2441_; uint8_t v___x_2442_; 
v___x_2441_ = lean_array_get_size(v_as_2436_);
v___x_2442_ = lean_nat_dec_le(v_stop_2438_, v___x_2441_);
if (v___x_2442_ == 0)
{
uint8_t v___x_2443_; 
v___x_2443_ = lean_nat_dec_lt(v_start_2437_, v___x_2441_);
if (v___x_2443_ == 0)
{
return v___x_2439_;
}
else
{
size_t v___x_2444_; size_t v___x_2445_; lean_object* v___x_2446_; 
v___x_2444_ = lean_usize_of_nat(v_start_2437_);
v___x_2445_ = lean_usize_of_nat(v___x_2441_);
v___x_2446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0(v_key_2435_, v_as_2436_, v___x_2444_, v___x_2445_, v___x_2439_);
return v___x_2446_;
}
}
else
{
size_t v___x_2447_; size_t v___x_2448_; lean_object* v___x_2449_; 
v___x_2447_ = lean_usize_of_nat(v_start_2437_);
v___x_2448_ = lean_usize_of_nat(v_stop_2438_);
v___x_2449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0(v_key_2435_, v_as_2436_, v___x_2447_, v___x_2448_, v___x_2439_);
return v___x_2449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0___boxed(lean_object* v_key_2450_, lean_object* v_as_2451_, lean_object* v_start_2452_, lean_object* v_stop_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0(v_key_2450_, v_as_2451_, v_start_2452_, v_stop_2453_);
lean_dec(v_stop_2453_);
lean_dec(v_start_2452_);
lean_dec_ref(v_as_2451_);
lean_dec_ref(v_key_2450_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll(lean_object* v_query_2455_, lean_object* v_key_2456_){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = lean_unsigned_to_nat(0u);
v___x_2458_ = lean_array_get_size(v_query_2455_);
v___x_2459_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0(v_key_2456_, v_query_2455_, v___x_2457_, v___x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll___boxed(lean_object* v_query_2460_, lean_object* v_key_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Std_Http_URI_Query_findAll(v_query_2460_, v_key_2461_);
lean_dec_ref(v_key_2461_);
lean_dec_ref(v_query_2460_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert(lean_object* v_query_2463_, lean_object* v_key_2464_, lean_object* v_value_2465_){
_start:
{
lean_object* v_encodedKey_2466_; lean_object* v_encodedValue_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v_encodedKey_2466_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_2464_);
v_encodedValue_2467_ = l_Std_Http_URI_EncodedQueryParam_encode(v_value_2465_);
v___x_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2468_, 0, v_encodedValue_2467_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v_encodedKey_2466_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = lean_array_push(v_query_2463_, v___x_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object* v_query_2471_, lean_object* v_key_2472_, lean_object* v_value_2473_){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v_key_2472_);
lean_ctor_set(v___x_2474_, 1, v_value_2473_);
v___x_2475_ = lean_array_push(v_query_2471_, v___x_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_ofList(lean_object* v_pairs_2479_){
_start:
{
lean_object* v___x_2480_; 
v___x_2480_ = lean_array_mk(v_pairs_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(lean_object* v_key_2481_, lean_object* v_as_2482_, size_t v_i_2483_, size_t v_stop_2484_){
_start:
{
uint8_t v___x_2485_; 
v___x_2485_ = lean_usize_dec_eq(v_i_2483_, v_stop_2484_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v_fst_2487_; uint8_t v___x_2488_; 
v___x_2486_ = lean_array_uget_borrowed(v_as_2482_, v_i_2483_);
v_fst_2487_ = lean_ctor_get(v___x_2486_, 0);
v___x_2488_ = lean_sarray_dec_eq(v_fst_2487_, v_key_2481_);
if (v___x_2488_ == 0)
{
size_t v___x_2489_; size_t v___x_2490_; 
v___x_2489_ = ((size_t)1ULL);
v___x_2490_ = lean_usize_add(v_i_2483_, v___x_2489_);
v_i_2483_ = v___x_2490_;
goto _start;
}
else
{
return v___x_2488_;
}
}
else
{
uint8_t v___x_2492_; 
v___x_2492_ = 0;
return v___x_2492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(lean_object* v_key_2493_, lean_object* v_as_2494_, lean_object* v_i_2495_, lean_object* v_stop_2496_){
_start:
{
size_t v_i_boxed_2497_; size_t v_stop_boxed_2498_; uint8_t v_res_2499_; lean_object* v_r_2500_; 
v_i_boxed_2497_ = lean_unbox_usize(v_i_2495_);
lean_dec(v_i_2495_);
v_stop_boxed_2498_ = lean_unbox_usize(v_stop_2496_);
lean_dec(v_stop_2496_);
v_res_2499_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_2493_, v_as_2494_, v_i_boxed_2497_, v_stop_boxed_2498_);
lean_dec_ref(v_as_2494_);
lean_dec_ref(v_key_2493_);
v_r_2500_ = lean_box(v_res_2499_);
return v_r_2500_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_containsEncoded(lean_object* v_query_2501_, lean_object* v_key_2502_){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; uint8_t v___x_2505_; 
v___x_2503_ = lean_unsigned_to_nat(0u);
v___x_2504_ = lean_array_get_size(v_query_2501_);
v___x_2505_ = lean_nat_dec_lt(v___x_2503_, v___x_2504_);
if (v___x_2505_ == 0)
{
return v___x_2505_;
}
else
{
if (v___x_2505_ == 0)
{
return v___x_2505_;
}
else
{
size_t v___x_2506_; size_t v___x_2507_; uint8_t v___x_2508_; 
v___x_2506_ = ((size_t)0ULL);
v___x_2507_ = lean_usize_of_nat(v___x_2504_);
v___x_2508_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_2502_, v_query_2501_, v___x_2506_, v___x_2507_);
return v___x_2508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_containsEncoded___boxed(lean_object* v_query_2509_, lean_object* v_key_2510_){
_start:
{
uint8_t v_res_2511_; lean_object* v_r_2512_; 
v_res_2511_ = l_Std_Http_URI_Query_containsEncoded(v_query_2509_, v_key_2510_);
lean_dec_ref(v_key_2510_);
lean_dec_ref(v_query_2509_);
v_r_2512_ = lean_box(v_res_2511_);
return v_r_2512_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_contains_spec__0(lean_object* v_key_2513_, lean_object* v_as_2514_, size_t v_i_2515_, size_t v_stop_2516_){
_start:
{
uint8_t v___x_2517_; 
v___x_2517_ = lean_usize_dec_eq(v_i_2515_, v_stop_2516_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; lean_object* v_fst_2519_; uint8_t v___x_2520_; 
v___x_2518_ = lean_array_uget_borrowed(v_as_2514_, v_i_2515_);
v_fst_2519_ = lean_ctor_get(v___x_2518_, 0);
v___x_2520_ = l_Std_Http_URI_EncodedQueryString_decodesTo___redArg(v_fst_2519_, v_key_2513_);
if (v___x_2520_ == 0)
{
size_t v___x_2521_; size_t v___x_2522_; 
v___x_2521_ = ((size_t)1ULL);
v___x_2522_ = lean_usize_add(v_i_2515_, v___x_2521_);
v_i_2515_ = v___x_2522_;
goto _start;
}
else
{
return v___x_2520_;
}
}
else
{
uint8_t v___x_2524_; 
v___x_2524_ = 0;
return v___x_2524_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_contains_spec__0___boxed(lean_object* v_key_2525_, lean_object* v_as_2526_, lean_object* v_i_2527_, lean_object* v_stop_2528_){
_start:
{
size_t v_i_boxed_2529_; size_t v_stop_boxed_2530_; uint8_t v_res_2531_; lean_object* v_r_2532_; 
v_i_boxed_2529_ = lean_unbox_usize(v_i_2527_);
lean_dec(v_i_2527_);
v_stop_boxed_2530_ = lean_unbox_usize(v_stop_2528_);
lean_dec(v_stop_2528_);
v_res_2531_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_contains_spec__0(v_key_2525_, v_as_2526_, v_i_boxed_2529_, v_stop_boxed_2530_);
lean_dec_ref(v_as_2526_);
lean_dec_ref(v_key_2525_);
v_r_2532_ = lean_box(v_res_2531_);
return v_r_2532_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_contains(lean_object* v_query_2533_, lean_object* v_key_2534_){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2535_ = lean_unsigned_to_nat(0u);
v___x_2536_ = lean_array_get_size(v_query_2533_);
v___x_2537_ = lean_nat_dec_lt(v___x_2535_, v___x_2536_);
if (v___x_2537_ == 0)
{
return v___x_2537_;
}
else
{
if (v___x_2537_ == 0)
{
return v___x_2537_;
}
else
{
size_t v___x_2538_; size_t v___x_2539_; uint8_t v___x_2540_; 
v___x_2538_ = ((size_t)0ULL);
v___x_2539_ = lean_usize_of_nat(v___x_2536_);
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_contains_spec__0(v_key_2534_, v_query_2533_, v___x_2538_, v___x_2539_);
return v___x_2540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_contains___boxed(lean_object* v_query_2541_, lean_object* v_key_2542_){
_start:
{
uint8_t v_res_2543_; lean_object* v_r_2544_; 
v_res_2543_ = l_Std_Http_URI_Query_contains(v_query_2541_, v_key_2542_);
lean_dec_ref(v_key_2542_);
lean_dec_ref(v_query_2541_);
v_r_2544_ = lean_box(v_res_2543_);
return v_r_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(lean_object* v_key_2545_, lean_object* v_as_2546_, size_t v_i_2547_, size_t v_stop_2548_, lean_object* v_b_2549_){
_start:
{
lean_object* v___y_2551_; uint8_t v___x_2555_; 
v___x_2555_ = lean_usize_dec_eq(v_i_2547_, v_stop_2548_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; lean_object* v_fst_2557_; uint8_t v___x_2558_; 
v___x_2556_ = lean_array_uget_borrowed(v_as_2546_, v_i_2547_);
v_fst_2557_ = lean_ctor_get(v___x_2556_, 0);
v___x_2558_ = lean_sarray_dec_eq(v_fst_2557_, v_key_2545_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; 
lean_inc(v___x_2556_);
v___x_2559_ = lean_array_push(v_b_2549_, v___x_2556_);
v___y_2551_ = v___x_2559_;
goto v___jp_2550_;
}
else
{
v___y_2551_ = v_b_2549_;
goto v___jp_2550_;
}
}
else
{
return v_b_2549_;
}
v___jp_2550_:
{
size_t v___x_2552_; size_t v___x_2553_; 
v___x_2552_ = ((size_t)1ULL);
v___x_2553_ = lean_usize_add(v_i_2547_, v___x_2552_);
v_i_2547_ = v___x_2553_;
v_b_2549_ = v___y_2551_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(lean_object* v_key_2560_, lean_object* v_as_2561_, lean_object* v_i_2562_, lean_object* v_stop_2563_, lean_object* v_b_2564_){
_start:
{
size_t v_i_boxed_2565_; size_t v_stop_boxed_2566_; lean_object* v_res_2567_; 
v_i_boxed_2565_ = lean_unbox_usize(v_i_2562_);
lean_dec(v_i_2562_);
v_stop_boxed_2566_ = lean_unbox_usize(v_stop_2563_);
lean_dec(v_stop_2563_);
v_res_2567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2560_, v_as_2561_, v_i_boxed_2565_, v_stop_boxed_2566_, v_b_2564_);
lean_dec_ref(v_as_2561_);
lean_dec_ref(v_key_2560_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded(lean_object* v_query_2568_, lean_object* v_key_2569_){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2570_ = lean_unsigned_to_nat(0u);
v___x_2571_ = lean_array_get_size(v_query_2568_);
v___x_2572_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_2573_ = lean_nat_dec_lt(v___x_2570_, v___x_2571_);
if (v___x_2573_ == 0)
{
return v___x_2572_;
}
else
{
size_t v___x_2574_; size_t v___x_2575_; lean_object* v___x_2576_; 
v___x_2574_ = ((size_t)0ULL);
v___x_2575_ = lean_usize_of_nat(v___x_2571_);
v___x_2576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2569_, v_query_2568_, v___x_2574_, v___x_2575_, v___x_2572_);
return v___x_2576_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded___boxed(lean_object* v_query_2577_, lean_object* v_key_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Std_Http_URI_Query_eraseEncoded(v_query_2577_, v_key_2578_);
lean_dec_ref(v_key_2578_);
lean_dec_ref(v_query_2577_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_erase_spec__0(lean_object* v_key_2580_, lean_object* v_as_2581_, size_t v_i_2582_, size_t v_stop_2583_, lean_object* v_b_2584_){
_start:
{
lean_object* v___y_2586_; uint8_t v___x_2590_; 
v___x_2590_ = lean_usize_dec_eq(v_i_2582_, v_stop_2583_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; lean_object* v_fst_2592_; uint8_t v___x_2593_; 
v___x_2591_ = lean_array_uget_borrowed(v_as_2581_, v_i_2582_);
v_fst_2592_ = lean_ctor_get(v___x_2591_, 0);
v___x_2593_ = l_Std_Http_URI_EncodedQueryString_decodesTo___redArg(v_fst_2592_, v_key_2580_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; 
lean_inc(v___x_2591_);
v___x_2594_ = lean_array_push(v_b_2584_, v___x_2591_);
v___y_2586_ = v___x_2594_;
goto v___jp_2585_;
}
else
{
v___y_2586_ = v_b_2584_;
goto v___jp_2585_;
}
}
else
{
return v_b_2584_;
}
v___jp_2585_:
{
size_t v___x_2587_; size_t v___x_2588_; 
v___x_2587_ = ((size_t)1ULL);
v___x_2588_ = lean_usize_add(v_i_2582_, v___x_2587_);
v_i_2582_ = v___x_2588_;
v_b_2584_ = v___y_2586_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_erase_spec__0___boxed(lean_object* v_key_2595_, lean_object* v_as_2596_, lean_object* v_i_2597_, lean_object* v_stop_2598_, lean_object* v_b_2599_){
_start:
{
size_t v_i_boxed_2600_; size_t v_stop_boxed_2601_; lean_object* v_res_2602_; 
v_i_boxed_2600_ = lean_unbox_usize(v_i_2597_);
lean_dec(v_i_2597_);
v_stop_boxed_2601_ = lean_unbox_usize(v_stop_2598_);
lean_dec(v_stop_2598_);
v_res_2602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_erase_spec__0(v_key_2595_, v_as_2596_, v_i_boxed_2600_, v_stop_boxed_2601_, v_b_2599_);
lean_dec_ref(v_as_2596_);
lean_dec_ref(v_key_2595_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase(lean_object* v_query_2603_, lean_object* v_key_2604_){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; 
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = lean_array_get_size(v_query_2603_);
v___x_2607_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_2608_ = lean_nat_dec_lt(v___x_2605_, v___x_2606_);
if (v___x_2608_ == 0)
{
return v___x_2607_;
}
else
{
size_t v___x_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = ((size_t)0ULL);
v___x_2610_ = lean_usize_of_nat(v___x_2606_);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_erase_spec__0(v_key_2604_, v_query_2603_, v___x_2609_, v___x_2610_, v___x_2607_);
return v___x_2611_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase___boxed(lean_object* v_query_2612_, lean_object* v_key_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Std_Http_URI_Query_erase(v_query_2612_, v_key_2613_);
lean_dec_ref(v_key_2613_);
lean_dec_ref(v_query_2612_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get(lean_object* v_query_2617_, lean_object* v_key_2618_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Std_Http_URI_Query_find_x3f(v_query_2617_, v_key_2618_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v___x_2620_; 
v___x_2620_ = lean_box(0);
return v___x_2620_;
}
else
{
lean_object* v_val_2621_; 
v_val_2621_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_val_2621_);
lean_dec_ref_known(v___x_2619_, 1);
if (lean_obj_tag(v_val_2621_) == 0)
{
lean_object* v___x_2622_; 
v___x_2622_ = ((lean_object*)(l_Std_Http_URI_Query_get___closed__0));
return v___x_2622_;
}
else
{
lean_object* v_val_2623_; lean_object* v___x_2624_; 
v_val_2623_ = lean_ctor_get(v_val_2621_, 0);
lean_inc(v_val_2623_);
lean_dec_ref_known(v_val_2621_, 1);
v___x_2624_ = l_Std_Http_URI_EncodedQueryParam_decode(v_val_2623_);
lean_dec(v_val_2623_);
return v___x_2624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get___boxed(lean_object* v_query_2625_, lean_object* v_key_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Std_Http_URI_Query_get(v_query_2625_, v_key_2626_);
lean_dec_ref(v_key_2626_);
lean_dec_ref(v_query_2625_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD(lean_object* v_query_2628_, lean_object* v_key_2629_, lean_object* v_default_2630_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Std_Http_URI_Query_get(v_query_2628_, v_key_2629_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_inc_ref(v_default_2630_);
return v_default_2630_;
}
else
{
lean_object* v_val_2632_; 
v_val_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_val_2632_);
lean_dec_ref_known(v___x_2631_, 1);
return v_val_2632_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD___boxed(lean_object* v_query_2633_, lean_object* v_key_2634_, lean_object* v_default_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_Std_Http_URI_Query_getD(v_query_2633_, v_key_2634_, v_default_2635_);
lean_dec_ref(v_default_2635_);
lean_dec_ref(v_key_2634_);
lean_dec_ref(v_query_2633_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set(lean_object* v_query_2637_, lean_object* v_key_2638_, lean_object* v_value_2639_){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = l_Std_Http_URI_Query_erase(v_query_2637_, v_key_2638_);
v___x_2641_ = l_Std_Http_URI_Query_insert(v___x_2640_, v_key_2638_, v_value_2639_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set___boxed(lean_object* v_query_2642_, lean_object* v_key_2643_, lean_object* v_value_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Std_Http_URI_Query_set(v_query_2642_, v_key_2643_, v_value_2644_);
lean_dec_ref(v_query_2642_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(size_t v_sz_2646_, size_t v_i_2647_, lean_object* v_bs_2648_){
_start:
{
uint8_t v___x_2649_; 
v___x_2649_ = lean_usize_dec_lt(v_i_2647_, v_sz_2646_);
if (v___x_2649_ == 0)
{
return v_bs_2648_;
}
else
{
lean_object* v_v_2650_; lean_object* v_fst_2651_; lean_object* v_snd_2652_; lean_object* v___x_2653_; lean_object* v_bs_x27_2654_; lean_object* v___x_2655_; size_t v___x_2656_; size_t v___x_2657_; lean_object* v___x_2658_; 
v_v_2650_ = lean_array_uget_borrowed(v_bs_2648_, v_i_2647_);
v_fst_2651_ = lean_ctor_get(v_v_2650_, 0);
lean_inc(v_fst_2651_);
v_snd_2652_ = lean_ctor_get(v_v_2650_, 1);
lean_inc(v_snd_2652_);
v___x_2653_ = lean_unsigned_to_nat(0u);
v_bs_x27_2654_ = lean_array_uset(v_bs_2648_, v_i_2647_, v___x_2653_);
v___x_2655_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2651_, v_snd_2652_);
v___x_2656_ = ((size_t)1ULL);
v___x_2657_ = lean_usize_add(v_i_2647_, v___x_2656_);
v___x_2658_ = lean_array_uset(v_bs_x27_2654_, v_i_2647_, v___x_2655_);
v_i_2647_ = v___x_2657_;
v_bs_2648_ = v___x_2658_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0___boxed(lean_object* v_sz_2660_, lean_object* v_i_2661_, lean_object* v_bs_2662_){
_start:
{
size_t v_sz_boxed_2663_; size_t v_i_boxed_2664_; lean_object* v_res_2665_; 
v_sz_boxed_2663_ = lean_unbox_usize(v_sz_2660_);
lean_dec(v_sz_2660_);
v_i_boxed_2664_ = lean_unbox_usize(v_i_2661_);
lean_dec(v_i_2661_);
v_res_2665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_boxed_2663_, v_i_boxed_2664_, v_bs_2662_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toRawString(lean_object* v_query_2667_){
_start:
{
size_t v_sz_2668_; size_t v___x_2669_; lean_object* v_params_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v_sz_2668_ = lean_array_size(v_query_2667_);
v___x_2669_ = ((size_t)0ULL);
v_params_2670_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_2668_, v___x_2669_, v_query_2667_);
v___x_2671_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2672_ = lean_array_to_list(v_params_2670_);
v___x_2673_ = l_String_intercalate(v___x_2671_, v___x_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0(lean_object* v_x_2675_){
_start:
{
lean_object* v_fst_2676_; lean_object* v_snd_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v_fst_2676_ = lean_ctor_get(v_x_2675_, 0);
lean_inc(v_fst_2676_);
v_snd_2677_ = lean_ctor_get(v_x_2675_, 1);
lean_inc(v_snd_2677_);
lean_dec_ref(v_x_2675_);
v___x_2678_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
v___x_2679_ = l_Std_Http_URI_Query_insert(v___x_2678_, v_fst_2676_, v_snd_2677_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0(lean_object* v_x_2682_, lean_object* v_q_2683_){
_start:
{
lean_object* v_fst_2684_; lean_object* v_snd_2685_; lean_object* v___x_2686_; 
v_fst_2684_ = lean_ctor_get(v_x_2682_, 0);
lean_inc(v_fst_2684_);
v_snd_2685_ = lean_ctor_get(v_x_2682_, 1);
lean_inc(v_snd_2685_);
lean_dec_ref(v_x_2682_);
v___x_2686_ = l_Std_Http_URI_Query_insert(v_q_2683_, v_fst_2684_, v_snd_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__0(lean_object* v_x_2689_){
_start:
{
lean_object* v_fst_2690_; lean_object* v_snd_2691_; lean_object* v___x_2692_; 
v_fst_2690_ = lean_ctor_get(v_x_2689_, 0);
lean_inc(v_fst_2690_);
v_snd_2691_ = lean_ctor_get(v_x_2689_, 1);
lean_inc(v_snd_2691_);
lean_dec_ref(v_x_2689_);
v___x_2692_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2690_, v_snd_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__1(lean_object* v___f_2694_, lean_object* v_q_2695_){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; 
v___x_2696_ = lean_array_get_size(v_q_2695_);
v___x_2697_ = lean_unsigned_to_nat(0u);
v___x_2698_ = lean_nat_dec_eq(v___x_2696_, v___x_2697_);
if (v___x_2698_ == 0)
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v_encodedParams_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2699_ = lean_array_to_list(v_q_2695_);
v___x_2700_ = lean_box(0);
v_encodedParams_2701_ = l_List_mapTR_loop___redArg(v___f_2694_, v___x_2699_, v___x_2700_);
v___x_2702_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2703_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2704_ = l_String_intercalate(v___x_2703_, v_encodedParams_2701_);
v___x_2705_ = lean_string_append(v___x_2702_, v___x_2704_);
lean_dec_ref(v___x_2704_);
return v___x_2705_;
}
else
{
lean_object* v___x_2706_; 
lean_dec_ref(v_q_2695_);
lean_dec_ref(v___f_2694_);
v___x_2706_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2706_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
if (lean_obj_tag(v_a_2711_) == 0)
{
lean_object* v___x_2713_; 
v___x_2713_ = l_List_reverse___redArg(v_a_2712_);
return v___x_2713_;
}
else
{
lean_object* v_head_2714_; lean_object* v_tail_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2726_; 
v_head_2714_ = lean_ctor_get(v_a_2711_, 0);
v_tail_2715_ = lean_ctor_get(v_a_2711_, 1);
v_isSharedCheck_2726_ = !lean_is_exclusive(v_a_2711_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2717_ = v_a_2711_;
v_isShared_2718_ = v_isSharedCheck_2726_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_tail_2715_);
lean_inc(v_head_2714_);
lean_dec(v_a_2711_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2726_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v_fst_2719_; lean_object* v_snd_2720_; lean_object* v___x_2721_; lean_object* v___x_2723_; 
v_fst_2719_ = lean_ctor_get(v_head_2714_, 0);
lean_inc(v_fst_2719_);
v_snd_2720_ = lean_ctor_get(v_head_2714_, 1);
lean_inc(v_snd_2720_);
lean_dec(v_head_2714_);
v___x_2721_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2719_, v_snd_2720_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 1, v_a_2712_);
lean_ctor_set(v___x_2717_, 0, v___x_2721_);
v___x_2723_ = v___x_2717_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2721_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_a_2712_);
v___x_2723_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
v_a_2711_ = v_tail_2715_;
v_a_2712_ = v___x_2723_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatOption(lean_object* v_x_2727_){
_start:
{
if (lean_obj_tag(v_x_2727_) == 0)
{
lean_object* v___x_2728_; 
v___x_2728_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2728_;
}
else
{
lean_object* v_val_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; 
v_val_2729_ = lean_ctor_get(v_x_2727_, 0);
lean_inc(v_val_2729_);
lean_dec_ref_known(v_x_2727_, 1);
v___x_2730_ = lean_array_get_size(v_val_2729_);
v___x_2731_ = lean_unsigned_to_nat(0u);
v___x_2732_ = lean_nat_dec_eq(v___x_2730_, v___x_2731_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v_encodedParams_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2733_ = lean_array_to_list(v_val_2729_);
v___x_2734_ = lean_box(0);
v_encodedParams_2735_ = l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(v___x_2733_, v___x_2734_);
v___x_2736_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2737_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2738_ = l_String_intercalate(v___x_2737_, v_encodedParams_2735_);
v___x_2739_ = lean_string_append(v___x_2736_, v___x_2738_);
lean_dec_ref(v___x_2738_);
return v___x_2739_;
}
else
{
lean_object* v___x_2740_; 
lean_dec(v_val_2729_);
v___x_2740_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
return v___x_2740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(lean_object* v_x_2741_, lean_object* v_x_2742_){
_start:
{
if (lean_obj_tag(v_x_2741_) == 0)
{
lean_object* v___x_2743_; 
v___x_2743_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2743_;
}
else
{
lean_object* v_val_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v_val_2744_ = lean_ctor_get(v_x_2741_, 0);
lean_inc(v_val_2744_);
lean_dec_ref_known(v_x_2741_, 1);
v___x_2745_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2746_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_val_2744_);
v___x_2747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = l_Repr_addAppParen(v___x_2747_, v_x_2742_);
return v___x_2748_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(lean_object* v_x_2749_, lean_object* v_x_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_x_2749_, v_x_2750_);
lean_dec(v_x_2750_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object* v_x_2752_, lean_object* v_x_2753_){
_start:
{
if (lean_obj_tag(v_x_2752_) == 0)
{
lean_object* v___x_2754_; 
v___x_2754_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2754_;
}
else
{
lean_object* v_val_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_val_2755_ = lean_ctor_get(v_x_2752_, 0);
lean_inc(v_val_2755_);
lean_dec_ref_known(v_x_2752_, 1);
v___x_2756_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2757_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_val_2755_);
v___x_2758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = l_Repr_addAppParen(v___x_2758_, v_x_2753_);
return v___x_2759_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1___boxed(lean_object* v_x_2760_, lean_object* v_x_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_x_2760_, v_x_2761_);
lean_dec(v_x_2761_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(lean_object* v_x_2763_, lean_object* v_x_2764_){
_start:
{
if (lean_obj_tag(v_x_2763_) == 0)
{
lean_object* v___x_2765_; 
v___x_2765_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2765_;
}
else
{
lean_object* v_val_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2777_; 
v_val_2766_ = lean_ctor_get(v_x_2763_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_x_2763_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2768_ = v_x_2763_;
v_isShared_2769_ = v_isSharedCheck_2777_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_val_2766_);
lean_dec(v_x_2763_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2777_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2773_; 
v___x_2770_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2771_ = l_String_quote(v_val_2766_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set_tag(v___x_2768_, 3);
lean_ctor_set(v___x_2768_, 0, v___x_2771_);
v___x_2773_ = v___x_2768_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2771_);
v___x_2773_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2770_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
v___x_2775_ = l_Repr_addAppParen(v___x_2774_, v_x_2764_);
return v___x_2775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2___boxed(lean_object* v_x_2778_, lean_object* v_x_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_x_2778_, v_x_2779_);
lean_dec(v_x_2779_);
return v_res_2780_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_unsigned_to_nat(10u);
v___x_2791_ = lean_nat_to_int(v___x_2790_);
return v___x_2791_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = lean_unsigned_to_nat(13u);
v___x_2796_ = lean_nat_to_int(v___x_2795_);
return v___x_2796_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_unsigned_to_nat(9u);
v___x_2804_ = lean_nat_to_int(v___x_2803_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___redArg(lean_object* v_x_2808_){
_start:
{
lean_object* v_scheme_2809_; lean_object* v_authority_2810_; lean_object* v_path_2811_; lean_object* v_query_2812_; lean_object* v_fragment_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; uint8_t v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v_scheme_2809_ = lean_ctor_get(v_x_2808_, 0);
lean_inc_ref(v_scheme_2809_);
v_authority_2810_ = lean_ctor_get(v_x_2808_, 1);
lean_inc(v_authority_2810_);
v_path_2811_ = lean_ctor_get(v_x_2808_, 2);
lean_inc_ref(v_path_2811_);
v_query_2812_ = lean_ctor_get(v_x_2808_, 3);
lean_inc(v_query_2812_);
v_fragment_2813_ = lean_ctor_get(v_x_2808_, 4);
lean_inc(v_fragment_2813_);
lean_dec_ref(v_x_2808_);
v___x_2814_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2815_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2816_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2817_ = l_String_quote(v_scheme_2809_);
v___x_2818_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
v___x_2819_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2816_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
v___x_2820_ = 0;
v___x_2821_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2821_, 0, v___x_2819_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*1, v___x_2820_);
v___x_2822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2815_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2824_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2822_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = lean_box(1);
v___x_2826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__6));
v___x_2828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
v___x_2829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
lean_ctor_set(v___x_2829_, 1, v___x_2814_);
v___x_2830_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_2831_ = lean_unsigned_to_nat(0u);
v___x_2832_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_2810_, v___x_2831_);
v___x_2833_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2830_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
lean_ctor_set_uint8(v___x_2834_, sizeof(void*)*1, v___x_2820_);
v___x_2835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2829_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2835_);
lean_ctor_set(v___x_2836_, 1, v___x_2823_);
v___x_2837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
lean_ctor_set(v___x_2837_, 1, v___x_2825_);
v___x_2838_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_2839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2837_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
lean_ctor_set(v___x_2840_, 1, v___x_2814_);
v___x_2841_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2842_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_2811_);
v___x_2843_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2841_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
v___x_2844_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
lean_ctor_set_uint8(v___x_2844_, sizeof(void*)*1, v___x_2820_);
v___x_2845_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2840_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
v___x_2846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
lean_ctor_set(v___x_2846_, 1, v___x_2823_);
v___x_2847_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
lean_ctor_set(v___x_2847_, 1, v___x_2825_);
v___x_2848_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_2849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
lean_ctor_set(v___x_2850_, 1, v___x_2814_);
v___x_2851_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_2852_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_2812_, v___x_2831_);
v___x_2853_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2851_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
v___x_2854_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
lean_ctor_set_uint8(v___x_2854_, sizeof(void*)*1, v___x_2820_);
v___x_2855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2850_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_2856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
lean_ctor_set(v___x_2856_, 1, v___x_2823_);
v___x_2857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
lean_ctor_set(v___x_2857_, 1, v___x_2825_);
v___x_2858_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_2859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2857_);
lean_ctor_set(v___x_2859_, 1, v___x_2858_);
v___x_2860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
lean_ctor_set(v___x_2860_, 1, v___x_2814_);
v___x_2861_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_2862_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_2813_, v___x_2831_);
v___x_2863_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2861_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*1, v___x_2820_);
v___x_2865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2860_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2867_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
lean_ctor_set(v___x_2868_, 1, v___x_2865_);
v___x_2869_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2868_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
v___x_2871_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2866_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
v___x_2872_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*1, v___x_2820_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr(lean_object* v_x_2873_, lean_object* v_prec_2874_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Std_Http_instReprURI_repr___redArg(v_x_2873_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___boxed(lean_object* v_x_2876_, lean_object* v_prec_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Std_Http_instReprURI_repr(v_x_2876_, v_prec_2877_);
lean_dec(v_prec_2877_);
return v_res_2878_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object* v_x_2887_, lean_object* v_x_2888_){
_start:
{
if (lean_obj_tag(v_x_2887_) == 0)
{
if (lean_obj_tag(v_x_2888_) == 0)
{
uint8_t v___x_2889_; 
v___x_2889_ = 1;
return v___x_2889_;
}
else
{
uint8_t v___x_2890_; 
v___x_2890_ = 0;
return v___x_2890_;
}
}
else
{
if (lean_obj_tag(v_x_2888_) == 0)
{
uint8_t v___x_2891_; 
v___x_2891_ = 0;
return v___x_2891_;
}
else
{
lean_object* v_val_2892_; lean_object* v_val_2893_; uint8_t v___x_2894_; 
v_val_2892_ = lean_ctor_get(v_x_2887_, 0);
v_val_2893_ = lean_ctor_get(v_x_2888_, 0);
v___x_2894_ = l_Std_Http_URI_instBEqAuthority_beq(v_val_2892_, v_val_2893_);
return v___x_2894_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object* v_x_2895_, lean_object* v_x_2896_){
_start:
{
uint8_t v_res_2897_; lean_object* v_r_2898_; 
v_res_2897_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_x_2895_, v_x_2896_);
lean_dec(v_x_2896_);
lean_dec(v_x_2895_);
v_r_2898_ = lean_box(v_res_2897_);
return v_r_2898_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object* v_x_2899_, lean_object* v_x_2900_){
_start:
{
if (lean_obj_tag(v_x_2899_) == 0)
{
if (lean_obj_tag(v_x_2900_) == 0)
{
uint8_t v___x_2901_; 
v___x_2901_ = 1;
return v___x_2901_;
}
else
{
uint8_t v___x_2902_; 
v___x_2902_ = 0;
return v___x_2902_;
}
}
else
{
if (lean_obj_tag(v_x_2900_) == 0)
{
uint8_t v___x_2903_; 
v___x_2903_ = 0;
return v___x_2903_;
}
else
{
lean_object* v_val_2904_; lean_object* v_val_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; 
v_val_2904_ = lean_ctor_get(v_x_2899_, 0);
v_val_2905_ = lean_ctor_get(v_x_2900_, 0);
v___x_2906_ = lean_array_get_size(v_val_2904_);
v___x_2907_ = lean_array_get_size(v_val_2905_);
v___x_2908_ = lean_nat_dec_eq(v___x_2906_, v___x_2907_);
if (v___x_2908_ == 0)
{
return v___x_2908_;
}
else
{
uint8_t v___x_2909_; 
v___x_2909_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_val_2904_, v_val_2905_, v___x_2906_);
return v___x_2909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object* v_x_2910_, lean_object* v_x_2911_){
_start:
{
uint8_t v_res_2912_; lean_object* v_r_2913_; 
v_res_2912_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_x_2910_, v_x_2911_);
lean_dec(v_x_2911_);
lean_dec(v_x_2910_);
v_r_2913_ = lean_box(v_res_2912_);
return v_r_2913_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(lean_object* v_x_2914_, lean_object* v_x_2915_){
_start:
{
if (lean_obj_tag(v_x_2914_) == 0)
{
if (lean_obj_tag(v_x_2915_) == 0)
{
uint8_t v___x_2916_; 
v___x_2916_ = 1;
return v___x_2916_;
}
else
{
uint8_t v___x_2917_; 
v___x_2917_ = 0;
return v___x_2917_;
}
}
else
{
if (lean_obj_tag(v_x_2915_) == 0)
{
uint8_t v___x_2918_; 
v___x_2918_ = 0;
return v___x_2918_;
}
else
{
lean_object* v_val_2919_; lean_object* v_val_2920_; uint8_t v___x_2921_; 
v_val_2919_ = lean_ctor_get(v_x_2914_, 0);
v_val_2920_ = lean_ctor_get(v_x_2915_, 0);
v___x_2921_ = lean_string_dec_eq(v_val_2919_, v_val_2920_);
return v___x_2921_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2___boxed(lean_object* v_x_2922_, lean_object* v_x_2923_){
_start:
{
uint8_t v_res_2924_; lean_object* v_r_2925_; 
v_res_2924_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_x_2922_, v_x_2923_);
lean_dec(v_x_2923_);
lean_dec(v_x_2922_);
v_r_2925_ = lean_box(v_res_2924_);
return v_r_2925_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object* v_x_2926_, lean_object* v_x_2927_){
_start:
{
lean_object* v_scheme_2928_; lean_object* v_authority_2929_; lean_object* v_path_2930_; lean_object* v_query_2931_; lean_object* v_fragment_2932_; lean_object* v_scheme_2933_; lean_object* v_authority_2934_; lean_object* v_path_2935_; lean_object* v_query_2936_; lean_object* v_fragment_2937_; uint8_t v___x_2938_; 
v_scheme_2928_ = lean_ctor_get(v_x_2926_, 0);
v_authority_2929_ = lean_ctor_get(v_x_2926_, 1);
v_path_2930_ = lean_ctor_get(v_x_2926_, 2);
v_query_2931_ = lean_ctor_get(v_x_2926_, 3);
v_fragment_2932_ = lean_ctor_get(v_x_2926_, 4);
v_scheme_2933_ = lean_ctor_get(v_x_2927_, 0);
v_authority_2934_ = lean_ctor_get(v_x_2927_, 1);
v_path_2935_ = lean_ctor_get(v_x_2927_, 2);
v_query_2936_ = lean_ctor_get(v_x_2927_, 3);
v_fragment_2937_ = lean_ctor_get(v_x_2927_, 4);
v___x_2938_ = lean_string_dec_eq(v_scheme_2928_, v_scheme_2933_);
if (v___x_2938_ == 0)
{
return v___x_2938_;
}
else
{
uint8_t v___x_2939_; 
v___x_2939_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_2929_, v_authority_2934_);
if (v___x_2939_ == 0)
{
return v___x_2939_;
}
else
{
uint8_t v___x_2940_; 
v___x_2940_ = l_Std_Http_URI_instBEqPath_beq(v_path_2930_, v_path_2935_);
if (v___x_2940_ == 0)
{
return v___x_2940_;
}
else
{
uint8_t v___x_2941_; 
v___x_2941_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_2931_, v_query_2936_);
if (v___x_2941_ == 0)
{
return v___x_2941_;
}
else
{
uint8_t v___x_2942_; 
v___x_2942_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_2932_, v_fragment_2937_);
return v___x_2942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object* v_x_2943_, lean_object* v_x_2944_){
_start:
{
uint8_t v_res_2945_; lean_object* v_r_2946_; 
v_res_2945_ = l_Std_Http_instBEqURI_beq(v_x_2943_, v_x_2944_);
lean_dec_ref(v_x_2944_);
lean_dec_ref(v_x_2943_);
v_r_2946_ = lean_box(v_res_2945_);
return v_r_2946_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__0(lean_object* v_uri_2951_){
_start:
{
lean_object* v_scheme_2952_; lean_object* v_authority_2953_; lean_object* v_path_2954_; lean_object* v_query_2955_; lean_object* v_fragment_2956_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2969_; uint8_t v___y_2970_; lean_object* v___y_2981_; 
v_scheme_2952_ = lean_ctor_get(v_uri_2951_, 0);
lean_inc_ref(v_scheme_2952_);
v_authority_2953_ = lean_ctor_get(v_uri_2951_, 1);
lean_inc(v_authority_2953_);
v_path_2954_ = lean_ctor_get(v_uri_2951_, 2);
lean_inc_ref(v_path_2954_);
v_query_2955_ = lean_ctor_get(v_uri_2951_, 3);
lean_inc(v_query_2955_);
v_fragment_2956_ = lean_ctor_get(v_uri_2951_, 4);
lean_inc(v_fragment_2956_);
lean_dec_ref(v_uri_2951_);
if (lean_obj_tag(v_authority_2953_) == 0)
{
lean_object* v___x_2984_; 
v___x_2984_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2981_ = v___x_2984_;
goto v___jp_2980_;
}
else
{
lean_object* v_val_2985_; lean_object* v_userInfo_2986_; lean_object* v_host_2987_; lean_object* v_port_2988_; lean_object* v___x_2989_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3008_; 
v_val_2985_ = lean_ctor_get(v_authority_2953_, 0);
v_userInfo_2986_ = lean_ctor_get(v_val_2985_, 0);
v_host_2987_ = lean_ctor_get(v_val_2985_, 1);
v_port_2988_ = lean_ctor_get(v_val_2985_, 2);
v___x_2989_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__1));
if (lean_obj_tag(v_userInfo_2986_) == 0)
{
lean_object* v___x_3018_; 
v___x_3018_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3008_ = v___x_3018_;
goto v___jp_3007_;
}
else
{
lean_object* v_val_3019_; lean_object* v_password_3020_; 
v_val_3019_ = lean_ctor_get(v_userInfo_2986_, 0);
v_password_3020_ = lean_ctor_get(v_val_3019_, 1);
if (lean_obj_tag(v_password_3020_) == 0)
{
lean_object* v_username_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_username_3021_ = lean_ctor_get(v_val_3019_, 0);
lean_inc_ref(v_username_3021_);
v___x_3022_ = lean_string_from_utf8_unchecked(v_username_3021_);
v___x_3023_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3024_ = lean_string_append(v___x_3022_, v___x_3023_);
v___y_3008_ = v___x_3024_;
goto v___jp_3007_;
}
else
{
lean_object* v_username_3025_; lean_object* v_val_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v_username_3025_ = lean_ctor_get(v_val_3019_, 0);
v_val_3026_ = lean_ctor_get(v_password_3020_, 0);
lean_inc_ref(v_username_3025_);
v___x_3027_ = lean_string_from_utf8_unchecked(v_username_3025_);
v___x_3028_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3029_ = lean_string_append(v___x_3027_, v___x_3028_);
lean_inc(v_val_3026_);
v___x_3030_ = lean_string_from_utf8_unchecked(v_val_3026_);
v___x_3031_ = lean_string_append(v___x_3029_, v___x_3030_);
lean_dec_ref(v___x_3030_);
v___x_3032_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3033_ = lean_string_append(v___x_3031_, v___x_3032_);
v___y_3008_ = v___x_3033_;
goto v___jp_3007_;
}
}
v___jp_2990_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2994_ = lean_string_append(v___y_2991_, v___y_2992_);
lean_dec_ref(v___y_2992_);
v___x_2995_ = lean_string_append(v___x_2994_, v___y_2993_);
lean_dec_ref(v___y_2993_);
v___x_2996_ = lean_string_append(v___x_2989_, v___x_2995_);
lean_dec_ref(v___x_2995_);
v___y_2981_ = v___x_2996_;
goto v___jp_2980_;
}
v___jp_2997_:
{
switch(lean_obj_tag(v_port_2988_))
{
case 0:
{
lean_object* v___x_3000_; 
v___x_3000_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2991_ = v___y_2998_;
v___y_2992_ = v___y_2999_;
v___y_2993_ = v___x_3000_;
goto v___jp_2990_;
}
case 1:
{
lean_object* v___x_3001_; 
v___x_3001_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_2991_ = v___y_2998_;
v___y_2992_ = v___y_2999_;
v___y_2993_ = v___x_3001_;
goto v___jp_2990_;
}
default: 
{
uint16_t v_port_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_port_3002_ = lean_ctor_get_uint16(v_port_2988_, 0);
v___x_3003_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3004_ = lean_uint16_to_nat(v_port_3002_);
v___x_3005_ = l_Nat_reprFast(v___x_3004_);
v___x_3006_ = lean_string_append(v___x_3003_, v___x_3005_);
lean_dec_ref(v___x_3005_);
v___y_2991_ = v___y_2998_;
v___y_2992_ = v___y_2999_;
v___y_2993_ = v___x_3006_;
goto v___jp_2990_;
}
}
}
v___jp_3007_:
{
switch(lean_obj_tag(v_host_2987_))
{
case 0:
{
lean_object* v_name_3009_; 
v_name_3009_ = lean_ctor_get(v_host_2987_, 0);
lean_inc_ref(v_name_3009_);
v___y_2998_ = v___y_3008_;
v___y_2999_ = v_name_3009_;
goto v___jp_2997_;
}
case 1:
{
lean_object* v_ipv4_3010_; lean_object* v___x_3011_; 
v_ipv4_3010_ = lean_ctor_get(v_host_2987_, 0);
v___x_3011_ = lean_uv_ntop_v4(v_ipv4_3010_);
v___y_2998_ = v___y_3008_;
v___y_2999_ = v___x_3011_;
goto v___jp_2997_;
}
default: 
{
lean_object* v_ipv6_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v_ipv6_3012_ = lean_ctor_get(v_host_2987_, 0);
v___x_3013_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3014_ = lean_uv_ntop_v6(v_ipv6_3012_);
v___x_3015_ = lean_string_append(v___x_3013_, v___x_3014_);
lean_dec_ref(v___x_3014_);
v___x_3016_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3017_ = lean_string_append(v___x_3015_, v___x_3016_);
v___y_2998_ = v___y_3008_;
v___y_2999_ = v___x_3017_;
goto v___jp_2997_;
}
}
}
}
v___jp_2957_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2962_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2963_ = lean_string_append(v_scheme_2952_, v___x_2962_);
v___x_2964_ = lean_string_append(v___x_2963_, v___y_2959_);
lean_dec_ref(v___y_2959_);
v___x_2965_ = lean_string_append(v___x_2964_, v___y_2960_);
lean_dec_ref(v___y_2960_);
v___x_2966_ = lean_string_append(v___x_2965_, v___y_2958_);
lean_dec_ref(v___y_2958_);
v___x_2967_ = lean_string_append(v___x_2966_, v___y_2961_);
lean_dec_ref(v___y_2961_);
return v___x_2967_;
}
v___jp_2968_:
{
uint8_t v___x_2971_; lean_object* v_pathPart_2972_; lean_object* v_queryPart_2973_; 
v___x_2971_ = 1;
v_pathPart_2972_ = l_Std_Http_URI_Path_render(v_path_2954_, v___y_2970_, v___x_2971_);
v_queryPart_2973_ = l_Std_Http_URI_Query_formatOption(v_query_2955_);
if (lean_obj_tag(v_fragment_2956_) == 0)
{
lean_object* v___x_2974_; 
v___x_2974_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2958_ = v_queryPart_2973_;
v___y_2959_ = v___y_2969_;
v___y_2960_ = v_pathPart_2972_;
v___y_2961_ = v___x_2974_;
goto v___jp_2957_;
}
else
{
lean_object* v_val_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v_val_2975_ = lean_ctor_get(v_fragment_2956_, 0);
lean_inc(v_val_2975_);
lean_dec_ref_known(v_fragment_2956_, 1);
v___x_2976_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__0));
v___x_2977_ = l_Std_Http_URI_EncodedFragment_encode(v_val_2975_);
v___x_2978_ = lean_string_from_utf8_unchecked(v___x_2977_);
v___x_2979_ = lean_string_append(v___x_2976_, v___x_2978_);
lean_dec_ref(v___x_2978_);
v___y_2958_ = v_queryPart_2973_;
v___y_2959_ = v___y_2969_;
v___y_2960_ = v_pathPart_2972_;
v___y_2961_ = v___x_2979_;
goto v___jp_2957_;
}
}
v___jp_2980_:
{
if (lean_obj_tag(v_authority_2953_) == 0)
{
uint8_t v___x_2982_; 
v___x_2982_ = 0;
v___y_2969_ = v___y_2981_;
v___y_2970_ = v___x_2982_;
goto v___jp_2968_;
}
else
{
uint8_t v___x_2983_; 
lean_dec_ref_known(v_authority_2953_, 1);
v___x_2983_ = 1;
v___y_2969_ = v___y_2981_;
v___y_2970_ = v___x_2983_;
goto v___jp_2968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x3f(lean_object* v_b_3045_, lean_object* v_scheme_3046_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Std_Http_URI_Scheme_ofString_x3f(v_scheme_3046_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v___x_3048_; 
lean_dec_ref(v_b_3045_);
v___x_3048_ = lean_box(0);
return v___x_3048_;
}
else
{
lean_object* v_userInfo_3049_; lean_object* v_host_3050_; lean_object* v_port_3051_; lean_object* v_pathSegments_3052_; lean_object* v_query_3053_; lean_object* v_fragment_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3069_; 
v_userInfo_3049_ = lean_ctor_get(v_b_3045_, 1);
v_host_3050_ = lean_ctor_get(v_b_3045_, 2);
v_port_3051_ = lean_ctor_get(v_b_3045_, 3);
v_pathSegments_3052_ = lean_ctor_get(v_b_3045_, 4);
v_query_3053_ = lean_ctor_get(v_b_3045_, 5);
v_fragment_3054_ = lean_ctor_get(v_b_3045_, 6);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_b_3045_);
if (v_isSharedCheck_3069_ == 0)
{
lean_object* v_unused_3070_; 
v_unused_3070_ = lean_ctor_get(v_b_3045_, 0);
lean_dec(v_unused_3070_);
v___x_3056_ = v_b_3045_;
v_isShared_3057_ = v_isSharedCheck_3069_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_fragment_3054_);
lean_inc(v_query_3053_);
lean_inc(v_pathSegments_3052_);
lean_inc(v_port_3051_);
lean_inc(v_host_3050_);
lean_inc(v_userInfo_3049_);
lean_dec(v_b_3045_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3069_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
lean_inc_ref(v___x_3047_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v___x_3047_);
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v_userInfo_3049_);
lean_ctor_set(v_reuseFailAlloc_3068_, 2, v_host_3050_);
lean_ctor_set(v_reuseFailAlloc_3068_, 3, v_port_3051_);
lean_ctor_set(v_reuseFailAlloc_3068_, 4, v_pathSegments_3052_);
lean_ctor_set(v_reuseFailAlloc_3068_, 5, v_query_3053_);
lean_ctor_set(v_reuseFailAlloc_3068_, 6, v_fragment_3054_);
v___x_3059_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3066_ == 0)
{
lean_object* v_unused_3067_; 
v_unused_3067_ = lean_ctor_get(v___x_3047_, 0);
lean_dec(v_unused_3067_);
v___x_3061_ = v___x_3047_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_dec(v___x_3047_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 0, v___x_3059_);
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(lean_object* v_msg_3071_){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = ((lean_object*)(l_Std_Http_URI_instInhabitedBuilder_default));
v___x_3073_ = lean_panic_fn_borrowed(v___x_3072_, v_msg_3071_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x21(lean_object* v_b_3075_, lean_object* v_scheme_3076_){
_start:
{
lean_object* v___x_3077_; 
lean_inc_ref(v_scheme_3076_);
v___x_3077_ = l_Std_Http_URI_Builder_setScheme_x3f(v_b_3075_, v_scheme_3076_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3078_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_3079_ = ((lean_object*)(l_Std_Http_URI_Builder_setScheme_x21___closed__0));
v___x_3080_ = lean_unsigned_to_nat(749u);
v___x_3081_ = lean_unsigned_to_nat(14u);
v___x_3082_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_3083_ = l_String_quote(v_scheme_3076_);
v___x_3084_ = lean_string_append(v___x_3082_, v___x_3083_);
lean_dec_ref(v___x_3083_);
v___x_3085_ = l_mkPanicMessageWithDecl(v___x_3078_, v___x_3079_, v___x_3080_, v___x_3081_, v___x_3084_);
lean_dec_ref(v___x_3084_);
v___x_3086_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_3085_);
return v___x_3086_;
}
else
{
lean_object* v_val_3087_; 
lean_dec_ref(v_scheme_3076_);
v_val_3087_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_val_3087_);
lean_dec_ref_known(v___x_3077_, 1);
return v_val_3087_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Builder_setUserInfo___lam__0(uint8_t v___y_3088_){
_start:
{
uint8_t v___x_3132_; uint8_t v___x_3133_; 
v___x_3132_ = 48;
v___x_3133_ = lean_uint8_dec_le(v___x_3132_, v___y_3088_);
if (v___x_3133_ == 0)
{
goto v___jp_3127_;
}
else
{
uint8_t v___x_3134_; uint8_t v___x_3135_; 
v___x_3134_ = 57;
v___x_3135_ = lean_uint8_dec_le(v___y_3088_, v___x_3134_);
if (v___x_3135_ == 0)
{
goto v___jp_3127_;
}
else
{
return v___x_3135_;
}
}
v___jp_3089_:
{
uint8_t v___x_3090_; uint8_t v___x_3091_; 
v___x_3090_ = 45;
v___x_3091_ = lean_uint8_dec_eq(v___y_3088_, v___x_3090_);
if (v___x_3091_ == 0)
{
uint8_t v___x_3092_; uint8_t v___x_3093_; 
v___x_3092_ = 46;
v___x_3093_ = lean_uint8_dec_eq(v___y_3088_, v___x_3092_);
if (v___x_3093_ == 0)
{
uint8_t v___x_3094_; uint8_t v___x_3095_; 
v___x_3094_ = 95;
v___x_3095_ = lean_uint8_dec_eq(v___y_3088_, v___x_3094_);
if (v___x_3095_ == 0)
{
uint8_t v___x_3096_; uint8_t v___x_3097_; 
v___x_3096_ = 126;
v___x_3097_ = lean_uint8_dec_eq(v___y_3088_, v___x_3096_);
if (v___x_3097_ == 0)
{
uint8_t v___x_3098_; uint8_t v___x_3099_; 
v___x_3098_ = 33;
v___x_3099_ = lean_uint8_dec_eq(v___y_3088_, v___x_3098_);
if (v___x_3099_ == 0)
{
uint8_t v___x_3100_; uint8_t v___x_3101_; 
v___x_3100_ = 36;
v___x_3101_ = lean_uint8_dec_eq(v___y_3088_, v___x_3100_);
if (v___x_3101_ == 0)
{
uint8_t v___x_3102_; uint8_t v___x_3103_; 
v___x_3102_ = 38;
v___x_3103_ = lean_uint8_dec_eq(v___y_3088_, v___x_3102_);
if (v___x_3103_ == 0)
{
uint8_t v___x_3104_; uint8_t v___x_3105_; 
v___x_3104_ = 39;
v___x_3105_ = lean_uint8_dec_eq(v___y_3088_, v___x_3104_);
if (v___x_3105_ == 0)
{
uint8_t v___x_3106_; uint8_t v___x_3107_; 
v___x_3106_ = 40;
v___x_3107_ = lean_uint8_dec_eq(v___y_3088_, v___x_3106_);
if (v___x_3107_ == 0)
{
uint8_t v___x_3108_; uint8_t v___x_3109_; 
v___x_3108_ = 41;
v___x_3109_ = lean_uint8_dec_eq(v___y_3088_, v___x_3108_);
if (v___x_3109_ == 0)
{
uint8_t v___x_3110_; uint8_t v___x_3111_; 
v___x_3110_ = 42;
v___x_3111_ = lean_uint8_dec_eq(v___y_3088_, v___x_3110_);
if (v___x_3111_ == 0)
{
uint8_t v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = 43;
v___x_3113_ = lean_uint8_dec_eq(v___y_3088_, v___x_3112_);
if (v___x_3113_ == 0)
{
uint8_t v___x_3114_; uint8_t v___x_3115_; 
v___x_3114_ = 44;
v___x_3115_ = lean_uint8_dec_eq(v___y_3088_, v___x_3114_);
if (v___x_3115_ == 0)
{
uint8_t v___x_3116_; uint8_t v___x_3117_; 
v___x_3116_ = 59;
v___x_3117_ = lean_uint8_dec_eq(v___y_3088_, v___x_3116_);
if (v___x_3117_ == 0)
{
uint8_t v___x_3118_; uint8_t v___x_3119_; 
v___x_3118_ = 61;
v___x_3119_ = lean_uint8_dec_eq(v___y_3088_, v___x_3118_);
if (v___x_3119_ == 0)
{
uint8_t v___x_3120_; uint8_t v___x_3121_; 
v___x_3120_ = 58;
v___x_3121_ = lean_uint8_dec_eq(v___y_3088_, v___x_3120_);
return v___x_3121_;
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
else
{
return v___x_3109_;
}
}
else
{
return v___x_3107_;
}
}
else
{
return v___x_3105_;
}
}
else
{
return v___x_3103_;
}
}
else
{
return v___x_3101_;
}
}
else
{
return v___x_3099_;
}
}
else
{
return v___x_3097_;
}
}
else
{
return v___x_3095_;
}
}
else
{
return v___x_3093_;
}
}
else
{
return v___x_3091_;
}
}
v___jp_3122_:
{
uint8_t v___x_3123_; uint8_t v___x_3124_; 
v___x_3123_ = 65;
v___x_3124_ = lean_uint8_dec_le(v___x_3123_, v___y_3088_);
if (v___x_3124_ == 0)
{
goto v___jp_3089_;
}
else
{
uint8_t v___x_3125_; uint8_t v___x_3126_; 
v___x_3125_ = 90;
v___x_3126_ = lean_uint8_dec_le(v___y_3088_, v___x_3125_);
if (v___x_3126_ == 0)
{
goto v___jp_3089_;
}
else
{
return v___x_3126_;
}
}
}
v___jp_3127_:
{
uint8_t v___x_3128_; uint8_t v___x_3129_; 
v___x_3128_ = 97;
v___x_3129_ = lean_uint8_dec_le(v___x_3128_, v___y_3088_);
if (v___x_3129_ == 0)
{
goto v___jp_3122_;
}
else
{
uint8_t v___x_3130_; uint8_t v___x_3131_; 
v___x_3130_ = 122;
v___x_3131_ = lean_uint8_dec_le(v___y_3088_, v___x_3130_);
if (v___x_3131_ == 0)
{
goto v___jp_3122_;
}
else
{
return v___x_3131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo___lam__0___boxed(lean_object* v___y_3136_){
_start:
{
uint8_t v___y_287__boxed_3137_; uint8_t v_res_3138_; lean_object* v_r_3139_; 
v___y_287__boxed_3137_ = lean_unbox(v___y_3136_);
v_res_3138_ = l_Std_Http_URI_Builder_setUserInfo___lam__0(v___y_287__boxed_3137_);
v_r_3139_ = lean_box(v_res_3138_);
return v_r_3139_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo(lean_object* v_b_3141_, lean_object* v_username_3142_, lean_object* v_password_3143_){
_start:
{
lean_object* v_scheme_3144_; lean_object* v_host_3145_; lean_object* v_port_3146_; lean_object* v_pathSegments_3147_; lean_object* v_query_3148_; lean_object* v_fragment_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3174_; 
v_scheme_3144_ = lean_ctor_get(v_b_3141_, 0);
v_host_3145_ = lean_ctor_get(v_b_3141_, 2);
v_port_3146_ = lean_ctor_get(v_b_3141_, 3);
v_pathSegments_3147_ = lean_ctor_get(v_b_3141_, 4);
v_query_3148_ = lean_ctor_get(v_b_3141_, 5);
v_fragment_3149_ = lean_ctor_get(v_b_3141_, 6);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_b_3141_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; 
v_unused_3175_ = lean_ctor_get(v_b_3141_, 1);
lean_dec(v_unused_3175_);
v___x_3151_ = v_b_3141_;
v_isShared_3152_ = v_isSharedCheck_3174_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_fragment_3149_);
lean_inc(v_query_3148_);
lean_inc(v_pathSegments_3147_);
lean_inc(v_port_3146_);
lean_inc(v_host_3145_);
lean_inc(v_scheme_3144_);
lean_dec(v_b_3141_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3174_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___y_3154_; lean_object* v___f_3159_; lean_object* v___f_3160_; lean_object* v___x_3161_; 
v___f_3159_ = ((lean_object*)(l_Std_Http_URI_Builder_setUserInfo___closed__0));
v___f_3160_ = ((lean_object*)(l_Std_Http_URI_UserInfo_ofStrings___closed__0));
v___x_3161_ = l_Std_Http_URI_EncodedString_encodeEscaping(v___f_3159_, v_username_3142_, v___f_3160_);
if (lean_obj_tag(v_password_3143_) == 0)
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = lean_box(0);
v___x_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3161_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___y_3154_ = v___x_3163_;
goto v___jp_3153_;
}
else
{
lean_object* v_val_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3173_; 
v_val_3164_ = lean_ctor_get(v_password_3143_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_password_3143_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3166_ = v_password_3143_;
v_isShared_3167_ = v_isSharedCheck_3173_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_val_3164_);
lean_dec(v_password_3143_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3173_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3168_; lean_object* v___x_3170_; 
v___x_3168_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_3164_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 0, v___x_3168_);
v___x_3170_ = v___x_3166_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3168_);
v___x_3170_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
lean_object* v___x_3171_; 
v___x_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3161_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___y_3154_ = v___x_3171_;
goto v___jp_3153_;
}
}
}
v___jp_3153_:
{
lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3155_, 0, v___y_3154_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 1, v___x_3155_);
v___x_3157_ = v___x_3151_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_scheme_3144_);
lean_ctor_set(v_reuseFailAlloc_3158_, 1, v___x_3155_);
lean_ctor_set(v_reuseFailAlloc_3158_, 2, v_host_3145_);
lean_ctor_set(v_reuseFailAlloc_3158_, 3, v_port_3146_);
lean_ctor_set(v_reuseFailAlloc_3158_, 4, v_pathSegments_3147_);
lean_ctor_set(v_reuseFailAlloc_3158_, 5, v_query_3148_);
lean_ctor_set(v_reuseFailAlloc_3158_, 6, v_fragment_3149_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x3f(lean_object* v_b_3176_, lean_object* v_name_3177_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = lean_uv_pton_v4(v_name_3177_);
if (lean_obj_tag(v___x_3178_) == 1)
{
lean_object* v_val_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3202_; 
lean_dec_ref(v_name_3177_);
v_val_3179_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3181_ = v___x_3178_;
v_isShared_3182_ = v_isSharedCheck_3202_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_val_3179_);
lean_dec(v___x_3178_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3202_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v_scheme_3183_; lean_object* v_userInfo_3184_; lean_object* v_port_3185_; lean_object* v_pathSegments_3186_; lean_object* v_query_3187_; lean_object* v_fragment_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3200_; 
v_scheme_3183_ = lean_ctor_get(v_b_3176_, 0);
v_userInfo_3184_ = lean_ctor_get(v_b_3176_, 1);
v_port_3185_ = lean_ctor_get(v_b_3176_, 3);
v_pathSegments_3186_ = lean_ctor_get(v_b_3176_, 4);
v_query_3187_ = lean_ctor_get(v_b_3176_, 5);
v_fragment_3188_ = lean_ctor_get(v_b_3176_, 6);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_b_3176_);
if (v_isSharedCheck_3200_ == 0)
{
lean_object* v_unused_3201_; 
v_unused_3201_ = lean_ctor_get(v_b_3176_, 2);
lean_dec(v_unused_3201_);
v___x_3190_ = v_b_3176_;
v_isShared_3191_ = v_isSharedCheck_3200_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_fragment_3188_);
lean_inc(v_query_3187_);
lean_inc(v_pathSegments_3186_);
lean_inc(v_port_3185_);
lean_inc(v_userInfo_3184_);
lean_inc(v_scheme_3183_);
lean_dec(v_b_3176_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3200_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3192_; lean_object* v___x_3194_; 
v___x_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3192_, 0, v_val_3179_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 0, v___x_3192_);
v___x_3194_ = v___x_3181_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3192_);
v___x_3194_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3196_; 
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 2, v___x_3194_);
v___x_3196_ = v___x_3190_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_scheme_3183_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_userInfo_3184_);
lean_ctor_set(v_reuseFailAlloc_3198_, 2, v___x_3194_);
lean_ctor_set(v_reuseFailAlloc_3198_, 3, v_port_3185_);
lean_ctor_set(v_reuseFailAlloc_3198_, 4, v_pathSegments_3186_);
lean_ctor_set(v_reuseFailAlloc_3198_, 5, v_query_3187_);
lean_ctor_set(v_reuseFailAlloc_3198_, 6, v_fragment_3188_);
v___x_3196_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
lean_object* v___x_3197_; 
v___x_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
return v___x_3197_;
}
}
}
}
}
else
{
lean_object* v___x_3203_; 
lean_dec(v___x_3178_);
v___x_3203_ = l_Std_Http_URI_DomainName_ofString_x3f(v_name_3177_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v___x_3204_; 
lean_dec_ref(v_b_3176_);
v___x_3204_ = lean_box(0);
return v___x_3204_;
}
else
{
lean_object* v_val_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3228_; 
v_val_3205_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3207_ = v___x_3203_;
v_isShared_3208_ = v_isSharedCheck_3228_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_val_3205_);
lean_dec(v___x_3203_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3228_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v_scheme_3209_; lean_object* v_userInfo_3210_; lean_object* v_port_3211_; lean_object* v_pathSegments_3212_; lean_object* v_query_3213_; lean_object* v_fragment_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3226_; 
v_scheme_3209_ = lean_ctor_get(v_b_3176_, 0);
v_userInfo_3210_ = lean_ctor_get(v_b_3176_, 1);
v_port_3211_ = lean_ctor_get(v_b_3176_, 3);
v_pathSegments_3212_ = lean_ctor_get(v_b_3176_, 4);
v_query_3213_ = lean_ctor_get(v_b_3176_, 5);
v_fragment_3214_ = lean_ctor_get(v_b_3176_, 6);
v_isSharedCheck_3226_ = !lean_is_exclusive(v_b_3176_);
if (v_isSharedCheck_3226_ == 0)
{
lean_object* v_unused_3227_; 
v_unused_3227_ = lean_ctor_get(v_b_3176_, 2);
lean_dec(v_unused_3227_);
v___x_3216_ = v_b_3176_;
v_isShared_3217_ = v_isSharedCheck_3226_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_fragment_3214_);
lean_inc(v_query_3213_);
lean_inc(v_pathSegments_3212_);
lean_inc(v_port_3211_);
lean_inc(v_userInfo_3210_);
lean_inc(v_scheme_3209_);
lean_dec(v_b_3176_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3226_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3218_; lean_object* v___x_3220_; 
v___x_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3218_, 0, v_val_3205_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 0, v___x_3218_);
v___x_3220_ = v___x_3207_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3218_);
v___x_3220_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
lean_object* v___x_3222_; 
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 2, v___x_3220_);
v___x_3222_ = v___x_3216_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_scheme_3209_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v_userInfo_3210_);
lean_ctor_set(v_reuseFailAlloc_3224_, 2, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3224_, 3, v_port_3211_);
lean_ctor_set(v_reuseFailAlloc_3224_, 4, v_pathSegments_3212_);
lean_ctor_set(v_reuseFailAlloc_3224_, 5, v_query_3213_);
lean_ctor_set(v_reuseFailAlloc_3224_, 6, v_fragment_3214_);
v___x_3222_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3223_; 
v___x_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
return v___x_3223_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x21(lean_object* v_b_3231_, lean_object* v_name_3232_){
_start:
{
lean_object* v___x_3233_; 
lean_inc_ref(v_name_3232_);
v___x_3233_ = l_Std_Http_URI_Builder_setHost_x3f(v_b_3231_, v_name_3232_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3234_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_3235_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__0));
v___x_3236_ = lean_unsigned_to_nat(780u);
v___x_3237_ = lean_unsigned_to_nat(14u);
v___x_3238_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__1));
v___x_3239_ = l_String_quote(v_name_3232_);
v___x_3240_ = lean_string_append(v___x_3238_, v___x_3239_);
lean_dec_ref(v___x_3239_);
v___x_3241_ = l_mkPanicMessageWithDecl(v___x_3234_, v___x_3235_, v___x_3236_, v___x_3237_, v___x_3240_);
lean_dec_ref(v___x_3240_);
v___x_3242_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_3241_);
return v___x_3242_;
}
else
{
lean_object* v_val_3243_; 
lean_dec_ref(v_name_3232_);
v_val_3243_ = lean_ctor_get(v___x_3233_, 0);
lean_inc(v_val_3243_);
lean_dec_ref_known(v___x_3233_, 1);
return v_val_3243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv4(lean_object* v_b_3244_, lean_object* v_addr_3245_){
_start:
{
lean_object* v_scheme_3246_; lean_object* v_userInfo_3247_; lean_object* v_port_3248_; lean_object* v_pathSegments_3249_; lean_object* v_query_3250_; lean_object* v_fragment_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3260_; 
v_scheme_3246_ = lean_ctor_get(v_b_3244_, 0);
v_userInfo_3247_ = lean_ctor_get(v_b_3244_, 1);
v_port_3248_ = lean_ctor_get(v_b_3244_, 3);
v_pathSegments_3249_ = lean_ctor_get(v_b_3244_, 4);
v_query_3250_ = lean_ctor_get(v_b_3244_, 5);
v_fragment_3251_ = lean_ctor_get(v_b_3244_, 6);
v_isSharedCheck_3260_ = !lean_is_exclusive(v_b_3244_);
if (v_isSharedCheck_3260_ == 0)
{
lean_object* v_unused_3261_; 
v_unused_3261_ = lean_ctor_get(v_b_3244_, 2);
lean_dec(v_unused_3261_);
v___x_3253_ = v_b_3244_;
v_isShared_3254_ = v_isSharedCheck_3260_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_fragment_3251_);
lean_inc(v_query_3250_);
lean_inc(v_pathSegments_3249_);
lean_inc(v_port_3248_);
lean_inc(v_userInfo_3247_);
lean_inc(v_scheme_3246_);
lean_dec(v_b_3244_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3260_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3258_; 
v___x_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3255_, 0, v_addr_3245_);
v___x_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 2, v___x_3256_);
v___x_3258_ = v___x_3253_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_scheme_3246_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v_userInfo_3247_);
lean_ctor_set(v_reuseFailAlloc_3259_, 2, v___x_3256_);
lean_ctor_set(v_reuseFailAlloc_3259_, 3, v_port_3248_);
lean_ctor_set(v_reuseFailAlloc_3259_, 4, v_pathSegments_3249_);
lean_ctor_set(v_reuseFailAlloc_3259_, 5, v_query_3250_);
lean_ctor_set(v_reuseFailAlloc_3259_, 6, v_fragment_3251_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv6(lean_object* v_b_3262_, lean_object* v_addr_3263_){
_start:
{
lean_object* v_scheme_3264_; lean_object* v_userInfo_3265_; lean_object* v_port_3266_; lean_object* v_pathSegments_3267_; lean_object* v_query_3268_; lean_object* v_fragment_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3278_; 
v_scheme_3264_ = lean_ctor_get(v_b_3262_, 0);
v_userInfo_3265_ = lean_ctor_get(v_b_3262_, 1);
v_port_3266_ = lean_ctor_get(v_b_3262_, 3);
v_pathSegments_3267_ = lean_ctor_get(v_b_3262_, 4);
v_query_3268_ = lean_ctor_get(v_b_3262_, 5);
v_fragment_3269_ = lean_ctor_get(v_b_3262_, 6);
v_isSharedCheck_3278_ = !lean_is_exclusive(v_b_3262_);
if (v_isSharedCheck_3278_ == 0)
{
lean_object* v_unused_3279_; 
v_unused_3279_ = lean_ctor_get(v_b_3262_, 2);
lean_dec(v_unused_3279_);
v___x_3271_ = v_b_3262_;
v_isShared_3272_ = v_isSharedCheck_3278_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_fragment_3269_);
lean_inc(v_query_3268_);
lean_inc(v_pathSegments_3267_);
lean_inc(v_port_3266_);
lean_inc(v_userInfo_3265_);
lean_inc(v_scheme_3264_);
lean_dec(v_b_3262_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3278_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3276_; 
v___x_3273_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3273_, 0, v_addr_3263_);
v___x_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3273_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 2, v___x_3274_);
v___x_3276_ = v___x_3271_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_scheme_3264_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v_userInfo_3265_);
lean_ctor_set(v_reuseFailAlloc_3277_, 2, v___x_3274_);
lean_ctor_set(v_reuseFailAlloc_3277_, 3, v_port_3266_);
lean_ctor_set(v_reuseFailAlloc_3277_, 4, v_pathSegments_3267_);
lean_ctor_set(v_reuseFailAlloc_3277_, 5, v_query_3268_);
lean_ctor_set(v_reuseFailAlloc_3277_, 6, v_fragment_3269_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort(lean_object* v_b_3280_, uint16_t v_port_3281_){
_start:
{
lean_object* v_scheme_3282_; lean_object* v_userInfo_3283_; lean_object* v_host_3284_; lean_object* v_pathSegments_3285_; lean_object* v_query_3286_; lean_object* v_fragment_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3295_; 
v_scheme_3282_ = lean_ctor_get(v_b_3280_, 0);
v_userInfo_3283_ = lean_ctor_get(v_b_3280_, 1);
v_host_3284_ = lean_ctor_get(v_b_3280_, 2);
v_pathSegments_3285_ = lean_ctor_get(v_b_3280_, 4);
v_query_3286_ = lean_ctor_get(v_b_3280_, 5);
v_fragment_3287_ = lean_ctor_get(v_b_3280_, 6);
v_isSharedCheck_3295_ = !lean_is_exclusive(v_b_3280_);
if (v_isSharedCheck_3295_ == 0)
{
lean_object* v_unused_3296_; 
v_unused_3296_ = lean_ctor_get(v_b_3280_, 3);
lean_dec(v_unused_3296_);
v___x_3289_ = v_b_3280_;
v_isShared_3290_ = v_isSharedCheck_3295_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_fragment_3287_);
lean_inc(v_query_3286_);
lean_inc(v_pathSegments_3285_);
lean_inc(v_host_3284_);
lean_inc(v_userInfo_3283_);
lean_inc(v_scheme_3282_);
lean_dec(v_b_3280_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3295_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3291_; lean_object* v___x_3293_; 
v___x_3291_ = lean_alloc_ctor(2, 0, 2);
lean_ctor_set_uint16(v___x_3291_, 0, v_port_3281_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 3, v___x_3291_);
v___x_3293_ = v___x_3289_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_scheme_3282_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v_userInfo_3283_);
lean_ctor_set(v_reuseFailAlloc_3294_, 2, v_host_3284_);
lean_ctor_set(v_reuseFailAlloc_3294_, 3, v___x_3291_);
lean_ctor_set(v_reuseFailAlloc_3294_, 4, v_pathSegments_3285_);
lean_ctor_set(v_reuseFailAlloc_3294_, 5, v_query_3286_);
lean_ctor_set(v_reuseFailAlloc_3294_, 6, v_fragment_3287_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort___boxed(lean_object* v_b_3297_, lean_object* v_port_3298_){
_start:
{
uint16_t v_port_boxed_3299_; lean_object* v_res_3300_; 
v_port_boxed_3299_ = lean_unbox(v_port_3298_);
v_res_3300_ = l_Std_Http_URI_Builder_setPort(v_b_3297_, v_port_boxed_3299_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPath(lean_object* v_b_3301_, lean_object* v_segments_3302_){
_start:
{
lean_object* v_scheme_3303_; lean_object* v_userInfo_3304_; lean_object* v_host_3305_; lean_object* v_port_3306_; lean_object* v_query_3307_; lean_object* v_fragment_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
v_scheme_3303_ = lean_ctor_get(v_b_3301_, 0);
v_userInfo_3304_ = lean_ctor_get(v_b_3301_, 1);
v_host_3305_ = lean_ctor_get(v_b_3301_, 2);
v_port_3306_ = lean_ctor_get(v_b_3301_, 3);
v_query_3307_ = lean_ctor_get(v_b_3301_, 5);
v_fragment_3308_ = lean_ctor_get(v_b_3301_, 6);
v_isSharedCheck_3315_ = !lean_is_exclusive(v_b_3301_);
if (v_isSharedCheck_3315_ == 0)
{
lean_object* v_unused_3316_; 
v_unused_3316_ = lean_ctor_get(v_b_3301_, 4);
lean_dec(v_unused_3316_);
v___x_3310_ = v_b_3301_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_fragment_3308_);
lean_inc(v_query_3307_);
lean_inc(v_port_3306_);
lean_inc(v_host_3305_);
lean_inc(v_userInfo_3304_);
lean_inc(v_scheme_3303_);
lean_dec(v_b_3301_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 4, v_segments_3302_);
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_scheme_3303_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_userInfo_3304_);
lean_ctor_set(v_reuseFailAlloc_3314_, 2, v_host_3305_);
lean_ctor_set(v_reuseFailAlloc_3314_, 3, v_port_3306_);
lean_ctor_set(v_reuseFailAlloc_3314_, 4, v_segments_3302_);
lean_ctor_set(v_reuseFailAlloc_3314_, 5, v_query_3307_);
lean_ctor_set(v_reuseFailAlloc_3314_, 6, v_fragment_3308_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_appendPathSegment(lean_object* v_b_3317_, lean_object* v_segment_3318_){
_start:
{
lean_object* v_scheme_3319_; lean_object* v_userInfo_3320_; lean_object* v_host_3321_; lean_object* v_port_3322_; lean_object* v_pathSegments_3323_; lean_object* v_query_3324_; lean_object* v_fragment_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3333_; 
v_scheme_3319_ = lean_ctor_get(v_b_3317_, 0);
v_userInfo_3320_ = lean_ctor_get(v_b_3317_, 1);
v_host_3321_ = lean_ctor_get(v_b_3317_, 2);
v_port_3322_ = lean_ctor_get(v_b_3317_, 3);
v_pathSegments_3323_ = lean_ctor_get(v_b_3317_, 4);
v_query_3324_ = lean_ctor_get(v_b_3317_, 5);
v_fragment_3325_ = lean_ctor_get(v_b_3317_, 6);
v_isSharedCheck_3333_ = !lean_is_exclusive(v_b_3317_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3327_ = v_b_3317_;
v_isShared_3328_ = v_isSharedCheck_3333_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_fragment_3325_);
lean_inc(v_query_3324_);
lean_inc(v_pathSegments_3323_);
lean_inc(v_port_3322_);
lean_inc(v_host_3321_);
lean_inc(v_userInfo_3320_);
lean_inc(v_scheme_3319_);
lean_dec(v_b_3317_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3333_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3329_; lean_object* v___x_3331_; 
v___x_3329_ = lean_array_push(v_pathSegments_3323_, v_segment_3318_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 4, v___x_3329_);
v___x_3331_ = v___x_3327_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_scheme_3319_);
lean_ctor_set(v_reuseFailAlloc_3332_, 1, v_userInfo_3320_);
lean_ctor_set(v_reuseFailAlloc_3332_, 2, v_host_3321_);
lean_ctor_set(v_reuseFailAlloc_3332_, 3, v_port_3322_);
lean_ctor_set(v_reuseFailAlloc_3332_, 4, v___x_3329_);
lean_ctor_set(v_reuseFailAlloc_3332_, 5, v_query_3324_);
lean_ctor_set(v_reuseFailAlloc_3332_, 6, v_fragment_3325_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryParam(lean_object* v_b_3334_, lean_object* v_key_3335_, lean_object* v_value_3336_){
_start:
{
lean_object* v_scheme_3337_; lean_object* v_userInfo_3338_; lean_object* v_host_3339_; lean_object* v_port_3340_; lean_object* v_pathSegments_3341_; lean_object* v_query_3342_; lean_object* v_fragment_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3353_; 
v_scheme_3337_ = lean_ctor_get(v_b_3334_, 0);
v_userInfo_3338_ = lean_ctor_get(v_b_3334_, 1);
v_host_3339_ = lean_ctor_get(v_b_3334_, 2);
v_port_3340_ = lean_ctor_get(v_b_3334_, 3);
v_pathSegments_3341_ = lean_ctor_get(v_b_3334_, 4);
v_query_3342_ = lean_ctor_get(v_b_3334_, 5);
v_fragment_3343_ = lean_ctor_get(v_b_3334_, 6);
v_isSharedCheck_3353_ = !lean_is_exclusive(v_b_3334_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3345_ = v_b_3334_;
v_isShared_3346_ = v_isSharedCheck_3353_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_fragment_3343_);
lean_inc(v_query_3342_);
lean_inc(v_pathSegments_3341_);
lean_inc(v_port_3340_);
lean_inc(v_host_3339_);
lean_inc(v_userInfo_3338_);
lean_inc(v_scheme_3337_);
lean_dec(v_b_3334_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3353_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3351_; 
v___x_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3347_, 0, v_value_3336_);
v___x_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3348_, 0, v_key_3335_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___x_3349_ = lean_array_push(v_query_3342_, v___x_3348_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 5, v___x_3349_);
v___x_3351_ = v___x_3345_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_scheme_3337_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v_userInfo_3338_);
lean_ctor_set(v_reuseFailAlloc_3352_, 2, v_host_3339_);
lean_ctor_set(v_reuseFailAlloc_3352_, 3, v_port_3340_);
lean_ctor_set(v_reuseFailAlloc_3352_, 4, v_pathSegments_3341_);
lean_ctor_set(v_reuseFailAlloc_3352_, 5, v___x_3349_);
lean_ctor_set(v_reuseFailAlloc_3352_, 6, v_fragment_3343_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryFlag(lean_object* v_b_3354_, lean_object* v_key_3355_){
_start:
{
lean_object* v_scheme_3356_; lean_object* v_userInfo_3357_; lean_object* v_host_3358_; lean_object* v_port_3359_; lean_object* v_pathSegments_3360_; lean_object* v_query_3361_; lean_object* v_fragment_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3372_; 
v_scheme_3356_ = lean_ctor_get(v_b_3354_, 0);
v_userInfo_3357_ = lean_ctor_get(v_b_3354_, 1);
v_host_3358_ = lean_ctor_get(v_b_3354_, 2);
v_port_3359_ = lean_ctor_get(v_b_3354_, 3);
v_pathSegments_3360_ = lean_ctor_get(v_b_3354_, 4);
v_query_3361_ = lean_ctor_get(v_b_3354_, 5);
v_fragment_3362_ = lean_ctor_get(v_b_3354_, 6);
v_isSharedCheck_3372_ = !lean_is_exclusive(v_b_3354_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3364_ = v_b_3354_;
v_isShared_3365_ = v_isSharedCheck_3372_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_fragment_3362_);
lean_inc(v_query_3361_);
lean_inc(v_pathSegments_3360_);
lean_inc(v_port_3359_);
lean_inc(v_host_3358_);
lean_inc(v_userInfo_3357_);
lean_inc(v_scheme_3356_);
lean_dec(v_b_3354_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3372_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3370_; 
v___x_3366_ = lean_box(0);
v___x_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3367_, 0, v_key_3355_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___x_3368_ = lean_array_push(v_query_3361_, v___x_3367_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 5, v___x_3368_);
v___x_3370_ = v___x_3364_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_scheme_3356_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v_userInfo_3357_);
lean_ctor_set(v_reuseFailAlloc_3371_, 2, v_host_3358_);
lean_ctor_set(v_reuseFailAlloc_3371_, 3, v_port_3359_);
lean_ctor_set(v_reuseFailAlloc_3371_, 4, v_pathSegments_3360_);
lean_ctor_set(v_reuseFailAlloc_3371_, 5, v___x_3368_);
lean_ctor_set(v_reuseFailAlloc_3371_, 6, v_fragment_3362_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setQuery(lean_object* v_b_3373_, lean_object* v_query_3374_){
_start:
{
lean_object* v_scheme_3375_; lean_object* v_userInfo_3376_; lean_object* v_host_3377_; lean_object* v_port_3378_; lean_object* v_pathSegments_3379_; lean_object* v_fragment_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
v_scheme_3375_ = lean_ctor_get(v_b_3373_, 0);
v_userInfo_3376_ = lean_ctor_get(v_b_3373_, 1);
v_host_3377_ = lean_ctor_get(v_b_3373_, 2);
v_port_3378_ = lean_ctor_get(v_b_3373_, 3);
v_pathSegments_3379_ = lean_ctor_get(v_b_3373_, 4);
v_fragment_3380_ = lean_ctor_get(v_b_3373_, 6);
v_isSharedCheck_3387_ = !lean_is_exclusive(v_b_3373_);
if (v_isSharedCheck_3387_ == 0)
{
lean_object* v_unused_3388_; 
v_unused_3388_ = lean_ctor_get(v_b_3373_, 5);
lean_dec(v_unused_3388_);
v___x_3382_ = v_b_3373_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_fragment_3380_);
lean_inc(v_pathSegments_3379_);
lean_inc(v_port_3378_);
lean_inc(v_host_3377_);
lean_inc(v_userInfo_3376_);
lean_inc(v_scheme_3375_);
lean_dec(v_b_3373_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 5, v_query_3374_);
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_scheme_3375_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_userInfo_3376_);
lean_ctor_set(v_reuseFailAlloc_3386_, 2, v_host_3377_);
lean_ctor_set(v_reuseFailAlloc_3386_, 3, v_port_3378_);
lean_ctor_set(v_reuseFailAlloc_3386_, 4, v_pathSegments_3379_);
lean_ctor_set(v_reuseFailAlloc_3386_, 5, v_query_3374_);
lean_ctor_set(v_reuseFailAlloc_3386_, 6, v_fragment_3380_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setFragment(lean_object* v_b_3389_, lean_object* v_fragment_3390_){
_start:
{
lean_object* v_scheme_3391_; lean_object* v_userInfo_3392_; lean_object* v_host_3393_; lean_object* v_port_3394_; lean_object* v_pathSegments_3395_; lean_object* v_query_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3404_; 
v_scheme_3391_ = lean_ctor_get(v_b_3389_, 0);
v_userInfo_3392_ = lean_ctor_get(v_b_3389_, 1);
v_host_3393_ = lean_ctor_get(v_b_3389_, 2);
v_port_3394_ = lean_ctor_get(v_b_3389_, 3);
v_pathSegments_3395_ = lean_ctor_get(v_b_3389_, 4);
v_query_3396_ = lean_ctor_get(v_b_3389_, 5);
v_isSharedCheck_3404_ = !lean_is_exclusive(v_b_3389_);
if (v_isSharedCheck_3404_ == 0)
{
lean_object* v_unused_3405_; 
v_unused_3405_ = lean_ctor_get(v_b_3389_, 6);
lean_dec(v_unused_3405_);
v___x_3398_ = v_b_3389_;
v_isShared_3399_ = v_isSharedCheck_3404_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_query_3396_);
lean_inc(v_pathSegments_3395_);
lean_inc(v_port_3394_);
lean_inc(v_host_3393_);
lean_inc(v_userInfo_3392_);
lean_inc(v_scheme_3391_);
lean_dec(v_b_3389_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3404_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3400_; lean_object* v___x_3402_; 
v___x_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3400_, 0, v_fragment_3390_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 6, v___x_3400_);
v___x_3402_ = v___x_3398_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_scheme_3391_);
lean_ctor_set(v_reuseFailAlloc_3403_, 1, v_userInfo_3392_);
lean_ctor_set(v_reuseFailAlloc_3403_, 2, v_host_3393_);
lean_ctor_set(v_reuseFailAlloc_3403_, 3, v_port_3394_);
lean_ctor_set(v_reuseFailAlloc_3403_, 4, v_pathSegments_3395_);
lean_ctor_set(v_reuseFailAlloc_3403_, 5, v_query_3396_);
lean_ctor_set(v_reuseFailAlloc_3403_, 6, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(size_t v_sz_3406_, size_t v_i_3407_, lean_object* v_bs_3408_){
_start:
{
uint8_t v___x_3409_; 
v___x_3409_ = lean_usize_dec_lt(v_i_3407_, v_sz_3406_);
if (v___x_3409_ == 0)
{
return v_bs_3408_;
}
else
{
lean_object* v_v_3410_; lean_object* v___x_3411_; lean_object* v_bs_x27_3412_; lean_object* v___x_3413_; size_t v___x_3414_; size_t v___x_3415_; lean_object* v___x_3416_; 
v_v_3410_ = lean_array_uget(v_bs_3408_, v_i_3407_);
v___x_3411_ = lean_unsigned_to_nat(0u);
v_bs_x27_3412_ = lean_array_uset(v_bs_3408_, v_i_3407_, v___x_3411_);
v___x_3413_ = l_Std_Http_URI_EncodedSegment_encode(v_v_3410_);
v___x_3414_ = ((size_t)1ULL);
v___x_3415_ = lean_usize_add(v_i_3407_, v___x_3414_);
v___x_3416_ = lean_array_uset(v_bs_x27_3412_, v_i_3407_, v___x_3413_);
v_i_3407_ = v___x_3415_;
v_bs_3408_ = v___x_3416_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0___boxed(lean_object* v_sz_3418_, lean_object* v_i_3419_, lean_object* v_bs_3420_){
_start:
{
size_t v_sz_boxed_3421_; size_t v_i_boxed_3422_; lean_object* v_res_3423_; 
v_sz_boxed_3421_ = lean_unbox_usize(v_sz_3418_);
lean_dec(v_sz_3418_);
v_i_boxed_3422_ = lean_unbox_usize(v_i_3419_);
lean_dec(v_i_3419_);
v_res_3423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_boxed_3421_, v_i_boxed_3422_, v_bs_3420_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(size_t v_sz_3424_, size_t v_i_3425_, lean_object* v_bs_3426_){
_start:
{
uint8_t v___x_3427_; 
v___x_3427_ = lean_usize_dec_lt(v_i_3425_, v_sz_3424_);
if (v___x_3427_ == 0)
{
return v_bs_3426_;
}
else
{
lean_object* v_v_3428_; lean_object* v_fst_3429_; lean_object* v_snd_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3459_; 
v_v_3428_ = lean_array_uget(v_bs_3426_, v_i_3425_);
v_fst_3429_ = lean_ctor_get(v_v_3428_, 0);
v_snd_3430_ = lean_ctor_get(v_v_3428_, 1);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_v_3428_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3432_ = v_v_3428_;
v_isShared_3433_ = v_isSharedCheck_3459_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_snd_3430_);
lean_inc(v_fst_3429_);
lean_dec(v_v_3428_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3459_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; lean_object* v_bs_x27_3435_; lean_object* v___y_3437_; lean_object* v___x_3442_; 
v___x_3434_ = lean_unsigned_to_nat(0u);
v_bs_x27_3435_ = lean_array_uset(v_bs_3426_, v_i_3425_, v___x_3434_);
v___x_3442_ = l_Std_Http_URI_EncodedQueryParam_encode(v_fst_3429_);
if (lean_obj_tag(v_snd_3430_) == 0)
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3443_ = lean_box(0);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3443_);
lean_ctor_set(v___x_3432_, 0, v___x_3442_);
v___x_3445_ = v___x_3432_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
v___y_3437_ = v___x_3445_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_val_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3458_; 
v_val_3447_ = lean_ctor_get(v_snd_3430_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_snd_3430_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3449_ = v_snd_3430_;
v_isShared_3450_ = v_isSharedCheck_3458_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_val_3447_);
lean_dec(v_snd_3430_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3458_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3451_ = l_Std_Http_URI_EncodedQueryParam_encode(v_val_3447_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v___x_3451_);
v___x_3453_ = v___x_3449_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3455_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3453_);
lean_ctor_set(v___x_3432_, 0, v___x_3442_);
v___x_3455_ = v___x_3432_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
v___y_3437_ = v___x_3455_;
goto v___jp_3436_;
}
}
}
}
v___jp_3436_:
{
size_t v___x_3438_; size_t v___x_3439_; lean_object* v___x_3440_; 
v___x_3438_ = ((size_t)1ULL);
v___x_3439_ = lean_usize_add(v_i_3425_, v___x_3438_);
v___x_3440_ = lean_array_uset(v_bs_x27_3435_, v_i_3425_, v___y_3437_);
v_i_3425_ = v___x_3439_;
v_bs_3426_ = v___x_3440_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1___boxed(lean_object* v_sz_3460_, lean_object* v_i_3461_, lean_object* v_bs_3462_){
_start:
{
size_t v_sz_boxed_3463_; size_t v_i_boxed_3464_; lean_object* v_res_3465_; 
v_sz_boxed_3463_ = lean_unbox_usize(v_sz_3460_);
lean_dec(v_sz_3460_);
v_i_boxed_3464_ = lean_unbox_usize(v_i_3461_);
lean_dec(v_i_3461_);
v_res_3465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_boxed_3463_, v_i_boxed_3464_, v_bs_3462_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_build(lean_object* v_b_3466_){
_start:
{
lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; uint8_t v___y_3472_; lean_object* v___y_3473_; lean_object* v_scheme_3489_; lean_object* v_userInfo_3490_; lean_object* v_host_3491_; lean_object* v_port_3492_; lean_object* v_pathSegments_3493_; lean_object* v_query_3494_; lean_object* v_fragment_3495_; lean_object* v___y_3497_; 
v_scheme_3489_ = lean_ctor_get(v_b_3466_, 0);
lean_inc(v_scheme_3489_);
v_userInfo_3490_ = lean_ctor_get(v_b_3466_, 1);
lean_inc(v_userInfo_3490_);
v_host_3491_ = lean_ctor_get(v_b_3466_, 2);
lean_inc(v_host_3491_);
v_port_3492_ = lean_ctor_get(v_b_3466_, 3);
lean_inc(v_port_3492_);
v_pathSegments_3493_ = lean_ctor_get(v_b_3466_, 4);
lean_inc_ref(v_pathSegments_3493_);
v_query_3494_ = lean_ctor_get(v_b_3466_, 5);
lean_inc_ref(v_query_3494_);
v_fragment_3495_ = lean_ctor_get(v_b_3466_, 6);
lean_inc(v_fragment_3495_);
lean_dec_ref(v_b_3466_);
if (lean_obj_tag(v_scheme_3489_) == 0)
{
lean_object* v___x_3510_; 
v___x_3510_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___y_3497_ = v___x_3510_;
goto v___jp_3496_;
}
else
{
lean_object* v_val_3511_; 
v_val_3511_ = lean_ctor_get(v_scheme_3489_, 0);
lean_inc(v_val_3511_);
lean_dec_ref_known(v_scheme_3489_, 1);
v___y_3497_ = v_val_3511_;
goto v___jp_3496_;
}
v___jp_3467_:
{
size_t v_sz_3474_; size_t v___x_3475_; lean_object* v___x_3476_; lean_object* v_path_3477_; size_t v_sz_3478_; lean_object* v_query_3479_; lean_object* v___x_3480_; lean_object* v_query_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; uint8_t v___x_3484_; 
v_sz_3474_ = lean_array_size(v___y_3470_);
v___x_3475_ = ((size_t)0ULL);
v___x_3476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_3474_, v___x_3475_, v___y_3470_);
v_path_3477_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_path_3477_, 0, v___x_3476_);
lean_ctor_set_uint8(v_path_3477_, sizeof(void*)*1, v___y_3472_);
v_sz_3478_ = lean_array_size(v___y_3468_);
v_query_3479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_3478_, v___x_3475_, v___y_3468_);
v___x_3480_ = lean_array_to_list(v_query_3479_);
v_query_3481_ = lean_array_mk(v___x_3480_);
v___x_3482_ = lean_array_get_size(v_query_3481_);
v___x_3483_ = lean_unsigned_to_nat(0u);
v___x_3484_ = lean_nat_dec_eq(v___x_3482_, v___x_3483_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3485_, 0, v_query_3481_);
v___x_3486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3486_, 0, v___y_3469_);
lean_ctor_set(v___x_3486_, 1, v___y_3473_);
lean_ctor_set(v___x_3486_, 2, v_path_3477_);
lean_ctor_set(v___x_3486_, 3, v___x_3485_);
lean_ctor_set(v___x_3486_, 4, v___y_3471_);
return v___x_3486_;
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_dec_ref(v_query_3481_);
v___x_3487_ = lean_box(0);
v___x_3488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3488_, 0, v___y_3469_);
lean_ctor_set(v___x_3488_, 1, v___y_3473_);
lean_ctor_set(v___x_3488_, 2, v_path_3477_);
lean_ctor_set(v___x_3488_, 3, v___x_3487_);
lean_ctor_set(v___x_3488_, 4, v___y_3471_);
return v___x_3488_;
}
}
v___jp_3496_:
{
if (lean_obj_tag(v_host_3491_) == 0)
{
uint8_t v___x_3498_; lean_object* v___x_3499_; 
lean_dec(v_port_3492_);
lean_dec(v_userInfo_3490_);
v___x_3498_ = 1;
v___x_3499_ = lean_box(0);
v___y_3468_ = v_query_3494_;
v___y_3469_ = v___y_3497_;
v___y_3470_ = v_pathSegments_3493_;
v___y_3471_ = v_fragment_3495_;
v___y_3472_ = v___x_3498_;
v___y_3473_ = v___x_3499_;
goto v___jp_3467_;
}
else
{
lean_object* v_val_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3509_; 
v_val_3500_ = lean_ctor_get(v_host_3491_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v_host_3491_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3502_ = v_host_3491_;
v_isShared_3503_ = v_isSharedCheck_3509_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_val_3500_);
lean_dec(v_host_3491_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3509_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
uint8_t v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3507_; 
v___x_3504_ = 1;
v___x_3505_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3505_, 0, v_userInfo_3490_);
lean_ctor_set(v___x_3505_, 1, v_val_3500_);
lean_ctor_set(v___x_3505_, 2, v_port_3492_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 0, v___x_3505_);
v___x_3507_ = v___x_3502_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
v___y_3468_ = v_query_3494_;
v___y_3469_ = v___y_3497_;
v___y_3470_ = v_pathSegments_3493_;
v___y_3471_ = v_fragment_3495_;
v___y_3472_ = v___x_3504_;
v___y_3473_ = v___x_3507_;
goto v___jp_3467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withScheme_x21(lean_object* v_uri_3512_, lean_object* v_scheme_3513_){
_start:
{
lean_object* v_authority_3514_; lean_object* v_path_3515_; lean_object* v_query_3516_; lean_object* v_fragment_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3525_; 
v_authority_3514_ = lean_ctor_get(v_uri_3512_, 1);
v_path_3515_ = lean_ctor_get(v_uri_3512_, 2);
v_query_3516_ = lean_ctor_get(v_uri_3512_, 3);
v_fragment_3517_ = lean_ctor_get(v_uri_3512_, 4);
v_isSharedCheck_3525_ = !lean_is_exclusive(v_uri_3512_);
if (v_isSharedCheck_3525_ == 0)
{
lean_object* v_unused_3526_; 
v_unused_3526_ = lean_ctor_get(v_uri_3512_, 0);
lean_dec(v_unused_3526_);
v___x_3519_ = v_uri_3512_;
v_isShared_3520_ = v_isSharedCheck_3525_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_fragment_3517_);
lean_inc(v_query_3516_);
lean_inc(v_path_3515_);
lean_inc(v_authority_3514_);
lean_dec(v_uri_3512_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3525_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3521_ = l_Std_Http_URI_Scheme_ofString_x21(v_scheme_3513_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v___x_3521_);
v___x_3523_ = v___x_3519_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3521_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v_authority_3514_);
lean_ctor_set(v_reuseFailAlloc_3524_, 2, v_path_3515_);
lean_ctor_set(v_reuseFailAlloc_3524_, 3, v_query_3516_);
lean_ctor_set(v_reuseFailAlloc_3524_, 4, v_fragment_3517_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withAuthority(lean_object* v_uri_3527_, lean_object* v_authority_3528_){
_start:
{
lean_object* v_scheme_3529_; lean_object* v_path_3530_; lean_object* v_query_3531_; lean_object* v_fragment_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
v_scheme_3529_ = lean_ctor_get(v_uri_3527_, 0);
v_path_3530_ = lean_ctor_get(v_uri_3527_, 2);
v_query_3531_ = lean_ctor_get(v_uri_3527_, 3);
v_fragment_3532_ = lean_ctor_get(v_uri_3527_, 4);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_uri_3527_);
if (v_isSharedCheck_3539_ == 0)
{
lean_object* v_unused_3540_; 
v_unused_3540_ = lean_ctor_get(v_uri_3527_, 1);
lean_dec(v_unused_3540_);
v___x_3534_ = v_uri_3527_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_fragment_3532_);
lean_inc(v_query_3531_);
lean_inc(v_path_3530_);
lean_inc(v_scheme_3529_);
lean_dec(v_uri_3527_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 1, v_authority_3528_);
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_scheme_3529_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_authority_3528_);
lean_ctor_set(v_reuseFailAlloc_3538_, 2, v_path_3530_);
lean_ctor_set(v_reuseFailAlloc_3538_, 3, v_query_3531_);
lean_ctor_set(v_reuseFailAlloc_3538_, 4, v_fragment_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withPath(lean_object* v_uri_3541_, lean_object* v_path_3542_){
_start:
{
lean_object* v_scheme_3543_; lean_object* v_authority_3544_; lean_object* v_query_3545_; lean_object* v_fragment_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
v_scheme_3543_ = lean_ctor_get(v_uri_3541_, 0);
v_authority_3544_ = lean_ctor_get(v_uri_3541_, 1);
v_query_3545_ = lean_ctor_get(v_uri_3541_, 3);
v_fragment_3546_ = lean_ctor_get(v_uri_3541_, 4);
v_isSharedCheck_3553_ = !lean_is_exclusive(v_uri_3541_);
if (v_isSharedCheck_3553_ == 0)
{
lean_object* v_unused_3554_; 
v_unused_3554_ = lean_ctor_get(v_uri_3541_, 2);
lean_dec(v_unused_3554_);
v___x_3548_ = v_uri_3541_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_fragment_3546_);
lean_inc(v_query_3545_);
lean_inc(v_authority_3544_);
lean_inc(v_scheme_3543_);
lean_dec(v_uri_3541_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
lean_ctor_set(v___x_3548_, 2, v_path_3542_);
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_scheme_3543_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_authority_3544_);
lean_ctor_set(v_reuseFailAlloc_3552_, 2, v_path_3542_);
lean_ctor_set(v_reuseFailAlloc_3552_, 3, v_query_3545_);
lean_ctor_set(v_reuseFailAlloc_3552_, 4, v_fragment_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withQuery(lean_object* v_uri_3555_, lean_object* v_query_3556_){
_start:
{
lean_object* v_scheme_3557_; lean_object* v_authority_3558_; lean_object* v_path_3559_; lean_object* v_fragment_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3568_; 
v_scheme_3557_ = lean_ctor_get(v_uri_3555_, 0);
v_authority_3558_ = lean_ctor_get(v_uri_3555_, 1);
v_path_3559_ = lean_ctor_get(v_uri_3555_, 2);
v_fragment_3560_ = lean_ctor_get(v_uri_3555_, 4);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_uri_3555_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; 
v_unused_3569_ = lean_ctor_get(v_uri_3555_, 3);
lean_dec(v_unused_3569_);
v___x_3562_ = v_uri_3555_;
v_isShared_3563_ = v_isSharedCheck_3568_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_fragment_3560_);
lean_inc(v_path_3559_);
lean_inc(v_authority_3558_);
lean_inc(v_scheme_3557_);
lean_dec(v_uri_3555_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3568_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3564_; lean_object* v___x_3566_; 
v___x_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3564_, 0, v_query_3556_);
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 3, v___x_3564_);
v___x_3566_ = v___x_3562_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_scheme_3557_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_authority_3558_);
lean_ctor_set(v_reuseFailAlloc_3567_, 2, v_path_3559_);
lean_ctor_set(v_reuseFailAlloc_3567_, 3, v___x_3564_);
lean_ctor_set(v_reuseFailAlloc_3567_, 4, v_fragment_3560_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withFragment(lean_object* v_uri_3570_, lean_object* v_fragment_3571_){
_start:
{
lean_object* v_scheme_3572_; lean_object* v_authority_3573_; lean_object* v_path_3574_; lean_object* v_query_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
v_scheme_3572_ = lean_ctor_get(v_uri_3570_, 0);
v_authority_3573_ = lean_ctor_get(v_uri_3570_, 1);
v_path_3574_ = lean_ctor_get(v_uri_3570_, 2);
v_query_3575_ = lean_ctor_get(v_uri_3570_, 3);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_uri_3570_);
if (v_isSharedCheck_3582_ == 0)
{
lean_object* v_unused_3583_; 
v_unused_3583_ = lean_ctor_get(v_uri_3570_, 4);
lean_dec(v_unused_3583_);
v___x_3577_ = v_uri_3570_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_query_3575_);
lean_inc(v_path_3574_);
lean_inc(v_authority_3573_);
lean_inc(v_scheme_3572_);
lean_dec(v_uri_3570_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 4, v_fragment_3571_);
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_scheme_3572_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v_authority_3573_);
lean_ctor_set(v_reuseFailAlloc_3581_, 2, v_path_3574_);
lean_ctor_set(v_reuseFailAlloc_3581_, 3, v_query_3575_);
lean_ctor_set(v_reuseFailAlloc_3581_, 4, v_fragment_3571_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_normalize(lean_object* v_uri_3584_){
_start:
{
lean_object* v_scheme_3585_; lean_object* v_authority_3586_; lean_object* v_path_3587_; lean_object* v_query_3588_; lean_object* v_fragment_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3597_; 
v_scheme_3585_ = lean_ctor_get(v_uri_3584_, 0);
v_authority_3586_ = lean_ctor_get(v_uri_3584_, 1);
v_path_3587_ = lean_ctor_get(v_uri_3584_, 2);
v_query_3588_ = lean_ctor_get(v_uri_3584_, 3);
v_fragment_3589_ = lean_ctor_get(v_uri_3584_, 4);
v_isSharedCheck_3597_ = !lean_is_exclusive(v_uri_3584_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3591_ = v_uri_3584_;
v_isShared_3592_ = v_isSharedCheck_3597_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_fragment_3589_);
lean_inc(v_query_3588_);
lean_inc(v_path_3587_);
lean_inc(v_authority_3586_);
lean_inc(v_scheme_3585_);
lean_dec(v_uri_3584_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3597_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3593_; lean_object* v___x_3595_; 
v___x_3593_ = l_Std_Http_URI_Path_normalize(v_path_3587_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 2, v___x_3593_);
v___x_3595_ = v___x_3591_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_scheme_3585_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_authority_3586_);
lean_ctor_set(v_reuseFailAlloc_3596_, 2, v___x_3593_);
lean_ctor_set(v_reuseFailAlloc_3596_, 3, v_query_3588_);
lean_ctor_set(v_reuseFailAlloc_3596_, 4, v_fragment_3589_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___redArg(lean_object* v_x_3598_){
_start:
{
lean_object* v_scheme_3599_; lean_object* v_host_3600_; uint16_t v_port_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; uint8_t v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v_ctr_3622_; lean_object* v_a_3623_; 
v_scheme_3599_ = lean_ctor_get(v_x_3598_, 0);
lean_inc_ref(v_scheme_3599_);
v_host_3600_ = lean_ctor_get(v_x_3598_, 1);
lean_inc_ref(v_host_3600_);
v_port_3601_ = lean_ctor_get_uint16(v_x_3598_, sizeof(void*)*2);
lean_dec_ref(v_x_3598_);
v___x_3602_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_3603_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_3604_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_3605_ = l_String_quote(v_scheme_3599_);
v___x_3606_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
v___x_3607_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3604_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = 0;
v___x_3609_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3609_, 0, v___x_3607_);
lean_ctor_set_uint8(v___x_3609_, sizeof(void*)*1, v___x_3608_);
v___x_3610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3603_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
v___x_3611_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_3612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3610_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
v___x_3613_ = lean_box(1);
v___x_3614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3612_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_3616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3614_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
v___x_3617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3616_);
lean_ctor_set(v___x_3617_, 1, v___x_3602_);
v___x_3618_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_3619_ = lean_unsigned_to_nat(0u);
v___x_3620_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_3600_))
{
case 0:
{
lean_object* v_name_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3662_; 
v_name_3653_ = lean_ctor_get(v_host_3600_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_host_3600_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3655_ = v_host_3600_;
v_isShared_3656_ = v_isSharedCheck_3662_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_name_3653_);
lean_dec(v_host_3600_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3662_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
v___x_3657_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_3658_ = l_String_quote(v_name_3653_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set_tag(v___x_3655_, 3);
lean_ctor_set(v___x_3655_, 0, v___x_3658_);
v___x_3660_ = v___x_3655_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3658_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
v_ctr_3622_ = v___x_3657_;
v_a_3623_ = v___x_3660_;
goto v___jp_3621_;
}
}
}
case 1:
{
lean_object* v_ipv4_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3672_; 
v_ipv4_3663_ = lean_ctor_get(v_host_3600_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v_host_3600_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3665_ = v_host_3600_;
v_isShared_3666_ = v_isSharedCheck_3672_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_ipv4_3663_);
lean_dec(v_host_3600_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3672_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3670_; 
v___x_3667_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_3668_ = lean_uv_ntop_v4(v_ipv4_3663_);
lean_dec_ref(v_ipv4_3663_);
if (v_isShared_3666_ == 0)
{
lean_ctor_set_tag(v___x_3665_, 3);
lean_ctor_set(v___x_3665_, 0, v___x_3668_);
v___x_3670_ = v___x_3665_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3668_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
v_ctr_3622_ = v___x_3667_;
v_a_3623_ = v___x_3670_;
goto v___jp_3621_;
}
}
}
default: 
{
lean_object* v_ipv6_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3682_; 
v_ipv6_3673_ = lean_ctor_get(v_host_3600_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v_host_3600_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3675_ = v_host_3600_;
v_isShared_3676_ = v_isSharedCheck_3682_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_ipv6_3673_);
lean_dec(v_host_3600_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3682_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3680_; 
v___x_3677_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_3678_ = lean_uv_ntop_v6(v_ipv6_3673_);
lean_dec_ref(v_ipv6_3673_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set_tag(v___x_3675_, 3);
lean_ctor_set(v___x_3675_, 0, v___x_3678_);
v___x_3680_ = v___x_3675_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3678_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
v_ctr_3622_ = v___x_3677_;
v_a_3623_ = v___x_3680_;
goto v___jp_3621_;
}
}
}
}
v___jp_3621_:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3624_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_3625_ = lean_string_append(v___x_3624_, v_ctr_3622_);
v___x_3626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3625_);
v___x_3627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3626_);
lean_ctor_set(v___x_3627_, 1, v___x_3613_);
v___x_3628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3627_);
lean_ctor_set(v___x_3628_, 1, v_a_3623_);
v___x_3629_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3620_);
lean_ctor_set(v___x_3629_, 1, v___x_3628_);
v___x_3630_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3630_, 0, v___x_3629_);
lean_ctor_set_uint8(v___x_3630_, sizeof(void*)*1, v___x_3608_);
v___x_3631_ = l_Repr_addAppParen(v___x_3630_, v___x_3619_);
v___x_3632_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3618_);
lean_ctor_set(v___x_3632_, 1, v___x_3631_);
v___x_3633_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
lean_ctor_set_uint8(v___x_3633_, sizeof(void*)*1, v___x_3608_);
v___x_3634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3617_);
lean_ctor_set(v___x_3634_, 1, v___x_3633_);
v___x_3635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
lean_ctor_set(v___x_3635_, 1, v___x_3611_);
v___x_3636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3635_);
lean_ctor_set(v___x_3636_, 1, v___x_3613_);
v___x_3637_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_3638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3636_);
lean_ctor_set(v___x_3638_, 1, v___x_3637_);
v___x_3639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3638_);
lean_ctor_set(v___x_3639_, 1, v___x_3602_);
v___x_3640_ = lean_uint16_to_nat(v_port_3601_);
v___x_3641_ = l_Nat_reprFast(v___x_3640_);
v___x_3642_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
v___x_3643_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3618_);
lean_ctor_set(v___x_3643_, 1, v___x_3642_);
v___x_3644_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
lean_ctor_set_uint8(v___x_3644_, sizeof(void*)*1, v___x_3608_);
v___x_3645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3639_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_3647_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_3648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3647_);
lean_ctor_set(v___x_3648_, 1, v___x_3645_);
v___x_3649_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_3650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3648_);
lean_ctor_set(v___x_3650_, 1, v___x_3649_);
v___x_3651_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3646_);
lean_ctor_set(v___x_3651_, 1, v___x_3650_);
v___x_3652_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
lean_ctor_set_uint8(v___x_3652_, sizeof(void*)*1, v___x_3608_);
return v___x_3652_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr(lean_object* v_x_3683_, lean_object* v_prec_3684_){
_start:
{
lean_object* v___x_3685_; 
v___x_3685_ = l_Std_Http_URI_instReprOrigin_repr___redArg(v_x_3683_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___boxed(lean_object* v_x_3686_, lean_object* v_prec_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l_Std_Http_URI_instReprOrigin_repr(v_x_3686_, v_prec_3687_);
lean_dec(v_prec_3687_);
return v_res_3688_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqOrigin_beq(lean_object* v_x_3691_, lean_object* v_x_3692_){
_start:
{
lean_object* v_scheme_3693_; lean_object* v_host_3694_; uint16_t v_port_3695_; lean_object* v_scheme_3696_; lean_object* v_host_3697_; uint16_t v_port_3698_; uint8_t v___x_3699_; 
v_scheme_3693_ = lean_ctor_get(v_x_3691_, 0);
v_host_3694_ = lean_ctor_get(v_x_3691_, 1);
v_port_3695_ = lean_ctor_get_uint16(v_x_3691_, sizeof(void*)*2);
v_scheme_3696_ = lean_ctor_get(v_x_3692_, 0);
v_host_3697_ = lean_ctor_get(v_x_3692_, 1);
v_port_3698_ = lean_ctor_get_uint16(v_x_3692_, sizeof(void*)*2);
v___x_3699_ = lean_string_dec_eq(v_scheme_3693_, v_scheme_3696_);
if (v___x_3699_ == 0)
{
return v___x_3699_;
}
else
{
uint8_t v___x_3700_; 
v___x_3700_ = l_Std_Http_URI_instBEqHost_beq(v_host_3694_, v_host_3697_);
if (v___x_3700_ == 0)
{
return v___x_3700_;
}
else
{
uint8_t v___x_3701_; 
v___x_3701_ = lean_uint16_dec_eq(v_port_3695_, v_port_3698_);
return v___x_3701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqOrigin_beq___boxed(lean_object* v_x_3702_, lean_object* v_x_3703_){
_start:
{
uint8_t v_res_3704_; lean_object* v_r_3705_; 
v_res_3704_ = l_Std_Http_URI_instBEqOrigin_beq(v_x_3702_, v_x_3703_);
lean_dec_ref(v_x_3703_);
lean_dec_ref(v_x_3702_);
v_r_3705_ = lean_box(v_res_3704_);
return v_r_3705_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Origin_hostHeader(lean_object* v_o_3708_){
_start:
{
lean_object* v_scheme_3709_; lean_object* v_host_3710_; uint16_t v_port_3711_; lean_object* v___y_3713_; uint16_t v_defaultPort_3719_; uint8_t v___x_3720_; 
v_scheme_3709_ = lean_ctor_get(v_o_3708_, 0);
lean_inc_ref(v_scheme_3709_);
v_host_3710_ = lean_ctor_get(v_o_3708_, 1);
lean_inc_ref(v_host_3710_);
v_port_3711_ = lean_ctor_get_uint16(v_o_3708_, sizeof(void*)*2);
lean_dec_ref(v_o_3708_);
v_defaultPort_3719_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_3709_);
lean_dec_ref(v_scheme_3709_);
v___x_3720_ = lean_uint16_dec_eq(v_port_3711_, v_defaultPort_3719_);
if (v___x_3720_ == 0)
{
switch(lean_obj_tag(v_host_3710_))
{
case 0:
{
lean_object* v_name_3721_; 
v_name_3721_ = lean_ctor_get(v_host_3710_, 0);
lean_inc_ref(v_name_3721_);
lean_dec_ref_known(v_host_3710_, 1);
v___y_3713_ = v_name_3721_;
goto v___jp_3712_;
}
case 1:
{
lean_object* v_ipv4_3722_; lean_object* v___x_3723_; 
v_ipv4_3722_ = lean_ctor_get(v_host_3710_, 0);
lean_inc_ref(v_ipv4_3722_);
lean_dec_ref_known(v_host_3710_, 1);
v___x_3723_ = lean_uv_ntop_v4(v_ipv4_3722_);
lean_dec_ref(v_ipv4_3722_);
v___y_3713_ = v___x_3723_;
goto v___jp_3712_;
}
default: 
{
lean_object* v_ipv6_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v_ipv6_3724_ = lean_ctor_get(v_host_3710_, 0);
lean_inc_ref(v_ipv6_3724_);
lean_dec_ref_known(v_host_3710_, 1);
v___x_3725_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3726_ = lean_uv_ntop_v6(v_ipv6_3724_);
lean_dec_ref(v_ipv6_3724_);
v___x_3727_ = lean_string_append(v___x_3725_, v___x_3726_);
lean_dec_ref(v___x_3726_);
v___x_3728_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3729_ = lean_string_append(v___x_3727_, v___x_3728_);
v___y_3713_ = v___x_3729_;
goto v___jp_3712_;
}
}
}
else
{
switch(lean_obj_tag(v_host_3710_))
{
case 0:
{
lean_object* v_name_3730_; 
v_name_3730_ = lean_ctor_get(v_host_3710_, 0);
lean_inc_ref(v_name_3730_);
lean_dec_ref_known(v_host_3710_, 1);
return v_name_3730_;
}
case 1:
{
lean_object* v_ipv4_3731_; lean_object* v___x_3732_; 
v_ipv4_3731_ = lean_ctor_get(v_host_3710_, 0);
lean_inc_ref(v_ipv4_3731_);
lean_dec_ref_known(v_host_3710_, 1);
v___x_3732_ = lean_uv_ntop_v4(v_ipv4_3731_);
lean_dec_ref(v_ipv4_3731_);
return v___x_3732_;
}
default: 
{
lean_object* v_ipv6_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v_ipv6_3733_ = lean_ctor_get(v_host_3710_, 0);
lean_inc_ref(v_ipv6_3733_);
lean_dec_ref_known(v_host_3710_, 1);
v___x_3734_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3735_ = lean_uv_ntop_v6(v_ipv6_3733_);
lean_dec_ref(v_ipv6_3733_);
v___x_3736_ = lean_string_append(v___x_3734_, v___x_3735_);
lean_dec_ref(v___x_3735_);
v___x_3737_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3738_ = lean_string_append(v___x_3736_, v___x_3737_);
return v___x_3738_;
}
}
}
v___jp_3712_:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3714_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3715_ = lean_string_append(v___y_3713_, v___x_3714_);
v___x_3716_ = lean_uint16_to_nat(v_port_3711_);
v___x_3717_ = l_Nat_reprFast(v___x_3716_);
v___x_3718_ = lean_string_append(v___x_3715_, v___x_3717_);
lean_dec_ref(v___x_3717_);
return v___x_3718_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___redArg(lean_object* v_x_3745_){
_start:
{
lean_object* v_authority_3746_; lean_object* v_path_3747_; lean_object* v_query_3748_; lean_object* v_fragment_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; uint8_t v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v_authority_3746_ = lean_ctor_get(v_x_3745_, 0);
lean_inc(v_authority_3746_);
v_path_3747_ = lean_ctor_get(v_x_3745_, 1);
lean_inc_ref(v_path_3747_);
v_query_3748_ = lean_ctor_get(v_x_3745_, 2);
lean_inc(v_query_3748_);
v_fragment_3749_ = lean_ctor_get(v_x_3745_, 3);
lean_inc(v_fragment_3749_);
lean_dec_ref(v_x_3745_);
v___x_3750_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_3751_ = ((lean_object*)(l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__1));
v___x_3752_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_3753_ = lean_unsigned_to_nat(0u);
v___x_3754_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_3746_, v___x_3753_);
v___x_3755_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3752_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___x_3756_ = 0;
v___x_3757_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3757_, 0, v___x_3755_);
lean_ctor_set_uint8(v___x_3757_, sizeof(void*)*1, v___x_3756_);
v___x_3758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3751_);
lean_ctor_set(v___x_3758_, 1, v___x_3757_);
v___x_3759_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_3760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3758_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = lean_box(1);
v___x_3762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3760_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_3764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3762_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3764_);
lean_ctor_set(v___x_3765_, 1, v___x_3750_);
v___x_3766_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_3767_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3747_);
v___x_3768_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3766_);
lean_ctor_set(v___x_3768_, 1, v___x_3767_);
v___x_3769_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3769_, 0, v___x_3768_);
lean_ctor_set_uint8(v___x_3769_, sizeof(void*)*1, v___x_3756_);
v___x_3770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3765_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v___x_3771_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
lean_ctor_set(v___x_3771_, 1, v___x_3759_);
v___x_3772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3771_);
lean_ctor_set(v___x_3772_, 1, v___x_3761_);
v___x_3773_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_3774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3772_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3774_);
lean_ctor_set(v___x_3775_, 1, v___x_3750_);
v___x_3776_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_3777_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3748_, v___x_3753_);
v___x_3778_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3776_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
v___x_3779_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3779_, 0, v___x_3778_);
lean_ctor_set_uint8(v___x_3779_, sizeof(void*)*1, v___x_3756_);
v___x_3780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3775_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
v___x_3781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3780_);
lean_ctor_set(v___x_3781_, 1, v___x_3759_);
v___x_3782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3781_);
lean_ctor_set(v___x_3782_, 1, v___x_3761_);
v___x_3783_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_3784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3782_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
v___x_3785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3784_);
lean_ctor_set(v___x_3785_, 1, v___x_3750_);
v___x_3786_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_3787_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_3749_, v___x_3753_);
v___x_3788_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3786_);
lean_ctor_set(v___x_3788_, 1, v___x_3787_);
v___x_3789_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3789_, 0, v___x_3788_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*1, v___x_3756_);
v___x_3790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3785_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
v___x_3791_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_3792_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_3793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3792_);
lean_ctor_set(v___x_3793_, 1, v___x_3790_);
v___x_3794_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_3795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3793_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v___x_3796_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3791_);
lean_ctor_set(v___x_3796_, 1, v___x_3795_);
v___x_3797_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
lean_ctor_set_uint8(v___x_3797_, sizeof(void*)*1, v___x_3756_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr(lean_object* v_x_3798_, lean_object* v_prec_3799_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_x_3798_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___boxed(lean_object* v_x_3801_, lean_object* v_prec_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_Std_Http_URI_instReprRelativeRef_repr(v_x_3801_, v_prec_3802_);
lean_dec(v_prec_3802_);
return v_res_3803_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqRelativeRef_beq(lean_object* v_x_3811_, lean_object* v_x_3812_){
_start:
{
lean_object* v_authority_3813_; lean_object* v_path_3814_; lean_object* v_query_3815_; lean_object* v_fragment_3816_; lean_object* v_authority_3817_; lean_object* v_path_3818_; lean_object* v_query_3819_; lean_object* v_fragment_3820_; uint8_t v___x_3821_; 
v_authority_3813_ = lean_ctor_get(v_x_3811_, 0);
v_path_3814_ = lean_ctor_get(v_x_3811_, 1);
v_query_3815_ = lean_ctor_get(v_x_3811_, 2);
v_fragment_3816_ = lean_ctor_get(v_x_3811_, 3);
v_authority_3817_ = lean_ctor_get(v_x_3812_, 0);
v_path_3818_ = lean_ctor_get(v_x_3812_, 1);
v_query_3819_ = lean_ctor_get(v_x_3812_, 2);
v_fragment_3820_ = lean_ctor_get(v_x_3812_, 3);
v___x_3821_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_3813_, v_authority_3817_);
if (v___x_3821_ == 0)
{
return v___x_3821_;
}
else
{
uint8_t v___x_3822_; 
v___x_3822_ = l_Std_Http_URI_instBEqPath_beq(v_path_3814_, v_path_3818_);
if (v___x_3822_ == 0)
{
return v___x_3822_;
}
else
{
uint8_t v___x_3823_; 
v___x_3823_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_3815_, v_query_3819_);
if (v___x_3823_ == 0)
{
return v___x_3823_;
}
else
{
uint8_t v___x_3824_; 
v___x_3824_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_3816_, v_fragment_3820_);
return v___x_3824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqRelativeRef_beq___boxed(lean_object* v_x_3825_, lean_object* v_x_3826_){
_start:
{
uint8_t v_res_3827_; lean_object* v_r_3828_; 
v_res_3827_ = l_Std_Http_URI_instBEqRelativeRef_beq(v_x_3825_, v_x_3826_);
lean_dec_ref(v_x_3826_);
lean_dec_ref(v_x_3825_);
v_r_3828_ = lean_box(v_res_3827_);
return v_r_3828_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringRelativeRef___lam__0(lean_object* v_ref_3831_){
_start:
{
lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v_authority_3840_; lean_object* v_path_3841_; lean_object* v_query_3842_; lean_object* v_fragment_3843_; lean_object* v___y_3845_; uint8_t v___y_3846_; lean_object* v___y_3857_; 
v_authority_3840_ = lean_ctor_get(v_ref_3831_, 0);
lean_inc(v_authority_3840_);
v_path_3841_ = lean_ctor_get(v_ref_3831_, 1);
lean_inc_ref(v_path_3841_);
v_query_3842_ = lean_ctor_get(v_ref_3831_, 2);
lean_inc(v_query_3842_);
v_fragment_3843_ = lean_ctor_get(v_ref_3831_, 3);
lean_inc(v_fragment_3843_);
lean_dec_ref(v_ref_3831_);
if (lean_obj_tag(v_authority_3840_) == 0)
{
lean_object* v___x_3860_; 
v___x_3860_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3857_ = v___x_3860_;
goto v___jp_3856_;
}
else
{
lean_object* v_val_3861_; lean_object* v_userInfo_3862_; lean_object* v_host_3863_; lean_object* v_port_3864_; lean_object* v___x_3865_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3884_; 
v_val_3861_ = lean_ctor_get(v_authority_3840_, 0);
v_userInfo_3862_ = lean_ctor_get(v_val_3861_, 0);
v_host_3863_ = lean_ctor_get(v_val_3861_, 1);
v_port_3864_ = lean_ctor_get(v_val_3861_, 2);
v___x_3865_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__1));
if (lean_obj_tag(v_userInfo_3862_) == 0)
{
lean_object* v___x_3894_; 
v___x_3894_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3884_ = v___x_3894_;
goto v___jp_3883_;
}
else
{
lean_object* v_val_3895_; lean_object* v_password_3896_; 
v_val_3895_ = lean_ctor_get(v_userInfo_3862_, 0);
v_password_3896_ = lean_ctor_get(v_val_3895_, 1);
if (lean_obj_tag(v_password_3896_) == 0)
{
lean_object* v_username_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v_username_3897_ = lean_ctor_get(v_val_3895_, 0);
lean_inc_ref(v_username_3897_);
v___x_3898_ = lean_string_from_utf8_unchecked(v_username_3897_);
v___x_3899_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3900_ = lean_string_append(v___x_3898_, v___x_3899_);
v___y_3884_ = v___x_3900_;
goto v___jp_3883_;
}
else
{
lean_object* v_username_3901_; lean_object* v_val_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v_username_3901_ = lean_ctor_get(v_val_3895_, 0);
v_val_3902_ = lean_ctor_get(v_password_3896_, 0);
lean_inc_ref(v_username_3901_);
v___x_3903_ = lean_string_from_utf8_unchecked(v_username_3901_);
v___x_3904_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3905_ = lean_string_append(v___x_3903_, v___x_3904_);
lean_inc(v_val_3902_);
v___x_3906_ = lean_string_from_utf8_unchecked(v_val_3902_);
v___x_3907_ = lean_string_append(v___x_3905_, v___x_3906_);
lean_dec_ref(v___x_3906_);
v___x_3908_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3909_ = lean_string_append(v___x_3907_, v___x_3908_);
v___y_3884_ = v___x_3909_;
goto v___jp_3883_;
}
}
v___jp_3866_:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3870_ = lean_string_append(v___y_3867_, v___y_3868_);
lean_dec_ref(v___y_3868_);
v___x_3871_ = lean_string_append(v___x_3870_, v___y_3869_);
lean_dec_ref(v___y_3869_);
v___x_3872_ = lean_string_append(v___x_3865_, v___x_3871_);
lean_dec_ref(v___x_3871_);
v___y_3857_ = v___x_3872_;
goto v___jp_3856_;
}
v___jp_3873_:
{
switch(lean_obj_tag(v_port_3864_))
{
case 0:
{
lean_object* v___x_3876_; 
v___x_3876_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3867_ = v___y_3874_;
v___y_3868_ = v___y_3875_;
v___y_3869_ = v___x_3876_;
goto v___jp_3866_;
}
case 1:
{
lean_object* v___x_3877_; 
v___x_3877_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3867_ = v___y_3874_;
v___y_3868_ = v___y_3875_;
v___y_3869_ = v___x_3877_;
goto v___jp_3866_;
}
default: 
{
uint16_t v_port_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v_port_3878_ = lean_ctor_get_uint16(v_port_3864_, 0);
v___x_3879_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3880_ = lean_uint16_to_nat(v_port_3878_);
v___x_3881_ = l_Nat_reprFast(v___x_3880_);
v___x_3882_ = lean_string_append(v___x_3879_, v___x_3881_);
lean_dec_ref(v___x_3881_);
v___y_3867_ = v___y_3874_;
v___y_3868_ = v___y_3875_;
v___y_3869_ = v___x_3882_;
goto v___jp_3866_;
}
}
}
v___jp_3883_:
{
switch(lean_obj_tag(v_host_3863_))
{
case 0:
{
lean_object* v_name_3885_; 
v_name_3885_ = lean_ctor_get(v_host_3863_, 0);
lean_inc_ref(v_name_3885_);
v___y_3874_ = v___y_3884_;
v___y_3875_ = v_name_3885_;
goto v___jp_3873_;
}
case 1:
{
lean_object* v_ipv4_3886_; lean_object* v___x_3887_; 
v_ipv4_3886_ = lean_ctor_get(v_host_3863_, 0);
v___x_3887_ = lean_uv_ntop_v4(v_ipv4_3886_);
v___y_3874_ = v___y_3884_;
v___y_3875_ = v___x_3887_;
goto v___jp_3873_;
}
default: 
{
lean_object* v_ipv6_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
v_ipv6_3888_ = lean_ctor_get(v_host_3863_, 0);
v___x_3889_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3890_ = lean_uv_ntop_v6(v_ipv6_3888_);
v___x_3891_ = lean_string_append(v___x_3889_, v___x_3890_);
lean_dec_ref(v___x_3890_);
v___x_3892_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3893_ = lean_string_append(v___x_3891_, v___x_3892_);
v___y_3874_ = v___y_3884_;
v___y_3875_ = v___x_3893_;
goto v___jp_3873_;
}
}
}
}
v___jp_3832_:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3837_ = lean_string_append(v___y_3835_, v___y_3834_);
lean_dec_ref(v___y_3834_);
v___x_3838_ = lean_string_append(v___x_3837_, v___y_3833_);
lean_dec_ref(v___y_3833_);
v___x_3839_ = lean_string_append(v___x_3838_, v___y_3836_);
lean_dec_ref(v___y_3836_);
return v___x_3839_;
}
v___jp_3844_:
{
uint8_t v___x_3847_; lean_object* v_pathPart_3848_; lean_object* v_queryPart_3849_; 
v___x_3847_ = 0;
v_pathPart_3848_ = l_Std_Http_URI_Path_render(v_path_3841_, v___y_3846_, v___x_3847_);
v_queryPart_3849_ = l_Std_Http_URI_Query_formatOption(v_query_3842_);
if (lean_obj_tag(v_fragment_3843_) == 0)
{
lean_object* v___x_3850_; 
v___x_3850_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3833_ = v_queryPart_3849_;
v___y_3834_ = v_pathPart_3848_;
v___y_3835_ = v___y_3845_;
v___y_3836_ = v___x_3850_;
goto v___jp_3832_;
}
else
{
lean_object* v_val_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v_val_3851_ = lean_ctor_get(v_fragment_3843_, 0);
lean_inc(v_val_3851_);
lean_dec_ref_known(v_fragment_3843_, 1);
v___x_3852_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__0));
v___x_3853_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3851_);
v___x_3854_ = lean_string_from_utf8_unchecked(v___x_3853_);
v___x_3855_ = lean_string_append(v___x_3852_, v___x_3854_);
lean_dec_ref(v___x_3854_);
v___y_3833_ = v_queryPart_3849_;
v___y_3834_ = v_pathPart_3848_;
v___y_3835_ = v___y_3845_;
v___y_3836_ = v___x_3855_;
goto v___jp_3832_;
}
}
v___jp_3856_:
{
if (lean_obj_tag(v_authority_3840_) == 0)
{
uint8_t v___x_3858_; 
v___x_3858_ = 0;
v___y_3845_ = v___y_3857_;
v___y_3846_ = v___x_3858_;
goto v___jp_3844_;
}
else
{
uint8_t v___x_3859_; 
lean_dec_ref_known(v_authority_3840_, 1);
v___x_3859_ = 1;
v___y_3845_ = v___y_3857_;
v___y_3846_ = v___x_3859_;
goto v___jp_3844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___impl(lean_object* v_x_3912_){
_start:
{
lean_object* v___x_3913_; 
v___x_3913_ = lean_obj_tag_nat(v_x_3912_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___impl___boxed(lean_object* v_x_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Std_Http_URIReference_ctorIdx___impl(v_x_3914_);
lean_dec_ref(v_x_3914_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___redArg(lean_object* v_t_3916_, lean_object* v_k_3917_){
_start:
{
lean_object* v_uri_3918_; lean_object* v___x_3919_; 
v_uri_3918_ = lean_ctor_get(v_t_3916_, 0);
lean_inc_ref(v_uri_3918_);
lean_dec_ref(v_t_3916_);
v___x_3919_ = lean_apply_1(v_k_3917_, v_uri_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim(lean_object* v_motive_3920_, lean_object* v_ctorIdx_3921_, lean_object* v_t_3922_, lean_object* v_h_3923_, lean_object* v_k_3924_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3922_, v_k_3924_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___boxed(lean_object* v_motive_3926_, lean_object* v_ctorIdx_3927_, lean_object* v_t_3928_, lean_object* v_h_3929_, lean_object* v_k_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l_Std_Http_URIReference_ctorElim(v_motive_3926_, v_ctorIdx_3927_, v_t_3928_, v_h_3929_, v_k_3930_);
lean_dec(v_ctorIdx_3927_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim___redArg(lean_object* v_t_3932_, lean_object* v_absolute_3933_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3932_, v_absolute_3933_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim(lean_object* v_motive_3935_, lean_object* v_t_3936_, lean_object* v_h_3937_, lean_object* v_absolute_3938_){
_start:
{
lean_object* v___x_3939_; 
v___x_3939_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3936_, v_absolute_3938_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim___redArg(lean_object* v_t_3940_, lean_object* v_relative_3941_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3940_, v_relative_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim(lean_object* v_motive_3943_, lean_object* v_t_3944_, lean_object* v_h_3945_, lean_object* v_relative_3946_){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3944_, v_relative_3946_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr(lean_object* v_x_3960_, lean_object* v_prec_3961_){
_start:
{
if (lean_obj_tag(v_x_3960_) == 0)
{
lean_object* v_uri_3962_; lean_object* v___y_3964_; lean_object* v___x_3972_; uint8_t v___x_3973_; 
v_uri_3962_ = lean_ctor_get(v_x_3960_, 0);
lean_inc_ref(v_uri_3962_);
lean_dec_ref_known(v_x_3960_, 1);
v___x_3972_ = lean_unsigned_to_nat(1024u);
v___x_3973_ = lean_nat_dec_le(v___x_3972_, v_prec_3961_);
if (v___x_3973_ == 0)
{
lean_object* v___x_3974_; 
v___x_3974_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3964_ = v___x_3974_;
goto v___jp_3963_;
}
else
{
lean_object* v___x_3975_; 
v___x_3975_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3964_ = v___x_3975_;
goto v___jp_3963_;
}
v___jp_3963_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; uint8_t v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3965_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__2));
v___x_3966_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3962_);
v___x_3967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3965_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
lean_inc(v___y_3964_);
v___x_3968_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3968_, 0, v___y_3964_);
lean_ctor_set(v___x_3968_, 1, v___x_3967_);
v___x_3969_ = 0;
v___x_3970_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3970_, 0, v___x_3968_);
lean_ctor_set_uint8(v___x_3970_, sizeof(void*)*1, v___x_3969_);
v___x_3971_ = l_Repr_addAppParen(v___x_3970_, v_prec_3961_);
return v___x_3971_;
}
}
else
{
lean_object* v_ref_3976_; lean_object* v___y_3978_; lean_object* v___x_3986_; uint8_t v___x_3987_; 
v_ref_3976_ = lean_ctor_get(v_x_3960_, 0);
lean_inc_ref(v_ref_3976_);
lean_dec_ref_known(v_x_3960_, 1);
v___x_3986_ = lean_unsigned_to_nat(1024u);
v___x_3987_ = lean_nat_dec_le(v___x_3986_, v_prec_3961_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3988_; 
v___x_3988_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3978_ = v___x_3988_;
goto v___jp_3977_;
}
else
{
lean_object* v___x_3989_; 
v___x_3989_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3978_ = v___x_3989_;
goto v___jp_3977_;
}
v___jp_3977_:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3979_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__5));
v___x_3980_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_ref_3976_);
v___x_3981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3979_);
lean_ctor_set(v___x_3981_, 1, v___x_3980_);
lean_inc(v___y_3978_);
v___x_3982_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___y_3978_);
lean_ctor_set(v___x_3982_, 1, v___x_3981_);
v___x_3983_ = 0;
v___x_3984_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3984_, 0, v___x_3982_);
lean_ctor_set_uint8(v___x_3984_, sizeof(void*)*1, v___x_3983_);
v___x_3985_ = l_Repr_addAppParen(v___x_3984_, v_prec_3961_);
return v___x_3985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr___boxed(lean_object* v_x_3990_, lean_object* v_prec_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_Std_Http_instReprURIReference_repr(v_x_3990_, v_prec_3991_);
lean_dec(v_prec_3991_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURIReference___lam__0(lean_object* v_x_3999_){
_start:
{
lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; 
if (lean_obj_tag(v_x_3999_) == 0)
{
lean_object* v_uri_4008_; lean_object* v_scheme_4009_; lean_object* v_authority_4010_; lean_object* v_path_4011_; lean_object* v_query_4012_; lean_object* v_fragment_4013_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4026_; uint8_t v___y_4027_; lean_object* v___y_4038_; 
v_uri_4008_ = lean_ctor_get(v_x_3999_, 0);
lean_inc_ref(v_uri_4008_);
lean_dec_ref_known(v_x_3999_, 1);
v_scheme_4009_ = lean_ctor_get(v_uri_4008_, 0);
lean_inc_ref(v_scheme_4009_);
v_authority_4010_ = lean_ctor_get(v_uri_4008_, 1);
lean_inc(v_authority_4010_);
v_path_4011_ = lean_ctor_get(v_uri_4008_, 2);
lean_inc_ref(v_path_4011_);
v_query_4012_ = lean_ctor_get(v_uri_4008_, 3);
lean_inc(v_query_4012_);
v_fragment_4013_ = lean_ctor_get(v_uri_4008_, 4);
lean_inc(v_fragment_4013_);
lean_dec_ref(v_uri_4008_);
if (lean_obj_tag(v_authority_4010_) == 0)
{
lean_object* v___x_4041_; 
v___x_4041_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4038_ = v___x_4041_;
goto v___jp_4037_;
}
else
{
lean_object* v_val_4042_; lean_object* v_userInfo_4043_; lean_object* v_host_4044_; lean_object* v_port_4045_; lean_object* v___x_4046_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4065_; 
v_val_4042_ = lean_ctor_get(v_authority_4010_, 0);
v_userInfo_4043_ = lean_ctor_get(v_val_4042_, 0);
v_host_4044_ = lean_ctor_get(v_val_4042_, 1);
v_port_4045_ = lean_ctor_get(v_val_4042_, 2);
v___x_4046_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__1));
if (lean_obj_tag(v_userInfo_4043_) == 0)
{
lean_object* v___x_4075_; 
v___x_4075_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4065_ = v___x_4075_;
goto v___jp_4064_;
}
else
{
lean_object* v_val_4076_; lean_object* v_password_4077_; 
v_val_4076_ = lean_ctor_get(v_userInfo_4043_, 0);
v_password_4077_ = lean_ctor_get(v_val_4076_, 1);
if (lean_obj_tag(v_password_4077_) == 0)
{
lean_object* v_username_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v_username_4078_ = lean_ctor_get(v_val_4076_, 0);
lean_inc_ref(v_username_4078_);
v___x_4079_ = lean_string_from_utf8_unchecked(v_username_4078_);
v___x_4080_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4081_ = lean_string_append(v___x_4079_, v___x_4080_);
v___y_4065_ = v___x_4081_;
goto v___jp_4064_;
}
else
{
lean_object* v_username_4082_; lean_object* v_val_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v_username_4082_ = lean_ctor_get(v_val_4076_, 0);
v_val_4083_ = lean_ctor_get(v_password_4077_, 0);
lean_inc_ref(v_username_4082_);
v___x_4084_ = lean_string_from_utf8_unchecked(v_username_4082_);
v___x_4085_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4086_ = lean_string_append(v___x_4084_, v___x_4085_);
lean_inc(v_val_4083_);
v___x_4087_ = lean_string_from_utf8_unchecked(v_val_4083_);
v___x_4088_ = lean_string_append(v___x_4086_, v___x_4087_);
lean_dec_ref(v___x_4087_);
v___x_4089_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4090_ = lean_string_append(v___x_4088_, v___x_4089_);
v___y_4065_ = v___x_4090_;
goto v___jp_4064_;
}
}
v___jp_4047_:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4051_ = lean_string_append(v___y_4048_, v___y_4049_);
lean_dec_ref(v___y_4049_);
v___x_4052_ = lean_string_append(v___x_4051_, v___y_4050_);
lean_dec_ref(v___y_4050_);
v___x_4053_ = lean_string_append(v___x_4046_, v___x_4052_);
lean_dec_ref(v___x_4052_);
v___y_4038_ = v___x_4053_;
goto v___jp_4037_;
}
v___jp_4054_:
{
switch(lean_obj_tag(v_port_4045_))
{
case 0:
{
lean_object* v___x_4057_; 
v___x_4057_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4048_ = v___y_4055_;
v___y_4049_ = v___y_4056_;
v___y_4050_ = v___x_4057_;
goto v___jp_4047_;
}
case 1:
{
lean_object* v___x_4058_; 
v___x_4058_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_4048_ = v___y_4055_;
v___y_4049_ = v___y_4056_;
v___y_4050_ = v___x_4058_;
goto v___jp_4047_;
}
default: 
{
uint16_t v_port_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v_port_4059_ = lean_ctor_get_uint16(v_port_4045_, 0);
v___x_4060_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4061_ = lean_uint16_to_nat(v_port_4059_);
v___x_4062_ = l_Nat_reprFast(v___x_4061_);
v___x_4063_ = lean_string_append(v___x_4060_, v___x_4062_);
lean_dec_ref(v___x_4062_);
v___y_4048_ = v___y_4055_;
v___y_4049_ = v___y_4056_;
v___y_4050_ = v___x_4063_;
goto v___jp_4047_;
}
}
}
v___jp_4064_:
{
switch(lean_obj_tag(v_host_4044_))
{
case 0:
{
lean_object* v_name_4066_; 
v_name_4066_ = lean_ctor_get(v_host_4044_, 0);
lean_inc_ref(v_name_4066_);
v___y_4055_ = v___y_4065_;
v___y_4056_ = v_name_4066_;
goto v___jp_4054_;
}
case 1:
{
lean_object* v_ipv4_4067_; lean_object* v___x_4068_; 
v_ipv4_4067_ = lean_ctor_get(v_host_4044_, 0);
v___x_4068_ = lean_uv_ntop_v4(v_ipv4_4067_);
v___y_4055_ = v___y_4065_;
v___y_4056_ = v___x_4068_;
goto v___jp_4054_;
}
default: 
{
lean_object* v_ipv6_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v_ipv6_4069_ = lean_ctor_get(v_host_4044_, 0);
v___x_4070_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4071_ = lean_uv_ntop_v6(v_ipv6_4069_);
v___x_4072_ = lean_string_append(v___x_4070_, v___x_4071_);
lean_dec_ref(v___x_4071_);
v___x_4073_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4074_ = lean_string_append(v___x_4072_, v___x_4073_);
v___y_4055_ = v___y_4065_;
v___y_4056_ = v___x_4074_;
goto v___jp_4054_;
}
}
}
}
v___jp_4014_:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4019_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4020_ = lean_string_append(v_scheme_4009_, v___x_4019_);
v___x_4021_ = lean_string_append(v___x_4020_, v___y_4015_);
lean_dec_ref(v___y_4015_);
v___x_4022_ = lean_string_append(v___x_4021_, v___y_4017_);
lean_dec_ref(v___y_4017_);
v___x_4023_ = lean_string_append(v___x_4022_, v___y_4016_);
lean_dec_ref(v___y_4016_);
v___x_4024_ = lean_string_append(v___x_4023_, v___y_4018_);
lean_dec_ref(v___y_4018_);
return v___x_4024_;
}
v___jp_4025_:
{
uint8_t v___x_4028_; lean_object* v_pathPart_4029_; lean_object* v_queryPart_4030_; 
v___x_4028_ = 1;
v_pathPart_4029_ = l_Std_Http_URI_Path_render(v_path_4011_, v___y_4027_, v___x_4028_);
v_queryPart_4030_ = l_Std_Http_URI_Query_formatOption(v_query_4012_);
if (lean_obj_tag(v_fragment_4013_) == 0)
{
lean_object* v___x_4031_; 
v___x_4031_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4015_ = v___y_4026_;
v___y_4016_ = v_queryPart_4030_;
v___y_4017_ = v_pathPart_4029_;
v___y_4018_ = v___x_4031_;
goto v___jp_4014_;
}
else
{
lean_object* v_val_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v_val_4032_ = lean_ctor_get(v_fragment_4013_, 0);
lean_inc(v_val_4032_);
lean_dec_ref_known(v_fragment_4013_, 1);
v___x_4033_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__0));
v___x_4034_ = l_Std_Http_URI_EncodedFragment_encode(v_val_4032_);
v___x_4035_ = lean_string_from_utf8_unchecked(v___x_4034_);
v___x_4036_ = lean_string_append(v___x_4033_, v___x_4035_);
lean_dec_ref(v___x_4035_);
v___y_4015_ = v___y_4026_;
v___y_4016_ = v_queryPart_4030_;
v___y_4017_ = v_pathPart_4029_;
v___y_4018_ = v___x_4036_;
goto v___jp_4014_;
}
}
v___jp_4037_:
{
if (lean_obj_tag(v_authority_4010_) == 0)
{
uint8_t v___x_4039_; 
v___x_4039_ = 0;
v___y_4026_ = v___y_4038_;
v___y_4027_ = v___x_4039_;
goto v___jp_4025_;
}
else
{
uint8_t v___x_4040_; 
lean_dec_ref_known(v_authority_4010_, 1);
v___x_4040_ = 1;
v___y_4026_ = v___y_4038_;
v___y_4027_ = v___x_4040_;
goto v___jp_4025_;
}
}
}
else
{
lean_object* v_ref_4091_; lean_object* v_authority_4092_; lean_object* v_path_4093_; lean_object* v_query_4094_; lean_object* v_fragment_4095_; lean_object* v___y_4097_; uint8_t v___y_4098_; lean_object* v___y_4109_; 
v_ref_4091_ = lean_ctor_get(v_x_3999_, 0);
lean_inc_ref(v_ref_4091_);
lean_dec_ref_known(v_x_3999_, 1);
v_authority_4092_ = lean_ctor_get(v_ref_4091_, 0);
lean_inc(v_authority_4092_);
v_path_4093_ = lean_ctor_get(v_ref_4091_, 1);
lean_inc_ref(v_path_4093_);
v_query_4094_ = lean_ctor_get(v_ref_4091_, 2);
lean_inc(v_query_4094_);
v_fragment_4095_ = lean_ctor_get(v_ref_4091_, 3);
lean_inc(v_fragment_4095_);
lean_dec_ref(v_ref_4091_);
if (lean_obj_tag(v_authority_4092_) == 0)
{
lean_object* v___x_4112_; 
v___x_4112_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4109_ = v___x_4112_;
goto v___jp_4108_;
}
else
{
lean_object* v_val_4113_; lean_object* v_userInfo_4114_; lean_object* v_host_4115_; lean_object* v_port_4116_; lean_object* v___x_4117_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4136_; 
v_val_4113_ = lean_ctor_get(v_authority_4092_, 0);
v_userInfo_4114_ = lean_ctor_get(v_val_4113_, 0);
v_host_4115_ = lean_ctor_get(v_val_4113_, 1);
v_port_4116_ = lean_ctor_get(v_val_4113_, 2);
v___x_4117_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__1));
if (lean_obj_tag(v_userInfo_4114_) == 0)
{
lean_object* v___x_4146_; 
v___x_4146_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4136_ = v___x_4146_;
goto v___jp_4135_;
}
else
{
lean_object* v_val_4147_; lean_object* v_password_4148_; 
v_val_4147_ = lean_ctor_get(v_userInfo_4114_, 0);
v_password_4148_ = lean_ctor_get(v_val_4147_, 1);
if (lean_obj_tag(v_password_4148_) == 0)
{
lean_object* v_username_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v_username_4149_ = lean_ctor_get(v_val_4147_, 0);
lean_inc_ref(v_username_4149_);
v___x_4150_ = lean_string_from_utf8_unchecked(v_username_4149_);
v___x_4151_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4152_ = lean_string_append(v___x_4150_, v___x_4151_);
v___y_4136_ = v___x_4152_;
goto v___jp_4135_;
}
else
{
lean_object* v_username_4153_; lean_object* v_val_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v_username_4153_ = lean_ctor_get(v_val_4147_, 0);
v_val_4154_ = lean_ctor_get(v_password_4148_, 0);
lean_inc_ref(v_username_4153_);
v___x_4155_ = lean_string_from_utf8_unchecked(v_username_4153_);
v___x_4156_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4157_ = lean_string_append(v___x_4155_, v___x_4156_);
lean_inc(v_val_4154_);
v___x_4158_ = lean_string_from_utf8_unchecked(v_val_4154_);
v___x_4159_ = lean_string_append(v___x_4157_, v___x_4158_);
lean_dec_ref(v___x_4158_);
v___x_4160_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4161_ = lean_string_append(v___x_4159_, v___x_4160_);
v___y_4136_ = v___x_4161_;
goto v___jp_4135_;
}
}
v___jp_4118_:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4122_ = lean_string_append(v___y_4119_, v___y_4120_);
lean_dec_ref(v___y_4120_);
v___x_4123_ = lean_string_append(v___x_4122_, v___y_4121_);
lean_dec_ref(v___y_4121_);
v___x_4124_ = lean_string_append(v___x_4117_, v___x_4123_);
lean_dec_ref(v___x_4123_);
v___y_4109_ = v___x_4124_;
goto v___jp_4108_;
}
v___jp_4125_:
{
switch(lean_obj_tag(v_port_4116_))
{
case 0:
{
lean_object* v___x_4128_; 
v___x_4128_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4119_ = v___y_4126_;
v___y_4120_ = v___y_4127_;
v___y_4121_ = v___x_4128_;
goto v___jp_4118_;
}
case 1:
{
lean_object* v___x_4129_; 
v___x_4129_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_4119_ = v___y_4126_;
v___y_4120_ = v___y_4127_;
v___y_4121_ = v___x_4129_;
goto v___jp_4118_;
}
default: 
{
uint16_t v_port_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v_port_4130_ = lean_ctor_get_uint16(v_port_4116_, 0);
v___x_4131_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4132_ = lean_uint16_to_nat(v_port_4130_);
v___x_4133_ = l_Nat_reprFast(v___x_4132_);
v___x_4134_ = lean_string_append(v___x_4131_, v___x_4133_);
lean_dec_ref(v___x_4133_);
v___y_4119_ = v___y_4126_;
v___y_4120_ = v___y_4127_;
v___y_4121_ = v___x_4134_;
goto v___jp_4118_;
}
}
}
v___jp_4135_:
{
switch(lean_obj_tag(v_host_4115_))
{
case 0:
{
lean_object* v_name_4137_; 
v_name_4137_ = lean_ctor_get(v_host_4115_, 0);
lean_inc_ref(v_name_4137_);
v___y_4126_ = v___y_4136_;
v___y_4127_ = v_name_4137_;
goto v___jp_4125_;
}
case 1:
{
lean_object* v_ipv4_4138_; lean_object* v___x_4139_; 
v_ipv4_4138_ = lean_ctor_get(v_host_4115_, 0);
v___x_4139_ = lean_uv_ntop_v4(v_ipv4_4138_);
v___y_4126_ = v___y_4136_;
v___y_4127_ = v___x_4139_;
goto v___jp_4125_;
}
default: 
{
lean_object* v_ipv6_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v_ipv6_4140_ = lean_ctor_get(v_host_4115_, 0);
v___x_4141_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4142_ = lean_uv_ntop_v6(v_ipv6_4140_);
v___x_4143_ = lean_string_append(v___x_4141_, v___x_4142_);
lean_dec_ref(v___x_4142_);
v___x_4144_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4145_ = lean_string_append(v___x_4143_, v___x_4144_);
v___y_4126_ = v___y_4136_;
v___y_4127_ = v___x_4145_;
goto v___jp_4125_;
}
}
}
}
v___jp_4096_:
{
uint8_t v___x_4099_; lean_object* v_pathPart_4100_; lean_object* v_queryPart_4101_; 
v___x_4099_ = 0;
v_pathPart_4100_ = l_Std_Http_URI_Path_render(v_path_4093_, v___y_4098_, v___x_4099_);
v_queryPart_4101_ = l_Std_Http_URI_Query_formatOption(v_query_4094_);
if (lean_obj_tag(v_fragment_4095_) == 0)
{
lean_object* v___x_4102_; 
v___x_4102_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4001_ = v_pathPart_4100_;
v___y_4002_ = v___y_4097_;
v___y_4003_ = v_queryPart_4101_;
v___y_4004_ = v___x_4102_;
goto v___jp_4000_;
}
else
{
lean_object* v_val_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
v_val_4103_ = lean_ctor_get(v_fragment_4095_, 0);
lean_inc(v_val_4103_);
lean_dec_ref_known(v_fragment_4095_, 1);
v___x_4104_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__0));
v___x_4105_ = l_Std_Http_URI_EncodedFragment_encode(v_val_4103_);
v___x_4106_ = lean_string_from_utf8_unchecked(v___x_4105_);
v___x_4107_ = lean_string_append(v___x_4104_, v___x_4106_);
lean_dec_ref(v___x_4106_);
v___y_4001_ = v_pathPart_4100_;
v___y_4002_ = v___y_4097_;
v___y_4003_ = v_queryPart_4101_;
v___y_4004_ = v___x_4107_;
goto v___jp_4000_;
}
}
v___jp_4108_:
{
if (lean_obj_tag(v_authority_4092_) == 0)
{
uint8_t v___x_4110_; 
v___x_4110_ = 0;
v___y_4097_ = v___y_4109_;
v___y_4098_ = v___x_4110_;
goto v___jp_4096_;
}
else
{
uint8_t v___x_4111_; 
lean_dec_ref_known(v_authority_4092_, 1);
v___x_4111_ = 1;
v___y_4097_ = v___y_4109_;
v___y_4098_ = v___x_4111_;
goto v___jp_4096_;
}
}
}
v___jp_4000_:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4005_ = lean_string_append(v___y_4002_, v___y_4001_);
lean_dec_ref(v___y_4001_);
v___x_4006_ = lean_string_append(v___x_4005_, v___y_4003_);
lean_dec_ref(v___y_4003_);
v___x_4007_ = lean_string_append(v___x_4006_, v___y_4004_);
lean_dec_ref(v___y_4004_);
return v___x_4007_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___impl(lean_object* v_x_4164_){
_start:
{
lean_object* v___x_4165_; 
v___x_4165_ = lean_obj_tag_nat(v_x_4164_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___impl___boxed(lean_object* v_x_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l_Std_Http_RequestTarget_ctorIdx___impl(v_x_4166_);
lean_dec(v_x_4166_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___redArg(lean_object* v_t_4168_, lean_object* v_k_4169_){
_start:
{
switch(lean_obj_tag(v_t_4168_))
{
case 0:
{
lean_object* v_path_4170_; lean_object* v_query_4171_; lean_object* v___x_4172_; 
v_path_4170_ = lean_ctor_get(v_t_4168_, 0);
lean_inc_ref(v_path_4170_);
v_query_4171_ = lean_ctor_get(v_t_4168_, 1);
lean_inc(v_query_4171_);
lean_dec_ref_known(v_t_4168_, 2);
v___x_4172_ = lean_apply_2(v_k_4169_, v_path_4170_, v_query_4171_);
return v___x_4172_;
}
case 3:
{
return v_k_4169_;
}
default: 
{
lean_object* v_uri_4173_; lean_object* v___x_4174_; 
v_uri_4173_ = lean_ctor_get(v_t_4168_, 0);
lean_inc_ref(v_uri_4173_);
lean_dec(v_t_4168_);
v___x_4174_ = lean_apply_1(v_k_4169_, v_uri_4173_);
return v___x_4174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim(lean_object* v_motive_4175_, lean_object* v_ctorIdx_4176_, lean_object* v_t_4177_, lean_object* v_h_4178_, lean_object* v_k_4179_){
_start:
{
lean_object* v___x_4180_; 
v___x_4180_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4177_, v_k_4179_);
return v___x_4180_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___boxed(lean_object* v_motive_4181_, lean_object* v_ctorIdx_4182_, lean_object* v_t_4183_, lean_object* v_h_4184_, lean_object* v_k_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Std_Http_RequestTarget_ctorElim(v_motive_4181_, v_ctorIdx_4182_, v_t_4183_, v_h_4184_, v_k_4185_);
lean_dec(v_ctorIdx_4182_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim___redArg(lean_object* v_t_4187_, lean_object* v_originForm_4188_){
_start:
{
lean_object* v___x_4189_; 
v___x_4189_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4187_, v_originForm_4188_);
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim(lean_object* v_motive_4190_, lean_object* v_t_4191_, lean_object* v_h_4192_, lean_object* v_originForm_4193_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4191_, v_originForm_4193_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim___redArg(lean_object* v_t_4195_, lean_object* v_absoluteForm_4196_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4195_, v_absoluteForm_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim(lean_object* v_motive_4198_, lean_object* v_t_4199_, lean_object* v_h_4200_, lean_object* v_absoluteForm_4201_){
_start:
{
lean_object* v___x_4202_; 
v___x_4202_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4199_, v_absoluteForm_4201_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim___redArg(lean_object* v_t_4203_, lean_object* v_authorityForm_4204_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4203_, v_authorityForm_4204_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim(lean_object* v_motive_4206_, lean_object* v_t_4207_, lean_object* v_h_4208_, lean_object* v_authorityForm_4209_){
_start:
{
lean_object* v___x_4210_; 
v___x_4210_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4207_, v_authorityForm_4209_);
return v___x_4210_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim___redArg(lean_object* v_t_4211_, lean_object* v_asteriskForm_4212_){
_start:
{
lean_object* v___x_4213_; 
v___x_4213_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4211_, v_asteriskForm_4212_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim(lean_object* v_motive_4214_, lean_object* v_t_4215_, lean_object* v_h_4216_, lean_object* v_asteriskForm_4217_){
_start:
{
lean_object* v___x_4218_; 
v___x_4218_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_4215_, v_asteriskForm_4217_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object* v_x_4245_, lean_object* v_prec_4246_){
_start:
{
lean_object* v___y_4248_; 
switch(lean_obj_tag(v_x_4245_))
{
case 0:
{
lean_object* v_path_4254_; lean_object* v_query_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4279_; 
v_path_4254_ = lean_ctor_get(v_x_4245_, 0);
v_query_4255_ = lean_ctor_get(v_x_4245_, 1);
v_isSharedCheck_4279_ = !lean_is_exclusive(v_x_4245_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4257_ = v_x_4245_;
v_isShared_4258_ = v_isSharedCheck_4279_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_query_4255_);
lean_inc(v_path_4254_);
lean_dec(v_x_4245_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4279_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___y_4260_; lean_object* v___x_4275_; uint8_t v___x_4276_; 
v___x_4275_ = lean_unsigned_to_nat(1024u);
v___x_4276_ = lean_nat_dec_le(v___x_4275_, v_prec_4246_);
if (v___x_4276_ == 0)
{
lean_object* v___x_4277_; 
v___x_4277_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_4260_ = v___x_4277_;
goto v___jp_4259_;
}
else
{
lean_object* v___x_4278_; 
v___x_4278_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_4260_ = v___x_4278_;
goto v___jp_4259_;
}
v___jp_4259_:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4266_; 
v___x_4261_ = lean_box(1);
v___x_4262_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__4));
v___x_4263_ = lean_unsigned_to_nat(1024u);
v___x_4264_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_4254_);
if (v_isShared_4258_ == 0)
{
lean_ctor_set_tag(v___x_4257_, 5);
lean_ctor_set(v___x_4257_, 1, v___x_4264_);
lean_ctor_set(v___x_4257_, 0, v___x_4262_);
v___x_4266_ = v___x_4257_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4262_);
lean_ctor_set(v_reuseFailAlloc_4274_, 1, v___x_4264_);
v___x_4266_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; uint8_t v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4266_);
lean_ctor_set(v___x_4267_, 1, v___x_4261_);
v___x_4268_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_4255_, v___x_4263_);
v___x_4269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4267_);
lean_ctor_set(v___x_4269_, 1, v___x_4268_);
lean_inc(v___y_4260_);
v___x_4270_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4270_, 0, v___y_4260_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
v___x_4271_ = 0;
v___x_4272_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4272_, 0, v___x_4270_);
lean_ctor_set_uint8(v___x_4272_, sizeof(void*)*1, v___x_4271_);
v___x_4273_ = l_Repr_addAppParen(v___x_4272_, v_prec_4246_);
return v___x_4273_;
}
}
}
}
case 1:
{
lean_object* v_uri_4280_; lean_object* v___y_4282_; lean_object* v___x_4290_; uint8_t v___x_4291_; 
v_uri_4280_ = lean_ctor_get(v_x_4245_, 0);
lean_inc_ref(v_uri_4280_);
lean_dec_ref_known(v_x_4245_, 1);
v___x_4290_ = lean_unsigned_to_nat(1024u);
v___x_4291_ = lean_nat_dec_le(v___x_4290_, v_prec_4246_);
if (v___x_4291_ == 0)
{
lean_object* v___x_4292_; 
v___x_4292_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_4282_ = v___x_4292_;
goto v___jp_4281_;
}
else
{
lean_object* v___x_4293_; 
v___x_4293_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_4282_ = v___x_4293_;
goto v___jp_4281_;
}
v___jp_4281_:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; uint8_t v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4283_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__7));
v___x_4284_ = l_Std_Http_instReprURI_repr___redArg(v_uri_4280_);
v___x_4285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4285_, 0, v___x_4283_);
lean_ctor_set(v___x_4285_, 1, v___x_4284_);
lean_inc(v___y_4282_);
v___x_4286_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4286_, 0, v___y_4282_);
lean_ctor_set(v___x_4286_, 1, v___x_4285_);
v___x_4287_ = 0;
v___x_4288_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4288_, 0, v___x_4286_);
lean_ctor_set_uint8(v___x_4288_, sizeof(void*)*1, v___x_4287_);
v___x_4289_ = l_Repr_addAppParen(v___x_4288_, v_prec_4246_);
return v___x_4289_;
}
}
case 2:
{
lean_object* v_authority_4294_; lean_object* v___y_4296_; lean_object* v___x_4304_; uint8_t v___x_4305_; 
v_authority_4294_ = lean_ctor_get(v_x_4245_, 0);
lean_inc_ref(v_authority_4294_);
lean_dec_ref_known(v_x_4245_, 1);
v___x_4304_ = lean_unsigned_to_nat(1024u);
v___x_4305_ = lean_nat_dec_le(v___x_4304_, v_prec_4246_);
if (v___x_4305_ == 0)
{
lean_object* v___x_4306_; 
v___x_4306_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_4296_ = v___x_4306_;
goto v___jp_4295_;
}
else
{
lean_object* v___x_4307_; 
v___x_4307_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_4296_ = v___x_4307_;
goto v___jp_4295_;
}
v___jp_4295_:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; uint8_t v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; 
v___x_4297_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__10));
v___x_4298_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_authority_4294_);
v___x_4299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4297_);
lean_ctor_set(v___x_4299_, 1, v___x_4298_);
lean_inc(v___y_4296_);
v___x_4300_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4300_, 0, v___y_4296_);
lean_ctor_set(v___x_4300_, 1, v___x_4299_);
v___x_4301_ = 0;
v___x_4302_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4302_, 0, v___x_4300_);
lean_ctor_set_uint8(v___x_4302_, sizeof(void*)*1, v___x_4301_);
v___x_4303_ = l_Repr_addAppParen(v___x_4302_, v_prec_4246_);
return v___x_4303_;
}
}
default: 
{
lean_object* v___x_4308_; uint8_t v___x_4309_; 
v___x_4308_ = lean_unsigned_to_nat(1024u);
v___x_4309_ = lean_nat_dec_le(v___x_4308_, v_prec_4246_);
if (v___x_4309_ == 0)
{
lean_object* v___x_4310_; 
v___x_4310_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_4248_ = v___x_4310_;
goto v___jp_4247_;
}
else
{
lean_object* v___x_4311_; 
v___x_4311_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_4248_ = v___x_4311_;
goto v___jp_4247_;
}
}
}
v___jp_4247_:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; uint8_t v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4249_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__1));
lean_inc(v___y_4248_);
v___x_4250_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4250_, 0, v___y_4248_);
lean_ctor_set(v___x_4250_, 1, v___x_4249_);
v___x_4251_ = 0;
v___x_4252_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4252_, 0, v___x_4250_);
lean_ctor_set_uint8(v___x_4252_, sizeof(void*)*1, v___x_4251_);
v___x_4253_ = l_Repr_addAppParen(v___x_4252_, v_prec_4246_);
return v___x_4253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr___boxed(lean_object* v_x_4312_, lean_object* v_prec_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l_Std_Http_instReprRequestTarget_repr(v_x_4312_, v_prec_4313_);
lean_dec(v_prec_4313_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path(lean_object* v_x_4320_){
_start:
{
switch(lean_obj_tag(v_x_4320_))
{
case 0:
{
lean_object* v_path_4321_; 
v_path_4321_ = lean_ctor_get(v_x_4320_, 0);
lean_inc_ref(v_path_4321_);
return v_path_4321_;
}
case 1:
{
lean_object* v_uri_4322_; lean_object* v_path_4323_; 
v_uri_4322_ = lean_ctor_get(v_x_4320_, 0);
v_path_4323_ = lean_ctor_get(v_uri_4322_, 2);
lean_inc_ref(v_path_4323_);
return v_path_4323_;
}
default: 
{
lean_object* v___x_4324_; 
v___x_4324_ = ((lean_object*)(l_Std_Http_RequestTarget_path___closed__0));
return v___x_4324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path___boxed(lean_object* v_x_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l_Std_Http_RequestTarget_path(v_x_4325_);
lean_dec(v_x_4325_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query(lean_object* v_x_4327_){
_start:
{
switch(lean_obj_tag(v_x_4327_))
{
case 0:
{
lean_object* v_query_4328_; 
v_query_4328_ = lean_ctor_get(v_x_4327_, 1);
if (lean_obj_tag(v_query_4328_) == 0)
{
lean_object* v___x_4329_; 
v___x_4329_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_4329_;
}
else
{
lean_object* v_val_4330_; 
v_val_4330_ = lean_ctor_get(v_query_4328_, 0);
lean_inc(v_val_4330_);
return v_val_4330_;
}
}
case 1:
{
lean_object* v_uri_4331_; lean_object* v_query_4332_; 
v_uri_4331_ = lean_ctor_get(v_x_4327_, 0);
v_query_4332_ = lean_ctor_get(v_uri_4331_, 3);
if (lean_obj_tag(v_query_4332_) == 0)
{
lean_object* v___x_4333_; 
v___x_4333_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_4333_;
}
else
{
lean_object* v_val_4334_; 
v_val_4334_ = lean_ctor_get(v_query_4332_, 0);
lean_inc(v_val_4334_);
return v_val_4334_;
}
}
default: 
{
lean_object* v___x_4335_; 
v___x_4335_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_4335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query___boxed(lean_object* v_x_4336_){
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = l_Std_Http_RequestTarget_query(v_x_4336_);
lean_dec(v_x_4336_);
return v_res_4337_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authority_x3f(lean_object* v_x_4338_){
_start:
{
switch(lean_obj_tag(v_x_4338_))
{
case 2:
{
lean_object* v_authority_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
v_authority_4339_ = lean_ctor_get(v_x_4338_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v_x_4338_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v_x_4338_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_authority_4339_);
lean_dec(v_x_4338_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
lean_ctor_set_tag(v___x_4341_, 1);
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_authority_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
case 1:
{
lean_object* v_uri_4347_; lean_object* v_authority_4348_; 
v_uri_4347_ = lean_ctor_get(v_x_4338_, 0);
lean_inc_ref(v_uri_4347_);
lean_dec_ref_known(v_x_4338_, 1);
v_authority_4348_ = lean_ctor_get(v_uri_4347_, 1);
lean_inc(v_authority_4348_);
lean_dec_ref(v_uri_4347_);
return v_authority_4348_;
}
default: 
{
lean_object* v___x_4349_; 
lean_dec(v_x_4338_);
v___x_4349_ = lean_box(0);
return v___x_4349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__0(lean_object* v_x_4351_){
_start:
{
switch(lean_obj_tag(v_x_4351_))
{
case 0:
{
lean_object* v_path_4352_; lean_object* v_query_4353_; lean_object* v___y_4355_; uint8_t v___x_4358_; lean_object* v_pathStr_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; uint8_t v___x_4362_; 
v_path_4352_ = lean_ctor_get(v_x_4351_, 0);
lean_inc_ref(v_path_4352_);
v_query_4353_ = lean_ctor_get(v_x_4351_, 1);
lean_inc(v_query_4353_);
lean_dec_ref_known(v_x_4351_, 2);
v___x_4358_ = 1;
v_pathStr_4359_ = l_Std_Http_URI_Path_render(v_path_4352_, v___x_4358_, v___x_4358_);
v___x_4360_ = lean_string_utf8_byte_size(v_pathStr_4359_);
v___x_4361_ = lean_unsigned_to_nat(0u);
v___x_4362_ = lean_nat_dec_eq(v___x_4360_, v___x_4361_);
if (v___x_4362_ == 0)
{
v___y_4355_ = v_pathStr_4359_;
goto v___jp_4354_;
}
else
{
lean_object* v___x_4363_; 
lean_dec_ref(v_pathStr_4359_);
v___x_4363_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___y_4355_ = v___x_4363_;
goto v___jp_4354_;
}
v___jp_4354_:
{
lean_object* v_queryStr_4356_; lean_object* v___x_4357_; 
v_queryStr_4356_ = l_Std_Http_URI_Query_formatOption(v_query_4353_);
v___x_4357_ = lean_string_append(v___y_4355_, v_queryStr_4356_);
lean_dec_ref(v_queryStr_4356_);
return v___x_4357_;
}
}
case 1:
{
lean_object* v_uri_4364_; lean_object* v_scheme_4365_; lean_object* v_authority_4366_; lean_object* v_path_4367_; lean_object* v_query_4368_; lean_object* v___y_4370_; uint8_t v___y_4371_; lean_object* v___y_4381_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v_port_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; 
v_uri_4364_ = lean_ctor_get(v_x_4351_, 0);
lean_inc_ref(v_uri_4364_);
lean_dec_ref_known(v_x_4351_, 1);
v_scheme_4365_ = lean_ctor_get(v_uri_4364_, 0);
lean_inc_ref(v_scheme_4365_);
v_authority_4366_ = lean_ctor_get(v_uri_4364_, 1);
lean_inc(v_authority_4366_);
v_path_4367_ = lean_ctor_get(v_uri_4364_, 2);
lean_inc_ref(v_path_4367_);
v_query_4368_ = lean_ctor_get(v_uri_4364_, 3);
lean_inc(v_query_4368_);
lean_dec_ref(v_uri_4364_);
if (lean_obj_tag(v_authority_4366_) == 0)
{
lean_object* v___x_4406_; 
v___x_4406_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4381_ = v___x_4406_;
goto v___jp_4380_;
}
else
{
lean_object* v_val_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4436_; 
v_val_4407_ = lean_ctor_get(v_authority_4366_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v_authority_4366_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4409_ = v_authority_4366_;
v_isShared_4410_ = v_isSharedCheck_4436_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_val_4407_);
lean_dec(v_authority_4366_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4436_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v_host_4411_; lean_object* v_port_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4434_; 
v_host_4411_ = lean_ctor_get(v_val_4407_, 1);
v_port_4412_ = lean_ctor_get(v_val_4407_, 2);
v_isSharedCheck_4434_ = !lean_is_exclusive(v_val_4407_);
if (v_isSharedCheck_4434_ == 0)
{
lean_object* v_unused_4435_; 
v_unused_4435_ = lean_ctor_get(v_val_4407_, 0);
lean_dec(v_unused_4435_);
v___x_4414_ = v_val_4407_;
v_isShared_4415_ = v_isSharedCheck_4434_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_port_4412_);
lean_inc(v_host_4411_);
lean_dec(v_val_4407_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4434_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4416_; lean_object* v___x_4418_; 
v___x_4416_ = lean_box(0);
lean_inc(v_port_4412_);
lean_inc_ref(v_host_4411_);
if (v_isShared_4415_ == 0)
{
lean_ctor_set(v___x_4414_, 0, v___x_4416_);
v___x_4418_ = v___x_4414_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v___x_4416_);
lean_ctor_set(v_reuseFailAlloc_4433_, 1, v_host_4411_);
lean_ctor_set(v_reuseFailAlloc_4433_, 2, v_port_4412_);
v___x_4418_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
lean_object* v___x_4420_; 
if (v_isShared_4410_ == 0)
{
lean_ctor_set(v___x_4409_, 0, v___x_4418_);
v___x_4420_ = v___x_4409_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4418_);
v___x_4420_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4421_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__1));
v___x_4422_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
switch(lean_obj_tag(v_host_4411_))
{
case 0:
{
lean_object* v_name_4423_; 
v_name_4423_ = lean_ctor_get(v_host_4411_, 0);
lean_inc_ref(v_name_4423_);
lean_dec_ref_known(v_host_4411_, 1);
v___y_4394_ = v___x_4422_;
v___y_4395_ = v___x_4420_;
v_port_4396_ = v_port_4412_;
v___y_4397_ = v___x_4421_;
v___y_4398_ = v_name_4423_;
goto v___jp_4393_;
}
case 1:
{
lean_object* v_ipv4_4424_; lean_object* v___x_4425_; 
v_ipv4_4424_ = lean_ctor_get(v_host_4411_, 0);
lean_inc_ref(v_ipv4_4424_);
lean_dec_ref_known(v_host_4411_, 1);
v___x_4425_ = lean_uv_ntop_v4(v_ipv4_4424_);
lean_dec_ref(v_ipv4_4424_);
v___y_4394_ = v___x_4422_;
v___y_4395_ = v___x_4420_;
v_port_4396_ = v_port_4412_;
v___y_4397_ = v___x_4421_;
v___y_4398_ = v___x_4425_;
goto v___jp_4393_;
}
default: 
{
lean_object* v_ipv6_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v_ipv6_4426_ = lean_ctor_get(v_host_4411_, 0);
lean_inc_ref(v_ipv6_4426_);
lean_dec_ref_known(v_host_4411_, 1);
v___x_4427_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4428_ = lean_uv_ntop_v6(v_ipv6_4426_);
lean_dec_ref(v_ipv6_4426_);
v___x_4429_ = lean_string_append(v___x_4427_, v___x_4428_);
lean_dec_ref(v___x_4428_);
v___x_4430_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4431_ = lean_string_append(v___x_4429_, v___x_4430_);
v___y_4394_ = v___x_4422_;
v___y_4395_ = v___x_4420_;
v_port_4396_ = v_port_4412_;
v___y_4397_ = v___x_4421_;
v___y_4398_ = v___x_4431_;
goto v___jp_4393_;
}
}
}
}
}
}
}
v___jp_4369_:
{
uint8_t v___x_4372_; lean_object* v_pathPart_4373_; lean_object* v_queryPart_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4372_ = 1;
v_pathPart_4373_ = l_Std_Http_URI_Path_render(v_path_4367_, v___y_4371_, v___x_4372_);
v_queryPart_4374_ = l_Std_Http_URI_Query_formatOption(v_query_4368_);
v___x_4375_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4376_ = lean_string_append(v_scheme_4365_, v___x_4375_);
v___x_4377_ = lean_string_append(v___x_4376_, v___y_4370_);
lean_dec_ref(v___y_4370_);
v___x_4378_ = lean_string_append(v___x_4377_, v_pathPart_4373_);
lean_dec_ref(v_pathPart_4373_);
v___x_4379_ = lean_string_append(v___x_4378_, v_queryPart_4374_);
lean_dec_ref(v_queryPart_4374_);
return v___x_4379_;
}
v___jp_4380_:
{
uint8_t v___x_4382_; 
v___x_4382_ = 0;
lean_inc_ref(v___y_4381_);
v___y_4370_ = v___y_4381_;
v___y_4371_ = v___x_4382_;
goto v___jp_4369_;
}
v___jp_4383_:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; uint8_t v___x_4392_; 
lean_dec(v___y_4386_);
lean_inc_ref(v___y_4384_);
v___x_4389_ = lean_string_append(v___y_4384_, v___y_4385_);
lean_dec_ref(v___y_4385_);
v___x_4390_ = lean_string_append(v___x_4389_, v___y_4388_);
lean_dec_ref(v___y_4388_);
lean_inc_ref(v___y_4387_);
v___x_4391_ = lean_string_append(v___y_4387_, v___x_4390_);
lean_dec_ref(v___x_4390_);
v___x_4392_ = 1;
v___y_4370_ = v___x_4391_;
v___y_4371_ = v___x_4392_;
goto v___jp_4369_;
}
v___jp_4393_:
{
switch(lean_obj_tag(v_port_4396_))
{
case 0:
{
lean_object* v___x_4399_; 
v___x_4399_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4384_ = v___y_4394_;
v___y_4385_ = v___y_4398_;
v___y_4386_ = v___y_4395_;
v___y_4387_ = v___y_4397_;
v___y_4388_ = v___x_4399_;
goto v___jp_4383_;
}
case 1:
{
lean_object* v___x_4400_; 
v___x_4400_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_4384_ = v___y_4394_;
v___y_4385_ = v___y_4398_;
v___y_4386_ = v___y_4395_;
v___y_4387_ = v___y_4397_;
v___y_4388_ = v___x_4400_;
goto v___jp_4383_;
}
default: 
{
uint16_t v_port_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v_port_4401_ = lean_ctor_get_uint16(v_port_4396_, 0);
lean_dec_ref_known(v_port_4396_, 0);
v___x_4402_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4403_ = lean_uint16_to_nat(v_port_4401_);
v___x_4404_ = l_Nat_reprFast(v___x_4403_);
v___x_4405_ = lean_string_append(v___x_4402_, v___x_4404_);
lean_dec_ref(v___x_4404_);
v___y_4384_ = v___y_4394_;
v___y_4385_ = v___y_4398_;
v___y_4386_ = v___y_4395_;
v___y_4387_ = v___y_4397_;
v___y_4388_ = v___x_4405_;
goto v___jp_4383_;
}
}
}
}
case 2:
{
lean_object* v_authority_4437_; lean_object* v_host_4438_; lean_object* v_port_4439_; lean_object* v___y_4441_; 
v_authority_4437_ = lean_ctor_get(v_x_4351_, 0);
lean_inc_ref(v_authority_4437_);
lean_dec_ref_known(v_x_4351_, 1);
v_host_4438_ = lean_ctor_get(v_authority_4437_, 1);
lean_inc_ref(v_host_4438_);
v_port_4439_ = lean_ctor_get(v_authority_4437_, 2);
lean_inc(v_port_4439_);
lean_dec_ref(v_authority_4437_);
switch(lean_obj_tag(v_host_4438_))
{
case 0:
{
lean_object* v_name_4450_; 
v_name_4450_ = lean_ctor_get(v_host_4438_, 0);
lean_inc_ref(v_name_4450_);
lean_dec_ref_known(v_host_4438_, 1);
v___y_4441_ = v_name_4450_;
goto v___jp_4440_;
}
case 1:
{
lean_object* v_ipv4_4451_; lean_object* v___x_4452_; 
v_ipv4_4451_ = lean_ctor_get(v_host_4438_, 0);
lean_inc_ref(v_ipv4_4451_);
lean_dec_ref_known(v_host_4438_, 1);
v___x_4452_ = lean_uv_ntop_v4(v_ipv4_4451_);
lean_dec_ref(v_ipv4_4451_);
v___y_4441_ = v___x_4452_;
goto v___jp_4440_;
}
default: 
{
lean_object* v_ipv6_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
v_ipv6_4453_ = lean_ctor_get(v_host_4438_, 0);
lean_inc_ref(v_ipv6_4453_);
lean_dec_ref_known(v_host_4438_, 1);
v___x_4454_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4455_ = lean_uv_ntop_v6(v_ipv6_4453_);
lean_dec_ref(v_ipv6_4453_);
v___x_4456_ = lean_string_append(v___x_4454_, v___x_4455_);
lean_dec_ref(v___x_4455_);
v___x_4457_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4458_ = lean_string_append(v___x_4456_, v___x_4457_);
v___y_4441_ = v___x_4458_;
goto v___jp_4440_;
}
}
v___jp_4440_:
{
switch(lean_obj_tag(v_port_4439_))
{
case 0:
{
return v___y_4441_;
}
case 1:
{
lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4442_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4443_ = lean_string_append(v___y_4441_, v___x_4442_);
return v___x_4443_;
}
default: 
{
uint16_t v_port_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v_port_4444_ = lean_ctor_get_uint16(v_port_4439_, 0);
lean_dec_ref_known(v_port_4439_, 0);
v___x_4445_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4446_ = lean_uint16_to_nat(v_port_4444_);
v___x_4447_ = l_Nat_reprFast(v___x_4446_);
v___x_4448_ = lean_string_append(v___x_4445_, v___x_4447_);
lean_dec_ref(v___x_4447_);
v___x_4449_ = lean_string_append(v___y_4441_, v___x_4448_);
lean_dec_ref(v___x_4448_);
return v___x_4449_;
}
}
}
}
default: 
{
lean_object* v___x_4459_; 
v___x_4459_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__0___closed__0));
return v___x_4459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__0(lean_object* v_out_4462_, lean_object* v_target_4463_){
_start:
{
lean_object* v___y_4465_; 
switch(lean_obj_tag(v_target_4463_))
{
case 0:
{
lean_object* v_path_4472_; lean_object* v_query_4473_; lean_object* v___y_4475_; uint8_t v___x_4478_; lean_object* v_pathStr_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; uint8_t v___x_4482_; 
v_path_4472_ = lean_ctor_get(v_target_4463_, 0);
lean_inc_ref(v_path_4472_);
v_query_4473_ = lean_ctor_get(v_target_4463_, 1);
lean_inc(v_query_4473_);
lean_dec_ref_known(v_target_4463_, 2);
v___x_4478_ = 1;
v_pathStr_4479_ = l_Std_Http_URI_Path_render(v_path_4472_, v___x_4478_, v___x_4478_);
v___x_4480_ = lean_string_utf8_byte_size(v_pathStr_4479_);
v___x_4481_ = lean_unsigned_to_nat(0u);
v___x_4482_ = lean_nat_dec_eq(v___x_4480_, v___x_4481_);
if (v___x_4482_ == 0)
{
v___y_4475_ = v_pathStr_4479_;
goto v___jp_4474_;
}
else
{
lean_object* v___x_4483_; 
lean_dec_ref(v_pathStr_4479_);
v___x_4483_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___y_4475_ = v___x_4483_;
goto v___jp_4474_;
}
v___jp_4474_:
{
lean_object* v_queryStr_4476_; lean_object* v___x_4477_; 
v_queryStr_4476_ = l_Std_Http_URI_Query_formatOption(v_query_4473_);
v___x_4477_ = lean_string_append(v___y_4475_, v_queryStr_4476_);
lean_dec_ref(v_queryStr_4476_);
v___y_4465_ = v___x_4477_;
goto v___jp_4464_;
}
}
case 1:
{
lean_object* v_uri_4484_; lean_object* v_scheme_4485_; lean_object* v_authority_4486_; lean_object* v_path_4487_; lean_object* v_query_4488_; lean_object* v___y_4490_; uint8_t v___y_4491_; lean_object* v___y_4501_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v_port_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; 
v_uri_4484_ = lean_ctor_get(v_target_4463_, 0);
lean_inc_ref(v_uri_4484_);
lean_dec_ref_known(v_target_4463_, 1);
v_scheme_4485_ = lean_ctor_get(v_uri_4484_, 0);
lean_inc_ref(v_scheme_4485_);
v_authority_4486_ = lean_ctor_get(v_uri_4484_, 1);
lean_inc(v_authority_4486_);
v_path_4487_ = lean_ctor_get(v_uri_4484_, 2);
lean_inc_ref(v_path_4487_);
v_query_4488_ = lean_ctor_get(v_uri_4484_, 3);
lean_inc(v_query_4488_);
lean_dec_ref(v_uri_4484_);
if (lean_obj_tag(v_authority_4486_) == 0)
{
lean_object* v___x_4526_; 
v___x_4526_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4501_ = v___x_4526_;
goto v___jp_4500_;
}
else
{
lean_object* v_val_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4556_; 
v_val_4527_ = lean_ctor_get(v_authority_4486_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v_authority_4486_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4529_ = v_authority_4486_;
v_isShared_4530_ = v_isSharedCheck_4556_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_val_4527_);
lean_dec(v_authority_4486_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4556_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v_host_4531_; lean_object* v_port_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4554_; 
v_host_4531_ = lean_ctor_get(v_val_4527_, 1);
v_port_4532_ = lean_ctor_get(v_val_4527_, 2);
v_isSharedCheck_4554_ = !lean_is_exclusive(v_val_4527_);
if (v_isSharedCheck_4554_ == 0)
{
lean_object* v_unused_4555_; 
v_unused_4555_ = lean_ctor_get(v_val_4527_, 0);
lean_dec(v_unused_4555_);
v___x_4534_ = v_val_4527_;
v_isShared_4535_ = v_isSharedCheck_4554_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_port_4532_);
lean_inc(v_host_4531_);
lean_dec(v_val_4527_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4554_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v___x_4536_; lean_object* v___x_4538_; 
v___x_4536_ = lean_box(0);
lean_inc(v_port_4532_);
lean_inc_ref(v_host_4531_);
if (v_isShared_4535_ == 0)
{
lean_ctor_set(v___x_4534_, 0, v___x_4536_);
v___x_4538_ = v___x_4534_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4536_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v_host_4531_);
lean_ctor_set(v_reuseFailAlloc_4553_, 2, v_port_4532_);
v___x_4538_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
lean_object* v___x_4540_; 
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 0, v___x_4538_);
v___x_4540_ = v___x_4529_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v___x_4538_);
v___x_4540_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__0___closed__1));
v___x_4542_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
switch(lean_obj_tag(v_host_4531_))
{
case 0:
{
lean_object* v_name_4543_; 
v_name_4543_ = lean_ctor_get(v_host_4531_, 0);
lean_inc_ref(v_name_4543_);
lean_dec_ref_known(v_host_4531_, 1);
v_port_4514_ = v_port_4532_;
v___y_4515_ = v___x_4541_;
v___y_4516_ = v___x_4540_;
v___y_4517_ = v___x_4542_;
v___y_4518_ = v_name_4543_;
goto v___jp_4513_;
}
case 1:
{
lean_object* v_ipv4_4544_; lean_object* v___x_4545_; 
v_ipv4_4544_ = lean_ctor_get(v_host_4531_, 0);
lean_inc_ref(v_ipv4_4544_);
lean_dec_ref_known(v_host_4531_, 1);
v___x_4545_ = lean_uv_ntop_v4(v_ipv4_4544_);
lean_dec_ref(v_ipv4_4544_);
v_port_4514_ = v_port_4532_;
v___y_4515_ = v___x_4541_;
v___y_4516_ = v___x_4540_;
v___y_4517_ = v___x_4542_;
v___y_4518_ = v___x_4545_;
goto v___jp_4513_;
}
default: 
{
lean_object* v_ipv6_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; 
v_ipv6_4546_ = lean_ctor_get(v_host_4531_, 0);
lean_inc_ref(v_ipv6_4546_);
lean_dec_ref_known(v_host_4531_, 1);
v___x_4547_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4548_ = lean_uv_ntop_v6(v_ipv6_4546_);
lean_dec_ref(v_ipv6_4546_);
v___x_4549_ = lean_string_append(v___x_4547_, v___x_4548_);
lean_dec_ref(v___x_4548_);
v___x_4550_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4551_ = lean_string_append(v___x_4549_, v___x_4550_);
v_port_4514_ = v_port_4532_;
v___y_4515_ = v___x_4541_;
v___y_4516_ = v___x_4540_;
v___y_4517_ = v___x_4542_;
v___y_4518_ = v___x_4551_;
goto v___jp_4513_;
}
}
}
}
}
}
}
v___jp_4489_:
{
uint8_t v___x_4492_; lean_object* v_pathPart_4493_; lean_object* v_queryPart_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4492_ = 1;
v_pathPart_4493_ = l_Std_Http_URI_Path_render(v_path_4487_, v___y_4491_, v___x_4492_);
v_queryPart_4494_ = l_Std_Http_URI_Query_formatOption(v_query_4488_);
v___x_4495_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4496_ = lean_string_append(v_scheme_4485_, v___x_4495_);
v___x_4497_ = lean_string_append(v___x_4496_, v___y_4490_);
lean_dec_ref(v___y_4490_);
v___x_4498_ = lean_string_append(v___x_4497_, v_pathPart_4493_);
lean_dec_ref(v_pathPart_4493_);
v___x_4499_ = lean_string_append(v___x_4498_, v_queryPart_4494_);
lean_dec_ref(v_queryPart_4494_);
v___y_4465_ = v___x_4499_;
goto v___jp_4464_;
}
v___jp_4500_:
{
uint8_t v___x_4502_; 
v___x_4502_ = 0;
lean_inc_ref(v___y_4501_);
v___y_4490_ = v___y_4501_;
v___y_4491_ = v___x_4502_;
goto v___jp_4489_;
}
v___jp_4503_:
{
lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; uint8_t v___x_4512_; 
lean_dec(v___y_4505_);
lean_inc_ref(v___y_4507_);
v___x_4509_ = lean_string_append(v___y_4507_, v___y_4504_);
lean_dec_ref(v___y_4504_);
v___x_4510_ = lean_string_append(v___x_4509_, v___y_4508_);
lean_dec_ref(v___y_4508_);
lean_inc_ref(v___y_4506_);
v___x_4511_ = lean_string_append(v___y_4506_, v___x_4510_);
lean_dec_ref(v___x_4510_);
v___x_4512_ = 1;
v___y_4490_ = v___x_4511_;
v___y_4491_ = v___x_4512_;
goto v___jp_4489_;
}
v___jp_4513_:
{
switch(lean_obj_tag(v_port_4514_))
{
case 0:
{
lean_object* v___x_4519_; 
v___x_4519_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4504_ = v___y_4518_;
v___y_4505_ = v___y_4516_;
v___y_4506_ = v___y_4515_;
v___y_4507_ = v___y_4517_;
v___y_4508_ = v___x_4519_;
goto v___jp_4503_;
}
case 1:
{
lean_object* v___x_4520_; 
v___x_4520_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_4504_ = v___y_4518_;
v___y_4505_ = v___y_4516_;
v___y_4506_ = v___y_4515_;
v___y_4507_ = v___y_4517_;
v___y_4508_ = v___x_4520_;
goto v___jp_4503_;
}
default: 
{
uint16_t v_port_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
v_port_4521_ = lean_ctor_get_uint16(v_port_4514_, 0);
lean_dec_ref_known(v_port_4514_, 0);
v___x_4522_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4523_ = lean_uint16_to_nat(v_port_4521_);
v___x_4524_ = l_Nat_reprFast(v___x_4523_);
v___x_4525_ = lean_string_append(v___x_4522_, v___x_4524_);
lean_dec_ref(v___x_4524_);
v___y_4504_ = v___y_4518_;
v___y_4505_ = v___y_4516_;
v___y_4506_ = v___y_4515_;
v___y_4507_ = v___y_4517_;
v___y_4508_ = v___x_4525_;
goto v___jp_4503_;
}
}
}
}
case 2:
{
lean_object* v_authority_4557_; lean_object* v_host_4558_; lean_object* v_port_4559_; lean_object* v___y_4561_; 
v_authority_4557_ = lean_ctor_get(v_target_4463_, 0);
lean_inc_ref(v_authority_4557_);
lean_dec_ref_known(v_target_4463_, 1);
v_host_4558_ = lean_ctor_get(v_authority_4557_, 1);
lean_inc_ref(v_host_4558_);
v_port_4559_ = lean_ctor_get(v_authority_4557_, 2);
lean_inc(v_port_4559_);
lean_dec_ref(v_authority_4557_);
switch(lean_obj_tag(v_host_4558_))
{
case 0:
{
lean_object* v_name_4570_; 
v_name_4570_ = lean_ctor_get(v_host_4558_, 0);
lean_inc_ref(v_name_4570_);
lean_dec_ref_known(v_host_4558_, 1);
v___y_4561_ = v_name_4570_;
goto v___jp_4560_;
}
case 1:
{
lean_object* v_ipv4_4571_; lean_object* v___x_4572_; 
v_ipv4_4571_ = lean_ctor_get(v_host_4558_, 0);
lean_inc_ref(v_ipv4_4571_);
lean_dec_ref_known(v_host_4558_, 1);
v___x_4572_ = lean_uv_ntop_v4(v_ipv4_4571_);
lean_dec_ref(v_ipv4_4571_);
v___y_4561_ = v___x_4572_;
goto v___jp_4560_;
}
default: 
{
lean_object* v_ipv6_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
v_ipv6_4573_ = lean_ctor_get(v_host_4558_, 0);
lean_inc_ref(v_ipv6_4573_);
lean_dec_ref_known(v_host_4558_, 1);
v___x_4574_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4575_ = lean_uv_ntop_v6(v_ipv6_4573_);
lean_dec_ref(v_ipv6_4573_);
v___x_4576_ = lean_string_append(v___x_4574_, v___x_4575_);
lean_dec_ref(v___x_4575_);
v___x_4577_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4578_ = lean_string_append(v___x_4576_, v___x_4577_);
v___y_4561_ = v___x_4578_;
goto v___jp_4560_;
}
}
v___jp_4560_:
{
switch(lean_obj_tag(v_port_4559_))
{
case 0:
{
v___y_4465_ = v___y_4561_;
goto v___jp_4464_;
}
case 1:
{
lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4562_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4563_ = lean_string_append(v___y_4561_, v___x_4562_);
v___y_4465_ = v___x_4563_;
goto v___jp_4464_;
}
default: 
{
uint16_t v_port_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v_port_4564_ = lean_ctor_get_uint16(v_port_4559_, 0);
lean_dec_ref_known(v_port_4559_, 0);
v___x_4565_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4566_ = lean_uint16_to_nat(v_port_4564_);
v___x_4567_ = l_Nat_reprFast(v___x_4566_);
v___x_4568_ = lean_string_append(v___x_4565_, v___x_4567_);
lean_dec_ref(v___x_4567_);
v___x_4569_ = lean_string_append(v___y_4561_, v___x_4568_);
lean_dec_ref(v___x_4568_);
v___y_4465_ = v___x_4569_;
goto v___jp_4464_;
}
}
}
}
default: 
{
lean_object* v___x_4579_; 
v___x_4579_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__0___closed__0));
v___y_4465_ = v___x_4579_;
goto v___jp_4464_;
}
}
v___jp_4464_:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; uint8_t v___x_4470_; lean_object* v___x_4471_; 
v___x_4466_ = lean_string_to_utf8(v___y_4465_);
v___x_4467_ = lean_unsigned_to_nat(0u);
v___x_4468_ = lean_byte_array_size(v_out_4462_);
v___x_4469_ = lean_byte_array_size(v___x_4466_);
v___x_4470_ = 0;
v___x_4471_ = lean_byte_array_copy_slice(v___x_4466_, v___x_4467_, v_out_4462_, v___x_4468_, v___x_4469_, v___x_4470_);
lean_dec_ref(v___x_4466_);
return v___x_4471_;
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
