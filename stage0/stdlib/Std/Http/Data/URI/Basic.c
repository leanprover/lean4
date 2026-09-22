// Lean compiler output
// Module: Std.Http.Data.URI.Basic
// Imports: import Init.Data.ToString public import Std.Net public import Std.Http.Internal public import Std.Http.Data.URI.Encoding public import Init.Data.String.Search public import Init.Data.String.Length
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
uint8_t lean_sarray_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t l_Std_Http_Internal_instDecidableIsLowerCase(lean_object*);
lean_object* lean_string_data(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Std_Net_instDecidableEqIPv4Addr_decEq(lean_object*, lean_object*);
uint8_t l_Std_Net_instDecidableEqIPv6Addr_decEq(lean_object*, lean_object*);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* lean_array_mk(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_ByteArray_empty;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Std_Http_URI_EncodedSegment_encode(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_Http_URI_EncodedQueryParam_encode(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_List_getLast_x3f___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object*);
extern lean_object* l_Std_Net_instInhabitedIPv4Addr_default;
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_URI_EncodedString_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Option_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_EncodedUserInfo_decode(lean_object*);
lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object*);
lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object*);
lean_object* l_ByteArray_decEq___boxed(lean_object*, lean_object*);
lean_object* l_List_eraseDupsBy___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqUserInfo_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqUserInfo_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instBEqUserInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instBEqUserInfo_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instBEqUserInfo___closed__0 = (const lean_object*)&l_Std_Http_URI_instBEqUserInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instBEqUserInfo = (const lean_object*)&l_Std_Http_URI_instBEqUserInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidDomainLabel___boxed(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_DomainName_ofString_x3f(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parent(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_appendEncoded(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0_value;
static const lean_string_object l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".."};
static const lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1_value;
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_instBEqQuery___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instBEqQuery___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instBEqQuery___closed__0 = (const lean_object*)&l_Std_Http_URI_instBEqQuery___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instBEqQuery = (const lean_object*)&l_Std_Http_URI_instBEqQuery___closed__0_value;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_values(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray___boxed(lean_object*);
static const lean_string_object l_Std_Http_URI_Query_formatQueryParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l_Std_Http_URI_Query_formatQueryParam___closed__0 = (const lean_object*)&l_Std_Http_URI_Query_formatQueryParam___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Http_URI_Query_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_URI_Query_empty___closed__0 = (const lean_object*)&l_Std_Http_URI_Query_empty___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_Query_empty = (const lean_object*)&l_Std_Http_URI_Query_empty___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_ofList(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_containsEncoded(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_containsEncoded___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_Query_instSingletonProdString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_Query_instSingletonProdString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_Query_instSingletonProdString___closed__0 = (const lean_object*)&l_Std_Http_URI_Query_instSingletonProdString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_Query_instSingletonProdString = (const lean_object*)&l_Std_Http_URI_Query_instSingletonProdString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_Query_instInsertProdString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_Query_instInsertProdString___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instBEqURI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instBEqURI_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instBEqURI___closed__0 = (const lean_object*)&l_Std_Http_instBEqURI___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instBEqURI = (const lean_object*)&l_Std_Http_instBEqURI___closed__0_value;
static const lean_string_object l_Std_Http_instToStringURI___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Std_Http_instToStringURI___lam__1___closed__0 = (const lean_object*)&l_Std_Http_instToStringURI___lam__1___closed__0_value;
static const lean_string_object l_Std_Http_instToStringURI___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "//"};
static const lean_object* l_Std_Http_instToStringURI___lam__1___closed__1 = (const lean_object*)&l_Std_Http_instToStringURI___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instToStringURI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instToStringURI___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value)} };
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x3f(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_URI_Builder_setHost_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Std.Http.URI.Builder.setHost!"};
static const lean_object* l_Std_Http_URI_Builder_setHost_x21___closed__0 = (const lean_object*)&l_Std_Http_URI_Builder_setHost_x21___closed__0_value;
static const lean_string_object l_Std_Http_URI_Builder_setHost_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid domain name: "};
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
LEAN_EXPORT lean_object* l_Std_Http_instToStringRelativeRef___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instToStringRelativeRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instToStringRelativeRef___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value)} };
static const lean_object* l_Std_Http_instToStringRelativeRef___closed__0 = (const lean_object*)&l_Std_Http_instToStringRelativeRef___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instToStringRelativeRef = (const lean_object*)&l_Std_Http_instToStringRelativeRef___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_instToStringURIReference___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instToStringURIReference___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instToStringURIReference___lam__2, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value),((lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value)} };
static const lean_object* l_Std_Http_instToStringURIReference___closed__0 = (const lean_object*)&l_Std_Http_instToStringURIReference___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instToStringURIReference = (const lean_object*)&l_Std_Http_instToStringURIReference___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___boxed(lean_object*);
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
static const lean_array_object l_Std_Http_RequestTarget_path___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_RequestTarget_path___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_path___closed__0_value;
static const lean_ctor_object l_Std_Http_RequestTarget_path___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_RequestTarget_path___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_RequestTarget_path___closed__1 = (const lean_object*)&l_Std_Http_RequestTarget_path___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authority_x3f(lean_object*);
static const lean_string_object l_Std_Http_RequestTarget_instToString___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Std_Http_RequestTarget_instToString___lam__2___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_instToString___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_RequestTarget_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_RequestTarget_instToString___lam__2, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value),((lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value)} };
static const lean_object* l_Std_Http_RequestTarget_instToString___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_RequestTarget_instToString = (const lean_object*)&l_Std_Http_RequestTarget_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_RequestTarget_instEncodeV11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_RequestTarget_instEncodeV11___lam__2, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value),((lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value)} };
static const lean_object* l_Std_Http_RequestTarget_instEncodeV11___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_instEncodeV11___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_RequestTarget_instEncodeV11 = (const lean_object*)&l_Std_Http_RequestTarget_instEncodeV11___closed__0_value;
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(lean_object* v_s_3_, lean_object* v_p_4_){
_start:
{
uint32_t v___y_6_; lean_object* v___x_11_; uint8_t v_decide_12_; 
v___x_11_ = lean_string_utf8_byte_size(v_s_3_);
v_decide_12_ = lean_nat_dec_eq(v_p_4_, v___x_11_);
if (v_decide_12_ == 0)
{
uint32_t v___x_13_; uint8_t v___y_15_; uint32_t v___x_18_; uint8_t v___x_19_; 
v___x_13_ = lean_string_utf8_get_fast(v_s_3_, v_p_4_);
v___x_18_ = 65;
v___x_19_ = lean_uint32_dec_le(v___x_18_, v___x_13_);
if (v___x_19_ == 0)
{
v___y_15_ = v___x_19_;
goto v___jp_14_;
}
else
{
uint32_t v___x_20_; uint8_t v___x_21_; 
v___x_20_ = 90;
v___x_21_ = lean_uint32_dec_le(v___x_13_, v___x_20_);
v___y_15_ = v___x_21_;
goto v___jp_14_;
}
v___jp_14_:
{
if (v___y_15_ == 0)
{
v___y_6_ = v___x_13_;
goto v___jp_5_;
}
else
{
uint32_t v___x_16_; uint32_t v___x_17_; 
v___x_16_ = 32;
v___x_17_ = lean_uint32_add(v___x_13_, v___x_16_);
v___y_6_ = v___x_17_;
goto v___jp_5_;
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
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
lean_inc(v_p_4_);
v___x_7_ = lean_string_utf8_set(v_s_3_, v_p_4_, v___y_6_);
v___x_8_ = l_Char_utf8Size(v___y_6_);
v___x_9_ = lean_nat_add(v_p_4_, v___x_8_);
lean_dec(v___x_8_);
lean_dec(v_p_4_);
v_s_3_ = v___x_7_;
v_p_4_ = v___x_9_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(lean_object* v_x_22_){
_start:
{
if (lean_obj_tag(v_x_22_) == 0)
{
uint8_t v___x_23_; 
v___x_23_ = 1;
return v___x_23_;
}
else
{
lean_object* v_head_24_; lean_object* v_tail_25_; uint8_t v___y_40_; uint32_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v_head_24_ = lean_ctor_get(v_x_22_, 0);
v_tail_25_ = lean_ctor_get(v_x_22_, 1);
v___x_56_ = lean_unbox_uint32(v_head_24_);
v___x_57_ = lean_uint32_to_nat(v___x_56_);
v___x_58_ = lean_unsigned_to_nat(128u);
v___x_59_ = lean_nat_dec_lt(v___x_57_, v___x_58_);
lean_dec(v___x_57_);
if (v___x_59_ == 0)
{
goto v___jp_26_;
}
else
{
uint32_t v___x_60_; uint32_t v___x_61_; uint8_t v___x_62_; 
v___x_60_ = 48;
v___x_61_ = lean_unbox_uint32(v_head_24_);
v___x_62_ = lean_uint32_dec_le(v___x_60_, v___x_61_);
if (v___x_62_ == 0)
{
goto v___jp_49_;
}
else
{
uint32_t v___x_63_; uint32_t v___x_64_; uint8_t v___x_65_; 
v___x_63_ = 57;
v___x_64_ = lean_unbox_uint32(v_head_24_);
v___x_65_ = lean_uint32_dec_le(v___x_64_, v___x_63_);
if (v___x_65_ == 0)
{
goto v___jp_49_;
}
else
{
v_x_22_ = v_tail_25_;
goto _start;
}
}
}
v___jp_26_:
{
uint32_t v___x_27_; uint32_t v___x_28_; uint8_t v___x_29_; 
v___x_27_ = 43;
v___x_28_ = lean_unbox_uint32(v_head_24_);
v___x_29_ = lean_uint32_dec_eq(v___x_28_, v___x_27_);
if (v___x_29_ == 0)
{
uint32_t v___x_30_; uint32_t v___x_31_; uint8_t v___x_32_; 
v___x_30_ = 45;
v___x_31_ = lean_unbox_uint32(v_head_24_);
v___x_32_ = lean_uint32_dec_eq(v___x_31_, v___x_30_);
if (v___x_32_ == 0)
{
uint32_t v___x_33_; uint32_t v___x_34_; uint8_t v___x_35_; 
v___x_33_ = 46;
v___x_34_ = lean_unbox_uint32(v_head_24_);
v___x_35_ = lean_uint32_dec_eq(v___x_34_, v___x_33_);
if (v___x_35_ == 0)
{
return v___x_35_;
}
else
{
v_x_22_ = v_tail_25_;
goto _start;
}
}
else
{
v_x_22_ = v_tail_25_;
goto _start;
}
}
else
{
v_x_22_ = v_tail_25_;
goto _start;
}
}
v___jp_39_:
{
if (v___y_40_ == 0)
{
uint32_t v___x_41_; uint32_t v___x_42_; uint8_t v___x_43_; 
v___x_41_ = 97;
v___x_42_ = lean_unbox_uint32(v_head_24_);
v___x_43_ = lean_uint32_dec_le(v___x_41_, v___x_42_);
if (v___x_43_ == 0)
{
goto v___jp_26_;
}
else
{
uint32_t v___x_44_; uint32_t v___x_45_; uint8_t v___x_46_; 
v___x_44_ = 122;
v___x_45_ = lean_unbox_uint32(v_head_24_);
v___x_46_ = lean_uint32_dec_le(v___x_45_, v___x_44_);
if (v___x_46_ == 0)
{
goto v___jp_26_;
}
else
{
v_x_22_ = v_tail_25_;
goto _start;
}
}
}
else
{
v_x_22_ = v_tail_25_;
goto _start;
}
}
v___jp_49_:
{
uint32_t v___x_50_; uint32_t v___x_51_; uint8_t v___x_52_; 
v___x_50_ = 65;
v___x_51_ = lean_unbox_uint32(v_head_24_);
v___x_52_ = lean_uint32_dec_le(v___x_50_, v___x_51_);
if (v___x_52_ == 0)
{
v___y_40_ = v___x_52_;
goto v___jp_39_;
}
else
{
uint32_t v___x_53_; uint32_t v___x_54_; uint8_t v___x_55_; 
v___x_53_ = 90;
v___x_54_ = lean_unbox_uint32(v_head_24_);
v___x_55_ = lean_uint32_dec_le(v___x_54_, v___x_53_);
v___y_40_ = v___x_55_;
goto v___jp_39_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1___boxed(lean_object* v_x_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(v_x_67_);
lean_dec(v_x_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x3f(lean_object* v_s_70_){
_start:
{
lean_object* v___x_71_; lean_object* v_lower_72_; uint8_t v___y_74_; uint8_t v___x_77_; uint8_t v___y_79_; lean_object* v___x_80_; uint8_t v___x_81_; uint8_t v___y_83_; lean_object* v___x_84_; 
v___x_71_ = lean_unsigned_to_nat(0u);
v_lower_72_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_70_, v___x_71_);
lean_inc_ref_n(v_lower_72_, 2);
v___x_77_ = l_Std_Http_Internal_instDecidableIsLowerCase(v_lower_72_);
v___x_80_ = lean_string_data(v_lower_72_);
v___x_81_ = l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(v___x_80_);
v___x_84_ = l_List_head_x3f___redArg(v___x_80_);
lean_dec(v___x_80_);
if (lean_obj_tag(v___x_84_) == 0)
{
uint8_t v___x_85_; 
v___x_85_ = 0;
v___y_83_ = v___x_85_;
goto v___jp_82_;
}
else
{
lean_object* v_val_86_; uint8_t v___y_88_; uint32_t v___x_95_; uint32_t v___x_96_; uint8_t v___x_97_; 
v_val_86_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_val_86_);
lean_dec_ref_known(v___x_84_, 1);
v___x_95_ = 65;
v___x_96_ = lean_unbox_uint32(v_val_86_);
v___x_97_ = lean_uint32_dec_le(v___x_95_, v___x_96_);
if (v___x_97_ == 0)
{
v___y_88_ = v___x_97_;
goto v___jp_87_;
}
else
{
uint32_t v___x_98_; uint32_t v___x_99_; uint8_t v___x_100_; 
v___x_98_ = 90;
v___x_99_ = lean_unbox_uint32(v_val_86_);
v___x_100_ = lean_uint32_dec_le(v___x_99_, v___x_98_);
v___y_88_ = v___x_100_;
goto v___jp_87_;
}
v___jp_87_:
{
if (v___y_88_ == 0)
{
uint32_t v___x_89_; uint32_t v___x_90_; uint8_t v___x_91_; 
v___x_89_ = 97;
v___x_90_ = lean_unbox_uint32(v_val_86_);
v___x_91_ = lean_uint32_dec_le(v___x_89_, v___x_90_);
if (v___x_91_ == 0)
{
lean_dec(v_val_86_);
v___y_83_ = v___x_91_;
goto v___jp_82_;
}
else
{
uint32_t v___x_92_; uint32_t v___x_93_; uint8_t v___x_94_; 
v___x_92_ = 122;
v___x_93_ = lean_unbox_uint32(v_val_86_);
lean_dec(v_val_86_);
v___x_94_ = lean_uint32_dec_le(v___x_93_, v___x_92_);
v___y_83_ = v___x_94_;
goto v___jp_82_;
}
}
else
{
lean_dec(v_val_86_);
v___y_83_ = v___y_88_;
goto v___jp_82_;
}
}
}
v___jp_73_:
{
if (v___y_74_ == 0)
{
lean_object* v___x_75_; 
lean_dec_ref(v_lower_72_);
v___x_75_ = lean_box(0);
return v___x_75_;
}
else
{
lean_object* v___x_76_; 
v___x_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_76_, 0, v_lower_72_);
return v___x_76_;
}
}
v___jp_78_:
{
if (v___x_77_ == 0)
{
v___y_74_ = v___x_77_;
goto v___jp_73_;
}
else
{
v___y_74_ = v___y_79_;
goto v___jp_73_;
}
}
v___jp_82_:
{
if (v___x_81_ == 0)
{
v___y_79_ = v___x_81_;
goto v___jp_78_;
}
else
{
v___y_79_ = v___y_83_;
goto v___jp_78_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(lean_object* v_msg_101_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = ((lean_object*)(l_Std_Http_URI_instInhabitedScheme___closed__0));
v___x_103_ = lean_panic_fn_borrowed(v___x_102_, v_msg_101_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x21(lean_object* v_s_107_){
_start:
{
lean_object* v___x_108_; 
lean_inc_ref(v_s_107_);
v___x_108_ = l_Std_Http_URI_Scheme_ofString_x3f(v_s_107_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_109_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_110_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__1));
v___x_111_ = lean_unsigned_to_nat(84u);
v___x_112_ = lean_unsigned_to_nat(12u);
v___x_113_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_114_ = l_String_quote(v_s_107_);
v___x_115_ = lean_string_append(v___x_113_, v___x_114_);
lean_dec_ref(v___x_114_);
v___x_116_ = l_mkPanicMessageWithDecl(v___x_109_, v___x_110_, v___x_111_, v___x_112_, v___x_115_);
lean_dec_ref(v___x_115_);
v___x_117_ = l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(v___x_116_);
return v___x_117_;
}
else
{
lean_object* v_val_118_; 
lean_dec_ref(v_s_107_);
v_val_118_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_val_118_);
lean_dec_ref_known(v___x_108_, 1);
return v_val_118_;
}
}
}
LEAN_EXPORT uint16_t l_Std_Http_URI_Scheme_defaultPort(lean_object* v_scheme_120_){
_start:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___x_122_ = lean_string_dec_eq(v_scheme_120_, v___x_121_);
if (v___x_122_ == 0)
{
uint16_t v___x_123_; 
v___x_123_ = 80;
return v___x_123_;
}
else
{
uint16_t v___x_124_; 
v___x_124_ = 443;
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_defaultPort___boxed(lean_object* v_scheme_125_){
_start:
{
uint16_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_125_);
lean_dec_ref(v_scheme_125_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofPort(uint16_t v_port_128_){
_start:
{
uint16_t v___x_129_; uint8_t v___x_130_; 
v___x_129_ = 443;
v___x_130_ = lean_uint16_dec_eq(v_port_128_, v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
v___x_131_ = ((lean_object*)(l_Std_Http_URI_instInhabitedScheme___closed__0));
return v___x_131_;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofPort___boxed(lean_object* v_port_133_){
_start:
{
uint16_t v_port_boxed_134_; lean_object* v_res_135_; 
v_port_boxed_134_ = lean_unbox(v_port_133_);
v_res_135_ = l_Std_Http_URI_Scheme_ofPort(v_port_boxed_134_);
return v_res_135_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__0(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_box(0);
v___x_137_ = l_ByteArray_empty;
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_136_);
return v___x_138_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default(void){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_obj_once(&l_Std_Http_URI_instInhabitedUserInfo_default___closed__0, &l_Std_Http_URI_instInhabitedUserInfo_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__0);
return v___x_139_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo(void){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Std_Http_URI_instInhabitedUserInfo_default;
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
lean_object* v___x_149_; 
v___x_149_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_149_;
}
else
{
lean_object* v_val_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_162_; 
v_val_150_ = lean_ctor_get(v_x_147_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v_x_147_);
if (v_isSharedCheck_162_ == 0)
{
v___x_152_ = v_x_147_;
v_isShared_153_ = v_isSharedCheck_162_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_val_150_);
lean_dec(v_x_147_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_162_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_154_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_155_ = lean_string_from_utf8_unchecked(v_val_150_);
v___x_156_ = l_String_quote(v___x_155_);
if (v_isShared_153_ == 0)
{
lean_ctor_set_tag(v___x_152_, 3);
lean_ctor_set(v___x_152_, 0, v___x_156_);
v___x_158_ = v___x_152_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_161_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_154_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = l_Repr_addAppParen(v___x_159_, v_x_148_);
return v___x_160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___boxed(lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_x_163_, v_x_164_);
lean_dec(v_x_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_URI_instReprUserInfo_repr_spec__1(lean_object* v_a_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_nat_to_int(v_a_166_);
return v___x_167_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_unsigned_to_nat(12u);
v___x_182_ = lean_nat_to_int(v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0));
v___x_191_ = lean_string_length(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13);
v___x_193_ = lean_nat_to_int(v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg(lean_object* v_x_198_){
_start:
{
lean_object* v_username_199_; lean_object* v_password_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_235_; 
v_username_199_ = lean_ctor_get(v_x_198_, 0);
v_password_200_ = lean_ctor_get(v_x_198_, 1);
v_isSharedCheck_235_ = !lean_is_exclusive(v_x_198_);
if (v_isSharedCheck_235_ == 0)
{
v___x_202_ = v_x_198_;
v_isShared_203_ = v_isSharedCheck_235_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_password_200_);
lean_inc(v_username_199_);
lean_dec(v_x_198_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_235_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_204_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_205_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__6));
v___x_206_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_207_ = lean_string_from_utf8_unchecked(v_username_199_);
v___x_208_ = l_String_quote(v___x_207_);
v___x_209_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
if (v_isShared_203_ == 0)
{
lean_ctor_set_tag(v___x_202_, 4);
lean_ctor_set(v___x_202_, 1, v___x_209_);
lean_ctor_set(v___x_202_, 0, v___x_206_);
v___x_211_ = v___x_202_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v___x_209_);
v___x_211_ = v_reuseFailAlloc_234_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
uint8_t v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_212_ = 0;
v___x_213_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_213_, 0, v___x_211_);
lean_ctor_set_uint8(v___x_213_, sizeof(void*)*1, v___x_212_);
v___x_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_205_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_214_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = lean_box(1);
v___x_218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__11));
v___x_220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_204_);
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_password_200_, v___x_222_);
v___x_224_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_206_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v___x_212_);
v___x_226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_221_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_228_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___x_226_);
v___x_230_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_227_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*1, v___x_212_);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr(lean_object* v_x_236_, lean_object* v_prec_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_x_236_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___boxed(lean_object* v_x_239_, lean_object* v_prec_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Std_Http_URI_instReprUserInfo_repr(v_x_239_, v_prec_240_);
lean_dec(v_prec_240_);
return v_res_241_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
if (lean_obj_tag(v_x_244_) == 0)
{
if (lean_obj_tag(v_x_245_) == 0)
{
uint8_t v___x_246_; 
v___x_246_ = 1;
return v___x_246_;
}
else
{
uint8_t v___x_247_; 
v___x_247_ = 0;
return v___x_247_;
}
}
else
{
if (lean_obj_tag(v_x_245_) == 0)
{
uint8_t v___x_248_; 
v___x_248_ = 0;
return v___x_248_;
}
else
{
lean_object* v_val_249_; lean_object* v_val_250_; uint8_t v___x_251_; 
v_val_249_ = lean_ctor_get(v_x_244_, 0);
v_val_250_ = lean_ctor_get(v_x_245_, 0);
v___x_251_ = lean_sarray_dec_eq(v_val_249_, v_val_250_);
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0___boxed(lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_x_252_, v_x_253_);
lean_dec(v_x_253_);
lean_dec(v_x_252_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqUserInfo_beq(lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
lean_object* v_username_258_; lean_object* v_password_259_; lean_object* v_username_260_; lean_object* v_password_261_; uint8_t v___x_262_; 
v_username_258_ = lean_ctor_get(v_x_256_, 0);
v_password_259_ = lean_ctor_get(v_x_256_, 1);
v_username_260_ = lean_ctor_get(v_x_257_, 0);
v_password_261_ = lean_ctor_get(v_x_257_, 1);
v___x_262_ = lean_sarray_dec_eq(v_username_258_, v_username_260_);
if (v___x_262_ == 0)
{
return v___x_262_;
}
else
{
uint8_t v___x_263_; 
v___x_263_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_password_259_, v_password_261_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqUserInfo_beq___boxed(lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
uint8_t v_res_266_; lean_object* v_r_267_; 
v_res_266_ = l_Std_Http_URI_instBEqUserInfo_beq(v_x_264_, v_x_265_);
lean_dec_ref(v_x_265_);
lean_dec_ref(v_x_264_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings(lean_object* v_username_270_, lean_object* v_password_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_270_);
if (lean_obj_tag(v_password_271_) == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_box(0);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
return v___x_274_;
}
else
{
lean_object* v_val_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_284_; 
v_val_275_ = lean_ctor_get(v_password_271_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v_password_271_);
if (v_isSharedCheck_284_ == 0)
{
v___x_277_ = v_password_271_;
v_isShared_278_ = v_isSharedCheck_284_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_val_275_);
lean_dec(v_password_271_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_284_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_279_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_275_);
lean_dec(v_val_275_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_279_);
v___x_281_ = v___x_277_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_283_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_282_; 
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_272_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings___boxed(lean_object* v_username_285_, lean_object* v_password_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Std_Http_URI_UserInfo_ofStrings(v_username_285_, v_password_286_);
lean_dec_ref(v_username_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f(lean_object* v_ui_288_){
_start:
{
lean_object* v_username_289_; lean_object* v___x_290_; 
v_username_289_ = lean_ctor_get(v_ui_288_, 0);
v___x_290_ = l_Std_Http_URI_EncodedUserInfo_decode(v_username_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f___boxed(lean_object* v_ui_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Std_Http_URI_UserInfo_username_x3f(v_ui_291_);
lean_dec_ref(v_ui_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f(lean_object* v_ui_293_){
_start:
{
lean_object* v_password_294_; 
v_password_294_ = lean_ctor_get(v_ui_293_, 1);
if (lean_obj_tag(v_password_294_) == 0)
{
lean_object* v___x_295_; 
v___x_295_ = lean_box(0);
return v___x_295_;
}
else
{
lean_object* v_val_296_; lean_object* v___x_297_; 
v_val_296_ = lean_ctor_get(v_password_294_, 0);
v___x_297_ = l_Std_Http_URI_EncodedUserInfo_decode(v_val_296_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f___boxed(lean_object* v_ui_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Std_Http_URI_UserInfo_password_x3f(v_ui_298_);
lean_dec_ref(v_ui_298_);
return v_res_299_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(lean_object* v_x_300_){
_start:
{
if (lean_obj_tag(v_x_300_) == 0)
{
uint8_t v___x_301_; 
v___x_301_ = 1;
return v___x_301_;
}
else
{
lean_object* v_head_302_; lean_object* v_tail_303_; uint8_t v___y_305_; uint8_t v___y_312_; uint32_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v_head_302_ = lean_ctor_get(v_x_300_, 0);
v_tail_303_ = lean_ctor_get(v_x_300_, 1);
v___x_327_ = lean_unbox_uint32(v_head_302_);
v___x_328_ = lean_uint32_to_nat(v___x_327_);
v___x_329_ = lean_unsigned_to_nat(128u);
v___x_330_ = lean_nat_dec_lt(v___x_328_, v___x_329_);
lean_dec(v___x_328_);
if (v___x_330_ == 0)
{
v___y_305_ = v___x_330_;
goto v___jp_304_;
}
else
{
uint32_t v___x_331_; uint32_t v___x_332_; uint8_t v___x_333_; 
v___x_331_ = 48;
v___x_332_ = lean_unbox_uint32(v_head_302_);
v___x_333_ = lean_uint32_dec_le(v___x_331_, v___x_332_);
if (v___x_333_ == 0)
{
goto v___jp_320_;
}
else
{
uint32_t v___x_334_; uint32_t v___x_335_; uint8_t v___x_336_; 
v___x_334_ = 57;
v___x_335_ = lean_unbox_uint32(v_head_302_);
v___x_336_ = lean_uint32_dec_le(v___x_335_, v___x_334_);
if (v___x_336_ == 0)
{
goto v___jp_320_;
}
else
{
v___y_305_ = v___x_336_;
goto v___jp_304_;
}
}
}
v___jp_304_:
{
if (v___y_305_ == 0)
{
uint32_t v___x_306_; uint32_t v___x_307_; uint8_t v___x_308_; 
v___x_306_ = 45;
v___x_307_ = lean_unbox_uint32(v_head_302_);
v___x_308_ = lean_uint32_dec_eq(v___x_307_, v___x_306_);
if (v___x_308_ == 0)
{
return v___x_308_;
}
else
{
v_x_300_ = v_tail_303_;
goto _start;
}
}
else
{
v_x_300_ = v_tail_303_;
goto _start;
}
}
v___jp_311_:
{
if (v___y_312_ == 0)
{
uint32_t v___x_313_; uint32_t v___x_314_; uint8_t v___x_315_; 
v___x_313_ = 97;
v___x_314_ = lean_unbox_uint32(v_head_302_);
v___x_315_ = lean_uint32_dec_le(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
v___y_305_ = v___x_315_;
goto v___jp_304_;
}
else
{
uint32_t v___x_316_; uint32_t v___x_317_; uint8_t v___x_318_; 
v___x_316_ = 122;
v___x_317_ = lean_unbox_uint32(v_head_302_);
v___x_318_ = lean_uint32_dec_le(v___x_317_, v___x_316_);
v___y_305_ = v___x_318_;
goto v___jp_304_;
}
}
else
{
v_x_300_ = v_tail_303_;
goto _start;
}
}
v___jp_320_:
{
uint32_t v___x_321_; uint32_t v___x_322_; uint8_t v___x_323_; 
v___x_321_ = 65;
v___x_322_ = lean_unbox_uint32(v_head_302_);
v___x_323_ = lean_uint32_dec_le(v___x_321_, v___x_322_);
if (v___x_323_ == 0)
{
v___y_312_ = v___x_323_;
goto v___jp_311_;
}
else
{
uint32_t v___x_324_; uint32_t v___x_325_; uint8_t v___x_326_; 
v___x_324_ = 90;
v___x_325_ = lean_unbox_uint32(v_head_302_);
v___x_326_ = lean_uint32_dec_le(v___x_325_, v___x_324_);
v___y_312_ = v___x_326_;
goto v___jp_311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0___boxed(lean_object* v_x_337_){
_start:
{
uint8_t v_res_338_; lean_object* v_r_339_; 
v_res_338_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v_x_337_);
lean_dec(v_x_337_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object* v_s_340_){
_start:
{
uint32_t v___y_342_; uint8_t v___y_343_; uint32_t v___y_349_; lean_object* v_chars_354_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v_chars_354_ = lean_string_data(v_s_340_);
v___x_371_ = l_List_lengthTR___redArg(v_chars_354_);
v___x_372_ = lean_unsigned_to_nat(63u);
v___x_373_ = lean_nat_dec_le(v___x_371_, v___x_372_);
lean_dec(v___x_371_);
if (v___x_373_ == 0)
{
lean_dec(v_chars_354_);
return v___x_373_;
}
else
{
uint8_t v___x_374_; 
v___x_374_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v_chars_354_);
if (v___x_374_ == 0)
{
lean_dec(v_chars_354_);
return v___x_374_;
}
else
{
lean_object* v___x_375_; 
v___x_375_ = l_List_head_x3f___redArg(v_chars_354_);
if (lean_obj_tag(v___x_375_) == 0)
{
uint8_t v___x_376_; 
lean_dec(v_chars_354_);
v___x_376_ = 0;
return v___x_376_;
}
else
{
lean_object* v_val_377_; uint8_t v___y_379_; uint32_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v_val_377_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_val_377_);
lean_dec_ref_known(v___x_375_, 1);
v___x_393_ = lean_unbox_uint32(v_val_377_);
v___x_394_ = lean_uint32_to_nat(v___x_393_);
v___x_395_ = lean_unsigned_to_nat(128u);
v___x_396_ = lean_nat_dec_lt(v___x_394_, v___x_395_);
lean_dec(v___x_394_);
if (v___x_396_ == 0)
{
lean_dec(v_val_377_);
lean_dec(v_chars_354_);
return v___x_396_;
}
else
{
uint32_t v___x_397_; uint32_t v___x_398_; uint8_t v___x_399_; 
v___x_397_ = 48;
v___x_398_ = lean_unbox_uint32(v_val_377_);
v___x_399_ = lean_uint32_dec_le(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
goto v___jp_386_;
}
else
{
uint32_t v___x_400_; uint32_t v___x_401_; uint8_t v___x_402_; 
v___x_400_ = 57;
v___x_401_ = lean_unbox_uint32(v_val_377_);
v___x_402_ = lean_uint32_dec_le(v___x_401_, v___x_400_);
if (v___x_402_ == 0)
{
goto v___jp_386_;
}
else
{
lean_dec(v_val_377_);
goto v___jp_355_;
}
}
}
v___jp_378_:
{
if (v___y_379_ == 0)
{
uint32_t v___x_380_; uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_380_ = 97;
v___x_381_ = lean_unbox_uint32(v_val_377_);
v___x_382_ = lean_uint32_dec_le(v___x_380_, v___x_381_);
if (v___x_382_ == 0)
{
lean_dec(v_val_377_);
lean_dec(v_chars_354_);
return v___x_382_;
}
else
{
uint32_t v___x_383_; uint32_t v___x_384_; uint8_t v___x_385_; 
v___x_383_ = 122;
v___x_384_ = lean_unbox_uint32(v_val_377_);
lean_dec(v_val_377_);
v___x_385_ = lean_uint32_dec_le(v___x_384_, v___x_383_);
if (v___x_385_ == 0)
{
lean_dec(v_chars_354_);
return v___x_385_;
}
else
{
goto v___jp_355_;
}
}
}
else
{
lean_dec(v_val_377_);
goto v___jp_355_;
}
}
v___jp_386_:
{
uint32_t v___x_387_; uint32_t v___x_388_; uint8_t v___x_389_; 
v___x_387_ = 65;
v___x_388_ = lean_unbox_uint32(v_val_377_);
v___x_389_ = lean_uint32_dec_le(v___x_387_, v___x_388_);
if (v___x_389_ == 0)
{
v___y_379_ = v___x_389_;
goto v___jp_378_;
}
else
{
uint32_t v___x_390_; uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_390_ = 90;
v___x_391_ = lean_unbox_uint32(v_val_377_);
v___x_392_ = lean_uint32_dec_le(v___x_391_, v___x_390_);
v___y_379_ = v___x_392_;
goto v___jp_378_;
}
}
}
}
}
v___jp_341_:
{
if (v___y_343_ == 0)
{
uint32_t v___x_344_; uint8_t v___x_345_; 
v___x_344_ = 97;
v___x_345_ = lean_uint32_dec_le(v___x_344_, v___y_342_);
if (v___x_345_ == 0)
{
return v___x_345_;
}
else
{
uint32_t v___x_346_; uint8_t v___x_347_; 
v___x_346_ = 122;
v___x_347_ = lean_uint32_dec_le(v___y_342_, v___x_346_);
return v___x_347_;
}
}
else
{
return v___y_343_;
}
}
v___jp_348_:
{
uint32_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = 65;
v___x_351_ = lean_uint32_dec_le(v___x_350_, v___y_349_);
if (v___x_351_ == 0)
{
v___y_342_ = v___y_349_;
v___y_343_ = v___x_351_;
goto v___jp_341_;
}
else
{
uint32_t v___x_352_; uint8_t v___x_353_; 
v___x_352_ = 90;
v___x_353_ = lean_uint32_dec_le(v___y_349_, v___x_352_);
v___y_342_ = v___y_349_;
v___y_343_ = v___x_353_;
goto v___jp_341_;
}
}
v___jp_355_:
{
lean_object* v___x_356_; 
v___x_356_ = l_List_getLast_x3f___redArg(v_chars_354_);
lean_dec(v_chars_354_);
if (lean_obj_tag(v___x_356_) == 0)
{
uint8_t v___x_357_; 
v___x_357_ = 0;
return v___x_357_;
}
else
{
lean_object* v_val_358_; uint32_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_val_358_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_val_358_);
lean_dec_ref_known(v___x_356_, 1);
v___x_359_ = lean_unbox_uint32(v_val_358_);
v___x_360_ = lean_uint32_to_nat(v___x_359_);
v___x_361_ = lean_unsigned_to_nat(128u);
v___x_362_ = lean_nat_dec_lt(v___x_360_, v___x_361_);
lean_dec(v___x_360_);
if (v___x_362_ == 0)
{
lean_dec(v_val_358_);
return v___x_362_;
}
else
{
uint32_t v___x_363_; uint32_t v___x_364_; uint8_t v___x_365_; 
v___x_363_ = 48;
v___x_364_ = lean_unbox_uint32(v_val_358_);
v___x_365_ = lean_uint32_dec_le(v___x_363_, v___x_364_);
if (v___x_365_ == 0)
{
uint32_t v___x_366_; 
v___x_366_ = lean_unbox_uint32(v_val_358_);
lean_dec(v_val_358_);
v___y_349_ = v___x_366_;
goto v___jp_348_;
}
else
{
uint32_t v___x_367_; uint32_t v___x_368_; uint8_t v___x_369_; 
v___x_367_ = 57;
v___x_368_ = lean_unbox_uint32(v_val_358_);
v___x_369_ = lean_uint32_dec_le(v___x_368_, v___x_367_);
if (v___x_369_ == 0)
{
uint32_t v___x_370_; 
v___x_370_ = lean_unbox_uint32(v_val_358_);
lean_dec(v_val_358_);
v___y_349_ = v___x_370_;
goto v___jp_348_;
}
else
{
lean_dec(v_val_358_);
return v___x_369_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidDomainLabel___boxed(lean_object* v_s_403_){
_start:
{
uint8_t v_res_404_; lean_object* v_r_405_; 
v_res_404_ = l_Std_Http_URI_isValidDomainLabel(v_s_403_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg(){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___closed__0));
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___boxed(lean_object* v___dummy_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg();
return v_res_411_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg();
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(lean_object* v_s_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___boxed(lean_object* v_s_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(v_s_415_);
lean_dec_ref(v_s_415_);
return v_res_416_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___redArg(lean_object* v_lower_417_, lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v_a_420_, uint8_t v_b_421_){
_start:
{
if (lean_obj_tag(v_a_420_) == 0)
{
lean_object* v_currPos_422_; lean_object* v_searcher_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_460_; 
v_currPos_422_ = lean_ctor_get(v_a_420_, 0);
v_searcher_423_ = lean_ctor_get(v_a_420_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v_a_420_);
if (v_isSharedCheck_460_ == 0)
{
v___x_425_ = v_a_420_;
v_isShared_426_ = v_isSharedCheck_460_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_searcher_423_);
lean_inc(v_currPos_422_);
lean_dec(v_a_420_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_460_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v_str_427_; lean_object* v_startInclusive_428_; lean_object* v_endExclusive_429_; uint8_t v___x_430_; lean_object* v_it_432_; lean_object* v_startInclusive_433_; lean_object* v_endExclusive_434_; lean_object* v___x_438_; uint8_t v_decide_439_; 
v_str_427_ = lean_ctor_get(v___x_418_, 0);
v_startInclusive_428_ = lean_ctor_get(v___x_418_, 1);
v_endExclusive_429_ = lean_ctor_get(v___x_418_, 2);
v___x_430_ = 1;
v___x_438_ = lean_nat_sub(v_endExclusive_429_, v_startInclusive_428_);
v_decide_439_ = lean_nat_dec_eq(v_searcher_423_, v___x_438_);
lean_dec(v___x_438_);
if (v_decide_439_ == 0)
{
uint32_t v___x_440_; lean_object* v___x_441_; uint32_t v___x_442_; uint8_t v___x_443_; 
v___x_440_ = 46;
v___x_441_ = lean_nat_add(v_startInclusive_428_, v_searcher_423_);
v___x_442_ = lean_string_utf8_get_fast(v_str_427_, v___x_441_);
v___x_443_ = lean_uint32_dec_eq(v___x_442_, v___x_440_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
lean_dec(v_searcher_423_);
v___x_444_ = lean_string_utf8_next_fast(v_str_427_, v___x_441_);
lean_dec(v___x_441_);
v___x_445_ = lean_nat_sub(v___x_444_, v_startInclusive_428_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 1, v___x_445_);
v___x_447_ = v___x_425_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_currPos_422_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v___x_445_);
v___x_447_ = v_reuseFailAlloc_449_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
v_a_420_ = v___x_447_;
goto _start;
}
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v_slice_453_; lean_object* v_nextIt_455_; 
v___x_450_ = lean_string_utf8_next_fast(v_str_427_, v___x_441_);
v___x_451_ = lean_nat_sub(v___x_450_, v___x_441_);
lean_dec(v___x_441_);
v___x_452_ = lean_nat_add(v_searcher_423_, v___x_451_);
lean_dec(v___x_451_);
v_slice_453_ = l_String_Slice_subslice_x21(v___x_418_, v_currPos_422_, v_searcher_423_);
lean_inc(v___x_452_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 1, v___x_452_);
lean_ctor_set(v___x_425_, 0, v___x_452_);
v_nextIt_455_ = v___x_425_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v___x_452_);
v_nextIt_455_ = v_reuseFailAlloc_458_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v_startInclusive_456_; lean_object* v_endExclusive_457_; 
v_startInclusive_456_ = lean_ctor_get(v_slice_453_, 0);
lean_inc(v_startInclusive_456_);
v_endExclusive_457_ = lean_ctor_get(v_slice_453_, 1);
lean_inc(v_endExclusive_457_);
lean_dec_ref(v_slice_453_);
v_it_432_ = v_nextIt_455_;
v_startInclusive_433_ = v_startInclusive_456_;
v_endExclusive_434_ = v_endExclusive_457_;
goto v___jp_431_;
}
}
}
else
{
lean_object* v___x_459_; 
lean_del_object(v___x_425_);
lean_dec(v_searcher_423_);
v___x_459_ = lean_box(1);
lean_inc(v___x_419_);
v_it_432_ = v___x_459_;
v_startInclusive_433_ = v_currPos_422_;
v_endExclusive_434_ = v___x_419_;
goto v___jp_431_;
}
v___jp_431_:
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = lean_string_utf8_extract_fast(v_lower_417_, v_startInclusive_433_, v_endExclusive_434_);
lean_dec(v_endExclusive_434_);
lean_dec(v_startInclusive_433_);
v___x_436_ = l_Std_Http_URI_isValidDomainLabel(v___x_435_);
if (v___x_436_ == 0)
{
lean_dec(v_it_432_);
lean_dec(v___x_419_);
return v___x_436_;
}
else
{
v_a_420_ = v_it_432_;
v_b_421_ = v___x_430_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_419_);
return v_b_421_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___redArg___boxed(lean_object* v_lower_461_, lean_object* v___x_462_, lean_object* v___x_463_, lean_object* v_a_464_, lean_object* v_b_465_){
_start:
{
uint8_t v_b_boxed_466_; uint8_t v_res_467_; lean_object* v_r_468_; 
v_b_boxed_466_ = lean_unbox(v_b_465_);
v_res_467_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___redArg(v_lower_461_, v___x_462_, v___x_463_, v_a_464_, v_b_boxed_466_);
lean_dec_ref(v___x_462_);
lean_dec_ref(v_lower_461_);
v_r_468_ = lean_box(v_res_467_);
return v_r_468_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(lean_object* v_lower_469_, lean_object* v___x_470_, lean_object* v___x_471_, lean_object* v_a_472_, uint8_t v_b_473_){
_start:
{
if (lean_obj_tag(v_a_472_) == 0)
{
lean_object* v_currPos_474_; lean_object* v_searcher_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_512_; 
v_currPos_474_ = lean_ctor_get(v_a_472_, 0);
v_searcher_475_ = lean_ctor_get(v_a_472_, 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_a_472_);
if (v_isSharedCheck_512_ == 0)
{
v___x_477_ = v_a_472_;
v_isShared_478_ = v_isSharedCheck_512_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_searcher_475_);
lean_inc(v_currPos_474_);
lean_dec(v_a_472_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_512_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v_str_479_; lean_object* v_startInclusive_480_; lean_object* v_endExclusive_481_; uint8_t v___x_482_; lean_object* v_it_484_; lean_object* v_startInclusive_485_; lean_object* v_endExclusive_486_; lean_object* v___x_490_; uint8_t v_decide_491_; 
v_str_479_ = lean_ctor_get(v___x_470_, 0);
v_startInclusive_480_ = lean_ctor_get(v___x_470_, 1);
v_endExclusive_481_ = lean_ctor_get(v___x_470_, 2);
v___x_482_ = 1;
v___x_490_ = lean_nat_sub(v_endExclusive_481_, v_startInclusive_480_);
v_decide_491_ = lean_nat_dec_eq(v_searcher_475_, v___x_490_);
lean_dec(v___x_490_);
if (v_decide_491_ == 0)
{
lean_object* v___x_492_; uint32_t v___x_493_; uint32_t v___x_494_; uint8_t v___x_495_; 
v___x_492_ = lean_nat_add(v_startInclusive_480_, v_searcher_475_);
v___x_493_ = lean_string_utf8_get_fast(v_str_479_, v___x_492_);
v___x_494_ = 46;
v___x_495_ = lean_uint32_dec_eq(v___x_493_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
lean_dec(v_searcher_475_);
v___x_496_ = lean_string_utf8_next_fast(v_str_479_, v___x_492_);
lean_dec(v___x_492_);
v___x_497_ = lean_nat_sub(v___x_496_, v_startInclusive_480_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 1, v___x_497_);
v___x_499_ = v___x_477_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_currPos_474_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v___x_497_);
v___x_499_ = v_reuseFailAlloc_501_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
uint8_t v___x_500_; 
v___x_500_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___redArg(v_lower_469_, v___x_470_, v___x_471_, v___x_499_, v_b_473_);
return v___x_500_;
}
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v_slice_505_; lean_object* v_nextIt_507_; 
v___x_502_ = lean_string_utf8_next_fast(v_str_479_, v___x_492_);
v___x_503_ = lean_nat_sub(v___x_502_, v___x_492_);
lean_dec(v___x_492_);
v___x_504_ = lean_nat_add(v_searcher_475_, v___x_503_);
lean_dec(v___x_503_);
v_slice_505_ = l_String_Slice_subslice_x21(v___x_470_, v_currPos_474_, v_searcher_475_);
lean_inc(v___x_504_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 1, v___x_504_);
lean_ctor_set(v___x_477_, 0, v___x_504_);
v_nextIt_507_ = v___x_477_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v___x_504_);
v_nextIt_507_ = v_reuseFailAlloc_510_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v_startInclusive_508_; lean_object* v_endExclusive_509_; 
v_startInclusive_508_ = lean_ctor_get(v_slice_505_, 0);
lean_inc(v_startInclusive_508_);
v_endExclusive_509_ = lean_ctor_get(v_slice_505_, 1);
lean_inc(v_endExclusive_509_);
lean_dec_ref(v_slice_505_);
v_it_484_ = v_nextIt_507_;
v_startInclusive_485_ = v_startInclusive_508_;
v_endExclusive_486_ = v_endExclusive_509_;
goto v___jp_483_;
}
}
}
else
{
lean_object* v___x_511_; 
lean_del_object(v___x_477_);
lean_dec(v_searcher_475_);
v___x_511_ = lean_box(1);
lean_inc(v___x_471_);
v_it_484_ = v___x_511_;
v_startInclusive_485_ = v_currPos_474_;
v_endExclusive_486_ = v___x_471_;
goto v___jp_483_;
}
v___jp_483_:
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = lean_string_utf8_extract_fast(v_lower_469_, v_startInclusive_485_, v_endExclusive_486_);
lean_dec(v_endExclusive_486_);
lean_dec(v_startInclusive_485_);
v___x_488_ = l_Std_Http_URI_isValidDomainLabel(v___x_487_);
if (v___x_488_ == 0)
{
lean_dec(v_it_484_);
lean_dec(v___x_471_);
return v___x_488_;
}
else
{
uint8_t v___x_489_; 
v___x_489_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___redArg(v_lower_469_, v___x_470_, v___x_471_, v_it_484_, v___x_482_);
return v___x_489_;
}
}
}
}
else
{
lean_dec(v___x_471_);
return v_b_473_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg___boxed(lean_object* v_lower_513_, lean_object* v___x_514_, lean_object* v___x_515_, lean_object* v_a_516_, lean_object* v_b_517_){
_start:
{
uint8_t v_b_boxed_518_; uint8_t v_res_519_; lean_object* v_r_520_; 
v_b_boxed_518_ = lean_unbox(v_b_517_);
v_res_519_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v_lower_513_, v___x_514_, v___x_515_, v_a_516_, v_b_boxed_518_);
lean_dec_ref(v___x_514_);
lean_dec_ref(v_lower_513_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1___redArg(lean_object* v___x_521_, lean_object* v___x_522_, lean_object* v_a_523_, uint8_t v_b_524_){
_start:
{
if (lean_obj_tag(v_a_523_) == 0)
{
lean_object* v_currPos_525_; lean_object* v_searcher_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_547_; 
v_currPos_525_ = lean_ctor_get(v_a_523_, 0);
v_searcher_526_ = lean_ctor_get(v_a_523_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_a_523_);
if (v_isSharedCheck_547_ == 0)
{
v___x_528_ = v_a_523_;
v_isShared_529_ = v_isSharedCheck_547_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_searcher_526_);
lean_inc(v_currPos_525_);
lean_dec(v_a_523_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_547_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_str_530_; lean_object* v_startInclusive_531_; lean_object* v_endExclusive_532_; lean_object* v___x_533_; uint8_t v___x_534_; lean_object* v___x_535_; uint8_t v_decide_536_; 
v_str_530_ = lean_ctor_get(v___x_522_, 0);
v_startInclusive_531_ = lean_ctor_get(v___x_522_, 1);
v_endExclusive_532_ = lean_ctor_get(v___x_522_, 2);
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_nat_dec_eq(v___x_521_, v___x_533_);
v___x_535_ = lean_nat_sub(v_endExclusive_532_, v_startInclusive_531_);
v_decide_536_ = lean_nat_dec_eq(v_searcher_526_, v___x_535_);
lean_dec(v___x_535_);
if (v_decide_536_ == 0)
{
uint32_t v___x_537_; lean_object* v___x_538_; uint32_t v___x_539_; uint8_t v___x_540_; 
v___x_537_ = 46;
v___x_538_ = lean_nat_add(v_startInclusive_531_, v_searcher_526_);
lean_dec(v_searcher_526_);
v___x_539_ = lean_string_utf8_get_fast(v_str_530_, v___x_538_);
v___x_540_ = lean_uint32_dec_eq(v___x_539_, v___x_537_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_541_ = lean_string_utf8_next_fast(v_str_530_, v___x_538_);
lean_dec(v___x_538_);
v___x_542_ = lean_nat_sub(v___x_541_, v_startInclusive_531_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 1, v___x_542_);
v___x_544_ = v___x_528_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_currPos_525_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v___x_542_);
v___x_544_ = v_reuseFailAlloc_546_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
v_a_523_ = v___x_544_;
goto _start;
}
}
else
{
lean_dec(v___x_538_);
lean_del_object(v___x_528_);
lean_dec(v_currPos_525_);
return v___x_534_;
}
}
else
{
lean_del_object(v___x_528_);
lean_dec(v_searcher_526_);
lean_dec(v_currPos_525_);
return v___x_534_;
}
}
}
else
{
return v_b_524_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1___redArg___boxed(lean_object* v___x_548_, lean_object* v___x_549_, lean_object* v_a_550_, lean_object* v_b_551_){
_start:
{
uint8_t v_b_boxed_552_; uint8_t v_res_553_; lean_object* v_r_554_; 
v_b_boxed_552_ = lean_unbox(v_b_551_);
v_res_553_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1___redArg(v___x_548_, v___x_549_, v_a_550_, v_b_boxed_552_);
lean_dec_ref(v___x_549_);
lean_dec(v___x_548_);
v_r_554_ = lean_box(v_res_553_);
return v_r_554_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(lean_object* v___x_555_, lean_object* v_lower_556_, lean_object* v___x_557_, lean_object* v___x_558_, lean_object* v_a_559_, uint8_t v_b_560_){
_start:
{
if (lean_obj_tag(v_a_559_) == 0)
{
lean_object* v_currPos_561_; lean_object* v_searcher_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_583_; 
v_currPos_561_ = lean_ctor_get(v_a_559_, 0);
v_searcher_562_ = lean_ctor_get(v_a_559_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v_a_559_);
if (v_isSharedCheck_583_ == 0)
{
v___x_564_ = v_a_559_;
v_isShared_565_ = v_isSharedCheck_583_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_searcher_562_);
lean_inc(v_currPos_561_);
lean_dec(v_a_559_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_583_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v_str_566_; lean_object* v_startInclusive_567_; lean_object* v_endExclusive_568_; lean_object* v___x_569_; uint8_t v___x_570_; lean_object* v___x_571_; uint8_t v_decide_572_; 
v_str_566_ = lean_ctor_get(v___x_557_, 0);
v_startInclusive_567_ = lean_ctor_get(v___x_557_, 1);
v_endExclusive_568_ = lean_ctor_get(v___x_557_, 2);
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = lean_nat_dec_eq(v___x_555_, v___x_569_);
v___x_571_ = lean_nat_sub(v_endExclusive_568_, v_startInclusive_567_);
v_decide_572_ = lean_nat_dec_eq(v_searcher_562_, v___x_571_);
lean_dec(v___x_571_);
if (v_decide_572_ == 0)
{
lean_object* v___x_573_; uint32_t v___x_574_; uint32_t v___x_575_; uint8_t v___x_576_; 
v___x_573_ = lean_nat_add(v_startInclusive_567_, v_searcher_562_);
lean_dec(v_searcher_562_);
v___x_574_ = lean_string_utf8_get_fast(v_str_566_, v___x_573_);
v___x_575_ = 46;
v___x_576_ = lean_uint32_dec_eq(v___x_574_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_577_ = lean_string_utf8_next_fast(v_str_566_, v___x_573_);
lean_dec(v___x_573_);
v___x_578_ = lean_nat_sub(v___x_577_, v_startInclusive_567_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v___x_578_);
v___x_580_ = v___x_564_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_currPos_561_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v___x_578_);
v___x_580_ = v_reuseFailAlloc_582_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
uint8_t v___x_581_; 
v___x_581_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1___redArg(v___x_555_, v___x_557_, v___x_580_, v_b_560_);
return v___x_581_;
}
}
else
{
lean_dec(v___x_573_);
lean_del_object(v___x_564_);
lean_dec(v_currPos_561_);
return v___x_570_;
}
}
else
{
lean_del_object(v___x_564_);
lean_dec(v_searcher_562_);
lean_dec(v_currPos_561_);
return v___x_570_;
}
}
}
else
{
return v_b_560_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg___boxed(lean_object* v___x_584_, lean_object* v_lower_585_, lean_object* v___x_586_, lean_object* v___x_587_, lean_object* v_a_588_, lean_object* v_b_589_){
_start:
{
uint8_t v_b_boxed_590_; uint8_t v_res_591_; lean_object* v_r_592_; 
v_b_boxed_590_ = lean_unbox(v_b_589_);
v_res_591_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_584_, v_lower_585_, v___x_586_, v___x_587_, v_a_588_, v_b_boxed_590_);
lean_dec(v___x_587_);
lean_dec_ref(v___x_586_);
lean_dec_ref(v_lower_585_);
lean_dec(v___x_584_);
v_r_592_ = lean_box(v_res_591_);
return v_r_592_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_DomainName_ofString_x3f(lean_object* v_s_593_){
_start:
{
lean_object* v___x_594_; lean_object* v_lower_595_; uint8_t v___y_597_; uint8_t v___y_598_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_594_ = lean_unsigned_to_nat(0u);
v_lower_595_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_593_, v___x_594_);
v___x_602_ = lean_string_utf8_byte_size(v_lower_595_);
v___x_603_ = lean_nat_dec_eq(v___x_602_, v___x_594_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; uint8_t v___y_608_; uint8_t v___x_613_; 
lean_inc_ref(v_lower_595_);
v___x_604_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_604_, 0, v_lower_595_);
lean_ctor_set(v___x_604_, 1, v___x_594_);
lean_ctor_set(v___x_604_, 2, v___x_602_);
v___x_605_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0);
v___x_606_ = 1;
v___x_613_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_602_, v_lower_595_, v___x_604_, v___x_602_, v___x_605_, v___x_606_);
if (v___x_613_ == 0)
{
v___y_608_ = v___x_606_;
goto v___jp_607_;
}
else
{
v___y_608_ = v___x_603_;
goto v___jp_607_;
}
v___jp_607_:
{
uint8_t v___x_609_; 
v___x_609_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v_lower_595_, v___x_604_, v___x_602_, v___x_605_, v___x_606_);
lean_dec_ref_known(v___x_604_, 3);
if (v___x_609_ == 0)
{
v___y_597_ = v___y_608_;
v___y_598_ = v___x_609_;
goto v___jp_596_;
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_610_ = lean_string_length(v_lower_595_);
v___x_611_ = lean_unsigned_to_nat(255u);
v___x_612_ = lean_nat_dec_le(v___x_610_, v___x_611_);
v___y_597_ = v___y_608_;
v___y_598_ = v___x_612_;
goto v___jp_596_;
}
}
}
else
{
lean_object* v___x_614_; 
lean_dec_ref(v_lower_595_);
v___x_614_ = lean_box(0);
return v___x_614_;
}
v___jp_596_:
{
if (v___y_597_ == 0)
{
lean_object* v___x_599_; 
lean_dec_ref(v_lower_595_);
v___x_599_ = lean_box(0);
return v___x_599_;
}
else
{
if (v___y_598_ == 0)
{
lean_object* v___x_600_; 
lean_dec_ref(v_lower_595_);
v___x_600_ = lean_box(0);
return v___x_600_;
}
else
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_lower_595_);
return v___x_601_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(lean_object* v___x_615_, lean_object* v_lower_616_, lean_object* v___x_617_, lean_object* v___x_618_, lean_object* v_inst_619_, lean_object* v_R_620_, lean_object* v_a_621_, uint8_t v_b_622_, lean_object* v_c_623_){
_start:
{
uint8_t v___x_624_; 
v___x_624_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_615_, v_lower_616_, v___x_617_, v___x_618_, v_a_621_, v_b_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___boxed(lean_object* v___x_625_, lean_object* v_lower_626_, lean_object* v___x_627_, lean_object* v___x_628_, lean_object* v_inst_629_, lean_object* v_R_630_, lean_object* v_a_631_, lean_object* v_b_632_, lean_object* v_c_633_){
_start:
{
uint8_t v_b_boxed_634_; uint8_t v_res_635_; lean_object* v_r_636_; 
v_b_boxed_634_ = lean_unbox(v_b_632_);
v_res_635_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(v___x_625_, v_lower_626_, v___x_627_, v___x_628_, v_inst_629_, v_R_630_, v_a_631_, v_b_boxed_634_, v_c_633_);
lean_dec(v___x_628_);
lean_dec_ref(v___x_627_);
lean_dec_ref(v_lower_626_);
lean_dec(v___x_625_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(lean_object* v_lower_637_, lean_object* v___x_638_, lean_object* v___x_639_, lean_object* v_inst_640_, lean_object* v_R_641_, lean_object* v_a_642_, uint8_t v_b_643_, lean_object* v_c_644_){
_start:
{
uint8_t v___x_645_; 
v___x_645_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v_lower_637_, v___x_638_, v___x_639_, v_a_642_, v_b_643_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___boxed(lean_object* v_lower_646_, lean_object* v___x_647_, lean_object* v___x_648_, lean_object* v_inst_649_, lean_object* v_R_650_, lean_object* v_a_651_, lean_object* v_b_652_, lean_object* v_c_653_){
_start:
{
uint8_t v_b_boxed_654_; uint8_t v_res_655_; lean_object* v_r_656_; 
v_b_boxed_654_ = lean_unbox(v_b_652_);
v_res_655_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(v_lower_646_, v___x_647_, v___x_648_, v_inst_649_, v_R_650_, v_a_651_, v_b_boxed_654_, v_c_653_);
lean_dec_ref(v___x_647_);
lean_dec_ref(v_lower_646_);
v_r_656_ = lean_box(v_res_655_);
return v_r_656_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1(lean_object* v___x_657_, lean_object* v_lower_658_, lean_object* v___x_659_, lean_object* v___x_660_, lean_object* v_inst_661_, lean_object* v_R_662_, lean_object* v_a_663_, uint8_t v_b_664_, lean_object* v_c_665_){
_start:
{
uint8_t v___x_666_; 
v___x_666_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1___redArg(v___x_657_, v___x_659_, v_a_663_, v_b_664_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1___boxed(lean_object* v___x_667_, lean_object* v_lower_668_, lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v_inst_671_, lean_object* v_R_672_, lean_object* v_a_673_, lean_object* v_b_674_, lean_object* v_c_675_){
_start:
{
uint8_t v_b_boxed_676_; uint8_t v_res_677_; lean_object* v_r_678_; 
v_b_boxed_676_ = lean_unbox(v_b_674_);
v_res_677_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1(v___x_667_, v_lower_668_, v___x_669_, v___x_670_, v_inst_671_, v_R_672_, v_a_673_, v_b_boxed_676_, v_c_675_);
lean_dec(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v_lower_668_);
lean_dec(v___x_667_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3(lean_object* v_lower_679_, lean_object* v___x_680_, lean_object* v___x_681_, lean_object* v_inst_682_, lean_object* v_R_683_, lean_object* v_a_684_, uint8_t v_b_685_, lean_object* v_c_686_){
_start:
{
uint8_t v___x_687_; 
v___x_687_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___redArg(v_lower_679_, v___x_680_, v___x_681_, v_a_684_, v_b_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___boxed(lean_object* v_lower_688_, lean_object* v___x_689_, lean_object* v___x_690_, lean_object* v_inst_691_, lean_object* v_R_692_, lean_object* v_a_693_, lean_object* v_b_694_, lean_object* v_c_695_){
_start:
{
uint8_t v_b_boxed_696_; uint8_t v_res_697_; lean_object* v_r_698_; 
v_b_boxed_696_ = lean_unbox(v_b_694_);
v_res_697_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3(v_lower_688_, v___x_689_, v___x_690_, v_inst_691_, v_R_692_, v_a_693_, v_b_boxed_696_, v_c_695_);
lean_dec_ref(v___x_689_);
lean_dec_ref(v_lower_688_);
v_r_698_ = lean_box(v_res_697_);
return v_r_698_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx(lean_object* v_x_699_){
_start:
{
switch(lean_obj_tag(v_x_699_))
{
case 0:
{
lean_object* v___x_700_; 
v___x_700_ = lean_unsigned_to_nat(0u);
return v___x_700_;
}
case 1:
{
lean_object* v___x_701_; 
v___x_701_ = lean_unsigned_to_nat(1u);
return v___x_701_;
}
default: 
{
lean_object* v___x_702_; 
v___x_702_ = lean_unsigned_to_nat(2u);
return v___x_702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx___boxed(lean_object* v_x_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_Http_URI_Host_ctorIdx(v_x_703_);
lean_dec_ref(v_x_703_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___redArg(lean_object* v_t_705_, lean_object* v_k_706_){
_start:
{
lean_object* v_name_707_; lean_object* v___x_708_; 
v_name_707_ = lean_ctor_get(v_t_705_, 0);
lean_inc_ref(v_name_707_);
lean_dec_ref(v_t_705_);
v___x_708_ = lean_apply_1(v_k_706_, v_name_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim(lean_object* v_motive_709_, lean_object* v_ctorIdx_710_, lean_object* v_t_711_, lean_object* v_h_712_, lean_object* v_k_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_711_, v_k_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___boxed(lean_object* v_motive_715_, lean_object* v_ctorIdx_716_, lean_object* v_t_717_, lean_object* v_h_718_, lean_object* v_k_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_Http_URI_Host_ctorElim(v_motive_715_, v_ctorIdx_716_, v_t_717_, v_h_718_, v_k_719_);
lean_dec(v_ctorIdx_716_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim___redArg(lean_object* v_t_721_, lean_object* v_name_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_721_, v_name_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim(lean_object* v_motive_724_, lean_object* v_t_725_, lean_object* v_h_726_, lean_object* v_name_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_725_, v_name_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim___redArg(lean_object* v_t_729_, lean_object* v_ipv4_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_729_, v_ipv4_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim(lean_object* v_motive_732_, lean_object* v_t_733_, lean_object* v_h_734_, lean_object* v_ipv4_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_733_, v_ipv4_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim___redArg(lean_object* v_t_737_, lean_object* v_ipv6_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_737_, v_ipv6_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim(lean_object* v_motive_740_, lean_object* v_t_741_, lean_object* v_h_742_, lean_object* v_ipv6_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_741_, v_ipv6_743_);
return v___x_744_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default___closed__0(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default(void){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = lean_obj_once(&l_Std_Http_URI_instInhabitedHost_default___closed__0, &l_Std_Http_URI_instInhabitedHost_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedHost_default___closed__0);
return v___x_747_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost(void){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Std_Http_URI_instInhabitedHost_default;
return v___x_748_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqHost_beq(lean_object* v_x_749_, lean_object* v_x_750_){
_start:
{
switch(lean_obj_tag(v_x_749_))
{
case 0:
{
if (lean_obj_tag(v_x_750_) == 0)
{
lean_object* v_name_751_; lean_object* v_name_752_; uint8_t v___x_753_; 
v_name_751_ = lean_ctor_get(v_x_749_, 0);
v_name_752_ = lean_ctor_get(v_x_750_, 0);
v___x_753_ = lean_string_dec_eq(v_name_751_, v_name_752_);
return v___x_753_;
}
else
{
uint8_t v___x_754_; 
v___x_754_ = 0;
return v___x_754_;
}
}
case 1:
{
if (lean_obj_tag(v_x_750_) == 1)
{
lean_object* v_ipv4_755_; lean_object* v_ipv4_756_; uint8_t v___x_757_; 
v_ipv4_755_ = lean_ctor_get(v_x_749_, 0);
v_ipv4_756_ = lean_ctor_get(v_x_750_, 0);
v___x_757_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_ipv4_755_, v_ipv4_756_);
return v___x_757_;
}
else
{
uint8_t v___x_758_; 
v___x_758_ = 0;
return v___x_758_;
}
}
default: 
{
if (lean_obj_tag(v_x_750_) == 2)
{
lean_object* v_ipv6_759_; lean_object* v_ipv6_760_; uint8_t v___x_761_; 
v_ipv6_759_ = lean_ctor_get(v_x_749_, 0);
v_ipv6_760_ = lean_ctor_get(v_x_750_, 0);
v___x_761_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_ipv6_759_, v_ipv6_760_);
return v___x_761_;
}
else
{
uint8_t v___x_762_; 
v___x_762_ = 0;
return v___x_762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqHost_beq___boxed(lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
uint8_t v_res_765_; lean_object* v_r_766_; 
v_res_765_ = l_Std_Http_URI_instBEqHost_beq(v_x_763_, v_x_764_);
lean_dec_ref(v_x_764_);
lean_dec_ref(v_x_763_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__4(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_unsigned_to_nat(2u);
v___x_774_ = lean_nat_to_int(v___x_773_);
return v___x_774_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__5(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_unsigned_to_nat(1u);
v___x_776_ = lean_nat_to_int(v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0(lean_object* v_x_777_, lean_object* v_prec_778_){
_start:
{
lean_object* v___y_780_; lean_object* v_ctr_781_; lean_object* v_a_782_; lean_object* v___y_794_; lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_825_ = lean_unsigned_to_nat(1024u);
v___x_826_ = lean_nat_dec_le(v___x_825_, v_prec_778_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; 
v___x_827_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_794_ = v___x_827_;
goto v___jp_793_;
}
else
{
lean_object* v___x_828_; 
v___x_828_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_794_ = v___x_828_;
goto v___jp_793_;
}
v___jp_779_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_783_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_784_ = lean_string_append(v___x_783_, v_ctr_781_);
v___x_785_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
v___x_786_ = lean_box(1);
v___x_787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v_a_782_);
lean_inc(v___y_780_);
v___x_789_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_789_, 0, v___y_780_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = 0;
v___x_791_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_791_, 0, v___x_789_);
lean_ctor_set_uint8(v___x_791_, sizeof(void*)*1, v___x_790_);
v___x_792_ = l_Repr_addAppParen(v___x_791_, v_prec_778_);
return v___x_792_;
}
v___jp_793_:
{
switch(lean_obj_tag(v_x_777_))
{
case 0:
{
lean_object* v_name_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_804_; 
v_name_795_ = lean_ctor_get(v_x_777_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_804_ == 0)
{
v___x_797_ = v_x_777_;
v_isShared_798_ = v_isSharedCheck_804_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_name_795_);
lean_dec(v_x_777_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_804_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_799_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_800_ = l_String_quote(v_name_795_);
if (v_isShared_798_ == 0)
{
lean_ctor_set_tag(v___x_797_, 3);
lean_ctor_set(v___x_797_, 0, v___x_800_);
v___x_802_ = v___x_797_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
v___y_780_ = v___y_794_;
v_ctr_781_ = v___x_799_;
v_a_782_ = v___x_802_;
goto v___jp_779_;
}
}
}
case 1:
{
lean_object* v_ipv4_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_814_; 
v_ipv4_805_ = lean_ctor_get(v_x_777_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_814_ == 0)
{
v___x_807_ = v_x_777_;
v_isShared_808_ = v_isSharedCheck_814_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_ipv4_805_);
lean_dec(v_x_777_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_814_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_809_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_810_ = lean_uv_ntop_v4(v_ipv4_805_);
lean_dec_ref(v_ipv4_805_);
if (v_isShared_808_ == 0)
{
lean_ctor_set_tag(v___x_807_, 3);
lean_ctor_set(v___x_807_, 0, v___x_810_);
v___x_812_ = v___x_807_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
v___y_780_ = v___y_794_;
v_ctr_781_ = v___x_809_;
v_a_782_ = v___x_812_;
goto v___jp_779_;
}
}
}
default: 
{
lean_object* v_ipv6_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_824_; 
v_ipv6_815_ = lean_ctor_get(v_x_777_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_824_ == 0)
{
v___x_817_ = v_x_777_;
v_isShared_818_ = v_isSharedCheck_824_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_ipv6_815_);
lean_dec(v_x_777_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_824_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_819_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_820_ = lean_uv_ntop_v6(v_ipv6_815_);
lean_dec_ref(v_ipv6_815_);
if (v_isShared_818_ == 0)
{
lean_ctor_set_tag(v___x_817_, 3);
lean_ctor_set(v___x_817_, 0, v___x_820_);
v___x_822_ = v___x_817_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
v___y_780_ = v___y_794_;
v_ctr_781_ = v___x_819_;
v_a_782_ = v___x_822_;
goto v___jp_779_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0___boxed(lean_object* v_x_829_, lean_object* v_prec_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Std_Http_URI_instReprHost___lam__0(v_x_829_, v_prec_830_);
lean_dec(v_prec_830_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0(lean_object* v_x_836_){
_start:
{
switch(lean_obj_tag(v_x_836_))
{
case 0:
{
lean_object* v_name_837_; 
v_name_837_ = lean_ctor_get(v_x_836_, 0);
lean_inc_ref(v_name_837_);
return v_name_837_;
}
case 1:
{
lean_object* v_ipv4_838_; lean_object* v___x_839_; 
v_ipv4_838_ = lean_ctor_get(v_x_836_, 0);
v___x_839_ = lean_uv_ntop_v4(v_ipv4_838_);
return v___x_839_;
}
default: 
{
lean_object* v_ipv6_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_ipv6_840_ = lean_ctor_get(v_x_836_, 0);
v___x_841_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_842_ = lean_uv_ntop_v6(v_ipv6_840_);
v___x_843_ = lean_string_append(v___x_841_, v___x_842_);
lean_dec_ref(v___x_842_);
v___x_844_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_845_ = lean_string_append(v___x_843_, v___x_844_);
return v___x_845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0___boxed(lean_object* v_x_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Std_Http_URI_instToStringHost___lam__0(v_x_846_);
lean_dec_ref(v_x_846_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx(lean_object* v_x_850_){
_start:
{
switch(lean_obj_tag(v_x_850_))
{
case 0:
{
lean_object* v___x_851_; 
v___x_851_ = lean_unsigned_to_nat(0u);
return v___x_851_;
}
case 1:
{
lean_object* v___x_852_; 
v___x_852_ = lean_unsigned_to_nat(1u);
return v___x_852_;
}
default: 
{
lean_object* v___x_853_; 
v___x_853_ = lean_unsigned_to_nat(2u);
return v___x_853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___boxed(lean_object* v_x_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Std_Http_URI_Port_ctorIdx(v_x_854_);
lean_dec(v_x_854_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg(lean_object* v_t_856_, lean_object* v_k_857_){
_start:
{
if (lean_obj_tag(v_t_856_) == 2)
{
uint16_t v_port_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_port_858_ = lean_ctor_get_uint16(v_t_856_, 0);
v___x_859_ = lean_box(v_port_858_);
v___x_860_ = lean_apply_1(v_k_857_, v___x_859_);
return v___x_860_;
}
else
{
return v_k_857_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg___boxed(lean_object* v_t_861_, lean_object* v_k_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_861_, v_k_862_);
lean_dec(v_t_861_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim(lean_object* v_motive_864_, lean_object* v_ctorIdx_865_, lean_object* v_t_866_, lean_object* v_h_867_, lean_object* v_k_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_866_, v_k_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___boxed(lean_object* v_motive_870_, lean_object* v_ctorIdx_871_, lean_object* v_t_872_, lean_object* v_h_873_, lean_object* v_k_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Std_Http_URI_Port_ctorElim(v_motive_870_, v_ctorIdx_871_, v_t_872_, v_h_873_, v_k_874_);
lean_dec(v_t_872_);
lean_dec(v_ctorIdx_871_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg(lean_object* v_t_876_, lean_object* v_omitted_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_876_, v_omitted_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg___boxed(lean_object* v_t_879_, lean_object* v_omitted_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Std_Http_URI_Port_omitted_elim___redArg(v_t_879_, v_omitted_880_);
lean_dec(v_t_879_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim(lean_object* v_motive_882_, lean_object* v_t_883_, lean_object* v_h_884_, lean_object* v_omitted_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_883_, v_omitted_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___boxed(lean_object* v_motive_887_, lean_object* v_t_888_, lean_object* v_h_889_, lean_object* v_omitted_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Std_Http_URI_Port_omitted_elim(v_motive_887_, v_t_888_, v_h_889_, v_omitted_890_);
lean_dec(v_t_888_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg(lean_object* v_t_892_, lean_object* v_empty_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_892_, v_empty_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg___boxed(lean_object* v_t_895_, lean_object* v_empty_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Std_Http_URI_Port_empty_elim___redArg(v_t_895_, v_empty_896_);
lean_dec(v_t_895_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim(lean_object* v_motive_898_, lean_object* v_t_899_, lean_object* v_h_900_, lean_object* v_empty_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_899_, v_empty_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___boxed(lean_object* v_motive_903_, lean_object* v_t_904_, lean_object* v_h_905_, lean_object* v_empty_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Std_Http_URI_Port_empty_elim(v_motive_903_, v_t_904_, v_h_905_, v_empty_906_);
lean_dec(v_t_904_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg(lean_object* v_t_908_, lean_object* v_value_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_908_, v_value_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg___boxed(lean_object* v_t_911_, lean_object* v_value_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Std_Http_URI_Port_value_elim___redArg(v_t_911_, v_value_912_);
lean_dec(v_t_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim(lean_object* v_motive_914_, lean_object* v_t_915_, lean_object* v_h_916_, lean_object* v_value_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_915_, v_value_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___boxed(lean_object* v_motive_919_, lean_object* v_t_920_, lean_object* v_h_921_, lean_object* v_value_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_Http_URI_Port_value_elim(v_motive_919_, v_t_920_, v_h_921_, v_value_922_);
lean_dec(v_t_920_);
return v_res_923_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort_default(void){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_box(0);
return v___x_924_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort(void){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = lean_box(0);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr(lean_object* v_x_938_, lean_object* v_prec_939_){
_start:
{
lean_object* v___y_941_; lean_object* v___y_948_; 
switch(lean_obj_tag(v_x_938_))
{
case 0:
{
lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_954_ = lean_unsigned_to_nat(1024u);
v___x_955_ = lean_nat_dec_le(v___x_954_, v_prec_939_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
v___x_956_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_948_ = v___x_956_;
goto v___jp_947_;
}
else
{
lean_object* v___x_957_; 
v___x_957_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_948_ = v___x_957_;
goto v___jp_947_;
}
}
case 1:
{
lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_958_ = lean_unsigned_to_nat(1024u);
v___x_959_ = lean_nat_dec_le(v___x_958_, v_prec_939_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; 
v___x_960_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_941_ = v___x_960_;
goto v___jp_940_;
}
else
{
lean_object* v___x_961_; 
v___x_961_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_941_ = v___x_961_;
goto v___jp_940_;
}
}
default: 
{
uint16_t v_port_962_; lean_object* v___y_964_; lean_object* v___x_974_; uint8_t v___x_975_; 
v_port_962_ = lean_ctor_get_uint16(v_x_938_, 0);
v___x_974_ = lean_unsigned_to_nat(1024u);
v___x_975_ = lean_nat_dec_le(v___x_974_, v_prec_939_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; 
v___x_976_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_964_ = v___x_976_;
goto v___jp_963_;
}
else
{
lean_object* v___x_977_; 
v___x_977_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_964_ = v___x_977_;
goto v___jp_963_;
}
v___jp_963_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_965_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__6));
v___x_966_ = lean_uint16_to_nat(v_port_962_);
v___x_967_ = l_Nat_reprFast(v___x_966_);
v___x_968_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
v___x_969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_965_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
lean_inc(v___y_964_);
v___x_970_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_970_, 0, v___y_964_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = 0;
v___x_972_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*1, v___x_971_);
v___x_973_ = l_Repr_addAppParen(v___x_972_, v_prec_939_);
return v___x_973_;
}
}
}
v___jp_940_:
{
lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_942_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__1));
lean_inc(v___y_941_);
v___x_943_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_943_, 0, v___y_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = 0;
v___x_945_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*1, v___x_944_);
v___x_946_ = l_Repr_addAppParen(v___x_945_, v_prec_939_);
return v___x_946_;
}
v___jp_947_:
{
lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_949_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__3));
lean_inc(v___y_948_);
v___x_950_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_950_, 0, v___y_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = 0;
v___x_952_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set_uint8(v___x_952_, sizeof(void*)*1, v___x_951_);
v___x_953_ = l_Repr_addAppParen(v___x_952_, v_prec_939_);
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr___boxed(lean_object* v_x_978_, lean_object* v_prec_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Std_Http_URI_instReprPort_repr(v_x_978_, v_prec_979_);
lean_dec(v_prec_979_);
lean_dec(v_x_978_);
return v_res_980_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort_decEq(lean_object* v_x_983_, lean_object* v_x_984_){
_start:
{
switch(lean_obj_tag(v_x_983_))
{
case 0:
{
if (lean_obj_tag(v_x_984_) == 0)
{
uint8_t v___x_985_; 
v___x_985_ = 1;
return v___x_985_;
}
else
{
uint8_t v___x_986_; 
v___x_986_ = 0;
return v___x_986_;
}
}
case 1:
{
if (lean_obj_tag(v_x_984_) == 1)
{
uint8_t v___x_987_; 
v___x_987_ = 1;
return v___x_987_;
}
else
{
uint8_t v___x_988_; 
v___x_988_ = 0;
return v___x_988_;
}
}
default: 
{
if (lean_obj_tag(v_x_984_) == 2)
{
uint16_t v_port_989_; uint16_t v_port_990_; uint8_t v___x_991_; 
v_port_989_ = lean_ctor_get_uint16(v_x_983_, 0);
v_port_990_ = lean_ctor_get_uint16(v_x_984_, 0);
v___x_991_ = lean_uint16_dec_eq(v_port_989_, v_port_990_);
return v___x_991_;
}
else
{
uint8_t v___x_992_; 
v___x_992_ = 0;
return v___x_992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort_decEq___boxed(lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
uint8_t v_res_995_; lean_object* v_r_996_; 
v_res_995_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_993_, v_x_994_);
lean_dec(v_x_994_);
lean_dec(v_x_993_);
v_r_996_ = lean_box(v_res_995_);
return v_r_996_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort(lean_object* v_x_997_, lean_object* v_x_998_){
_start:
{
uint8_t v___x_999_; 
v___x_999_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_997_, v_x_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort___boxed(lean_object* v_x_1000_, lean_object* v_x_1001_){
_start:
{
uint8_t v_res_1002_; lean_object* v_r_1003_; 
v_res_1002_ = l_Std_Http_URI_instDecidableEqPort(v_x_1000_, v_x_1001_);
lean_dec(v_x_1001_);
lean_dec(v_x_1000_);
v_r_1003_ = lean_box(v_res_1002_);
return v_r_1003_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1004_ = lean_box(0);
v___x_1005_ = l_Std_Http_URI_instInhabitedHost_default;
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_1005_);
lean_ctor_set(v___x_1007_, 2, v___x_1004_);
return v___x_1007_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default(void){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_obj_once(&l_Std_Http_URI_instInhabitedAuthority_default___closed__0, &l_Std_Http_URI_instInhabitedAuthority_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0);
return v___x_1008_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority(void){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Std_Http_URI_instInhabitedAuthority_default;
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
if (lean_obj_tag(v_x_1010_) == 0)
{
lean_object* v___x_1012_; 
v___x_1012_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1012_;
}
else
{
lean_object* v_val_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_val_1013_ = lean_ctor_get(v_x_1010_, 0);
lean_inc(v_val_1013_);
lean_dec_ref_known(v_x_1010_, 1);
v___x_1014_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1015_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_val_1013_);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_Repr_addAppParen(v___x_1016_, v_x_1011_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0___boxed(lean_object* v_x_1018_, lean_object* v_x_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_x_1018_, v_x_1019_);
lean_dec(v_x_1019_);
return v_res_1020_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = lean_unsigned_to_nat(8u);
v___x_1034_ = lean_nat_to_int(v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg(lean_object* v_x_1038_){
_start:
{
lean_object* v_userInfo_1039_; lean_object* v_host_1040_; lean_object* v_port_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v_ctr_1061_; lean_object* v_a_1062_; 
v_userInfo_1039_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_userInfo_1039_);
v_host_1040_ = lean_ctor_get(v_x_1038_, 1);
lean_inc_ref(v_host_1040_);
v_port_1041_ = lean_ctor_get(v_x_1038_, 2);
lean_inc(v_port_1041_);
lean_dec_ref(v_x_1038_);
v___x_1042_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1043_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3));
v___x_1044_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_userInfo_1039_, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1044_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = 0;
v___x_1049_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set_uint8(v___x_1049_, sizeof(void*)*1, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1043_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_box(1);
v___x_1054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_1056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v___x_1042_);
v___x_1058_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_1059_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_1040_))
{
case 0:
{
lean_object* v_name_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1099_; 
v_name_1090_ = lean_ctor_get(v_host_1040_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_host_1040_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1092_ = v_host_1040_;
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_name_1090_);
lean_dec(v_host_1040_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1094_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_1095_ = l_String_quote(v_name_1090_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 3);
lean_ctor_set(v___x_1092_, 0, v___x_1095_);
v___x_1097_ = v___x_1092_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
v_ctr_1061_ = v___x_1094_;
v_a_1062_ = v___x_1097_;
goto v___jp_1060_;
}
}
}
case 1:
{
lean_object* v_ipv4_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1109_; 
v_ipv4_1100_ = lean_ctor_get(v_host_1040_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_host_1040_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1102_ = v_host_1040_;
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_ipv4_1100_);
lean_dec(v_host_1040_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1104_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_1105_ = lean_uv_ntop_v4(v_ipv4_1100_);
lean_dec_ref(v_ipv4_1100_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set_tag(v___x_1102_, 3);
lean_ctor_set(v___x_1102_, 0, v___x_1105_);
v___x_1107_ = v___x_1102_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
v_ctr_1061_ = v___x_1104_;
v_a_1062_ = v___x_1107_;
goto v___jp_1060_;
}
}
}
default: 
{
lean_object* v_ipv6_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1119_; 
v_ipv6_1110_ = lean_ctor_get(v_host_1040_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_host_1040_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1112_ = v_host_1040_;
v_isShared_1113_ = v_isSharedCheck_1119_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_ipv6_1110_);
lean_dec(v_host_1040_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1119_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1114_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_1115_ = lean_uv_ntop_v6(v_ipv6_1110_);
lean_dec_ref(v_ipv6_1110_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set_tag(v___x_1112_, 3);
lean_ctor_set(v___x_1112_, 0, v___x_1115_);
v___x_1117_ = v___x_1112_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
v_ctr_1061_ = v___x_1114_;
v_a_1062_ = v___x_1117_;
goto v___jp_1060_;
}
}
}
}
v___jp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1063_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_1064_ = lean_string_append(v___x_1063_, v_ctr_1061_);
v___x_1065_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v___x_1053_);
v___x_1067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v_a_1062_);
v___x_1068_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1059_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*1, v___x_1048_);
v___x_1070_ = l_Repr_addAppParen(v___x_1069_, v___x_1045_);
v___x_1071_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1058_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set_uint8(v___x_1072_, sizeof(void*)*1, v___x_1048_);
v___x_1073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1057_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v___x_1051_);
v___x_1075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v___x_1053_);
v___x_1076_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_1077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_1042_);
v___x_1079_ = l_Std_Http_URI_instReprPort_repr(v_port_1041_, v___x_1045_);
lean_dec(v_port_1041_);
v___x_1080_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1058_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set_uint8(v___x_1081_, sizeof(void*)*1, v___x_1048_);
v___x_1082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1078_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1084_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set(v___x_1085_, 1, v___x_1082_);
v___x_1086_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1083_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*1, v___x_1048_);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr(lean_object* v_x_1120_, lean_object* v_prec_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_x_1120_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___boxed(lean_object* v_x_1123_, lean_object* v_prec_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Std_Http_URI_instReprAuthority_repr(v_x_1123_, v_prec_1124_);
lean_dec(v_prec_1124_);
return v_res_1125_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
if (lean_obj_tag(v_x_1128_) == 0)
{
if (lean_obj_tag(v_x_1129_) == 0)
{
uint8_t v___x_1130_; 
v___x_1130_ = 1;
return v___x_1130_;
}
else
{
uint8_t v___x_1131_; 
v___x_1131_ = 0;
return v___x_1131_;
}
}
else
{
if (lean_obj_tag(v_x_1129_) == 0)
{
uint8_t v___x_1132_; 
v___x_1132_ = 0;
return v___x_1132_;
}
else
{
lean_object* v_val_1133_; lean_object* v_val_1134_; uint8_t v___x_1135_; 
v_val_1133_ = lean_ctor_get(v_x_1128_, 0);
v_val_1134_ = lean_ctor_get(v_x_1129_, 0);
v___x_1135_ = l_Std_Http_URI_instBEqUserInfo_beq(v_val_1133_, v_val_1134_);
return v___x_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0___boxed(lean_object* v_x_1136_, lean_object* v_x_1137_){
_start:
{
uint8_t v_res_1138_; lean_object* v_r_1139_; 
v_res_1138_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_x_1136_, v_x_1137_);
lean_dec(v_x_1137_);
lean_dec(v_x_1136_);
v_r_1139_ = lean_box(v_res_1138_);
return v_r_1139_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqAuthority_beq(lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
lean_object* v_userInfo_1142_; lean_object* v_host_1143_; lean_object* v_port_1144_; lean_object* v_userInfo_1145_; lean_object* v_host_1146_; lean_object* v_port_1147_; uint8_t v___x_1148_; 
v_userInfo_1142_ = lean_ctor_get(v_x_1140_, 0);
v_host_1143_ = lean_ctor_get(v_x_1140_, 1);
v_port_1144_ = lean_ctor_get(v_x_1140_, 2);
v_userInfo_1145_ = lean_ctor_get(v_x_1141_, 0);
v_host_1146_ = lean_ctor_get(v_x_1141_, 1);
v_port_1147_ = lean_ctor_get(v_x_1141_, 2);
v___x_1148_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_userInfo_1142_, v_userInfo_1145_);
if (v___x_1148_ == 0)
{
return v___x_1148_;
}
else
{
uint8_t v___x_1149_; 
v___x_1149_ = l_Std_Http_URI_instBEqHost_beq(v_host_1143_, v_host_1146_);
if (v___x_1149_ == 0)
{
return v___x_1149_;
}
else
{
uint8_t v___x_1150_; 
v___x_1150_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1144_, v_port_1147_);
return v___x_1150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqAuthority_beq___boxed(lean_object* v_x_1151_, lean_object* v_x_1152_){
_start:
{
uint8_t v_res_1153_; lean_object* v_r_1154_; 
v_res_1153_ = l_Std_Http_URI_instBEqAuthority_beq(v_x_1151_, v_x_1152_);
lean_dec_ref(v_x_1152_);
lean_dec_ref(v_x_1151_);
v_r_1154_ = lean_box(v_res_1153_);
return v_r_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringAuthority___lam__0(lean_object* v_auth_1160_){
_start:
{
lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v_userInfo_1167_; lean_object* v_host_1168_; lean_object* v_port_1169_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1181_; 
v_userInfo_1167_ = lean_ctor_get(v_auth_1160_, 0);
lean_inc(v_userInfo_1167_);
v_host_1168_ = lean_ctor_get(v_auth_1160_, 1);
lean_inc_ref(v_host_1168_);
v_port_1169_ = lean_ctor_get(v_auth_1160_, 2);
lean_inc(v_port_1169_);
lean_dec_ref(v_auth_1160_);
if (lean_obj_tag(v_userInfo_1167_) == 0)
{
lean_object* v___x_1191_; 
v___x_1191_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1181_ = v___x_1191_;
goto v___jp_1180_;
}
else
{
lean_object* v_val_1192_; lean_object* v_password_1193_; 
v_val_1192_ = lean_ctor_get(v_userInfo_1167_, 0);
lean_inc(v_val_1192_);
lean_dec_ref_known(v_userInfo_1167_, 1);
v_password_1193_ = lean_ctor_get(v_val_1192_, 1);
if (lean_obj_tag(v_password_1193_) == 0)
{
lean_object* v_username_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v_username_1194_ = lean_ctor_get(v_val_1192_, 0);
lean_inc_ref(v_username_1194_);
lean_dec(v_val_1192_);
v___x_1195_ = lean_string_from_utf8_unchecked(v_username_1194_);
v___x_1196_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1197_ = lean_string_append(v___x_1195_, v___x_1196_);
v___y_1181_ = v___x_1197_;
goto v___jp_1180_;
}
else
{
lean_object* v_username_1198_; lean_object* v_val_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_inc_ref(v_password_1193_);
v_username_1198_ = lean_ctor_get(v_val_1192_, 0);
lean_inc_ref(v_username_1198_);
lean_dec(v_val_1192_);
v_val_1199_ = lean_ctor_get(v_password_1193_, 0);
lean_inc(v_val_1199_);
lean_dec_ref_known(v_password_1193_, 1);
v___x_1200_ = lean_string_from_utf8_unchecked(v_username_1198_);
v___x_1201_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1202_ = lean_string_append(v___x_1200_, v___x_1201_);
v___x_1203_ = lean_string_from_utf8_unchecked(v_val_1199_);
v___x_1204_ = lean_string_append(v___x_1202_, v___x_1203_);
lean_dec_ref(v___x_1203_);
v___x_1205_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1206_ = lean_string_append(v___x_1204_, v___x_1205_);
v___y_1181_ = v___x_1206_;
goto v___jp_1180_;
}
}
v___jp_1161_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_string_append(v___y_1162_, v___y_1163_);
lean_dec_ref(v___y_1163_);
v___x_1166_ = lean_string_append(v___x_1165_, v___y_1164_);
lean_dec_ref(v___y_1164_);
return v___x_1166_;
}
v___jp_1170_:
{
switch(lean_obj_tag(v_port_1169_))
{
case 0:
{
lean_object* v___x_1173_; 
v___x_1173_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1162_ = v___y_1171_;
v___y_1163_ = v___y_1172_;
v___y_1164_ = v___x_1173_;
goto v___jp_1161_;
}
case 1:
{
lean_object* v___x_1174_; 
v___x_1174_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_1162_ = v___y_1171_;
v___y_1163_ = v___y_1172_;
v___y_1164_ = v___x_1174_;
goto v___jp_1161_;
}
default: 
{
uint16_t v_port_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_port_1175_ = lean_ctor_get_uint16(v_port_1169_, 0);
lean_dec_ref_known(v_port_1169_, 0);
v___x_1176_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1177_ = lean_uint16_to_nat(v_port_1175_);
v___x_1178_ = l_Nat_reprFast(v___x_1177_);
v___x_1179_ = lean_string_append(v___x_1176_, v___x_1178_);
lean_dec_ref(v___x_1178_);
v___y_1162_ = v___y_1171_;
v___y_1163_ = v___y_1172_;
v___y_1164_ = v___x_1179_;
goto v___jp_1161_;
}
}
}
v___jp_1180_:
{
switch(lean_obj_tag(v_host_1168_))
{
case 0:
{
lean_object* v_name_1182_; 
v_name_1182_ = lean_ctor_get(v_host_1168_, 0);
lean_inc_ref(v_name_1182_);
lean_dec_ref_known(v_host_1168_, 1);
v___y_1171_ = v___y_1181_;
v___y_1172_ = v_name_1182_;
goto v___jp_1170_;
}
case 1:
{
lean_object* v_ipv4_1183_; lean_object* v___x_1184_; 
v_ipv4_1183_ = lean_ctor_get(v_host_1168_, 0);
lean_inc_ref(v_ipv4_1183_);
lean_dec_ref_known(v_host_1168_, 1);
v___x_1184_ = lean_uv_ntop_v4(v_ipv4_1183_);
lean_dec_ref(v_ipv4_1183_);
v___y_1171_ = v___y_1181_;
v___y_1172_ = v___x_1184_;
goto v___jp_1170_;
}
default: 
{
lean_object* v_ipv6_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v_ipv6_1185_ = lean_ctor_get(v_host_1168_, 0);
lean_inc_ref(v_ipv6_1185_);
lean_dec_ref_known(v_host_1168_, 1);
v___x_1186_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_1187_ = lean_uv_ntop_v6(v_ipv6_1185_);
lean_dec_ref(v_ipv6_1185_);
v___x_1188_ = lean_string_append(v___x_1186_, v___x_1187_);
lean_dec_ref(v___x_1187_);
v___x_1189_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_1190_ = lean_string_append(v___x_1188_, v___x_1189_);
v___y_1171_ = v___y_1181_;
v___y_1172_ = v___x_1190_;
goto v___jp_1170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1216_, lean_object* v_x_1217_, lean_object* v_x_1218_){
_start:
{
if (lean_obj_tag(v_x_1218_) == 0)
{
lean_dec(v_x_1216_);
return v_x_1217_;
}
else
{
lean_object* v_head_1219_; lean_object* v_tail_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1232_; 
v_head_1219_ = lean_ctor_get(v_x_1218_, 0);
v_tail_1220_ = lean_ctor_get(v_x_1218_, 1);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_x_1218_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1222_ = v_x_1218_;
v_isShared_1223_ = v_isSharedCheck_1232_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_tail_1220_);
lean_inc(v_head_1219_);
lean_dec(v_x_1218_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1232_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
lean_inc(v_x_1216_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set_tag(v___x_1222_, 5);
lean_ctor_set(v___x_1222_, 1, v_x_1216_);
lean_ctor_set(v___x_1222_, 0, v_x_1217_);
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_x_1217_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_x_1216_);
v___x_1225_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1226_ = lean_string_from_utf8_unchecked(v_head_1219_);
v___x_1227_ = l_String_quote(v___x_1226_);
v___x_1228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1225_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v_x_1217_ = v___x_1229_;
v_x_1218_ = v_tail_1220_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(lean_object* v_x_1233_, lean_object* v_x_1234_, lean_object* v_x_1235_){
_start:
{
if (lean_obj_tag(v_x_1235_) == 0)
{
lean_dec(v_x_1233_);
return v_x_1234_;
}
else
{
lean_object* v_head_1236_; lean_object* v_tail_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1249_; 
v_head_1236_ = lean_ctor_get(v_x_1235_, 0);
v_tail_1237_ = lean_ctor_get(v_x_1235_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_x_1235_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1239_ = v_x_1235_;
v_isShared_1240_ = v_isSharedCheck_1249_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_tail_1237_);
lean_inc(v_head_1236_);
lean_dec(v_x_1235_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1249_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
lean_inc(v_x_1233_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set_tag(v___x_1239_, 5);
lean_ctor_set(v___x_1239_, 1, v_x_1233_);
lean_ctor_set(v___x_1239_, 0, v_x_1234_);
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_x_1234_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_x_1233_);
v___x_1242_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1243_ = lean_string_from_utf8_unchecked(v_head_1236_);
v___x_1244_ = l_String_quote(v___x_1243_);
v___x_1245_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
v___x_1246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1242_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(v_x_1233_, v___x_1246_, v_tail_1237_);
return v___x_1247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(lean_object* v___y_1250_){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = lean_string_from_utf8_unchecked(v___y_1250_);
v___x_1252_ = l_String_quote(v___x_1251_);
v___x_1253_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(lean_object* v_x_1254_, lean_object* v_x_1255_){
_start:
{
if (lean_obj_tag(v_x_1254_) == 0)
{
lean_object* v___x_1256_; 
lean_dec(v_x_1255_);
v___x_1256_ = lean_box(0);
return v___x_1256_;
}
else
{
lean_object* v_tail_1257_; 
v_tail_1257_ = lean_ctor_get(v_x_1254_, 1);
if (lean_obj_tag(v_tail_1257_) == 0)
{
lean_object* v_head_1258_; lean_object* v___x_1259_; 
lean_dec(v_x_1255_);
v_head_1258_ = lean_ctor_get(v_x_1254_, 0);
lean_inc(v_head_1258_);
lean_dec_ref_known(v_x_1254_, 2);
v___x_1259_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1258_);
return v___x_1259_;
}
else
{
lean_object* v_head_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_inc(v_tail_1257_);
v_head_1260_ = lean_ctor_get(v_x_1254_, 0);
lean_inc(v_head_1260_);
lean_dec_ref_known(v_x_1254_, 2);
v___x_1261_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1260_);
v___x_1262_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(v_x_1255_, v___x_1261_, v_tail_1257_);
return v___x_1262_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0));
v___x_1268_ = lean_string_length(v___x_1267_);
return v___x_1268_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2);
v___x_1270_ = lean_nat_to_int(v___x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(lean_object* v_xs_1278_){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1279_ = lean_array_get_size(v_xs_1278_);
v___x_1280_ = lean_unsigned_to_nat(0u);
v___x_1281_ = lean_nat_dec_eq(v___x_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1282_ = lean_array_to_list(v_xs_1278_);
v___x_1283_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1284_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(v___x_1282_, v___x_1283_);
v___x_1285_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1286_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
lean_ctor_set(v___x_1287_, 1, v___x_1284_);
v___x_1288_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
v___x_1290_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1285_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = l_Std_Format_fill(v___x_1290_);
return v___x_1291_;
}
else
{
lean_object* v___x_1292_; 
lean_dec_ref(v_xs_1278_);
v___x_1292_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1292_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___redArg(lean_object* v_x_1305_){
_start:
{
lean_object* v_segments_1306_; uint8_t v_absolute_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1339_; 
v_segments_1306_ = lean_ctor_get(v_x_1305_, 0);
v_absolute_1307_ = lean_ctor_get_uint8(v_x_1305_, sizeof(void*)*1);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_x_1305_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1309_ = v_x_1305_;
v_isShared_1310_ = v_isSharedCheck_1339_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_segments_1306_);
lean_dec(v_x_1305_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1339_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; lean_object* v___x_1318_; 
v___x_1311_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1312_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__3));
v___x_1313_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_1314_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(v_segments_1306_);
v___x_1315_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = 0;
if (v_isShared_1310_ == 0)
{
lean_ctor_set_tag(v___x_1309_, 6);
lean_ctor_set(v___x_1309_, 0, v___x_1315_);
v___x_1318_ = v___x_1309_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1315_);
v___x_1318_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_ctor_set_uint8(v___x_1318_, sizeof(void*)*1, v___x_1316_);
v___x_1319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1312_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1319_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
v___x_1322_ = lean_box(1);
v___x_1323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1321_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__5));
v___x_1325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1323_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
v___x_1326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set(v___x_1326_, 1, v___x_1311_);
v___x_1327_ = l_Bool_repr___redArg(v_absolute_1307_);
v___x_1328_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1313_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
lean_ctor_set_uint8(v___x_1329_, sizeof(void*)*1, v___x_1316_);
v___x_1330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1326_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1332_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
lean_ctor_set(v___x_1333_, 1, v___x_1330_);
v___x_1334_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1333_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1331_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set_uint8(v___x_1337_, sizeof(void*)*1, v___x_1316_);
return v___x_1337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr(lean_object* v_x_1340_, lean_object* v_prec_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Std_Http_URI_instReprPath_repr___redArg(v_x_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___boxed(lean_object* v_x_1343_, lean_object* v_prec_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Std_Http_URI_instReprPath_repr(v_x_1343_, v_prec_1344_);
lean_dec(v_prec_1344_);
return v_res_1345_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(lean_object* v_xs_1348_, lean_object* v_ys_1349_, lean_object* v_x_1350_){
_start:
{
lean_object* v_zero_1351_; uint8_t v_isZero_1352_; 
v_zero_1351_ = lean_unsigned_to_nat(0u);
v_isZero_1352_ = lean_nat_dec_eq(v_x_1350_, v_zero_1351_);
if (v_isZero_1352_ == 1)
{
lean_dec(v_x_1350_);
return v_isZero_1352_;
}
else
{
lean_object* v_one_1353_; lean_object* v_n_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v_one_1353_ = lean_unsigned_to_nat(1u);
v_n_1354_ = lean_nat_sub(v_x_1350_, v_one_1353_);
lean_dec(v_x_1350_);
v___x_1355_ = lean_array_fget_borrowed(v_xs_1348_, v_n_1354_);
v___x_1356_ = lean_array_fget_borrowed(v_ys_1349_, v_n_1354_);
v___x_1357_ = lean_sarray_dec_eq(v___x_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_dec(v_n_1354_);
return v___x_1357_;
}
else
{
v_x_1350_ = v_n_1354_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg___boxed(lean_object* v_xs_1359_, lean_object* v_ys_1360_, lean_object* v_x_1361_){
_start:
{
uint8_t v_res_1362_; lean_object* v_r_1363_; 
v_res_1362_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1359_, v_ys_1360_, v_x_1361_);
lean_dec_ref(v_ys_1360_);
lean_dec_ref(v_xs_1359_);
v_r_1363_ = lean_box(v_res_1362_);
return v_r_1363_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqPath_beq(lean_object* v_x_1364_, lean_object* v_x_1365_){
_start:
{
lean_object* v_segments_1366_; uint8_t v_absolute_1367_; lean_object* v_segments_1368_; uint8_t v_absolute_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v_segments_1366_ = lean_ctor_get(v_x_1364_, 0);
v_absolute_1367_ = lean_ctor_get_uint8(v_x_1364_, sizeof(void*)*1);
v_segments_1368_ = lean_ctor_get(v_x_1365_, 0);
v_absolute_1369_ = lean_ctor_get_uint8(v_x_1365_, sizeof(void*)*1);
v___x_1370_ = lean_array_get_size(v_segments_1366_);
v___x_1371_ = lean_array_get_size(v_segments_1368_);
v___x_1372_ = lean_nat_dec_eq(v___x_1370_, v___x_1371_);
if (v___x_1372_ == 0)
{
return v___x_1372_;
}
else
{
uint8_t v___x_1373_; 
v___x_1373_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_segments_1366_, v_segments_1368_, v___x_1370_);
if (v___x_1373_ == 0)
{
return v___x_1373_;
}
else
{
if (v_absolute_1369_ == 0)
{
if (v_absolute_1367_ == 0)
{
return v___x_1373_;
}
else
{
return v_absolute_1369_;
}
}
else
{
return v_absolute_1367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqPath_beq___boxed(lean_object* v_x_1374_, lean_object* v_x_1375_){
_start:
{
uint8_t v_res_1376_; lean_object* v_r_1377_; 
v_res_1376_ = l_Std_Http_URI_instBEqPath_beq(v_x_1374_, v_x_1375_);
lean_dec_ref(v_x_1375_);
lean_dec_ref(v_x_1374_);
v_r_1377_ = lean_box(v_res_1376_);
return v_r_1377_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(lean_object* v_xs_1378_, lean_object* v_ys_1379_, lean_object* v_hsz_1380_, lean_object* v_x_1381_, lean_object* v_x_1382_){
_start:
{
uint8_t v___x_1383_; 
v___x_1383_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1378_, v_ys_1379_, v_x_1381_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___boxed(lean_object* v_xs_1384_, lean_object* v_ys_1385_, lean_object* v_hsz_1386_, lean_object* v_x_1387_, lean_object* v_x_1388_){
_start:
{
uint8_t v_res_1389_; lean_object* v_r_1390_; 
v_res_1389_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(v_xs_1384_, v_ys_1385_, v_hsz_1386_, v_x_1387_, v_x_1388_);
lean_dec_ref(v_ys_1385_);
lean_dec_ref(v_xs_1384_);
v_r_1390_ = lean_box(v_res_1389_);
return v_r_1390_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__0(lean_object* v_x_1393_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_string_from_utf8_unchecked(v_x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__1(lean_object* v___f_1415_, lean_object* v_path_1416_){
_start:
{
lean_object* v_segments_1417_; uint8_t v_absolute_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; size_t v_sz_1421_; size_t v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v_result_1425_; 
v_segments_1417_ = lean_ctor_get(v_path_1416_, 0);
lean_inc_ref(v_segments_1417_);
v_absolute_1418_ = lean_ctor_get_uint8(v_path_1416_, sizeof(void*)*1);
lean_dec_ref(v_path_1416_);
v___x_1419_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_1420_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_1421_ = lean_array_size(v_segments_1417_);
v___x_1422_ = ((size_t)0ULL);
v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1420_, v___f_1415_, v_sz_1421_, v___x_1422_, v_segments_1417_);
v___x_1424_ = lean_array_to_list(v___x_1423_);
v_result_1425_ = l_String_intercalate(v___x_1419_, v___x_1424_);
if (v_absolute_1418_ == 0)
{
return v_result_1425_;
}
else
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_string_append(v___x_1419_, v_result_1425_);
lean_dec_ref(v_result_1425_);
return v___x_1426_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Path_isEmpty(lean_object* v_p_1431_){
_start:
{
lean_object* v_segments_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v_segments_1432_ = lean_ctor_get(v_p_1431_, 0);
v___x_1433_ = lean_array_get_size(v_segments_1432_);
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = lean_nat_dec_eq(v___x_1433_, v___x_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_isEmpty___boxed(lean_object* v_p_1436_){
_start:
{
uint8_t v_res_1437_; lean_object* v_r_1438_; 
v_res_1437_ = l_Std_Http_URI_Path_isEmpty(v_p_1436_);
lean_dec_ref(v_p_1436_);
v_r_1438_ = lean_box(v_res_1437_);
return v_r_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parent(lean_object* v_p_1439_){
_start:
{
lean_object* v_segments_1440_; uint8_t v_absolute_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v_segments_1440_ = lean_ctor_get(v_p_1439_, 0);
v_absolute_1441_ = lean_ctor_get_uint8(v_p_1439_, sizeof(void*)*1);
v___x_1442_ = lean_array_get_size(v_segments_1440_);
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = lean_nat_dec_eq(v___x_1442_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1452_; 
lean_inc_ref(v_segments_1440_);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_p_1439_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v_p_1439_, 0);
lean_dec(v_unused_1453_);
v___x_1446_ = v_p_1439_;
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
else
{
lean_dec(v_p_1439_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1448_ = lean_array_pop(v_segments_1440_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v___x_1448_);
v___x_1450_ = v___x_1446_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
lean_ctor_set_uint8(v_reuseFailAlloc_1451_, sizeof(void*)*1, v_absolute_1441_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
else
{
return v_p_1439_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join(lean_object* v_p1_1454_, lean_object* v_p2_1455_){
_start:
{
uint8_t v_absolute_1456_; 
v_absolute_1456_ = lean_ctor_get_uint8(v_p2_1455_, sizeof(void*)*1);
if (v_absolute_1456_ == 0)
{
lean_object* v_segments_1457_; lean_object* v_segments_1458_; uint8_t v_absolute_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1467_; 
v_segments_1457_ = lean_ctor_get(v_p2_1455_, 0);
v_segments_1458_ = lean_ctor_get(v_p1_1454_, 0);
v_absolute_1459_ = lean_ctor_get_uint8(v_p1_1454_, sizeof(void*)*1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_p1_1454_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1461_ = v_p1_1454_;
v_isShared_1462_ = v_isSharedCheck_1467_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_segments_1458_);
lean_dec(v_p1_1454_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1467_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1463_ = l_Array_append___redArg(v_segments_1458_, v_segments_1457_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1463_);
v___x_1465_ = v___x_1461_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
lean_ctor_set_uint8(v_reuseFailAlloc_1466_, sizeof(void*)*1, v_absolute_1459_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
else
{
lean_dec_ref(v_p1_1454_);
lean_inc_ref(v_p2_1455_);
return v_p2_1455_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join___boxed(lean_object* v_p1_1468_, lean_object* v_p2_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Std_Http_URI_Path_join(v_p1_1468_, v_p2_1469_);
lean_dec_ref(v_p2_1469_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append(lean_object* v_p_1471_, lean_object* v_segment_1472_){
_start:
{
lean_object* v_segments_1473_; uint8_t v_absolute_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1483_; 
v_segments_1473_ = lean_ctor_get(v_p_1471_, 0);
v_absolute_1474_ = lean_ctor_get_uint8(v_p_1471_, sizeof(void*)*1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_p_1471_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1476_ = v_p_1471_;
v_isShared_1477_ = v_isSharedCheck_1483_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_segments_1473_);
lean_dec(v_p_1471_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1483_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1478_ = l_Std_Http_URI_EncodedSegment_encode(v_segment_1472_);
v___x_1479_ = lean_array_push(v_segments_1473_, v___x_1478_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1479_);
v___x_1481_ = v___x_1476_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
lean_ctor_set_uint8(v_reuseFailAlloc_1482_, sizeof(void*)*1, v_absolute_1474_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append___boxed(lean_object* v_p_1484_, lean_object* v_segment_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Std_Http_URI_Path_append(v_p_1484_, v_segment_1485_);
lean_dec_ref(v_segment_1485_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_appendEncoded(lean_object* v_p_1487_, lean_object* v_segment_1488_){
_start:
{
lean_object* v_segments_1489_; uint8_t v_absolute_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1498_; 
v_segments_1489_ = lean_ctor_get(v_p_1487_, 0);
v_absolute_1490_ = lean_ctor_get_uint8(v_p_1487_, sizeof(void*)*1);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_p_1487_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1492_ = v_p_1487_;
v_isShared_1493_ = v_isSharedCheck_1498_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_segments_1489_);
lean_dec(v_p_1487_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1498_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1494_ = lean_array_push(v_segments_1489_, v_segment_1488_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v___x_1494_);
v___x_1496_ = v___x_1492_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
lean_ctor_set_uint8(v_reuseFailAlloc_1497_, sizeof(void*)*1, v_absolute_1490_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(lean_object* v_input_1501_, lean_object* v_output_1502_){
_start:
{
if (lean_obj_tag(v_input_1501_) == 0)
{
lean_object* v___x_1503_; 
v___x_1503_ = l_List_reverse___redArg(v_output_1502_);
return v___x_1503_;
}
else
{
lean_object* v_head_1504_; lean_object* v_tail_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1522_; 
v_head_1504_ = lean_ctor_get(v_input_1501_, 0);
v_tail_1505_ = lean_ctor_get(v_input_1501_, 1);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_input_1501_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1507_ = v_input_1501_;
v_isShared_1508_ = v_isSharedCheck_1522_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_tail_1505_);
lean_inc(v_head_1504_);
lean_dec(v_input_1501_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1522_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
lean_inc(v_head_1504_);
v___x_1509_ = lean_string_from_utf8_unchecked(v_head_1504_);
v___x_1510_ = ((lean_object*)(l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0));
v___x_1511_ = lean_string_dec_eq(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = ((lean_object*)(l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1));
v___x_1513_ = lean_string_dec_eq(v___x_1509_, v___x_1512_);
lean_dec_ref(v___x_1509_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1515_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v_output_1502_);
v___x_1515_ = v___x_1507_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_head_1504_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_output_1502_);
v___x_1515_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
v_input_1501_ = v_tail_1505_;
v_output_1502_ = v___x_1515_;
goto _start;
}
}
else
{
lean_del_object(v___x_1507_);
lean_dec(v_head_1504_);
if (lean_obj_tag(v_output_1502_) == 0)
{
v_input_1501_ = v_tail_1505_;
goto _start;
}
else
{
lean_object* v_tail_1519_; 
v_tail_1519_ = lean_ctor_get(v_output_1502_, 1);
lean_inc(v_tail_1519_);
lean_dec_ref_known(v_output_1502_, 2);
v_input_1501_ = v_tail_1505_;
v_output_1502_ = v_tail_1519_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_1509_);
lean_del_object(v___x_1507_);
lean_dec(v_head_1504_);
v_input_1501_ = v_tail_1505_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_normalize(lean_object* v_p_1523_){
_start:
{
lean_object* v_segments_1524_; uint8_t v_absolute_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1536_; 
v_segments_1524_ = lean_ctor_get(v_p_1523_, 0);
v_absolute_1525_ = lean_ctor_get_uint8(v_p_1523_, sizeof(void*)*1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_p_1523_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1527_ = v_p_1523_;
v_isShared_1528_ = v_isSharedCheck_1536_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_segments_1524_);
lean_dec(v_p_1523_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1536_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1529_ = lean_array_to_list(v_segments_1524_);
v___x_1530_ = lean_box(0);
v___x_1531_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(v___x_1529_, v___x_1530_);
v___x_1532_ = lean_array_mk(v___x_1531_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1532_);
v___x_1534_ = v___x_1527_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
lean_ctor_set_uint8(v_reuseFailAlloc_1535_, sizeof(void*)*1, v_absolute_1525_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(size_t v_sz_1537_, size_t v_i_1538_, lean_object* v_bs_1539_){
_start:
{
uint8_t v___x_1540_; 
v___x_1540_ = lean_usize_dec_lt(v_i_1538_, v_sz_1537_);
if (v___x_1540_ == 0)
{
return v_bs_1539_;
}
else
{
lean_object* v_v_1541_; lean_object* v___x_1542_; lean_object* v_bs_x27_1543_; lean_object* v___y_1545_; lean_object* v___x_1550_; 
v_v_1541_ = lean_array_uget(v_bs_1539_, v_i_1538_);
v___x_1542_ = lean_unsigned_to_nat(0u);
v_bs_x27_1543_ = lean_array_uset(v_bs_1539_, v_i_1538_, v___x_1542_);
v___x_1550_ = l_Std_Http_URI_EncodedSegment_decode(v_v_1541_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_string_from_utf8_unchecked(v_v_1541_);
v___y_1545_ = v___x_1551_;
goto v___jp_1544_;
}
else
{
lean_object* v_val_1552_; 
lean_dec(v_v_1541_);
v_val_1552_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v___x_1550_, 1);
v___y_1545_ = v_val_1552_;
goto v___jp_1544_;
}
v___jp_1544_:
{
size_t v___x_1546_; size_t v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = ((size_t)1ULL);
v___x_1547_ = lean_usize_add(v_i_1538_, v___x_1546_);
v___x_1548_ = lean_array_uset(v_bs_x27_1543_, v_i_1538_, v___y_1545_);
v_i_1538_ = v___x_1547_;
v_bs_1539_ = v___x_1548_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0___boxed(lean_object* v_sz_1553_, lean_object* v_i_1554_, lean_object* v_bs_1555_){
_start:
{
size_t v_sz_boxed_1556_; size_t v_i_boxed_1557_; lean_object* v_res_1558_; 
v_sz_boxed_1556_ = lean_unbox_usize(v_sz_1553_);
lean_dec(v_sz_1553_);
v_i_boxed_1557_ = lean_unbox_usize(v_i_1554_);
lean_dec(v_i_1554_);
v_res_1558_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_boxed_1556_, v_i_boxed_1557_, v_bs_1555_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_toDecodedSegments(lean_object* v_p_1559_){
_start:
{
lean_object* v_segments_1560_; size_t v_sz_1561_; size_t v___x_1562_; lean_object* v___x_1563_; 
v_segments_1560_ = lean_ctor_get(v_p_1559_, 0);
lean_inc_ref(v_segments_1560_);
lean_dec_ref(v_p_1559_);
v_sz_1561_ = lean_array_size(v_segments_1560_);
v___x_1562_ = ((size_t)0ULL);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_1561_, v___x_1562_, v_segments_1560_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___redArg(lean_object* v_xs_1572_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1574_ = l_Array_repr___redArg(v___x_1573_, v_xs_1572_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1(lean_object* v_xs_1575_, lean_object* v_x_1576_){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1578_ = l_Array_repr___redArg(v___x_1577_, v_xs_1575_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___boxed(lean_object* v_xs_1579_, lean_object* v_x_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Std_Http_URI_instReprQuery___aux__1(v_xs_1579_, v_x_1580_);
lean_dec(v_x_1580_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_1582_, lean_object* v_x_1583_, lean_object* v_x_1584_){
_start:
{
if (lean_obj_tag(v_x_1584_) == 0)
{
lean_dec(v_x_1582_);
return v_x_1583_;
}
else
{
lean_object* v_head_1585_; lean_object* v_tail_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1595_; 
v_head_1585_ = lean_ctor_get(v_x_1584_, 0);
v_tail_1586_ = lean_ctor_get(v_x_1584_, 1);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1588_ = v_x_1584_;
v_isShared_1589_ = v_isSharedCheck_1595_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_tail_1586_);
lean_inc(v_head_1585_);
lean_dec(v_x_1584_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1595_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
lean_inc(v_x_1582_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set_tag(v___x_1588_, 5);
lean_ctor_set(v___x_1588_, 1, v_x_1582_);
lean_ctor_set(v___x_1588_, 0, v_x_1583_);
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_x_1583_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_x_1582_);
v___x_1591_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
lean_ctor_set(v___x_1592_, 1, v_head_1585_);
v_x_1583_ = v___x_1592_;
v_x_1584_ = v_tail_1586_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(lean_object* v_x_1596_, lean_object* v_x_1597_){
_start:
{
if (lean_obj_tag(v_x_1596_) == 0)
{
lean_object* v___x_1598_; 
lean_dec(v_x_1597_);
v___x_1598_ = lean_box(0);
return v___x_1598_;
}
else
{
lean_object* v_tail_1599_; 
v_tail_1599_ = lean_ctor_get(v_x_1596_, 1);
if (lean_obj_tag(v_tail_1599_) == 0)
{
lean_object* v_head_1600_; 
lean_dec(v_x_1597_);
v_head_1600_ = lean_ctor_get(v_x_1596_, 0);
lean_inc(v_head_1600_);
lean_dec_ref_known(v_x_1596_, 2);
return v_head_1600_;
}
else
{
lean_object* v_head_1601_; lean_object* v___x_1602_; 
lean_inc(v_tail_1599_);
v_head_1601_ = lean_ctor_get(v_x_1596_, 0);
lean_inc(v_head_1601_);
lean_dec_ref_known(v_x_1596_, 2);
v___x_1602_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(v_x_1597_, v_head_1601_, v_tail_1599_);
return v___x_1602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(lean_object* v_x_1603_, lean_object* v_x_1604_){
_start:
{
if (lean_obj_tag(v_x_1603_) == 0)
{
lean_object* v___x_1605_; 
v___x_1605_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1605_;
}
else
{
lean_object* v_val_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1618_; 
v_val_1606_ = lean_ctor_get(v_x_1603_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_x_1603_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1608_ = v_x_1603_;
v_isShared_1609_ = v_isSharedCheck_1618_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_val_1606_);
lean_dec(v_x_1603_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1618_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1610_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1611_ = lean_string_from_utf8_unchecked(v_val_1606_);
v___x_1612_ = l_String_quote(v___x_1611_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set_tag(v___x_1608_, 3);
lean_ctor_set(v___x_1608_, 0, v___x_1612_);
v___x_1614_ = v___x_1608_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1612_);
v___x_1614_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1610_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = l_Repr_addAppParen(v___x_1615_, v_x_1604_);
return v___x_1616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1619_, lean_object* v_x_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_x_1619_, v_x_1620_);
lean_dec(v_x_1620_);
return v_res_1621_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0));
v___x_1625_ = lean_string_length(v___x_1624_);
return v___x_1625_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2);
v___x_1627_ = lean_nat_to_int(v___x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(lean_object* v_x_1632_){
_start:
{
lean_object* v_fst_1633_; lean_object* v_snd_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1659_; 
v_fst_1633_ = lean_ctor_get(v_x_1632_, 0);
v_snd_1634_ = lean_ctor_get(v_x_1632_, 1);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_x_1632_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1636_ = v_x_1632_;
v_isShared_1637_ = v_isSharedCheck_1659_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_snd_1634_);
lean_inc(v_fst_1633_);
lean_dec(v_x_1632_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1659_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1638_ = lean_string_from_utf8_unchecked(v_fst_1633_);
v___x_1639_ = l_String_quote(v___x_1638_);
v___x_1640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
v___x_1641_ = lean_box(0);
if (v_isShared_1637_ == 0)
{
lean_ctor_set_tag(v___x_1636_, 1);
lean_ctor_set(v___x_1636_, 1, v___x_1641_);
lean_ctor_set(v___x_1636_, 0, v___x_1640_);
v___x_1643_ = v___x_1636_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; 
v___x_1644_ = lean_unsigned_to_nat(0u);
v___x_1645_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_snd_1634_, v___x_1644_);
v___x_1646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_ctor_set(v___x_1646_, 1, v___x_1643_);
v___x_1647_ = l_List_reverse___redArg(v___x_1646_);
v___x_1648_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1649_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(v___x_1647_, v___x_1648_);
v___x_1650_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3);
v___x_1651_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4));
v___x_1652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
lean_ctor_set(v___x_1652_, 1, v___x_1649_);
v___x_1653_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5));
v___x_1654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1650_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = 0;
v___x_1657_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set_uint8(v___x_1657_, sizeof(void*)*1, v___x_1656_);
return v___x_1657_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(lean_object* v_x_1660_, lean_object* v_x_1661_, lean_object* v_x_1662_){
_start:
{
if (lean_obj_tag(v_x_1662_) == 0)
{
lean_dec(v_x_1660_);
return v_x_1661_;
}
else
{
lean_object* v_head_1663_; lean_object* v_tail_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1674_; 
v_head_1663_ = lean_ctor_get(v_x_1662_, 0);
v_tail_1664_ = lean_ctor_get(v_x_1662_, 1);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_x_1662_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1666_ = v_x_1662_;
v_isShared_1667_ = v_isSharedCheck_1674_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_tail_1664_);
lean_inc(v_head_1663_);
lean_dec(v_x_1662_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1674_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
lean_inc(v_x_1660_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set_tag(v___x_1666_, 5);
lean_ctor_set(v___x_1666_, 1, v_x_1660_);
lean_ctor_set(v___x_1666_, 0, v_x_1661_);
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_x_1661_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_x_1660_);
v___x_1669_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1663_);
v___x_1671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v_x_1661_ = v___x_1671_;
v_x_1662_ = v_tail_1664_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(lean_object* v_x_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_){
_start:
{
if (lean_obj_tag(v_x_1677_) == 0)
{
lean_dec(v_x_1675_);
return v_x_1676_;
}
else
{
lean_object* v_head_1678_; lean_object* v_tail_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1689_; 
v_head_1678_ = lean_ctor_get(v_x_1677_, 0);
v_tail_1679_ = lean_ctor_get(v_x_1677_, 1);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_x_1677_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1681_ = v_x_1677_;
v_isShared_1682_ = v_isSharedCheck_1689_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_tail_1679_);
lean_inc(v_head_1678_);
lean_dec(v_x_1677_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1689_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
lean_inc(v_x_1675_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 5);
lean_ctor_set(v___x_1681_, 1, v_x_1675_);
lean_ctor_set(v___x_1681_, 0, v_x_1676_);
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_x_1676_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_x_1675_);
v___x_1684_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1678_);
v___x_1686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(v_x_1675_, v___x_1686_, v_tail_1679_);
return v___x_1687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(lean_object* v_x_1690_, lean_object* v_x_1691_){
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
lean_object* v_head_1694_; lean_object* v___x_1695_; 
lean_dec(v_x_1691_);
v_head_1694_ = lean_ctor_get(v_x_1690_, 0);
lean_inc(v_head_1694_);
lean_dec_ref_known(v_x_1690_, 2);
v___x_1695_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1694_);
return v___x_1695_;
}
else
{
lean_object* v_head_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
lean_inc(v_tail_1693_);
v_head_1696_ = lean_ctor_get(v_x_1690_, 0);
lean_inc(v_head_1696_);
lean_dec_ref_known(v_x_1690_, 2);
v___x_1697_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1696_);
v___x_1698_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(v_x_1691_, v___x_1697_, v_tail_1693_);
return v___x_1698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(lean_object* v_xs_1699_){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; 
v___x_1700_ = lean_array_get_size(v_xs_1699_);
v___x_1701_ = lean_unsigned_to_nat(0u);
v___x_1702_ = lean_nat_dec_eq(v___x_1700_, v___x_1701_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1703_ = lean_array_to_list(v_xs_1699_);
v___x_1704_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1705_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(v___x_1703_, v___x_1704_);
v___x_1706_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1707_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
lean_ctor_set(v___x_1708_, 1, v___x_1705_);
v___x_1709_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1706_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = l_Std_Format_fill(v___x_1711_);
return v___x_1712_;
}
else
{
lean_object* v___x_1713_; 
lean_dec_ref(v_xs_1699_);
v___x_1713_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1713_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0(lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v___y_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0___boxed(lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Std_Http_URI_instReprQuery___lam__0(v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(lean_object* v_x_1722_, lean_object* v_x_1723_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_x_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___boxed(lean_object* v_x_1725_, lean_object* v_x_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(v_x_1725_, v_x_1726_);
lean_dec(v_x_1726_);
return v_res_1727_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1___lam__0(lean_object* v___f_1732_, lean_object* v_x_1733_, lean_object* v_x_1734_){
_start:
{
lean_object* v_fst_1735_; lean_object* v_snd_1736_; lean_object* v_fst_1737_; lean_object* v_snd_1738_; uint8_t v___x_1739_; 
v_fst_1735_ = lean_ctor_get(v_x_1733_, 0);
lean_inc(v_fst_1735_);
v_snd_1736_ = lean_ctor_get(v_x_1733_, 1);
lean_inc(v_snd_1736_);
lean_dec_ref(v_x_1733_);
v_fst_1737_ = lean_ctor_get(v_x_1734_, 0);
lean_inc(v_fst_1737_);
v_snd_1738_ = lean_ctor_get(v_x_1734_, 1);
lean_inc(v_snd_1738_);
lean_dec_ref(v_x_1734_);
v___x_1739_ = lean_sarray_dec_eq(v_fst_1735_, v_fst_1737_);
lean_dec(v_fst_1737_);
lean_dec(v_fst_1735_);
if (v___x_1739_ == 0)
{
lean_dec(v_snd_1738_);
lean_dec(v_snd_1736_);
lean_dec_ref(v___f_1732_);
return v___x_1739_;
}
else
{
uint8_t v___x_1740_; 
v___x_1740_ = l_Option_instBEq_beq___redArg(v___f_1732_, v_snd_1736_, v_snd_1738_);
return v___x_1740_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___lam__0___boxed(lean_object* v___f_1741_, lean_object* v_x_1742_, lean_object* v_x_1743_){
_start:
{
uint8_t v_res_1744_; lean_object* v_r_1745_; 
v_res_1744_ = l_Std_Http_URI_instBEqQuery___aux__1___lam__0(v___f_1741_, v_x_1742_, v_x_1743_);
v_r_1745_ = lean_box(v_res_1744_);
return v_r_1745_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1(lean_object* v_xs_1749_, lean_object* v_ys_1750_){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; 
v___x_1751_ = lean_array_get_size(v_xs_1749_);
v___x_1752_ = lean_array_get_size(v_ys_1750_);
v___x_1753_ = lean_nat_dec_eq(v___x_1751_, v___x_1752_);
if (v___x_1753_ == 0)
{
return v___x_1753_;
}
else
{
lean_object* v___f_1754_; uint8_t v___x_1755_; 
v___f_1754_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__1));
v___x_1755_ = l_Array_isEqvAux___redArg(v_xs_1749_, v_ys_1750_, v___f_1754_, v___x_1751_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___boxed(lean_object* v_xs_1756_, lean_object* v_ys_1757_){
_start:
{
uint8_t v_res_1758_; lean_object* v_r_1759_; 
v_res_1758_ = l_Std_Http_URI_instBEqQuery___aux__1(v_xs_1756_, v_ys_1757_);
lean_dec_ref(v_ys_1757_);
lean_dec_ref(v_xs_1756_);
v_r_1759_ = lean_box(v_res_1758_);
return v_r_1759_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(lean_object* v_x_1760_, lean_object* v_x_1761_){
_start:
{
if (lean_obj_tag(v_x_1760_) == 0)
{
if (lean_obj_tag(v_x_1761_) == 0)
{
uint8_t v___x_1762_; 
v___x_1762_ = 1;
return v___x_1762_;
}
else
{
uint8_t v___x_1763_; 
v___x_1763_ = 0;
return v___x_1763_;
}
}
else
{
if (lean_obj_tag(v_x_1761_) == 0)
{
uint8_t v___x_1764_; 
v___x_1764_ = 0;
return v___x_1764_;
}
else
{
lean_object* v_val_1765_; lean_object* v_val_1766_; uint8_t v___x_1767_; 
v_val_1765_ = lean_ctor_get(v_x_1760_, 0);
v_val_1766_ = lean_ctor_get(v_x_1761_, 0);
v___x_1767_ = lean_sarray_dec_eq(v_val_1765_, v_val_1766_);
return v___x_1767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0___boxed(lean_object* v_x_1768_, lean_object* v_x_1769_){
_start:
{
uint8_t v_res_1770_; lean_object* v_r_1771_; 
v_res_1770_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_x_1768_, v_x_1769_);
lean_dec(v_x_1769_);
lean_dec(v_x_1768_);
v_r_1771_ = lean_box(v_res_1770_);
return v_r_1771_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(lean_object* v_xs_1772_, lean_object* v_ys_1773_, lean_object* v_x_1774_){
_start:
{
lean_object* v_zero_1775_; uint8_t v_isZero_1776_; 
v_zero_1775_ = lean_unsigned_to_nat(0u);
v_isZero_1776_ = lean_nat_dec_eq(v_x_1774_, v_zero_1775_);
if (v_isZero_1776_ == 1)
{
lean_dec(v_x_1774_);
return v_isZero_1776_;
}
else
{
lean_object* v_one_1777_; lean_object* v_n_1778_; lean_object* v___x_1779_; lean_object* v_fst_1780_; lean_object* v_snd_1781_; lean_object* v___x_1782_; lean_object* v_fst_1783_; lean_object* v_snd_1784_; uint8_t v___x_1785_; 
v_one_1777_ = lean_unsigned_to_nat(1u);
v_n_1778_ = lean_nat_sub(v_x_1774_, v_one_1777_);
lean_dec(v_x_1774_);
v___x_1779_ = lean_array_fget_borrowed(v_xs_1772_, v_n_1778_);
v_fst_1780_ = lean_ctor_get(v___x_1779_, 0);
v_snd_1781_ = lean_ctor_get(v___x_1779_, 1);
v___x_1782_ = lean_array_fget_borrowed(v_ys_1773_, v_n_1778_);
v_fst_1783_ = lean_ctor_get(v___x_1782_, 0);
v_snd_1784_ = lean_ctor_get(v___x_1782_, 1);
v___x_1785_ = lean_sarray_dec_eq(v_fst_1780_, v_fst_1783_);
if (v___x_1785_ == 0)
{
lean_dec(v_n_1778_);
return v___x_1785_;
}
else
{
uint8_t v___x_1786_; 
v___x_1786_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_snd_1781_, v_snd_1784_);
if (v___x_1786_ == 0)
{
lean_dec(v_n_1778_);
return v___x_1786_;
}
else
{
v_x_1774_ = v_n_1778_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg___boxed(lean_object* v_xs_1788_, lean_object* v_ys_1789_, lean_object* v_x_1790_){
_start:
{
uint8_t v_res_1791_; lean_object* v_r_1792_; 
v_res_1791_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1788_, v_ys_1789_, v_x_1790_);
lean_dec_ref(v_ys_1789_);
lean_dec_ref(v_xs_1788_);
v_r_1792_ = lean_box(v_res_1791_);
return v_r_1792_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___lam__0(lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1795_ = lean_array_get_size(v___y_1793_);
v___x_1796_ = lean_array_get_size(v___y_1794_);
v___x_1797_ = lean_nat_dec_eq(v___x_1795_, v___x_1796_);
if (v___x_1797_ == 0)
{
return v___x_1797_;
}
else
{
uint8_t v___x_1798_; 
v___x_1798_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v___y_1793_, v___y_1794_, v___x_1795_);
return v___x_1798_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___lam__0___boxed(lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
uint8_t v_res_1801_; lean_object* v_r_1802_; 
v_res_1801_ = l_Std_Http_URI_instBEqQuery___lam__0(v___y_1799_, v___y_1800_);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v___y_1799_);
v_r_1802_ = lean_box(v_res_1801_);
return v_r_1802_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(lean_object* v_xs_1805_, lean_object* v_ys_1806_, lean_object* v_hsz_1807_, lean_object* v_x_1808_, lean_object* v_x_1809_){
_start:
{
uint8_t v___x_1810_; 
v___x_1810_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1805_, v_ys_1806_, v_x_1808_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___boxed(lean_object* v_xs_1811_, lean_object* v_ys_1812_, lean_object* v_hsz_1813_, lean_object* v_x_1814_, lean_object* v_x_1815_){
_start:
{
uint8_t v_res_1816_; lean_object* v_r_1817_; 
v_res_1816_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(v_xs_1811_, v_ys_1812_, v_hsz_1813_, v_x_1814_, v_x_1815_);
lean_dec_ref(v_ys_1812_);
lean_dec_ref(v_xs_1811_);
v_r_1817_ = lean_box(v_res_1816_);
return v_r_1817_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(lean_object* v_as_1818_){
_start:
{
lean_object* v___f_1819_; lean_object* v___x_1820_; 
v___f_1819_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__0));
v___x_1820_ = l_List_eraseDupsBy___redArg(v___f_1819_, v_as_1818_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(size_t v_sz_1821_, size_t v_i_1822_, lean_object* v_bs_1823_){
_start:
{
uint8_t v___x_1824_; 
v___x_1824_ = lean_usize_dec_lt(v_i_1822_, v_sz_1821_);
if (v___x_1824_ == 0)
{
return v_bs_1823_;
}
else
{
lean_object* v_v_1825_; lean_object* v_fst_1826_; lean_object* v___x_1827_; lean_object* v_bs_x27_1828_; size_t v___x_1829_; size_t v___x_1830_; lean_object* v___x_1831_; 
v_v_1825_ = lean_array_uget_borrowed(v_bs_1823_, v_i_1822_);
v_fst_1826_ = lean_ctor_get(v_v_1825_, 0);
lean_inc(v_fst_1826_);
v___x_1827_ = lean_unsigned_to_nat(0u);
v_bs_x27_1828_ = lean_array_uset(v_bs_1823_, v_i_1822_, v___x_1827_);
v___x_1829_ = ((size_t)1ULL);
v___x_1830_ = lean_usize_add(v_i_1822_, v___x_1829_);
v___x_1831_ = lean_array_uset(v_bs_x27_1828_, v_i_1822_, v_fst_1826_);
v_i_1822_ = v___x_1830_;
v_bs_1823_ = v___x_1831_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0___boxed(lean_object* v_sz_1833_, lean_object* v_i_1834_, lean_object* v_bs_1835_){
_start:
{
size_t v_sz_boxed_1836_; size_t v_i_boxed_1837_; lean_object* v_res_1838_; 
v_sz_boxed_1836_ = lean_unbox_usize(v_sz_1833_);
lean_dec(v_sz_1833_);
v_i_boxed_1837_ = lean_unbox_usize(v_i_1834_);
lean_dec(v_i_1834_);
v_res_1838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_boxed_1836_, v_i_boxed_1837_, v_bs_1835_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names(lean_object* v_query_1839_){
_start:
{
size_t v_sz_1840_; size_t v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v_sz_1840_ = lean_array_size(v_query_1839_);
v___x_1841_ = ((size_t)0ULL);
v___x_1842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_1840_, v___x_1841_, v_query_1839_);
v___x_1843_ = lean_array_to_list(v___x_1842_);
v___x_1844_ = l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(v___x_1843_);
v___x_1845_ = lean_array_mk(v___x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(size_t v_sz_1846_, size_t v_i_1847_, lean_object* v_bs_1848_){
_start:
{
uint8_t v___x_1849_; 
v___x_1849_ = lean_usize_dec_lt(v_i_1847_, v_sz_1846_);
if (v___x_1849_ == 0)
{
return v_bs_1848_;
}
else
{
lean_object* v_v_1850_; lean_object* v_snd_1851_; lean_object* v___x_1852_; lean_object* v_bs_x27_1853_; size_t v___x_1854_; size_t v___x_1855_; lean_object* v___x_1856_; 
v_v_1850_ = lean_array_uget_borrowed(v_bs_1848_, v_i_1847_);
v_snd_1851_ = lean_ctor_get(v_v_1850_, 1);
lean_inc(v_snd_1851_);
v___x_1852_ = lean_unsigned_to_nat(0u);
v_bs_x27_1853_ = lean_array_uset(v_bs_1848_, v_i_1847_, v___x_1852_);
v___x_1854_ = ((size_t)1ULL);
v___x_1855_ = lean_usize_add(v_i_1847_, v___x_1854_);
v___x_1856_ = lean_array_uset(v_bs_x27_1853_, v_i_1847_, v_snd_1851_);
v_i_1847_ = v___x_1855_;
v_bs_1848_ = v___x_1856_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0___boxed(lean_object* v_sz_1858_, lean_object* v_i_1859_, lean_object* v_bs_1860_){
_start:
{
size_t v_sz_boxed_1861_; size_t v_i_boxed_1862_; lean_object* v_res_1863_; 
v_sz_boxed_1861_ = lean_unbox_usize(v_sz_1858_);
lean_dec(v_sz_1858_);
v_i_boxed_1862_ = lean_unbox_usize(v_i_1859_);
lean_dec(v_i_1859_);
v_res_1863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_boxed_1861_, v_i_boxed_1862_, v_bs_1860_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_values(lean_object* v_query_1864_){
_start:
{
size_t v_sz_1865_; size_t v___x_1866_; lean_object* v___x_1867_; 
v_sz_1865_ = lean_array_size(v_query_1864_);
v___x_1866_ = ((size_t)0ULL);
v___x_1867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_1865_, v___x_1866_, v_query_1864_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray(lean_object* v_query_1868_){
_start:
{
lean_inc_ref(v_query_1868_);
return v_query_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray___boxed(lean_object* v_query_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Std_Http_URI_Query_toArray(v_query_1869_);
lean_dec_ref(v_query_1869_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object* v_key_1872_, lean_object* v_value_1873_){
_start:
{
if (lean_obj_tag(v_value_1873_) == 0)
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_string_from_utf8_unchecked(v_key_1872_);
return v___x_1874_;
}
else
{
lean_object* v_val_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v_val_1875_ = lean_ctor_get(v_value_1873_, 0);
lean_inc(v_val_1875_);
lean_dec_ref_known(v_value_1873_, 1);
v___x_1876_ = lean_string_from_utf8_unchecked(v_key_1872_);
v___x_1877_ = ((lean_object*)(l_Std_Http_URI_Query_formatQueryParam___closed__0));
v___x_1878_ = lean_string_append(v___x_1876_, v___x_1877_);
v___x_1879_ = lean_string_from_utf8_unchecked(v_val_1875_);
v___x_1880_ = lean_string_append(v___x_1878_, v___x_1879_);
lean_dec_ref(v___x_1879_);
return v___x_1880_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(lean_object* v_key_1884_, lean_object* v_as_1885_, size_t v_sz_1886_, size_t v_i_1887_, lean_object* v_b_1888_){
_start:
{
uint8_t v___x_1889_; 
v___x_1889_ = lean_usize_dec_lt(v_i_1887_, v_sz_1886_);
if (v___x_1889_ == 0)
{
lean_inc_ref(v_b_1888_);
return v_b_1888_;
}
else
{
lean_object* v_a_1890_; lean_object* v_fst_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; 
v_a_1890_ = lean_array_uget_borrowed(v_as_1885_, v_i_1887_);
v_fst_1891_ = lean_ctor_get(v_a_1890_, 0);
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_sarray_dec_eq(v_fst_1891_, v_key_1884_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; size_t v___x_1895_; size_t v___x_1896_; 
v___x_1894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v___x_1895_ = ((size_t)1ULL);
v___x_1896_ = lean_usize_add(v_i_1887_, v___x_1895_);
v_i_1887_ = v___x_1896_;
v_b_1888_ = v___x_1894_;
goto _start;
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
lean_inc(v_a_1890_);
v___x_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1898_, 0, v_a_1890_);
v___x_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
v___x_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set(v___x_1900_, 1, v___x_1892_);
return v___x_1900_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___boxed(lean_object* v_key_1901_, lean_object* v_as_1902_, lean_object* v_sz_1903_, lean_object* v_i_1904_, lean_object* v_b_1905_){
_start:
{
size_t v_sz_boxed_1906_; size_t v_i_boxed_1907_; lean_object* v_res_1908_; 
v_sz_boxed_1906_ = lean_unbox_usize(v_sz_1903_);
lean_dec(v_sz_1903_);
v_i_boxed_1907_ = lean_unbox_usize(v_i_1904_);
lean_dec(v_i_1904_);
v_res_1908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1901_, v_as_1902_, v_sz_boxed_1906_, v_i_boxed_1907_, v_b_1905_);
lean_dec_ref(v_b_1905_);
lean_dec_ref(v_as_1902_);
lean_dec_ref(v_key_1901_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f(lean_object* v_query_1909_, lean_object* v_key_1910_){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; size_t v_sz_1913_; size_t v___x_1914_; lean_object* v___x_1915_; lean_object* v_fst_1916_; 
v___x_1911_ = lean_box(0);
v___x_1912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v_sz_1913_ = lean_array_size(v_query_1909_);
v___x_1914_ = ((size_t)0ULL);
v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1910_, v_query_1909_, v_sz_1913_, v___x_1914_, v___x_1912_);
v_fst_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_fst_1916_);
lean_dec_ref(v___x_1915_);
if (lean_obj_tag(v_fst_1916_) == 0)
{
return v___x_1911_;
}
else
{
lean_object* v_val_1917_; 
v_val_1917_ = lean_ctor_get(v_fst_1916_, 0);
lean_inc(v_val_1917_);
lean_dec_ref_known(v_fst_1916_, 1);
if (lean_obj_tag(v_val_1917_) == 0)
{
return v___x_1911_;
}
else
{
lean_object* v_val_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1926_; 
v_val_1918_ = lean_ctor_get(v_val_1917_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_val_1917_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1920_ = v_val_1917_;
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_val_1918_);
lean_dec(v_val_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v_snd_1922_; lean_object* v___x_1924_; 
v_snd_1922_ = lean_ctor_get(v_val_1918_, 1);
lean_inc(v_snd_1922_);
lean_dec(v_val_1918_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v_snd_1922_);
v___x_1924_ = v___x_1920_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_snd_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f___boxed(lean_object* v_query_1927_, lean_object* v_key_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1927_, v_key_1928_);
lean_dec_ref(v_key_1928_);
lean_dec_ref(v_query_1927_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f(lean_object* v_query_1930_, lean_object* v_key_1931_){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1931_);
v___x_1933_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1930_, v___x_1932_);
lean_dec_ref(v___x_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f___boxed(lean_object* v_query_1934_, lean_object* v_key_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Std_Http_URI_Query_find_x3f(v_query_1934_, v_key_1935_);
lean_dec_ref(v_key_1935_);
lean_dec_ref(v_query_1934_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(lean_object* v_key_1937_, lean_object* v_as_1938_, size_t v_i_1939_, size_t v_stop_1940_, lean_object* v_b_1941_){
_start:
{
lean_object* v___y_1943_; uint8_t v___x_1947_; 
v___x_1947_ = lean_usize_dec_eq(v_i_1939_, v_stop_1940_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; lean_object* v_fst_1949_; lean_object* v_snd_1950_; uint8_t v___x_1951_; 
v___x_1948_ = lean_array_uget_borrowed(v_as_1938_, v_i_1939_);
v_fst_1949_ = lean_ctor_get(v___x_1948_, 0);
v_snd_1950_ = lean_ctor_get(v___x_1948_, 1);
v___x_1951_ = lean_sarray_dec_eq(v_fst_1949_, v_key_1937_);
if (v___x_1951_ == 0)
{
v___y_1943_ = v_b_1941_;
goto v___jp_1942_;
}
else
{
lean_object* v___x_1952_; 
lean_inc(v_snd_1950_);
v___x_1952_ = lean_array_push(v_b_1941_, v_snd_1950_);
v___y_1943_ = v___x_1952_;
goto v___jp_1942_;
}
}
else
{
return v_b_1941_;
}
v___jp_1942_:
{
size_t v___x_1944_; size_t v___x_1945_; 
v___x_1944_ = ((size_t)1ULL);
v___x_1945_ = lean_usize_add(v_i_1939_, v___x_1944_);
v_i_1939_ = v___x_1945_;
v_b_1941_ = v___y_1943_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0___boxed(lean_object* v_key_1953_, lean_object* v_as_1954_, lean_object* v_i_1955_, lean_object* v_stop_1956_, lean_object* v_b_1957_){
_start:
{
size_t v_i_boxed_1958_; size_t v_stop_boxed_1959_; lean_object* v_res_1960_; 
v_i_boxed_1958_ = lean_unbox_usize(v_i_1955_);
lean_dec(v_i_1955_);
v_stop_boxed_1959_ = lean_unbox_usize(v_stop_1956_);
lean_dec(v_stop_1956_);
v_res_1960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1953_, v_as_1954_, v_i_boxed_1958_, v_stop_boxed_1959_, v_b_1957_);
lean_dec_ref(v_as_1954_);
lean_dec_ref(v_key_1953_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(lean_object* v_key_1963_, lean_object* v_as_1964_, lean_object* v_start_1965_, lean_object* v_stop_1966_){
_start:
{
lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_1968_ = lean_nat_dec_lt(v_start_1965_, v_stop_1966_);
if (v___x_1968_ == 0)
{
return v___x_1967_;
}
else
{
lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1969_ = lean_array_get_size(v_as_1964_);
v___x_1970_ = lean_nat_dec_le(v_stop_1966_, v___x_1969_);
if (v___x_1970_ == 0)
{
uint8_t v___x_1971_; 
v___x_1971_ = lean_nat_dec_lt(v_start_1965_, v___x_1969_);
if (v___x_1971_ == 0)
{
return v___x_1967_;
}
else
{
size_t v___x_1972_; size_t v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = lean_usize_of_nat(v_start_1965_);
v___x_1973_ = lean_usize_of_nat(v___x_1969_);
v___x_1974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1963_, v_as_1964_, v___x_1972_, v___x_1973_, v___x_1967_);
return v___x_1974_;
}
}
else
{
size_t v___x_1975_; size_t v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = lean_usize_of_nat(v_start_1965_);
v___x_1976_ = lean_usize_of_nat(v_stop_1966_);
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1963_, v_as_1964_, v___x_1975_, v___x_1976_, v___x_1967_);
return v___x_1977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___boxed(lean_object* v_key_1978_, lean_object* v_as_1979_, lean_object* v_start_1980_, lean_object* v_stop_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1978_, v_as_1979_, v_start_1980_, v_stop_1981_);
lean_dec(v_stop_1981_);
lean_dec(v_start_1980_);
lean_dec_ref(v_as_1979_);
lean_dec_ref(v_key_1978_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded(lean_object* v_query_1983_, lean_object* v_key_1984_){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = lean_unsigned_to_nat(0u);
v___x_1986_ = lean_array_get_size(v_query_1983_);
v___x_1987_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1984_, v_query_1983_, v___x_1985_, v___x_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded___boxed(lean_object* v_query_1988_, lean_object* v_key_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1988_, v_key_1989_);
lean_dec_ref(v_key_1989_);
lean_dec_ref(v_query_1988_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll(lean_object* v_query_1991_, lean_object* v_key_1992_){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1992_);
v___x_1994_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1991_, v___x_1993_);
lean_dec_ref(v___x_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll___boxed(lean_object* v_query_1995_, lean_object* v_key_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Std_Http_URI_Query_findAll(v_query_1995_, v_key_1996_);
lean_dec_ref(v_key_1996_);
lean_dec_ref(v_query_1995_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert(lean_object* v_query_1998_, lean_object* v_key_1999_, lean_object* v_value_2000_){
_start:
{
lean_object* v_encodedKey_2001_; lean_object* v_encodedValue_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v_encodedKey_2001_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1999_);
v_encodedValue_2002_ = l_Std_Http_URI_EncodedQueryParam_encode(v_value_2000_);
v___x_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2003_, 0, v_encodedValue_2002_);
v___x_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2004_, 0, v_encodedKey_2001_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = lean_array_push(v_query_1998_, v___x_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert___boxed(lean_object* v_query_2006_, lean_object* v_key_2007_, lean_object* v_value_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Std_Http_URI_Query_insert(v_query_2006_, v_key_2007_, v_value_2008_);
lean_dec_ref(v_value_2008_);
lean_dec_ref(v_key_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object* v_query_2010_, lean_object* v_key_2011_, lean_object* v_value_2012_){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2013_, 0, v_key_2011_);
lean_ctor_set(v___x_2013_, 1, v_value_2012_);
v___x_2014_ = lean_array_push(v_query_2010_, v___x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_ofList(lean_object* v_pairs_2018_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_array_mk(v_pairs_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(lean_object* v_key_2020_, lean_object* v_as_2021_, size_t v_i_2022_, size_t v_stop_2023_){
_start:
{
uint8_t v___x_2024_; 
v___x_2024_ = lean_usize_dec_eq(v_i_2022_, v_stop_2023_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; lean_object* v_fst_2026_; uint8_t v___x_2027_; 
v___x_2025_ = lean_array_uget_borrowed(v_as_2021_, v_i_2022_);
v_fst_2026_ = lean_ctor_get(v___x_2025_, 0);
v___x_2027_ = lean_sarray_dec_eq(v_fst_2026_, v_key_2020_);
if (v___x_2027_ == 0)
{
size_t v___x_2028_; size_t v___x_2029_; 
v___x_2028_ = ((size_t)1ULL);
v___x_2029_ = lean_usize_add(v_i_2022_, v___x_2028_);
v_i_2022_ = v___x_2029_;
goto _start;
}
else
{
return v___x_2027_;
}
}
else
{
uint8_t v___x_2031_; 
v___x_2031_ = 0;
return v___x_2031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(lean_object* v_key_2032_, lean_object* v_as_2033_, lean_object* v_i_2034_, lean_object* v_stop_2035_){
_start:
{
size_t v_i_boxed_2036_; size_t v_stop_boxed_2037_; uint8_t v_res_2038_; lean_object* v_r_2039_; 
v_i_boxed_2036_ = lean_unbox_usize(v_i_2034_);
lean_dec(v_i_2034_);
v_stop_boxed_2037_ = lean_unbox_usize(v_stop_2035_);
lean_dec(v_stop_2035_);
v_res_2038_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_2032_, v_as_2033_, v_i_boxed_2036_, v_stop_boxed_2037_);
lean_dec_ref(v_as_2033_);
lean_dec_ref(v_key_2032_);
v_r_2039_ = lean_box(v_res_2038_);
return v_r_2039_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_containsEncoded(lean_object* v_query_2040_, lean_object* v_key_2041_){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2042_ = lean_unsigned_to_nat(0u);
v___x_2043_ = lean_array_get_size(v_query_2040_);
v___x_2044_ = lean_nat_dec_lt(v___x_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
return v___x_2044_;
}
else
{
if (v___x_2044_ == 0)
{
return v___x_2044_;
}
else
{
size_t v___x_2045_; size_t v___x_2046_; uint8_t v___x_2047_; 
v___x_2045_ = ((size_t)0ULL);
v___x_2046_ = lean_usize_of_nat(v___x_2043_);
v___x_2047_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_2041_, v_query_2040_, v___x_2045_, v___x_2046_);
return v___x_2047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_containsEncoded___boxed(lean_object* v_query_2048_, lean_object* v_key_2049_){
_start:
{
uint8_t v_res_2050_; lean_object* v_r_2051_; 
v_res_2050_ = l_Std_Http_URI_Query_containsEncoded(v_query_2048_, v_key_2049_);
lean_dec_ref(v_key_2049_);
lean_dec_ref(v_query_2048_);
v_r_2051_ = lean_box(v_res_2050_);
return v_r_2051_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_contains(lean_object* v_query_2052_, lean_object* v_key_2053_){
_start:
{
lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2054_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_2053_);
v___x_2055_ = l_Std_Http_URI_Query_containsEncoded(v_query_2052_, v___x_2054_);
lean_dec_ref(v___x_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_contains___boxed(lean_object* v_query_2056_, lean_object* v_key_2057_){
_start:
{
uint8_t v_res_2058_; lean_object* v_r_2059_; 
v_res_2058_ = l_Std_Http_URI_Query_contains(v_query_2056_, v_key_2057_);
lean_dec_ref(v_key_2057_);
lean_dec_ref(v_query_2056_);
v_r_2059_ = lean_box(v_res_2058_);
return v_r_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(lean_object* v_key_2060_, lean_object* v_as_2061_, size_t v_i_2062_, size_t v_stop_2063_, lean_object* v_b_2064_){
_start:
{
lean_object* v___y_2066_; uint8_t v___x_2070_; 
v___x_2070_ = lean_usize_dec_eq(v_i_2062_, v_stop_2063_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; lean_object* v_fst_2074_; uint8_t v___x_2075_; 
v___x_2071_ = lean_array_uget_borrowed(v_as_2061_, v_i_2062_);
v_fst_2074_ = lean_ctor_get(v___x_2071_, 0);
v___x_2075_ = lean_sarray_dec_eq(v_fst_2074_, v_key_2060_);
if (v___x_2075_ == 0)
{
goto v___jp_2072_;
}
else
{
if (v___x_2070_ == 0)
{
v___y_2066_ = v_b_2064_;
goto v___jp_2065_;
}
else
{
goto v___jp_2072_;
}
}
v___jp_2072_:
{
lean_object* v___x_2073_; 
lean_inc(v___x_2071_);
v___x_2073_ = lean_array_push(v_b_2064_, v___x_2071_);
v___y_2066_ = v___x_2073_;
goto v___jp_2065_;
}
}
else
{
return v_b_2064_;
}
v___jp_2065_:
{
size_t v___x_2067_; size_t v___x_2068_; 
v___x_2067_ = ((size_t)1ULL);
v___x_2068_ = lean_usize_add(v_i_2062_, v___x_2067_);
v_i_2062_ = v___x_2068_;
v_b_2064_ = v___y_2066_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(lean_object* v_key_2076_, lean_object* v_as_2077_, lean_object* v_i_2078_, lean_object* v_stop_2079_, lean_object* v_b_2080_){
_start:
{
size_t v_i_boxed_2081_; size_t v_stop_boxed_2082_; lean_object* v_res_2083_; 
v_i_boxed_2081_ = lean_unbox_usize(v_i_2078_);
lean_dec(v_i_2078_);
v_stop_boxed_2082_ = lean_unbox_usize(v_stop_2079_);
lean_dec(v_stop_2079_);
v_res_2083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2076_, v_as_2077_, v_i_boxed_2081_, v_stop_boxed_2082_, v_b_2080_);
lean_dec_ref(v_as_2077_);
lean_dec_ref(v_key_2076_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded(lean_object* v_query_2084_, lean_object* v_key_2085_){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = lean_array_get_size(v_query_2084_);
v___x_2088_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_2089_ = lean_nat_dec_lt(v___x_2086_, v___x_2087_);
if (v___x_2089_ == 0)
{
return v___x_2088_;
}
else
{
uint8_t v___x_2090_; 
v___x_2090_ = lean_nat_dec_le(v___x_2087_, v___x_2087_);
if (v___x_2090_ == 0)
{
if (v___x_2089_ == 0)
{
return v___x_2088_;
}
else
{
size_t v___x_2091_; size_t v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = ((size_t)0ULL);
v___x_2092_ = lean_usize_of_nat(v___x_2087_);
v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2085_, v_query_2084_, v___x_2091_, v___x_2092_, v___x_2088_);
return v___x_2093_;
}
}
else
{
size_t v___x_2094_; size_t v___x_2095_; lean_object* v___x_2096_; 
v___x_2094_ = ((size_t)0ULL);
v___x_2095_ = lean_usize_of_nat(v___x_2087_);
v___x_2096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2085_, v_query_2084_, v___x_2094_, v___x_2095_, v___x_2088_);
return v___x_2096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded___boxed(lean_object* v_query_2097_, lean_object* v_key_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Std_Http_URI_Query_eraseEncoded(v_query_2097_, v_key_2098_);
lean_dec_ref(v_key_2098_);
lean_dec_ref(v_query_2097_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase(lean_object* v_query_2100_, lean_object* v_key_2101_){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_2101_);
v___x_2103_ = l_Std_Http_URI_Query_eraseEncoded(v_query_2100_, v___x_2102_);
lean_dec_ref(v___x_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase___boxed(lean_object* v_query_2104_, lean_object* v_key_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Std_Http_URI_Query_erase(v_query_2104_, v_key_2105_);
lean_dec_ref(v_key_2105_);
lean_dec_ref(v_query_2104_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get(lean_object* v_query_2109_, lean_object* v_key_2110_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Std_Http_URI_Query_find_x3f(v_query_2109_, v_key_2110_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v___x_2112_; 
v___x_2112_ = lean_box(0);
return v___x_2112_;
}
else
{
lean_object* v_val_2113_; 
v_val_2113_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_val_2113_);
lean_dec_ref_known(v___x_2111_, 1);
if (lean_obj_tag(v_val_2113_) == 0)
{
lean_object* v___x_2114_; 
v___x_2114_ = ((lean_object*)(l_Std_Http_URI_Query_get___closed__0));
return v___x_2114_;
}
else
{
lean_object* v_val_2115_; lean_object* v___x_2116_; 
v_val_2115_ = lean_ctor_get(v_val_2113_, 0);
lean_inc(v_val_2115_);
lean_dec_ref_known(v_val_2113_, 1);
v___x_2116_ = l_Std_Http_URI_EncodedQueryParam_decode(v_val_2115_);
lean_dec(v_val_2115_);
return v___x_2116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get___boxed(lean_object* v_query_2117_, lean_object* v_key_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Std_Http_URI_Query_get(v_query_2117_, v_key_2118_);
lean_dec_ref(v_key_2118_);
lean_dec_ref(v_query_2117_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD(lean_object* v_query_2120_, lean_object* v_key_2121_, lean_object* v_default_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Std_Http_URI_Query_get(v_query_2120_, v_key_2121_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_inc_ref(v_default_2122_);
return v_default_2122_;
}
else
{
lean_object* v_val_2124_; 
v_val_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_val_2124_);
lean_dec_ref_known(v___x_2123_, 1);
return v_val_2124_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD___boxed(lean_object* v_query_2125_, lean_object* v_key_2126_, lean_object* v_default_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Std_Http_URI_Query_getD(v_query_2125_, v_key_2126_, v_default_2127_);
lean_dec_ref(v_default_2127_);
lean_dec_ref(v_key_2126_);
lean_dec_ref(v_query_2125_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set(lean_object* v_query_2129_, lean_object* v_key_2130_, lean_object* v_value_2131_){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = l_Std_Http_URI_Query_erase(v_query_2129_, v_key_2130_);
v___x_2133_ = l_Std_Http_URI_Query_insert(v___x_2132_, v_key_2130_, v_value_2131_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set___boxed(lean_object* v_query_2134_, lean_object* v_key_2135_, lean_object* v_value_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Std_Http_URI_Query_set(v_query_2134_, v_key_2135_, v_value_2136_);
lean_dec_ref(v_value_2136_);
lean_dec_ref(v_key_2135_);
lean_dec_ref(v_query_2134_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(size_t v_sz_2138_, size_t v_i_2139_, lean_object* v_bs_2140_){
_start:
{
uint8_t v___x_2141_; 
v___x_2141_ = lean_usize_dec_lt(v_i_2139_, v_sz_2138_);
if (v___x_2141_ == 0)
{
return v_bs_2140_;
}
else
{
lean_object* v_v_2142_; lean_object* v_fst_2143_; lean_object* v_snd_2144_; lean_object* v___x_2145_; lean_object* v_bs_x27_2146_; lean_object* v___x_2147_; size_t v___x_2148_; size_t v___x_2149_; lean_object* v___x_2150_; 
v_v_2142_ = lean_array_uget_borrowed(v_bs_2140_, v_i_2139_);
v_fst_2143_ = lean_ctor_get(v_v_2142_, 0);
lean_inc(v_fst_2143_);
v_snd_2144_ = lean_ctor_get(v_v_2142_, 1);
lean_inc(v_snd_2144_);
v___x_2145_ = lean_unsigned_to_nat(0u);
v_bs_x27_2146_ = lean_array_uset(v_bs_2140_, v_i_2139_, v___x_2145_);
v___x_2147_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2143_, v_snd_2144_);
v___x_2148_ = ((size_t)1ULL);
v___x_2149_ = lean_usize_add(v_i_2139_, v___x_2148_);
v___x_2150_ = lean_array_uset(v_bs_x27_2146_, v_i_2139_, v___x_2147_);
v_i_2139_ = v___x_2149_;
v_bs_2140_ = v___x_2150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0___boxed(lean_object* v_sz_2152_, lean_object* v_i_2153_, lean_object* v_bs_2154_){
_start:
{
size_t v_sz_boxed_2155_; size_t v_i_boxed_2156_; lean_object* v_res_2157_; 
v_sz_boxed_2155_ = lean_unbox_usize(v_sz_2152_);
lean_dec(v_sz_2152_);
v_i_boxed_2156_ = lean_unbox_usize(v_i_2153_);
lean_dec(v_i_2153_);
v_res_2157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_boxed_2155_, v_i_boxed_2156_, v_bs_2154_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toRawString(lean_object* v_query_2159_){
_start:
{
size_t v_sz_2160_; size_t v___x_2161_; lean_object* v_params_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v_sz_2160_ = lean_array_size(v_query_2159_);
v___x_2161_ = ((size_t)0ULL);
v_params_2162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_2160_, v___x_2161_, v_query_2159_);
v___x_2163_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2164_ = lean_array_to_list(v_params_2162_);
v___x_2165_ = l_String_intercalate(v___x_2163_, v___x_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0(lean_object* v_x_2167_){
_start:
{
lean_object* v_fst_2168_; lean_object* v_snd_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v_fst_2168_ = lean_ctor_get(v_x_2167_, 0);
v_snd_2169_ = lean_ctor_get(v_x_2167_, 1);
v___x_2170_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
v___x_2171_ = l_Std_Http_URI_Query_insert(v___x_2170_, v_fst_2168_, v_snd_2169_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0___boxed(lean_object* v_x_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l_Std_Http_URI_Query_instSingletonProdString___lam__0(v_x_2172_);
lean_dec_ref(v_x_2172_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0(lean_object* v_x_2176_, lean_object* v_q_2177_){
_start:
{
lean_object* v_fst_2178_; lean_object* v_snd_2179_; lean_object* v___x_2180_; 
v_fst_2178_ = lean_ctor_get(v_x_2176_, 0);
v_snd_2179_ = lean_ctor_get(v_x_2176_, 1);
v___x_2180_ = l_Std_Http_URI_Query_insert(v_q_2177_, v_fst_2178_, v_snd_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0___boxed(lean_object* v_x_2181_, lean_object* v_q_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Std_Http_URI_Query_instInsertProdString___lam__0(v_x_2181_, v_q_2182_);
lean_dec_ref(v_x_2181_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__0(lean_object* v_x_2186_){
_start:
{
lean_object* v_fst_2187_; lean_object* v_snd_2188_; lean_object* v___x_2189_; 
v_fst_2187_ = lean_ctor_get(v_x_2186_, 0);
lean_inc(v_fst_2187_);
v_snd_2188_ = lean_ctor_get(v_x_2186_, 1);
lean_inc(v_snd_2188_);
lean_dec_ref(v_x_2186_);
v___x_2189_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2187_, v_snd_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__1(lean_object* v___f_2191_, lean_object* v_q_2192_){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2193_ = lean_array_get_size(v_q_2192_);
v___x_2194_ = lean_unsigned_to_nat(0u);
v___x_2195_ = lean_nat_dec_eq(v___x_2193_, v___x_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v_encodedParams_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2196_ = lean_array_to_list(v_q_2192_);
v___x_2197_ = lean_box(0);
v_encodedParams_2198_ = l_List_mapTR_loop___redArg(v___f_2191_, v___x_2196_, v___x_2197_);
v___x_2199_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2200_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2201_ = l_String_intercalate(v___x_2200_, v_encodedParams_2198_);
v___x_2202_ = lean_string_append(v___x_2199_, v___x_2201_);
lean_dec_ref(v___x_2201_);
return v___x_2202_;
}
else
{
lean_object* v___x_2203_; 
lean_dec_ref(v_q_2192_);
lean_dec_ref(v___f_2191_);
v___x_2203_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2203_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
if (lean_obj_tag(v_a_2208_) == 0)
{
lean_object* v___x_2210_; 
v___x_2210_ = l_List_reverse___redArg(v_a_2209_);
return v___x_2210_;
}
else
{
lean_object* v_head_2211_; lean_object* v_tail_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2223_; 
v_head_2211_ = lean_ctor_get(v_a_2208_, 0);
v_tail_2212_ = lean_ctor_get(v_a_2208_, 1);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_a_2208_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2214_ = v_a_2208_;
v_isShared_2215_ = v_isSharedCheck_2223_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_tail_2212_);
lean_inc(v_head_2211_);
lean_dec(v_a_2208_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2223_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v_fst_2216_; lean_object* v_snd_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
v_fst_2216_ = lean_ctor_get(v_head_2211_, 0);
lean_inc(v_fst_2216_);
v_snd_2217_ = lean_ctor_get(v_head_2211_, 1);
lean_inc(v_snd_2217_);
lean_dec(v_head_2211_);
v___x_2218_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2216_, v_snd_2217_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v_a_2209_);
lean_ctor_set(v___x_2214_, 0, v___x_2218_);
v___x_2220_ = v___x_2214_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_a_2209_);
v___x_2220_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
v_a_2208_ = v_tail_2212_;
v_a_2209_ = v___x_2220_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatOption(lean_object* v_x_2224_){
_start:
{
if (lean_obj_tag(v_x_2224_) == 0)
{
lean_object* v___x_2225_; 
v___x_2225_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2225_;
}
else
{
lean_object* v_val_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; 
v_val_2226_ = lean_ctor_get(v_x_2224_, 0);
lean_inc(v_val_2226_);
lean_dec_ref_known(v_x_2224_, 1);
v___x_2227_ = lean_array_get_size(v_val_2226_);
v___x_2228_ = lean_unsigned_to_nat(0u);
v___x_2229_ = lean_nat_dec_eq(v___x_2227_, v___x_2228_);
if (v___x_2229_ == 0)
{
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v_encodedParams_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2230_ = lean_array_to_list(v_val_2226_);
v___x_2231_ = lean_box(0);
v_encodedParams_2232_ = l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(v___x_2230_, v___x_2231_);
v___x_2233_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2234_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2235_ = l_String_intercalate(v___x_2234_, v_encodedParams_2232_);
v___x_2236_ = lean_string_append(v___x_2233_, v___x_2235_);
lean_dec_ref(v___x_2235_);
return v___x_2236_;
}
else
{
lean_object* v___x_2237_; 
lean_dec(v_val_2226_);
v___x_2237_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2237_;
}
}
else
{
lean_object* v___x_2238_; 
lean_dec(v_val_2226_);
v___x_2238_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
return v___x_2238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(lean_object* v_x_2239_, lean_object* v_x_2240_){
_start:
{
if (lean_obj_tag(v_x_2239_) == 0)
{
lean_object* v___x_2241_; 
v___x_2241_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2241_;
}
else
{
lean_object* v_val_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_val_2242_ = lean_ctor_get(v_x_2239_, 0);
lean_inc(v_val_2242_);
lean_dec_ref_known(v_x_2239_, 1);
v___x_2243_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2244_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_val_2242_);
v___x_2245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2243_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = l_Repr_addAppParen(v___x_2245_, v_x_2240_);
return v___x_2246_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(lean_object* v_x_2247_, lean_object* v_x_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_x_2247_, v_x_2248_);
lean_dec(v_x_2248_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object* v_x_2250_, lean_object* v_x_2251_){
_start:
{
if (lean_obj_tag(v_x_2250_) == 0)
{
lean_object* v___x_2252_; 
v___x_2252_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2252_;
}
else
{
lean_object* v_val_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v_val_2253_ = lean_ctor_get(v_x_2250_, 0);
lean_inc(v_val_2253_);
lean_dec_ref_known(v_x_2250_, 1);
v___x_2254_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2255_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_val_2253_);
v___x_2256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = l_Repr_addAppParen(v___x_2256_, v_x_2251_);
return v___x_2257_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1___boxed(lean_object* v_x_2258_, lean_object* v_x_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_x_2258_, v_x_2259_);
lean_dec(v_x_2259_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(lean_object* v_x_2261_, lean_object* v_x_2262_){
_start:
{
if (lean_obj_tag(v_x_2261_) == 0)
{
lean_object* v___x_2263_; 
v___x_2263_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2263_;
}
else
{
lean_object* v_val_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2275_; 
v_val_2264_ = lean_ctor_get(v_x_2261_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_x_2261_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2266_ = v_x_2261_;
v_isShared_2267_ = v_isSharedCheck_2275_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_val_2264_);
lean_dec(v_x_2261_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2275_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2268_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2269_ = l_String_quote(v_val_2264_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set_tag(v___x_2266_, 3);
lean_ctor_set(v___x_2266_, 0, v___x_2269_);
v___x_2271_ = v___x_2266_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2268_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
v___x_2273_ = l_Repr_addAppParen(v___x_2272_, v_x_2262_);
return v___x_2273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2___boxed(lean_object* v_x_2276_, lean_object* v_x_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_x_2276_, v_x_2277_);
lean_dec(v_x_2277_);
return v_res_2278_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = lean_unsigned_to_nat(10u);
v___x_2289_ = lean_nat_to_int(v___x_2288_);
return v___x_2289_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_unsigned_to_nat(13u);
v___x_2294_ = lean_nat_to_int(v___x_2293_);
return v___x_2294_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = lean_unsigned_to_nat(9u);
v___x_2302_ = lean_nat_to_int(v___x_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___redArg(lean_object* v_x_2306_){
_start:
{
lean_object* v_scheme_2307_; lean_object* v_authority_2308_; lean_object* v_path_2309_; lean_object* v_query_2310_; lean_object* v_fragment_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_scheme_2307_ = lean_ctor_get(v_x_2306_, 0);
lean_inc_ref(v_scheme_2307_);
v_authority_2308_ = lean_ctor_get(v_x_2306_, 1);
lean_inc(v_authority_2308_);
v_path_2309_ = lean_ctor_get(v_x_2306_, 2);
lean_inc_ref(v_path_2309_);
v_query_2310_ = lean_ctor_get(v_x_2306_, 3);
lean_inc(v_query_2310_);
v_fragment_2311_ = lean_ctor_get(v_x_2306_, 4);
lean_inc(v_fragment_2311_);
lean_dec_ref(v_x_2306_);
v___x_2312_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2313_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2314_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2315_ = l_String_quote(v_scheme_2307_);
v___x_2316_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
v___x_2317_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2314_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = 0;
v___x_2319_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set_uint8(v___x_2319_, sizeof(void*)*1, v___x_2318_);
v___x_2320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2313_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = lean_box(1);
v___x_2324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2322_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
v___x_2325_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__6));
v___x_2326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
v___x_2327_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___x_2312_);
v___x_2328_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_2329_ = lean_unsigned_to_nat(0u);
v___x_2330_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_2308_, v___x_2329_);
v___x_2331_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2328_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*1, v___x_2318_);
v___x_2333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2327_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
v___x_2334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
lean_ctor_set(v___x_2334_, 1, v___x_2321_);
v___x_2335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
lean_ctor_set(v___x_2335_, 1, v___x_2323_);
v___x_2336_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_2337_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2335_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v___x_2338_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
lean_ctor_set(v___x_2338_, 1, v___x_2312_);
v___x_2339_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2340_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_2309_);
v___x_2341_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2339_);
lean_ctor_set(v___x_2341_, 1, v___x_2340_);
v___x_2342_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
lean_ctor_set_uint8(v___x_2342_, sizeof(void*)*1, v___x_2318_);
v___x_2343_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2338_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
v___x_2344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
lean_ctor_set(v___x_2344_, 1, v___x_2321_);
v___x_2345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
lean_ctor_set(v___x_2345_, 1, v___x_2323_);
v___x_2346_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_2347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
lean_ctor_set(v___x_2348_, 1, v___x_2312_);
v___x_2349_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_2350_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_2310_, v___x_2329_);
v___x_2351_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2349_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
v___x_2352_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
lean_ctor_set_uint8(v___x_2352_, sizeof(void*)*1, v___x_2318_);
v___x_2353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2348_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
v___x_2354_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
lean_ctor_set(v___x_2354_, 1, v___x_2321_);
v___x_2355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
lean_ctor_set(v___x_2355_, 1, v___x_2323_);
v___x_2356_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_2357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
lean_ctor_set(v___x_2358_, 1, v___x_2312_);
v___x_2359_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_2360_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_2311_, v___x_2329_);
v___x_2361_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*1, v___x_2318_);
v___x_2363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2358_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
v___x_2364_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2365_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
lean_ctor_set(v___x_2366_, 1, v___x_2363_);
v___x_2367_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2366_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___x_2369_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2364_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
lean_ctor_set_uint8(v___x_2370_, sizeof(void*)*1, v___x_2318_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr(lean_object* v_x_2371_, lean_object* v_prec_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Std_Http_instReprURI_repr___redArg(v_x_2371_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___boxed(lean_object* v_x_2374_, lean_object* v_prec_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Std_Http_instReprURI_repr(v_x_2374_, v_prec_2375_);
lean_dec(v_prec_2375_);
return v_res_2376_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object* v_x_2385_, lean_object* v_x_2386_){
_start:
{
if (lean_obj_tag(v_x_2385_) == 0)
{
if (lean_obj_tag(v_x_2386_) == 0)
{
uint8_t v___x_2387_; 
v___x_2387_ = 1;
return v___x_2387_;
}
else
{
uint8_t v___x_2388_; 
v___x_2388_ = 0;
return v___x_2388_;
}
}
else
{
if (lean_obj_tag(v_x_2386_) == 0)
{
uint8_t v___x_2389_; 
v___x_2389_ = 0;
return v___x_2389_;
}
else
{
lean_object* v_val_2390_; lean_object* v_val_2391_; uint8_t v___x_2392_; 
v_val_2390_ = lean_ctor_get(v_x_2385_, 0);
v_val_2391_ = lean_ctor_get(v_x_2386_, 0);
v___x_2392_ = l_Std_Http_URI_instBEqAuthority_beq(v_val_2390_, v_val_2391_);
return v___x_2392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object* v_x_2393_, lean_object* v_x_2394_){
_start:
{
uint8_t v_res_2395_; lean_object* v_r_2396_; 
v_res_2395_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_x_2393_, v_x_2394_);
lean_dec(v_x_2394_);
lean_dec(v_x_2393_);
v_r_2396_ = lean_box(v_res_2395_);
return v_r_2396_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object* v_x_2397_, lean_object* v_x_2398_){
_start:
{
if (lean_obj_tag(v_x_2397_) == 0)
{
if (lean_obj_tag(v_x_2398_) == 0)
{
uint8_t v___x_2399_; 
v___x_2399_ = 1;
return v___x_2399_;
}
else
{
uint8_t v___x_2400_; 
v___x_2400_ = 0;
return v___x_2400_;
}
}
else
{
if (lean_obj_tag(v_x_2398_) == 0)
{
uint8_t v___x_2401_; 
v___x_2401_ = 0;
return v___x_2401_;
}
else
{
lean_object* v_val_2402_; lean_object* v_val_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
v_val_2402_ = lean_ctor_get(v_x_2397_, 0);
v_val_2403_ = lean_ctor_get(v_x_2398_, 0);
v___x_2404_ = lean_array_get_size(v_val_2402_);
v___x_2405_ = lean_array_get_size(v_val_2403_);
v___x_2406_ = lean_nat_dec_eq(v___x_2404_, v___x_2405_);
if (v___x_2406_ == 0)
{
return v___x_2406_;
}
else
{
uint8_t v___x_2407_; 
v___x_2407_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_val_2402_, v_val_2403_, v___x_2404_);
return v___x_2407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object* v_x_2408_, lean_object* v_x_2409_){
_start:
{
uint8_t v_res_2410_; lean_object* v_r_2411_; 
v_res_2410_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_x_2408_, v_x_2409_);
lean_dec(v_x_2409_);
lean_dec(v_x_2408_);
v_r_2411_ = lean_box(v_res_2410_);
return v_r_2411_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2(lean_object* v_x_2412_, lean_object* v_x_2413_){
_start:
{
if (lean_obj_tag(v_x_2412_) == 0)
{
if (lean_obj_tag(v_x_2413_) == 0)
{
uint8_t v___x_2414_; 
v___x_2414_ = 1;
return v___x_2414_;
}
else
{
uint8_t v___x_2415_; 
v___x_2415_ = 0;
return v___x_2415_;
}
}
else
{
if (lean_obj_tag(v_x_2413_) == 0)
{
uint8_t v___x_2416_; 
v___x_2416_ = 0;
return v___x_2416_;
}
else
{
lean_object* v_val_2417_; lean_object* v_val_2418_; uint8_t v___x_2419_; 
v_val_2417_ = lean_ctor_get(v_x_2412_, 0);
v_val_2418_ = lean_ctor_get(v_x_2413_, 0);
v___x_2419_ = lean_string_dec_eq(v_val_2417_, v_val_2418_);
return v___x_2419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2___boxed(lean_object* v_x_2420_, lean_object* v_x_2421_){
_start:
{
uint8_t v_res_2422_; lean_object* v_r_2423_; 
v_res_2422_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_x_2420_, v_x_2421_);
lean_dec(v_x_2421_);
lean_dec(v_x_2420_);
v_r_2423_ = lean_box(v_res_2422_);
return v_r_2423_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object* v_x_2424_, lean_object* v_x_2425_){
_start:
{
lean_object* v_scheme_2426_; lean_object* v_authority_2427_; lean_object* v_path_2428_; lean_object* v_query_2429_; lean_object* v_fragment_2430_; lean_object* v_scheme_2431_; lean_object* v_authority_2432_; lean_object* v_path_2433_; lean_object* v_query_2434_; lean_object* v_fragment_2435_; uint8_t v___x_2436_; 
v_scheme_2426_ = lean_ctor_get(v_x_2424_, 0);
v_authority_2427_ = lean_ctor_get(v_x_2424_, 1);
v_path_2428_ = lean_ctor_get(v_x_2424_, 2);
v_query_2429_ = lean_ctor_get(v_x_2424_, 3);
v_fragment_2430_ = lean_ctor_get(v_x_2424_, 4);
v_scheme_2431_ = lean_ctor_get(v_x_2425_, 0);
v_authority_2432_ = lean_ctor_get(v_x_2425_, 1);
v_path_2433_ = lean_ctor_get(v_x_2425_, 2);
v_query_2434_ = lean_ctor_get(v_x_2425_, 3);
v_fragment_2435_ = lean_ctor_get(v_x_2425_, 4);
v___x_2436_ = lean_string_dec_eq(v_scheme_2426_, v_scheme_2431_);
if (v___x_2436_ == 0)
{
return v___x_2436_;
}
else
{
uint8_t v___x_2437_; 
v___x_2437_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_2427_, v_authority_2432_);
if (v___x_2437_ == 0)
{
return v___x_2437_;
}
else
{
uint8_t v___x_2438_; 
v___x_2438_ = l_Std_Http_URI_instBEqPath_beq(v_path_2428_, v_path_2433_);
if (v___x_2438_ == 0)
{
return v___x_2438_;
}
else
{
uint8_t v___x_2439_; 
v___x_2439_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_2429_, v_query_2434_);
if (v___x_2439_ == 0)
{
return v___x_2439_;
}
else
{
uint8_t v___x_2440_; 
v___x_2440_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_2430_, v_fragment_2435_);
return v___x_2440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object* v_x_2441_, lean_object* v_x_2442_){
_start:
{
uint8_t v_res_2443_; lean_object* v_r_2444_; 
v_res_2443_ = l_Std_Http_instBEqURI_beq(v_x_2441_, v_x_2442_);
lean_dec_ref(v_x_2442_);
lean_dec_ref(v_x_2441_);
v_r_2444_ = lean_box(v_res_2443_);
return v_r_2444_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__1(lean_object* v___f_2449_, lean_object* v_uri_2450_){
_start:
{
lean_object* v_scheme_2451_; lean_object* v_authority_2452_; lean_object* v_path_2453_; lean_object* v_query_2454_; lean_object* v_fragment_2455_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2478_; 
v_scheme_2451_ = lean_ctor_get(v_uri_2450_, 0);
lean_inc_ref(v_scheme_2451_);
v_authority_2452_ = lean_ctor_get(v_uri_2450_, 1);
lean_inc(v_authority_2452_);
v_path_2453_ = lean_ctor_get(v_uri_2450_, 2);
lean_inc_ref(v_path_2453_);
v_query_2454_ = lean_ctor_get(v_uri_2450_, 3);
lean_inc(v_query_2454_);
v_fragment_2455_ = lean_ctor_get(v_uri_2450_, 4);
lean_inc(v_fragment_2455_);
lean_dec_ref(v_uri_2450_);
if (lean_obj_tag(v_authority_2452_) == 0)
{
lean_object* v___x_2489_; 
v___x_2489_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2478_ = v___x_2489_;
goto v___jp_2477_;
}
else
{
lean_object* v_val_2490_; lean_object* v_userInfo_2491_; lean_object* v_host_2492_; lean_object* v_port_2493_; lean_object* v___x_2494_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2513_; 
v_val_2490_ = lean_ctor_get(v_authority_2452_, 0);
lean_inc(v_val_2490_);
lean_dec_ref_known(v_authority_2452_, 1);
v_userInfo_2491_ = lean_ctor_get(v_val_2490_, 0);
lean_inc(v_userInfo_2491_);
v_host_2492_ = lean_ctor_get(v_val_2490_, 1);
lean_inc_ref(v_host_2492_);
v_port_2493_ = lean_ctor_get(v_val_2490_, 2);
lean_inc(v_port_2493_);
lean_dec(v_val_2490_);
v___x_2494_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_2491_) == 0)
{
lean_object* v___x_2523_; 
v___x_2523_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2513_ = v___x_2523_;
goto v___jp_2512_;
}
else
{
lean_object* v_val_2524_; lean_object* v_password_2525_; 
v_val_2524_ = lean_ctor_get(v_userInfo_2491_, 0);
lean_inc(v_val_2524_);
lean_dec_ref_known(v_userInfo_2491_, 1);
v_password_2525_ = lean_ctor_get(v_val_2524_, 1);
if (lean_obj_tag(v_password_2525_) == 0)
{
lean_object* v_username_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v_username_2526_ = lean_ctor_get(v_val_2524_, 0);
lean_inc_ref(v_username_2526_);
lean_dec(v_val_2524_);
v___x_2527_ = lean_string_from_utf8_unchecked(v_username_2526_);
v___x_2528_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2529_ = lean_string_append(v___x_2527_, v___x_2528_);
v___y_2513_ = v___x_2529_;
goto v___jp_2512_;
}
else
{
lean_object* v_username_2530_; lean_object* v_val_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
lean_inc_ref(v_password_2525_);
v_username_2530_ = lean_ctor_get(v_val_2524_, 0);
lean_inc_ref(v_username_2530_);
lean_dec(v_val_2524_);
v_val_2531_ = lean_ctor_get(v_password_2525_, 0);
lean_inc(v_val_2531_);
lean_dec_ref_known(v_password_2525_, 1);
v___x_2532_ = lean_string_from_utf8_unchecked(v_username_2530_);
v___x_2533_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2534_ = lean_string_append(v___x_2532_, v___x_2533_);
v___x_2535_ = lean_string_from_utf8_unchecked(v_val_2531_);
v___x_2536_ = lean_string_append(v___x_2534_, v___x_2535_);
lean_dec_ref(v___x_2535_);
v___x_2537_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2538_ = lean_string_append(v___x_2536_, v___x_2537_);
v___y_2513_ = v___x_2538_;
goto v___jp_2512_;
}
}
v___jp_2495_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = lean_string_append(v___y_2496_, v___y_2497_);
lean_dec_ref(v___y_2497_);
v___x_2500_ = lean_string_append(v___x_2499_, v___y_2498_);
lean_dec_ref(v___y_2498_);
v___x_2501_ = lean_string_append(v___x_2494_, v___x_2500_);
lean_dec_ref(v___x_2500_);
v___y_2478_ = v___x_2501_;
goto v___jp_2477_;
}
v___jp_2502_:
{
switch(lean_obj_tag(v_port_2493_))
{
case 0:
{
lean_object* v___x_2505_; 
v___x_2505_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2496_ = v___y_2503_;
v___y_2497_ = v___y_2504_;
v___y_2498_ = v___x_2505_;
goto v___jp_2495_;
}
case 1:
{
lean_object* v___x_2506_; 
v___x_2506_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_2496_ = v___y_2503_;
v___y_2497_ = v___y_2504_;
v___y_2498_ = v___x_2506_;
goto v___jp_2495_;
}
default: 
{
uint16_t v_port_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v_port_2507_ = lean_ctor_get_uint16(v_port_2493_, 0);
lean_dec_ref_known(v_port_2493_, 0);
v___x_2508_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2509_ = lean_uint16_to_nat(v_port_2507_);
v___x_2510_ = l_Nat_reprFast(v___x_2509_);
v___x_2511_ = lean_string_append(v___x_2508_, v___x_2510_);
lean_dec_ref(v___x_2510_);
v___y_2496_ = v___y_2503_;
v___y_2497_ = v___y_2504_;
v___y_2498_ = v___x_2511_;
goto v___jp_2495_;
}
}
}
v___jp_2512_:
{
switch(lean_obj_tag(v_host_2492_))
{
case 0:
{
lean_object* v_name_2514_; 
v_name_2514_ = lean_ctor_get(v_host_2492_, 0);
lean_inc_ref(v_name_2514_);
lean_dec_ref_known(v_host_2492_, 1);
v___y_2503_ = v___y_2513_;
v___y_2504_ = v_name_2514_;
goto v___jp_2502_;
}
case 1:
{
lean_object* v_ipv4_2515_; lean_object* v___x_2516_; 
v_ipv4_2515_ = lean_ctor_get(v_host_2492_, 0);
lean_inc_ref(v_ipv4_2515_);
lean_dec_ref_known(v_host_2492_, 1);
v___x_2516_ = lean_uv_ntop_v4(v_ipv4_2515_);
lean_dec_ref(v_ipv4_2515_);
v___y_2503_ = v___y_2513_;
v___y_2504_ = v___x_2516_;
goto v___jp_2502_;
}
default: 
{
lean_object* v_ipv6_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v_ipv6_2517_ = lean_ctor_get(v_host_2492_, 0);
lean_inc_ref(v_ipv6_2517_);
lean_dec_ref_known(v_host_2492_, 1);
v___x_2518_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_2519_ = lean_uv_ntop_v6(v_ipv6_2517_);
lean_dec_ref(v_ipv6_2517_);
v___x_2520_ = lean_string_append(v___x_2518_, v___x_2519_);
lean_dec_ref(v___x_2519_);
v___x_2521_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_2522_ = lean_string_append(v___x_2520_, v___x_2521_);
v___y_2503_ = v___y_2513_;
v___y_2504_ = v___x_2522_;
goto v___jp_2502_;
}
}
}
}
v___jp_2456_:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2461_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2462_ = lean_string_append(v_scheme_2451_, v___x_2461_);
v___x_2463_ = lean_string_append(v___x_2462_, v___y_2458_);
lean_dec_ref(v___y_2458_);
v___x_2464_ = lean_string_append(v___x_2463_, v___y_2457_);
lean_dec_ref(v___y_2457_);
v___x_2465_ = lean_string_append(v___x_2464_, v___y_2459_);
lean_dec_ref(v___y_2459_);
v___x_2466_ = lean_string_append(v___x_2465_, v___y_2460_);
lean_dec_ref(v___y_2460_);
return v___x_2466_;
}
v___jp_2467_:
{
lean_object* v_queryPart_2470_; 
v_queryPart_2470_ = l_Std_Http_URI_Query_formatOption(v_query_2454_);
if (lean_obj_tag(v_fragment_2455_) == 0)
{
lean_object* v___x_2471_; 
v___x_2471_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2457_ = v___y_2469_;
v___y_2458_ = v___y_2468_;
v___y_2459_ = v_queryPart_2470_;
v___y_2460_ = v___x_2471_;
goto v___jp_2456_;
}
else
{
lean_object* v_val_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_val_2472_ = lean_ctor_get(v_fragment_2455_, 0);
lean_inc(v_val_2472_);
lean_dec_ref_known(v_fragment_2455_, 1);
v___x_2473_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_2474_ = l_Std_Http_URI_EncodedFragment_encode(v_val_2472_);
lean_dec(v_val_2472_);
v___x_2475_ = lean_string_from_utf8_unchecked(v___x_2474_);
v___x_2476_ = lean_string_append(v___x_2473_, v___x_2475_);
lean_dec_ref(v___x_2475_);
v___y_2457_ = v___y_2469_;
v___y_2458_ = v___y_2468_;
v___y_2459_ = v_queryPart_2470_;
v___y_2460_ = v___x_2476_;
goto v___jp_2456_;
}
}
v___jp_2477_:
{
lean_object* v_segments_2479_; uint8_t v_absolute_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; size_t v_sz_2483_; size_t v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v_result_2487_; 
v_segments_2479_ = lean_ctor_get(v_path_2453_, 0);
lean_inc_ref(v_segments_2479_);
v_absolute_2480_ = lean_ctor_get_uint8(v_path_2453_, sizeof(void*)*1);
lean_dec_ref(v_path_2453_);
v___x_2481_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_2482_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_2483_ = lean_array_size(v_segments_2479_);
v___x_2484_ = ((size_t)0ULL);
v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2482_, v___f_2449_, v_sz_2483_, v___x_2484_, v_segments_2479_);
v___x_2486_ = lean_array_to_list(v___x_2485_);
v_result_2487_ = l_String_intercalate(v___x_2481_, v___x_2486_);
if (v_absolute_2480_ == 0)
{
v___y_2468_ = v___y_2478_;
v___y_2469_ = v_result_2487_;
goto v___jp_2467_;
}
else
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_string_append(v___x_2481_, v_result_2487_);
lean_dec_ref(v_result_2487_);
v___y_2468_ = v___y_2478_;
v___y_2469_ = v___x_2488_;
goto v___jp_2467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x3f(lean_object* v_b_2551_, lean_object* v_scheme_2552_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Std_Http_URI_Scheme_ofString_x3f(v_scheme_2552_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v___x_2554_; 
lean_dec_ref(v_b_2551_);
v___x_2554_ = lean_box(0);
return v___x_2554_;
}
else
{
lean_object* v_userInfo_2555_; lean_object* v_host_2556_; lean_object* v_port_2557_; lean_object* v_pathSegments_2558_; lean_object* v_query_2559_; lean_object* v_fragment_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2575_; 
v_userInfo_2555_ = lean_ctor_get(v_b_2551_, 1);
v_host_2556_ = lean_ctor_get(v_b_2551_, 2);
v_port_2557_ = lean_ctor_get(v_b_2551_, 3);
v_pathSegments_2558_ = lean_ctor_get(v_b_2551_, 4);
v_query_2559_ = lean_ctor_get(v_b_2551_, 5);
v_fragment_2560_ = lean_ctor_get(v_b_2551_, 6);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_b_2551_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; 
v_unused_2576_ = lean_ctor_get(v_b_2551_, 0);
lean_dec(v_unused_2576_);
v___x_2562_ = v_b_2551_;
v_isShared_2563_ = v_isSharedCheck_2575_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_fragment_2560_);
lean_inc(v_query_2559_);
lean_inc(v_pathSegments_2558_);
lean_inc(v_port_2557_);
lean_inc(v_host_2556_);
lean_inc(v_userInfo_2555_);
lean_dec(v_b_2551_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2575_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
lean_inc_ref(v___x_2553_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2553_);
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2553_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_userInfo_2555_);
lean_ctor_set(v_reuseFailAlloc_2574_, 2, v_host_2556_);
lean_ctor_set(v_reuseFailAlloc_2574_, 3, v_port_2557_);
lean_ctor_set(v_reuseFailAlloc_2574_, 4, v_pathSegments_2558_);
lean_ctor_set(v_reuseFailAlloc_2574_, 5, v_query_2559_);
lean_ctor_set(v_reuseFailAlloc_2574_, 6, v_fragment_2560_);
v___x_2565_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2572_ == 0)
{
lean_object* v_unused_2573_; 
v_unused_2573_ = lean_ctor_get(v___x_2553_, 0);
lean_dec(v_unused_2573_);
v___x_2567_ = v___x_2553_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_dec(v___x_2553_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(lean_object* v_msg_2577_){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = ((lean_object*)(l_Std_Http_URI_instInhabitedBuilder_default));
v___x_2579_ = lean_panic_fn_borrowed(v___x_2578_, v_msg_2577_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x21(lean_object* v_b_2581_, lean_object* v_scheme_2582_){
_start:
{
lean_object* v___x_2583_; 
lean_inc_ref(v_scheme_2582_);
v___x_2583_ = l_Std_Http_URI_Builder_setScheme_x3f(v_b_2581_, v_scheme_2582_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2584_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2585_ = ((lean_object*)(l_Std_Http_URI_Builder_setScheme_x21___closed__0));
v___x_2586_ = lean_unsigned_to_nat(687u);
v___x_2587_ = lean_unsigned_to_nat(14u);
v___x_2588_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_2589_ = l_String_quote(v_scheme_2582_);
v___x_2590_ = lean_string_append(v___x_2588_, v___x_2589_);
lean_dec_ref(v___x_2589_);
v___x_2591_ = l_mkPanicMessageWithDecl(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2587_, v___x_2590_);
lean_dec_ref(v___x_2590_);
v___x_2592_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2591_);
return v___x_2592_;
}
else
{
lean_object* v_val_2593_; 
lean_dec_ref(v_scheme_2582_);
v_val_2593_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_val_2593_);
lean_dec_ref_known(v___x_2583_, 1);
return v_val_2593_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo(lean_object* v_b_2594_, lean_object* v_username_2595_, lean_object* v_password_2596_){
_start:
{
lean_object* v_scheme_2597_; lean_object* v_host_2598_; lean_object* v_port_2599_; lean_object* v_pathSegments_2600_; lean_object* v_query_2601_; lean_object* v_fragment_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2625_; 
v_scheme_2597_ = lean_ctor_get(v_b_2594_, 0);
v_host_2598_ = lean_ctor_get(v_b_2594_, 2);
v_port_2599_ = lean_ctor_get(v_b_2594_, 3);
v_pathSegments_2600_ = lean_ctor_get(v_b_2594_, 4);
v_query_2601_ = lean_ctor_get(v_b_2594_, 5);
v_fragment_2602_ = lean_ctor_get(v_b_2594_, 6);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_b_2594_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; 
v_unused_2626_ = lean_ctor_get(v_b_2594_, 1);
lean_dec(v_unused_2626_);
v___x_2604_ = v_b_2594_;
v_isShared_2605_ = v_isSharedCheck_2625_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_fragment_2602_);
lean_inc(v_query_2601_);
lean_inc(v_pathSegments_2600_);
lean_inc(v_port_2599_);
lean_inc(v_host_2598_);
lean_inc(v_scheme_2597_);
lean_dec(v_b_2594_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2625_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___y_2607_; lean_object* v___x_2612_; 
v___x_2612_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_2595_);
if (lean_obj_tag(v_password_2596_) == 0)
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = lean_box(0);
v___x_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2612_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___y_2607_ = v___x_2614_;
goto v___jp_2606_;
}
else
{
lean_object* v_val_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2624_; 
v_val_2615_ = lean_ctor_get(v_password_2596_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v_password_2596_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2617_ = v_password_2596_;
v_isShared_2618_ = v_isSharedCheck_2624_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_val_2615_);
lean_dec(v_password_2596_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2624_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2619_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_2615_);
lean_dec(v_val_2615_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2619_);
v___x_2621_ = v___x_2617_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2622_; 
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2612_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
v___y_2607_ = v___x_2622_;
goto v___jp_2606_;
}
}
}
v___jp_2606_:
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
v___x_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2608_, 0, v___y_2607_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 1, v___x_2608_);
v___x_2610_ = v___x_2604_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_scheme_2597_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v___x_2608_);
lean_ctor_set(v_reuseFailAlloc_2611_, 2, v_host_2598_);
lean_ctor_set(v_reuseFailAlloc_2611_, 3, v_port_2599_);
lean_ctor_set(v_reuseFailAlloc_2611_, 4, v_pathSegments_2600_);
lean_ctor_set(v_reuseFailAlloc_2611_, 5, v_query_2601_);
lean_ctor_set(v_reuseFailAlloc_2611_, 6, v_fragment_2602_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo___boxed(lean_object* v_b_2627_, lean_object* v_username_2628_, lean_object* v_password_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Std_Http_URI_Builder_setUserInfo(v_b_2627_, v_username_2628_, v_password_2629_);
lean_dec_ref(v_username_2628_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x3f(lean_object* v_b_2631_, lean_object* v_name_2632_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Std_Http_URI_DomainName_ofString_x3f(v_name_2632_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v___x_2634_; 
lean_dec_ref(v_b_2631_);
v___x_2634_ = lean_box(0);
return v___x_2634_;
}
else
{
lean_object* v_val_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2658_; 
v_val_2635_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2637_ = v___x_2633_;
v_isShared_2638_ = v_isSharedCheck_2658_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_val_2635_);
lean_dec(v___x_2633_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2658_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v_scheme_2639_; lean_object* v_userInfo_2640_; lean_object* v_port_2641_; lean_object* v_pathSegments_2642_; lean_object* v_query_2643_; lean_object* v_fragment_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2656_; 
v_scheme_2639_ = lean_ctor_get(v_b_2631_, 0);
v_userInfo_2640_ = lean_ctor_get(v_b_2631_, 1);
v_port_2641_ = lean_ctor_get(v_b_2631_, 3);
v_pathSegments_2642_ = lean_ctor_get(v_b_2631_, 4);
v_query_2643_ = lean_ctor_get(v_b_2631_, 5);
v_fragment_2644_ = lean_ctor_get(v_b_2631_, 6);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_b_2631_);
if (v_isSharedCheck_2656_ == 0)
{
lean_object* v_unused_2657_; 
v_unused_2657_ = lean_ctor_get(v_b_2631_, 2);
lean_dec(v_unused_2657_);
v___x_2646_ = v_b_2631_;
v_isShared_2647_ = v_isSharedCheck_2656_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_fragment_2644_);
lean_inc(v_query_2643_);
lean_inc(v_pathSegments_2642_);
lean_inc(v_port_2641_);
lean_inc(v_userInfo_2640_);
lean_inc(v_scheme_2639_);
lean_dec(v_b_2631_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2656_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2648_, 0, v_val_2635_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v___x_2648_);
v___x_2650_ = v___x_2637_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2652_; 
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 2, v___x_2650_);
v___x_2652_ = v___x_2646_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_scheme_2639_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_userInfo_2640_);
lean_ctor_set(v_reuseFailAlloc_2654_, 2, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2654_, 3, v_port_2641_);
lean_ctor_set(v_reuseFailAlloc_2654_, 4, v_pathSegments_2642_);
lean_ctor_set(v_reuseFailAlloc_2654_, 5, v_query_2643_);
lean_ctor_set(v_reuseFailAlloc_2654_, 6, v_fragment_2644_);
v___x_2652_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2653_; 
v___x_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
return v___x_2653_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x21(lean_object* v_b_2661_, lean_object* v_name_2662_){
_start:
{
lean_object* v___x_2663_; 
lean_inc_ref(v_name_2662_);
v___x_2663_ = l_Std_Http_URI_Builder_setHost_x3f(v_b_2661_, v_name_2662_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2664_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2665_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__0));
v___x_2666_ = lean_unsigned_to_nat(716u);
v___x_2667_ = lean_unsigned_to_nat(14u);
v___x_2668_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__1));
v___x_2669_ = l_String_quote(v_name_2662_);
v___x_2670_ = lean_string_append(v___x_2668_, v___x_2669_);
lean_dec_ref(v___x_2669_);
v___x_2671_ = l_mkPanicMessageWithDecl(v___x_2664_, v___x_2665_, v___x_2666_, v___x_2667_, v___x_2670_);
lean_dec_ref(v___x_2670_);
v___x_2672_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2671_);
return v___x_2672_;
}
else
{
lean_object* v_val_2673_; 
lean_dec_ref(v_name_2662_);
v_val_2673_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_val_2673_);
lean_dec_ref_known(v___x_2663_, 1);
return v_val_2673_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv4(lean_object* v_b_2674_, lean_object* v_addr_2675_){
_start:
{
lean_object* v_scheme_2676_; lean_object* v_userInfo_2677_; lean_object* v_port_2678_; lean_object* v_pathSegments_2679_; lean_object* v_query_2680_; lean_object* v_fragment_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2690_; 
v_scheme_2676_ = lean_ctor_get(v_b_2674_, 0);
v_userInfo_2677_ = lean_ctor_get(v_b_2674_, 1);
v_port_2678_ = lean_ctor_get(v_b_2674_, 3);
v_pathSegments_2679_ = lean_ctor_get(v_b_2674_, 4);
v_query_2680_ = lean_ctor_get(v_b_2674_, 5);
v_fragment_2681_ = lean_ctor_get(v_b_2674_, 6);
v_isSharedCheck_2690_ = !lean_is_exclusive(v_b_2674_);
if (v_isSharedCheck_2690_ == 0)
{
lean_object* v_unused_2691_; 
v_unused_2691_ = lean_ctor_get(v_b_2674_, 2);
lean_dec(v_unused_2691_);
v___x_2683_ = v_b_2674_;
v_isShared_2684_ = v_isSharedCheck_2690_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_fragment_2681_);
lean_inc(v_query_2680_);
lean_inc(v_pathSegments_2679_);
lean_inc(v_port_2678_);
lean_inc(v_userInfo_2677_);
lean_inc(v_scheme_2676_);
lean_dec(v_b_2674_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2690_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2685_, 0, v_addr_2675_);
v___x_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 2, v___x_2686_);
v___x_2688_ = v___x_2683_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_scheme_2676_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v_userInfo_2677_);
lean_ctor_set(v_reuseFailAlloc_2689_, 2, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2689_, 3, v_port_2678_);
lean_ctor_set(v_reuseFailAlloc_2689_, 4, v_pathSegments_2679_);
lean_ctor_set(v_reuseFailAlloc_2689_, 5, v_query_2680_);
lean_ctor_set(v_reuseFailAlloc_2689_, 6, v_fragment_2681_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv6(lean_object* v_b_2692_, lean_object* v_addr_2693_){
_start:
{
lean_object* v_scheme_2694_; lean_object* v_userInfo_2695_; lean_object* v_port_2696_; lean_object* v_pathSegments_2697_; lean_object* v_query_2698_; lean_object* v_fragment_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2708_; 
v_scheme_2694_ = lean_ctor_get(v_b_2692_, 0);
v_userInfo_2695_ = lean_ctor_get(v_b_2692_, 1);
v_port_2696_ = lean_ctor_get(v_b_2692_, 3);
v_pathSegments_2697_ = lean_ctor_get(v_b_2692_, 4);
v_query_2698_ = lean_ctor_get(v_b_2692_, 5);
v_fragment_2699_ = lean_ctor_get(v_b_2692_, 6);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_b_2692_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; 
v_unused_2709_ = lean_ctor_get(v_b_2692_, 2);
lean_dec(v_unused_2709_);
v___x_2701_ = v_b_2692_;
v_isShared_2702_ = v_isSharedCheck_2708_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_fragment_2699_);
lean_inc(v_query_2698_);
lean_inc(v_pathSegments_2697_);
lean_inc(v_port_2696_);
lean_inc(v_userInfo_2695_);
lean_inc(v_scheme_2694_);
lean_dec(v_b_2692_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2708_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2703_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2703_, 0, v_addr_2693_);
v___x_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 2, v___x_2704_);
v___x_2706_ = v___x_2701_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_scheme_2694_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_userInfo_2695_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2707_, 3, v_port_2696_);
lean_ctor_set(v_reuseFailAlloc_2707_, 4, v_pathSegments_2697_);
lean_ctor_set(v_reuseFailAlloc_2707_, 5, v_query_2698_);
lean_ctor_set(v_reuseFailAlloc_2707_, 6, v_fragment_2699_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort(lean_object* v_b_2710_, uint16_t v_port_2711_){
_start:
{
lean_object* v_scheme_2712_; lean_object* v_userInfo_2713_; lean_object* v_host_2714_; lean_object* v_pathSegments_2715_; lean_object* v_query_2716_; lean_object* v_fragment_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2725_; 
v_scheme_2712_ = lean_ctor_get(v_b_2710_, 0);
v_userInfo_2713_ = lean_ctor_get(v_b_2710_, 1);
v_host_2714_ = lean_ctor_get(v_b_2710_, 2);
v_pathSegments_2715_ = lean_ctor_get(v_b_2710_, 4);
v_query_2716_ = lean_ctor_get(v_b_2710_, 5);
v_fragment_2717_ = lean_ctor_get(v_b_2710_, 6);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_b_2710_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; 
v_unused_2726_ = lean_ctor_get(v_b_2710_, 3);
lean_dec(v_unused_2726_);
v___x_2719_ = v_b_2710_;
v_isShared_2720_ = v_isSharedCheck_2725_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_fragment_2717_);
lean_inc(v_query_2716_);
lean_inc(v_pathSegments_2715_);
lean_inc(v_host_2714_);
lean_inc(v_userInfo_2713_);
lean_inc(v_scheme_2712_);
lean_dec(v_b_2710_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2725_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2721_; lean_object* v___x_2723_; 
v___x_2721_ = lean_alloc_ctor(2, 0, 2);
lean_ctor_set_uint16(v___x_2721_, 0, v_port_2711_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 3, v___x_2721_);
v___x_2723_ = v___x_2719_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_scheme_2712_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_userInfo_2713_);
lean_ctor_set(v_reuseFailAlloc_2724_, 2, v_host_2714_);
lean_ctor_set(v_reuseFailAlloc_2724_, 3, v___x_2721_);
lean_ctor_set(v_reuseFailAlloc_2724_, 4, v_pathSegments_2715_);
lean_ctor_set(v_reuseFailAlloc_2724_, 5, v_query_2716_);
lean_ctor_set(v_reuseFailAlloc_2724_, 6, v_fragment_2717_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort___boxed(lean_object* v_b_2727_, lean_object* v_port_2728_){
_start:
{
uint16_t v_port_boxed_2729_; lean_object* v_res_2730_; 
v_port_boxed_2729_ = lean_unbox(v_port_2728_);
v_res_2730_ = l_Std_Http_URI_Builder_setPort(v_b_2727_, v_port_boxed_2729_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPath(lean_object* v_b_2731_, lean_object* v_segments_2732_){
_start:
{
lean_object* v_scheme_2733_; lean_object* v_userInfo_2734_; lean_object* v_host_2735_; lean_object* v_port_2736_; lean_object* v_query_2737_; lean_object* v_fragment_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
v_scheme_2733_ = lean_ctor_get(v_b_2731_, 0);
v_userInfo_2734_ = lean_ctor_get(v_b_2731_, 1);
v_host_2735_ = lean_ctor_get(v_b_2731_, 2);
v_port_2736_ = lean_ctor_get(v_b_2731_, 3);
v_query_2737_ = lean_ctor_get(v_b_2731_, 5);
v_fragment_2738_ = lean_ctor_get(v_b_2731_, 6);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_b_2731_);
if (v_isSharedCheck_2745_ == 0)
{
lean_object* v_unused_2746_; 
v_unused_2746_ = lean_ctor_get(v_b_2731_, 4);
lean_dec(v_unused_2746_);
v___x_2740_ = v_b_2731_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_fragment_2738_);
lean_inc(v_query_2737_);
lean_inc(v_port_2736_);
lean_inc(v_host_2735_);
lean_inc(v_userInfo_2734_);
lean_inc(v_scheme_2733_);
lean_dec(v_b_2731_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 4, v_segments_2732_);
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_scheme_2733_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_userInfo_2734_);
lean_ctor_set(v_reuseFailAlloc_2744_, 2, v_host_2735_);
lean_ctor_set(v_reuseFailAlloc_2744_, 3, v_port_2736_);
lean_ctor_set(v_reuseFailAlloc_2744_, 4, v_segments_2732_);
lean_ctor_set(v_reuseFailAlloc_2744_, 5, v_query_2737_);
lean_ctor_set(v_reuseFailAlloc_2744_, 6, v_fragment_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_appendPathSegment(lean_object* v_b_2747_, lean_object* v_segment_2748_){
_start:
{
lean_object* v_scheme_2749_; lean_object* v_userInfo_2750_; lean_object* v_host_2751_; lean_object* v_port_2752_; lean_object* v_pathSegments_2753_; lean_object* v_query_2754_; lean_object* v_fragment_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2763_; 
v_scheme_2749_ = lean_ctor_get(v_b_2747_, 0);
v_userInfo_2750_ = lean_ctor_get(v_b_2747_, 1);
v_host_2751_ = lean_ctor_get(v_b_2747_, 2);
v_port_2752_ = lean_ctor_get(v_b_2747_, 3);
v_pathSegments_2753_ = lean_ctor_get(v_b_2747_, 4);
v_query_2754_ = lean_ctor_get(v_b_2747_, 5);
v_fragment_2755_ = lean_ctor_get(v_b_2747_, 6);
v_isSharedCheck_2763_ = !lean_is_exclusive(v_b_2747_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2757_ = v_b_2747_;
v_isShared_2758_ = v_isSharedCheck_2763_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_fragment_2755_);
lean_inc(v_query_2754_);
lean_inc(v_pathSegments_2753_);
lean_inc(v_port_2752_);
lean_inc(v_host_2751_);
lean_inc(v_userInfo_2750_);
lean_inc(v_scheme_2749_);
lean_dec(v_b_2747_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2763_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; lean_object* v___x_2761_; 
v___x_2759_ = lean_array_push(v_pathSegments_2753_, v_segment_2748_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 4, v___x_2759_);
v___x_2761_ = v___x_2757_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_scheme_2749_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v_userInfo_2750_);
lean_ctor_set(v_reuseFailAlloc_2762_, 2, v_host_2751_);
lean_ctor_set(v_reuseFailAlloc_2762_, 3, v_port_2752_);
lean_ctor_set(v_reuseFailAlloc_2762_, 4, v___x_2759_);
lean_ctor_set(v_reuseFailAlloc_2762_, 5, v_query_2754_);
lean_ctor_set(v_reuseFailAlloc_2762_, 6, v_fragment_2755_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryParam(lean_object* v_b_2764_, lean_object* v_key_2765_, lean_object* v_value_2766_){
_start:
{
lean_object* v_scheme_2767_; lean_object* v_userInfo_2768_; lean_object* v_host_2769_; lean_object* v_port_2770_; lean_object* v_pathSegments_2771_; lean_object* v_query_2772_; lean_object* v_fragment_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2783_; 
v_scheme_2767_ = lean_ctor_get(v_b_2764_, 0);
v_userInfo_2768_ = lean_ctor_get(v_b_2764_, 1);
v_host_2769_ = lean_ctor_get(v_b_2764_, 2);
v_port_2770_ = lean_ctor_get(v_b_2764_, 3);
v_pathSegments_2771_ = lean_ctor_get(v_b_2764_, 4);
v_query_2772_ = lean_ctor_get(v_b_2764_, 5);
v_fragment_2773_ = lean_ctor_get(v_b_2764_, 6);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_b_2764_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2775_ = v_b_2764_;
v_isShared_2776_ = v_isSharedCheck_2783_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_fragment_2773_);
lean_inc(v_query_2772_);
lean_inc(v_pathSegments_2771_);
lean_inc(v_port_2770_);
lean_inc(v_host_2769_);
lean_inc(v_userInfo_2768_);
lean_inc(v_scheme_2767_);
lean_dec(v_b_2764_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2783_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2777_, 0, v_value_2766_);
v___x_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2778_, 0, v_key_2765_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = lean_array_push(v_query_2772_, v___x_2778_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 5, v___x_2779_);
v___x_2781_ = v___x_2775_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_scheme_2767_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_userInfo_2768_);
lean_ctor_set(v_reuseFailAlloc_2782_, 2, v_host_2769_);
lean_ctor_set(v_reuseFailAlloc_2782_, 3, v_port_2770_);
lean_ctor_set(v_reuseFailAlloc_2782_, 4, v_pathSegments_2771_);
lean_ctor_set(v_reuseFailAlloc_2782_, 5, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2782_, 6, v_fragment_2773_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryFlag(lean_object* v_b_2784_, lean_object* v_key_2785_){
_start:
{
lean_object* v_scheme_2786_; lean_object* v_userInfo_2787_; lean_object* v_host_2788_; lean_object* v_port_2789_; lean_object* v_pathSegments_2790_; lean_object* v_query_2791_; lean_object* v_fragment_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2802_; 
v_scheme_2786_ = lean_ctor_get(v_b_2784_, 0);
v_userInfo_2787_ = lean_ctor_get(v_b_2784_, 1);
v_host_2788_ = lean_ctor_get(v_b_2784_, 2);
v_port_2789_ = lean_ctor_get(v_b_2784_, 3);
v_pathSegments_2790_ = lean_ctor_get(v_b_2784_, 4);
v_query_2791_ = lean_ctor_get(v_b_2784_, 5);
v_fragment_2792_ = lean_ctor_get(v_b_2784_, 6);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_b_2784_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2794_ = v_b_2784_;
v_isShared_2795_ = v_isSharedCheck_2802_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_fragment_2792_);
lean_inc(v_query_2791_);
lean_inc(v_pathSegments_2790_);
lean_inc(v_port_2789_);
lean_inc(v_host_2788_);
lean_inc(v_userInfo_2787_);
lean_inc(v_scheme_2786_);
lean_dec(v_b_2784_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2802_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2796_ = lean_box(0);
v___x_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2797_, 0, v_key_2785_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = lean_array_push(v_query_2791_, v___x_2797_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 5, v___x_2798_);
v___x_2800_ = v___x_2794_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_scheme_2786_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_userInfo_2787_);
lean_ctor_set(v_reuseFailAlloc_2801_, 2, v_host_2788_);
lean_ctor_set(v_reuseFailAlloc_2801_, 3, v_port_2789_);
lean_ctor_set(v_reuseFailAlloc_2801_, 4, v_pathSegments_2790_);
lean_ctor_set(v_reuseFailAlloc_2801_, 5, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2801_, 6, v_fragment_2792_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setQuery(lean_object* v_b_2803_, lean_object* v_query_2804_){
_start:
{
lean_object* v_scheme_2805_; lean_object* v_userInfo_2806_; lean_object* v_host_2807_; lean_object* v_port_2808_; lean_object* v_pathSegments_2809_; lean_object* v_fragment_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
v_scheme_2805_ = lean_ctor_get(v_b_2803_, 0);
v_userInfo_2806_ = lean_ctor_get(v_b_2803_, 1);
v_host_2807_ = lean_ctor_get(v_b_2803_, 2);
v_port_2808_ = lean_ctor_get(v_b_2803_, 3);
v_pathSegments_2809_ = lean_ctor_get(v_b_2803_, 4);
v_fragment_2810_ = lean_ctor_get(v_b_2803_, 6);
v_isSharedCheck_2817_ = !lean_is_exclusive(v_b_2803_);
if (v_isSharedCheck_2817_ == 0)
{
lean_object* v_unused_2818_; 
v_unused_2818_ = lean_ctor_get(v_b_2803_, 5);
lean_dec(v_unused_2818_);
v___x_2812_ = v_b_2803_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_fragment_2810_);
lean_inc(v_pathSegments_2809_);
lean_inc(v_port_2808_);
lean_inc(v_host_2807_);
lean_inc(v_userInfo_2806_);
lean_inc(v_scheme_2805_);
lean_dec(v_b_2803_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 5, v_query_2804_);
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_scheme_2805_);
lean_ctor_set(v_reuseFailAlloc_2816_, 1, v_userInfo_2806_);
lean_ctor_set(v_reuseFailAlloc_2816_, 2, v_host_2807_);
lean_ctor_set(v_reuseFailAlloc_2816_, 3, v_port_2808_);
lean_ctor_set(v_reuseFailAlloc_2816_, 4, v_pathSegments_2809_);
lean_ctor_set(v_reuseFailAlloc_2816_, 5, v_query_2804_);
lean_ctor_set(v_reuseFailAlloc_2816_, 6, v_fragment_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setFragment(lean_object* v_b_2819_, lean_object* v_fragment_2820_){
_start:
{
lean_object* v_scheme_2821_; lean_object* v_userInfo_2822_; lean_object* v_host_2823_; lean_object* v_port_2824_; lean_object* v_pathSegments_2825_; lean_object* v_query_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2834_; 
v_scheme_2821_ = lean_ctor_get(v_b_2819_, 0);
v_userInfo_2822_ = lean_ctor_get(v_b_2819_, 1);
v_host_2823_ = lean_ctor_get(v_b_2819_, 2);
v_port_2824_ = lean_ctor_get(v_b_2819_, 3);
v_pathSegments_2825_ = lean_ctor_get(v_b_2819_, 4);
v_query_2826_ = lean_ctor_get(v_b_2819_, 5);
v_isSharedCheck_2834_ = !lean_is_exclusive(v_b_2819_);
if (v_isSharedCheck_2834_ == 0)
{
lean_object* v_unused_2835_; 
v_unused_2835_ = lean_ctor_get(v_b_2819_, 6);
lean_dec(v_unused_2835_);
v___x_2828_ = v_b_2819_;
v_isShared_2829_ = v_isSharedCheck_2834_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_query_2826_);
lean_inc(v_pathSegments_2825_);
lean_inc(v_port_2824_);
lean_inc(v_host_2823_);
lean_inc(v_userInfo_2822_);
lean_inc(v_scheme_2821_);
lean_dec(v_b_2819_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2834_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2830_; lean_object* v___x_2832_; 
v___x_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2830_, 0, v_fragment_2820_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 6, v___x_2830_);
v___x_2832_ = v___x_2828_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_scheme_2821_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_userInfo_2822_);
lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_host_2823_);
lean_ctor_set(v_reuseFailAlloc_2833_, 3, v_port_2824_);
lean_ctor_set(v_reuseFailAlloc_2833_, 4, v_pathSegments_2825_);
lean_ctor_set(v_reuseFailAlloc_2833_, 5, v_query_2826_);
lean_ctor_set(v_reuseFailAlloc_2833_, 6, v___x_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(size_t v_sz_2836_, size_t v_i_2837_, lean_object* v_bs_2838_){
_start:
{
uint8_t v___x_2839_; 
v___x_2839_ = lean_usize_dec_lt(v_i_2837_, v_sz_2836_);
if (v___x_2839_ == 0)
{
return v_bs_2838_;
}
else
{
lean_object* v_v_2840_; lean_object* v___x_2841_; lean_object* v_bs_x27_2842_; lean_object* v___x_2843_; size_t v___x_2844_; size_t v___x_2845_; lean_object* v___x_2846_; 
v_v_2840_ = lean_array_uget(v_bs_2838_, v_i_2837_);
v___x_2841_ = lean_unsigned_to_nat(0u);
v_bs_x27_2842_ = lean_array_uset(v_bs_2838_, v_i_2837_, v___x_2841_);
v___x_2843_ = l_Std_Http_URI_EncodedSegment_encode(v_v_2840_);
lean_dec(v_v_2840_);
v___x_2844_ = ((size_t)1ULL);
v___x_2845_ = lean_usize_add(v_i_2837_, v___x_2844_);
v___x_2846_ = lean_array_uset(v_bs_x27_2842_, v_i_2837_, v___x_2843_);
v_i_2837_ = v___x_2845_;
v_bs_2838_ = v___x_2846_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0___boxed(lean_object* v_sz_2848_, lean_object* v_i_2849_, lean_object* v_bs_2850_){
_start:
{
size_t v_sz_boxed_2851_; size_t v_i_boxed_2852_; lean_object* v_res_2853_; 
v_sz_boxed_2851_ = lean_unbox_usize(v_sz_2848_);
lean_dec(v_sz_2848_);
v_i_boxed_2852_ = lean_unbox_usize(v_i_2849_);
lean_dec(v_i_2849_);
v_res_2853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_boxed_2851_, v_i_boxed_2852_, v_bs_2850_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(size_t v_sz_2854_, size_t v_i_2855_, lean_object* v_bs_2856_){
_start:
{
uint8_t v___x_2857_; 
v___x_2857_ = lean_usize_dec_lt(v_i_2855_, v_sz_2854_);
if (v___x_2857_ == 0)
{
return v_bs_2856_;
}
else
{
lean_object* v_v_2858_; lean_object* v_fst_2859_; lean_object* v_snd_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2889_; 
v_v_2858_ = lean_array_uget(v_bs_2856_, v_i_2855_);
v_fst_2859_ = lean_ctor_get(v_v_2858_, 0);
v_snd_2860_ = lean_ctor_get(v_v_2858_, 1);
v_isSharedCheck_2889_ = !lean_is_exclusive(v_v_2858_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2862_ = v_v_2858_;
v_isShared_2863_ = v_isSharedCheck_2889_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_snd_2860_);
lean_inc(v_fst_2859_);
lean_dec(v_v_2858_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2889_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; lean_object* v_bs_x27_2865_; lean_object* v___y_2867_; lean_object* v___x_2872_; 
v___x_2864_ = lean_unsigned_to_nat(0u);
v_bs_x27_2865_ = lean_array_uset(v_bs_2856_, v_i_2855_, v___x_2864_);
v___x_2872_ = l_Std_Http_URI_EncodedQueryParam_encode(v_fst_2859_);
lean_dec(v_fst_2859_);
if (lean_obj_tag(v_snd_2860_) == 0)
{
lean_object* v___x_2873_; lean_object* v___x_2875_; 
v___x_2873_ = lean_box(0);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 1, v___x_2873_);
lean_ctor_set(v___x_2862_, 0, v___x_2872_);
v___x_2875_ = v___x_2862_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2872_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v___x_2873_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
v___y_2867_ = v___x_2875_;
goto v___jp_2866_;
}
}
else
{
lean_object* v_val_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2888_; 
v_val_2877_ = lean_ctor_get(v_snd_2860_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_snd_2860_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2879_ = v_snd_2860_;
v_isShared_2880_ = v_isSharedCheck_2888_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_val_2877_);
lean_dec(v_snd_2860_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2888_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2881_ = l_Std_Http_URI_EncodedQueryParam_encode(v_val_2877_);
lean_dec(v_val_2877_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 0, v___x_2881_);
v___x_2883_ = v___x_2879_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2885_; 
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 1, v___x_2883_);
lean_ctor_set(v___x_2862_, 0, v___x_2872_);
v___x_2885_ = v___x_2862_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2872_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
v___y_2867_ = v___x_2885_;
goto v___jp_2866_;
}
}
}
}
v___jp_2866_:
{
size_t v___x_2868_; size_t v___x_2869_; lean_object* v___x_2870_; 
v___x_2868_ = ((size_t)1ULL);
v___x_2869_ = lean_usize_add(v_i_2855_, v___x_2868_);
v___x_2870_ = lean_array_uset(v_bs_x27_2865_, v_i_2855_, v___y_2867_);
v_i_2855_ = v___x_2869_;
v_bs_2856_ = v___x_2870_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1___boxed(lean_object* v_sz_2890_, lean_object* v_i_2891_, lean_object* v_bs_2892_){
_start:
{
size_t v_sz_boxed_2893_; size_t v_i_boxed_2894_; lean_object* v_res_2895_; 
v_sz_boxed_2893_ = lean_unbox_usize(v_sz_2890_);
lean_dec(v_sz_2890_);
v_i_boxed_2894_ = lean_unbox_usize(v_i_2891_);
lean_dec(v_i_2891_);
v_res_2895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_boxed_2893_, v_i_boxed_2894_, v_bs_2892_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_build(lean_object* v_b_2896_){
_start:
{
lean_object* v___y_2898_; lean_object* v___y_2899_; uint8_t v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v_scheme_2919_; lean_object* v_userInfo_2920_; lean_object* v_host_2921_; lean_object* v_port_2922_; lean_object* v_pathSegments_2923_; lean_object* v_query_2924_; lean_object* v_fragment_2925_; lean_object* v___y_2927_; 
v_scheme_2919_ = lean_ctor_get(v_b_2896_, 0);
lean_inc(v_scheme_2919_);
v_userInfo_2920_ = lean_ctor_get(v_b_2896_, 1);
lean_inc(v_userInfo_2920_);
v_host_2921_ = lean_ctor_get(v_b_2896_, 2);
lean_inc(v_host_2921_);
v_port_2922_ = lean_ctor_get(v_b_2896_, 3);
lean_inc(v_port_2922_);
v_pathSegments_2923_ = lean_ctor_get(v_b_2896_, 4);
lean_inc_ref(v_pathSegments_2923_);
v_query_2924_ = lean_ctor_get(v_b_2896_, 5);
lean_inc_ref(v_query_2924_);
v_fragment_2925_ = lean_ctor_get(v_b_2896_, 6);
lean_inc(v_fragment_2925_);
lean_dec_ref(v_b_2896_);
if (lean_obj_tag(v_scheme_2919_) == 0)
{
lean_object* v___x_2940_; 
v___x_2940_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___y_2927_ = v___x_2940_;
goto v___jp_2926_;
}
else
{
lean_object* v_val_2941_; 
v_val_2941_ = lean_ctor_get(v_scheme_2919_, 0);
lean_inc(v_val_2941_);
lean_dec_ref_known(v_scheme_2919_, 1);
v___y_2927_ = v_val_2941_;
goto v___jp_2926_;
}
v___jp_2897_:
{
size_t v_sz_2904_; size_t v___x_2905_; lean_object* v___x_2906_; lean_object* v_path_2907_; size_t v_sz_2908_; lean_object* v_query_2909_; lean_object* v___x_2910_; lean_object* v_query_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; uint8_t v___x_2914_; 
v_sz_2904_ = lean_array_size(v___y_2902_);
v___x_2905_ = ((size_t)0ULL);
v___x_2906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_2904_, v___x_2905_, v___y_2902_);
v_path_2907_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_path_2907_, 0, v___x_2906_);
lean_ctor_set_uint8(v_path_2907_, sizeof(void*)*1, v___y_2900_);
v_sz_2908_ = lean_array_size(v___y_2901_);
v_query_2909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_2908_, v___x_2905_, v___y_2901_);
v___x_2910_ = lean_array_to_list(v_query_2909_);
v_query_2911_ = lean_array_mk(v___x_2910_);
v___x_2912_ = lean_array_get_size(v_query_2911_);
v___x_2913_ = lean_unsigned_to_nat(0u);
v___x_2914_ = lean_nat_dec_eq(v___x_2912_, v___x_2913_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2915_, 0, v_query_2911_);
v___x_2916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2916_, 0, v___y_2898_);
lean_ctor_set(v___x_2916_, 1, v___y_2903_);
lean_ctor_set(v___x_2916_, 2, v_path_2907_);
lean_ctor_set(v___x_2916_, 3, v___x_2915_);
lean_ctor_set(v___x_2916_, 4, v___y_2899_);
return v___x_2916_;
}
else
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
lean_dec_ref(v_query_2911_);
v___x_2917_ = lean_box(0);
v___x_2918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2918_, 0, v___y_2898_);
lean_ctor_set(v___x_2918_, 1, v___y_2903_);
lean_ctor_set(v___x_2918_, 2, v_path_2907_);
lean_ctor_set(v___x_2918_, 3, v___x_2917_);
lean_ctor_set(v___x_2918_, 4, v___y_2899_);
return v___x_2918_;
}
}
v___jp_2926_:
{
if (lean_obj_tag(v_host_2921_) == 0)
{
uint8_t v___x_2928_; lean_object* v___x_2929_; 
lean_dec(v_port_2922_);
lean_dec(v_userInfo_2920_);
v___x_2928_ = 1;
v___x_2929_ = lean_box(0);
v___y_2898_ = v___y_2927_;
v___y_2899_ = v_fragment_2925_;
v___y_2900_ = v___x_2928_;
v___y_2901_ = v_query_2924_;
v___y_2902_ = v_pathSegments_2923_;
v___y_2903_ = v___x_2929_;
goto v___jp_2897_;
}
else
{
lean_object* v_val_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2939_; 
v_val_2930_ = lean_ctor_get(v_host_2921_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v_host_2921_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2932_ = v_host_2921_;
v_isShared_2933_ = v_isSharedCheck_2939_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_val_2930_);
lean_dec(v_host_2921_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2939_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
uint8_t v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2934_ = 1;
v___x_2935_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2935_, 0, v_userInfo_2920_);
lean_ctor_set(v___x_2935_, 1, v_val_2930_);
lean_ctor_set(v___x_2935_, 2, v_port_2922_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v___x_2935_);
v___x_2937_ = v___x_2932_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2935_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
v___y_2898_ = v___y_2927_;
v___y_2899_ = v_fragment_2925_;
v___y_2900_ = v___x_2934_;
v___y_2901_ = v_query_2924_;
v___y_2902_ = v_pathSegments_2923_;
v___y_2903_ = v___x_2937_;
goto v___jp_2897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withScheme_x21(lean_object* v_uri_2942_, lean_object* v_scheme_2943_){
_start:
{
lean_object* v_authority_2944_; lean_object* v_path_2945_; lean_object* v_query_2946_; lean_object* v_fragment_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2955_; 
v_authority_2944_ = lean_ctor_get(v_uri_2942_, 1);
v_path_2945_ = lean_ctor_get(v_uri_2942_, 2);
v_query_2946_ = lean_ctor_get(v_uri_2942_, 3);
v_fragment_2947_ = lean_ctor_get(v_uri_2942_, 4);
v_isSharedCheck_2955_ = !lean_is_exclusive(v_uri_2942_);
if (v_isSharedCheck_2955_ == 0)
{
lean_object* v_unused_2956_; 
v_unused_2956_ = lean_ctor_get(v_uri_2942_, 0);
lean_dec(v_unused_2956_);
v___x_2949_ = v_uri_2942_;
v_isShared_2950_ = v_isSharedCheck_2955_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_fragment_2947_);
lean_inc(v_query_2946_);
lean_inc(v_path_2945_);
lean_inc(v_authority_2944_);
lean_dec(v_uri_2942_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2955_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2951_; lean_object* v___x_2953_; 
v___x_2951_ = l_Std_Http_URI_Scheme_ofString_x21(v_scheme_2943_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 0, v___x_2951_);
v___x_2953_ = v___x_2949_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2951_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_authority_2944_);
lean_ctor_set(v_reuseFailAlloc_2954_, 2, v_path_2945_);
lean_ctor_set(v_reuseFailAlloc_2954_, 3, v_query_2946_);
lean_ctor_set(v_reuseFailAlloc_2954_, 4, v_fragment_2947_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withAuthority(lean_object* v_uri_2957_, lean_object* v_authority_2958_){
_start:
{
lean_object* v_scheme_2959_; lean_object* v_path_2960_; lean_object* v_query_2961_; lean_object* v_fragment_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
v_scheme_2959_ = lean_ctor_get(v_uri_2957_, 0);
v_path_2960_ = lean_ctor_get(v_uri_2957_, 2);
v_query_2961_ = lean_ctor_get(v_uri_2957_, 3);
v_fragment_2962_ = lean_ctor_get(v_uri_2957_, 4);
v_isSharedCheck_2969_ = !lean_is_exclusive(v_uri_2957_);
if (v_isSharedCheck_2969_ == 0)
{
lean_object* v_unused_2970_; 
v_unused_2970_ = lean_ctor_get(v_uri_2957_, 1);
lean_dec(v_unused_2970_);
v___x_2964_ = v_uri_2957_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_fragment_2962_);
lean_inc(v_query_2961_);
lean_inc(v_path_2960_);
lean_inc(v_scheme_2959_);
lean_dec(v_uri_2957_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 1, v_authority_2958_);
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_scheme_2959_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_authority_2958_);
lean_ctor_set(v_reuseFailAlloc_2968_, 2, v_path_2960_);
lean_ctor_set(v_reuseFailAlloc_2968_, 3, v_query_2961_);
lean_ctor_set(v_reuseFailAlloc_2968_, 4, v_fragment_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withPath(lean_object* v_uri_2971_, lean_object* v_path_2972_){
_start:
{
lean_object* v_scheme_2973_; lean_object* v_authority_2974_; lean_object* v_query_2975_; lean_object* v_fragment_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
v_scheme_2973_ = lean_ctor_get(v_uri_2971_, 0);
v_authority_2974_ = lean_ctor_get(v_uri_2971_, 1);
v_query_2975_ = lean_ctor_get(v_uri_2971_, 3);
v_fragment_2976_ = lean_ctor_get(v_uri_2971_, 4);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_uri_2971_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; 
v_unused_2984_ = lean_ctor_get(v_uri_2971_, 2);
lean_dec(v_unused_2984_);
v___x_2978_ = v_uri_2971_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_fragment_2976_);
lean_inc(v_query_2975_);
lean_inc(v_authority_2974_);
lean_inc(v_scheme_2973_);
lean_dec(v_uri_2971_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 2, v_path_2972_);
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_scheme_2973_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_authority_2974_);
lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_path_2972_);
lean_ctor_set(v_reuseFailAlloc_2982_, 3, v_query_2975_);
lean_ctor_set(v_reuseFailAlloc_2982_, 4, v_fragment_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withQuery(lean_object* v_uri_2985_, lean_object* v_query_2986_){
_start:
{
lean_object* v_scheme_2987_; lean_object* v_authority_2988_; lean_object* v_path_2989_; lean_object* v_fragment_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2998_; 
v_scheme_2987_ = lean_ctor_get(v_uri_2985_, 0);
v_authority_2988_ = lean_ctor_get(v_uri_2985_, 1);
v_path_2989_ = lean_ctor_get(v_uri_2985_, 2);
v_fragment_2990_ = lean_ctor_get(v_uri_2985_, 4);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_uri_2985_);
if (v_isSharedCheck_2998_ == 0)
{
lean_object* v_unused_2999_; 
v_unused_2999_ = lean_ctor_get(v_uri_2985_, 3);
lean_dec(v_unused_2999_);
v___x_2992_ = v_uri_2985_;
v_isShared_2993_ = v_isSharedCheck_2998_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_fragment_2990_);
lean_inc(v_path_2989_);
lean_inc(v_authority_2988_);
lean_inc(v_scheme_2987_);
lean_dec(v_uri_2985_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2998_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2994_; lean_object* v___x_2996_; 
v___x_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2994_, 0, v_query_2986_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 3, v___x_2994_);
v___x_2996_ = v___x_2992_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_scheme_2987_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v_authority_2988_);
lean_ctor_set(v_reuseFailAlloc_2997_, 2, v_path_2989_);
lean_ctor_set(v_reuseFailAlloc_2997_, 3, v___x_2994_);
lean_ctor_set(v_reuseFailAlloc_2997_, 4, v_fragment_2990_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withFragment(lean_object* v_uri_3000_, lean_object* v_fragment_3001_){
_start:
{
lean_object* v_scheme_3002_; lean_object* v_authority_3003_; lean_object* v_path_3004_; lean_object* v_query_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
v_scheme_3002_ = lean_ctor_get(v_uri_3000_, 0);
v_authority_3003_ = lean_ctor_get(v_uri_3000_, 1);
v_path_3004_ = lean_ctor_get(v_uri_3000_, 2);
v_query_3005_ = lean_ctor_get(v_uri_3000_, 3);
v_isSharedCheck_3012_ = !lean_is_exclusive(v_uri_3000_);
if (v_isSharedCheck_3012_ == 0)
{
lean_object* v_unused_3013_; 
v_unused_3013_ = lean_ctor_get(v_uri_3000_, 4);
lean_dec(v_unused_3013_);
v___x_3007_ = v_uri_3000_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_query_3005_);
lean_inc(v_path_3004_);
lean_inc(v_authority_3003_);
lean_inc(v_scheme_3002_);
lean_dec(v_uri_3000_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 4, v_fragment_3001_);
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_scheme_3002_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_authority_3003_);
lean_ctor_set(v_reuseFailAlloc_3011_, 2, v_path_3004_);
lean_ctor_set(v_reuseFailAlloc_3011_, 3, v_query_3005_);
lean_ctor_set(v_reuseFailAlloc_3011_, 4, v_fragment_3001_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_normalize(lean_object* v_uri_3014_){
_start:
{
lean_object* v_scheme_3015_; lean_object* v_authority_3016_; lean_object* v_path_3017_; lean_object* v_query_3018_; lean_object* v_fragment_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3027_; 
v_scheme_3015_ = lean_ctor_get(v_uri_3014_, 0);
v_authority_3016_ = lean_ctor_get(v_uri_3014_, 1);
v_path_3017_ = lean_ctor_get(v_uri_3014_, 2);
v_query_3018_ = lean_ctor_get(v_uri_3014_, 3);
v_fragment_3019_ = lean_ctor_get(v_uri_3014_, 4);
v_isSharedCheck_3027_ = !lean_is_exclusive(v_uri_3014_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3021_ = v_uri_3014_;
v_isShared_3022_ = v_isSharedCheck_3027_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_fragment_3019_);
lean_inc(v_query_3018_);
lean_inc(v_path_3017_);
lean_inc(v_authority_3016_);
lean_inc(v_scheme_3015_);
lean_dec(v_uri_3014_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3027_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3023_ = l_Std_Http_URI_Path_normalize(v_path_3017_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 2, v___x_3023_);
v___x_3025_ = v___x_3021_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_scheme_3015_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v_authority_3016_);
lean_ctor_set(v_reuseFailAlloc_3026_, 2, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3026_, 3, v_query_3018_);
lean_ctor_set(v_reuseFailAlloc_3026_, 4, v_fragment_3019_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___redArg(lean_object* v_x_3028_){
_start:
{
lean_object* v_scheme_3029_; lean_object* v_host_3030_; uint16_t v_port_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; uint8_t v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v_ctr_3052_; lean_object* v_a_3053_; 
v_scheme_3029_ = lean_ctor_get(v_x_3028_, 0);
lean_inc_ref(v_scheme_3029_);
v_host_3030_ = lean_ctor_get(v_x_3028_, 1);
lean_inc_ref(v_host_3030_);
v_port_3031_ = lean_ctor_get_uint16(v_x_3028_, sizeof(void*)*2);
lean_dec_ref(v_x_3028_);
v___x_3032_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_3033_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_3034_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_3035_ = l_String_quote(v_scheme_3029_);
v___x_3036_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
v___x_3037_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3034_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = 0;
v___x_3039_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3039_, 0, v___x_3037_);
lean_ctor_set_uint8(v___x_3039_, sizeof(void*)*1, v___x_3038_);
v___x_3040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3033_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_3042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3040_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = lean_box(1);
v___x_3044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3042_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_3046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3044_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
lean_ctor_set(v___x_3047_, 1, v___x_3032_);
v___x_3048_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_3049_ = lean_unsigned_to_nat(0u);
v___x_3050_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_3030_))
{
case 0:
{
lean_object* v_name_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3092_; 
v_name_3083_ = lean_ctor_get(v_host_3030_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v_host_3030_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3085_ = v_host_3030_;
v_isShared_3086_ = v_isSharedCheck_3092_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_name_3083_);
lean_dec(v_host_3030_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3092_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3090_; 
v___x_3087_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_3088_ = l_String_quote(v_name_3083_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set_tag(v___x_3085_, 3);
lean_ctor_set(v___x_3085_, 0, v___x_3088_);
v___x_3090_ = v___x_3085_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3088_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
v_ctr_3052_ = v___x_3087_;
v_a_3053_ = v___x_3090_;
goto v___jp_3051_;
}
}
}
case 1:
{
lean_object* v_ipv4_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3102_; 
v_ipv4_3093_ = lean_ctor_get(v_host_3030_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_host_3030_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3095_ = v_host_3030_;
v_isShared_3096_ = v_isSharedCheck_3102_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_ipv4_3093_);
lean_dec(v_host_3030_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3102_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3100_; 
v___x_3097_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_3098_ = lean_uv_ntop_v4(v_ipv4_3093_);
lean_dec_ref(v_ipv4_3093_);
if (v_isShared_3096_ == 0)
{
lean_ctor_set_tag(v___x_3095_, 3);
lean_ctor_set(v___x_3095_, 0, v___x_3098_);
v___x_3100_ = v___x_3095_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
v_ctr_3052_ = v___x_3097_;
v_a_3053_ = v___x_3100_;
goto v___jp_3051_;
}
}
}
default: 
{
lean_object* v_ipv6_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3112_; 
v_ipv6_3103_ = lean_ctor_get(v_host_3030_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_host_3030_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3105_ = v_host_3030_;
v_isShared_3106_ = v_isSharedCheck_3112_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_ipv6_3103_);
lean_dec(v_host_3030_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3112_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3110_; 
v___x_3107_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_3108_ = lean_uv_ntop_v6(v_ipv6_3103_);
lean_dec_ref(v_ipv6_3103_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set_tag(v___x_3105_, 3);
lean_ctor_set(v___x_3105_, 0, v___x_3108_);
v___x_3110_ = v___x_3105_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
v_ctr_3052_ = v___x_3107_;
v_a_3053_ = v___x_3110_;
goto v___jp_3051_;
}
}
}
}
v___jp_3051_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3054_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_3055_ = lean_string_append(v___x_3054_, v_ctr_3052_);
v___x_3056_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
v___x_3057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
lean_ctor_set(v___x_3057_, 1, v___x_3043_);
v___x_3058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
lean_ctor_set(v___x_3058_, 1, v_a_3053_);
v___x_3059_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3050_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
v___x_3060_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
lean_ctor_set_uint8(v___x_3060_, sizeof(void*)*1, v___x_3038_);
v___x_3061_ = l_Repr_addAppParen(v___x_3060_, v___x_3049_);
v___x_3062_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3048_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
lean_ctor_set_uint8(v___x_3063_, sizeof(void*)*1, v___x_3038_);
v___x_3064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3047_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
v___x_3065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
lean_ctor_set(v___x_3065_, 1, v___x_3041_);
v___x_3066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
lean_ctor_set(v___x_3066_, 1, v___x_3043_);
v___x_3067_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_3068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3066_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
lean_ctor_set(v___x_3069_, 1, v___x_3032_);
v___x_3070_ = lean_uint16_to_nat(v_port_3031_);
v___x_3071_ = l_Nat_reprFast(v___x_3070_);
v___x_3072_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
v___x_3073_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3048_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
v___x_3074_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
lean_ctor_set_uint8(v___x_3074_, sizeof(void*)*1, v___x_3038_);
v___x_3075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3069_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_3077_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_3078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
lean_ctor_set(v___x_3078_, 1, v___x_3075_);
v___x_3079_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_3080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3078_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3076_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set_uint8(v___x_3082_, sizeof(void*)*1, v___x_3038_);
return v___x_3082_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr(lean_object* v_x_3113_, lean_object* v_prec_3114_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l_Std_Http_URI_instReprOrigin_repr___redArg(v_x_3113_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___boxed(lean_object* v_x_3116_, lean_object* v_prec_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l_Std_Http_URI_instReprOrigin_repr(v_x_3116_, v_prec_3117_);
lean_dec(v_prec_3117_);
return v_res_3118_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqOrigin_beq(lean_object* v_x_3121_, lean_object* v_x_3122_){
_start:
{
lean_object* v_scheme_3123_; lean_object* v_host_3124_; uint16_t v_port_3125_; lean_object* v_scheme_3126_; lean_object* v_host_3127_; uint16_t v_port_3128_; uint8_t v___x_3129_; 
v_scheme_3123_ = lean_ctor_get(v_x_3121_, 0);
v_host_3124_ = lean_ctor_get(v_x_3121_, 1);
v_port_3125_ = lean_ctor_get_uint16(v_x_3121_, sizeof(void*)*2);
v_scheme_3126_ = lean_ctor_get(v_x_3122_, 0);
v_host_3127_ = lean_ctor_get(v_x_3122_, 1);
v_port_3128_ = lean_ctor_get_uint16(v_x_3122_, sizeof(void*)*2);
v___x_3129_ = lean_string_dec_eq(v_scheme_3123_, v_scheme_3126_);
if (v___x_3129_ == 0)
{
return v___x_3129_;
}
else
{
uint8_t v___x_3130_; 
v___x_3130_ = l_Std_Http_URI_instBEqHost_beq(v_host_3124_, v_host_3127_);
if (v___x_3130_ == 0)
{
return v___x_3130_;
}
else
{
uint8_t v___x_3131_; 
v___x_3131_ = lean_uint16_dec_eq(v_port_3125_, v_port_3128_);
return v___x_3131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqOrigin_beq___boxed(lean_object* v_x_3132_, lean_object* v_x_3133_){
_start:
{
uint8_t v_res_3134_; lean_object* v_r_3135_; 
v_res_3134_ = l_Std_Http_URI_instBEqOrigin_beq(v_x_3132_, v_x_3133_);
lean_dec_ref(v_x_3133_);
lean_dec_ref(v_x_3132_);
v_r_3135_ = lean_box(v_res_3134_);
return v_r_3135_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Origin_hostHeader(lean_object* v_o_3138_){
_start:
{
lean_object* v_scheme_3139_; lean_object* v_host_3140_; uint16_t v_port_3141_; lean_object* v___y_3143_; uint16_t v_defaultPort_3149_; uint8_t v___x_3150_; 
v_scheme_3139_ = lean_ctor_get(v_o_3138_, 0);
lean_inc_ref(v_scheme_3139_);
v_host_3140_ = lean_ctor_get(v_o_3138_, 1);
lean_inc_ref(v_host_3140_);
v_port_3141_ = lean_ctor_get_uint16(v_o_3138_, sizeof(void*)*2);
lean_dec_ref(v_o_3138_);
v_defaultPort_3149_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_3139_);
lean_dec_ref(v_scheme_3139_);
v___x_3150_ = lean_uint16_dec_eq(v_port_3141_, v_defaultPort_3149_);
if (v___x_3150_ == 0)
{
switch(lean_obj_tag(v_host_3140_))
{
case 0:
{
lean_object* v_name_3151_; 
v_name_3151_ = lean_ctor_get(v_host_3140_, 0);
lean_inc_ref(v_name_3151_);
lean_dec_ref_known(v_host_3140_, 1);
v___y_3143_ = v_name_3151_;
goto v___jp_3142_;
}
case 1:
{
lean_object* v_ipv4_3152_; lean_object* v___x_3153_; 
v_ipv4_3152_ = lean_ctor_get(v_host_3140_, 0);
lean_inc_ref(v_ipv4_3152_);
lean_dec_ref_known(v_host_3140_, 1);
v___x_3153_ = lean_uv_ntop_v4(v_ipv4_3152_);
lean_dec_ref(v_ipv4_3152_);
v___y_3143_ = v___x_3153_;
goto v___jp_3142_;
}
default: 
{
lean_object* v_ipv6_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v_ipv6_3154_ = lean_ctor_get(v_host_3140_, 0);
lean_inc_ref(v_ipv6_3154_);
lean_dec_ref_known(v_host_3140_, 1);
v___x_3155_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3156_ = lean_uv_ntop_v6(v_ipv6_3154_);
lean_dec_ref(v_ipv6_3154_);
v___x_3157_ = lean_string_append(v___x_3155_, v___x_3156_);
lean_dec_ref(v___x_3156_);
v___x_3158_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3159_ = lean_string_append(v___x_3157_, v___x_3158_);
v___y_3143_ = v___x_3159_;
goto v___jp_3142_;
}
}
}
else
{
switch(lean_obj_tag(v_host_3140_))
{
case 0:
{
lean_object* v_name_3160_; 
v_name_3160_ = lean_ctor_get(v_host_3140_, 0);
lean_inc_ref(v_name_3160_);
lean_dec_ref_known(v_host_3140_, 1);
return v_name_3160_;
}
case 1:
{
lean_object* v_ipv4_3161_; lean_object* v___x_3162_; 
v_ipv4_3161_ = lean_ctor_get(v_host_3140_, 0);
lean_inc_ref(v_ipv4_3161_);
lean_dec_ref_known(v_host_3140_, 1);
v___x_3162_ = lean_uv_ntop_v4(v_ipv4_3161_);
lean_dec_ref(v_ipv4_3161_);
return v___x_3162_;
}
default: 
{
lean_object* v_ipv6_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v_ipv6_3163_ = lean_ctor_get(v_host_3140_, 0);
lean_inc_ref(v_ipv6_3163_);
lean_dec_ref_known(v_host_3140_, 1);
v___x_3164_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3165_ = lean_uv_ntop_v6(v_ipv6_3163_);
lean_dec_ref(v_ipv6_3163_);
v___x_3166_ = lean_string_append(v___x_3164_, v___x_3165_);
lean_dec_ref(v___x_3165_);
v___x_3167_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3168_ = lean_string_append(v___x_3166_, v___x_3167_);
return v___x_3168_;
}
}
}
v___jp_3142_:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3144_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3145_ = lean_string_append(v___y_3143_, v___x_3144_);
v___x_3146_ = lean_uint16_to_nat(v_port_3141_);
v___x_3147_ = l_Nat_reprFast(v___x_3146_);
v___x_3148_ = lean_string_append(v___x_3145_, v___x_3147_);
lean_dec_ref(v___x_3147_);
return v___x_3148_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___redArg(lean_object* v_x_3175_){
_start:
{
lean_object* v_authority_3176_; lean_object* v_path_3177_; lean_object* v_query_3178_; lean_object* v_fragment_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; uint8_t v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v_authority_3176_ = lean_ctor_get(v_x_3175_, 0);
lean_inc(v_authority_3176_);
v_path_3177_ = lean_ctor_get(v_x_3175_, 1);
lean_inc_ref(v_path_3177_);
v_query_3178_ = lean_ctor_get(v_x_3175_, 2);
lean_inc(v_query_3178_);
v_fragment_3179_ = lean_ctor_get(v_x_3175_, 3);
lean_inc(v_fragment_3179_);
lean_dec_ref(v_x_3175_);
v___x_3180_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_3181_ = ((lean_object*)(l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__1));
v___x_3182_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_3183_ = lean_unsigned_to_nat(0u);
v___x_3184_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_3176_, v___x_3183_);
v___x_3185_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3182_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = 0;
v___x_3187_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3187_, 0, v___x_3185_);
lean_ctor_set_uint8(v___x_3187_, sizeof(void*)*1, v___x_3186_);
v___x_3188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3181_);
lean_ctor_set(v___x_3188_, 1, v___x_3187_);
v___x_3189_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_3190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3188_);
lean_ctor_set(v___x_3190_, 1, v___x_3189_);
v___x_3191_ = lean_box(1);
v___x_3192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3190_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
v___x_3193_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_3194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3192_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
lean_ctor_set(v___x_3195_, 1, v___x_3180_);
v___x_3196_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_3197_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3177_);
v___x_3198_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3196_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3199_, 0, v___x_3198_);
lean_ctor_set_uint8(v___x_3199_, sizeof(void*)*1, v___x_3186_);
v___x_3200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3195_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
v___x_3201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
lean_ctor_set(v___x_3201_, 1, v___x_3189_);
v___x_3202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
lean_ctor_set(v___x_3202_, 1, v___x_3191_);
v___x_3203_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_3204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3202_);
lean_ctor_set(v___x_3204_, 1, v___x_3203_);
v___x_3205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
lean_ctor_set(v___x_3205_, 1, v___x_3180_);
v___x_3206_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_3207_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3178_, v___x_3183_);
v___x_3208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3206_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
v___x_3209_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
lean_ctor_set_uint8(v___x_3209_, sizeof(void*)*1, v___x_3186_);
v___x_3210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3205_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
v___x_3211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
lean_ctor_set(v___x_3211_, 1, v___x_3189_);
v___x_3212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
lean_ctor_set(v___x_3212_, 1, v___x_3191_);
v___x_3213_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_3214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3212_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
v___x_3215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
lean_ctor_set(v___x_3215_, 1, v___x_3180_);
v___x_3216_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_3217_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_3179_, v___x_3183_);
v___x_3218_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3216_);
lean_ctor_set(v___x_3218_, 1, v___x_3217_);
v___x_3219_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
lean_ctor_set_uint8(v___x_3219_, sizeof(void*)*1, v___x_3186_);
v___x_3220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3215_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_3222_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_3223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
lean_ctor_set(v___x_3223_, 1, v___x_3220_);
v___x_3224_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_3225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3223_);
lean_ctor_set(v___x_3225_, 1, v___x_3224_);
v___x_3226_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3221_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
v___x_3227_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*1, v___x_3186_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr(lean_object* v_x_3228_, lean_object* v_prec_3229_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_x_3228_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___boxed(lean_object* v_x_3231_, lean_object* v_prec_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Std_Http_URI_instReprRelativeRef_repr(v_x_3231_, v_prec_3232_);
lean_dec(v_prec_3232_);
return v_res_3233_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqRelativeRef_beq(lean_object* v_x_3241_, lean_object* v_x_3242_){
_start:
{
lean_object* v_authority_3243_; lean_object* v_path_3244_; lean_object* v_query_3245_; lean_object* v_fragment_3246_; lean_object* v_authority_3247_; lean_object* v_path_3248_; lean_object* v_query_3249_; lean_object* v_fragment_3250_; uint8_t v___x_3251_; 
v_authority_3243_ = lean_ctor_get(v_x_3241_, 0);
v_path_3244_ = lean_ctor_get(v_x_3241_, 1);
v_query_3245_ = lean_ctor_get(v_x_3241_, 2);
v_fragment_3246_ = lean_ctor_get(v_x_3241_, 3);
v_authority_3247_ = lean_ctor_get(v_x_3242_, 0);
v_path_3248_ = lean_ctor_get(v_x_3242_, 1);
v_query_3249_ = lean_ctor_get(v_x_3242_, 2);
v_fragment_3250_ = lean_ctor_get(v_x_3242_, 3);
v___x_3251_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_3243_, v_authority_3247_);
if (v___x_3251_ == 0)
{
return v___x_3251_;
}
else
{
uint8_t v___x_3252_; 
v___x_3252_ = l_Std_Http_URI_instBEqPath_beq(v_path_3244_, v_path_3248_);
if (v___x_3252_ == 0)
{
return v___x_3252_;
}
else
{
uint8_t v___x_3253_; 
v___x_3253_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_3245_, v_query_3249_);
if (v___x_3253_ == 0)
{
return v___x_3253_;
}
else
{
uint8_t v___x_3254_; 
v___x_3254_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_3246_, v_fragment_3250_);
return v___x_3254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqRelativeRef_beq___boxed(lean_object* v_x_3255_, lean_object* v_x_3256_){
_start:
{
uint8_t v_res_3257_; lean_object* v_r_3258_; 
v_res_3257_ = l_Std_Http_URI_instBEqRelativeRef_beq(v_x_3255_, v_x_3256_);
lean_dec_ref(v_x_3256_);
lean_dec_ref(v_x_3255_);
v_r_3258_ = lean_box(v_res_3257_);
return v_r_3258_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringRelativeRef___lam__1(lean_object* v___f_3261_, lean_object* v_ref_3262_){
_start:
{
lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v_authority_3271_; lean_object* v_path_3272_; lean_object* v_query_3273_; lean_object* v_fragment_3274_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3286_; 
v_authority_3271_ = lean_ctor_get(v_ref_3262_, 0);
lean_inc(v_authority_3271_);
v_path_3272_ = lean_ctor_get(v_ref_3262_, 1);
lean_inc_ref(v_path_3272_);
v_query_3273_ = lean_ctor_get(v_ref_3262_, 2);
lean_inc(v_query_3273_);
v_fragment_3274_ = lean_ctor_get(v_ref_3262_, 3);
lean_inc(v_fragment_3274_);
lean_dec_ref(v_ref_3262_);
if (lean_obj_tag(v_authority_3271_) == 0)
{
lean_object* v___x_3297_; 
v___x_3297_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3286_ = v___x_3297_;
goto v___jp_3285_;
}
else
{
lean_object* v_val_3298_; lean_object* v_userInfo_3299_; lean_object* v_host_3300_; lean_object* v_port_3301_; lean_object* v___x_3302_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3321_; 
v_val_3298_ = lean_ctor_get(v_authority_3271_, 0);
lean_inc(v_val_3298_);
lean_dec_ref_known(v_authority_3271_, 1);
v_userInfo_3299_ = lean_ctor_get(v_val_3298_, 0);
lean_inc(v_userInfo_3299_);
v_host_3300_ = lean_ctor_get(v_val_3298_, 1);
lean_inc_ref(v_host_3300_);
v_port_3301_ = lean_ctor_get(v_val_3298_, 2);
lean_inc(v_port_3301_);
lean_dec(v_val_3298_);
v___x_3302_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3299_) == 0)
{
lean_object* v___x_3331_; 
v___x_3331_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3321_ = v___x_3331_;
goto v___jp_3320_;
}
else
{
lean_object* v_val_3332_; lean_object* v_password_3333_; 
v_val_3332_ = lean_ctor_get(v_userInfo_3299_, 0);
lean_inc(v_val_3332_);
lean_dec_ref_known(v_userInfo_3299_, 1);
v_password_3333_ = lean_ctor_get(v_val_3332_, 1);
if (lean_obj_tag(v_password_3333_) == 0)
{
lean_object* v_username_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v_username_3334_ = lean_ctor_get(v_val_3332_, 0);
lean_inc_ref(v_username_3334_);
lean_dec(v_val_3332_);
v___x_3335_ = lean_string_from_utf8_unchecked(v_username_3334_);
v___x_3336_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3337_ = lean_string_append(v___x_3335_, v___x_3336_);
v___y_3321_ = v___x_3337_;
goto v___jp_3320_;
}
else
{
lean_object* v_username_3338_; lean_object* v_val_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
lean_inc_ref(v_password_3333_);
v_username_3338_ = lean_ctor_get(v_val_3332_, 0);
lean_inc_ref(v_username_3338_);
lean_dec(v_val_3332_);
v_val_3339_ = lean_ctor_get(v_password_3333_, 0);
lean_inc(v_val_3339_);
lean_dec_ref_known(v_password_3333_, 1);
v___x_3340_ = lean_string_from_utf8_unchecked(v_username_3338_);
v___x_3341_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3342_ = lean_string_append(v___x_3340_, v___x_3341_);
v___x_3343_ = lean_string_from_utf8_unchecked(v_val_3339_);
v___x_3344_ = lean_string_append(v___x_3342_, v___x_3343_);
lean_dec_ref(v___x_3343_);
v___x_3345_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3346_ = lean_string_append(v___x_3344_, v___x_3345_);
v___y_3321_ = v___x_3346_;
goto v___jp_3320_;
}
}
v___jp_3303_:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3307_ = lean_string_append(v___y_3304_, v___y_3305_);
lean_dec_ref(v___y_3305_);
v___x_3308_ = lean_string_append(v___x_3307_, v___y_3306_);
lean_dec_ref(v___y_3306_);
v___x_3309_ = lean_string_append(v___x_3302_, v___x_3308_);
lean_dec_ref(v___x_3308_);
v___y_3286_ = v___x_3309_;
goto v___jp_3285_;
}
v___jp_3310_:
{
switch(lean_obj_tag(v_port_3301_))
{
case 0:
{
lean_object* v___x_3313_; 
v___x_3313_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3304_ = v___y_3311_;
v___y_3305_ = v___y_3312_;
v___y_3306_ = v___x_3313_;
goto v___jp_3303_;
}
case 1:
{
lean_object* v___x_3314_; 
v___x_3314_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3304_ = v___y_3311_;
v___y_3305_ = v___y_3312_;
v___y_3306_ = v___x_3314_;
goto v___jp_3303_;
}
default: 
{
uint16_t v_port_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_port_3315_ = lean_ctor_get_uint16(v_port_3301_, 0);
lean_dec_ref_known(v_port_3301_, 0);
v___x_3316_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3317_ = lean_uint16_to_nat(v_port_3315_);
v___x_3318_ = l_Nat_reprFast(v___x_3317_);
v___x_3319_ = lean_string_append(v___x_3316_, v___x_3318_);
lean_dec_ref(v___x_3318_);
v___y_3304_ = v___y_3311_;
v___y_3305_ = v___y_3312_;
v___y_3306_ = v___x_3319_;
goto v___jp_3303_;
}
}
}
v___jp_3320_:
{
switch(lean_obj_tag(v_host_3300_))
{
case 0:
{
lean_object* v_name_3322_; 
v_name_3322_ = lean_ctor_get(v_host_3300_, 0);
lean_inc_ref(v_name_3322_);
lean_dec_ref_known(v_host_3300_, 1);
v___y_3311_ = v___y_3321_;
v___y_3312_ = v_name_3322_;
goto v___jp_3310_;
}
case 1:
{
lean_object* v_ipv4_3323_; lean_object* v___x_3324_; 
v_ipv4_3323_ = lean_ctor_get(v_host_3300_, 0);
lean_inc_ref(v_ipv4_3323_);
lean_dec_ref_known(v_host_3300_, 1);
v___x_3324_ = lean_uv_ntop_v4(v_ipv4_3323_);
lean_dec_ref(v_ipv4_3323_);
v___y_3311_ = v___y_3321_;
v___y_3312_ = v___x_3324_;
goto v___jp_3310_;
}
default: 
{
lean_object* v_ipv6_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v_ipv6_3325_ = lean_ctor_get(v_host_3300_, 0);
lean_inc_ref(v_ipv6_3325_);
lean_dec_ref_known(v_host_3300_, 1);
v___x_3326_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3327_ = lean_uv_ntop_v6(v_ipv6_3325_);
lean_dec_ref(v_ipv6_3325_);
v___x_3328_ = lean_string_append(v___x_3326_, v___x_3327_);
lean_dec_ref(v___x_3327_);
v___x_3329_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3330_ = lean_string_append(v___x_3328_, v___x_3329_);
v___y_3311_ = v___y_3321_;
v___y_3312_ = v___x_3330_;
goto v___jp_3310_;
}
}
}
}
v___jp_3263_:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3268_ = lean_string_append(v___y_3265_, v___y_3266_);
lean_dec_ref(v___y_3266_);
v___x_3269_ = lean_string_append(v___x_3268_, v___y_3264_);
lean_dec_ref(v___y_3264_);
v___x_3270_ = lean_string_append(v___x_3269_, v___y_3267_);
lean_dec_ref(v___y_3267_);
return v___x_3270_;
}
v___jp_3275_:
{
lean_object* v_queryPart_3278_; 
v_queryPart_3278_ = l_Std_Http_URI_Query_formatOption(v_query_3273_);
if (lean_obj_tag(v_fragment_3274_) == 0)
{
lean_object* v___x_3279_; 
v___x_3279_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3264_ = v_queryPart_3278_;
v___y_3265_ = v___y_3276_;
v___y_3266_ = v___y_3277_;
v___y_3267_ = v___x_3279_;
goto v___jp_3263_;
}
else
{
lean_object* v_val_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v_val_3280_ = lean_ctor_get(v_fragment_3274_, 0);
lean_inc(v_val_3280_);
lean_dec_ref_known(v_fragment_3274_, 1);
v___x_3281_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3282_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3280_);
lean_dec(v_val_3280_);
v___x_3283_ = lean_string_from_utf8_unchecked(v___x_3282_);
v___x_3284_ = lean_string_append(v___x_3281_, v___x_3283_);
lean_dec_ref(v___x_3283_);
v___y_3264_ = v_queryPart_3278_;
v___y_3265_ = v___y_3276_;
v___y_3266_ = v___y_3277_;
v___y_3267_ = v___x_3284_;
goto v___jp_3263_;
}
}
v___jp_3285_:
{
lean_object* v_segments_3287_; uint8_t v_absolute_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; size_t v_sz_3291_; size_t v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v_result_3295_; 
v_segments_3287_ = lean_ctor_get(v_path_3272_, 0);
lean_inc_ref(v_segments_3287_);
v_absolute_3288_ = lean_ctor_get_uint8(v_path_3272_, sizeof(void*)*1);
lean_dec_ref(v_path_3272_);
v___x_3289_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3290_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3291_ = lean_array_size(v_segments_3287_);
v___x_3292_ = ((size_t)0ULL);
v___x_3293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3290_, v___f_3261_, v_sz_3291_, v___x_3292_, v_segments_3287_);
v___x_3294_ = lean_array_to_list(v___x_3293_);
v_result_3295_ = l_String_intercalate(v___x_3289_, v___x_3294_);
if (v_absolute_3288_ == 0)
{
v___y_3276_ = v___y_3286_;
v___y_3277_ = v_result_3295_;
goto v___jp_3275_;
}
else
{
lean_object* v___x_3296_; 
v___x_3296_ = lean_string_append(v___x_3289_, v_result_3295_);
lean_dec_ref(v_result_3295_);
v___y_3276_ = v___y_3286_;
v___y_3277_ = v___x_3296_;
goto v___jp_3275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx(lean_object* v_x_3350_){
_start:
{
if (lean_obj_tag(v_x_3350_) == 0)
{
lean_object* v___x_3351_; 
v___x_3351_ = lean_unsigned_to_nat(0u);
return v___x_3351_;
}
else
{
lean_object* v___x_3352_; 
v___x_3352_ = lean_unsigned_to_nat(1u);
return v___x_3352_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___boxed(lean_object* v_x_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_Std_Http_URIReference_ctorIdx(v_x_3353_);
lean_dec_ref(v_x_3353_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___redArg(lean_object* v_t_3355_, lean_object* v_k_3356_){
_start:
{
lean_object* v_uri_3357_; lean_object* v___x_3358_; 
v_uri_3357_ = lean_ctor_get(v_t_3355_, 0);
lean_inc_ref(v_uri_3357_);
lean_dec_ref(v_t_3355_);
v___x_3358_ = lean_apply_1(v_k_3356_, v_uri_3357_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim(lean_object* v_motive_3359_, lean_object* v_ctorIdx_3360_, lean_object* v_t_3361_, lean_object* v_h_3362_, lean_object* v_k_3363_){
_start:
{
lean_object* v___x_3364_; 
v___x_3364_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3361_, v_k_3363_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___boxed(lean_object* v_motive_3365_, lean_object* v_ctorIdx_3366_, lean_object* v_t_3367_, lean_object* v_h_3368_, lean_object* v_k_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Std_Http_URIReference_ctorElim(v_motive_3365_, v_ctorIdx_3366_, v_t_3367_, v_h_3368_, v_k_3369_);
lean_dec(v_ctorIdx_3366_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim___redArg(lean_object* v_t_3371_, lean_object* v_absolute_3372_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3371_, v_absolute_3372_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim(lean_object* v_motive_3374_, lean_object* v_t_3375_, lean_object* v_h_3376_, lean_object* v_absolute_3377_){
_start:
{
lean_object* v___x_3378_; 
v___x_3378_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3375_, v_absolute_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim___redArg(lean_object* v_t_3379_, lean_object* v_relative_3380_){
_start:
{
lean_object* v___x_3381_; 
v___x_3381_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3379_, v_relative_3380_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim(lean_object* v_motive_3382_, lean_object* v_t_3383_, lean_object* v_h_3384_, lean_object* v_relative_3385_){
_start:
{
lean_object* v___x_3386_; 
v___x_3386_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3383_, v_relative_3385_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr(lean_object* v_x_3399_, lean_object* v_prec_3400_){
_start:
{
if (lean_obj_tag(v_x_3399_) == 0)
{
lean_object* v_uri_3401_; lean_object* v___y_3403_; lean_object* v___x_3411_; uint8_t v___x_3412_; 
v_uri_3401_ = lean_ctor_get(v_x_3399_, 0);
lean_inc_ref(v_uri_3401_);
lean_dec_ref_known(v_x_3399_, 1);
v___x_3411_ = lean_unsigned_to_nat(1024u);
v___x_3412_ = lean_nat_dec_le(v___x_3411_, v_prec_3400_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; 
v___x_3413_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3403_ = v___x_3413_;
goto v___jp_3402_;
}
else
{
lean_object* v___x_3414_; 
v___x_3414_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3403_ = v___x_3414_;
goto v___jp_3402_;
}
v___jp_3402_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3404_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__2));
v___x_3405_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3401_);
v___x_3406_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3404_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
lean_inc(v___y_3403_);
v___x_3407_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___y_3403_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
v___x_3408_ = 0;
v___x_3409_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3409_, 0, v___x_3407_);
lean_ctor_set_uint8(v___x_3409_, sizeof(void*)*1, v___x_3408_);
v___x_3410_ = l_Repr_addAppParen(v___x_3409_, v_prec_3400_);
return v___x_3410_;
}
}
else
{
lean_object* v_ref_3415_; lean_object* v___y_3417_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v_ref_3415_ = lean_ctor_get(v_x_3399_, 0);
lean_inc_ref(v_ref_3415_);
lean_dec_ref_known(v_x_3399_, 1);
v___x_3425_ = lean_unsigned_to_nat(1024u);
v___x_3426_ = lean_nat_dec_le(v___x_3425_, v_prec_3400_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3417_ = v___x_3427_;
goto v___jp_3416_;
}
else
{
lean_object* v___x_3428_; 
v___x_3428_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3417_ = v___x_3428_;
goto v___jp_3416_;
}
v___jp_3416_:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; uint8_t v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3418_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__5));
v___x_3419_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_ref_3415_);
v___x_3420_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
lean_inc(v___y_3417_);
v___x_3421_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___y_3417_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = 0;
v___x_3423_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3423_, 0, v___x_3421_);
lean_ctor_set_uint8(v___x_3423_, sizeof(void*)*1, v___x_3422_);
v___x_3424_ = l_Repr_addAppParen(v___x_3423_, v_prec_3400_);
return v___x_3424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr___boxed(lean_object* v_x_3429_, lean_object* v_prec_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_Std_Http_instReprURIReference_repr(v_x_3429_, v_prec_3430_);
lean_dec(v_prec_3430_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURIReference___lam__2(lean_object* v___f_3438_, lean_object* v___f_3439_, lean_object* v_x_3440_){
_start:
{
lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; 
if (lean_obj_tag(v_x_3440_) == 0)
{
lean_object* v_uri_3449_; lean_object* v_scheme_3450_; lean_object* v_authority_3451_; lean_object* v_path_3452_; lean_object* v_query_3453_; lean_object* v_fragment_3454_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3477_; 
lean_dec_ref(v___f_3439_);
v_uri_3449_ = lean_ctor_get(v_x_3440_, 0);
lean_inc_ref(v_uri_3449_);
lean_dec_ref_known(v_x_3440_, 1);
v_scheme_3450_ = lean_ctor_get(v_uri_3449_, 0);
lean_inc_ref(v_scheme_3450_);
v_authority_3451_ = lean_ctor_get(v_uri_3449_, 1);
lean_inc(v_authority_3451_);
v_path_3452_ = lean_ctor_get(v_uri_3449_, 2);
lean_inc_ref(v_path_3452_);
v_query_3453_ = lean_ctor_get(v_uri_3449_, 3);
lean_inc(v_query_3453_);
v_fragment_3454_ = lean_ctor_get(v_uri_3449_, 4);
lean_inc(v_fragment_3454_);
lean_dec_ref(v_uri_3449_);
if (lean_obj_tag(v_authority_3451_) == 0)
{
lean_object* v___x_3488_; 
v___x_3488_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3477_ = v___x_3488_;
goto v___jp_3476_;
}
else
{
lean_object* v_val_3489_; lean_object* v_userInfo_3490_; lean_object* v_host_3491_; lean_object* v_port_3492_; lean_object* v___x_3493_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3512_; 
v_val_3489_ = lean_ctor_get(v_authority_3451_, 0);
lean_inc(v_val_3489_);
lean_dec_ref_known(v_authority_3451_, 1);
v_userInfo_3490_ = lean_ctor_get(v_val_3489_, 0);
lean_inc(v_userInfo_3490_);
v_host_3491_ = lean_ctor_get(v_val_3489_, 1);
lean_inc_ref(v_host_3491_);
v_port_3492_ = lean_ctor_get(v_val_3489_, 2);
lean_inc(v_port_3492_);
lean_dec(v_val_3489_);
v___x_3493_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3490_) == 0)
{
lean_object* v___x_3522_; 
v___x_3522_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3512_ = v___x_3522_;
goto v___jp_3511_;
}
else
{
lean_object* v_val_3523_; lean_object* v_password_3524_; 
v_val_3523_ = lean_ctor_get(v_userInfo_3490_, 0);
lean_inc(v_val_3523_);
lean_dec_ref_known(v_userInfo_3490_, 1);
v_password_3524_ = lean_ctor_get(v_val_3523_, 1);
if (lean_obj_tag(v_password_3524_) == 0)
{
lean_object* v_username_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v_username_3525_ = lean_ctor_get(v_val_3523_, 0);
lean_inc_ref(v_username_3525_);
lean_dec(v_val_3523_);
v___x_3526_ = lean_string_from_utf8_unchecked(v_username_3525_);
v___x_3527_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3528_ = lean_string_append(v___x_3526_, v___x_3527_);
v___y_3512_ = v___x_3528_;
goto v___jp_3511_;
}
else
{
lean_object* v_username_3529_; lean_object* v_val_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_inc_ref(v_password_3524_);
v_username_3529_ = lean_ctor_get(v_val_3523_, 0);
lean_inc_ref(v_username_3529_);
lean_dec(v_val_3523_);
v_val_3530_ = lean_ctor_get(v_password_3524_, 0);
lean_inc(v_val_3530_);
lean_dec_ref_known(v_password_3524_, 1);
v___x_3531_ = lean_string_from_utf8_unchecked(v_username_3529_);
v___x_3532_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3533_ = lean_string_append(v___x_3531_, v___x_3532_);
v___x_3534_ = lean_string_from_utf8_unchecked(v_val_3530_);
v___x_3535_ = lean_string_append(v___x_3533_, v___x_3534_);
lean_dec_ref(v___x_3534_);
v___x_3536_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3537_ = lean_string_append(v___x_3535_, v___x_3536_);
v___y_3512_ = v___x_3537_;
goto v___jp_3511_;
}
}
v___jp_3494_:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = lean_string_append(v___y_3495_, v___y_3496_);
lean_dec_ref(v___y_3496_);
v___x_3499_ = lean_string_append(v___x_3498_, v___y_3497_);
lean_dec_ref(v___y_3497_);
v___x_3500_ = lean_string_append(v___x_3493_, v___x_3499_);
lean_dec_ref(v___x_3499_);
v___y_3477_ = v___x_3500_;
goto v___jp_3476_;
}
v___jp_3501_:
{
switch(lean_obj_tag(v_port_3492_))
{
case 0:
{
lean_object* v___x_3504_; 
v___x_3504_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3495_ = v___y_3502_;
v___y_3496_ = v___y_3503_;
v___y_3497_ = v___x_3504_;
goto v___jp_3494_;
}
case 1:
{
lean_object* v___x_3505_; 
v___x_3505_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3495_ = v___y_3502_;
v___y_3496_ = v___y_3503_;
v___y_3497_ = v___x_3505_;
goto v___jp_3494_;
}
default: 
{
uint16_t v_port_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v_port_3506_ = lean_ctor_get_uint16(v_port_3492_, 0);
lean_dec_ref_known(v_port_3492_, 0);
v___x_3507_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3508_ = lean_uint16_to_nat(v_port_3506_);
v___x_3509_ = l_Nat_reprFast(v___x_3508_);
v___x_3510_ = lean_string_append(v___x_3507_, v___x_3509_);
lean_dec_ref(v___x_3509_);
v___y_3495_ = v___y_3502_;
v___y_3496_ = v___y_3503_;
v___y_3497_ = v___x_3510_;
goto v___jp_3494_;
}
}
}
v___jp_3511_:
{
switch(lean_obj_tag(v_host_3491_))
{
case 0:
{
lean_object* v_name_3513_; 
v_name_3513_ = lean_ctor_get(v_host_3491_, 0);
lean_inc_ref(v_name_3513_);
lean_dec_ref_known(v_host_3491_, 1);
v___y_3502_ = v___y_3512_;
v___y_3503_ = v_name_3513_;
goto v___jp_3501_;
}
case 1:
{
lean_object* v_ipv4_3514_; lean_object* v___x_3515_; 
v_ipv4_3514_ = lean_ctor_get(v_host_3491_, 0);
lean_inc_ref(v_ipv4_3514_);
lean_dec_ref_known(v_host_3491_, 1);
v___x_3515_ = lean_uv_ntop_v4(v_ipv4_3514_);
lean_dec_ref(v_ipv4_3514_);
v___y_3502_ = v___y_3512_;
v___y_3503_ = v___x_3515_;
goto v___jp_3501_;
}
default: 
{
lean_object* v_ipv6_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v_ipv6_3516_ = lean_ctor_get(v_host_3491_, 0);
lean_inc_ref(v_ipv6_3516_);
lean_dec_ref_known(v_host_3491_, 1);
v___x_3517_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3518_ = lean_uv_ntop_v6(v_ipv6_3516_);
lean_dec_ref(v_ipv6_3516_);
v___x_3519_ = lean_string_append(v___x_3517_, v___x_3518_);
lean_dec_ref(v___x_3518_);
v___x_3520_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3521_ = lean_string_append(v___x_3519_, v___x_3520_);
v___y_3502_ = v___y_3512_;
v___y_3503_ = v___x_3521_;
goto v___jp_3501_;
}
}
}
}
v___jp_3455_:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3460_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3461_ = lean_string_append(v_scheme_3450_, v___x_3460_);
v___x_3462_ = lean_string_append(v___x_3461_, v___y_3457_);
lean_dec_ref(v___y_3457_);
v___x_3463_ = lean_string_append(v___x_3462_, v___y_3456_);
lean_dec_ref(v___y_3456_);
v___x_3464_ = lean_string_append(v___x_3463_, v___y_3458_);
lean_dec_ref(v___y_3458_);
v___x_3465_ = lean_string_append(v___x_3464_, v___y_3459_);
lean_dec_ref(v___y_3459_);
return v___x_3465_;
}
v___jp_3466_:
{
lean_object* v_queryPart_3469_; 
v_queryPart_3469_ = l_Std_Http_URI_Query_formatOption(v_query_3453_);
if (lean_obj_tag(v_fragment_3454_) == 0)
{
lean_object* v___x_3470_; 
v___x_3470_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3456_ = v___y_3468_;
v___y_3457_ = v___y_3467_;
v___y_3458_ = v_queryPart_3469_;
v___y_3459_ = v___x_3470_;
goto v___jp_3455_;
}
else
{
lean_object* v_val_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v_val_3471_ = lean_ctor_get(v_fragment_3454_, 0);
lean_inc(v_val_3471_);
lean_dec_ref_known(v_fragment_3454_, 1);
v___x_3472_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3473_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3471_);
lean_dec(v_val_3471_);
v___x_3474_ = lean_string_from_utf8_unchecked(v___x_3473_);
v___x_3475_ = lean_string_append(v___x_3472_, v___x_3474_);
lean_dec_ref(v___x_3474_);
v___y_3456_ = v___y_3468_;
v___y_3457_ = v___y_3467_;
v___y_3458_ = v_queryPart_3469_;
v___y_3459_ = v___x_3475_;
goto v___jp_3455_;
}
}
v___jp_3476_:
{
lean_object* v_segments_3478_; uint8_t v_absolute_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; size_t v_sz_3482_; size_t v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v_result_3486_; 
v_segments_3478_ = lean_ctor_get(v_path_3452_, 0);
lean_inc_ref(v_segments_3478_);
v_absolute_3479_ = lean_ctor_get_uint8(v_path_3452_, sizeof(void*)*1);
lean_dec_ref(v_path_3452_);
v___x_3480_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3481_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3482_ = lean_array_size(v_segments_3478_);
v___x_3483_ = ((size_t)0ULL);
v___x_3484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3481_, v___f_3438_, v_sz_3482_, v___x_3483_, v_segments_3478_);
v___x_3485_ = lean_array_to_list(v___x_3484_);
v_result_3486_ = l_String_intercalate(v___x_3480_, v___x_3485_);
if (v_absolute_3479_ == 0)
{
v___y_3467_ = v___y_3477_;
v___y_3468_ = v_result_3486_;
goto v___jp_3466_;
}
else
{
lean_object* v___x_3487_; 
v___x_3487_ = lean_string_append(v___x_3480_, v_result_3486_);
lean_dec_ref(v_result_3486_);
v___y_3467_ = v___y_3477_;
v___y_3468_ = v___x_3487_;
goto v___jp_3466_;
}
}
}
else
{
lean_object* v_ref_3538_; lean_object* v_authority_3539_; lean_object* v_path_3540_; lean_object* v_query_3541_; lean_object* v_fragment_3542_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3554_; 
lean_dec_ref(v___f_3438_);
v_ref_3538_ = lean_ctor_get(v_x_3440_, 0);
lean_inc_ref(v_ref_3538_);
lean_dec_ref_known(v_x_3440_, 1);
v_authority_3539_ = lean_ctor_get(v_ref_3538_, 0);
lean_inc(v_authority_3539_);
v_path_3540_ = lean_ctor_get(v_ref_3538_, 1);
lean_inc_ref(v_path_3540_);
v_query_3541_ = lean_ctor_get(v_ref_3538_, 2);
lean_inc(v_query_3541_);
v_fragment_3542_ = lean_ctor_get(v_ref_3538_, 3);
lean_inc(v_fragment_3542_);
lean_dec_ref(v_ref_3538_);
if (lean_obj_tag(v_authority_3539_) == 0)
{
lean_object* v___x_3565_; 
v___x_3565_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3554_ = v___x_3565_;
goto v___jp_3553_;
}
else
{
lean_object* v_val_3566_; lean_object* v_userInfo_3567_; lean_object* v_host_3568_; lean_object* v_port_3569_; lean_object* v___x_3570_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3589_; 
v_val_3566_ = lean_ctor_get(v_authority_3539_, 0);
lean_inc(v_val_3566_);
lean_dec_ref_known(v_authority_3539_, 1);
v_userInfo_3567_ = lean_ctor_get(v_val_3566_, 0);
lean_inc(v_userInfo_3567_);
v_host_3568_ = lean_ctor_get(v_val_3566_, 1);
lean_inc_ref(v_host_3568_);
v_port_3569_ = lean_ctor_get(v_val_3566_, 2);
lean_inc(v_port_3569_);
lean_dec(v_val_3566_);
v___x_3570_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3567_) == 0)
{
lean_object* v___x_3599_; 
v___x_3599_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3589_ = v___x_3599_;
goto v___jp_3588_;
}
else
{
lean_object* v_val_3600_; lean_object* v_password_3601_; 
v_val_3600_ = lean_ctor_get(v_userInfo_3567_, 0);
lean_inc(v_val_3600_);
lean_dec_ref_known(v_userInfo_3567_, 1);
v_password_3601_ = lean_ctor_get(v_val_3600_, 1);
if (lean_obj_tag(v_password_3601_) == 0)
{
lean_object* v_username_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v_username_3602_ = lean_ctor_get(v_val_3600_, 0);
lean_inc_ref(v_username_3602_);
lean_dec(v_val_3600_);
v___x_3603_ = lean_string_from_utf8_unchecked(v_username_3602_);
v___x_3604_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3605_ = lean_string_append(v___x_3603_, v___x_3604_);
v___y_3589_ = v___x_3605_;
goto v___jp_3588_;
}
else
{
lean_object* v_username_3606_; lean_object* v_val_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
lean_inc_ref(v_password_3601_);
v_username_3606_ = lean_ctor_get(v_val_3600_, 0);
lean_inc_ref(v_username_3606_);
lean_dec(v_val_3600_);
v_val_3607_ = lean_ctor_get(v_password_3601_, 0);
lean_inc(v_val_3607_);
lean_dec_ref_known(v_password_3601_, 1);
v___x_3608_ = lean_string_from_utf8_unchecked(v_username_3606_);
v___x_3609_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3610_ = lean_string_append(v___x_3608_, v___x_3609_);
v___x_3611_ = lean_string_from_utf8_unchecked(v_val_3607_);
v___x_3612_ = lean_string_append(v___x_3610_, v___x_3611_);
lean_dec_ref(v___x_3611_);
v___x_3613_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3614_ = lean_string_append(v___x_3612_, v___x_3613_);
v___y_3589_ = v___x_3614_;
goto v___jp_3588_;
}
}
v___jp_3571_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3575_ = lean_string_append(v___y_3573_, v___y_3572_);
lean_dec_ref(v___y_3572_);
v___x_3576_ = lean_string_append(v___x_3575_, v___y_3574_);
lean_dec_ref(v___y_3574_);
v___x_3577_ = lean_string_append(v___x_3570_, v___x_3576_);
lean_dec_ref(v___x_3576_);
v___y_3554_ = v___x_3577_;
goto v___jp_3553_;
}
v___jp_3578_:
{
switch(lean_obj_tag(v_port_3569_))
{
case 0:
{
lean_object* v___x_3581_; 
v___x_3581_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3572_ = v___y_3580_;
v___y_3573_ = v___y_3579_;
v___y_3574_ = v___x_3581_;
goto v___jp_3571_;
}
case 1:
{
lean_object* v___x_3582_; 
v___x_3582_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3572_ = v___y_3580_;
v___y_3573_ = v___y_3579_;
v___y_3574_ = v___x_3582_;
goto v___jp_3571_;
}
default: 
{
uint16_t v_port_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v_port_3583_ = lean_ctor_get_uint16(v_port_3569_, 0);
lean_dec_ref_known(v_port_3569_, 0);
v___x_3584_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3585_ = lean_uint16_to_nat(v_port_3583_);
v___x_3586_ = l_Nat_reprFast(v___x_3585_);
v___x_3587_ = lean_string_append(v___x_3584_, v___x_3586_);
lean_dec_ref(v___x_3586_);
v___y_3572_ = v___y_3580_;
v___y_3573_ = v___y_3579_;
v___y_3574_ = v___x_3587_;
goto v___jp_3571_;
}
}
}
v___jp_3588_:
{
switch(lean_obj_tag(v_host_3568_))
{
case 0:
{
lean_object* v_name_3590_; 
v_name_3590_ = lean_ctor_get(v_host_3568_, 0);
lean_inc_ref(v_name_3590_);
lean_dec_ref_known(v_host_3568_, 1);
v___y_3579_ = v___y_3589_;
v___y_3580_ = v_name_3590_;
goto v___jp_3578_;
}
case 1:
{
lean_object* v_ipv4_3591_; lean_object* v___x_3592_; 
v_ipv4_3591_ = lean_ctor_get(v_host_3568_, 0);
lean_inc_ref(v_ipv4_3591_);
lean_dec_ref_known(v_host_3568_, 1);
v___x_3592_ = lean_uv_ntop_v4(v_ipv4_3591_);
lean_dec_ref(v_ipv4_3591_);
v___y_3579_ = v___y_3589_;
v___y_3580_ = v___x_3592_;
goto v___jp_3578_;
}
default: 
{
lean_object* v_ipv6_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v_ipv6_3593_ = lean_ctor_get(v_host_3568_, 0);
lean_inc_ref(v_ipv6_3593_);
lean_dec_ref_known(v_host_3568_, 1);
v___x_3594_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3595_ = lean_uv_ntop_v6(v_ipv6_3593_);
lean_dec_ref(v_ipv6_3593_);
v___x_3596_ = lean_string_append(v___x_3594_, v___x_3595_);
lean_dec_ref(v___x_3595_);
v___x_3597_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3598_ = lean_string_append(v___x_3596_, v___x_3597_);
v___y_3579_ = v___y_3589_;
v___y_3580_ = v___x_3598_;
goto v___jp_3578_;
}
}
}
}
v___jp_3543_:
{
lean_object* v_queryPart_3546_; 
v_queryPart_3546_ = l_Std_Http_URI_Query_formatOption(v_query_3541_);
if (lean_obj_tag(v_fragment_3542_) == 0)
{
lean_object* v___x_3547_; 
v___x_3547_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3442_ = v___y_3545_;
v___y_3443_ = v___y_3544_;
v___y_3444_ = v_queryPart_3546_;
v___y_3445_ = v___x_3547_;
goto v___jp_3441_;
}
else
{
lean_object* v_val_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v_val_3548_ = lean_ctor_get(v_fragment_3542_, 0);
lean_inc(v_val_3548_);
lean_dec_ref_known(v_fragment_3542_, 1);
v___x_3549_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3550_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3548_);
lean_dec(v_val_3548_);
v___x_3551_ = lean_string_from_utf8_unchecked(v___x_3550_);
v___x_3552_ = lean_string_append(v___x_3549_, v___x_3551_);
lean_dec_ref(v___x_3551_);
v___y_3442_ = v___y_3545_;
v___y_3443_ = v___y_3544_;
v___y_3444_ = v_queryPart_3546_;
v___y_3445_ = v___x_3552_;
goto v___jp_3441_;
}
}
v___jp_3553_:
{
lean_object* v_segments_3555_; uint8_t v_absolute_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; size_t v_sz_3559_; size_t v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v_result_3563_; 
v_segments_3555_ = lean_ctor_get(v_path_3540_, 0);
lean_inc_ref(v_segments_3555_);
v_absolute_3556_ = lean_ctor_get_uint8(v_path_3540_, sizeof(void*)*1);
lean_dec_ref(v_path_3540_);
v___x_3557_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3558_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3559_ = lean_array_size(v_segments_3555_);
v___x_3560_ = ((size_t)0ULL);
v___x_3561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3558_, v___f_3439_, v_sz_3559_, v___x_3560_, v_segments_3555_);
v___x_3562_ = lean_array_to_list(v___x_3561_);
v_result_3563_ = l_String_intercalate(v___x_3557_, v___x_3562_);
if (v_absolute_3556_ == 0)
{
v___y_3544_ = v___y_3554_;
v___y_3545_ = v_result_3563_;
goto v___jp_3543_;
}
else
{
lean_object* v___x_3564_; 
v___x_3564_ = lean_string_append(v___x_3557_, v_result_3563_);
lean_dec_ref(v_result_3563_);
v___y_3544_ = v___y_3554_;
v___y_3545_ = v___x_3564_;
goto v___jp_3543_;
}
}
}
v___jp_3441_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = lean_string_append(v___y_3443_, v___y_3442_);
lean_dec_ref(v___y_3442_);
v___x_3447_ = lean_string_append(v___x_3446_, v___y_3444_);
lean_dec_ref(v___y_3444_);
v___x_3448_ = lean_string_append(v___x_3447_, v___y_3445_);
lean_dec_ref(v___y_3445_);
return v___x_3448_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx(lean_object* v_x_3618_){
_start:
{
switch(lean_obj_tag(v_x_3618_))
{
case 0:
{
lean_object* v___x_3619_; 
v___x_3619_ = lean_unsigned_to_nat(0u);
return v___x_3619_;
}
case 1:
{
lean_object* v___x_3620_; 
v___x_3620_ = lean_unsigned_to_nat(1u);
return v___x_3620_;
}
case 2:
{
lean_object* v___x_3621_; 
v___x_3621_ = lean_unsigned_to_nat(2u);
return v___x_3621_;
}
default: 
{
lean_object* v___x_3622_; 
v___x_3622_ = lean_unsigned_to_nat(3u);
return v___x_3622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___boxed(lean_object* v_x_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Std_Http_RequestTarget_ctorIdx(v_x_3623_);
lean_dec(v_x_3623_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___redArg(lean_object* v_t_3625_, lean_object* v_k_3626_){
_start:
{
switch(lean_obj_tag(v_t_3625_))
{
case 0:
{
lean_object* v_path_3627_; lean_object* v_query_3628_; lean_object* v___x_3629_; 
v_path_3627_ = lean_ctor_get(v_t_3625_, 0);
lean_inc_ref(v_path_3627_);
v_query_3628_ = lean_ctor_get(v_t_3625_, 1);
lean_inc(v_query_3628_);
lean_dec_ref_known(v_t_3625_, 2);
v___x_3629_ = lean_apply_2(v_k_3626_, v_path_3627_, v_query_3628_);
return v___x_3629_;
}
case 3:
{
return v_k_3626_;
}
default: 
{
lean_object* v_uri_3630_; lean_object* v___x_3631_; 
v_uri_3630_ = lean_ctor_get(v_t_3625_, 0);
lean_inc_ref(v_uri_3630_);
lean_dec(v_t_3625_);
v___x_3631_ = lean_apply_1(v_k_3626_, v_uri_3630_);
return v___x_3631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim(lean_object* v_motive_3632_, lean_object* v_ctorIdx_3633_, lean_object* v_t_3634_, lean_object* v_h_3635_, lean_object* v_k_3636_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3634_, v_k_3636_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___boxed(lean_object* v_motive_3638_, lean_object* v_ctorIdx_3639_, lean_object* v_t_3640_, lean_object* v_h_3641_, lean_object* v_k_3642_){
_start:
{
lean_object* v_res_3643_; 
v_res_3643_ = l_Std_Http_RequestTarget_ctorElim(v_motive_3638_, v_ctorIdx_3639_, v_t_3640_, v_h_3641_, v_k_3642_);
lean_dec(v_ctorIdx_3639_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim___redArg(lean_object* v_t_3644_, lean_object* v_originForm_3645_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3644_, v_originForm_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim(lean_object* v_motive_3647_, lean_object* v_t_3648_, lean_object* v_h_3649_, lean_object* v_originForm_3650_){
_start:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3648_, v_originForm_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim___redArg(lean_object* v_t_3652_, lean_object* v_absoluteForm_3653_){
_start:
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3652_, v_absoluteForm_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim(lean_object* v_motive_3655_, lean_object* v_t_3656_, lean_object* v_h_3657_, lean_object* v_absoluteForm_3658_){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3656_, v_absoluteForm_3658_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim___redArg(lean_object* v_t_3660_, lean_object* v_authorityForm_3661_){
_start:
{
lean_object* v___x_3662_; 
v___x_3662_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3660_, v_authorityForm_3661_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim(lean_object* v_motive_3663_, lean_object* v_t_3664_, lean_object* v_h_3665_, lean_object* v_authorityForm_3666_){
_start:
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3664_, v_authorityForm_3666_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim___redArg(lean_object* v_t_3668_, lean_object* v_asteriskForm_3669_){
_start:
{
lean_object* v___x_3670_; 
v___x_3670_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3668_, v_asteriskForm_3669_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim(lean_object* v_motive_3671_, lean_object* v_t_3672_, lean_object* v_h_3673_, lean_object* v_asteriskForm_3674_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3672_, v_asteriskForm_3674_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object* v_x_3702_, lean_object* v_prec_3703_){
_start:
{
lean_object* v___y_3705_; 
switch(lean_obj_tag(v_x_3702_))
{
case 0:
{
lean_object* v_path_3711_; lean_object* v_query_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3736_; 
v_path_3711_ = lean_ctor_get(v_x_3702_, 0);
v_query_3712_ = lean_ctor_get(v_x_3702_, 1);
v_isSharedCheck_3736_ = !lean_is_exclusive(v_x_3702_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3714_ = v_x_3702_;
v_isShared_3715_ = v_isSharedCheck_3736_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_query_3712_);
lean_inc(v_path_3711_);
lean_dec(v_x_3702_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3736_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___y_3717_; lean_object* v___x_3732_; uint8_t v___x_3733_; 
v___x_3732_ = lean_unsigned_to_nat(1024u);
v___x_3733_ = lean_nat_dec_le(v___x_3732_, v_prec_3703_);
if (v___x_3733_ == 0)
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3717_ = v___x_3734_;
goto v___jp_3716_;
}
else
{
lean_object* v___x_3735_; 
v___x_3735_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3717_ = v___x_3735_;
goto v___jp_3716_;
}
v___jp_3716_:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3723_; 
v___x_3718_ = lean_box(1);
v___x_3719_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__4));
v___x_3720_ = lean_unsigned_to_nat(1024u);
v___x_3721_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3711_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set_tag(v___x_3714_, 5);
lean_ctor_set(v___x_3714_, 1, v___x_3721_);
lean_ctor_set(v___x_3714_, 0, v___x_3719_);
v___x_3723_ = v___x_3714_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3731_, 1, v___x_3721_);
v___x_3723_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
lean_ctor_set(v___x_3724_, 1, v___x_3718_);
v___x_3725_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3712_, v___x_3720_);
v___x_3726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3724_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
lean_inc(v___y_3717_);
v___x_3727_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___y_3717_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
v___x_3728_ = 0;
v___x_3729_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set_uint8(v___x_3729_, sizeof(void*)*1, v___x_3728_);
v___x_3730_ = l_Repr_addAppParen(v___x_3729_, v_prec_3703_);
return v___x_3730_;
}
}
}
}
case 1:
{
lean_object* v_uri_3737_; lean_object* v___y_3739_; lean_object* v___x_3747_; uint8_t v___x_3748_; 
v_uri_3737_ = lean_ctor_get(v_x_3702_, 0);
lean_inc_ref(v_uri_3737_);
lean_dec_ref_known(v_x_3702_, 1);
v___x_3747_ = lean_unsigned_to_nat(1024u);
v___x_3748_ = lean_nat_dec_le(v___x_3747_, v_prec_3703_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3749_; 
v___x_3749_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3739_ = v___x_3749_;
goto v___jp_3738_;
}
else
{
lean_object* v___x_3750_; 
v___x_3750_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3739_ = v___x_3750_;
goto v___jp_3738_;
}
v___jp_3738_:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; uint8_t v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3740_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__7));
v___x_3741_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3737_);
v___x_3742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3740_);
lean_ctor_set(v___x_3742_, 1, v___x_3741_);
lean_inc(v___y_3739_);
v___x_3743_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___y_3739_);
lean_ctor_set(v___x_3743_, 1, v___x_3742_);
v___x_3744_ = 0;
v___x_3745_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3745_, 0, v___x_3743_);
lean_ctor_set_uint8(v___x_3745_, sizeof(void*)*1, v___x_3744_);
v___x_3746_ = l_Repr_addAppParen(v___x_3745_, v_prec_3703_);
return v___x_3746_;
}
}
case 2:
{
lean_object* v_authority_3751_; lean_object* v___y_3753_; lean_object* v___x_3761_; uint8_t v___x_3762_; 
v_authority_3751_ = lean_ctor_get(v_x_3702_, 0);
lean_inc_ref(v_authority_3751_);
lean_dec_ref_known(v_x_3702_, 1);
v___x_3761_ = lean_unsigned_to_nat(1024u);
v___x_3762_ = lean_nat_dec_le(v___x_3761_, v_prec_3703_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; 
v___x_3763_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3753_ = v___x_3763_;
goto v___jp_3752_;
}
else
{
lean_object* v___x_3764_; 
v___x_3764_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3753_ = v___x_3764_;
goto v___jp_3752_;
}
v___jp_3752_:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; uint8_t v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3754_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__10));
v___x_3755_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_authority_3751_);
v___x_3756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3754_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
lean_inc(v___y_3753_);
v___x_3757_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___y_3753_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
v___x_3758_ = 0;
v___x_3759_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3759_, 0, v___x_3757_);
lean_ctor_set_uint8(v___x_3759_, sizeof(void*)*1, v___x_3758_);
v___x_3760_ = l_Repr_addAppParen(v___x_3759_, v_prec_3703_);
return v___x_3760_;
}
}
default: 
{
lean_object* v___x_3765_; uint8_t v___x_3766_; 
v___x_3765_ = lean_unsigned_to_nat(1024u);
v___x_3766_ = lean_nat_dec_le(v___x_3765_, v_prec_3703_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; 
v___x_3767_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3705_ = v___x_3767_;
goto v___jp_3704_;
}
else
{
lean_object* v___x_3768_; 
v___x_3768_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3705_ = v___x_3768_;
goto v___jp_3704_;
}
}
}
v___jp_3704_:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; uint8_t v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3706_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__1));
lean_inc(v___y_3705_);
v___x_3707_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___y_3705_);
lean_ctor_set(v___x_3707_, 1, v___x_3706_);
v___x_3708_ = 0;
v___x_3709_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3709_, 0, v___x_3707_);
lean_ctor_set_uint8(v___x_3709_, sizeof(void*)*1, v___x_3708_);
v___x_3710_ = l_Repr_addAppParen(v___x_3709_, v_prec_3703_);
return v___x_3710_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr___boxed(lean_object* v_x_3769_, lean_object* v_prec_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Std_Http_instReprRequestTarget_repr(v_x_3769_, v_prec_3770_);
lean_dec(v_prec_3770_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path(lean_object* v_x_3779_){
_start:
{
switch(lean_obj_tag(v_x_3779_))
{
case 0:
{
lean_object* v_path_3780_; 
v_path_3780_ = lean_ctor_get(v_x_3779_, 0);
lean_inc_ref(v_path_3780_);
return v_path_3780_;
}
case 1:
{
lean_object* v_uri_3781_; lean_object* v_path_3782_; 
v_uri_3781_ = lean_ctor_get(v_x_3779_, 0);
v_path_3782_ = lean_ctor_get(v_uri_3781_, 2);
lean_inc_ref(v_path_3782_);
return v_path_3782_;
}
default: 
{
lean_object* v___x_3783_; 
v___x_3783_ = ((lean_object*)(l_Std_Http_RequestTarget_path___closed__1));
return v___x_3783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path___boxed(lean_object* v_x_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l_Std_Http_RequestTarget_path(v_x_3784_);
lean_dec(v_x_3784_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query(lean_object* v_x_3786_){
_start:
{
switch(lean_obj_tag(v_x_3786_))
{
case 0:
{
lean_object* v_query_3787_; 
v_query_3787_ = lean_ctor_get(v_x_3786_, 1);
if (lean_obj_tag(v_query_3787_) == 0)
{
lean_object* v___x_3788_; 
v___x_3788_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3788_;
}
else
{
lean_object* v_val_3789_; 
v_val_3789_ = lean_ctor_get(v_query_3787_, 0);
lean_inc(v_val_3789_);
return v_val_3789_;
}
}
case 1:
{
lean_object* v_uri_3790_; lean_object* v_query_3791_; 
v_uri_3790_ = lean_ctor_get(v_x_3786_, 0);
v_query_3791_ = lean_ctor_get(v_uri_3790_, 3);
if (lean_obj_tag(v_query_3791_) == 0)
{
lean_object* v___x_3792_; 
v___x_3792_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3792_;
}
else
{
lean_object* v_val_3793_; 
v_val_3793_ = lean_ctor_get(v_query_3791_, 0);
lean_inc(v_val_3793_);
return v_val_3793_;
}
}
default: 
{
lean_object* v___x_3794_; 
v___x_3794_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query___boxed(lean_object* v_x_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_Std_Http_RequestTarget_query(v_x_3795_);
lean_dec(v_x_3795_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authority_x3f(lean_object* v_x_3797_){
_start:
{
switch(lean_obj_tag(v_x_3797_))
{
case 2:
{
lean_object* v_authority_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
v_authority_3798_ = lean_ctor_get(v_x_3797_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v_x_3797_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v_x_3797_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_authority_3798_);
lean_dec(v_x_3797_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
lean_ctor_set_tag(v___x_3800_, 1);
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_authority_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
case 1:
{
lean_object* v_uri_3806_; lean_object* v_authority_3807_; 
v_uri_3806_ = lean_ctor_get(v_x_3797_, 0);
lean_inc_ref(v_uri_3806_);
lean_dec_ref_known(v_x_3797_, 1);
v_authority_3807_ = lean_ctor_get(v_uri_3806_, 1);
lean_inc(v_authority_3807_);
lean_dec_ref(v_uri_3806_);
return v_authority_3807_;
}
default: 
{
lean_object* v___x_3808_; 
lean_dec(v_x_3797_);
v___x_3808_ = lean_box(0);
return v___x_3808_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__2(lean_object* v___f_3810_, lean_object* v___f_3811_, lean_object* v_x_3812_){
_start:
{
lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; 
switch(lean_obj_tag(v_x_3812_))
{
case 0:
{
lean_object* v_path_3819_; lean_object* v_query_3820_; lean_object* v___y_3822_; lean_object* v_segments_3825_; uint8_t v_absolute_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; size_t v_sz_3829_; size_t v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v_result_3833_; 
lean_dec_ref(v___f_3811_);
v_path_3819_ = lean_ctor_get(v_x_3812_, 0);
lean_inc_ref(v_path_3819_);
v_query_3820_ = lean_ctor_get(v_x_3812_, 1);
lean_inc(v_query_3820_);
lean_dec_ref_known(v_x_3812_, 2);
v_segments_3825_ = lean_ctor_get(v_path_3819_, 0);
lean_inc_ref(v_segments_3825_);
v_absolute_3826_ = lean_ctor_get_uint8(v_path_3819_, sizeof(void*)*1);
lean_dec_ref(v_path_3819_);
v___x_3827_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3828_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3829_ = lean_array_size(v_segments_3825_);
v___x_3830_ = ((size_t)0ULL);
v___x_3831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3828_, v___f_3810_, v_sz_3829_, v___x_3830_, v_segments_3825_);
v___x_3832_ = lean_array_to_list(v___x_3831_);
v_result_3833_ = l_String_intercalate(v___x_3827_, v___x_3832_);
if (v_absolute_3826_ == 0)
{
v___y_3822_ = v_result_3833_;
goto v___jp_3821_;
}
else
{
lean_object* v___x_3834_; 
v___x_3834_ = lean_string_append(v___x_3827_, v_result_3833_);
lean_dec_ref(v_result_3833_);
v___y_3822_ = v___x_3834_;
goto v___jp_3821_;
}
v___jp_3821_:
{
lean_object* v_queryStr_3823_; lean_object* v___x_3824_; 
v_queryStr_3823_ = l_Std_Http_URI_Query_formatOption(v_query_3820_);
v___x_3824_ = lean_string_append(v___y_3822_, v_queryStr_3823_);
lean_dec_ref(v_queryStr_3823_);
return v___x_3824_;
}
}
case 1:
{
lean_object* v_uri_3835_; lean_object* v_scheme_3836_; lean_object* v_authority_3837_; lean_object* v_path_3838_; lean_object* v_query_3839_; lean_object* v_fragment_3840_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3863_; 
lean_dec_ref(v___f_3810_);
v_uri_3835_ = lean_ctor_get(v_x_3812_, 0);
lean_inc_ref(v_uri_3835_);
lean_dec_ref_known(v_x_3812_, 1);
v_scheme_3836_ = lean_ctor_get(v_uri_3835_, 0);
lean_inc_ref(v_scheme_3836_);
v_authority_3837_ = lean_ctor_get(v_uri_3835_, 1);
lean_inc(v_authority_3837_);
v_path_3838_ = lean_ctor_get(v_uri_3835_, 2);
lean_inc_ref(v_path_3838_);
v_query_3839_ = lean_ctor_get(v_uri_3835_, 3);
lean_inc(v_query_3839_);
v_fragment_3840_ = lean_ctor_get(v_uri_3835_, 4);
lean_inc(v_fragment_3840_);
lean_dec_ref(v_uri_3835_);
if (lean_obj_tag(v_authority_3837_) == 0)
{
lean_object* v___x_3874_; 
v___x_3874_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3863_ = v___x_3874_;
goto v___jp_3862_;
}
else
{
lean_object* v_val_3875_; lean_object* v_userInfo_3876_; lean_object* v_host_3877_; lean_object* v_port_3878_; lean_object* v___x_3879_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3898_; 
v_val_3875_ = lean_ctor_get(v_authority_3837_, 0);
lean_inc(v_val_3875_);
lean_dec_ref_known(v_authority_3837_, 1);
v_userInfo_3876_ = lean_ctor_get(v_val_3875_, 0);
lean_inc(v_userInfo_3876_);
v_host_3877_ = lean_ctor_get(v_val_3875_, 1);
lean_inc_ref(v_host_3877_);
v_port_3878_ = lean_ctor_get(v_val_3875_, 2);
lean_inc(v_port_3878_);
lean_dec(v_val_3875_);
v___x_3879_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3876_) == 0)
{
lean_object* v___x_3908_; 
v___x_3908_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3898_ = v___x_3908_;
goto v___jp_3897_;
}
else
{
lean_object* v_val_3909_; lean_object* v_password_3910_; 
v_val_3909_ = lean_ctor_get(v_userInfo_3876_, 0);
lean_inc(v_val_3909_);
lean_dec_ref_known(v_userInfo_3876_, 1);
v_password_3910_ = lean_ctor_get(v_val_3909_, 1);
if (lean_obj_tag(v_password_3910_) == 0)
{
lean_object* v_username_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_username_3911_ = lean_ctor_get(v_val_3909_, 0);
lean_inc_ref(v_username_3911_);
lean_dec(v_val_3909_);
v___x_3912_ = lean_string_from_utf8_unchecked(v_username_3911_);
v___x_3913_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3914_ = lean_string_append(v___x_3912_, v___x_3913_);
v___y_3898_ = v___x_3914_;
goto v___jp_3897_;
}
else
{
lean_object* v_username_3915_; lean_object* v_val_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
lean_inc_ref(v_password_3910_);
v_username_3915_ = lean_ctor_get(v_val_3909_, 0);
lean_inc_ref(v_username_3915_);
lean_dec(v_val_3909_);
v_val_3916_ = lean_ctor_get(v_password_3910_, 0);
lean_inc(v_val_3916_);
lean_dec_ref_known(v_password_3910_, 1);
v___x_3917_ = lean_string_from_utf8_unchecked(v_username_3915_);
v___x_3918_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3919_ = lean_string_append(v___x_3917_, v___x_3918_);
v___x_3920_ = lean_string_from_utf8_unchecked(v_val_3916_);
v___x_3921_ = lean_string_append(v___x_3919_, v___x_3920_);
lean_dec_ref(v___x_3920_);
v___x_3922_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3923_ = lean_string_append(v___x_3921_, v___x_3922_);
v___y_3898_ = v___x_3923_;
goto v___jp_3897_;
}
}
v___jp_3880_:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3884_ = lean_string_append(v___y_3881_, v___y_3882_);
lean_dec_ref(v___y_3882_);
v___x_3885_ = lean_string_append(v___x_3884_, v___y_3883_);
lean_dec_ref(v___y_3883_);
v___x_3886_ = lean_string_append(v___x_3879_, v___x_3885_);
lean_dec_ref(v___x_3885_);
v___y_3863_ = v___x_3886_;
goto v___jp_3862_;
}
v___jp_3887_:
{
switch(lean_obj_tag(v_port_3878_))
{
case 0:
{
lean_object* v___x_3890_; 
v___x_3890_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3881_ = v___y_3888_;
v___y_3882_ = v___y_3889_;
v___y_3883_ = v___x_3890_;
goto v___jp_3880_;
}
case 1:
{
lean_object* v___x_3891_; 
v___x_3891_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3881_ = v___y_3888_;
v___y_3882_ = v___y_3889_;
v___y_3883_ = v___x_3891_;
goto v___jp_3880_;
}
default: 
{
uint16_t v_port_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v_port_3892_ = lean_ctor_get_uint16(v_port_3878_, 0);
lean_dec_ref_known(v_port_3878_, 0);
v___x_3893_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3894_ = lean_uint16_to_nat(v_port_3892_);
v___x_3895_ = l_Nat_reprFast(v___x_3894_);
v___x_3896_ = lean_string_append(v___x_3893_, v___x_3895_);
lean_dec_ref(v___x_3895_);
v___y_3881_ = v___y_3888_;
v___y_3882_ = v___y_3889_;
v___y_3883_ = v___x_3896_;
goto v___jp_3880_;
}
}
}
v___jp_3897_:
{
switch(lean_obj_tag(v_host_3877_))
{
case 0:
{
lean_object* v_name_3899_; 
v_name_3899_ = lean_ctor_get(v_host_3877_, 0);
lean_inc_ref(v_name_3899_);
lean_dec_ref_known(v_host_3877_, 1);
v___y_3888_ = v___y_3898_;
v___y_3889_ = v_name_3899_;
goto v___jp_3887_;
}
case 1:
{
lean_object* v_ipv4_3900_; lean_object* v___x_3901_; 
v_ipv4_3900_ = lean_ctor_get(v_host_3877_, 0);
lean_inc_ref(v_ipv4_3900_);
lean_dec_ref_known(v_host_3877_, 1);
v___x_3901_ = lean_uv_ntop_v4(v_ipv4_3900_);
lean_dec_ref(v_ipv4_3900_);
v___y_3888_ = v___y_3898_;
v___y_3889_ = v___x_3901_;
goto v___jp_3887_;
}
default: 
{
lean_object* v_ipv6_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_ipv6_3902_ = lean_ctor_get(v_host_3877_, 0);
lean_inc_ref(v_ipv6_3902_);
lean_dec_ref_known(v_host_3877_, 1);
v___x_3903_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3904_ = lean_uv_ntop_v6(v_ipv6_3902_);
lean_dec_ref(v_ipv6_3902_);
v___x_3905_ = lean_string_append(v___x_3903_, v___x_3904_);
lean_dec_ref(v___x_3904_);
v___x_3906_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3907_ = lean_string_append(v___x_3905_, v___x_3906_);
v___y_3888_ = v___y_3898_;
v___y_3889_ = v___x_3907_;
goto v___jp_3887_;
}
}
}
}
v___jp_3841_:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3846_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3847_ = lean_string_append(v_scheme_3836_, v___x_3846_);
v___x_3848_ = lean_string_append(v___x_3847_, v___y_3844_);
lean_dec_ref(v___y_3844_);
v___x_3849_ = lean_string_append(v___x_3848_, v___y_3842_);
lean_dec_ref(v___y_3842_);
v___x_3850_ = lean_string_append(v___x_3849_, v___y_3843_);
lean_dec_ref(v___y_3843_);
v___x_3851_ = lean_string_append(v___x_3850_, v___y_3845_);
lean_dec_ref(v___y_3845_);
return v___x_3851_;
}
v___jp_3852_:
{
lean_object* v_queryPart_3855_; 
v_queryPart_3855_ = l_Std_Http_URI_Query_formatOption(v_query_3839_);
if (lean_obj_tag(v_fragment_3840_) == 0)
{
lean_object* v___x_3856_; 
v___x_3856_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3842_ = v___y_3854_;
v___y_3843_ = v_queryPart_3855_;
v___y_3844_ = v___y_3853_;
v___y_3845_ = v___x_3856_;
goto v___jp_3841_;
}
else
{
lean_object* v_val_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v_val_3857_ = lean_ctor_get(v_fragment_3840_, 0);
lean_inc(v_val_3857_);
lean_dec_ref_known(v_fragment_3840_, 1);
v___x_3858_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3859_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3857_);
lean_dec(v_val_3857_);
v___x_3860_ = lean_string_from_utf8_unchecked(v___x_3859_);
v___x_3861_ = lean_string_append(v___x_3858_, v___x_3860_);
lean_dec_ref(v___x_3860_);
v___y_3842_ = v___y_3854_;
v___y_3843_ = v_queryPart_3855_;
v___y_3844_ = v___y_3853_;
v___y_3845_ = v___x_3861_;
goto v___jp_3841_;
}
}
v___jp_3862_:
{
lean_object* v_segments_3864_; uint8_t v_absolute_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; size_t v_sz_3868_; size_t v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v_result_3872_; 
v_segments_3864_ = lean_ctor_get(v_path_3838_, 0);
lean_inc_ref(v_segments_3864_);
v_absolute_3865_ = lean_ctor_get_uint8(v_path_3838_, sizeof(void*)*1);
lean_dec_ref(v_path_3838_);
v___x_3866_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3867_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3868_ = lean_array_size(v_segments_3864_);
v___x_3869_ = ((size_t)0ULL);
v___x_3870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3867_, v___f_3811_, v_sz_3868_, v___x_3869_, v_segments_3864_);
v___x_3871_ = lean_array_to_list(v___x_3870_);
v_result_3872_ = l_String_intercalate(v___x_3866_, v___x_3871_);
if (v_absolute_3865_ == 0)
{
v___y_3853_ = v___y_3863_;
v___y_3854_ = v_result_3872_;
goto v___jp_3852_;
}
else
{
lean_object* v___x_3873_; 
v___x_3873_ = lean_string_append(v___x_3866_, v_result_3872_);
lean_dec_ref(v_result_3872_);
v___y_3853_ = v___y_3863_;
v___y_3854_ = v___x_3873_;
goto v___jp_3852_;
}
}
}
case 2:
{
lean_object* v_authority_3924_; lean_object* v_userInfo_3925_; lean_object* v_host_3926_; lean_object* v_port_3927_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3939_; 
lean_dec_ref(v___f_3811_);
lean_dec_ref(v___f_3810_);
v_authority_3924_ = lean_ctor_get(v_x_3812_, 0);
lean_inc_ref(v_authority_3924_);
lean_dec_ref_known(v_x_3812_, 1);
v_userInfo_3925_ = lean_ctor_get(v_authority_3924_, 0);
lean_inc(v_userInfo_3925_);
v_host_3926_ = lean_ctor_get(v_authority_3924_, 1);
lean_inc_ref(v_host_3926_);
v_port_3927_ = lean_ctor_get(v_authority_3924_, 2);
lean_inc(v_port_3927_);
lean_dec_ref(v_authority_3924_);
if (lean_obj_tag(v_userInfo_3925_) == 0)
{
lean_object* v___x_3949_; 
v___x_3949_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3939_ = v___x_3949_;
goto v___jp_3938_;
}
else
{
lean_object* v_val_3950_; lean_object* v_password_3951_; 
v_val_3950_ = lean_ctor_get(v_userInfo_3925_, 0);
lean_inc(v_val_3950_);
lean_dec_ref_known(v_userInfo_3925_, 1);
v_password_3951_ = lean_ctor_get(v_val_3950_, 1);
if (lean_obj_tag(v_password_3951_) == 0)
{
lean_object* v_username_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v_username_3952_ = lean_ctor_get(v_val_3950_, 0);
lean_inc_ref(v_username_3952_);
lean_dec(v_val_3950_);
v___x_3953_ = lean_string_from_utf8_unchecked(v_username_3952_);
v___x_3954_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3955_ = lean_string_append(v___x_3953_, v___x_3954_);
v___y_3939_ = v___x_3955_;
goto v___jp_3938_;
}
else
{
lean_object* v_username_3956_; lean_object* v_val_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
lean_inc_ref(v_password_3951_);
v_username_3956_ = lean_ctor_get(v_val_3950_, 0);
lean_inc_ref(v_username_3956_);
lean_dec(v_val_3950_);
v_val_3957_ = lean_ctor_get(v_password_3951_, 0);
lean_inc(v_val_3957_);
lean_dec_ref_known(v_password_3951_, 1);
v___x_3958_ = lean_string_from_utf8_unchecked(v_username_3956_);
v___x_3959_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3960_ = lean_string_append(v___x_3958_, v___x_3959_);
v___x_3961_ = lean_string_from_utf8_unchecked(v_val_3957_);
v___x_3962_ = lean_string_append(v___x_3960_, v___x_3961_);
lean_dec_ref(v___x_3961_);
v___x_3963_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3964_ = lean_string_append(v___x_3962_, v___x_3963_);
v___y_3939_ = v___x_3964_;
goto v___jp_3938_;
}
}
v___jp_3928_:
{
switch(lean_obj_tag(v_port_3927_))
{
case 0:
{
lean_object* v___x_3931_; 
v___x_3931_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3814_ = v___y_3930_;
v___y_3815_ = v___y_3929_;
v___y_3816_ = v___x_3931_;
goto v___jp_3813_;
}
case 1:
{
lean_object* v___x_3932_; 
v___x_3932_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3814_ = v___y_3930_;
v___y_3815_ = v___y_3929_;
v___y_3816_ = v___x_3932_;
goto v___jp_3813_;
}
default: 
{
uint16_t v_port_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v_port_3933_ = lean_ctor_get_uint16(v_port_3927_, 0);
lean_dec_ref_known(v_port_3927_, 0);
v___x_3934_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3935_ = lean_uint16_to_nat(v_port_3933_);
v___x_3936_ = l_Nat_reprFast(v___x_3935_);
v___x_3937_ = lean_string_append(v___x_3934_, v___x_3936_);
lean_dec_ref(v___x_3936_);
v___y_3814_ = v___y_3930_;
v___y_3815_ = v___y_3929_;
v___y_3816_ = v___x_3937_;
goto v___jp_3813_;
}
}
}
v___jp_3938_:
{
switch(lean_obj_tag(v_host_3926_))
{
case 0:
{
lean_object* v_name_3940_; 
v_name_3940_ = lean_ctor_get(v_host_3926_, 0);
lean_inc_ref(v_name_3940_);
lean_dec_ref_known(v_host_3926_, 1);
v___y_3929_ = v___y_3939_;
v___y_3930_ = v_name_3940_;
goto v___jp_3928_;
}
case 1:
{
lean_object* v_ipv4_3941_; lean_object* v___x_3942_; 
v_ipv4_3941_ = lean_ctor_get(v_host_3926_, 0);
lean_inc_ref(v_ipv4_3941_);
lean_dec_ref_known(v_host_3926_, 1);
v___x_3942_ = lean_uv_ntop_v4(v_ipv4_3941_);
lean_dec_ref(v_ipv4_3941_);
v___y_3929_ = v___y_3939_;
v___y_3930_ = v___x_3942_;
goto v___jp_3928_;
}
default: 
{
lean_object* v_ipv6_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v_ipv6_3943_ = lean_ctor_get(v_host_3926_, 0);
lean_inc_ref(v_ipv6_3943_);
lean_dec_ref_known(v_host_3926_, 1);
v___x_3944_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3945_ = lean_uv_ntop_v6(v_ipv6_3943_);
lean_dec_ref(v_ipv6_3943_);
v___x_3946_ = lean_string_append(v___x_3944_, v___x_3945_);
lean_dec_ref(v___x_3945_);
v___x_3947_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3948_ = lean_string_append(v___x_3946_, v___x_3947_);
v___y_3929_ = v___y_3939_;
v___y_3930_ = v___x_3948_;
goto v___jp_3928_;
}
}
}
}
default: 
{
lean_object* v___x_3965_; 
lean_dec_ref(v___f_3811_);
lean_dec_ref(v___f_3810_);
v___x_3965_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__2___closed__0));
return v___x_3965_;
}
}
v___jp_3813_:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3817_ = lean_string_append(v___y_3815_, v___y_3814_);
lean_dec_ref(v___y_3814_);
v___x_3818_ = lean_string_append(v___x_3817_, v___y_3816_);
lean_dec_ref(v___y_3816_);
return v___x_3818_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__2(lean_object* v___f_3969_, lean_object* v___f_3970_, lean_object* v_buffer_3971_, lean_object* v_target_3972_){
_start:
{
lean_object* v___y_3974_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; 
switch(lean_obj_tag(v_target_3972_))
{
case 0:
{
lean_object* v_path_3994_; lean_object* v_query_3995_; lean_object* v___y_3997_; lean_object* v_segments_4000_; uint8_t v_absolute_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; size_t v_sz_4004_; size_t v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v_result_4008_; 
lean_dec_ref(v___f_3970_);
v_path_3994_ = lean_ctor_get(v_target_3972_, 0);
lean_inc_ref(v_path_3994_);
v_query_3995_ = lean_ctor_get(v_target_3972_, 1);
lean_inc(v_query_3995_);
lean_dec_ref_known(v_target_3972_, 2);
v_segments_4000_ = lean_ctor_get(v_path_3994_, 0);
lean_inc_ref(v_segments_4000_);
v_absolute_4001_ = lean_ctor_get_uint8(v_path_3994_, sizeof(void*)*1);
lean_dec_ref(v_path_3994_);
v___x_4002_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_4003_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_4004_ = lean_array_size(v_segments_4000_);
v___x_4005_ = ((size_t)0ULL);
v___x_4006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4003_, v___f_3969_, v_sz_4004_, v___x_4005_, v_segments_4000_);
v___x_4007_ = lean_array_to_list(v___x_4006_);
v_result_4008_ = l_String_intercalate(v___x_4002_, v___x_4007_);
if (v_absolute_4001_ == 0)
{
v___y_3997_ = v_result_4008_;
goto v___jp_3996_;
}
else
{
lean_object* v___x_4009_; 
v___x_4009_ = lean_string_append(v___x_4002_, v_result_4008_);
lean_dec_ref(v_result_4008_);
v___y_3997_ = v___x_4009_;
goto v___jp_3996_;
}
v___jp_3996_:
{
lean_object* v_queryStr_3998_; lean_object* v___x_3999_; 
v_queryStr_3998_ = l_Std_Http_URI_Query_formatOption(v_query_3995_);
v___x_3999_ = lean_string_append(v___y_3997_, v_queryStr_3998_);
lean_dec_ref(v_queryStr_3998_);
v___y_3974_ = v___x_3999_;
goto v___jp_3973_;
}
}
case 1:
{
lean_object* v_uri_4010_; lean_object* v_scheme_4011_; lean_object* v_authority_4012_; lean_object* v_path_4013_; lean_object* v_query_4014_; lean_object* v_fragment_4015_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4038_; 
lean_dec_ref(v___f_3969_);
v_uri_4010_ = lean_ctor_get(v_target_3972_, 0);
lean_inc_ref(v_uri_4010_);
lean_dec_ref_known(v_target_3972_, 1);
v_scheme_4011_ = lean_ctor_get(v_uri_4010_, 0);
lean_inc_ref(v_scheme_4011_);
v_authority_4012_ = lean_ctor_get(v_uri_4010_, 1);
lean_inc(v_authority_4012_);
v_path_4013_ = lean_ctor_get(v_uri_4010_, 2);
lean_inc_ref(v_path_4013_);
v_query_4014_ = lean_ctor_get(v_uri_4010_, 3);
lean_inc(v_query_4014_);
v_fragment_4015_ = lean_ctor_get(v_uri_4010_, 4);
lean_inc(v_fragment_4015_);
lean_dec_ref(v_uri_4010_);
if (lean_obj_tag(v_authority_4012_) == 0)
{
lean_object* v___x_4049_; 
v___x_4049_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4038_ = v___x_4049_;
goto v___jp_4037_;
}
else
{
lean_object* v_val_4050_; lean_object* v_userInfo_4051_; lean_object* v_host_4052_; lean_object* v_port_4053_; lean_object* v___x_4054_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4073_; 
v_val_4050_ = lean_ctor_get(v_authority_4012_, 0);
lean_inc(v_val_4050_);
lean_dec_ref_known(v_authority_4012_, 1);
v_userInfo_4051_ = lean_ctor_get(v_val_4050_, 0);
lean_inc(v_userInfo_4051_);
v_host_4052_ = lean_ctor_get(v_val_4050_, 1);
lean_inc_ref(v_host_4052_);
v_port_4053_ = lean_ctor_get(v_val_4050_, 2);
lean_inc(v_port_4053_);
lean_dec(v_val_4050_);
v___x_4054_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_4051_) == 0)
{
lean_object* v___x_4083_; 
v___x_4083_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4073_ = v___x_4083_;
goto v___jp_4072_;
}
else
{
lean_object* v_val_4084_; lean_object* v_password_4085_; 
v_val_4084_ = lean_ctor_get(v_userInfo_4051_, 0);
lean_inc(v_val_4084_);
lean_dec_ref_known(v_userInfo_4051_, 1);
v_password_4085_ = lean_ctor_get(v_val_4084_, 1);
if (lean_obj_tag(v_password_4085_) == 0)
{
lean_object* v_username_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v_username_4086_ = lean_ctor_get(v_val_4084_, 0);
lean_inc_ref(v_username_4086_);
lean_dec(v_val_4084_);
v___x_4087_ = lean_string_from_utf8_unchecked(v_username_4086_);
v___x_4088_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4089_ = lean_string_append(v___x_4087_, v___x_4088_);
v___y_4073_ = v___x_4089_;
goto v___jp_4072_;
}
else
{
lean_object* v_username_4090_; lean_object* v_val_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
lean_inc_ref(v_password_4085_);
v_username_4090_ = lean_ctor_get(v_val_4084_, 0);
lean_inc_ref(v_username_4090_);
lean_dec(v_val_4084_);
v_val_4091_ = lean_ctor_get(v_password_4085_, 0);
lean_inc(v_val_4091_);
lean_dec_ref_known(v_password_4085_, 1);
v___x_4092_ = lean_string_from_utf8_unchecked(v_username_4090_);
v___x_4093_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4094_ = lean_string_append(v___x_4092_, v___x_4093_);
v___x_4095_ = lean_string_from_utf8_unchecked(v_val_4091_);
v___x_4096_ = lean_string_append(v___x_4094_, v___x_4095_);
lean_dec_ref(v___x_4095_);
v___x_4097_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4098_ = lean_string_append(v___x_4096_, v___x_4097_);
v___y_4073_ = v___x_4098_;
goto v___jp_4072_;
}
}
v___jp_4055_:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4059_ = lean_string_append(v___y_4056_, v___y_4057_);
lean_dec_ref(v___y_4057_);
v___x_4060_ = lean_string_append(v___x_4059_, v___y_4058_);
lean_dec_ref(v___y_4058_);
v___x_4061_ = lean_string_append(v___x_4054_, v___x_4060_);
lean_dec_ref(v___x_4060_);
v___y_4038_ = v___x_4061_;
goto v___jp_4037_;
}
v___jp_4062_:
{
switch(lean_obj_tag(v_port_4053_))
{
case 0:
{
lean_object* v___x_4065_; 
v___x_4065_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4056_ = v___y_4063_;
v___y_4057_ = v___y_4064_;
v___y_4058_ = v___x_4065_;
goto v___jp_4055_;
}
case 1:
{
lean_object* v___x_4066_; 
v___x_4066_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_4056_ = v___y_4063_;
v___y_4057_ = v___y_4064_;
v___y_4058_ = v___x_4066_;
goto v___jp_4055_;
}
default: 
{
uint16_t v_port_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v_port_4067_ = lean_ctor_get_uint16(v_port_4053_, 0);
lean_dec_ref_known(v_port_4053_, 0);
v___x_4068_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4069_ = lean_uint16_to_nat(v_port_4067_);
v___x_4070_ = l_Nat_reprFast(v___x_4069_);
v___x_4071_ = lean_string_append(v___x_4068_, v___x_4070_);
lean_dec_ref(v___x_4070_);
v___y_4056_ = v___y_4063_;
v___y_4057_ = v___y_4064_;
v___y_4058_ = v___x_4071_;
goto v___jp_4055_;
}
}
}
v___jp_4072_:
{
switch(lean_obj_tag(v_host_4052_))
{
case 0:
{
lean_object* v_name_4074_; 
v_name_4074_ = lean_ctor_get(v_host_4052_, 0);
lean_inc_ref(v_name_4074_);
lean_dec_ref_known(v_host_4052_, 1);
v___y_4063_ = v___y_4073_;
v___y_4064_ = v_name_4074_;
goto v___jp_4062_;
}
case 1:
{
lean_object* v_ipv4_4075_; lean_object* v___x_4076_; 
v_ipv4_4075_ = lean_ctor_get(v_host_4052_, 0);
lean_inc_ref(v_ipv4_4075_);
lean_dec_ref_known(v_host_4052_, 1);
v___x_4076_ = lean_uv_ntop_v4(v_ipv4_4075_);
lean_dec_ref(v_ipv4_4075_);
v___y_4063_ = v___y_4073_;
v___y_4064_ = v___x_4076_;
goto v___jp_4062_;
}
default: 
{
lean_object* v_ipv6_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v_ipv6_4077_ = lean_ctor_get(v_host_4052_, 0);
lean_inc_ref(v_ipv6_4077_);
lean_dec_ref_known(v_host_4052_, 1);
v___x_4078_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4079_ = lean_uv_ntop_v6(v_ipv6_4077_);
lean_dec_ref(v_ipv6_4077_);
v___x_4080_ = lean_string_append(v___x_4078_, v___x_4079_);
lean_dec_ref(v___x_4079_);
v___x_4081_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4082_ = lean_string_append(v___x_4080_, v___x_4081_);
v___y_4063_ = v___y_4073_;
v___y_4064_ = v___x_4082_;
goto v___jp_4062_;
}
}
}
}
v___jp_4016_:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4021_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4022_ = lean_string_append(v_scheme_4011_, v___x_4021_);
v___x_4023_ = lean_string_append(v___x_4022_, v___y_4018_);
lean_dec_ref(v___y_4018_);
v___x_4024_ = lean_string_append(v___x_4023_, v___y_4017_);
lean_dec_ref(v___y_4017_);
v___x_4025_ = lean_string_append(v___x_4024_, v___y_4019_);
lean_dec_ref(v___y_4019_);
v___x_4026_ = lean_string_append(v___x_4025_, v___y_4020_);
lean_dec_ref(v___y_4020_);
v___y_3974_ = v___x_4026_;
goto v___jp_3973_;
}
v___jp_4027_:
{
lean_object* v_queryPart_4030_; 
v_queryPart_4030_ = l_Std_Http_URI_Query_formatOption(v_query_4014_);
if (lean_obj_tag(v_fragment_4015_) == 0)
{
lean_object* v___x_4031_; 
v___x_4031_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4017_ = v___y_4029_;
v___y_4018_ = v___y_4028_;
v___y_4019_ = v_queryPart_4030_;
v___y_4020_ = v___x_4031_;
goto v___jp_4016_;
}
else
{
lean_object* v_val_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v_val_4032_ = lean_ctor_get(v_fragment_4015_, 0);
lean_inc(v_val_4032_);
lean_dec_ref_known(v_fragment_4015_, 1);
v___x_4033_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_4034_ = l_Std_Http_URI_EncodedFragment_encode(v_val_4032_);
lean_dec(v_val_4032_);
v___x_4035_ = lean_string_from_utf8_unchecked(v___x_4034_);
v___x_4036_ = lean_string_append(v___x_4033_, v___x_4035_);
lean_dec_ref(v___x_4035_);
v___y_4017_ = v___y_4029_;
v___y_4018_ = v___y_4028_;
v___y_4019_ = v_queryPart_4030_;
v___y_4020_ = v___x_4036_;
goto v___jp_4016_;
}
}
v___jp_4037_:
{
lean_object* v_segments_4039_; uint8_t v_absolute_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; size_t v_sz_4043_; size_t v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v_result_4047_; 
v_segments_4039_ = lean_ctor_get(v_path_4013_, 0);
lean_inc_ref(v_segments_4039_);
v_absolute_4040_ = lean_ctor_get_uint8(v_path_4013_, sizeof(void*)*1);
lean_dec_ref(v_path_4013_);
v___x_4041_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_4042_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_4043_ = lean_array_size(v_segments_4039_);
v___x_4044_ = ((size_t)0ULL);
v___x_4045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4042_, v___f_3970_, v_sz_4043_, v___x_4044_, v_segments_4039_);
v___x_4046_ = lean_array_to_list(v___x_4045_);
v_result_4047_ = l_String_intercalate(v___x_4041_, v___x_4046_);
if (v_absolute_4040_ == 0)
{
v___y_4028_ = v___y_4038_;
v___y_4029_ = v_result_4047_;
goto v___jp_4027_;
}
else
{
lean_object* v___x_4048_; 
v___x_4048_ = lean_string_append(v___x_4041_, v_result_4047_);
lean_dec_ref(v_result_4047_);
v___y_4028_ = v___y_4038_;
v___y_4029_ = v___x_4048_;
goto v___jp_4027_;
}
}
}
case 2:
{
lean_object* v_authority_4099_; lean_object* v_userInfo_4100_; lean_object* v_host_4101_; lean_object* v_port_4102_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4114_; 
lean_dec_ref(v___f_3970_);
lean_dec_ref(v___f_3969_);
v_authority_4099_ = lean_ctor_get(v_target_3972_, 0);
lean_inc_ref(v_authority_4099_);
lean_dec_ref_known(v_target_3972_, 1);
v_userInfo_4100_ = lean_ctor_get(v_authority_4099_, 0);
lean_inc(v_userInfo_4100_);
v_host_4101_ = lean_ctor_get(v_authority_4099_, 1);
lean_inc_ref(v_host_4101_);
v_port_4102_ = lean_ctor_get(v_authority_4099_, 2);
lean_inc(v_port_4102_);
lean_dec_ref(v_authority_4099_);
if (lean_obj_tag(v_userInfo_4100_) == 0)
{
lean_object* v___x_4124_; 
v___x_4124_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4114_ = v___x_4124_;
goto v___jp_4113_;
}
else
{
lean_object* v_val_4125_; lean_object* v_password_4126_; 
v_val_4125_ = lean_ctor_get(v_userInfo_4100_, 0);
lean_inc(v_val_4125_);
lean_dec_ref_known(v_userInfo_4100_, 1);
v_password_4126_ = lean_ctor_get(v_val_4125_, 1);
if (lean_obj_tag(v_password_4126_) == 0)
{
lean_object* v_username_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v_username_4127_ = lean_ctor_get(v_val_4125_, 0);
lean_inc_ref(v_username_4127_);
lean_dec(v_val_4125_);
v___x_4128_ = lean_string_from_utf8_unchecked(v_username_4127_);
v___x_4129_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4130_ = lean_string_append(v___x_4128_, v___x_4129_);
v___y_4114_ = v___x_4130_;
goto v___jp_4113_;
}
else
{
lean_object* v_username_4131_; lean_object* v_val_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
lean_inc_ref(v_password_4126_);
v_username_4131_ = lean_ctor_get(v_val_4125_, 0);
lean_inc_ref(v_username_4131_);
lean_dec(v_val_4125_);
v_val_4132_ = lean_ctor_get(v_password_4126_, 0);
lean_inc(v_val_4132_);
lean_dec_ref_known(v_password_4126_, 1);
v___x_4133_ = lean_string_from_utf8_unchecked(v_username_4131_);
v___x_4134_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4135_ = lean_string_append(v___x_4133_, v___x_4134_);
v___x_4136_ = lean_string_from_utf8_unchecked(v_val_4132_);
v___x_4137_ = lean_string_append(v___x_4135_, v___x_4136_);
lean_dec_ref(v___x_4136_);
v___x_4138_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4139_ = lean_string_append(v___x_4137_, v___x_4138_);
v___y_4114_ = v___x_4139_;
goto v___jp_4113_;
}
}
v___jp_4103_:
{
switch(lean_obj_tag(v_port_4102_))
{
case 0:
{
lean_object* v___x_4106_; 
v___x_4106_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3989_ = v___y_4105_;
v___y_3990_ = v___y_4104_;
v___y_3991_ = v___x_4106_;
goto v___jp_3988_;
}
case 1:
{
lean_object* v___x_4107_; 
v___x_4107_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3989_ = v___y_4105_;
v___y_3990_ = v___y_4104_;
v___y_3991_ = v___x_4107_;
goto v___jp_3988_;
}
default: 
{
uint16_t v_port_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v_port_4108_ = lean_ctor_get_uint16(v_port_4102_, 0);
lean_dec_ref_known(v_port_4102_, 0);
v___x_4109_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4110_ = lean_uint16_to_nat(v_port_4108_);
v___x_4111_ = l_Nat_reprFast(v___x_4110_);
v___x_4112_ = lean_string_append(v___x_4109_, v___x_4111_);
lean_dec_ref(v___x_4111_);
v___y_3989_ = v___y_4105_;
v___y_3990_ = v___y_4104_;
v___y_3991_ = v___x_4112_;
goto v___jp_3988_;
}
}
}
v___jp_4113_:
{
switch(lean_obj_tag(v_host_4101_))
{
case 0:
{
lean_object* v_name_4115_; 
v_name_4115_ = lean_ctor_get(v_host_4101_, 0);
lean_inc_ref(v_name_4115_);
lean_dec_ref_known(v_host_4101_, 1);
v___y_4104_ = v___y_4114_;
v___y_4105_ = v_name_4115_;
goto v___jp_4103_;
}
case 1:
{
lean_object* v_ipv4_4116_; lean_object* v___x_4117_; 
v_ipv4_4116_ = lean_ctor_get(v_host_4101_, 0);
lean_inc_ref(v_ipv4_4116_);
lean_dec_ref_known(v_host_4101_, 1);
v___x_4117_ = lean_uv_ntop_v4(v_ipv4_4116_);
lean_dec_ref(v_ipv4_4116_);
v___y_4104_ = v___y_4114_;
v___y_4105_ = v___x_4117_;
goto v___jp_4103_;
}
default: 
{
lean_object* v_ipv6_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v_ipv6_4118_ = lean_ctor_get(v_host_4101_, 0);
lean_inc_ref(v_ipv6_4118_);
lean_dec_ref_known(v_host_4101_, 1);
v___x_4119_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4120_ = lean_uv_ntop_v6(v_ipv6_4118_);
lean_dec_ref(v_ipv6_4118_);
v___x_4121_ = lean_string_append(v___x_4119_, v___x_4120_);
lean_dec_ref(v___x_4120_);
v___x_4122_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4123_ = lean_string_append(v___x_4121_, v___x_4122_);
v___y_4104_ = v___y_4114_;
v___y_4105_ = v___x_4123_;
goto v___jp_4103_;
}
}
}
}
default: 
{
lean_object* v___x_4140_; 
lean_dec_ref(v___f_3970_);
lean_dec_ref(v___f_3969_);
v___x_4140_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__2___closed__0));
v___y_3974_ = v___x_4140_;
goto v___jp_3973_;
}
}
v___jp_3973_:
{
lean_object* v_data_3975_; lean_object* v_size_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3987_; 
v_data_3975_ = lean_ctor_get(v_buffer_3971_, 0);
v_size_3976_ = lean_ctor_get(v_buffer_3971_, 1);
v_isSharedCheck_3987_ = !lean_is_exclusive(v_buffer_3971_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3978_ = v_buffer_3971_;
v_isShared_3979_ = v_isSharedCheck_3987_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_size_3976_);
lean_inc(v_data_3975_);
lean_dec(v_buffer_3971_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3987_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3985_; 
v___x_3980_ = lean_string_to_utf8(v___y_3974_);
lean_dec_ref(v___y_3974_);
lean_inc_ref(v___x_3980_);
v___x_3981_ = lean_array_push(v_data_3975_, v___x_3980_);
v___x_3982_ = lean_byte_array_size(v___x_3980_);
lean_dec_ref(v___x_3980_);
v___x_3983_ = lean_nat_add(v_size_3976_, v___x_3982_);
lean_dec(v_size_3976_);
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 1, v___x_3983_);
lean_ctor_set(v___x_3978_, 0, v___x_3981_);
v___x_3985_ = v___x_3978_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___x_3981_);
lean_ctor_set(v_reuseFailAlloc_3986_, 1, v___x_3983_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
v___jp_3988_:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3992_ = lean_string_append(v___y_3990_, v___y_3989_);
lean_dec_ref(v___y_3989_);
v___x_3993_ = lean_string_append(v___x_3992_, v___y_3991_);
lean_dec_ref(v___y_3991_);
v___y_3974_ = v___x_3993_;
goto v___jp_3973_;
}
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
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
