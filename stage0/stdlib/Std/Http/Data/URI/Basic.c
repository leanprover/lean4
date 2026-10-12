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
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t l_Std_Http_Internal_instDecidableIsLowerCase(lean_object*);
lean_object* l_String_toListImpl(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_sarray_dec_eq(lean_object*, lean_object*);
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
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_List_getLast_x3f___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object*);
extern lean_object* l_Std_Net_instInhabitedIPv4Addr_default;
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_instToStringURIReference___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instToStringURIReference___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instToStringURIReference___lam__2, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value),((lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value)} };
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
uint32_t v___x_13_; uint32_t v___x_14_; uint8_t v___x_15_; 
v___x_13_ = lean_string_utf8_get_fast(v_s_3_, v_p_4_);
v___x_14_ = 65;
v___x_15_ = lean_uint32_dec_le(v___x_14_, v___x_13_);
if (v___x_15_ == 0)
{
v___y_6_ = v___x_13_;
goto v___jp_5_;
}
else
{
uint32_t v___x_16_; uint8_t v___x_17_; 
v___x_16_ = 90;
v___x_17_ = lean_uint32_dec_le(v___x_13_, v___x_16_);
if (v___x_17_ == 0)
{
v___y_6_ = v___x_13_;
goto v___jp_5_;
}
else
{
uint32_t v___x_18_; uint32_t v___x_19_; 
v___x_18_ = 32;
v___x_19_ = lean_uint32_add(v___x_13_, v___x_18_);
v___y_6_ = v___x_19_;
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
uint8_t l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(lean_object* v_x_20_){
_start:
{
if (lean_obj_tag(v_x_20_) == 0)
{
uint8_t v___x_21_; 
v___x_21_ = 1;
return v___x_21_;
}
else
{
lean_object* v_head_22_; lean_object* v_tail_23_; uint32_t v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v_head_22_ = lean_ctor_get(v_x_20_, 0);
v_tail_23_ = lean_ctor_get(v_x_20_, 1);
v___x_53_ = lean_unbox_uint32(v_head_22_);
v___x_54_ = lean_uint32_to_nat(v___x_53_);
v___x_55_ = lean_unsigned_to_nat(128u);
v___x_56_ = lean_nat_dec_lt(v___x_54_, v___x_55_);
lean_dec(v___x_54_);
if (v___x_56_ == 0)
{
goto v___jp_24_;
}
else
{
uint32_t v___x_57_; uint32_t v___x_58_; uint8_t v___x_59_; 
v___x_57_ = 48;
v___x_58_ = lean_unbox_uint32(v_head_22_);
v___x_59_ = lean_uint32_dec_le(v___x_57_, v___x_58_);
if (v___x_59_ == 0)
{
goto v___jp_45_;
}
else
{
uint32_t v___x_60_; uint32_t v___x_61_; uint8_t v___x_62_; 
v___x_60_ = 57;
v___x_61_ = lean_unbox_uint32(v_head_22_);
v___x_62_ = lean_uint32_dec_le(v___x_61_, v___x_60_);
if (v___x_62_ == 0)
{
goto v___jp_45_;
}
else
{
v_x_20_ = v_tail_23_;
goto _start;
}
}
}
v___jp_24_:
{
uint32_t v___x_25_; uint32_t v___x_26_; uint8_t v___x_27_; 
v___x_25_ = 43;
v___x_26_ = lean_unbox_uint32(v_head_22_);
v___x_27_ = lean_uint32_dec_eq(v___x_26_, v___x_25_);
if (v___x_27_ == 0)
{
uint32_t v___x_28_; uint32_t v___x_29_; uint8_t v___x_30_; 
v___x_28_ = 45;
v___x_29_ = lean_unbox_uint32(v_head_22_);
v___x_30_ = lean_uint32_dec_eq(v___x_29_, v___x_28_);
if (v___x_30_ == 0)
{
uint32_t v___x_31_; uint32_t v___x_32_; uint8_t v___x_33_; 
v___x_31_ = 46;
v___x_32_ = lean_unbox_uint32(v_head_22_);
v___x_33_ = lean_uint32_dec_eq(v___x_32_, v___x_31_);
if (v___x_33_ == 0)
{
return v___x_33_;
}
else
{
v_x_20_ = v_tail_23_;
goto _start;
}
}
else
{
v_x_20_ = v_tail_23_;
goto _start;
}
}
else
{
v_x_20_ = v_tail_23_;
goto _start;
}
}
v___jp_37_:
{
uint32_t v___x_38_; uint32_t v___x_39_; uint8_t v___x_40_; 
v___x_38_ = 97;
v___x_39_ = lean_unbox_uint32(v_head_22_);
v___x_40_ = lean_uint32_dec_le(v___x_38_, v___x_39_);
if (v___x_40_ == 0)
{
goto v___jp_24_;
}
else
{
uint32_t v___x_41_; uint32_t v___x_42_; uint8_t v___x_43_; 
v___x_41_ = 122;
v___x_42_ = lean_unbox_uint32(v_head_22_);
v___x_43_ = lean_uint32_dec_le(v___x_42_, v___x_41_);
if (v___x_43_ == 0)
{
goto v___jp_24_;
}
else
{
v_x_20_ = v_tail_23_;
goto _start;
}
}
}
v___jp_45_:
{
uint32_t v___x_46_; uint32_t v___x_47_; uint8_t v___x_48_; 
v___x_46_ = 65;
v___x_47_ = lean_unbox_uint32(v_head_22_);
v___x_48_ = lean_uint32_dec_le(v___x_46_, v___x_47_);
if (v___x_48_ == 0)
{
goto v___jp_37_;
}
else
{
uint32_t v___x_49_; uint32_t v___x_50_; uint8_t v___x_51_; 
v___x_49_ = 90;
v___x_50_ = lean_unbox_uint32(v_head_22_);
v___x_51_ = lean_uint32_dec_le(v___x_50_, v___x_49_);
if (v___x_51_ == 0)
{
goto v___jp_37_;
}
else
{
v_x_20_ = v_tail_23_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_20_ = stack[0].m_obj;
uint8_t v_res_64_;
v_res_64_ = l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(v_x_20_);
stack->m_num = v_res_64_;
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1___boxed(lean_object* v_x_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(v_x_65_);
lean_dec(v_x_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x3f(lean_object* v_s_68_){
_start:
{
lean_object* v___x_69_; lean_object* v_lower_70_; uint8_t v___y_72_; uint8_t v___x_75_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v_lower_70_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_68_, v___x_69_);
lean_inc_ref(v_lower_70_);
v___x_75_ = l_Std_Http_Internal_instDecidableIsLowerCase(v_lower_70_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; 
lean_dec_ref(v_lower_70_);
v___x_76_ = lean_box(0);
return v___x_76_;
}
else
{
lean_object* v___x_77_; uint8_t v___x_78_; 
lean_inc_ref(v_lower_70_);
v___x_77_ = l_String_toListImpl(v_lower_70_);
v___x_78_ = l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(v___x_77_);
if (v___x_78_ == 0)
{
lean_dec(v___x_77_);
v___y_72_ = v___x_78_;
goto v___jp_71_;
}
else
{
lean_object* v___x_79_; 
v___x_79_ = l_List_head_x3f___redArg(v___x_77_);
lean_dec(v___x_77_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v___x_80_; 
lean_dec_ref(v_lower_70_);
v___x_80_ = lean_box(0);
return v___x_80_;
}
else
{
lean_object* v_val_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_102_; 
v_val_81_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_102_ == 0)
{
v___x_83_ = v___x_79_;
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_val_81_);
lean_dec(v___x_79_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
uint32_t v___x_93_; uint32_t v___x_94_; uint8_t v___x_95_; 
v___x_93_ = 65;
v___x_94_ = lean_unbox_uint32(v_val_81_);
v___x_95_ = lean_uint32_dec_le(v___x_93_, v___x_94_);
if (v___x_95_ == 0)
{
lean_del_object(v___x_83_);
goto v___jp_85_;
}
else
{
uint32_t v___x_96_; uint32_t v___x_97_; uint8_t v___x_98_; 
v___x_96_ = 90;
v___x_97_ = lean_unbox_uint32(v_val_81_);
v___x_98_ = lean_uint32_dec_le(v___x_97_, v___x_96_);
if (v___x_98_ == 0)
{
lean_del_object(v___x_83_);
goto v___jp_85_;
}
else
{
lean_object* v___x_100_; 
lean_dec(v_val_81_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v_lower_70_);
v___x_100_ = v___x_83_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_lower_70_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
v___jp_85_:
{
uint32_t v___x_86_; uint32_t v___x_87_; uint8_t v___x_88_; 
v___x_86_ = 97;
v___x_87_ = lean_unbox_uint32(v_val_81_);
v___x_88_ = lean_uint32_dec_le(v___x_86_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; 
lean_dec(v_val_81_);
lean_dec_ref(v_lower_70_);
v___x_89_ = lean_box(0);
return v___x_89_;
}
else
{
uint32_t v___x_90_; uint32_t v___x_91_; uint8_t v___x_92_; 
v___x_90_ = 122;
v___x_91_ = lean_unbox_uint32(v_val_81_);
lean_dec(v_val_81_);
v___x_92_ = lean_uint32_dec_le(v___x_91_, v___x_90_);
v___y_72_ = v___x_92_;
goto v___jp_71_;
}
}
}
}
}
}
v___jp_71_:
{
if (v___y_72_ == 0)
{
lean_object* v___x_73_; 
lean_dec_ref(v_lower_70_);
v___x_73_ = lean_box(0);
return v___x_73_;
}
else
{
lean_object* v___x_74_; 
v___x_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_74_, 0, v_lower_70_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(lean_object* v_msg_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = ((lean_object*)(l_Std_Http_URI_instInhabitedScheme___closed__0));
v___x_105_ = lean_panic_fn_borrowed(v___x_104_, v_msg_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x21(lean_object* v_s_109_){
_start:
{
lean_object* v___x_110_; 
lean_inc_ref(v_s_109_);
v___x_110_ = l_Std_Http_URI_Scheme_ofString_x3f(v_s_109_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_111_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_112_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__1));
v___x_113_ = lean_unsigned_to_nat(84u);
v___x_114_ = lean_unsigned_to_nat(12u);
v___x_115_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_116_ = l_String_quote(v_s_109_);
v___x_117_ = lean_string_append(v___x_115_, v___x_116_);
lean_dec_ref(v___x_116_);
v___x_118_ = l_mkPanicMessageWithDecl(v___x_111_, v___x_112_, v___x_113_, v___x_114_, v___x_117_);
lean_dec_ref(v___x_117_);
v___x_119_ = l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(v___x_118_);
return v___x_119_;
}
else
{
lean_object* v_val_120_; 
lean_dec_ref(v_s_109_);
v_val_120_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_val_120_);
lean_dec_ref_known(v___x_110_, 1);
return v_val_120_;
}
}
}
uint16_t l_Std_Http_URI_Scheme_defaultPort(lean_object* v_scheme_122_){
_start:
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___x_124_ = lean_string_dec_eq(v_scheme_122_, v___x_123_);
if (v___x_124_ == 0)
{
uint16_t v___x_125_; 
v___x_125_ = 80;
return v___x_125_;
}
else
{
uint16_t v___x_126_; 
v___x_126_ = 443;
return v___x_126_;
}
}
}
LEAN_EXPORT void l_Std_Http_URI_Scheme_defaultPort_0interp(lean_interpreter_value* stack)
{
lean_object* v_scheme_122_ = stack[0].m_obj;
uint16_t v_res_127_;
v_res_127_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_122_);
stack->m_num = v_res_127_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_defaultPort___boxed(lean_object* v_scheme_128_){
_start:
{
uint16_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_128_);
lean_dec_ref(v_scheme_128_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
lean_object* l_Std_Http_URI_Scheme_ofPort(uint16_t v_port_131_){
_start:
{
uint16_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = 443;
v___x_133_ = lean_uint16_dec_eq(v_port_131_, v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; 
v___x_134_ = ((lean_object*)(l_Std_Http_URI_instInhabitedScheme___closed__0));
return v___x_134_;
}
else
{
lean_object* v___x_135_; 
v___x_135_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
return v___x_135_;
}
}
}
LEAN_EXPORT void l_Std_Http_URI_Scheme_ofPort_0interp(lean_interpreter_value* stack)
{
uint16_t v_port_131_ = stack[0].m_num;
lean_object* v_res_136_;
v_res_136_ = l_Std_Http_URI_Scheme_ofPort(v_port_131_);
stack->m_obj
 = v_res_136_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofPort___boxed(lean_object* v_port_137_){
_start:
{
uint16_t v_port_boxed_138_; lean_object* v_res_139_; 
v_port_boxed_138_ = lean_unbox(v_port_137_);
v_res_139_ = l_Std_Http_URI_Scheme_ofPort(v_port_boxed_138_);
return v_res_139_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__0(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_box(0);
v___x_141_ = l_ByteArray_empty;
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___x_140_);
return v___x_142_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default(void){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_obj_once(&l_Std_Http_URI_instInhabitedUserInfo_default___closed__0, &l_Std_Http_URI_instInhabitedUserInfo_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__0);
return v___x_143_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo(void){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Std_Http_URI_instInhabitedUserInfo_default;
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_151_) == 0)
{
lean_object* v___x_153_; 
v___x_153_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_153_;
}
else
{
lean_object* v_val_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_166_; 
v_val_154_ = lean_ctor_get(v_x_151_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v_x_151_);
if (v_isSharedCheck_166_ == 0)
{
v___x_156_ = v_x_151_;
v_isShared_157_ = v_isSharedCheck_166_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_val_154_);
lean_dec(v_x_151_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_166_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_158_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_159_ = lean_string_from_utf8_unchecked(v_val_154_);
v___x_160_ = l_String_quote(v___x_159_);
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 3);
lean_ctor_set(v___x_156_, 0, v___x_160_);
v___x_162_ = v___x_156_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_165_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_158_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = l_Repr_addAppParen(v___x_163_, v_x_152_);
return v___x_164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___boxed(lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_x_167_, v_x_168_);
lean_dec(v_x_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_URI_instReprUserInfo_repr_spec__1(lean_object* v_a_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_nat_to_int(v_a_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(12u);
v___x_186_ = lean_nat_to_int(v___x_185_);
return v___x_186_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0));
v___x_195_ = lean_string_length(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13);
v___x_197_ = lean_nat_to_int(v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg(lean_object* v_x_202_){
_start:
{
lean_object* v_username_203_; lean_object* v_password_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_239_; 
v_username_203_ = lean_ctor_get(v_x_202_, 0);
v_password_204_ = lean_ctor_get(v_x_202_, 1);
v_isSharedCheck_239_ = !lean_is_exclusive(v_x_202_);
if (v_isSharedCheck_239_ == 0)
{
v___x_206_ = v_x_202_;
v_isShared_207_ = v_isSharedCheck_239_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_password_204_);
lean_inc(v_username_203_);
lean_dec(v_x_202_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_239_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_208_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_209_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__6));
v___x_210_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_211_ = lean_string_from_utf8_unchecked(v_username_203_);
v___x_212_ = l_String_quote(v___x_211_);
v___x_213_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
if (v_isShared_207_ == 0)
{
lean_ctor_set_tag(v___x_206_, 4);
lean_ctor_set(v___x_206_, 1, v___x_213_);
lean_ctor_set(v___x_206_, 0, v___x_210_);
v___x_215_ = v___x_206_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___x_213_);
v___x_215_ = v_reuseFailAlloc_238_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_216_ = 0;
v___x_217_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set_uint8(v___x_217_, sizeof(void*)*1, v___x_216_);
v___x_218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_209_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = lean_box(1);
v___x_222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__11));
v___x_224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v___x_208_);
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_password_204_, v___x_226_);
v___x_228_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_210_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*1, v___x_216_);
v___x_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_225_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_232_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v___x_230_);
v___x_234_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_231_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*1, v___x_216_);
return v___x_237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr(lean_object* v_x_240_, lean_object* v_prec_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_x_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___boxed(lean_object* v_x_243_, lean_object* v_prec_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Http_URI_instReprUserInfo_repr(v_x_243_, v_prec_244_);
lean_dec(v_prec_244_);
return v_res_245_;
}
}
uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
if (lean_obj_tag(v_x_249_) == 0)
{
uint8_t v___x_250_; 
v___x_250_ = 1;
return v___x_250_;
}
else
{
uint8_t v___x_251_; 
v___x_251_ = 0;
return v___x_251_;
}
}
else
{
if (lean_obj_tag(v_x_249_) == 0)
{
uint8_t v___x_252_; 
v___x_252_ = 0;
return v___x_252_;
}
else
{
lean_object* v_val_253_; lean_object* v_val_254_; uint8_t v___x_255_; 
v_val_253_ = lean_ctor_get(v_x_248_, 0);
v_val_254_ = lean_ctor_get(v_x_249_, 0);
v___x_255_ = lean_sarray_dec_eq(v_val_253_, v_val_254_);
return v___x_255_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_248_ = stack[0].m_obj;
lean_object* v_x_249_ = stack[1].m_obj;
uint8_t v_res_256_;
v_res_256_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_x_248_, v_x_249_);
stack->m_num = v_res_256_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0___boxed(lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_x_257_, v_x_258_);
lean_dec(v_x_258_);
lean_dec(v_x_257_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
uint8_t l_Std_Http_URI_instBEqUserInfo_beq(lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
lean_object* v_username_263_; lean_object* v_password_264_; lean_object* v_username_265_; lean_object* v_password_266_; uint8_t v___x_267_; 
v_username_263_ = lean_ctor_get(v_x_261_, 0);
v_password_264_ = lean_ctor_get(v_x_261_, 1);
v_username_265_ = lean_ctor_get(v_x_262_, 0);
v_password_266_ = lean_ctor_get(v_x_262_, 1);
v___x_267_ = lean_sarray_dec_eq(v_username_263_, v_username_265_);
if (v___x_267_ == 0)
{
return v___x_267_;
}
else
{
uint8_t v___x_268_; 
v___x_268_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_password_264_, v_password_266_);
return v___x_268_;
}
}
}
LEAN_EXPORT void l_Std_Http_URI_instBEqUserInfo_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_261_ = stack[0].m_obj;
lean_object* v_x_262_ = stack[1].m_obj;
uint8_t v_res_269_;
v_res_269_ = l_Std_Http_URI_instBEqUserInfo_beq(v_x_261_, v_x_262_);
stack->m_num = v_res_269_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqUserInfo_beq___boxed(lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
uint8_t v_res_272_; lean_object* v_r_273_; 
v_res_272_ = l_Std_Http_URI_instBEqUserInfo_beq(v_x_270_, v_x_271_);
lean_dec_ref(v_x_271_);
lean_dec_ref(v_x_270_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings(lean_object* v_username_276_, lean_object* v_password_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_276_);
if (lean_obj_tag(v_password_277_) == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_box(0);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
return v___x_280_;
}
else
{
lean_object* v_val_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_290_; 
v_val_281_ = lean_ctor_get(v_password_277_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v_password_277_);
if (v_isSharedCheck_290_ == 0)
{
v___x_283_ = v_password_277_;
v_isShared_284_ = v_isSharedCheck_290_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_val_281_);
lean_dec(v_password_277_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_290_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_281_);
lean_dec(v_val_281_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_285_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_289_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; 
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_278_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
return v___x_288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings___boxed(lean_object* v_username_291_, lean_object* v_password_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Std_Http_URI_UserInfo_ofStrings(v_username_291_, v_password_292_);
lean_dec_ref(v_username_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f(lean_object* v_ui_294_){
_start:
{
lean_object* v_username_295_; lean_object* v___x_296_; 
v_username_295_ = lean_ctor_get(v_ui_294_, 0);
v___x_296_ = l_Std_Http_URI_EncodedUserInfo_decode(v_username_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f___boxed(lean_object* v_ui_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_Http_URI_UserInfo_username_x3f(v_ui_297_);
lean_dec_ref(v_ui_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f(lean_object* v_ui_299_){
_start:
{
lean_object* v_password_300_; 
v_password_300_ = lean_ctor_get(v_ui_299_, 1);
if (lean_obj_tag(v_password_300_) == 0)
{
lean_object* v___x_301_; 
v___x_301_ = lean_box(0);
return v___x_301_;
}
else
{
lean_object* v_val_302_; lean_object* v___x_303_; 
v_val_302_ = lean_ctor_get(v_password_300_, 0);
v___x_303_ = l_Std_Http_URI_EncodedUserInfo_decode(v_val_302_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f___boxed(lean_object* v_ui_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Std_Http_URI_UserInfo_password_x3f(v_ui_304_);
lean_dec_ref(v_ui_304_);
return v_res_305_;
}
}
uint8_t l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(lean_object* v_x_306_){
_start:
{
if (lean_obj_tag(v_x_306_) == 0)
{
uint8_t v___x_307_; 
v___x_307_ = 1;
return v___x_307_;
}
else
{
lean_object* v_head_308_; lean_object* v_tail_309_; uint32_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v_head_308_ = lean_ctor_get(v_x_306_, 0);
v_tail_309_ = lean_ctor_get(v_x_306_, 1);
v___x_331_ = lean_unbox_uint32(v_head_308_);
v___x_332_ = lean_uint32_to_nat(v___x_331_);
v___x_333_ = lean_unsigned_to_nat(128u);
v___x_334_ = lean_nat_dec_lt(v___x_332_, v___x_333_);
lean_dec(v___x_332_);
if (v___x_334_ == 0)
{
goto v___jp_310_;
}
else
{
uint32_t v___x_335_; uint32_t v___x_336_; uint8_t v___x_337_; 
v___x_335_ = 48;
v___x_336_ = lean_unbox_uint32(v_head_308_);
v___x_337_ = lean_uint32_dec_le(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
goto v___jp_323_;
}
else
{
uint32_t v___x_338_; uint32_t v___x_339_; uint8_t v___x_340_; 
v___x_338_ = 57;
v___x_339_ = lean_unbox_uint32(v_head_308_);
v___x_340_ = lean_uint32_dec_le(v___x_339_, v___x_338_);
if (v___x_340_ == 0)
{
goto v___jp_323_;
}
else
{
v_x_306_ = v_tail_309_;
goto _start;
}
}
}
v___jp_310_:
{
uint32_t v___x_311_; uint32_t v___x_312_; uint8_t v___x_313_; 
v___x_311_ = 45;
v___x_312_ = lean_unbox_uint32(v_head_308_);
v___x_313_ = lean_uint32_dec_eq(v___x_312_, v___x_311_);
if (v___x_313_ == 0)
{
return v___x_313_;
}
else
{
v_x_306_ = v_tail_309_;
goto _start;
}
}
v___jp_315_:
{
uint32_t v___x_316_; uint32_t v___x_317_; uint8_t v___x_318_; 
v___x_316_ = 97;
v___x_317_ = lean_unbox_uint32(v_head_308_);
v___x_318_ = lean_uint32_dec_le(v___x_316_, v___x_317_);
if (v___x_318_ == 0)
{
goto v___jp_310_;
}
else
{
uint32_t v___x_319_; uint32_t v___x_320_; uint8_t v___x_321_; 
v___x_319_ = 122;
v___x_320_ = lean_unbox_uint32(v_head_308_);
v___x_321_ = lean_uint32_dec_le(v___x_320_, v___x_319_);
if (v___x_321_ == 0)
{
goto v___jp_310_;
}
else
{
v_x_306_ = v_tail_309_;
goto _start;
}
}
}
v___jp_323_:
{
uint32_t v___x_324_; uint32_t v___x_325_; uint8_t v___x_326_; 
v___x_324_ = 65;
v___x_325_ = lean_unbox_uint32(v_head_308_);
v___x_326_ = lean_uint32_dec_le(v___x_324_, v___x_325_);
if (v___x_326_ == 0)
{
goto v___jp_315_;
}
else
{
uint32_t v___x_327_; uint32_t v___x_328_; uint8_t v___x_329_; 
v___x_327_ = 90;
v___x_328_ = lean_unbox_uint32(v_head_308_);
v___x_329_ = lean_uint32_dec_le(v___x_328_, v___x_327_);
if (v___x_329_ == 0)
{
goto v___jp_315_;
}
else
{
v_x_306_ = v_tail_309_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_306_ = stack[0].m_obj;
uint8_t v_res_342_;
v_res_342_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v_x_306_);
stack->m_num = v_res_342_;
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0___boxed(lean_object* v_x_343_){
_start:
{
uint8_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v_x_343_);
lean_dec(v_x_343_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object* v_s_346_){
_start:
{
uint32_t v___y_348_; uint32_t v___y_354_; lean_object* v_chars_359_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v_chars_359_ = l_String_toListImpl(v_s_346_);
v___x_376_ = l_List_lengthTR___redArg(v_chars_359_);
v___x_377_ = lean_unsigned_to_nat(63u);
v___x_378_ = lean_nat_dec_le(v___x_376_, v___x_377_);
lean_dec(v___x_376_);
if (v___x_378_ == 0)
{
lean_dec(v_chars_359_);
return v___x_378_;
}
else
{
uint8_t v___x_379_; 
v___x_379_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v_chars_359_);
if (v___x_379_ == 0)
{
lean_dec(v_chars_359_);
return v___x_379_;
}
else
{
lean_object* v___x_380_; 
v___x_380_ = l_List_head_x3f___redArg(v_chars_359_);
if (lean_obj_tag(v___x_380_) == 0)
{
uint8_t v___x_381_; 
lean_dec(v_chars_359_);
v___x_381_ = 0;
return v___x_381_;
}
else
{
lean_object* v_val_382_; uint32_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v_val_382_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_val_382_);
lean_dec_ref_known(v___x_380_, 1);
v___x_397_ = lean_unbox_uint32(v_val_382_);
v___x_398_ = lean_uint32_to_nat(v___x_397_);
v___x_399_ = lean_unsigned_to_nat(128u);
v___x_400_ = lean_nat_dec_lt(v___x_398_, v___x_399_);
lean_dec(v___x_398_);
if (v___x_400_ == 0)
{
lean_dec(v_val_382_);
lean_dec(v_chars_359_);
return v___x_400_;
}
else
{
uint32_t v___x_401_; uint32_t v___x_402_; uint8_t v___x_403_; 
v___x_401_ = 48;
v___x_402_ = lean_unbox_uint32(v_val_382_);
v___x_403_ = lean_uint32_dec_le(v___x_401_, v___x_402_);
if (v___x_403_ == 0)
{
goto v___jp_390_;
}
else
{
uint32_t v___x_404_; uint32_t v___x_405_; uint8_t v___x_406_; 
v___x_404_ = 57;
v___x_405_ = lean_unbox_uint32(v_val_382_);
v___x_406_ = lean_uint32_dec_le(v___x_405_, v___x_404_);
if (v___x_406_ == 0)
{
goto v___jp_390_;
}
else
{
lean_dec(v_val_382_);
goto v___jp_360_;
}
}
}
v___jp_383_:
{
uint32_t v___x_384_; uint32_t v___x_385_; uint8_t v___x_386_; 
v___x_384_ = 97;
v___x_385_ = lean_unbox_uint32(v_val_382_);
v___x_386_ = lean_uint32_dec_le(v___x_384_, v___x_385_);
if (v___x_386_ == 0)
{
lean_dec(v_val_382_);
lean_dec(v_chars_359_);
return v___x_386_;
}
else
{
uint32_t v___x_387_; uint32_t v___x_388_; uint8_t v___x_389_; 
v___x_387_ = 122;
v___x_388_ = lean_unbox_uint32(v_val_382_);
lean_dec(v_val_382_);
v___x_389_ = lean_uint32_dec_le(v___x_388_, v___x_387_);
if (v___x_389_ == 0)
{
lean_dec(v_chars_359_);
return v___x_389_;
}
else
{
goto v___jp_360_;
}
}
}
v___jp_390_:
{
uint32_t v___x_391_; uint32_t v___x_392_; uint8_t v___x_393_; 
v___x_391_ = 65;
v___x_392_ = lean_unbox_uint32(v_val_382_);
v___x_393_ = lean_uint32_dec_le(v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
goto v___jp_383_;
}
else
{
uint32_t v___x_394_; uint32_t v___x_395_; uint8_t v___x_396_; 
v___x_394_ = 90;
v___x_395_ = lean_unbox_uint32(v_val_382_);
v___x_396_ = lean_uint32_dec_le(v___x_395_, v___x_394_);
if (v___x_396_ == 0)
{
goto v___jp_383_;
}
else
{
lean_dec(v_val_382_);
goto v___jp_360_;
}
}
}
}
}
}
v___jp_347_:
{
uint32_t v___x_349_; uint8_t v___x_350_; 
v___x_349_ = 97;
v___x_350_ = lean_uint32_dec_le(v___x_349_, v___y_348_);
if (v___x_350_ == 0)
{
return v___x_350_;
}
else
{
uint32_t v___x_351_; uint8_t v___x_352_; 
v___x_351_ = 122;
v___x_352_ = lean_uint32_dec_le(v___y_348_, v___x_351_);
return v___x_352_;
}
}
v___jp_353_:
{
uint32_t v___x_355_; uint8_t v___x_356_; 
v___x_355_ = 65;
v___x_356_ = lean_uint32_dec_le(v___x_355_, v___y_354_);
if (v___x_356_ == 0)
{
v___y_348_ = v___y_354_;
goto v___jp_347_;
}
else
{
uint32_t v___x_357_; uint8_t v___x_358_; 
v___x_357_ = 90;
v___x_358_ = lean_uint32_dec_le(v___y_354_, v___x_357_);
if (v___x_358_ == 0)
{
v___y_348_ = v___y_354_;
goto v___jp_347_;
}
else
{
return v___x_358_;
}
}
}
v___jp_360_:
{
lean_object* v___x_361_; 
v___x_361_ = l_List_getLast_x3f___redArg(v_chars_359_);
lean_dec(v_chars_359_);
if (lean_obj_tag(v___x_361_) == 0)
{
uint8_t v___x_362_; 
v___x_362_ = 0;
return v___x_362_;
}
else
{
lean_object* v_val_363_; uint32_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v_val_363_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_val_363_);
lean_dec_ref_known(v___x_361_, 1);
v___x_364_ = lean_unbox_uint32(v_val_363_);
v___x_365_ = lean_uint32_to_nat(v___x_364_);
v___x_366_ = lean_unsigned_to_nat(128u);
v___x_367_ = lean_nat_dec_lt(v___x_365_, v___x_366_);
lean_dec(v___x_365_);
if (v___x_367_ == 0)
{
lean_dec(v_val_363_);
return v___x_367_;
}
else
{
uint32_t v___x_368_; uint32_t v___x_369_; uint8_t v___x_370_; 
v___x_368_ = 48;
v___x_369_ = lean_unbox_uint32(v_val_363_);
v___x_370_ = lean_uint32_dec_le(v___x_368_, v___x_369_);
if (v___x_370_ == 0)
{
uint32_t v___x_371_; 
v___x_371_ = lean_unbox_uint32(v_val_363_);
lean_dec(v_val_363_);
v___y_354_ = v___x_371_;
goto v___jp_353_;
}
else
{
uint32_t v___x_372_; uint32_t v___x_373_; uint8_t v___x_374_; 
v___x_372_ = 57;
v___x_373_ = lean_unbox_uint32(v_val_363_);
v___x_374_ = lean_uint32_dec_le(v___x_373_, v___x_372_);
if (v___x_374_ == 0)
{
uint32_t v___x_375_; 
v___x_375_ = lean_unbox_uint32(v_val_363_);
lean_dec(v_val_363_);
v___y_354_ = v___x_375_;
goto v___jp_353_;
}
else
{
lean_dec(v_val_363_);
return v___x_374_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_isValidDomainLabel_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_346_ = stack[0].m_obj;
uint8_t v_res_407_;
v_res_407_ = l_Std_Http_URI_isValidDomainLabel(v_s_346_);
stack->m_num = v_res_407_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidDomainLabel___boxed(lean_object* v_s_408_){
_start:
{
uint8_t v_res_409_; lean_object* v_r_410_; 
v_res_409_ = l_Std_Http_URI_isValidDomainLabel(v_s_408_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg(){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___closed__0));
return v___x_414_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_415_;
v_res_415_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg();
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___boxed(lean_object* v___dummy_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg();
return v_res_417_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg();
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(lean_object* v_s_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___boxed(lean_object* v_s_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(v_s_421_);
lean_dec_ref(v_s_421_);
return v_res_422_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(uint8_t v___x_423_, lean_object* v_lower_424_, lean_object* v___x_425_, lean_object* v___x_426_, lean_object* v_a_427_, uint8_t v_b_428_){
_start:
{
uint8_t v___y_430_; lean_object* v_it_431_; lean_object* v_startInclusive_432_; lean_object* v_endExclusive_433_; uint8_t v___y_438_; 
if (v___x_423_ == 0)
{
uint8_t v___x_464_; 
v___x_464_ = 1;
v___y_438_ = v___x_464_;
goto v___jp_437_;
}
else
{
uint8_t v___x_465_; 
v___x_465_ = 0;
v___y_438_ = v___x_465_;
goto v___jp_437_;
}
v___jp_429_:
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = lean_string_utf8_extract_fast(v_lower_424_, v_startInclusive_432_, v_endExclusive_433_);
lean_dec(v_endExclusive_433_);
lean_dec(v_startInclusive_432_);
v___x_435_ = l_Std_Http_URI_isValidDomainLabel(v___x_434_);
if (v___x_435_ == 0)
{
lean_dec(v_it_431_);
lean_dec(v___x_426_);
return v___x_435_;
}
else
{
v_a_427_ = v_it_431_;
v_b_428_ = v___y_430_;
goto _start;
}
}
v___jp_437_:
{
if (lean_obj_tag(v_a_427_) == 0)
{
lean_object* v_currPos_439_; lean_object* v_searcher_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_463_; 
v_currPos_439_ = lean_ctor_get(v_a_427_, 0);
v_searcher_440_ = lean_ctor_get(v_a_427_, 1);
v_isSharedCheck_463_ = !lean_is_exclusive(v_a_427_);
if (v_isSharedCheck_463_ == 0)
{
v___x_442_ = v_a_427_;
v_isShared_443_ = v_isSharedCheck_463_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_searcher_440_);
lean_inc(v_currPos_439_);
lean_dec(v_a_427_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_463_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
uint8_t v_decide_444_; 
v_decide_444_ = lean_nat_dec_eq(v_searcher_440_, v___x_426_);
if (v_decide_444_ == 0)
{
uint32_t v___x_445_; uint32_t v___x_446_; uint8_t v___x_447_; 
v___x_445_ = 46;
v___x_446_ = lean_string_utf8_get_fast(v_lower_424_, v_searcher_440_);
v___x_447_ = lean_uint32_dec_eq(v___x_446_, v___x_445_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = lean_string_utf8_next_fast(v_lower_424_, v_searcher_440_);
lean_dec(v_searcher_440_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 1, v___x_448_);
v___x_450_ = v___x_442_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_currPos_439_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_448_);
v___x_450_ = v_reuseFailAlloc_452_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
v_a_427_ = v___x_450_;
goto _start;
}
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v_slice_456_; lean_object* v_nextIt_458_; 
v___x_453_ = lean_string_utf8_next_fast(v_lower_424_, v_searcher_440_);
v___x_454_ = lean_nat_sub(v___x_453_, v_searcher_440_);
v___x_455_ = lean_nat_add(v_searcher_440_, v___x_454_);
lean_dec(v___x_454_);
v_slice_456_ = l_String_Slice_subslice_x21(v___x_425_, v_currPos_439_, v_searcher_440_);
lean_inc(v___x_455_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 1, v___x_455_);
lean_ctor_set(v___x_442_, 0, v___x_455_);
v_nextIt_458_ = v___x_442_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_455_);
v_nextIt_458_ = v_reuseFailAlloc_461_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v_startInclusive_459_; lean_object* v_endExclusive_460_; 
v_startInclusive_459_ = lean_ctor_get(v_slice_456_, 0);
lean_inc(v_startInclusive_459_);
v_endExclusive_460_ = lean_ctor_get(v_slice_456_, 1);
lean_inc(v_endExclusive_460_);
lean_dec_ref(v_slice_456_);
v___y_430_ = v___y_438_;
v_it_431_ = v_nextIt_458_;
v_startInclusive_432_ = v_startInclusive_459_;
v_endExclusive_433_ = v_endExclusive_460_;
goto v___jp_429_;
}
}
}
else
{
lean_object* v___x_462_; 
lean_del_object(v___x_442_);
lean_dec(v_searcher_440_);
v___x_462_ = lean_box(1);
lean_inc(v___x_426_);
v___y_430_ = v___y_438_;
v_it_431_ = v___x_462_;
v_startInclusive_432_ = v_currPos_439_;
v_endExclusive_433_ = v___x_426_;
goto v___jp_429_;
}
}
}
else
{
lean_dec(v___x_426_);
return v_b_428_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_423_ = stack[0].m_num;
lean_object* v_lower_424_ = stack[1].m_obj;
lean_object* v___x_425_ = stack[2].m_obj;
lean_object* v___x_426_ = stack[3].m_obj;
lean_object* v_a_427_ = stack[4].m_obj;
uint8_t v_b_428_ = stack[5].m_num;
uint8_t v_res_466_;
v_res_466_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_423_, v_lower_424_, v___x_425_, v___x_426_, v_a_427_, v_b_428_);
stack->m_num = v_res_466_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg___boxed(lean_object* v___x_467_, lean_object* v_lower_468_, lean_object* v___x_469_, lean_object* v___x_470_, lean_object* v_a_471_, lean_object* v_b_472_){
_start:
{
uint8_t v___x_3755__boxed_473_; uint8_t v_b_boxed_474_; uint8_t v_res_475_; lean_object* v_r_476_; 
v___x_3755__boxed_473_ = lean_unbox(v___x_467_);
v_b_boxed_474_ = lean_unbox(v_b_472_);
v_res_475_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_3755__boxed_473_, v_lower_468_, v___x_469_, v___x_470_, v_a_471_, v_b_boxed_474_);
lean_dec_ref(v___x_469_);
lean_dec_ref(v_lower_468_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(lean_object* v___x_477_, lean_object* v_lower_478_, lean_object* v___x_479_, lean_object* v_a_480_, uint8_t v_b_481_){
_start:
{
if (lean_obj_tag(v_a_480_) == 0)
{
lean_object* v_currPos_482_; lean_object* v_searcher_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_498_; 
v_currPos_482_ = lean_ctor_get(v_a_480_, 0);
v_searcher_483_ = lean_ctor_get(v_a_480_, 1);
v_isSharedCheck_498_ = !lean_is_exclusive(v_a_480_);
if (v_isSharedCheck_498_ == 0)
{
v___x_485_ = v_a_480_;
v_isShared_486_ = v_isSharedCheck_498_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_searcher_483_);
lean_inc(v_currPos_482_);
lean_dec(v_a_480_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_498_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; uint8_t v___x_488_; uint8_t v_decide_489_; 
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_nat_dec_eq(v___x_477_, v___x_487_);
v_decide_489_ = lean_nat_dec_eq(v_searcher_483_, v___x_479_);
if (v_decide_489_ == 0)
{
uint32_t v___x_490_; uint32_t v___x_491_; uint8_t v___x_492_; 
v___x_490_ = 46;
v___x_491_ = lean_string_utf8_get_fast(v_lower_478_, v_searcher_483_);
v___x_492_ = lean_uint32_dec_eq(v___x_491_, v___x_490_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_493_ = lean_string_utf8_next_fast(v_lower_478_, v_searcher_483_);
lean_dec(v_searcher_483_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v___x_493_);
v___x_495_ = v___x_485_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_currPos_482_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v___x_493_);
v___x_495_ = v_reuseFailAlloc_497_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
v_a_480_ = v___x_495_;
goto _start;
}
}
else
{
lean_del_object(v___x_485_);
lean_dec(v_searcher_483_);
lean_dec(v_currPos_482_);
return v___x_488_;
}
}
else
{
lean_del_object(v___x_485_);
lean_dec(v_searcher_483_);
lean_dec(v_currPos_482_);
return v___x_488_;
}
}
}
else
{
return v_b_481_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_477_ = stack[0].m_obj;
lean_object* v_lower_478_ = stack[1].m_obj;
lean_object* v___x_479_ = stack[2].m_obj;
lean_object* v_a_480_ = stack[3].m_obj;
uint8_t v_b_481_ = stack[4].m_num;
uint8_t v_res_499_;
v_res_499_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_477_, v_lower_478_, v___x_479_, v_a_480_, v_b_481_);
stack->m_num = v_res_499_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg___boxed(lean_object* v___x_500_, lean_object* v_lower_501_, lean_object* v___x_502_, lean_object* v_a_503_, lean_object* v_b_504_){
_start:
{
uint8_t v_b_boxed_505_; uint8_t v_res_506_; lean_object* v_r_507_; 
v_b_boxed_505_ = lean_unbox(v_b_504_);
v_res_506_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_500_, v_lower_501_, v___x_502_, v_a_503_, v_b_boxed_505_);
lean_dec(v___x_502_);
lean_dec_ref(v_lower_501_);
lean_dec(v___x_500_);
v_r_507_ = lean_box(v_res_506_);
return v_r_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_DomainName_ofString_x3f(lean_object* v_s_508_){
_start:
{
lean_object* v___x_509_; lean_object* v_lower_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_509_ = lean_unsigned_to_nat(0u);
v_lower_510_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_508_, v___x_509_);
v___x_511_ = lean_string_utf8_byte_size(v_lower_510_);
v___x_512_ = lean_nat_dec_eq(v___x_511_, v___x_509_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; uint8_t v___x_516_; uint8_t v___y_518_; 
lean_inc_ref(v_lower_510_);
v___x_513_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_513_, 0, v_lower_510_);
lean_ctor_set(v___x_513_, 1, v___x_509_);
lean_ctor_set(v___x_513_, 2, v___x_511_);
v___x_514_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0);
v___x_515_ = 1;
v___x_516_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_511_, v_lower_510_, v___x_511_, v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
v___y_518_ = v___x_515_;
goto v___jp_517_;
}
else
{
if (v___x_512_ == 0)
{
lean_object* v___x_526_; 
lean_dec_ref_known(v___x_513_, 3);
lean_dec_ref(v_lower_510_);
v___x_526_ = lean_box(0);
return v___x_526_;
}
else
{
v___y_518_ = v___x_512_;
goto v___jp_517_;
}
}
v___jp_517_:
{
uint8_t v___x_519_; 
v___x_519_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_516_, v_lower_510_, v___x_513_, v___x_511_, v___x_514_, v___y_518_);
lean_dec_ref_known(v___x_513_, 3);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
lean_dec_ref(v_lower_510_);
v___x_520_ = lean_box(0);
return v___x_520_;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_521_ = lean_string_length(v_lower_510_);
v___x_522_ = lean_unsigned_to_nat(255u);
v___x_523_ = lean_nat_dec_le(v___x_521_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; 
lean_dec_ref(v_lower_510_);
v___x_524_ = lean_box(0);
return v___x_524_;
}
else
{
lean_object* v___x_525_; 
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v_lower_510_);
return v___x_525_;
}
}
}
}
else
{
lean_object* v___x_527_; 
lean_dec_ref(v_lower_510_);
v___x_527_ = lean_box(0);
return v___x_527_;
}
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(lean_object* v___x_528_, lean_object* v_lower_529_, lean_object* v___x_530_, lean_object* v___x_531_, lean_object* v_inst_532_, lean_object* v_R_533_, lean_object* v_a_534_, uint8_t v_b_535_, lean_object* v_c_536_){
_start:
{
uint8_t v___x_537_; 
v___x_537_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_528_, v_lower_529_, v___x_531_, v_a_534_, v_b_535_);
return v___x_537_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_528_ = stack[0].m_obj;
lean_object* v_lower_529_ = stack[1].m_obj;
lean_object* v___x_530_ = stack[2].m_obj;
lean_object* v___x_531_ = stack[3].m_obj;
lean_object* v_a_534_ = stack[6].m_obj;
uint8_t v_b_535_ = stack[7].m_num;
uint8_t v_res_538_;
v_res_538_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(v___x_528_, v_lower_529_, v___x_530_, v___x_531_, lean_box(0), lean_box(0), v_a_534_, v_b_535_, lean_box(0));
stack->m_num = v_res_538_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___boxed(lean_object* v___x_539_, lean_object* v_lower_540_, lean_object* v___x_541_, lean_object* v___x_542_, lean_object* v_inst_543_, lean_object* v_R_544_, lean_object* v_a_545_, lean_object* v_b_546_, lean_object* v_c_547_){
_start:
{
uint8_t v_b_boxed_548_; uint8_t v_res_549_; lean_object* v_r_550_; 
v_b_boxed_548_ = lean_unbox(v_b_546_);
v_res_549_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(v___x_539_, v_lower_540_, v___x_541_, v___x_542_, v_inst_543_, v_R_544_, v_a_545_, v_b_boxed_548_, v_c_547_);
lean_dec(v___x_542_);
lean_dec_ref(v___x_541_);
lean_dec_ref(v_lower_540_);
lean_dec(v___x_539_);
v_r_550_ = lean_box(v_res_549_);
return v_r_550_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(uint8_t v___x_551_, lean_object* v_lower_552_, lean_object* v___x_553_, lean_object* v___x_554_, lean_object* v_inst_555_, lean_object* v_R_556_, lean_object* v_a_557_, uint8_t v_b_558_, lean_object* v_c_559_){
_start:
{
uint8_t v___x_560_; 
v___x_560_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_551_, v_lower_552_, v___x_553_, v___x_554_, v_a_557_, v_b_558_);
return v___x_560_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_551_ = stack[0].m_num;
lean_object* v_lower_552_ = stack[1].m_obj;
lean_object* v___x_553_ = stack[2].m_obj;
lean_object* v___x_554_ = stack[3].m_obj;
lean_object* v_a_557_ = stack[6].m_obj;
uint8_t v_b_558_ = stack[7].m_num;
uint8_t v_res_561_;
v_res_561_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(v___x_551_, v_lower_552_, v___x_553_, v___x_554_, lean_box(0), lean_box(0), v_a_557_, v_b_558_, lean_box(0));
stack->m_num = v_res_561_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___boxed(lean_object* v___x_562_, lean_object* v_lower_563_, lean_object* v___x_564_, lean_object* v___x_565_, lean_object* v_inst_566_, lean_object* v_R_567_, lean_object* v_a_568_, lean_object* v_b_569_, lean_object* v_c_570_){
_start:
{
uint8_t v___x_4002__boxed_571_; uint8_t v_b_boxed_572_; uint8_t v_res_573_; lean_object* v_r_574_; 
v___x_4002__boxed_571_ = lean_unbox(v___x_562_);
v_b_boxed_572_ = lean_unbox(v_b_569_);
v_res_573_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(v___x_4002__boxed_571_, v_lower_563_, v___x_564_, v___x_565_, v_inst_566_, v_R_567_, v_a_568_, v_b_boxed_572_, v_c_570_);
lean_dec_ref(v___x_564_);
lean_dec_ref(v_lower_563_);
v_r_574_ = lean_box(v_res_573_);
return v_r_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx___impl(lean_object* v_x_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = lean_obj_tag_nat(v_x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx___impl___boxed(lean_object* v_x_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Std_Http_URI_Host_ctorIdx___impl(v_x_577_);
lean_dec_ref(v_x_577_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___redArg(lean_object* v_t_579_, lean_object* v_k_580_){
_start:
{
lean_object* v_name_581_; lean_object* v___x_582_; 
v_name_581_ = lean_ctor_get(v_t_579_, 0);
lean_inc_ref(v_name_581_);
lean_dec_ref(v_t_579_);
v___x_582_ = lean_apply_1(v_k_580_, v_name_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim(lean_object* v_motive_583_, lean_object* v_ctorIdx_584_, lean_object* v_t_585_, lean_object* v_h_586_, lean_object* v_k_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_585_, v_k_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___boxed(lean_object* v_motive_589_, lean_object* v_ctorIdx_590_, lean_object* v_t_591_, lean_object* v_h_592_, lean_object* v_k_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Std_Http_URI_Host_ctorElim(v_motive_589_, v_ctorIdx_590_, v_t_591_, v_h_592_, v_k_593_);
lean_dec(v_ctorIdx_590_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim___redArg(lean_object* v_t_595_, lean_object* v_name_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_595_, v_name_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim(lean_object* v_motive_598_, lean_object* v_t_599_, lean_object* v_h_600_, lean_object* v_name_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_599_, v_name_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim___redArg(lean_object* v_t_603_, lean_object* v_ipv4_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_603_, v_ipv4_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim(lean_object* v_motive_606_, lean_object* v_t_607_, lean_object* v_h_608_, lean_object* v_ipv4_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_607_, v_ipv4_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim___redArg(lean_object* v_t_611_, lean_object* v_ipv6_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_611_, v_ipv6_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim(lean_object* v_motive_614_, lean_object* v_t_615_, lean_object* v_h_616_, lean_object* v_ipv6_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_615_, v_ipv6_617_);
return v___x_618_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default___closed__0(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
return v___x_620_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default(void){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = lean_obj_once(&l_Std_Http_URI_instInhabitedHost_default___closed__0, &l_Std_Http_URI_instInhabitedHost_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedHost_default___closed__0);
return v___x_621_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost(void){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Std_Http_URI_instInhabitedHost_default;
return v___x_622_;
}
}
uint8_t l_Std_Http_URI_instBEqHost_beq(lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
switch(lean_obj_tag(v_x_623_))
{
case 0:
{
if (lean_obj_tag(v_x_624_) == 0)
{
lean_object* v_name_625_; lean_object* v_name_626_; uint8_t v___x_627_; 
v_name_625_ = lean_ctor_get(v_x_623_, 0);
v_name_626_ = lean_ctor_get(v_x_624_, 0);
v___x_627_ = lean_string_dec_eq(v_name_625_, v_name_626_);
return v___x_627_;
}
else
{
uint8_t v___x_628_; 
v___x_628_ = 0;
return v___x_628_;
}
}
case 1:
{
if (lean_obj_tag(v_x_624_) == 1)
{
lean_object* v_ipv4_629_; lean_object* v_ipv4_630_; uint8_t v___x_631_; 
v_ipv4_629_ = lean_ctor_get(v_x_623_, 0);
v_ipv4_630_ = lean_ctor_get(v_x_624_, 0);
v___x_631_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_ipv4_629_, v_ipv4_630_);
return v___x_631_;
}
else
{
uint8_t v___x_632_; 
v___x_632_ = 0;
return v___x_632_;
}
}
default: 
{
if (lean_obj_tag(v_x_624_) == 2)
{
lean_object* v_ipv6_633_; lean_object* v_ipv6_634_; uint8_t v___x_635_; 
v_ipv6_633_ = lean_ctor_get(v_x_623_, 0);
v_ipv6_634_ = lean_ctor_get(v_x_624_, 0);
v___x_635_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_ipv6_633_, v_ipv6_634_);
return v___x_635_;
}
else
{
uint8_t v___x_636_; 
v___x_636_ = 0;
return v___x_636_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_instBEqHost_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_623_ = stack[0].m_obj;
lean_object* v_x_624_ = stack[1].m_obj;
uint8_t v_res_637_;
v_res_637_ = l_Std_Http_URI_instBEqHost_beq(v_x_623_, v_x_624_);
stack->m_num = v_res_637_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqHost_beq___boxed(lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
uint8_t v_res_640_; lean_object* v_r_641_; 
v_res_640_ = l_Std_Http_URI_instBEqHost_beq(v_x_638_, v_x_639_);
lean_dec_ref(v_x_639_);
lean_dec_ref(v_x_638_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__4(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_unsigned_to_nat(2u);
v___x_649_ = lean_nat_to_int(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__5(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_unsigned_to_nat(1u);
v___x_651_ = lean_nat_to_int(v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0(lean_object* v_x_652_, lean_object* v_prec_653_){
_start:
{
lean_object* v___y_655_; lean_object* v_ctr_656_; lean_object* v_a_657_; lean_object* v___y_669_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = lean_unsigned_to_nat(1024u);
v___x_701_ = lean_nat_dec_le(v___x_700_, v_prec_653_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
v___x_702_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_669_ = v___x_702_;
goto v___jp_668_;
}
else
{
lean_object* v___x_703_; 
v___x_703_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_669_ = v___x_703_;
goto v___jp_668_;
}
v___jp_654_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_658_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_659_ = lean_string_append(v___x_658_, v_ctr_656_);
v___x_660_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
v___x_661_ = lean_box(1);
v___x_662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v_a_657_);
lean_inc(v___y_655_);
v___x_664_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_664_, 0, v___y_655_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = 0;
v___x_666_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set_uint8(v___x_666_, sizeof(void*)*1, v___x_665_);
v___x_667_ = l_Repr_addAppParen(v___x_666_, v_prec_653_);
return v___x_667_;
}
v___jp_668_:
{
switch(lean_obj_tag(v_x_652_))
{
case 0:
{
lean_object* v_name_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_679_; 
v_name_670_ = lean_ctor_get(v_x_652_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v_x_652_);
if (v_isSharedCheck_679_ == 0)
{
v___x_672_ = v_x_652_;
v_isShared_673_ = v_isSharedCheck_679_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_name_670_);
lean_dec(v_x_652_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_679_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_674_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_675_ = l_String_quote(v_name_670_);
if (v_isShared_673_ == 0)
{
lean_ctor_set_tag(v___x_672_, 3);
lean_ctor_set(v___x_672_, 0, v___x_675_);
v___x_677_ = v___x_672_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
v___y_655_ = v___y_669_;
v_ctr_656_ = v___x_674_;
v_a_657_ = v___x_677_;
goto v___jp_654_;
}
}
}
case 1:
{
lean_object* v_ipv4_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_689_; 
v_ipv4_680_ = lean_ctor_get(v_x_652_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v_x_652_);
if (v_isSharedCheck_689_ == 0)
{
v___x_682_ = v_x_652_;
v_isShared_683_ = v_isSharedCheck_689_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_ipv4_680_);
lean_dec(v_x_652_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_689_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_684_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_685_ = lean_uv_ntop_v4(v_ipv4_680_);
lean_dec_ref(v_ipv4_680_);
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 3);
lean_ctor_set(v___x_682_, 0, v___x_685_);
v___x_687_ = v___x_682_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
v___y_655_ = v___y_669_;
v_ctr_656_ = v___x_684_;
v_a_657_ = v___x_687_;
goto v___jp_654_;
}
}
}
default: 
{
lean_object* v_ipv6_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_699_; 
v_ipv6_690_ = lean_ctor_get(v_x_652_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v_x_652_);
if (v_isSharedCheck_699_ == 0)
{
v___x_692_ = v_x_652_;
v_isShared_693_ = v_isSharedCheck_699_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_ipv6_690_);
lean_dec(v_x_652_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_699_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_694_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_695_ = lean_uv_ntop_v6(v_ipv6_690_);
lean_dec_ref(v_ipv6_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 3);
lean_ctor_set(v___x_692_, 0, v___x_695_);
v___x_697_ = v___x_692_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
v___y_655_ = v___y_669_;
v_ctr_656_ = v___x_694_;
v_a_657_ = v___x_697_;
goto v___jp_654_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0___boxed(lean_object* v_x_704_, lean_object* v_prec_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Std_Http_URI_instReprHost___lam__0(v_x_704_, v_prec_705_);
lean_dec(v_prec_705_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0(lean_object* v_x_711_){
_start:
{
switch(lean_obj_tag(v_x_711_))
{
case 0:
{
lean_object* v_name_712_; 
v_name_712_ = lean_ctor_get(v_x_711_, 0);
lean_inc_ref(v_name_712_);
return v_name_712_;
}
case 1:
{
lean_object* v_ipv4_713_; lean_object* v___x_714_; 
v_ipv4_713_ = lean_ctor_get(v_x_711_, 0);
v___x_714_ = lean_uv_ntop_v4(v_ipv4_713_);
return v___x_714_;
}
default: 
{
lean_object* v_ipv6_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_ipv6_715_ = lean_ctor_get(v_x_711_, 0);
v___x_716_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_717_ = lean_uv_ntop_v6(v_ipv6_715_);
v___x_718_ = lean_string_append(v___x_716_, v___x_717_);
lean_dec_ref(v___x_717_);
v___x_719_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_720_ = lean_string_append(v___x_718_, v___x_719_);
return v___x_720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0___boxed(lean_object* v_x_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Std_Http_URI_instToStringHost___lam__0(v_x_721_);
lean_dec_ref(v_x_721_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___impl(lean_object* v_x_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = lean_obj_tag_nat(v_x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___impl___boxed(lean_object* v_x_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_Http_URI_Port_ctorIdx___impl(v_x_727_);
lean_dec(v_x_727_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg(lean_object* v_t_729_, lean_object* v_k_730_){
_start:
{
if (lean_obj_tag(v_t_729_) == 2)
{
uint16_t v_port_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v_port_731_ = lean_ctor_get_uint16(v_t_729_, 0);
v___x_732_ = lean_box(v_port_731_);
v___x_733_ = lean_apply_1(v_k_730_, v___x_732_);
return v___x_733_;
}
else
{
return v_k_730_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg___boxed(lean_object* v_t_734_, lean_object* v_k_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_734_, v_k_735_);
lean_dec(v_t_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim(lean_object* v_motive_737_, lean_object* v_ctorIdx_738_, lean_object* v_t_739_, lean_object* v_h_740_, lean_object* v_k_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_739_, v_k_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___boxed(lean_object* v_motive_743_, lean_object* v_ctorIdx_744_, lean_object* v_t_745_, lean_object* v_h_746_, lean_object* v_k_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_Http_URI_Port_ctorElim(v_motive_743_, v_ctorIdx_744_, v_t_745_, v_h_746_, v_k_747_);
lean_dec(v_t_745_);
lean_dec(v_ctorIdx_744_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg(lean_object* v_t_749_, lean_object* v_omitted_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_749_, v_omitted_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg___boxed(lean_object* v_t_752_, lean_object* v_omitted_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Std_Http_URI_Port_omitted_elim___redArg(v_t_752_, v_omitted_753_);
lean_dec(v_t_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim(lean_object* v_motive_755_, lean_object* v_t_756_, lean_object* v_h_757_, lean_object* v_omitted_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_756_, v_omitted_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___boxed(lean_object* v_motive_760_, lean_object* v_t_761_, lean_object* v_h_762_, lean_object* v_omitted_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_Http_URI_Port_omitted_elim(v_motive_760_, v_t_761_, v_h_762_, v_omitted_763_);
lean_dec(v_t_761_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg(lean_object* v_t_765_, lean_object* v_empty_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_765_, v_empty_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg___boxed(lean_object* v_t_768_, lean_object* v_empty_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Std_Http_URI_Port_empty_elim___redArg(v_t_768_, v_empty_769_);
lean_dec(v_t_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim(lean_object* v_motive_771_, lean_object* v_t_772_, lean_object* v_h_773_, lean_object* v_empty_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_772_, v_empty_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___boxed(lean_object* v_motive_776_, lean_object* v_t_777_, lean_object* v_h_778_, lean_object* v_empty_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Std_Http_URI_Port_empty_elim(v_motive_776_, v_t_777_, v_h_778_, v_empty_779_);
lean_dec(v_t_777_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg(lean_object* v_t_781_, lean_object* v_value_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_781_, v_value_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg___boxed(lean_object* v_t_784_, lean_object* v_value_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Std_Http_URI_Port_value_elim___redArg(v_t_784_, v_value_785_);
lean_dec(v_t_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim(lean_object* v_motive_787_, lean_object* v_t_788_, lean_object* v_h_789_, lean_object* v_value_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_788_, v_value_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___boxed(lean_object* v_motive_792_, lean_object* v_t_793_, lean_object* v_h_794_, lean_object* v_value_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Std_Http_URI_Port_value_elim(v_motive_792_, v_t_793_, v_h_794_, v_value_795_);
lean_dec(v_t_793_);
return v_res_796_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort_default(void){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = lean_box(0);
return v___x_797_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort(void){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = lean_box(0);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr(lean_object* v_x_811_, lean_object* v_prec_812_){
_start:
{
lean_object* v___y_814_; lean_object* v___y_821_; 
switch(lean_obj_tag(v_x_811_))
{
case 0:
{
lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_827_ = lean_unsigned_to_nat(1024u);
v___x_828_ = lean_nat_dec_le(v___x_827_, v_prec_812_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
v___x_829_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_821_ = v___x_829_;
goto v___jp_820_;
}
else
{
lean_object* v___x_830_; 
v___x_830_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_821_ = v___x_830_;
goto v___jp_820_;
}
}
case 1:
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = lean_unsigned_to_nat(1024u);
v___x_832_ = lean_nat_dec_le(v___x_831_, v_prec_812_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; 
v___x_833_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_814_ = v___x_833_;
goto v___jp_813_;
}
else
{
lean_object* v___x_834_; 
v___x_834_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_814_ = v___x_834_;
goto v___jp_813_;
}
}
default: 
{
uint16_t v_port_835_; lean_object* v___y_837_; lean_object* v___x_847_; uint8_t v___x_848_; 
v_port_835_ = lean_ctor_get_uint16(v_x_811_, 0);
v___x_847_ = lean_unsigned_to_nat(1024u);
v___x_848_ = lean_nat_dec_le(v___x_847_, v_prec_812_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; 
v___x_849_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_837_ = v___x_849_;
goto v___jp_836_;
}
else
{
lean_object* v___x_850_; 
v___x_850_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_837_ = v___x_850_;
goto v___jp_836_;
}
v___jp_836_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_838_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__6));
v___x_839_ = lean_uint16_to_nat(v_port_835_);
v___x_840_ = l_Nat_reprFast(v___x_839_);
v___x_841_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
v___x_842_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_838_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
lean_inc(v___y_837_);
v___x_843_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_843_, 0, v___y_837_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = 0;
v___x_845_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_845_, 0, v___x_843_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*1, v___x_844_);
v___x_846_ = l_Repr_addAppParen(v___x_845_, v_prec_812_);
return v___x_846_;
}
}
}
v___jp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_815_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__1));
lean_inc(v___y_814_);
v___x_816_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_816_, 0, v___y_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = 0;
v___x_818_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*1, v___x_817_);
v___x_819_ = l_Repr_addAppParen(v___x_818_, v_prec_812_);
return v___x_819_;
}
v___jp_820_:
{
lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_822_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__3));
lean_inc(v___y_821_);
v___x_823_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_823_, 0, v___y_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = 0;
v___x_825_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set_uint8(v___x_825_, sizeof(void*)*1, v___x_824_);
v___x_826_ = l_Repr_addAppParen(v___x_825_, v_prec_812_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr___boxed(lean_object* v_x_851_, lean_object* v_prec_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Std_Http_URI_instReprPort_repr(v_x_851_, v_prec_852_);
lean_dec(v_prec_852_);
lean_dec(v_x_851_);
return v_res_853_;
}
}
uint8_t l_Std_Http_URI_instDecidableEqPort_decEq(lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
switch(lean_obj_tag(v_x_856_))
{
case 0:
{
if (lean_obj_tag(v_x_857_) == 0)
{
uint8_t v___x_858_; 
v___x_858_ = 1;
return v___x_858_;
}
else
{
uint8_t v___x_859_; 
v___x_859_ = 0;
return v___x_859_;
}
}
case 1:
{
if (lean_obj_tag(v_x_857_) == 1)
{
uint8_t v___x_860_; 
v___x_860_ = 1;
return v___x_860_;
}
else
{
uint8_t v___x_861_; 
v___x_861_ = 0;
return v___x_861_;
}
}
default: 
{
if (lean_obj_tag(v_x_857_) == 2)
{
uint16_t v_port_862_; uint16_t v_port_863_; uint8_t v___x_864_; 
v_port_862_ = lean_ctor_get_uint16(v_x_856_, 0);
v_port_863_ = lean_ctor_get_uint16(v_x_857_, 0);
v___x_864_ = lean_uint16_dec_eq(v_port_862_, v_port_863_);
return v___x_864_;
}
else
{
uint8_t v___x_865_; 
v___x_865_ = 0;
return v___x_865_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_instDecidableEqPort_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_856_ = stack[0].m_obj;
lean_object* v_x_857_ = stack[1].m_obj;
uint8_t v_res_866_;
v_res_866_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_856_, v_x_857_);
stack->m_num = v_res_866_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort_decEq___boxed(lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
uint8_t v_res_869_; lean_object* v_r_870_; 
v_res_869_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_867_, v_x_868_);
lean_dec(v_x_868_);
lean_dec(v_x_867_);
v_r_870_ = lean_box(v_res_869_);
return v_r_870_;
}
}
uint8_t l_Std_Http_URI_instDecidableEqPort(lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
uint8_t v___x_873_; 
v___x_873_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_871_, v_x_872_);
return v___x_873_;
}
}
LEAN_EXPORT void l_Std_Http_URI_instDecidableEqPort_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_871_ = stack[0].m_obj;
lean_object* v_x_872_ = stack[1].m_obj;
uint8_t v_res_874_;
v_res_874_ = l_Std_Http_URI_instDecidableEqPort(v_x_871_, v_x_872_);
stack->m_num = v_res_874_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort___boxed(lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
uint8_t v_res_877_; lean_object* v_r_878_; 
v_res_877_ = l_Std_Http_URI_instDecidableEqPort(v_x_875_, v_x_876_);
lean_dec(v_x_876_);
lean_dec(v_x_875_);
v_r_878_ = lean_box(v_res_877_);
return v_r_878_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_879_ = lean_box(0);
v___x_880_ = l_Std_Http_URI_instInhabitedHost_default;
v___x_881_ = lean_box(0);
v___x_882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v___x_880_);
lean_ctor_set(v___x_882_, 2, v___x_879_);
return v___x_882_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default(void){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = lean_obj_once(&l_Std_Http_URI_instInhabitedAuthority_default___closed__0, &l_Std_Http_URI_instInhabitedAuthority_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0);
return v___x_883_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority(void){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Std_Http_URI_instInhabitedAuthority_default;
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(lean_object* v_x_885_, lean_object* v_x_886_){
_start:
{
if (lean_obj_tag(v_x_885_) == 0)
{
lean_object* v___x_887_; 
v___x_887_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_887_;
}
else
{
lean_object* v_val_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_val_888_ = lean_ctor_get(v_x_885_, 0);
lean_inc(v_val_888_);
lean_dec_ref_known(v_x_885_, 1);
v___x_889_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_890_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_val_888_);
v___x_891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Repr_addAppParen(v___x_891_, v_x_886_);
return v___x_892_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0___boxed(lean_object* v_x_893_, lean_object* v_x_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_x_893_, v_x_894_);
lean_dec(v_x_894_);
return v_res_895_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_unsigned_to_nat(8u);
v___x_909_ = lean_nat_to_int(v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg(lean_object* v_x_913_){
_start:
{
lean_object* v_userInfo_914_; lean_object* v_host_915_; lean_object* v_port_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v_ctr_936_; lean_object* v_a_937_; 
v_userInfo_914_ = lean_ctor_get(v_x_913_, 0);
lean_inc(v_userInfo_914_);
v_host_915_ = lean_ctor_get(v_x_913_, 1);
lean_inc_ref(v_host_915_);
v_port_916_ = lean_ctor_get(v_x_913_, 2);
lean_inc(v_port_916_);
lean_dec_ref(v_x_913_);
v___x_917_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_918_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3));
v___x_919_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_userInfo_914_, v___x_920_);
v___x_922_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_919_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = 0;
v___x_924_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set_uint8(v___x_924_, sizeof(void*)*1, v___x_923_);
v___x_925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_918_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_box(1);
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v___x_917_);
v___x_933_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_934_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_915_))
{
case 0:
{
lean_object* v_name_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_974_; 
v_name_965_ = lean_ctor_get(v_host_915_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v_host_915_);
if (v_isSharedCheck_974_ == 0)
{
v___x_967_ = v_host_915_;
v_isShared_968_ = v_isSharedCheck_974_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_name_965_);
lean_dec(v_host_915_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_974_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_969_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_970_ = l_String_quote(v_name_965_);
if (v_isShared_968_ == 0)
{
lean_ctor_set_tag(v___x_967_, 3);
lean_ctor_set(v___x_967_, 0, v___x_970_);
v___x_972_ = v___x_967_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
v_ctr_936_ = v___x_969_;
v_a_937_ = v___x_972_;
goto v___jp_935_;
}
}
}
case 1:
{
lean_object* v_ipv4_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_984_; 
v_ipv4_975_ = lean_ctor_get(v_host_915_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v_host_915_);
if (v_isSharedCheck_984_ == 0)
{
v___x_977_ = v_host_915_;
v_isShared_978_ = v_isSharedCheck_984_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_ipv4_975_);
lean_dec(v_host_915_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_984_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_979_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_980_ = lean_uv_ntop_v4(v_ipv4_975_);
lean_dec_ref(v_ipv4_975_);
if (v_isShared_978_ == 0)
{
lean_ctor_set_tag(v___x_977_, 3);
lean_ctor_set(v___x_977_, 0, v___x_980_);
v___x_982_ = v___x_977_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
v_ctr_936_ = v___x_979_;
v_a_937_ = v___x_982_;
goto v___jp_935_;
}
}
}
default: 
{
lean_object* v_ipv6_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_994_; 
v_ipv6_985_ = lean_ctor_get(v_host_915_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v_host_915_);
if (v_isSharedCheck_994_ == 0)
{
v___x_987_ = v_host_915_;
v_isShared_988_ = v_isSharedCheck_994_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_ipv6_985_);
lean_dec(v_host_915_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_994_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_989_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_990_ = lean_uv_ntop_v6(v_ipv6_985_);
lean_dec_ref(v_ipv6_985_);
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 3);
lean_ctor_set(v___x_987_, 0, v___x_990_);
v___x_992_ = v___x_987_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
v_ctr_936_ = v___x_989_;
v_a_937_ = v___x_992_;
goto v___jp_935_;
}
}
}
}
v___jp_935_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_938_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_939_ = lean_string_append(v___x_938_, v_ctr_936_);
v___x_940_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
v___x_941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_928_);
v___x_942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v_a_937_);
v___x_943_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_934_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set_uint8(v___x_944_, sizeof(void*)*1, v___x_923_);
v___x_945_ = l_Repr_addAppParen(v___x_944_, v___x_920_);
v___x_946_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_933_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*1, v___x_923_);
v___x_948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_932_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_926_);
v___x_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___x_928_);
v___x_951_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set(v___x_953_, 1, v___x_917_);
v___x_954_ = l_Std_Http_URI_instReprPort_repr(v_port_916_, v___x_920_);
lean_dec(v_port_916_);
v___x_955_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_933_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set_uint8(v___x_956_, sizeof(void*)*1, v___x_923_);
v___x_957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_953_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_959_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v___x_957_);
v___x_961_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_958_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*1, v___x_923_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr(lean_object* v_x_995_, lean_object* v_prec_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_x_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___boxed(lean_object* v_x_998_, lean_object* v_prec_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Std_Http_URI_instReprAuthority_repr(v_x_998_, v_prec_999_);
lean_dec(v_prec_999_);
return v_res_1000_;
}
}
uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
if (lean_obj_tag(v_x_1003_) == 0)
{
if (lean_obj_tag(v_x_1004_) == 0)
{
uint8_t v___x_1005_; 
v___x_1005_ = 1;
return v___x_1005_;
}
else
{
uint8_t v___x_1006_; 
v___x_1006_ = 0;
return v___x_1006_;
}
}
else
{
if (lean_obj_tag(v_x_1004_) == 0)
{
uint8_t v___x_1007_; 
v___x_1007_ = 0;
return v___x_1007_;
}
else
{
lean_object* v_val_1008_; lean_object* v_val_1009_; uint8_t v___x_1010_; 
v_val_1008_ = lean_ctor_get(v_x_1003_, 0);
v_val_1009_ = lean_ctor_get(v_x_1004_, 0);
v___x_1010_ = l_Std_Http_URI_instBEqUserInfo_beq(v_val_1008_, v_val_1009_);
return v___x_1010_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1003_ = stack[0].m_obj;
lean_object* v_x_1004_ = stack[1].m_obj;
uint8_t v_res_1011_;
v_res_1011_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_x_1003_, v_x_1004_);
stack->m_num = v_res_1011_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0___boxed(lean_object* v_x_1012_, lean_object* v_x_1013_){
_start:
{
uint8_t v_res_1014_; lean_object* v_r_1015_; 
v_res_1014_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_x_1012_, v_x_1013_);
lean_dec(v_x_1013_);
lean_dec(v_x_1012_);
v_r_1015_ = lean_box(v_res_1014_);
return v_r_1015_;
}
}
uint8_t l_Std_Http_URI_instBEqAuthority_beq(lean_object* v_x_1016_, lean_object* v_x_1017_){
_start:
{
lean_object* v_userInfo_1018_; lean_object* v_host_1019_; lean_object* v_port_1020_; lean_object* v_userInfo_1021_; lean_object* v_host_1022_; lean_object* v_port_1023_; uint8_t v___x_1024_; 
v_userInfo_1018_ = lean_ctor_get(v_x_1016_, 0);
v_host_1019_ = lean_ctor_get(v_x_1016_, 1);
v_port_1020_ = lean_ctor_get(v_x_1016_, 2);
v_userInfo_1021_ = lean_ctor_get(v_x_1017_, 0);
v_host_1022_ = lean_ctor_get(v_x_1017_, 1);
v_port_1023_ = lean_ctor_get(v_x_1017_, 2);
v___x_1024_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_userInfo_1018_, v_userInfo_1021_);
if (v___x_1024_ == 0)
{
return v___x_1024_;
}
else
{
uint8_t v___x_1025_; 
v___x_1025_ = l_Std_Http_URI_instBEqHost_beq(v_host_1019_, v_host_1022_);
if (v___x_1025_ == 0)
{
return v___x_1025_;
}
else
{
uint8_t v___x_1026_; 
v___x_1026_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1020_, v_port_1023_);
return v___x_1026_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_instBEqAuthority_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1016_ = stack[0].m_obj;
lean_object* v_x_1017_ = stack[1].m_obj;
uint8_t v_res_1027_;
v_res_1027_ = l_Std_Http_URI_instBEqAuthority_beq(v_x_1016_, v_x_1017_);
stack->m_num = v_res_1027_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqAuthority_beq___boxed(lean_object* v_x_1028_, lean_object* v_x_1029_){
_start:
{
uint8_t v_res_1030_; lean_object* v_r_1031_; 
v_res_1030_ = l_Std_Http_URI_instBEqAuthority_beq(v_x_1028_, v_x_1029_);
lean_dec_ref(v_x_1029_);
lean_dec_ref(v_x_1028_);
v_r_1031_ = lean_box(v_res_1030_);
return v_r_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringAuthority___lam__0(lean_object* v_auth_1037_){
_start:
{
lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v_userInfo_1044_; lean_object* v_host_1045_; lean_object* v_port_1046_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1058_; 
v_userInfo_1044_ = lean_ctor_get(v_auth_1037_, 0);
lean_inc(v_userInfo_1044_);
v_host_1045_ = lean_ctor_get(v_auth_1037_, 1);
lean_inc_ref(v_host_1045_);
v_port_1046_ = lean_ctor_get(v_auth_1037_, 2);
lean_inc(v_port_1046_);
lean_dec_ref(v_auth_1037_);
if (lean_obj_tag(v_userInfo_1044_) == 0)
{
lean_object* v___x_1068_; 
v___x_1068_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1058_ = v___x_1068_;
goto v___jp_1057_;
}
else
{
lean_object* v_val_1069_; lean_object* v_password_1070_; 
v_val_1069_ = lean_ctor_get(v_userInfo_1044_, 0);
lean_inc(v_val_1069_);
lean_dec_ref_known(v_userInfo_1044_, 1);
v_password_1070_ = lean_ctor_get(v_val_1069_, 1);
if (lean_obj_tag(v_password_1070_) == 0)
{
lean_object* v_username_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_username_1071_ = lean_ctor_get(v_val_1069_, 0);
lean_inc_ref(v_username_1071_);
lean_dec(v_val_1069_);
v___x_1072_ = lean_string_from_utf8_unchecked(v_username_1071_);
v___x_1073_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1074_ = lean_string_append(v___x_1072_, v___x_1073_);
v___y_1058_ = v___x_1074_;
goto v___jp_1057_;
}
else
{
lean_object* v_username_1075_; lean_object* v_val_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_inc_ref(v_password_1070_);
v_username_1075_ = lean_ctor_get(v_val_1069_, 0);
lean_inc_ref(v_username_1075_);
lean_dec(v_val_1069_);
v_val_1076_ = lean_ctor_get(v_password_1070_, 0);
lean_inc(v_val_1076_);
lean_dec_ref_known(v_password_1070_, 1);
v___x_1077_ = lean_string_from_utf8_unchecked(v_username_1075_);
v___x_1078_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1079_ = lean_string_append(v___x_1077_, v___x_1078_);
v___x_1080_ = lean_string_from_utf8_unchecked(v_val_1076_);
v___x_1081_ = lean_string_append(v___x_1079_, v___x_1080_);
lean_dec_ref(v___x_1080_);
v___x_1082_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1083_ = lean_string_append(v___x_1081_, v___x_1082_);
v___y_1058_ = v___x_1083_;
goto v___jp_1057_;
}
}
v___jp_1038_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_string_append(v___y_1039_, v___y_1040_);
lean_dec_ref(v___y_1040_);
v___x_1043_ = lean_string_append(v___x_1042_, v___y_1041_);
lean_dec_ref(v___y_1041_);
return v___x_1043_;
}
v___jp_1047_:
{
switch(lean_obj_tag(v_port_1046_))
{
case 0:
{
lean_object* v___x_1050_; 
v___x_1050_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1039_ = v___y_1048_;
v___y_1040_ = v___y_1049_;
v___y_1041_ = v___x_1050_;
goto v___jp_1038_;
}
case 1:
{
lean_object* v___x_1051_; 
v___x_1051_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_1039_ = v___y_1048_;
v___y_1040_ = v___y_1049_;
v___y_1041_ = v___x_1051_;
goto v___jp_1038_;
}
default: 
{
uint16_t v_port_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_port_1052_ = lean_ctor_get_uint16(v_port_1046_, 0);
lean_dec_ref_known(v_port_1046_, 0);
v___x_1053_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1054_ = lean_uint16_to_nat(v_port_1052_);
v___x_1055_ = l_Nat_reprFast(v___x_1054_);
v___x_1056_ = lean_string_append(v___x_1053_, v___x_1055_);
lean_dec_ref(v___x_1055_);
v___y_1039_ = v___y_1048_;
v___y_1040_ = v___y_1049_;
v___y_1041_ = v___x_1056_;
goto v___jp_1038_;
}
}
}
v___jp_1057_:
{
switch(lean_obj_tag(v_host_1045_))
{
case 0:
{
lean_object* v_name_1059_; 
v_name_1059_ = lean_ctor_get(v_host_1045_, 0);
lean_inc_ref(v_name_1059_);
lean_dec_ref_known(v_host_1045_, 1);
v___y_1048_ = v___y_1058_;
v___y_1049_ = v_name_1059_;
goto v___jp_1047_;
}
case 1:
{
lean_object* v_ipv4_1060_; lean_object* v___x_1061_; 
v_ipv4_1060_ = lean_ctor_get(v_host_1045_, 0);
lean_inc_ref(v_ipv4_1060_);
lean_dec_ref_known(v_host_1045_, 1);
v___x_1061_ = lean_uv_ntop_v4(v_ipv4_1060_);
lean_dec_ref(v_ipv4_1060_);
v___y_1048_ = v___y_1058_;
v___y_1049_ = v___x_1061_;
goto v___jp_1047_;
}
default: 
{
lean_object* v_ipv6_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_ipv6_1062_ = lean_ctor_get(v_host_1045_, 0);
lean_inc_ref(v_ipv6_1062_);
lean_dec_ref_known(v_host_1045_, 1);
v___x_1063_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_1064_ = lean_uv_ntop_v6(v_ipv6_1062_);
lean_dec_ref(v_ipv6_1062_);
v___x_1065_ = lean_string_append(v___x_1063_, v___x_1064_);
lean_dec_ref(v___x_1064_);
v___x_1066_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_1067_ = lean_string_append(v___x_1065_, v___x_1066_);
v___y_1048_ = v___y_1058_;
v___y_1049_ = v___x_1067_;
goto v___jp_1047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_){
_start:
{
if (lean_obj_tag(v_x_1095_) == 0)
{
lean_dec(v_x_1093_);
return v_x_1094_;
}
else
{
lean_object* v_head_1096_; lean_object* v_tail_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1109_; 
v_head_1096_ = lean_ctor_get(v_x_1095_, 0);
v_tail_1097_ = lean_ctor_get(v_x_1095_, 1);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_x_1095_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1099_ = v_x_1095_;
v_isShared_1100_ = v_isSharedCheck_1109_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_tail_1097_);
lean_inc(v_head_1096_);
lean_dec(v_x_1095_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1109_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
lean_inc(v_x_1093_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set_tag(v___x_1099_, 5);
lean_ctor_set(v___x_1099_, 1, v_x_1093_);
lean_ctor_set(v___x_1099_, 0, v_x_1094_);
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_x_1094_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_x_1093_);
v___x_1102_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1103_ = lean_string_from_utf8_unchecked(v_head_1096_);
v___x_1104_ = l_String_quote(v___x_1103_);
v___x_1105_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
v___x_1106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1102_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v_x_1094_ = v___x_1106_;
v_x_1095_ = v_tail_1097_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(lean_object* v_x_1110_, lean_object* v_x_1111_, lean_object* v_x_1112_){
_start:
{
if (lean_obj_tag(v_x_1112_) == 0)
{
lean_dec(v_x_1110_);
return v_x_1111_;
}
else
{
lean_object* v_head_1113_; lean_object* v_tail_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1126_; 
v_head_1113_ = lean_ctor_get(v_x_1112_, 0);
v_tail_1114_ = lean_ctor_get(v_x_1112_, 1);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_x_1112_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1116_ = v_x_1112_;
v_isShared_1117_ = v_isSharedCheck_1126_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_tail_1114_);
lean_inc(v_head_1113_);
lean_dec(v_x_1112_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1126_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
lean_inc(v_x_1110_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set_tag(v___x_1116_, 5);
lean_ctor_set(v___x_1116_, 1, v_x_1110_);
lean_ctor_set(v___x_1116_, 0, v_x_1111_);
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_x_1111_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_x_1110_);
v___x_1119_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1120_ = lean_string_from_utf8_unchecked(v_head_1113_);
v___x_1121_ = l_String_quote(v___x_1120_);
v___x_1122_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
v___x_1123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1119_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(v_x_1110_, v___x_1123_, v_tail_1114_);
return v___x_1124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = lean_string_from_utf8_unchecked(v___y_1127_);
v___x_1129_ = l_String_quote(v___x_1128_);
v___x_1130_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(lean_object* v_x_1131_, lean_object* v_x_1132_){
_start:
{
if (lean_obj_tag(v_x_1131_) == 0)
{
lean_object* v___x_1133_; 
lean_dec(v_x_1132_);
v___x_1133_ = lean_box(0);
return v___x_1133_;
}
else
{
lean_object* v_tail_1134_; 
v_tail_1134_ = lean_ctor_get(v_x_1131_, 1);
if (lean_obj_tag(v_tail_1134_) == 0)
{
lean_object* v_head_1135_; lean_object* v___x_1136_; 
lean_dec(v_x_1132_);
v_head_1135_ = lean_ctor_get(v_x_1131_, 0);
lean_inc(v_head_1135_);
lean_dec_ref_known(v_x_1131_, 2);
v___x_1136_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1135_);
return v___x_1136_;
}
else
{
lean_object* v_head_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_inc(v_tail_1134_);
v_head_1137_ = lean_ctor_get(v_x_1131_, 0);
lean_inc(v_head_1137_);
lean_dec_ref_known(v_x_1131_, 2);
v___x_1138_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1137_);
v___x_1139_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(v_x_1132_, v___x_1138_, v_tail_1134_);
return v___x_1139_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0));
v___x_1145_ = lean_string_length(v___x_1144_);
return v___x_1145_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2);
v___x_1147_ = lean_nat_to_int(v___x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(lean_object* v_xs_1155_){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1156_ = lean_array_get_size(v_xs_1155_);
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = lean_nat_dec_eq(v___x_1156_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1159_ = lean_array_to_list(v_xs_1155_);
v___x_1160_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1161_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(v___x_1159_, v___x_1160_);
v___x_1162_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1163_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
lean_ctor_set(v___x_1164_, 1, v___x_1161_);
v___x_1165_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1164_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1162_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = l_Std_Format_fill(v___x_1167_);
return v___x_1168_;
}
else
{
lean_object* v___x_1169_; 
lean_dec_ref(v_xs_1155_);
v___x_1169_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1169_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___redArg(lean_object* v_x_1182_){
_start:
{
lean_object* v_segments_1183_; uint8_t v_absolute_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1216_; 
v_segments_1183_ = lean_ctor_get(v_x_1182_, 0);
v_absolute_1184_ = lean_ctor_get_uint8(v_x_1182_, sizeof(void*)*1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_x_1182_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1186_ = v_x_1182_;
v_isShared_1187_ = v_isSharedCheck_1216_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_segments_1183_);
lean_dec(v_x_1182_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1216_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; lean_object* v___x_1195_; 
v___x_1188_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1189_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__3));
v___x_1190_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_1191_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(v_segments_1183_);
v___x_1192_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = 0;
if (v_isShared_1187_ == 0)
{
lean_ctor_set_tag(v___x_1186_, 6);
lean_ctor_set(v___x_1186_, 0, v___x_1192_);
v___x_1195_ = v___x_1186_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1192_);
v___x_1195_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
lean_ctor_set_uint8(v___x_1195_, sizeof(void*)*1, v___x_1193_);
v___x_1196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1189_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = lean_box(1);
v___x_1200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__5));
v___x_1202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
lean_ctor_set(v___x_1203_, 1, v___x_1188_);
v___x_1204_ = l_Bool_repr___redArg(v_absolute_1184_);
v___x_1205_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1190_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set_uint8(v___x_1206_, sizeof(void*)*1, v___x_1193_);
v___x_1207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1203_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1209_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v___x_1207_);
v___x_1211_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1208_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*1, v___x_1193_);
return v___x_1214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr(lean_object* v_x_1217_, lean_object* v_prec_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Std_Http_URI_instReprPath_repr___redArg(v_x_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___boxed(lean_object* v_x_1220_, lean_object* v_prec_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Std_Http_URI_instReprPath_repr(v_x_1220_, v_prec_1221_);
lean_dec(v_prec_1221_);
return v_res_1222_;
}
}
uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(lean_object* v_xs_1225_, lean_object* v_ys_1226_, lean_object* v_x_1227_){
_start:
{
lean_object* v_zero_1228_; uint8_t v_isZero_1229_; 
v_zero_1228_ = lean_unsigned_to_nat(0u);
v_isZero_1229_ = lean_nat_dec_eq(v_x_1227_, v_zero_1228_);
if (v_isZero_1229_ == 1)
{
lean_dec(v_x_1227_);
return v_isZero_1229_;
}
else
{
lean_object* v_one_1230_; lean_object* v_n_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v_one_1230_ = lean_unsigned_to_nat(1u);
v_n_1231_ = lean_nat_sub(v_x_1227_, v_one_1230_);
lean_dec(v_x_1227_);
v___x_1232_ = lean_array_fget_borrowed(v_xs_1225_, v_n_1231_);
v___x_1233_ = lean_array_fget_borrowed(v_ys_1226_, v_n_1231_);
v___x_1234_ = lean_sarray_dec_eq(v___x_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_dec(v_n_1231_);
return v___x_1234_;
}
else
{
v_x_1227_ = v_n_1231_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1225_ = stack[0].m_obj;
lean_object* v_ys_1226_ = stack[1].m_obj;
lean_object* v_x_1227_ = stack[2].m_obj;
uint8_t v_res_1236_;
v_res_1236_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1225_, v_ys_1226_, v_x_1227_);
stack->m_num = v_res_1236_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg___boxed(lean_object* v_xs_1237_, lean_object* v_ys_1238_, lean_object* v_x_1239_){
_start:
{
uint8_t v_res_1240_; lean_object* v_r_1241_; 
v_res_1240_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1237_, v_ys_1238_, v_x_1239_);
lean_dec_ref(v_ys_1238_);
lean_dec_ref(v_xs_1237_);
v_r_1241_ = lean_box(v_res_1240_);
return v_r_1241_;
}
}
uint8_t l_Std_Http_URI_instBEqPath_beq(lean_object* v_x_1242_, lean_object* v_x_1243_){
_start:
{
lean_object* v_segments_1244_; uint8_t v_absolute_1245_; lean_object* v_segments_1246_; uint8_t v_absolute_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v_segments_1244_ = lean_ctor_get(v_x_1242_, 0);
v_absolute_1245_ = lean_ctor_get_uint8(v_x_1242_, sizeof(void*)*1);
v_segments_1246_ = lean_ctor_get(v_x_1243_, 0);
v_absolute_1247_ = lean_ctor_get_uint8(v_x_1243_, sizeof(void*)*1);
v___x_1248_ = lean_array_get_size(v_segments_1244_);
v___x_1249_ = lean_array_get_size(v_segments_1246_);
v___x_1250_ = lean_nat_dec_eq(v___x_1248_, v___x_1249_);
if (v___x_1250_ == 0)
{
return v___x_1250_;
}
else
{
uint8_t v___x_1251_; 
v___x_1251_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_segments_1244_, v_segments_1246_, v___x_1248_);
if (v___x_1251_ == 0)
{
return v___x_1251_;
}
else
{
if (v_absolute_1247_ == 0)
{
if (v_absolute_1245_ == 0)
{
return v___x_1251_;
}
else
{
return v_absolute_1247_;
}
}
else
{
return v_absolute_1245_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_instBEqPath_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1242_ = stack[0].m_obj;
lean_object* v_x_1243_ = stack[1].m_obj;
uint8_t v_res_1252_;
v_res_1252_ = l_Std_Http_URI_instBEqPath_beq(v_x_1242_, v_x_1243_);
stack->m_num = v_res_1252_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqPath_beq___boxed(lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
uint8_t v_res_1255_; lean_object* v_r_1256_; 
v_res_1255_ = l_Std_Http_URI_instBEqPath_beq(v_x_1253_, v_x_1254_);
lean_dec_ref(v_x_1254_);
lean_dec_ref(v_x_1253_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
}
}
uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(lean_object* v_xs_1257_, lean_object* v_ys_1258_, lean_object* v_hsz_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_){
_start:
{
uint8_t v___x_1262_; 
v___x_1262_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1257_, v_ys_1258_, v_x_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1257_ = stack[0].m_obj;
lean_object* v_ys_1258_ = stack[1].m_obj;
lean_object* v_x_1260_ = stack[3].m_obj;
uint8_t v_res_1263_;
v_res_1263_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(v_xs_1257_, v_ys_1258_, lean_box(0), v_x_1260_, lean_box(0));
stack->m_num = v_res_1263_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___boxed(lean_object* v_xs_1264_, lean_object* v_ys_1265_, lean_object* v_hsz_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_res_1269_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(v_xs_1264_, v_ys_1265_, v_hsz_1266_, v_x_1267_, v_x_1268_);
lean_dec_ref(v_ys_1265_);
lean_dec_ref(v_xs_1264_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__0(lean_object* v_x_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_string_from_utf8_unchecked(v_x_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__1(lean_object* v___f_1295_, lean_object* v_path_1296_){
_start:
{
lean_object* v_segments_1297_; uint8_t v_absolute_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; size_t v_sz_1301_; size_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v_result_1305_; 
v_segments_1297_ = lean_ctor_get(v_path_1296_, 0);
lean_inc_ref(v_segments_1297_);
v_absolute_1298_ = lean_ctor_get_uint8(v_path_1296_, sizeof(void*)*1);
lean_dec_ref(v_path_1296_);
v___x_1299_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_1300_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_1301_ = lean_array_size(v_segments_1297_);
v___x_1302_ = ((size_t)0ULL);
v___x_1303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1300_, v___f_1295_, v_sz_1301_, v___x_1302_, v_segments_1297_);
v___x_1304_ = lean_array_to_list(v___x_1303_);
v_result_1305_ = l_String_intercalate(v___x_1299_, v___x_1304_);
if (v_absolute_1298_ == 0)
{
return v_result_1305_;
}
else
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_string_append(v___x_1299_, v_result_1305_);
lean_dec_ref(v_result_1305_);
return v___x_1306_;
}
}
}
uint8_t l_Std_Http_URI_Path_isEmpty(lean_object* v_p_1311_){
_start:
{
lean_object* v_segments_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v_segments_1312_ = lean_ctor_get(v_p_1311_, 0);
v___x_1313_ = lean_array_get_size(v_segments_1312_);
v___x_1314_ = lean_unsigned_to_nat(0u);
v___x_1315_ = lean_nat_dec_eq(v___x_1313_, v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT void l_Std_Http_URI_Path_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1311_ = stack[0].m_obj;
uint8_t v_res_1316_;
v_res_1316_ = l_Std_Http_URI_Path_isEmpty(v_p_1311_);
stack->m_num = v_res_1316_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_isEmpty___boxed(lean_object* v_p_1317_){
_start:
{
uint8_t v_res_1318_; lean_object* v_r_1319_; 
v_res_1318_ = l_Std_Http_URI_Path_isEmpty(v_p_1317_);
lean_dec_ref(v_p_1317_);
v_r_1319_ = lean_box(v_res_1318_);
return v_r_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parent(lean_object* v_p_1320_){
_start:
{
lean_object* v_segments_1321_; uint8_t v_absolute_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_segments_1321_ = lean_ctor_get(v_p_1320_, 0);
v_absolute_1322_ = lean_ctor_get_uint8(v_p_1320_, sizeof(void*)*1);
v___x_1323_ = lean_array_get_size(v_segments_1321_);
v___x_1324_ = lean_unsigned_to_nat(0u);
v___x_1325_ = lean_nat_dec_eq(v___x_1323_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1333_; 
lean_inc_ref(v_segments_1321_);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_p_1320_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; 
v_unused_1334_ = lean_ctor_get(v_p_1320_, 0);
lean_dec(v_unused_1334_);
v___x_1327_ = v_p_1320_;
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
else
{
lean_dec(v_p_1320_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = lean_array_pop(v_segments_1321_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1329_);
v___x_1331_ = v___x_1327_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1332_, sizeof(void*)*1, v_absolute_1322_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
else
{
return v_p_1320_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join(lean_object* v_p1_1335_, lean_object* v_p2_1336_){
_start:
{
uint8_t v_absolute_1337_; 
v_absolute_1337_ = lean_ctor_get_uint8(v_p2_1336_, sizeof(void*)*1);
if (v_absolute_1337_ == 0)
{
lean_object* v_segments_1338_; lean_object* v_segments_1339_; uint8_t v_absolute_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1348_; 
v_segments_1338_ = lean_ctor_get(v_p2_1336_, 0);
v_segments_1339_ = lean_ctor_get(v_p1_1335_, 0);
v_absolute_1340_ = lean_ctor_get_uint8(v_p1_1335_, sizeof(void*)*1);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_p1_1335_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1342_ = v_p1_1335_;
v_isShared_1343_ = v_isSharedCheck_1348_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_segments_1339_);
lean_dec(v_p1_1335_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1348_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1344_ = l_Array_append___redArg(v_segments_1339_, v_segments_1338_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1344_);
v___x_1346_ = v___x_1342_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
lean_ctor_set_uint8(v_reuseFailAlloc_1347_, sizeof(void*)*1, v_absolute_1340_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
else
{
lean_dec_ref(v_p1_1335_);
lean_inc_ref(v_p2_1336_);
return v_p2_1336_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join___boxed(lean_object* v_p1_1349_, lean_object* v_p2_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Std_Http_URI_Path_join(v_p1_1349_, v_p2_1350_);
lean_dec_ref(v_p2_1350_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append(lean_object* v_p_1352_, lean_object* v_segment_1353_){
_start:
{
lean_object* v_segments_1354_; uint8_t v_absolute_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1364_; 
v_segments_1354_ = lean_ctor_get(v_p_1352_, 0);
v_absolute_1355_ = lean_ctor_get_uint8(v_p_1352_, sizeof(void*)*1);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_p_1352_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1357_ = v_p_1352_;
v_isShared_1358_ = v_isSharedCheck_1364_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_segments_1354_);
lean_dec(v_p_1352_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1364_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1359_ = l_Std_Http_URI_EncodedSegment_encode(v_segment_1353_);
v___x_1360_ = lean_array_push(v_segments_1354_, v___x_1359_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1360_);
v___x_1362_ = v___x_1357_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1360_);
lean_ctor_set_uint8(v_reuseFailAlloc_1363_, sizeof(void*)*1, v_absolute_1355_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append___boxed(lean_object* v_p_1365_, lean_object* v_segment_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Std_Http_URI_Path_append(v_p_1365_, v_segment_1366_);
lean_dec_ref(v_segment_1366_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_appendEncoded(lean_object* v_p_1368_, lean_object* v_segment_1369_){
_start:
{
lean_object* v_segments_1370_; uint8_t v_absolute_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1379_; 
v_segments_1370_ = lean_ctor_get(v_p_1368_, 0);
v_absolute_1371_ = lean_ctor_get_uint8(v_p_1368_, sizeof(void*)*1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_p_1368_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1373_ = v_p_1368_;
v_isShared_1374_ = v_isSharedCheck_1379_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_segments_1370_);
lean_dec(v_p_1368_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1379_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1375_ = lean_array_push(v_segments_1370_, v_segment_1369_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1375_);
v___x_1377_ = v___x_1373_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
lean_ctor_set_uint8(v_reuseFailAlloc_1378_, sizeof(void*)*1, v_absolute_1371_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(lean_object* v_input_1382_, lean_object* v_output_1383_){
_start:
{
if (lean_obj_tag(v_input_1382_) == 0)
{
lean_object* v___x_1384_; 
v___x_1384_ = l_List_reverse___redArg(v_output_1383_);
return v___x_1384_;
}
else
{
lean_object* v_head_1385_; lean_object* v_tail_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1403_; 
v_head_1385_ = lean_ctor_get(v_input_1382_, 0);
v_tail_1386_ = lean_ctor_get(v_input_1382_, 1);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_input_1382_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1388_ = v_input_1382_;
v_isShared_1389_ = v_isSharedCheck_1403_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_tail_1386_);
lean_inc(v_head_1385_);
lean_dec(v_input_1382_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1403_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
lean_inc(v_head_1385_);
v___x_1390_ = lean_string_from_utf8_unchecked(v_head_1385_);
v___x_1391_ = ((lean_object*)(l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0));
v___x_1392_ = lean_string_dec_eq(v___x_1390_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = ((lean_object*)(l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1));
v___x_1394_ = lean_string_dec_eq(v___x_1390_, v___x_1393_);
lean_dec_ref(v___x_1390_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1396_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 1, v_output_1383_);
v___x_1396_ = v___x_1388_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_head_1385_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_output_1383_);
v___x_1396_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
v_input_1382_ = v_tail_1386_;
v_output_1383_ = v___x_1396_;
goto _start;
}
}
else
{
lean_del_object(v___x_1388_);
lean_dec(v_head_1385_);
if (lean_obj_tag(v_output_1383_) == 0)
{
v_input_1382_ = v_tail_1386_;
goto _start;
}
else
{
lean_object* v_tail_1400_; 
v_tail_1400_ = lean_ctor_get(v_output_1383_, 1);
lean_inc(v_tail_1400_);
lean_dec_ref_known(v_output_1383_, 2);
v_input_1382_ = v_tail_1386_;
v_output_1383_ = v_tail_1400_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_1390_);
lean_del_object(v___x_1388_);
lean_dec(v_head_1385_);
v_input_1382_ = v_tail_1386_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_normalize(lean_object* v_p_1404_){
_start:
{
lean_object* v_segments_1405_; uint8_t v_absolute_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1417_; 
v_segments_1405_ = lean_ctor_get(v_p_1404_, 0);
v_absolute_1406_ = lean_ctor_get_uint8(v_p_1404_, sizeof(void*)*1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_p_1404_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1408_ = v_p_1404_;
v_isShared_1409_ = v_isSharedCheck_1417_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_segments_1405_);
lean_dec(v_p_1404_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1417_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1410_ = lean_array_to_list(v_segments_1405_);
v___x_1411_ = lean_box(0);
v___x_1412_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(v___x_1410_, v___x_1411_);
v___x_1413_ = lean_array_mk(v___x_1412_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1413_);
v___x_1415_ = v___x_1408_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
lean_ctor_set_uint8(v_reuseFailAlloc_1416_, sizeof(void*)*1, v_absolute_1406_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(size_t v_sz_1418_, size_t v_i_1419_, lean_object* v_bs_1420_){
_start:
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_usize_dec_lt(v_i_1419_, v_sz_1418_);
if (v___x_1421_ == 0)
{
return v_bs_1420_;
}
else
{
lean_object* v_v_1422_; lean_object* v___x_1423_; lean_object* v_bs_x27_1424_; lean_object* v___y_1426_; lean_object* v___x_1431_; 
v_v_1422_ = lean_array_uget(v_bs_1420_, v_i_1419_);
v___x_1423_ = lean_unsigned_to_nat(0u);
v_bs_x27_1424_ = lean_array_uset(v_bs_1420_, v_i_1419_, v___x_1423_);
v___x_1431_ = l_Std_Http_URI_EncodedSegment_decode(v_v_1422_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_string_from_utf8_unchecked(v_v_1422_);
v___y_1426_ = v___x_1432_;
goto v___jp_1425_;
}
else
{
lean_object* v_val_1433_; 
lean_dec(v_v_1422_);
v_val_1433_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_val_1433_);
lean_dec_ref_known(v___x_1431_, 1);
v___y_1426_ = v_val_1433_;
goto v___jp_1425_;
}
v___jp_1425_:
{
size_t v___x_1427_; size_t v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = ((size_t)1ULL);
v___x_1428_ = lean_usize_add(v_i_1419_, v___x_1427_);
v___x_1429_ = lean_array_uset(v_bs_x27_1424_, v_i_1419_, v___y_1426_);
v_i_1419_ = v___x_1428_;
v_bs_1420_ = v___x_1429_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1418_ = stack[0].m_num;
size_t v_i_1419_ = stack[1].m_num;
lean_object* v_bs_1420_ = stack[2].m_obj;
lean_object* v_res_1434_;
v_res_1434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_1418_, v_i_1419_, v_bs_1420_);
stack->m_obj
 = v_res_1434_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0___boxed(lean_object* v_sz_1435_, lean_object* v_i_1436_, lean_object* v_bs_1437_){
_start:
{
size_t v_sz_boxed_1438_; size_t v_i_boxed_1439_; lean_object* v_res_1440_; 
v_sz_boxed_1438_ = lean_unbox_usize(v_sz_1435_);
lean_dec(v_sz_1435_);
v_i_boxed_1439_ = lean_unbox_usize(v_i_1436_);
lean_dec(v_i_1436_);
v_res_1440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_boxed_1438_, v_i_boxed_1439_, v_bs_1437_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_toDecodedSegments(lean_object* v_p_1441_){
_start:
{
lean_object* v_segments_1442_; size_t v_sz_1443_; size_t v___x_1444_; lean_object* v___x_1445_; 
v_segments_1442_ = lean_ctor_get(v_p_1441_, 0);
lean_inc_ref(v_segments_1442_);
lean_dec_ref(v_p_1441_);
v_sz_1443_ = lean_array_size(v_segments_1442_);
v___x_1444_ = ((size_t)0ULL);
v___x_1445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_1443_, v___x_1444_, v_segments_1442_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___redArg(lean_object* v_xs_1454_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1456_ = l_Array_repr___redArg(v___x_1455_, v_xs_1454_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1(lean_object* v_xs_1457_, lean_object* v_x_1458_){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1460_ = l_Array_repr___redArg(v___x_1459_, v_xs_1457_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___boxed(lean_object* v_xs_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Std_Http_URI_instReprQuery___aux__1(v_xs_1461_, v_x_1462_);
lean_dec(v_x_1462_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_){
_start:
{
if (lean_obj_tag(v_x_1466_) == 0)
{
lean_dec(v_x_1464_);
return v_x_1465_;
}
else
{
lean_object* v_head_1467_; lean_object* v_tail_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1477_; 
v_head_1467_ = lean_ctor_get(v_x_1466_, 0);
v_tail_1468_ = lean_ctor_get(v_x_1466_, 1);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_x_1466_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1470_ = v_x_1466_;
v_isShared_1471_ = v_isSharedCheck_1477_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_tail_1468_);
lean_inc(v_head_1467_);
lean_dec(v_x_1466_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1477_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
lean_inc(v_x_1464_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set_tag(v___x_1470_, 5);
lean_ctor_set(v___x_1470_, 1, v_x_1464_);
lean_ctor_set(v___x_1470_, 0, v_x_1465_);
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_x_1465_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_x_1464_);
v___x_1473_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
lean_ctor_set(v___x_1474_, 1, v_head_1467_);
v_x_1465_ = v___x_1474_;
v_x_1466_ = v_tail_1468_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(lean_object* v_x_1478_, lean_object* v_x_1479_){
_start:
{
if (lean_obj_tag(v_x_1478_) == 0)
{
lean_object* v___x_1480_; 
lean_dec(v_x_1479_);
v___x_1480_ = lean_box(0);
return v___x_1480_;
}
else
{
lean_object* v_tail_1481_; 
v_tail_1481_ = lean_ctor_get(v_x_1478_, 1);
if (lean_obj_tag(v_tail_1481_) == 0)
{
lean_object* v_head_1482_; 
lean_dec(v_x_1479_);
v_head_1482_ = lean_ctor_get(v_x_1478_, 0);
lean_inc(v_head_1482_);
lean_dec_ref_known(v_x_1478_, 2);
return v_head_1482_;
}
else
{
lean_object* v_head_1483_; lean_object* v___x_1484_; 
lean_inc(v_tail_1481_);
v_head_1483_ = lean_ctor_get(v_x_1478_, 0);
lean_inc(v_head_1483_);
lean_dec_ref_known(v_x_1478_, 2);
v___x_1484_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(v_x_1479_, v_head_1483_, v_tail_1481_);
return v___x_1484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(lean_object* v_x_1485_, lean_object* v_x_1486_){
_start:
{
if (lean_obj_tag(v_x_1485_) == 0)
{
lean_object* v___x_1487_; 
v___x_1487_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1487_;
}
else
{
lean_object* v_val_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1500_; 
v_val_1488_ = lean_ctor_get(v_x_1485_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_x_1485_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1490_ = v_x_1485_;
v_isShared_1491_ = v_isSharedCheck_1500_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_val_1488_);
lean_dec(v_x_1485_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1500_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1492_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1493_ = lean_string_from_utf8_unchecked(v_val_1488_);
v___x_1494_ = l_String_quote(v___x_1493_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set_tag(v___x_1490_, 3);
lean_ctor_set(v___x_1490_, 0, v___x_1494_);
v___x_1496_ = v___x_1490_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1492_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = l_Repr_addAppParen(v___x_1497_, v_x_1486_);
return v___x_1498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1501_, lean_object* v_x_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_x_1501_, v_x_1502_);
lean_dec(v_x_1502_);
return v_res_1503_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0));
v___x_1507_ = lean_string_length(v___x_1506_);
return v___x_1507_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2);
v___x_1509_ = lean_nat_to_int(v___x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(lean_object* v_x_1514_){
_start:
{
lean_object* v_fst_1515_; lean_object* v_snd_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1541_; 
v_fst_1515_ = lean_ctor_get(v_x_1514_, 0);
v_snd_1516_ = lean_ctor_get(v_x_1514_, 1);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_x_1514_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1518_ = v_x_1514_;
v_isShared_1519_ = v_isSharedCheck_1541_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_snd_1516_);
lean_inc(v_fst_1515_);
lean_dec(v_x_1514_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1541_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1520_ = lean_string_from_utf8_unchecked(v_fst_1515_);
v___x_1521_ = l_String_quote(v___x_1520_);
v___x_1522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
v___x_1523_ = lean_box(0);
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 1);
lean_ctor_set(v___x_1518_, 1, v___x_1523_);
lean_ctor_set(v___x_1518_, 0, v___x_1522_);
v___x_1525_ = v___x_1518_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; lean_object* v___x_1539_; 
v___x_1526_ = lean_unsigned_to_nat(0u);
v___x_1527_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_snd_1516_, v___x_1526_);
v___x_1528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
lean_ctor_set(v___x_1528_, 1, v___x_1525_);
v___x_1529_ = l_List_reverse___redArg(v___x_1528_);
v___x_1530_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1531_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(v___x_1529_, v___x_1530_);
v___x_1532_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3);
v___x_1533_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4));
v___x_1534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v___x_1531_);
v___x_1535_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5));
v___x_1536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1532_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = 0;
v___x_1539_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*1, v___x_1538_);
return v___x_1539_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(lean_object* v_x_1542_, lean_object* v_x_1543_, lean_object* v_x_1544_){
_start:
{
if (lean_obj_tag(v_x_1544_) == 0)
{
lean_dec(v_x_1542_);
return v_x_1543_;
}
else
{
lean_object* v_head_1545_; lean_object* v_tail_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1556_; 
v_head_1545_ = lean_ctor_get(v_x_1544_, 0);
v_tail_1546_ = lean_ctor_get(v_x_1544_, 1);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_x_1544_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1548_ = v_x_1544_;
v_isShared_1549_ = v_isSharedCheck_1556_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_tail_1546_);
lean_inc(v_head_1545_);
lean_dec(v_x_1544_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1556_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
lean_inc(v_x_1542_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set_tag(v___x_1548_, 5);
lean_ctor_set(v___x_1548_, 1, v_x_1542_);
lean_ctor_set(v___x_1548_, 0, v_x_1543_);
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_x_1543_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_x_1542_);
v___x_1551_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1545_);
v___x_1553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v_x_1543_ = v___x_1553_;
v_x_1544_ = v_tail_1546_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(lean_object* v_x_1557_, lean_object* v_x_1558_, lean_object* v_x_1559_){
_start:
{
if (lean_obj_tag(v_x_1559_) == 0)
{
lean_dec(v_x_1557_);
return v_x_1558_;
}
else
{
lean_object* v_head_1560_; lean_object* v_tail_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1571_; 
v_head_1560_ = lean_ctor_get(v_x_1559_, 0);
v_tail_1561_ = lean_ctor_get(v_x_1559_, 1);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_x_1559_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1563_ = v_x_1559_;
v_isShared_1564_ = v_isSharedCheck_1571_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_tail_1561_);
lean_inc(v_head_1560_);
lean_dec(v_x_1559_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1571_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
lean_inc(v_x_1557_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set_tag(v___x_1563_, 5);
lean_ctor_set(v___x_1563_, 1, v_x_1557_);
lean_ctor_set(v___x_1563_, 0, v_x_1558_);
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_x_1558_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_x_1557_);
v___x_1566_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1560_);
v___x_1568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(v_x_1557_, v___x_1568_, v_tail_1561_);
return v___x_1569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(lean_object* v_x_1572_, lean_object* v_x_1573_){
_start:
{
if (lean_obj_tag(v_x_1572_) == 0)
{
lean_object* v___x_1574_; 
lean_dec(v_x_1573_);
v___x_1574_ = lean_box(0);
return v___x_1574_;
}
else
{
lean_object* v_tail_1575_; 
v_tail_1575_ = lean_ctor_get(v_x_1572_, 1);
if (lean_obj_tag(v_tail_1575_) == 0)
{
lean_object* v_head_1576_; lean_object* v___x_1577_; 
lean_dec(v_x_1573_);
v_head_1576_ = lean_ctor_get(v_x_1572_, 0);
lean_inc(v_head_1576_);
lean_dec_ref_known(v_x_1572_, 2);
v___x_1577_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1576_);
return v___x_1577_;
}
else
{
lean_object* v_head_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_inc(v_tail_1575_);
v_head_1578_ = lean_ctor_get(v_x_1572_, 0);
lean_inc(v_head_1578_);
lean_dec_ref_known(v_x_1572_, 2);
v___x_1579_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1578_);
v___x_1580_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(v_x_1573_, v___x_1579_, v_tail_1575_);
return v___x_1580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(lean_object* v_xs_1581_){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1582_ = lean_array_get_size(v_xs_1581_);
v___x_1583_ = lean_unsigned_to_nat(0u);
v___x_1584_ = lean_nat_dec_eq(v___x_1582_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1585_ = lean_array_to_list(v_xs_1581_);
v___x_1586_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1587_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(v___x_1585_, v___x_1586_);
v___x_1588_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1589_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
lean_ctor_set(v___x_1590_, 1, v___x_1587_);
v___x_1591_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1588_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = l_Std_Format_fill(v___x_1593_);
return v___x_1594_;
}
else
{
lean_object* v___x_1595_; 
lean_dec_ref(v_xs_1581_);
v___x_1595_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0(lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v___y_1596_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0___boxed(lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Std_Http_URI_instReprQuery___lam__0(v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_x_1604_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___boxed(lean_object* v_x_1607_, lean_object* v_x_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(v_x_1607_, v_x_1608_);
lean_dec(v_x_1608_);
return v_res_1609_;
}
}
uint8_t l_Std_Http_URI_instBEqQuery___aux__1___lam__0(lean_object* v___f_1614_, lean_object* v_x_1615_, lean_object* v_x_1616_){
_start:
{
lean_object* v_fst_1617_; lean_object* v_snd_1618_; lean_object* v_fst_1619_; lean_object* v_snd_1620_; uint8_t v___x_1621_; 
v_fst_1617_ = lean_ctor_get(v_x_1615_, 0);
lean_inc(v_fst_1617_);
v_snd_1618_ = lean_ctor_get(v_x_1615_, 1);
lean_inc(v_snd_1618_);
lean_dec_ref(v_x_1615_);
v_fst_1619_ = lean_ctor_get(v_x_1616_, 0);
lean_inc(v_fst_1619_);
v_snd_1620_ = lean_ctor_get(v_x_1616_, 1);
lean_inc(v_snd_1620_);
lean_dec_ref(v_x_1616_);
v___x_1621_ = lean_sarray_dec_eq(v_fst_1617_, v_fst_1619_);
lean_dec(v_fst_1619_);
lean_dec(v_fst_1617_);
if (v___x_1621_ == 0)
{
lean_dec(v_snd_1620_);
lean_dec(v_snd_1618_);
lean_dec_ref(v___f_1614_);
return v___x_1621_;
}
else
{
uint8_t v___x_1622_; 
v___x_1622_ = l_instBEqOption_beq___redArg(v___f_1614_, v_snd_1618_, v_snd_1620_);
return v___x_1622_;
}
}
}
LEAN_EXPORT void l_Std_Http_URI_instBEqQuery___aux__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1614_ = stack[0].m_obj;
lean_object* v_x_1615_ = stack[1].m_obj;
lean_object* v_x_1616_ = stack[2].m_obj;
uint8_t v_res_1623_;
v_res_1623_ = l_Std_Http_URI_instBEqQuery___aux__1___lam__0(v___f_1614_, v_x_1615_, v_x_1616_);
stack->m_num = v_res_1623_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___lam__0___boxed(lean_object* v___f_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_){
_start:
{
uint8_t v_res_1627_; lean_object* v_r_1628_; 
v_res_1627_ = l_Std_Http_URI_instBEqQuery___aux__1___lam__0(v___f_1624_, v_x_1625_, v_x_1626_);
v_r_1628_ = lean_box(v_res_1627_);
return v_r_1628_;
}
}
uint8_t l_Std_Http_URI_instBEqQuery___aux__1(lean_object* v_xs_1632_, lean_object* v_ys_1633_){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1634_ = lean_array_get_size(v_xs_1632_);
v___x_1635_ = lean_array_get_size(v_ys_1633_);
v___x_1636_ = lean_nat_dec_eq(v___x_1634_, v___x_1635_);
if (v___x_1636_ == 0)
{
return v___x_1636_;
}
else
{
lean_object* v___f_1637_; uint8_t v___x_1638_; 
v___f_1637_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__1));
v___x_1638_ = l_Array_isEqvAux___redArg(v_xs_1632_, v_ys_1633_, v___f_1637_, v___x_1634_);
return v___x_1638_;
}
}
}
LEAN_EXPORT void l_Std_Http_URI_instBEqQuery___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1632_ = stack[0].m_obj;
lean_object* v_ys_1633_ = stack[1].m_obj;
uint8_t v_res_1639_;
v_res_1639_ = l_Std_Http_URI_instBEqQuery___aux__1(v_xs_1632_, v_ys_1633_);
stack->m_num = v_res_1639_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___boxed(lean_object* v_xs_1640_, lean_object* v_ys_1641_){
_start:
{
uint8_t v_res_1642_; lean_object* v_r_1643_; 
v_res_1642_ = l_Std_Http_URI_instBEqQuery___aux__1(v_xs_1640_, v_ys_1641_);
lean_dec_ref(v_ys_1641_);
lean_dec_ref(v_xs_1640_);
v_r_1643_ = lean_box(v_res_1642_);
return v_r_1643_;
}
}
uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(lean_object* v_x_1644_, lean_object* v_x_1645_){
_start:
{
if (lean_obj_tag(v_x_1644_) == 0)
{
if (lean_obj_tag(v_x_1645_) == 0)
{
uint8_t v___x_1646_; 
v___x_1646_ = 1;
return v___x_1646_;
}
else
{
uint8_t v___x_1647_; 
v___x_1647_ = 0;
return v___x_1647_;
}
}
else
{
if (lean_obj_tag(v_x_1645_) == 0)
{
uint8_t v___x_1648_; 
v___x_1648_ = 0;
return v___x_1648_;
}
else
{
lean_object* v_val_1649_; lean_object* v_val_1650_; uint8_t v___x_1651_; 
v_val_1649_ = lean_ctor_get(v_x_1644_, 0);
v_val_1650_ = lean_ctor_get(v_x_1645_, 0);
v___x_1651_ = lean_sarray_dec_eq(v_val_1649_, v_val_1650_);
return v___x_1651_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1644_ = stack[0].m_obj;
lean_object* v_x_1645_ = stack[1].m_obj;
uint8_t v_res_1652_;
v_res_1652_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_x_1644_, v_x_1645_);
stack->m_num = v_res_1652_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0___boxed(lean_object* v_x_1653_, lean_object* v_x_1654_){
_start:
{
uint8_t v_res_1655_; lean_object* v_r_1656_; 
v_res_1655_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_x_1653_, v_x_1654_);
lean_dec(v_x_1654_);
lean_dec(v_x_1653_);
v_r_1656_ = lean_box(v_res_1655_);
return v_r_1656_;
}
}
uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(lean_object* v_xs_1657_, lean_object* v_ys_1658_, lean_object* v_x_1659_){
_start:
{
lean_object* v_zero_1660_; uint8_t v_isZero_1661_; 
v_zero_1660_ = lean_unsigned_to_nat(0u);
v_isZero_1661_ = lean_nat_dec_eq(v_x_1659_, v_zero_1660_);
if (v_isZero_1661_ == 1)
{
lean_dec(v_x_1659_);
return v_isZero_1661_;
}
else
{
lean_object* v_one_1662_; lean_object* v_n_1663_; lean_object* v___x_1664_; lean_object* v_fst_1665_; lean_object* v_snd_1666_; lean_object* v___x_1667_; lean_object* v_fst_1668_; lean_object* v_snd_1669_; uint8_t v___x_1670_; 
v_one_1662_ = lean_unsigned_to_nat(1u);
v_n_1663_ = lean_nat_sub(v_x_1659_, v_one_1662_);
lean_dec(v_x_1659_);
v___x_1664_ = lean_array_fget_borrowed(v_xs_1657_, v_n_1663_);
v_fst_1665_ = lean_ctor_get(v___x_1664_, 0);
v_snd_1666_ = lean_ctor_get(v___x_1664_, 1);
v___x_1667_ = lean_array_fget_borrowed(v_ys_1658_, v_n_1663_);
v_fst_1668_ = lean_ctor_get(v___x_1667_, 0);
v_snd_1669_ = lean_ctor_get(v___x_1667_, 1);
v___x_1670_ = lean_sarray_dec_eq(v_fst_1665_, v_fst_1668_);
if (v___x_1670_ == 0)
{
lean_dec(v_n_1663_);
return v___x_1670_;
}
else
{
uint8_t v___x_1671_; 
v___x_1671_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_snd_1666_, v_snd_1669_);
if (v___x_1671_ == 0)
{
lean_dec(v_n_1663_);
return v___x_1671_;
}
else
{
v_x_1659_ = v_n_1663_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1657_ = stack[0].m_obj;
lean_object* v_ys_1658_ = stack[1].m_obj;
lean_object* v_x_1659_ = stack[2].m_obj;
uint8_t v_res_1673_;
v_res_1673_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1657_, v_ys_1658_, v_x_1659_);
stack->m_num = v_res_1673_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg___boxed(lean_object* v_xs_1674_, lean_object* v_ys_1675_, lean_object* v_x_1676_){
_start:
{
uint8_t v_res_1677_; lean_object* v_r_1678_; 
v_res_1677_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1674_, v_ys_1675_, v_x_1676_);
lean_dec_ref(v_ys_1675_);
lean_dec_ref(v_xs_1674_);
v_r_1678_ = lean_box(v_res_1677_);
return v_r_1678_;
}
}
uint8_t l_Std_Http_URI_instBEqQuery___lam__0(lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1681_ = lean_array_get_size(v___y_1679_);
v___x_1682_ = lean_array_get_size(v___y_1680_);
v___x_1683_ = lean_nat_dec_eq(v___x_1681_, v___x_1682_);
if (v___x_1683_ == 0)
{
return v___x_1683_;
}
else
{
uint8_t v___x_1684_; 
v___x_1684_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v___y_1679_, v___y_1680_, v___x_1681_);
return v___x_1684_;
}
}
}
LEAN_EXPORT void l_Std_Http_URI_instBEqQuery___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1679_ = stack[0].m_obj;
lean_object* v___y_1680_ = stack[1].m_obj;
uint8_t v_res_1685_;
v_res_1685_ = l_Std_Http_URI_instBEqQuery___lam__0(v___y_1679_, v___y_1680_);
stack->m_num = v_res_1685_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___lam__0___boxed(lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
uint8_t v_res_1688_; lean_object* v_r_1689_; 
v_res_1688_ = l_Std_Http_URI_instBEqQuery___lam__0(v___y_1686_, v___y_1687_);
lean_dec_ref(v___y_1687_);
lean_dec_ref(v___y_1686_);
v_r_1689_ = lean_box(v_res_1688_);
return v_r_1689_;
}
}
uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(lean_object* v_xs_1692_, lean_object* v_ys_1693_, lean_object* v_hsz_1694_, lean_object* v_x_1695_, lean_object* v_x_1696_){
_start:
{
uint8_t v___x_1697_; 
v___x_1697_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1692_, v_ys_1693_, v_x_1695_);
return v___x_1697_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1692_ = stack[0].m_obj;
lean_object* v_ys_1693_ = stack[1].m_obj;
lean_object* v_x_1695_ = stack[3].m_obj;
uint8_t v_res_1698_;
v_res_1698_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(v_xs_1692_, v_ys_1693_, lean_box(0), v_x_1695_, lean_box(0));
stack->m_num = v_res_1698_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___boxed(lean_object* v_xs_1699_, lean_object* v_ys_1700_, lean_object* v_hsz_1701_, lean_object* v_x_1702_, lean_object* v_x_1703_){
_start:
{
uint8_t v_res_1704_; lean_object* v_r_1705_; 
v_res_1704_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(v_xs_1699_, v_ys_1700_, v_hsz_1701_, v_x_1702_, v_x_1703_);
lean_dec_ref(v_ys_1700_);
lean_dec_ref(v_xs_1699_);
v_r_1705_ = lean_box(v_res_1704_);
return v_r_1705_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(lean_object* v_as_1706_){
_start:
{
lean_object* v___f_1707_; lean_object* v___x_1708_; 
v___f_1707_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__0));
v___x_1708_ = l_List_eraseDupsBy___redArg(v___f_1707_, v_as_1706_);
return v___x_1708_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(size_t v_sz_1709_, size_t v_i_1710_, lean_object* v_bs_1711_){
_start:
{
uint8_t v___x_1712_; 
v___x_1712_ = lean_usize_dec_lt(v_i_1710_, v_sz_1709_);
if (v___x_1712_ == 0)
{
return v_bs_1711_;
}
else
{
lean_object* v_v_1713_; lean_object* v_fst_1714_; lean_object* v___x_1715_; lean_object* v_bs_x27_1716_; size_t v___x_1717_; size_t v___x_1718_; lean_object* v___x_1719_; 
v_v_1713_ = lean_array_uget_borrowed(v_bs_1711_, v_i_1710_);
v_fst_1714_ = lean_ctor_get(v_v_1713_, 0);
lean_inc(v_fst_1714_);
v___x_1715_ = lean_unsigned_to_nat(0u);
v_bs_x27_1716_ = lean_array_uset(v_bs_1711_, v_i_1710_, v___x_1715_);
v___x_1717_ = ((size_t)1ULL);
v___x_1718_ = lean_usize_add(v_i_1710_, v___x_1717_);
v___x_1719_ = lean_array_uset(v_bs_x27_1716_, v_i_1710_, v_fst_1714_);
v_i_1710_ = v___x_1718_;
v_bs_1711_ = v___x_1719_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1709_ = stack[0].m_num;
size_t v_i_1710_ = stack[1].m_num;
lean_object* v_bs_1711_ = stack[2].m_obj;
lean_object* v_res_1721_;
v_res_1721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_1709_, v_i_1710_, v_bs_1711_);
stack->m_obj
 = v_res_1721_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0___boxed(lean_object* v_sz_1722_, lean_object* v_i_1723_, lean_object* v_bs_1724_){
_start:
{
size_t v_sz_boxed_1725_; size_t v_i_boxed_1726_; lean_object* v_res_1727_; 
v_sz_boxed_1725_ = lean_unbox_usize(v_sz_1722_);
lean_dec(v_sz_1722_);
v_i_boxed_1726_ = lean_unbox_usize(v_i_1723_);
lean_dec(v_i_1723_);
v_res_1727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_boxed_1725_, v_i_boxed_1726_, v_bs_1724_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names(lean_object* v_query_1728_){
_start:
{
size_t v_sz_1729_; size_t v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v_sz_1729_ = lean_array_size(v_query_1728_);
v___x_1730_ = ((size_t)0ULL);
v___x_1731_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_1729_, v___x_1730_, v_query_1728_);
v___x_1732_ = lean_array_to_list(v___x_1731_);
v___x_1733_ = l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(v___x_1732_);
v___x_1734_ = lean_array_mk(v___x_1733_);
return v___x_1734_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(size_t v_sz_1735_, size_t v_i_1736_, lean_object* v_bs_1737_){
_start:
{
uint8_t v___x_1738_; 
v___x_1738_ = lean_usize_dec_lt(v_i_1736_, v_sz_1735_);
if (v___x_1738_ == 0)
{
return v_bs_1737_;
}
else
{
lean_object* v_v_1739_; lean_object* v_snd_1740_; lean_object* v___x_1741_; lean_object* v_bs_x27_1742_; size_t v___x_1743_; size_t v___x_1744_; lean_object* v___x_1745_; 
v_v_1739_ = lean_array_uget_borrowed(v_bs_1737_, v_i_1736_);
v_snd_1740_ = lean_ctor_get(v_v_1739_, 1);
lean_inc(v_snd_1740_);
v___x_1741_ = lean_unsigned_to_nat(0u);
v_bs_x27_1742_ = lean_array_uset(v_bs_1737_, v_i_1736_, v___x_1741_);
v___x_1743_ = ((size_t)1ULL);
v___x_1744_ = lean_usize_add(v_i_1736_, v___x_1743_);
v___x_1745_ = lean_array_uset(v_bs_x27_1742_, v_i_1736_, v_snd_1740_);
v_i_1736_ = v___x_1744_;
v_bs_1737_ = v___x_1745_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1735_ = stack[0].m_num;
size_t v_i_1736_ = stack[1].m_num;
lean_object* v_bs_1737_ = stack[2].m_obj;
lean_object* v_res_1747_;
v_res_1747_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_1735_, v_i_1736_, v_bs_1737_);
stack->m_obj
 = v_res_1747_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0___boxed(lean_object* v_sz_1748_, lean_object* v_i_1749_, lean_object* v_bs_1750_){
_start:
{
size_t v_sz_boxed_1751_; size_t v_i_boxed_1752_; lean_object* v_res_1753_; 
v_sz_boxed_1751_ = lean_unbox_usize(v_sz_1748_);
lean_dec(v_sz_1748_);
v_i_boxed_1752_ = lean_unbox_usize(v_i_1749_);
lean_dec(v_i_1749_);
v_res_1753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_boxed_1751_, v_i_boxed_1752_, v_bs_1750_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_values(lean_object* v_query_1754_){
_start:
{
size_t v_sz_1755_; size_t v___x_1756_; lean_object* v___x_1757_; 
v_sz_1755_ = lean_array_size(v_query_1754_);
v___x_1756_ = ((size_t)0ULL);
v___x_1757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_1755_, v___x_1756_, v_query_1754_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray(lean_object* v_query_1758_){
_start:
{
lean_inc_ref(v_query_1758_);
return v_query_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray___boxed(lean_object* v_query_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Std_Http_URI_Query_toArray(v_query_1759_);
lean_dec_ref(v_query_1759_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object* v_key_1762_, lean_object* v_value_1763_){
_start:
{
if (lean_obj_tag(v_value_1763_) == 0)
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_string_from_utf8_unchecked(v_key_1762_);
return v___x_1764_;
}
else
{
lean_object* v_val_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_val_1765_ = lean_ctor_get(v_value_1763_, 0);
lean_inc(v_val_1765_);
lean_dec_ref_known(v_value_1763_, 1);
v___x_1766_ = lean_string_from_utf8_unchecked(v_key_1762_);
v___x_1767_ = ((lean_object*)(l_Std_Http_URI_Query_formatQueryParam___closed__0));
v___x_1768_ = lean_string_append(v___x_1766_, v___x_1767_);
v___x_1769_ = lean_string_from_utf8_unchecked(v_val_1765_);
v___x_1770_ = lean_string_append(v___x_1768_, v___x_1769_);
lean_dec_ref(v___x_1769_);
return v___x_1770_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(lean_object* v_key_1774_, lean_object* v_as_1775_, size_t v_sz_1776_, size_t v_i_1777_, lean_object* v_b_1778_){
_start:
{
uint8_t v___x_1779_; 
v___x_1779_ = lean_usize_dec_lt(v_i_1777_, v_sz_1776_);
if (v___x_1779_ == 0)
{
lean_inc_ref(v_b_1778_);
return v_b_1778_;
}
else
{
lean_object* v_a_1780_; lean_object* v_fst_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; 
v_a_1780_ = lean_array_uget_borrowed(v_as_1775_, v_i_1777_);
v_fst_1781_ = lean_ctor_get(v_a_1780_, 0);
v___x_1782_ = lean_box(0);
v___x_1783_ = lean_sarray_dec_eq(v_fst_1781_, v_key_1774_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; size_t v___x_1785_; size_t v___x_1786_; 
v___x_1784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v___x_1785_ = ((size_t)1ULL);
v___x_1786_ = lean_usize_add(v_i_1777_, v___x_1785_);
v_i_1777_ = v___x_1786_;
v_b_1778_ = v___x_1784_;
goto _start;
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_inc(v_a_1780_);
v___x_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1788_, 0, v_a_1780_);
v___x_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
lean_ctor_set(v___x_1790_, 1, v___x_1782_);
return v___x_1790_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_key_1774_ = stack[0].m_obj;
lean_object* v_as_1775_ = stack[1].m_obj;
size_t v_sz_1776_ = stack[2].m_num;
size_t v_i_1777_ = stack[3].m_num;
lean_object* v_b_1778_ = stack[4].m_obj;
lean_object* v_res_1791_;
v_res_1791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1774_, v_as_1775_, v_sz_1776_, v_i_1777_, v_b_1778_);
stack->m_obj
 = v_res_1791_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___boxed(lean_object* v_key_1792_, lean_object* v_as_1793_, lean_object* v_sz_1794_, lean_object* v_i_1795_, lean_object* v_b_1796_){
_start:
{
size_t v_sz_boxed_1797_; size_t v_i_boxed_1798_; lean_object* v_res_1799_; 
v_sz_boxed_1797_ = lean_unbox_usize(v_sz_1794_);
lean_dec(v_sz_1794_);
v_i_boxed_1798_ = lean_unbox_usize(v_i_1795_);
lean_dec(v_i_1795_);
v_res_1799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1792_, v_as_1793_, v_sz_boxed_1797_, v_i_boxed_1798_, v_b_1796_);
lean_dec_ref(v_b_1796_);
lean_dec_ref(v_as_1793_);
lean_dec_ref(v_key_1792_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f(lean_object* v_query_1800_, lean_object* v_key_1801_){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; size_t v_sz_1804_; size_t v___x_1805_; lean_object* v___x_1806_; lean_object* v_fst_1807_; 
v___x_1802_ = lean_box(0);
v___x_1803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v_sz_1804_ = lean_array_size(v_query_1800_);
v___x_1805_ = ((size_t)0ULL);
v___x_1806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1801_, v_query_1800_, v_sz_1804_, v___x_1805_, v___x_1803_);
v_fst_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_fst_1807_);
lean_dec_ref(v___x_1806_);
if (lean_obj_tag(v_fst_1807_) == 0)
{
return v___x_1802_;
}
else
{
lean_object* v_val_1808_; 
v_val_1808_ = lean_ctor_get(v_fst_1807_, 0);
lean_inc(v_val_1808_);
lean_dec_ref_known(v_fst_1807_, 1);
if (lean_obj_tag(v_val_1808_) == 0)
{
return v___x_1802_;
}
else
{
lean_object* v_val_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1817_; 
v_val_1809_ = lean_ctor_get(v_val_1808_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_val_1808_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1811_ = v_val_1808_;
v_isShared_1812_ = v_isSharedCheck_1817_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_val_1809_);
lean_dec(v_val_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1817_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v_snd_1813_; lean_object* v___x_1815_; 
v_snd_1813_ = lean_ctor_get(v_val_1809_, 1);
lean_inc(v_snd_1813_);
lean_dec(v_val_1809_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v_snd_1813_);
v___x_1815_ = v___x_1811_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_snd_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f___boxed(lean_object* v_query_1818_, lean_object* v_key_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1818_, v_key_1819_);
lean_dec_ref(v_key_1819_);
lean_dec_ref(v_query_1818_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f(lean_object* v_query_1821_, lean_object* v_key_1822_){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1822_);
v___x_1824_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1821_, v___x_1823_);
lean_dec_ref(v___x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f___boxed(lean_object* v_query_1825_, lean_object* v_key_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Std_Http_URI_Query_find_x3f(v_query_1825_, v_key_1826_);
lean_dec_ref(v_key_1826_);
lean_dec_ref(v_query_1825_);
return v_res_1827_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(lean_object* v_key_1828_, lean_object* v_as_1829_, size_t v_i_1830_, size_t v_stop_1831_, lean_object* v_b_1832_){
_start:
{
lean_object* v___y_1834_; uint8_t v___x_1838_; 
v___x_1838_ = lean_usize_dec_eq(v_i_1830_, v_stop_1831_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v_fst_1840_; lean_object* v_snd_1841_; uint8_t v___x_1842_; 
v___x_1839_ = lean_array_uget_borrowed(v_as_1829_, v_i_1830_);
v_fst_1840_ = lean_ctor_get(v___x_1839_, 0);
v_snd_1841_ = lean_ctor_get(v___x_1839_, 1);
v___x_1842_ = lean_sarray_dec_eq(v_fst_1840_, v_key_1828_);
if (v___x_1842_ == 0)
{
v___y_1834_ = v_b_1832_;
goto v___jp_1833_;
}
else
{
lean_object* v___x_1843_; 
lean_inc(v_snd_1841_);
v___x_1843_ = lean_array_push(v_b_1832_, v_snd_1841_);
v___y_1834_ = v___x_1843_;
goto v___jp_1833_;
}
}
else
{
return v_b_1832_;
}
v___jp_1833_:
{
size_t v___x_1835_; size_t v___x_1836_; 
v___x_1835_ = ((size_t)1ULL);
v___x_1836_ = lean_usize_add(v_i_1830_, v___x_1835_);
v_i_1830_ = v___x_1836_;
v_b_1832_ = v___y_1834_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_key_1828_ = stack[0].m_obj;
lean_object* v_as_1829_ = stack[1].m_obj;
size_t v_i_1830_ = stack[2].m_num;
size_t v_stop_1831_ = stack[3].m_num;
lean_object* v_b_1832_ = stack[4].m_obj;
lean_object* v_res_1844_;
v_res_1844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1828_, v_as_1829_, v_i_1830_, v_stop_1831_, v_b_1832_);
stack->m_obj
 = v_res_1844_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0___boxed(lean_object* v_key_1845_, lean_object* v_as_1846_, lean_object* v_i_1847_, lean_object* v_stop_1848_, lean_object* v_b_1849_){
_start:
{
size_t v_i_boxed_1850_; size_t v_stop_boxed_1851_; lean_object* v_res_1852_; 
v_i_boxed_1850_ = lean_unbox_usize(v_i_1847_);
lean_dec(v_i_1847_);
v_stop_boxed_1851_ = lean_unbox_usize(v_stop_1848_);
lean_dec(v_stop_1848_);
v_res_1852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1845_, v_as_1846_, v_i_boxed_1850_, v_stop_boxed_1851_, v_b_1849_);
lean_dec_ref(v_as_1846_);
lean_dec_ref(v_key_1845_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(lean_object* v_key_1855_, lean_object* v_as_1856_, lean_object* v_start_1857_, lean_object* v_stop_1858_){
_start:
{
lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1859_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_1860_ = lean_nat_dec_lt(v_start_1857_, v_stop_1858_);
if (v___x_1860_ == 0)
{
return v___x_1859_;
}
else
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = lean_array_get_size(v_as_1856_);
v___x_1862_ = lean_nat_dec_le(v_stop_1858_, v___x_1861_);
if (v___x_1862_ == 0)
{
uint8_t v___x_1863_; 
v___x_1863_ = lean_nat_dec_lt(v_start_1857_, v___x_1861_);
if (v___x_1863_ == 0)
{
return v___x_1859_;
}
else
{
size_t v___x_1864_; size_t v___x_1865_; lean_object* v___x_1866_; 
v___x_1864_ = lean_usize_of_nat(v_start_1857_);
v___x_1865_ = lean_usize_of_nat(v___x_1861_);
v___x_1866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1855_, v_as_1856_, v___x_1864_, v___x_1865_, v___x_1859_);
return v___x_1866_;
}
}
else
{
size_t v___x_1867_; size_t v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = lean_usize_of_nat(v_start_1857_);
v___x_1868_ = lean_usize_of_nat(v_stop_1858_);
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1855_, v_as_1856_, v___x_1867_, v___x_1868_, v___x_1859_);
return v___x_1869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___boxed(lean_object* v_key_1870_, lean_object* v_as_1871_, lean_object* v_start_1872_, lean_object* v_stop_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1870_, v_as_1871_, v_start_1872_, v_stop_1873_);
lean_dec(v_stop_1873_);
lean_dec(v_start_1872_);
lean_dec_ref(v_as_1871_);
lean_dec_ref(v_key_1870_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded(lean_object* v_query_1875_, lean_object* v_key_1876_){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1877_ = lean_unsigned_to_nat(0u);
v___x_1878_ = lean_array_get_size(v_query_1875_);
v___x_1879_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1876_, v_query_1875_, v___x_1877_, v___x_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded___boxed(lean_object* v_query_1880_, lean_object* v_key_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1880_, v_key_1881_);
lean_dec_ref(v_key_1881_);
lean_dec_ref(v_query_1880_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll(lean_object* v_query_1883_, lean_object* v_key_1884_){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1884_);
v___x_1886_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1883_, v___x_1885_);
lean_dec_ref(v___x_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll___boxed(lean_object* v_query_1887_, lean_object* v_key_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Std_Http_URI_Query_findAll(v_query_1887_, v_key_1888_);
lean_dec_ref(v_key_1888_);
lean_dec_ref(v_query_1887_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert(lean_object* v_query_1890_, lean_object* v_key_1891_, lean_object* v_value_1892_){
_start:
{
lean_object* v_encodedKey_1893_; lean_object* v_encodedValue_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_encodedKey_1893_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1891_);
v_encodedValue_1894_ = l_Std_Http_URI_EncodedQueryParam_encode(v_value_1892_);
v___x_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1895_, 0, v_encodedValue_1894_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_encodedKey_1893_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = lean_array_push(v_query_1890_, v___x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert___boxed(lean_object* v_query_1898_, lean_object* v_key_1899_, lean_object* v_value_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Std_Http_URI_Query_insert(v_query_1898_, v_key_1899_, v_value_1900_);
lean_dec_ref(v_value_1900_);
lean_dec_ref(v_key_1899_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object* v_query_1902_, lean_object* v_key_1903_, lean_object* v_value_1904_){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1905_, 0, v_key_1903_);
lean_ctor_set(v___x_1905_, 1, v_value_1904_);
v___x_1906_ = lean_array_push(v_query_1902_, v___x_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_ofList(lean_object* v_pairs_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_array_mk(v_pairs_1910_);
return v___x_1911_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(lean_object* v_key_1912_, lean_object* v_as_1913_, size_t v_i_1914_, size_t v_stop_1915_){
_start:
{
uint8_t v___x_1916_; 
v___x_1916_ = lean_usize_dec_eq(v_i_1914_, v_stop_1915_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; lean_object* v_fst_1918_; uint8_t v___x_1919_; 
v___x_1917_ = lean_array_uget_borrowed(v_as_1913_, v_i_1914_);
v_fst_1918_ = lean_ctor_get(v___x_1917_, 0);
v___x_1919_ = lean_sarray_dec_eq(v_fst_1918_, v_key_1912_);
if (v___x_1919_ == 0)
{
size_t v___x_1920_; size_t v___x_1921_; 
v___x_1920_ = ((size_t)1ULL);
v___x_1921_ = lean_usize_add(v_i_1914_, v___x_1920_);
v_i_1914_ = v___x_1921_;
goto _start;
}
else
{
return v___x_1919_;
}
}
else
{
uint8_t v___x_1923_; 
v___x_1923_ = 0;
return v___x_1923_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_key_1912_ = stack[0].m_obj;
lean_object* v_as_1913_ = stack[1].m_obj;
size_t v_i_1914_ = stack[2].m_num;
size_t v_stop_1915_ = stack[3].m_num;
uint8_t v_res_1924_;
v_res_1924_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1912_, v_as_1913_, v_i_1914_, v_stop_1915_);
stack->m_num = v_res_1924_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(lean_object* v_key_1925_, lean_object* v_as_1926_, lean_object* v_i_1927_, lean_object* v_stop_1928_){
_start:
{
size_t v_i_boxed_1929_; size_t v_stop_boxed_1930_; uint8_t v_res_1931_; lean_object* v_r_1932_; 
v_i_boxed_1929_ = lean_unbox_usize(v_i_1927_);
lean_dec(v_i_1927_);
v_stop_boxed_1930_ = lean_unbox_usize(v_stop_1928_);
lean_dec(v_stop_1928_);
v_res_1931_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1925_, v_as_1926_, v_i_boxed_1929_, v_stop_boxed_1930_);
lean_dec_ref(v_as_1926_);
lean_dec_ref(v_key_1925_);
v_r_1932_ = lean_box(v_res_1931_);
return v_r_1932_;
}
}
uint8_t l_Std_Http_URI_Query_containsEncoded(lean_object* v_query_1933_, lean_object* v_key_1934_){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1935_ = lean_unsigned_to_nat(0u);
v___x_1936_ = lean_array_get_size(v_query_1933_);
v___x_1937_ = lean_nat_dec_lt(v___x_1935_, v___x_1936_);
if (v___x_1937_ == 0)
{
return v___x_1937_;
}
else
{
if (v___x_1937_ == 0)
{
return v___x_1937_;
}
else
{
size_t v___x_1938_; size_t v___x_1939_; uint8_t v___x_1940_; 
v___x_1938_ = ((size_t)0ULL);
v___x_1939_ = lean_usize_of_nat(v___x_1936_);
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1934_, v_query_1933_, v___x_1938_, v___x_1939_);
return v___x_1940_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_Query_containsEncoded_0interp(lean_interpreter_value* stack)
{
lean_object* v_query_1933_ = stack[0].m_obj;
lean_object* v_key_1934_ = stack[1].m_obj;
uint8_t v_res_1941_;
v_res_1941_ = l_Std_Http_URI_Query_containsEncoded(v_query_1933_, v_key_1934_);
stack->m_num = v_res_1941_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_containsEncoded___boxed(lean_object* v_query_1942_, lean_object* v_key_1943_){
_start:
{
uint8_t v_res_1944_; lean_object* v_r_1945_; 
v_res_1944_ = l_Std_Http_URI_Query_containsEncoded(v_query_1942_, v_key_1943_);
lean_dec_ref(v_key_1943_);
lean_dec_ref(v_query_1942_);
v_r_1945_ = lean_box(v_res_1944_);
return v_r_1945_;
}
}
uint8_t l_Std_Http_URI_Query_contains(lean_object* v_query_1946_, lean_object* v_key_1947_){
_start:
{
lean_object* v___x_1948_; uint8_t v___x_1949_; 
v___x_1948_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1947_);
v___x_1949_ = l_Std_Http_URI_Query_containsEncoded(v_query_1946_, v___x_1948_);
lean_dec_ref(v___x_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT void l_Std_Http_URI_Query_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_query_1946_ = stack[0].m_obj;
lean_object* v_key_1947_ = stack[1].m_obj;
uint8_t v_res_1950_;
v_res_1950_ = l_Std_Http_URI_Query_contains(v_query_1946_, v_key_1947_);
stack->m_num = v_res_1950_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_contains___boxed(lean_object* v_query_1951_, lean_object* v_key_1952_){
_start:
{
uint8_t v_res_1953_; lean_object* v_r_1954_; 
v_res_1953_ = l_Std_Http_URI_Query_contains(v_query_1951_, v_key_1952_);
lean_dec_ref(v_key_1952_);
lean_dec_ref(v_query_1951_);
v_r_1954_ = lean_box(v_res_1953_);
return v_r_1954_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(lean_object* v_key_1955_, lean_object* v_as_1956_, size_t v_i_1957_, size_t v_stop_1958_, lean_object* v_b_1959_){
_start:
{
lean_object* v___y_1961_; uint8_t v___x_1965_; 
v___x_1965_ = lean_usize_dec_eq(v_i_1957_, v_stop_1958_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; lean_object* v_fst_1969_; uint8_t v___x_1970_; 
v___x_1966_ = lean_array_uget_borrowed(v_as_1956_, v_i_1957_);
v_fst_1969_ = lean_ctor_get(v___x_1966_, 0);
v___x_1970_ = lean_sarray_dec_eq(v_fst_1969_, v_key_1955_);
if (v___x_1970_ == 0)
{
goto v___jp_1967_;
}
else
{
if (v___x_1965_ == 0)
{
v___y_1961_ = v_b_1959_;
goto v___jp_1960_;
}
else
{
goto v___jp_1967_;
}
}
v___jp_1967_:
{
lean_object* v___x_1968_; 
lean_inc(v___x_1966_);
v___x_1968_ = lean_array_push(v_b_1959_, v___x_1966_);
v___y_1961_ = v___x_1968_;
goto v___jp_1960_;
}
}
else
{
return v_b_1959_;
}
v___jp_1960_:
{
size_t v___x_1962_; size_t v___x_1963_; 
v___x_1962_ = ((size_t)1ULL);
v___x_1963_ = lean_usize_add(v_i_1957_, v___x_1962_);
v_i_1957_ = v___x_1963_;
v_b_1959_ = v___y_1961_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_key_1955_ = stack[0].m_obj;
lean_object* v_as_1956_ = stack[1].m_obj;
size_t v_i_1957_ = stack[2].m_num;
size_t v_stop_1958_ = stack[3].m_num;
lean_object* v_b_1959_ = stack[4].m_obj;
lean_object* v_res_1971_;
v_res_1971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1955_, v_as_1956_, v_i_1957_, v_stop_1958_, v_b_1959_);
stack->m_obj
 = v_res_1971_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(lean_object* v_key_1972_, lean_object* v_as_1973_, lean_object* v_i_1974_, lean_object* v_stop_1975_, lean_object* v_b_1976_){
_start:
{
size_t v_i_boxed_1977_; size_t v_stop_boxed_1978_; lean_object* v_res_1979_; 
v_i_boxed_1977_ = lean_unbox_usize(v_i_1974_);
lean_dec(v_i_1974_);
v_stop_boxed_1978_ = lean_unbox_usize(v_stop_1975_);
lean_dec(v_stop_1975_);
v_res_1979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1972_, v_as_1973_, v_i_boxed_1977_, v_stop_boxed_1978_, v_b_1976_);
lean_dec_ref(v_as_1973_);
lean_dec_ref(v_key_1972_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded(lean_object* v_query_1980_, lean_object* v_key_1981_){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1982_ = lean_unsigned_to_nat(0u);
v___x_1983_ = lean_array_get_size(v_query_1980_);
v___x_1984_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_1985_ = lean_nat_dec_lt(v___x_1982_, v___x_1983_);
if (v___x_1985_ == 0)
{
return v___x_1984_;
}
else
{
uint8_t v___x_1986_; 
v___x_1986_ = lean_nat_dec_le(v___x_1983_, v___x_1983_);
if (v___x_1986_ == 0)
{
if (v___x_1985_ == 0)
{
return v___x_1984_;
}
else
{
size_t v___x_1987_; size_t v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = ((size_t)0ULL);
v___x_1988_ = lean_usize_of_nat(v___x_1983_);
v___x_1989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1981_, v_query_1980_, v___x_1987_, v___x_1988_, v___x_1984_);
return v___x_1989_;
}
}
else
{
size_t v___x_1990_; size_t v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = ((size_t)0ULL);
v___x_1991_ = lean_usize_of_nat(v___x_1983_);
v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1981_, v_query_1980_, v___x_1990_, v___x_1991_, v___x_1984_);
return v___x_1992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded___boxed(lean_object* v_query_1993_, lean_object* v_key_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Std_Http_URI_Query_eraseEncoded(v_query_1993_, v_key_1994_);
lean_dec_ref(v_key_1994_);
lean_dec_ref(v_query_1993_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase(lean_object* v_query_1996_, lean_object* v_key_1997_){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1997_);
v___x_1999_ = l_Std_Http_URI_Query_eraseEncoded(v_query_1996_, v___x_1998_);
lean_dec_ref(v___x_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase___boxed(lean_object* v_query_2000_, lean_object* v_key_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Std_Http_URI_Query_erase(v_query_2000_, v_key_2001_);
lean_dec_ref(v_key_2001_);
lean_dec_ref(v_query_2000_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get(lean_object* v_query_2005_, lean_object* v_key_2006_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Std_Http_URI_Query_find_x3f(v_query_2005_, v_key_2006_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_box(0);
return v___x_2008_;
}
else
{
lean_object* v_val_2009_; 
v_val_2009_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_val_2009_);
lean_dec_ref_known(v___x_2007_, 1);
if (lean_obj_tag(v_val_2009_) == 0)
{
lean_object* v___x_2010_; 
v___x_2010_ = ((lean_object*)(l_Std_Http_URI_Query_get___closed__0));
return v___x_2010_;
}
else
{
lean_object* v_val_2011_; lean_object* v___x_2012_; 
v_val_2011_ = lean_ctor_get(v_val_2009_, 0);
lean_inc(v_val_2011_);
lean_dec_ref_known(v_val_2009_, 1);
v___x_2012_ = l_Std_Http_URI_EncodedQueryParam_decode(v_val_2011_);
lean_dec(v_val_2011_);
return v___x_2012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get___boxed(lean_object* v_query_2013_, lean_object* v_key_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Std_Http_URI_Query_get(v_query_2013_, v_key_2014_);
lean_dec_ref(v_key_2014_);
lean_dec_ref(v_query_2013_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD(lean_object* v_query_2016_, lean_object* v_key_2017_, lean_object* v_default_2018_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Std_Http_URI_Query_get(v_query_2016_, v_key_2017_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_inc_ref(v_default_2018_);
return v_default_2018_;
}
else
{
lean_object* v_val_2020_; 
v_val_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_val_2020_);
lean_dec_ref_known(v___x_2019_, 1);
return v_val_2020_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD___boxed(lean_object* v_query_2021_, lean_object* v_key_2022_, lean_object* v_default_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Std_Http_URI_Query_getD(v_query_2021_, v_key_2022_, v_default_2023_);
lean_dec_ref(v_default_2023_);
lean_dec_ref(v_key_2022_);
lean_dec_ref(v_query_2021_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set(lean_object* v_query_2025_, lean_object* v_key_2026_, lean_object* v_value_2027_){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = l_Std_Http_URI_Query_erase(v_query_2025_, v_key_2026_);
v___x_2029_ = l_Std_Http_URI_Query_insert(v___x_2028_, v_key_2026_, v_value_2027_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set___boxed(lean_object* v_query_2030_, lean_object* v_key_2031_, lean_object* v_value_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Std_Http_URI_Query_set(v_query_2030_, v_key_2031_, v_value_2032_);
lean_dec_ref(v_value_2032_);
lean_dec_ref(v_key_2031_);
lean_dec_ref(v_query_2030_);
return v_res_2033_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(size_t v_sz_2034_, size_t v_i_2035_, lean_object* v_bs_2036_){
_start:
{
uint8_t v___x_2037_; 
v___x_2037_ = lean_usize_dec_lt(v_i_2035_, v_sz_2034_);
if (v___x_2037_ == 0)
{
return v_bs_2036_;
}
else
{
lean_object* v_v_2038_; lean_object* v_fst_2039_; lean_object* v_snd_2040_; lean_object* v___x_2041_; lean_object* v_bs_x27_2042_; lean_object* v___x_2043_; size_t v___x_2044_; size_t v___x_2045_; lean_object* v___x_2046_; 
v_v_2038_ = lean_array_uget_borrowed(v_bs_2036_, v_i_2035_);
v_fst_2039_ = lean_ctor_get(v_v_2038_, 0);
lean_inc(v_fst_2039_);
v_snd_2040_ = lean_ctor_get(v_v_2038_, 1);
lean_inc(v_snd_2040_);
v___x_2041_ = lean_unsigned_to_nat(0u);
v_bs_x27_2042_ = lean_array_uset(v_bs_2036_, v_i_2035_, v___x_2041_);
v___x_2043_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2039_, v_snd_2040_);
v___x_2044_ = ((size_t)1ULL);
v___x_2045_ = lean_usize_add(v_i_2035_, v___x_2044_);
v___x_2046_ = lean_array_uset(v_bs_x27_2042_, v_i_2035_, v___x_2043_);
v_i_2035_ = v___x_2045_;
v_bs_2036_ = v___x_2046_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2034_ = stack[0].m_num;
size_t v_i_2035_ = stack[1].m_num;
lean_object* v_bs_2036_ = stack[2].m_obj;
lean_object* v_res_2048_;
v_res_2048_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_2034_, v_i_2035_, v_bs_2036_);
stack->m_obj
 = v_res_2048_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0___boxed(lean_object* v_sz_2049_, lean_object* v_i_2050_, lean_object* v_bs_2051_){
_start:
{
size_t v_sz_boxed_2052_; size_t v_i_boxed_2053_; lean_object* v_res_2054_; 
v_sz_boxed_2052_ = lean_unbox_usize(v_sz_2049_);
lean_dec(v_sz_2049_);
v_i_boxed_2053_ = lean_unbox_usize(v_i_2050_);
lean_dec(v_i_2050_);
v_res_2054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_boxed_2052_, v_i_boxed_2053_, v_bs_2051_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toRawString(lean_object* v_query_2056_){
_start:
{
size_t v_sz_2057_; size_t v___x_2058_; lean_object* v_params_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v_sz_2057_ = lean_array_size(v_query_2056_);
v___x_2058_ = ((size_t)0ULL);
v_params_2059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_2057_, v___x_2058_, v_query_2056_);
v___x_2060_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2061_ = lean_array_to_list(v_params_2059_);
v___x_2062_ = l_String_intercalate(v___x_2060_, v___x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0(lean_object* v_x_2064_){
_start:
{
lean_object* v_fst_2065_; lean_object* v_snd_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v_fst_2065_ = lean_ctor_get(v_x_2064_, 0);
v_snd_2066_ = lean_ctor_get(v_x_2064_, 1);
v___x_2067_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
v___x_2068_ = l_Std_Http_URI_Query_insert(v___x_2067_, v_fst_2065_, v_snd_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0___boxed(lean_object* v_x_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Std_Http_URI_Query_instSingletonProdString___lam__0(v_x_2069_);
lean_dec_ref(v_x_2069_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0(lean_object* v_x_2073_, lean_object* v_q_2074_){
_start:
{
lean_object* v_fst_2075_; lean_object* v_snd_2076_; lean_object* v___x_2077_; 
v_fst_2075_ = lean_ctor_get(v_x_2073_, 0);
v_snd_2076_ = lean_ctor_get(v_x_2073_, 1);
v___x_2077_ = l_Std_Http_URI_Query_insert(v_q_2074_, v_fst_2075_, v_snd_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0___boxed(lean_object* v_x_2078_, lean_object* v_q_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Std_Http_URI_Query_instInsertProdString___lam__0(v_x_2078_, v_q_2079_);
lean_dec_ref(v_x_2078_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__0(lean_object* v_x_2083_){
_start:
{
lean_object* v_fst_2084_; lean_object* v_snd_2085_; lean_object* v___x_2086_; 
v_fst_2084_ = lean_ctor_get(v_x_2083_, 0);
lean_inc(v_fst_2084_);
v_snd_2085_ = lean_ctor_get(v_x_2083_, 1);
lean_inc(v_snd_2085_);
lean_dec_ref(v_x_2083_);
v___x_2086_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2084_, v_snd_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__1(lean_object* v___f_2088_, lean_object* v_q_2089_){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2090_ = lean_array_get_size(v_q_2089_);
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = lean_nat_dec_eq(v___x_2090_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v_encodedParams_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2093_ = lean_array_to_list(v_q_2089_);
v___x_2094_ = lean_box(0);
v_encodedParams_2095_ = l_List_mapTR_loop___redArg(v___f_2088_, v___x_2093_, v___x_2094_);
v___x_2096_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2097_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2098_ = l_String_intercalate(v___x_2097_, v_encodedParams_2095_);
v___x_2099_ = lean_string_append(v___x_2096_, v___x_2098_);
lean_dec_ref(v___x_2098_);
return v___x_2099_;
}
else
{
lean_object* v___x_2100_; 
lean_dec_ref(v_q_2089_);
lean_dec_ref(v___f_2088_);
v___x_2100_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2100_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
if (lean_obj_tag(v_a_2105_) == 0)
{
lean_object* v___x_2107_; 
v___x_2107_ = l_List_reverse___redArg(v_a_2106_);
return v___x_2107_;
}
else
{
lean_object* v_head_2108_; lean_object* v_tail_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2120_; 
v_head_2108_ = lean_ctor_get(v_a_2105_, 0);
v_tail_2109_ = lean_ctor_get(v_a_2105_, 1);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_a_2105_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2111_ = v_a_2105_;
v_isShared_2112_ = v_isSharedCheck_2120_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_tail_2109_);
lean_inc(v_head_2108_);
lean_dec(v_a_2105_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2120_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v_fst_2113_; lean_object* v_snd_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
v_fst_2113_ = lean_ctor_get(v_head_2108_, 0);
lean_inc(v_fst_2113_);
v_snd_2114_ = lean_ctor_get(v_head_2108_, 1);
lean_inc(v_snd_2114_);
lean_dec(v_head_2108_);
v___x_2115_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2113_, v_snd_2114_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v_a_2106_);
lean_ctor_set(v___x_2111_, 0, v___x_2115_);
v___x_2117_ = v___x_2111_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_a_2106_);
v___x_2117_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
v_a_2105_ = v_tail_2109_;
v_a_2106_ = v___x_2117_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatOption(lean_object* v_x_2121_){
_start:
{
if (lean_obj_tag(v_x_2121_) == 0)
{
lean_object* v___x_2122_; 
v___x_2122_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2122_;
}
else
{
lean_object* v_val_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; uint8_t v___x_2126_; 
v_val_2123_ = lean_ctor_get(v_x_2121_, 0);
lean_inc(v_val_2123_);
lean_dec_ref_known(v_x_2121_, 1);
v___x_2124_ = lean_array_get_size(v_val_2123_);
v___x_2125_ = lean_unsigned_to_nat(0u);
v___x_2126_ = lean_nat_dec_eq(v___x_2124_, v___x_2125_);
if (v___x_2126_ == 0)
{
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v_encodedParams_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2127_ = lean_array_to_list(v_val_2123_);
v___x_2128_ = lean_box(0);
v_encodedParams_2129_ = l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(v___x_2127_, v___x_2128_);
v___x_2130_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2131_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2132_ = l_String_intercalate(v___x_2131_, v_encodedParams_2129_);
v___x_2133_ = lean_string_append(v___x_2130_, v___x_2132_);
lean_dec_ref(v___x_2132_);
return v___x_2133_;
}
else
{
lean_object* v___x_2134_; 
lean_dec(v_val_2123_);
v___x_2134_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2134_;
}
}
else
{
lean_object* v___x_2135_; 
lean_dec(v_val_2123_);
v___x_2135_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
return v___x_2135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(lean_object* v_x_2136_, lean_object* v_x_2137_){
_start:
{
if (lean_obj_tag(v_x_2136_) == 0)
{
lean_object* v___x_2138_; 
v___x_2138_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2138_;
}
else
{
lean_object* v_val_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v_val_2139_ = lean_ctor_get(v_x_2136_, 0);
lean_inc(v_val_2139_);
lean_dec_ref_known(v_x_2136_, 1);
v___x_2140_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2141_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_val_2139_);
v___x_2142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2140_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
v___x_2143_ = l_Repr_addAppParen(v___x_2142_, v_x_2137_);
return v___x_2143_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(lean_object* v_x_2144_, lean_object* v_x_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_x_2144_, v_x_2145_);
lean_dec(v_x_2145_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object* v_x_2147_, lean_object* v_x_2148_){
_start:
{
if (lean_obj_tag(v_x_2147_) == 0)
{
lean_object* v___x_2149_; 
v___x_2149_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2149_;
}
else
{
lean_object* v_val_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v_val_2150_ = lean_ctor_get(v_x_2147_, 0);
lean_inc(v_val_2150_);
lean_dec_ref_known(v_x_2147_, 1);
v___x_2151_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2152_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_val_2150_);
v___x_2153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2151_);
lean_ctor_set(v___x_2153_, 1, v___x_2152_);
v___x_2154_ = l_Repr_addAppParen(v___x_2153_, v_x_2148_);
return v___x_2154_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1___boxed(lean_object* v_x_2155_, lean_object* v_x_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_x_2155_, v_x_2156_);
lean_dec(v_x_2156_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(lean_object* v_x_2158_, lean_object* v_x_2159_){
_start:
{
if (lean_obj_tag(v_x_2158_) == 0)
{
lean_object* v___x_2160_; 
v___x_2160_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2160_;
}
else
{
lean_object* v_val_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2172_; 
v_val_2161_ = lean_ctor_get(v_x_2158_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_x_2158_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2163_ = v_x_2158_;
v_isShared_2164_ = v_isSharedCheck_2172_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_val_2161_);
lean_dec(v_x_2158_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2172_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2165_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2166_ = l_String_quote(v_val_2161_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set_tag(v___x_2163_, 3);
lean_ctor_set(v___x_2163_, 0, v___x_2166_);
v___x_2168_ = v___x_2163_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2165_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = l_Repr_addAppParen(v___x_2169_, v_x_2159_);
return v___x_2170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2___boxed(lean_object* v_x_2173_, lean_object* v_x_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_x_2173_, v_x_2174_);
lean_dec(v_x_2174_);
return v_res_2175_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = lean_unsigned_to_nat(10u);
v___x_2186_ = lean_nat_to_int(v___x_2185_);
return v___x_2186_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_unsigned_to_nat(13u);
v___x_2191_ = lean_nat_to_int(v___x_2190_);
return v___x_2191_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = lean_unsigned_to_nat(9u);
v___x_2199_ = lean_nat_to_int(v___x_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___redArg(lean_object* v_x_2203_){
_start:
{
lean_object* v_scheme_2204_; lean_object* v_authority_2205_; lean_object* v_path_2206_; lean_object* v_query_2207_; lean_object* v_fragment_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v_scheme_2204_ = lean_ctor_get(v_x_2203_, 0);
lean_inc_ref(v_scheme_2204_);
v_authority_2205_ = lean_ctor_get(v_x_2203_, 1);
lean_inc(v_authority_2205_);
v_path_2206_ = lean_ctor_get(v_x_2203_, 2);
lean_inc_ref(v_path_2206_);
v_query_2207_ = lean_ctor_get(v_x_2203_, 3);
lean_inc(v_query_2207_);
v_fragment_2208_ = lean_ctor_get(v_x_2203_, 4);
lean_inc(v_fragment_2208_);
lean_dec_ref(v_x_2203_);
v___x_2209_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2210_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2211_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2212_ = l_String_quote(v_scheme_2204_);
v___x_2213_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
v___x_2214_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2211_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = 0;
v___x_2216_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2216_, 0, v___x_2214_);
lean_ctor_set_uint8(v___x_2216_, sizeof(void*)*1, v___x_2215_);
v___x_2217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2210_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
v___x_2218_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2217_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = lean_box(1);
v___x_2221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2219_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__6));
v___x_2223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2221_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
v___x_2224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
lean_ctor_set(v___x_2224_, 1, v___x_2209_);
v___x_2225_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_2226_ = lean_unsigned_to_nat(0u);
v___x_2227_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_2205_, v___x_2226_);
v___x_2228_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2225_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
v___x_2229_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*1, v___x_2215_);
v___x_2230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2224_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
v___x_2231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
lean_ctor_set(v___x_2231_, 1, v___x_2218_);
v___x_2232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v___x_2220_);
v___x_2233_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_2234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2232_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
lean_ctor_set(v___x_2235_, 1, v___x_2209_);
v___x_2236_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2237_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_2206_);
v___x_2238_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2236_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
lean_ctor_set_uint8(v___x_2239_, sizeof(void*)*1, v___x_2215_);
v___x_2240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2235_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
lean_ctor_set(v___x_2241_, 1, v___x_2218_);
v___x_2242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set(v___x_2242_, 1, v___x_2220_);
v___x_2243_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_2244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2242_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
lean_ctor_set(v___x_2245_, 1, v___x_2209_);
v___x_2246_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_2247_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_2207_, v___x_2226_);
v___x_2248_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2246_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
v___x_2249_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
lean_ctor_set_uint8(v___x_2249_, sizeof(void*)*1, v___x_2215_);
v___x_2250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2245_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
lean_ctor_set(v___x_2251_, 1, v___x_2218_);
v___x_2252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v___x_2220_);
v___x_2253_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_2254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
lean_ctor_set(v___x_2255_, 1, v___x_2209_);
v___x_2256_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_2257_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_2208_, v___x_2226_);
v___x_2258_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
lean_ctor_set_uint8(v___x_2259_, sizeof(void*)*1, v___x_2215_);
v___x_2260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2255_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2262_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set(v___x_2263_, 1, v___x_2260_);
v___x_2264_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2263_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
v___x_2266_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2261_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*1, v___x_2215_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr(lean_object* v_x_2268_, lean_object* v_prec_2269_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Std_Http_instReprURI_repr___redArg(v_x_2268_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___boxed(lean_object* v_x_2271_, lean_object* v_prec_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Std_Http_instReprURI_repr(v_x_2271_, v_prec_2272_);
lean_dec(v_prec_2272_);
return v_res_2273_;
}
}
uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object* v_x_2282_, lean_object* v_x_2283_){
_start:
{
if (lean_obj_tag(v_x_2282_) == 0)
{
if (lean_obj_tag(v_x_2283_) == 0)
{
uint8_t v___x_2284_; 
v___x_2284_ = 1;
return v___x_2284_;
}
else
{
uint8_t v___x_2285_; 
v___x_2285_ = 0;
return v___x_2285_;
}
}
else
{
if (lean_obj_tag(v_x_2283_) == 0)
{
uint8_t v___x_2286_; 
v___x_2286_ = 0;
return v___x_2286_;
}
else
{
lean_object* v_val_2287_; lean_object* v_val_2288_; uint8_t v___x_2289_; 
v_val_2287_ = lean_ctor_get(v_x_2282_, 0);
v_val_2288_ = lean_ctor_get(v_x_2283_, 0);
v___x_2289_ = l_Std_Http_URI_instBEqAuthority_beq(v_val_2287_, v_val_2288_);
return v___x_2289_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2282_ = stack[0].m_obj;
lean_object* v_x_2283_ = stack[1].m_obj;
uint8_t v_res_2290_;
v_res_2290_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_x_2282_, v_x_2283_);
stack->m_num = v_res_2290_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object* v_x_2291_, lean_object* v_x_2292_){
_start:
{
uint8_t v_res_2293_; lean_object* v_r_2294_; 
v_res_2293_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_x_2291_, v_x_2292_);
lean_dec(v_x_2292_);
lean_dec(v_x_2291_);
v_r_2294_ = lean_box(v_res_2293_);
return v_r_2294_;
}
}
uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object* v_x_2295_, lean_object* v_x_2296_){
_start:
{
if (lean_obj_tag(v_x_2295_) == 0)
{
if (lean_obj_tag(v_x_2296_) == 0)
{
uint8_t v___x_2297_; 
v___x_2297_ = 1;
return v___x_2297_;
}
else
{
uint8_t v___x_2298_; 
v___x_2298_ = 0;
return v___x_2298_;
}
}
else
{
if (lean_obj_tag(v_x_2296_) == 0)
{
uint8_t v___x_2299_; 
v___x_2299_ = 0;
return v___x_2299_;
}
else
{
lean_object* v_val_2300_; lean_object* v_val_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v_val_2300_ = lean_ctor_get(v_x_2295_, 0);
v_val_2301_ = lean_ctor_get(v_x_2296_, 0);
v___x_2302_ = lean_array_get_size(v_val_2300_);
v___x_2303_ = lean_array_get_size(v_val_2301_);
v___x_2304_ = lean_nat_dec_eq(v___x_2302_, v___x_2303_);
if (v___x_2304_ == 0)
{
return v___x_2304_;
}
else
{
uint8_t v___x_2305_; 
v___x_2305_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_val_2300_, v_val_2301_, v___x_2302_);
return v___x_2305_;
}
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2295_ = stack[0].m_obj;
lean_object* v_x_2296_ = stack[1].m_obj;
uint8_t v_res_2306_;
v_res_2306_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_x_2295_, v_x_2296_);
stack->m_num = v_res_2306_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object* v_x_2307_, lean_object* v_x_2308_){
_start:
{
uint8_t v_res_2309_; lean_object* v_r_2310_; 
v_res_2309_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_x_2307_, v_x_2308_);
lean_dec(v_x_2308_);
lean_dec(v_x_2307_);
v_r_2310_ = lean_box(v_res_2309_);
return v_r_2310_;
}
}
uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(lean_object* v_x_2311_, lean_object* v_x_2312_){
_start:
{
if (lean_obj_tag(v_x_2311_) == 0)
{
if (lean_obj_tag(v_x_2312_) == 0)
{
uint8_t v___x_2313_; 
v___x_2313_ = 1;
return v___x_2313_;
}
else
{
uint8_t v___x_2314_; 
v___x_2314_ = 0;
return v___x_2314_;
}
}
else
{
if (lean_obj_tag(v_x_2312_) == 0)
{
uint8_t v___x_2315_; 
v___x_2315_ = 0;
return v___x_2315_;
}
else
{
lean_object* v_val_2316_; lean_object* v_val_2317_; uint8_t v___x_2318_; 
v_val_2316_ = lean_ctor_get(v_x_2311_, 0);
v_val_2317_ = lean_ctor_get(v_x_2312_, 0);
v___x_2318_ = lean_string_dec_eq(v_val_2316_, v_val_2317_);
return v___x_2318_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2311_ = stack[0].m_obj;
lean_object* v_x_2312_ = stack[1].m_obj;
uint8_t v_res_2319_;
v_res_2319_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_x_2311_, v_x_2312_);
stack->m_num = v_res_2319_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2___boxed(lean_object* v_x_2320_, lean_object* v_x_2321_){
_start:
{
uint8_t v_res_2322_; lean_object* v_r_2323_; 
v_res_2322_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_x_2320_, v_x_2321_);
lean_dec(v_x_2321_);
lean_dec(v_x_2320_);
v_r_2323_ = lean_box(v_res_2322_);
return v_r_2323_;
}
}
uint8_t l_Std_Http_instBEqURI_beq(lean_object* v_x_2324_, lean_object* v_x_2325_){
_start:
{
lean_object* v_scheme_2326_; lean_object* v_authority_2327_; lean_object* v_path_2328_; lean_object* v_query_2329_; lean_object* v_fragment_2330_; lean_object* v_scheme_2331_; lean_object* v_authority_2332_; lean_object* v_path_2333_; lean_object* v_query_2334_; lean_object* v_fragment_2335_; uint8_t v___x_2336_; 
v_scheme_2326_ = lean_ctor_get(v_x_2324_, 0);
v_authority_2327_ = lean_ctor_get(v_x_2324_, 1);
v_path_2328_ = lean_ctor_get(v_x_2324_, 2);
v_query_2329_ = lean_ctor_get(v_x_2324_, 3);
v_fragment_2330_ = lean_ctor_get(v_x_2324_, 4);
v_scheme_2331_ = lean_ctor_get(v_x_2325_, 0);
v_authority_2332_ = lean_ctor_get(v_x_2325_, 1);
v_path_2333_ = lean_ctor_get(v_x_2325_, 2);
v_query_2334_ = lean_ctor_get(v_x_2325_, 3);
v_fragment_2335_ = lean_ctor_get(v_x_2325_, 4);
v___x_2336_ = lean_string_dec_eq(v_scheme_2326_, v_scheme_2331_);
if (v___x_2336_ == 0)
{
return v___x_2336_;
}
else
{
uint8_t v___x_2337_; 
v___x_2337_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_2327_, v_authority_2332_);
if (v___x_2337_ == 0)
{
return v___x_2337_;
}
else
{
uint8_t v___x_2338_; 
v___x_2338_ = l_Std_Http_URI_instBEqPath_beq(v_path_2328_, v_path_2333_);
if (v___x_2338_ == 0)
{
return v___x_2338_;
}
else
{
uint8_t v___x_2339_; 
v___x_2339_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_2329_, v_query_2334_);
if (v___x_2339_ == 0)
{
return v___x_2339_;
}
else
{
uint8_t v___x_2340_; 
v___x_2340_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_2330_, v_fragment_2335_);
return v___x_2340_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_instBEqURI_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2324_ = stack[0].m_obj;
lean_object* v_x_2325_ = stack[1].m_obj;
uint8_t v_res_2341_;
v_res_2341_ = l_Std_Http_instBEqURI_beq(v_x_2324_, v_x_2325_);
stack->m_num = v_res_2341_;
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object* v_x_2342_, lean_object* v_x_2343_){
_start:
{
uint8_t v_res_2344_; lean_object* v_r_2345_; 
v_res_2344_ = l_Std_Http_instBEqURI_beq(v_x_2342_, v_x_2343_);
lean_dec_ref(v_x_2343_);
lean_dec_ref(v_x_2342_);
v_r_2345_ = lean_box(v_res_2344_);
return v_r_2345_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__1(lean_object* v___f_2350_, lean_object* v_uri_2351_){
_start:
{
lean_object* v_scheme_2352_; lean_object* v_authority_2353_; lean_object* v_path_2354_; lean_object* v_query_2355_; lean_object* v_fragment_2356_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2379_; 
v_scheme_2352_ = lean_ctor_get(v_uri_2351_, 0);
lean_inc_ref(v_scheme_2352_);
v_authority_2353_ = lean_ctor_get(v_uri_2351_, 1);
lean_inc(v_authority_2353_);
v_path_2354_ = lean_ctor_get(v_uri_2351_, 2);
lean_inc_ref(v_path_2354_);
v_query_2355_ = lean_ctor_get(v_uri_2351_, 3);
lean_inc(v_query_2355_);
v_fragment_2356_ = lean_ctor_get(v_uri_2351_, 4);
lean_inc(v_fragment_2356_);
lean_dec_ref(v_uri_2351_);
if (lean_obj_tag(v_authority_2353_) == 0)
{
lean_object* v___x_2390_; 
v___x_2390_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2379_ = v___x_2390_;
goto v___jp_2378_;
}
else
{
lean_object* v_val_2391_; lean_object* v_userInfo_2392_; lean_object* v_host_2393_; lean_object* v_port_2394_; lean_object* v___x_2395_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2414_; 
v_val_2391_ = lean_ctor_get(v_authority_2353_, 0);
lean_inc(v_val_2391_);
lean_dec_ref_known(v_authority_2353_, 1);
v_userInfo_2392_ = lean_ctor_get(v_val_2391_, 0);
lean_inc(v_userInfo_2392_);
v_host_2393_ = lean_ctor_get(v_val_2391_, 1);
lean_inc_ref(v_host_2393_);
v_port_2394_ = lean_ctor_get(v_val_2391_, 2);
lean_inc(v_port_2394_);
lean_dec(v_val_2391_);
v___x_2395_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_2392_) == 0)
{
lean_object* v___x_2424_; 
v___x_2424_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2414_ = v___x_2424_;
goto v___jp_2413_;
}
else
{
lean_object* v_val_2425_; lean_object* v_password_2426_; 
v_val_2425_ = lean_ctor_get(v_userInfo_2392_, 0);
lean_inc(v_val_2425_);
lean_dec_ref_known(v_userInfo_2392_, 1);
v_password_2426_ = lean_ctor_get(v_val_2425_, 1);
if (lean_obj_tag(v_password_2426_) == 0)
{
lean_object* v_username_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v_username_2427_ = lean_ctor_get(v_val_2425_, 0);
lean_inc_ref(v_username_2427_);
lean_dec(v_val_2425_);
v___x_2428_ = lean_string_from_utf8_unchecked(v_username_2427_);
v___x_2429_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2430_ = lean_string_append(v___x_2428_, v___x_2429_);
v___y_2414_ = v___x_2430_;
goto v___jp_2413_;
}
else
{
lean_object* v_username_2431_; lean_object* v_val_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
lean_inc_ref(v_password_2426_);
v_username_2431_ = lean_ctor_get(v_val_2425_, 0);
lean_inc_ref(v_username_2431_);
lean_dec(v_val_2425_);
v_val_2432_ = lean_ctor_get(v_password_2426_, 0);
lean_inc(v_val_2432_);
lean_dec_ref_known(v_password_2426_, 1);
v___x_2433_ = lean_string_from_utf8_unchecked(v_username_2431_);
v___x_2434_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2435_ = lean_string_append(v___x_2433_, v___x_2434_);
v___x_2436_ = lean_string_from_utf8_unchecked(v_val_2432_);
v___x_2437_ = lean_string_append(v___x_2435_, v___x_2436_);
lean_dec_ref(v___x_2436_);
v___x_2438_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2439_ = lean_string_append(v___x_2437_, v___x_2438_);
v___y_2414_ = v___x_2439_;
goto v___jp_2413_;
}
}
v___jp_2396_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2400_ = lean_string_append(v___y_2398_, v___y_2397_);
lean_dec_ref(v___y_2397_);
v___x_2401_ = lean_string_append(v___x_2400_, v___y_2399_);
lean_dec_ref(v___y_2399_);
v___x_2402_ = lean_string_append(v___x_2395_, v___x_2401_);
lean_dec_ref(v___x_2401_);
v___y_2379_ = v___x_2402_;
goto v___jp_2378_;
}
v___jp_2403_:
{
switch(lean_obj_tag(v_port_2394_))
{
case 0:
{
lean_object* v___x_2406_; 
v___x_2406_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2397_ = v___y_2405_;
v___y_2398_ = v___y_2404_;
v___y_2399_ = v___x_2406_;
goto v___jp_2396_;
}
case 1:
{
lean_object* v___x_2407_; 
v___x_2407_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_2397_ = v___y_2405_;
v___y_2398_ = v___y_2404_;
v___y_2399_ = v___x_2407_;
goto v___jp_2396_;
}
default: 
{
uint16_t v_port_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v_port_2408_ = lean_ctor_get_uint16(v_port_2394_, 0);
lean_dec_ref_known(v_port_2394_, 0);
v___x_2409_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2410_ = lean_uint16_to_nat(v_port_2408_);
v___x_2411_ = l_Nat_reprFast(v___x_2410_);
v___x_2412_ = lean_string_append(v___x_2409_, v___x_2411_);
lean_dec_ref(v___x_2411_);
v___y_2397_ = v___y_2405_;
v___y_2398_ = v___y_2404_;
v___y_2399_ = v___x_2412_;
goto v___jp_2396_;
}
}
}
v___jp_2413_:
{
switch(lean_obj_tag(v_host_2393_))
{
case 0:
{
lean_object* v_name_2415_; 
v_name_2415_ = lean_ctor_get(v_host_2393_, 0);
lean_inc_ref(v_name_2415_);
lean_dec_ref_known(v_host_2393_, 1);
v___y_2404_ = v___y_2414_;
v___y_2405_ = v_name_2415_;
goto v___jp_2403_;
}
case 1:
{
lean_object* v_ipv4_2416_; lean_object* v___x_2417_; 
v_ipv4_2416_ = lean_ctor_get(v_host_2393_, 0);
lean_inc_ref(v_ipv4_2416_);
lean_dec_ref_known(v_host_2393_, 1);
v___x_2417_ = lean_uv_ntop_v4(v_ipv4_2416_);
lean_dec_ref(v_ipv4_2416_);
v___y_2404_ = v___y_2414_;
v___y_2405_ = v___x_2417_;
goto v___jp_2403_;
}
default: 
{
lean_object* v_ipv6_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v_ipv6_2418_ = lean_ctor_get(v_host_2393_, 0);
lean_inc_ref(v_ipv6_2418_);
lean_dec_ref_known(v_host_2393_, 1);
v___x_2419_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_2420_ = lean_uv_ntop_v6(v_ipv6_2418_);
lean_dec_ref(v_ipv6_2418_);
v___x_2421_ = lean_string_append(v___x_2419_, v___x_2420_);
lean_dec_ref(v___x_2420_);
v___x_2422_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_2423_ = lean_string_append(v___x_2421_, v___x_2422_);
v___y_2404_ = v___y_2414_;
v___y_2405_ = v___x_2423_;
goto v___jp_2403_;
}
}
}
}
v___jp_2357_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2362_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2363_ = lean_string_append(v_scheme_2352_, v___x_2362_);
v___x_2364_ = lean_string_append(v___x_2363_, v___y_2360_);
lean_dec_ref(v___y_2360_);
v___x_2365_ = lean_string_append(v___x_2364_, v___y_2358_);
lean_dec_ref(v___y_2358_);
v___x_2366_ = lean_string_append(v___x_2365_, v___y_2359_);
lean_dec_ref(v___y_2359_);
v___x_2367_ = lean_string_append(v___x_2366_, v___y_2361_);
lean_dec_ref(v___y_2361_);
return v___x_2367_;
}
v___jp_2368_:
{
lean_object* v_queryPart_2371_; 
v_queryPart_2371_ = l_Std_Http_URI_Query_formatOption(v_query_2355_);
if (lean_obj_tag(v_fragment_2356_) == 0)
{
lean_object* v___x_2372_; 
v___x_2372_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2358_ = v___y_2370_;
v___y_2359_ = v_queryPart_2371_;
v___y_2360_ = v___y_2369_;
v___y_2361_ = v___x_2372_;
goto v___jp_2357_;
}
else
{
lean_object* v_val_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v_val_2373_ = lean_ctor_get(v_fragment_2356_, 0);
lean_inc(v_val_2373_);
lean_dec_ref_known(v_fragment_2356_, 1);
v___x_2374_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_2375_ = l_Std_Http_URI_EncodedFragment_encode(v_val_2373_);
lean_dec(v_val_2373_);
v___x_2376_ = lean_string_from_utf8_unchecked(v___x_2375_);
v___x_2377_ = lean_string_append(v___x_2374_, v___x_2376_);
lean_dec_ref(v___x_2376_);
v___y_2358_ = v___y_2370_;
v___y_2359_ = v_queryPart_2371_;
v___y_2360_ = v___y_2369_;
v___y_2361_ = v___x_2377_;
goto v___jp_2357_;
}
}
v___jp_2378_:
{
lean_object* v_segments_2380_; uint8_t v_absolute_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; size_t v_sz_2384_; size_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v_result_2388_; 
v_segments_2380_ = lean_ctor_get(v_path_2354_, 0);
lean_inc_ref(v_segments_2380_);
v_absolute_2381_ = lean_ctor_get_uint8(v_path_2354_, sizeof(void*)*1);
lean_dec_ref(v_path_2354_);
v___x_2382_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_2383_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_2384_ = lean_array_size(v_segments_2380_);
v___x_2385_ = ((size_t)0ULL);
v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2383_, v___f_2350_, v_sz_2384_, v___x_2385_, v_segments_2380_);
v___x_2387_ = lean_array_to_list(v___x_2386_);
v_result_2388_ = l_String_intercalate(v___x_2382_, v___x_2387_);
if (v_absolute_2381_ == 0)
{
v___y_2369_ = v___y_2379_;
v___y_2370_ = v_result_2388_;
goto v___jp_2368_;
}
else
{
lean_object* v___x_2389_; 
v___x_2389_ = lean_string_append(v___x_2382_, v_result_2388_);
lean_dec_ref(v_result_2388_);
v___y_2369_ = v___y_2379_;
v___y_2370_ = v___x_2389_;
goto v___jp_2368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x3f(lean_object* v_b_2452_, lean_object* v_scheme_2453_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Std_Http_URI_Scheme_ofString_x3f(v_scheme_2453_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v___x_2455_; 
lean_dec_ref(v_b_2452_);
v___x_2455_ = lean_box(0);
return v___x_2455_;
}
else
{
lean_object* v_userInfo_2456_; lean_object* v_host_2457_; lean_object* v_port_2458_; lean_object* v_pathSegments_2459_; lean_object* v_query_2460_; lean_object* v_fragment_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2476_; 
v_userInfo_2456_ = lean_ctor_get(v_b_2452_, 1);
v_host_2457_ = lean_ctor_get(v_b_2452_, 2);
v_port_2458_ = lean_ctor_get(v_b_2452_, 3);
v_pathSegments_2459_ = lean_ctor_get(v_b_2452_, 4);
v_query_2460_ = lean_ctor_get(v_b_2452_, 5);
v_fragment_2461_ = lean_ctor_get(v_b_2452_, 6);
v_isSharedCheck_2476_ = !lean_is_exclusive(v_b_2452_);
if (v_isSharedCheck_2476_ == 0)
{
lean_object* v_unused_2477_; 
v_unused_2477_ = lean_ctor_get(v_b_2452_, 0);
lean_dec(v_unused_2477_);
v___x_2463_ = v_b_2452_;
v_isShared_2464_ = v_isSharedCheck_2476_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_fragment_2461_);
lean_inc(v_query_2460_);
lean_inc(v_pathSegments_2459_);
lean_inc(v_port_2458_);
lean_inc(v_host_2457_);
lean_inc(v_userInfo_2456_);
lean_dec(v_b_2452_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2476_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
lean_inc_ref(v___x_2454_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v___x_2454_);
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_userInfo_2456_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_host_2457_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_port_2458_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v_pathSegments_2459_);
lean_ctor_set(v_reuseFailAlloc_2475_, 5, v_query_2460_);
lean_ctor_set(v_reuseFailAlloc_2475_, 6, v_fragment_2461_);
v___x_2466_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2473_ == 0)
{
lean_object* v_unused_2474_; 
v_unused_2474_ = lean_ctor_get(v___x_2454_, 0);
lean_dec(v_unused_2474_);
v___x_2468_ = v___x_2454_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_dec(v___x_2454_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v___x_2466_);
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(lean_object* v_msg_2478_){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = ((lean_object*)(l_Std_Http_URI_instInhabitedBuilder_default));
v___x_2480_ = lean_panic_fn_borrowed(v___x_2479_, v_msg_2478_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x21(lean_object* v_b_2482_, lean_object* v_scheme_2483_){
_start:
{
lean_object* v___x_2484_; 
lean_inc_ref(v_scheme_2483_);
v___x_2484_ = l_Std_Http_URI_Builder_setScheme_x3f(v_b_2482_, v_scheme_2483_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2485_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2486_ = ((lean_object*)(l_Std_Http_URI_Builder_setScheme_x21___closed__0));
v___x_2487_ = lean_unsigned_to_nat(687u);
v___x_2488_ = lean_unsigned_to_nat(14u);
v___x_2489_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_2490_ = l_String_quote(v_scheme_2483_);
v___x_2491_ = lean_string_append(v___x_2489_, v___x_2490_);
lean_dec_ref(v___x_2490_);
v___x_2492_ = l_mkPanicMessageWithDecl(v___x_2485_, v___x_2486_, v___x_2487_, v___x_2488_, v___x_2491_);
lean_dec_ref(v___x_2491_);
v___x_2493_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2492_);
return v___x_2493_;
}
else
{
lean_object* v_val_2494_; 
lean_dec_ref(v_scheme_2483_);
v_val_2494_ = lean_ctor_get(v___x_2484_, 0);
lean_inc(v_val_2494_);
lean_dec_ref_known(v___x_2484_, 1);
return v_val_2494_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo(lean_object* v_b_2495_, lean_object* v_username_2496_, lean_object* v_password_2497_){
_start:
{
lean_object* v_scheme_2498_; lean_object* v_host_2499_; lean_object* v_port_2500_; lean_object* v_pathSegments_2501_; lean_object* v_query_2502_; lean_object* v_fragment_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2526_; 
v_scheme_2498_ = lean_ctor_get(v_b_2495_, 0);
v_host_2499_ = lean_ctor_get(v_b_2495_, 2);
v_port_2500_ = lean_ctor_get(v_b_2495_, 3);
v_pathSegments_2501_ = lean_ctor_get(v_b_2495_, 4);
v_query_2502_ = lean_ctor_get(v_b_2495_, 5);
v_fragment_2503_ = lean_ctor_get(v_b_2495_, 6);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_b_2495_);
if (v_isSharedCheck_2526_ == 0)
{
lean_object* v_unused_2527_; 
v_unused_2527_ = lean_ctor_get(v_b_2495_, 1);
lean_dec(v_unused_2527_);
v___x_2505_ = v_b_2495_;
v_isShared_2506_ = v_isSharedCheck_2526_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_fragment_2503_);
lean_inc(v_query_2502_);
lean_inc(v_pathSegments_2501_);
lean_inc(v_port_2500_);
lean_inc(v_host_2499_);
lean_inc(v_scheme_2498_);
lean_dec(v_b_2495_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2526_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___y_2508_; lean_object* v___x_2513_; 
v___x_2513_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_2496_);
if (lean_obj_tag(v_password_2497_) == 0)
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = lean_box(0);
v___x_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
v___y_2508_ = v___x_2515_;
goto v___jp_2507_;
}
else
{
lean_object* v_val_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2525_; 
v_val_2516_ = lean_ctor_get(v_password_2497_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_password_2497_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2518_ = v_password_2497_;
v_isShared_2519_ = v_isSharedCheck_2525_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_val_2516_);
lean_dec(v_password_2497_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2525_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; lean_object* v___x_2522_; 
v___x_2520_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_2516_);
lean_dec(v_val_2516_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2520_);
v___x_2522_ = v___x_2518_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2520_);
v___x_2522_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2523_; 
v___x_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2513_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___y_2508_ = v___x_2523_;
goto v___jp_2507_;
}
}
}
v___jp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2509_, 0, v___y_2508_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 1, v___x_2509_);
v___x_2511_ = v___x_2505_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_scheme_2498_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2512_, 2, v_host_2499_);
lean_ctor_set(v_reuseFailAlloc_2512_, 3, v_port_2500_);
lean_ctor_set(v_reuseFailAlloc_2512_, 4, v_pathSegments_2501_);
lean_ctor_set(v_reuseFailAlloc_2512_, 5, v_query_2502_);
lean_ctor_set(v_reuseFailAlloc_2512_, 6, v_fragment_2503_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo___boxed(lean_object* v_b_2528_, lean_object* v_username_2529_, lean_object* v_password_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Std_Http_URI_Builder_setUserInfo(v_b_2528_, v_username_2529_, v_password_2530_);
lean_dec_ref(v_username_2529_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x3f(lean_object* v_b_2532_, lean_object* v_name_2533_){
_start:
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Std_Http_URI_DomainName_ofString_x3f(v_name_2533_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v___x_2535_; 
lean_dec_ref(v_b_2532_);
v___x_2535_ = lean_box(0);
return v___x_2535_;
}
else
{
lean_object* v_val_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2559_; 
v_val_2536_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2538_ = v___x_2534_;
v_isShared_2539_ = v_isSharedCheck_2559_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_val_2536_);
lean_dec(v___x_2534_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2559_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v_scheme_2540_; lean_object* v_userInfo_2541_; lean_object* v_port_2542_; lean_object* v_pathSegments_2543_; lean_object* v_query_2544_; lean_object* v_fragment_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2557_; 
v_scheme_2540_ = lean_ctor_get(v_b_2532_, 0);
v_userInfo_2541_ = lean_ctor_get(v_b_2532_, 1);
v_port_2542_ = lean_ctor_get(v_b_2532_, 3);
v_pathSegments_2543_ = lean_ctor_get(v_b_2532_, 4);
v_query_2544_ = lean_ctor_get(v_b_2532_, 5);
v_fragment_2545_ = lean_ctor_get(v_b_2532_, 6);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_b_2532_);
if (v_isSharedCheck_2557_ == 0)
{
lean_object* v_unused_2558_; 
v_unused_2558_ = lean_ctor_get(v_b_2532_, 2);
lean_dec(v_unused_2558_);
v___x_2547_ = v_b_2532_;
v_isShared_2548_ = v_isSharedCheck_2557_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_fragment_2545_);
lean_inc(v_query_2544_);
lean_inc(v_pathSegments_2543_);
lean_inc(v_port_2542_);
lean_inc(v_userInfo_2541_);
lean_inc(v_scheme_2540_);
lean_dec(v_b_2532_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2557_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2549_, 0, v_val_2536_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 0, v___x_2549_);
v___x_2551_ = v___x_2538_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2553_; 
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 2, v___x_2551_);
v___x_2553_ = v___x_2547_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_scheme_2540_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_userInfo_2541_);
lean_ctor_set(v_reuseFailAlloc_2555_, 2, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2555_, 3, v_port_2542_);
lean_ctor_set(v_reuseFailAlloc_2555_, 4, v_pathSegments_2543_);
lean_ctor_set(v_reuseFailAlloc_2555_, 5, v_query_2544_);
lean_ctor_set(v_reuseFailAlloc_2555_, 6, v_fragment_2545_);
v___x_2553_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
return v___x_2554_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x21(lean_object* v_b_2562_, lean_object* v_name_2563_){
_start:
{
lean_object* v___x_2564_; 
lean_inc_ref(v_name_2563_);
v___x_2564_ = l_Std_Http_URI_Builder_setHost_x3f(v_b_2562_, v_name_2563_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2565_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2566_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__0));
v___x_2567_ = lean_unsigned_to_nat(716u);
v___x_2568_ = lean_unsigned_to_nat(14u);
v___x_2569_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__1));
v___x_2570_ = l_String_quote(v_name_2563_);
v___x_2571_ = lean_string_append(v___x_2569_, v___x_2570_);
lean_dec_ref(v___x_2570_);
v___x_2572_ = l_mkPanicMessageWithDecl(v___x_2565_, v___x_2566_, v___x_2567_, v___x_2568_, v___x_2571_);
lean_dec_ref(v___x_2571_);
v___x_2573_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2572_);
return v___x_2573_;
}
else
{
lean_object* v_val_2574_; 
lean_dec_ref(v_name_2563_);
v_val_2574_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_val_2574_);
lean_dec_ref_known(v___x_2564_, 1);
return v_val_2574_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv4(lean_object* v_b_2575_, lean_object* v_addr_2576_){
_start:
{
lean_object* v_scheme_2577_; lean_object* v_userInfo_2578_; lean_object* v_port_2579_; lean_object* v_pathSegments_2580_; lean_object* v_query_2581_; lean_object* v_fragment_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2591_; 
v_scheme_2577_ = lean_ctor_get(v_b_2575_, 0);
v_userInfo_2578_ = lean_ctor_get(v_b_2575_, 1);
v_port_2579_ = lean_ctor_get(v_b_2575_, 3);
v_pathSegments_2580_ = lean_ctor_get(v_b_2575_, 4);
v_query_2581_ = lean_ctor_get(v_b_2575_, 5);
v_fragment_2582_ = lean_ctor_get(v_b_2575_, 6);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_b_2575_);
if (v_isSharedCheck_2591_ == 0)
{
lean_object* v_unused_2592_; 
v_unused_2592_ = lean_ctor_get(v_b_2575_, 2);
lean_dec(v_unused_2592_);
v___x_2584_ = v_b_2575_;
v_isShared_2585_ = v_isSharedCheck_2591_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_fragment_2582_);
lean_inc(v_query_2581_);
lean_inc(v_pathSegments_2580_);
lean_inc(v_port_2579_);
lean_inc(v_userInfo_2578_);
lean_inc(v_scheme_2577_);
lean_dec(v_b_2575_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2591_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2589_; 
v___x_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_addr_2576_);
v___x_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 2, v___x_2587_);
v___x_2589_ = v___x_2584_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_scheme_2577_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_userInfo_2578_);
lean_ctor_set(v_reuseFailAlloc_2590_, 2, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2590_, 3, v_port_2579_);
lean_ctor_set(v_reuseFailAlloc_2590_, 4, v_pathSegments_2580_);
lean_ctor_set(v_reuseFailAlloc_2590_, 5, v_query_2581_);
lean_ctor_set(v_reuseFailAlloc_2590_, 6, v_fragment_2582_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv6(lean_object* v_b_2593_, lean_object* v_addr_2594_){
_start:
{
lean_object* v_scheme_2595_; lean_object* v_userInfo_2596_; lean_object* v_port_2597_; lean_object* v_pathSegments_2598_; lean_object* v_query_2599_; lean_object* v_fragment_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2609_; 
v_scheme_2595_ = lean_ctor_get(v_b_2593_, 0);
v_userInfo_2596_ = lean_ctor_get(v_b_2593_, 1);
v_port_2597_ = lean_ctor_get(v_b_2593_, 3);
v_pathSegments_2598_ = lean_ctor_get(v_b_2593_, 4);
v_query_2599_ = lean_ctor_get(v_b_2593_, 5);
v_fragment_2600_ = lean_ctor_get(v_b_2593_, 6);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_b_2593_);
if (v_isSharedCheck_2609_ == 0)
{
lean_object* v_unused_2610_; 
v_unused_2610_ = lean_ctor_get(v_b_2593_, 2);
lean_dec(v_unused_2610_);
v___x_2602_ = v_b_2593_;
v_isShared_2603_ = v_isSharedCheck_2609_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_fragment_2600_);
lean_inc(v_query_2599_);
lean_inc(v_pathSegments_2598_);
lean_inc(v_port_2597_);
lean_inc(v_userInfo_2596_);
lean_inc(v_scheme_2595_);
lean_dec(v_b_2593_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2609_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2607_; 
v___x_2604_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2604_, 0, v_addr_2594_);
v___x_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 2, v___x_2605_);
v___x_2607_ = v___x_2602_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_scheme_2595_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v_userInfo_2596_);
lean_ctor_set(v_reuseFailAlloc_2608_, 2, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2608_, 3, v_port_2597_);
lean_ctor_set(v_reuseFailAlloc_2608_, 4, v_pathSegments_2598_);
lean_ctor_set(v_reuseFailAlloc_2608_, 5, v_query_2599_);
lean_ctor_set(v_reuseFailAlloc_2608_, 6, v_fragment_2600_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
lean_object* l_Std_Http_URI_Builder_setPort(lean_object* v_b_2611_, uint16_t v_port_2612_){
_start:
{
lean_object* v_scheme_2613_; lean_object* v_userInfo_2614_; lean_object* v_host_2615_; lean_object* v_pathSegments_2616_; lean_object* v_query_2617_; lean_object* v_fragment_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2626_; 
v_scheme_2613_ = lean_ctor_get(v_b_2611_, 0);
v_userInfo_2614_ = lean_ctor_get(v_b_2611_, 1);
v_host_2615_ = lean_ctor_get(v_b_2611_, 2);
v_pathSegments_2616_ = lean_ctor_get(v_b_2611_, 4);
v_query_2617_ = lean_ctor_get(v_b_2611_, 5);
v_fragment_2618_ = lean_ctor_get(v_b_2611_, 6);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_b_2611_);
if (v_isSharedCheck_2626_ == 0)
{
lean_object* v_unused_2627_; 
v_unused_2627_ = lean_ctor_get(v_b_2611_, 3);
lean_dec(v_unused_2627_);
v___x_2620_ = v_b_2611_;
v_isShared_2621_ = v_isSharedCheck_2626_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_fragment_2618_);
lean_inc(v_query_2617_);
lean_inc(v_pathSegments_2616_);
lean_inc(v_host_2615_);
lean_inc(v_userInfo_2614_);
lean_inc(v_scheme_2613_);
lean_dec(v_b_2611_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2626_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v___x_2624_; 
v___x_2622_ = lean_alloc_ctor(2, 0, 2);
lean_ctor_set_uint16(v___x_2622_, 0, v_port_2612_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 3, v___x_2622_);
v___x_2624_ = v___x_2620_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_scheme_2613_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_userInfo_2614_);
lean_ctor_set(v_reuseFailAlloc_2625_, 2, v_host_2615_);
lean_ctor_set(v_reuseFailAlloc_2625_, 3, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2625_, 4, v_pathSegments_2616_);
lean_ctor_set(v_reuseFailAlloc_2625_, 5, v_query_2617_);
lean_ctor_set(v_reuseFailAlloc_2625_, 6, v_fragment_2618_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_Builder_setPort_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_2611_ = stack[0].m_obj;
uint16_t v_port_2612_ = stack[1].m_num;
lean_object* v_res_2628_;
v_res_2628_ = l_Std_Http_URI_Builder_setPort(v_b_2611_, v_port_2612_);
stack->m_obj
 = v_res_2628_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort___boxed(lean_object* v_b_2629_, lean_object* v_port_2630_){
_start:
{
uint16_t v_port_boxed_2631_; lean_object* v_res_2632_; 
v_port_boxed_2631_ = lean_unbox(v_port_2630_);
v_res_2632_ = l_Std_Http_URI_Builder_setPort(v_b_2629_, v_port_boxed_2631_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPath(lean_object* v_b_2633_, lean_object* v_segments_2634_){
_start:
{
lean_object* v_scheme_2635_; lean_object* v_userInfo_2636_; lean_object* v_host_2637_; lean_object* v_port_2638_; lean_object* v_query_2639_; lean_object* v_fragment_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
v_scheme_2635_ = lean_ctor_get(v_b_2633_, 0);
v_userInfo_2636_ = lean_ctor_get(v_b_2633_, 1);
v_host_2637_ = lean_ctor_get(v_b_2633_, 2);
v_port_2638_ = lean_ctor_get(v_b_2633_, 3);
v_query_2639_ = lean_ctor_get(v_b_2633_, 5);
v_fragment_2640_ = lean_ctor_get(v_b_2633_, 6);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_b_2633_);
if (v_isSharedCheck_2647_ == 0)
{
lean_object* v_unused_2648_; 
v_unused_2648_ = lean_ctor_get(v_b_2633_, 4);
lean_dec(v_unused_2648_);
v___x_2642_ = v_b_2633_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_fragment_2640_);
lean_inc(v_query_2639_);
lean_inc(v_port_2638_);
lean_inc(v_host_2637_);
lean_inc(v_userInfo_2636_);
lean_inc(v_scheme_2635_);
lean_dec(v_b_2633_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 4, v_segments_2634_);
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_scheme_2635_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_userInfo_2636_);
lean_ctor_set(v_reuseFailAlloc_2646_, 2, v_host_2637_);
lean_ctor_set(v_reuseFailAlloc_2646_, 3, v_port_2638_);
lean_ctor_set(v_reuseFailAlloc_2646_, 4, v_segments_2634_);
lean_ctor_set(v_reuseFailAlloc_2646_, 5, v_query_2639_);
lean_ctor_set(v_reuseFailAlloc_2646_, 6, v_fragment_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_appendPathSegment(lean_object* v_b_2649_, lean_object* v_segment_2650_){
_start:
{
lean_object* v_scheme_2651_; lean_object* v_userInfo_2652_; lean_object* v_host_2653_; lean_object* v_port_2654_; lean_object* v_pathSegments_2655_; lean_object* v_query_2656_; lean_object* v_fragment_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2665_; 
v_scheme_2651_ = lean_ctor_get(v_b_2649_, 0);
v_userInfo_2652_ = lean_ctor_get(v_b_2649_, 1);
v_host_2653_ = lean_ctor_get(v_b_2649_, 2);
v_port_2654_ = lean_ctor_get(v_b_2649_, 3);
v_pathSegments_2655_ = lean_ctor_get(v_b_2649_, 4);
v_query_2656_ = lean_ctor_get(v_b_2649_, 5);
v_fragment_2657_ = lean_ctor_get(v_b_2649_, 6);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_b_2649_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2659_ = v_b_2649_;
v_isShared_2660_ = v_isSharedCheck_2665_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_fragment_2657_);
lean_inc(v_query_2656_);
lean_inc(v_pathSegments_2655_);
lean_inc(v_port_2654_);
lean_inc(v_host_2653_);
lean_inc(v_userInfo_2652_);
lean_inc(v_scheme_2651_);
lean_dec(v_b_2649_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2665_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; lean_object* v___x_2663_; 
v___x_2661_ = lean_array_push(v_pathSegments_2655_, v_segment_2650_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 4, v___x_2661_);
v___x_2663_ = v___x_2659_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_scheme_2651_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_userInfo_2652_);
lean_ctor_set(v_reuseFailAlloc_2664_, 2, v_host_2653_);
lean_ctor_set(v_reuseFailAlloc_2664_, 3, v_port_2654_);
lean_ctor_set(v_reuseFailAlloc_2664_, 4, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2664_, 5, v_query_2656_);
lean_ctor_set(v_reuseFailAlloc_2664_, 6, v_fragment_2657_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryParam(lean_object* v_b_2666_, lean_object* v_key_2667_, lean_object* v_value_2668_){
_start:
{
lean_object* v_scheme_2669_; lean_object* v_userInfo_2670_; lean_object* v_host_2671_; lean_object* v_port_2672_; lean_object* v_pathSegments_2673_; lean_object* v_query_2674_; lean_object* v_fragment_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2685_; 
v_scheme_2669_ = lean_ctor_get(v_b_2666_, 0);
v_userInfo_2670_ = lean_ctor_get(v_b_2666_, 1);
v_host_2671_ = lean_ctor_get(v_b_2666_, 2);
v_port_2672_ = lean_ctor_get(v_b_2666_, 3);
v_pathSegments_2673_ = lean_ctor_get(v_b_2666_, 4);
v_query_2674_ = lean_ctor_get(v_b_2666_, 5);
v_fragment_2675_ = lean_ctor_get(v_b_2666_, 6);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_b_2666_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2677_ = v_b_2666_;
v_isShared_2678_ = v_isSharedCheck_2685_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_fragment_2675_);
lean_inc(v_query_2674_);
lean_inc(v_pathSegments_2673_);
lean_inc(v_port_2672_);
lean_inc(v_host_2671_);
lean_inc(v_userInfo_2670_);
lean_inc(v_scheme_2669_);
lean_dec(v_b_2666_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2685_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_value_2668_);
v___x_2680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2680_, 0, v_key_2667_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = lean_array_push(v_query_2674_, v___x_2680_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 5, v___x_2681_);
v___x_2683_ = v___x_2677_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_scheme_2669_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_userInfo_2670_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v_host_2671_);
lean_ctor_set(v_reuseFailAlloc_2684_, 3, v_port_2672_);
lean_ctor_set(v_reuseFailAlloc_2684_, 4, v_pathSegments_2673_);
lean_ctor_set(v_reuseFailAlloc_2684_, 5, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2684_, 6, v_fragment_2675_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryFlag(lean_object* v_b_2686_, lean_object* v_key_2687_){
_start:
{
lean_object* v_scheme_2688_; lean_object* v_userInfo_2689_; lean_object* v_host_2690_; lean_object* v_port_2691_; lean_object* v_pathSegments_2692_; lean_object* v_query_2693_; lean_object* v_fragment_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2704_; 
v_scheme_2688_ = lean_ctor_get(v_b_2686_, 0);
v_userInfo_2689_ = lean_ctor_get(v_b_2686_, 1);
v_host_2690_ = lean_ctor_get(v_b_2686_, 2);
v_port_2691_ = lean_ctor_get(v_b_2686_, 3);
v_pathSegments_2692_ = lean_ctor_get(v_b_2686_, 4);
v_query_2693_ = lean_ctor_get(v_b_2686_, 5);
v_fragment_2694_ = lean_ctor_get(v_b_2686_, 6);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_b_2686_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2696_ = v_b_2686_;
v_isShared_2697_ = v_isSharedCheck_2704_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_fragment_2694_);
lean_inc(v_query_2693_);
lean_inc(v_pathSegments_2692_);
lean_inc(v_port_2691_);
lean_inc(v_host_2690_);
lean_inc(v_userInfo_2689_);
lean_inc(v_scheme_2688_);
lean_dec(v_b_2686_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2704_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2698_ = lean_box(0);
v___x_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2699_, 0, v_key_2687_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = lean_array_push(v_query_2693_, v___x_2699_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 5, v___x_2700_);
v___x_2702_ = v___x_2696_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_scheme_2688_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v_userInfo_2689_);
lean_ctor_set(v_reuseFailAlloc_2703_, 2, v_host_2690_);
lean_ctor_set(v_reuseFailAlloc_2703_, 3, v_port_2691_);
lean_ctor_set(v_reuseFailAlloc_2703_, 4, v_pathSegments_2692_);
lean_ctor_set(v_reuseFailAlloc_2703_, 5, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2703_, 6, v_fragment_2694_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setQuery(lean_object* v_b_2705_, lean_object* v_query_2706_){
_start:
{
lean_object* v_scheme_2707_; lean_object* v_userInfo_2708_; lean_object* v_host_2709_; lean_object* v_port_2710_; lean_object* v_pathSegments_2711_; lean_object* v_fragment_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
v_scheme_2707_ = lean_ctor_get(v_b_2705_, 0);
v_userInfo_2708_ = lean_ctor_get(v_b_2705_, 1);
v_host_2709_ = lean_ctor_get(v_b_2705_, 2);
v_port_2710_ = lean_ctor_get(v_b_2705_, 3);
v_pathSegments_2711_ = lean_ctor_get(v_b_2705_, 4);
v_fragment_2712_ = lean_ctor_get(v_b_2705_, 6);
v_isSharedCheck_2719_ = !lean_is_exclusive(v_b_2705_);
if (v_isSharedCheck_2719_ == 0)
{
lean_object* v_unused_2720_; 
v_unused_2720_ = lean_ctor_get(v_b_2705_, 5);
lean_dec(v_unused_2720_);
v___x_2714_ = v_b_2705_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_fragment_2712_);
lean_inc(v_pathSegments_2711_);
lean_inc(v_port_2710_);
lean_inc(v_host_2709_);
lean_inc(v_userInfo_2708_);
lean_inc(v_scheme_2707_);
lean_dec(v_b_2705_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 5, v_query_2706_);
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_scheme_2707_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v_userInfo_2708_);
lean_ctor_set(v_reuseFailAlloc_2718_, 2, v_host_2709_);
lean_ctor_set(v_reuseFailAlloc_2718_, 3, v_port_2710_);
lean_ctor_set(v_reuseFailAlloc_2718_, 4, v_pathSegments_2711_);
lean_ctor_set(v_reuseFailAlloc_2718_, 5, v_query_2706_);
lean_ctor_set(v_reuseFailAlloc_2718_, 6, v_fragment_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setFragment(lean_object* v_b_2721_, lean_object* v_fragment_2722_){
_start:
{
lean_object* v_scheme_2723_; lean_object* v_userInfo_2724_; lean_object* v_host_2725_; lean_object* v_port_2726_; lean_object* v_pathSegments_2727_; lean_object* v_query_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2736_; 
v_scheme_2723_ = lean_ctor_get(v_b_2721_, 0);
v_userInfo_2724_ = lean_ctor_get(v_b_2721_, 1);
v_host_2725_ = lean_ctor_get(v_b_2721_, 2);
v_port_2726_ = lean_ctor_get(v_b_2721_, 3);
v_pathSegments_2727_ = lean_ctor_get(v_b_2721_, 4);
v_query_2728_ = lean_ctor_get(v_b_2721_, 5);
v_isSharedCheck_2736_ = !lean_is_exclusive(v_b_2721_);
if (v_isSharedCheck_2736_ == 0)
{
lean_object* v_unused_2737_; 
v_unused_2737_ = lean_ctor_get(v_b_2721_, 6);
lean_dec(v_unused_2737_);
v___x_2730_ = v_b_2721_;
v_isShared_2731_ = v_isSharedCheck_2736_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_query_2728_);
lean_inc(v_pathSegments_2727_);
lean_inc(v_port_2726_);
lean_inc(v_host_2725_);
lean_inc(v_userInfo_2724_);
lean_inc(v_scheme_2723_);
lean_dec(v_b_2721_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2736_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2732_, 0, v_fragment_2722_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 6, v___x_2732_);
v___x_2734_ = v___x_2730_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_scheme_2723_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_userInfo_2724_);
lean_ctor_set(v_reuseFailAlloc_2735_, 2, v_host_2725_);
lean_ctor_set(v_reuseFailAlloc_2735_, 3, v_port_2726_);
lean_ctor_set(v_reuseFailAlloc_2735_, 4, v_pathSegments_2727_);
lean_ctor_set(v_reuseFailAlloc_2735_, 5, v_query_2728_);
lean_ctor_set(v_reuseFailAlloc_2735_, 6, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(size_t v_sz_2738_, size_t v_i_2739_, lean_object* v_bs_2740_){
_start:
{
uint8_t v___x_2741_; 
v___x_2741_ = lean_usize_dec_lt(v_i_2739_, v_sz_2738_);
if (v___x_2741_ == 0)
{
return v_bs_2740_;
}
else
{
lean_object* v_v_2742_; lean_object* v___x_2743_; lean_object* v_bs_x27_2744_; lean_object* v___x_2745_; size_t v___x_2746_; size_t v___x_2747_; lean_object* v___x_2748_; 
v_v_2742_ = lean_array_uget(v_bs_2740_, v_i_2739_);
v___x_2743_ = lean_unsigned_to_nat(0u);
v_bs_x27_2744_ = lean_array_uset(v_bs_2740_, v_i_2739_, v___x_2743_);
v___x_2745_ = l_Std_Http_URI_EncodedSegment_encode(v_v_2742_);
lean_dec(v_v_2742_);
v___x_2746_ = ((size_t)1ULL);
v___x_2747_ = lean_usize_add(v_i_2739_, v___x_2746_);
v___x_2748_ = lean_array_uset(v_bs_x27_2744_, v_i_2739_, v___x_2745_);
v_i_2739_ = v___x_2747_;
v_bs_2740_ = v___x_2748_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2738_ = stack[0].m_num;
size_t v_i_2739_ = stack[1].m_num;
lean_object* v_bs_2740_ = stack[2].m_obj;
lean_object* v_res_2750_;
v_res_2750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_2738_, v_i_2739_, v_bs_2740_);
stack->m_obj
 = v_res_2750_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0___boxed(lean_object* v_sz_2751_, lean_object* v_i_2752_, lean_object* v_bs_2753_){
_start:
{
size_t v_sz_boxed_2754_; size_t v_i_boxed_2755_; lean_object* v_res_2756_; 
v_sz_boxed_2754_ = lean_unbox_usize(v_sz_2751_);
lean_dec(v_sz_2751_);
v_i_boxed_2755_ = lean_unbox_usize(v_i_2752_);
lean_dec(v_i_2752_);
v_res_2756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_boxed_2754_, v_i_boxed_2755_, v_bs_2753_);
return v_res_2756_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(size_t v_sz_2757_, size_t v_i_2758_, lean_object* v_bs_2759_){
_start:
{
uint8_t v___x_2760_; 
v___x_2760_ = lean_usize_dec_lt(v_i_2758_, v_sz_2757_);
if (v___x_2760_ == 0)
{
return v_bs_2759_;
}
else
{
lean_object* v_v_2761_; lean_object* v_fst_2762_; lean_object* v_snd_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2792_; 
v_v_2761_ = lean_array_uget(v_bs_2759_, v_i_2758_);
v_fst_2762_ = lean_ctor_get(v_v_2761_, 0);
v_snd_2763_ = lean_ctor_get(v_v_2761_, 1);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_v_2761_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2765_ = v_v_2761_;
v_isShared_2766_ = v_isSharedCheck_2792_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_snd_2763_);
lean_inc(v_fst_2762_);
lean_dec(v_v_2761_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2792_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2767_; lean_object* v_bs_x27_2768_; lean_object* v___y_2770_; lean_object* v___x_2775_; 
v___x_2767_ = lean_unsigned_to_nat(0u);
v_bs_x27_2768_ = lean_array_uset(v_bs_2759_, v_i_2758_, v___x_2767_);
v___x_2775_ = l_Std_Http_URI_EncodedQueryParam_encode(v_fst_2762_);
lean_dec(v_fst_2762_);
if (lean_obj_tag(v_snd_2763_) == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2776_ = lean_box(0);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 1, v___x_2776_);
lean_ctor_set(v___x_2765_, 0, v___x_2775_);
v___x_2778_ = v___x_2765_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2775_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
v___y_2770_ = v___x_2778_;
goto v___jp_2769_;
}
}
else
{
lean_object* v_val_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2791_; 
v_val_2780_ = lean_ctor_get(v_snd_2763_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_snd_2763_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2782_ = v_snd_2763_;
v_isShared_2783_ = v_isSharedCheck_2791_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_val_2780_);
lean_dec(v_snd_2763_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2791_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2784_ = l_Std_Http_URI_EncodedQueryParam_encode(v_val_2780_);
lean_dec(v_val_2780_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___x_2784_);
v___x_2786_ = v___x_2782_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2788_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 1, v___x_2786_);
lean_ctor_set(v___x_2765_, 0, v___x_2775_);
v___x_2788_ = v___x_2765_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2775_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
v___y_2770_ = v___x_2788_;
goto v___jp_2769_;
}
}
}
}
v___jp_2769_:
{
size_t v___x_2771_; size_t v___x_2772_; lean_object* v___x_2773_; 
v___x_2771_ = ((size_t)1ULL);
v___x_2772_ = lean_usize_add(v_i_2758_, v___x_2771_);
v___x_2773_ = lean_array_uset(v_bs_x27_2768_, v_i_2758_, v___y_2770_);
v_i_2758_ = v___x_2772_;
v_bs_2759_ = v___x_2773_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2757_ = stack[0].m_num;
size_t v_i_2758_ = stack[1].m_num;
lean_object* v_bs_2759_ = stack[2].m_obj;
lean_object* v_res_2793_;
v_res_2793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_2757_, v_i_2758_, v_bs_2759_);
stack->m_obj
 = v_res_2793_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1___boxed(lean_object* v_sz_2794_, lean_object* v_i_2795_, lean_object* v_bs_2796_){
_start:
{
size_t v_sz_boxed_2797_; size_t v_i_boxed_2798_; lean_object* v_res_2799_; 
v_sz_boxed_2797_ = lean_unbox_usize(v_sz_2794_);
lean_dec(v_sz_2794_);
v_i_boxed_2798_ = lean_unbox_usize(v_i_2795_);
lean_dec(v_i_2795_);
v_res_2799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_boxed_2797_, v_i_boxed_2798_, v_bs_2796_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_build(lean_object* v_b_2800_){
_start:
{
lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; uint8_t v___y_2806_; lean_object* v___y_2807_; lean_object* v_scheme_2823_; lean_object* v_userInfo_2824_; lean_object* v_host_2825_; lean_object* v_port_2826_; lean_object* v_pathSegments_2827_; lean_object* v_query_2828_; lean_object* v_fragment_2829_; lean_object* v___y_2831_; 
v_scheme_2823_ = lean_ctor_get(v_b_2800_, 0);
lean_inc(v_scheme_2823_);
v_userInfo_2824_ = lean_ctor_get(v_b_2800_, 1);
lean_inc(v_userInfo_2824_);
v_host_2825_ = lean_ctor_get(v_b_2800_, 2);
lean_inc(v_host_2825_);
v_port_2826_ = lean_ctor_get(v_b_2800_, 3);
lean_inc(v_port_2826_);
v_pathSegments_2827_ = lean_ctor_get(v_b_2800_, 4);
lean_inc_ref(v_pathSegments_2827_);
v_query_2828_ = lean_ctor_get(v_b_2800_, 5);
lean_inc_ref(v_query_2828_);
v_fragment_2829_ = lean_ctor_get(v_b_2800_, 6);
lean_inc(v_fragment_2829_);
lean_dec_ref(v_b_2800_);
if (lean_obj_tag(v_scheme_2823_) == 0)
{
lean_object* v___x_2844_; 
v___x_2844_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___y_2831_ = v___x_2844_;
goto v___jp_2830_;
}
else
{
lean_object* v_val_2845_; 
v_val_2845_ = lean_ctor_get(v_scheme_2823_, 0);
lean_inc(v_val_2845_);
lean_dec_ref_known(v_scheme_2823_, 1);
v___y_2831_ = v_val_2845_;
goto v___jp_2830_;
}
v___jp_2801_:
{
size_t v_sz_2808_; size_t v___x_2809_; lean_object* v___x_2810_; lean_object* v_path_2811_; size_t v_sz_2812_; lean_object* v_query_2813_; lean_object* v___x_2814_; lean_object* v_query_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; 
v_sz_2808_ = lean_array_size(v___y_2803_);
v___x_2809_ = ((size_t)0ULL);
v___x_2810_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_2808_, v___x_2809_, v___y_2803_);
v_path_2811_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_path_2811_, 0, v___x_2810_);
lean_ctor_set_uint8(v_path_2811_, sizeof(void*)*1, v___y_2806_);
v_sz_2812_ = lean_array_size(v___y_2804_);
v_query_2813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_2812_, v___x_2809_, v___y_2804_);
v___x_2814_ = lean_array_to_list(v_query_2813_);
v_query_2815_ = lean_array_mk(v___x_2814_);
v___x_2816_ = lean_array_get_size(v_query_2815_);
v___x_2817_ = lean_unsigned_to_nat(0u);
v___x_2818_ = lean_nat_dec_eq(v___x_2816_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2819_, 0, v_query_2815_);
v___x_2820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2820_, 0, v___y_2802_);
lean_ctor_set(v___x_2820_, 1, v___y_2807_);
lean_ctor_set(v___x_2820_, 2, v_path_2811_);
lean_ctor_set(v___x_2820_, 3, v___x_2819_);
lean_ctor_set(v___x_2820_, 4, v___y_2805_);
return v___x_2820_;
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
lean_dec_ref(v_query_2815_);
v___x_2821_ = lean_box(0);
v___x_2822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2822_, 0, v___y_2802_);
lean_ctor_set(v___x_2822_, 1, v___y_2807_);
lean_ctor_set(v___x_2822_, 2, v_path_2811_);
lean_ctor_set(v___x_2822_, 3, v___x_2821_);
lean_ctor_set(v___x_2822_, 4, v___y_2805_);
return v___x_2822_;
}
}
v___jp_2830_:
{
if (lean_obj_tag(v_host_2825_) == 0)
{
uint8_t v___x_2832_; lean_object* v___x_2833_; 
lean_dec(v_port_2826_);
lean_dec(v_userInfo_2824_);
v___x_2832_ = 1;
v___x_2833_ = lean_box(0);
v___y_2802_ = v___y_2831_;
v___y_2803_ = v_pathSegments_2827_;
v___y_2804_ = v_query_2828_;
v___y_2805_ = v_fragment_2829_;
v___y_2806_ = v___x_2832_;
v___y_2807_ = v___x_2833_;
goto v___jp_2801_;
}
else
{
lean_object* v_val_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2843_; 
v_val_2834_ = lean_ctor_get(v_host_2825_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v_host_2825_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2836_ = v_host_2825_;
v_isShared_2837_ = v_isSharedCheck_2843_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_val_2834_);
lean_dec(v_host_2825_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2843_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
uint8_t v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2838_ = 1;
v___x_2839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2839_, 0, v_userInfo_2824_);
lean_ctor_set(v___x_2839_, 1, v_val_2834_);
lean_ctor_set(v___x_2839_, 2, v_port_2826_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2839_);
v___x_2841_ = v___x_2836_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2839_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
v___y_2802_ = v___y_2831_;
v___y_2803_ = v_pathSegments_2827_;
v___y_2804_ = v_query_2828_;
v___y_2805_ = v_fragment_2829_;
v___y_2806_ = v___x_2838_;
v___y_2807_ = v___x_2841_;
goto v___jp_2801_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withScheme_x21(lean_object* v_uri_2846_, lean_object* v_scheme_2847_){
_start:
{
lean_object* v_authority_2848_; lean_object* v_path_2849_; lean_object* v_query_2850_; lean_object* v_fragment_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2859_; 
v_authority_2848_ = lean_ctor_get(v_uri_2846_, 1);
v_path_2849_ = lean_ctor_get(v_uri_2846_, 2);
v_query_2850_ = lean_ctor_get(v_uri_2846_, 3);
v_fragment_2851_ = lean_ctor_get(v_uri_2846_, 4);
v_isSharedCheck_2859_ = !lean_is_exclusive(v_uri_2846_);
if (v_isSharedCheck_2859_ == 0)
{
lean_object* v_unused_2860_; 
v_unused_2860_ = lean_ctor_get(v_uri_2846_, 0);
lean_dec(v_unused_2860_);
v___x_2853_ = v_uri_2846_;
v_isShared_2854_ = v_isSharedCheck_2859_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_fragment_2851_);
lean_inc(v_query_2850_);
lean_inc(v_path_2849_);
lean_inc(v_authority_2848_);
lean_dec(v_uri_2846_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2859_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2855_; lean_object* v___x_2857_; 
v___x_2855_ = l_Std_Http_URI_Scheme_ofString_x21(v_scheme_2847_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v___x_2855_);
v___x_2857_ = v___x_2853_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v_authority_2848_);
lean_ctor_set(v_reuseFailAlloc_2858_, 2, v_path_2849_);
lean_ctor_set(v_reuseFailAlloc_2858_, 3, v_query_2850_);
lean_ctor_set(v_reuseFailAlloc_2858_, 4, v_fragment_2851_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withAuthority(lean_object* v_uri_2861_, lean_object* v_authority_2862_){
_start:
{
lean_object* v_scheme_2863_; lean_object* v_path_2864_; lean_object* v_query_2865_; lean_object* v_fragment_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
v_scheme_2863_ = lean_ctor_get(v_uri_2861_, 0);
v_path_2864_ = lean_ctor_get(v_uri_2861_, 2);
v_query_2865_ = lean_ctor_get(v_uri_2861_, 3);
v_fragment_2866_ = lean_ctor_get(v_uri_2861_, 4);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_uri_2861_);
if (v_isSharedCheck_2873_ == 0)
{
lean_object* v_unused_2874_; 
v_unused_2874_ = lean_ctor_get(v_uri_2861_, 1);
lean_dec(v_unused_2874_);
v___x_2868_ = v_uri_2861_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_fragment_2866_);
lean_inc(v_query_2865_);
lean_inc(v_path_2864_);
lean_inc(v_scheme_2863_);
lean_dec(v_uri_2861_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 1, v_authority_2862_);
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_scheme_2863_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_authority_2862_);
lean_ctor_set(v_reuseFailAlloc_2872_, 2, v_path_2864_);
lean_ctor_set(v_reuseFailAlloc_2872_, 3, v_query_2865_);
lean_ctor_set(v_reuseFailAlloc_2872_, 4, v_fragment_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withPath(lean_object* v_uri_2875_, lean_object* v_path_2876_){
_start:
{
lean_object* v_scheme_2877_; lean_object* v_authority_2878_; lean_object* v_query_2879_; lean_object* v_fragment_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
v_scheme_2877_ = lean_ctor_get(v_uri_2875_, 0);
v_authority_2878_ = lean_ctor_get(v_uri_2875_, 1);
v_query_2879_ = lean_ctor_get(v_uri_2875_, 3);
v_fragment_2880_ = lean_ctor_get(v_uri_2875_, 4);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_uri_2875_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; 
v_unused_2888_ = lean_ctor_get(v_uri_2875_, 2);
lean_dec(v_unused_2888_);
v___x_2882_ = v_uri_2875_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_fragment_2880_);
lean_inc(v_query_2879_);
lean_inc(v_authority_2878_);
lean_inc(v_scheme_2877_);
lean_dec(v_uri_2875_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 2, v_path_2876_);
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_scheme_2877_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_authority_2878_);
lean_ctor_set(v_reuseFailAlloc_2886_, 2, v_path_2876_);
lean_ctor_set(v_reuseFailAlloc_2886_, 3, v_query_2879_);
lean_ctor_set(v_reuseFailAlloc_2886_, 4, v_fragment_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withQuery(lean_object* v_uri_2889_, lean_object* v_query_2890_){
_start:
{
lean_object* v_scheme_2891_; lean_object* v_authority_2892_; lean_object* v_path_2893_; lean_object* v_fragment_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2902_; 
v_scheme_2891_ = lean_ctor_get(v_uri_2889_, 0);
v_authority_2892_ = lean_ctor_get(v_uri_2889_, 1);
v_path_2893_ = lean_ctor_get(v_uri_2889_, 2);
v_fragment_2894_ = lean_ctor_get(v_uri_2889_, 4);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_uri_2889_);
if (v_isSharedCheck_2902_ == 0)
{
lean_object* v_unused_2903_; 
v_unused_2903_ = lean_ctor_get(v_uri_2889_, 3);
lean_dec(v_unused_2903_);
v___x_2896_ = v_uri_2889_;
v_isShared_2897_ = v_isSharedCheck_2902_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_fragment_2894_);
lean_inc(v_path_2893_);
lean_inc(v_authority_2892_);
lean_inc(v_scheme_2891_);
lean_dec(v_uri_2889_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2902_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2898_, 0, v_query_2890_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 3, v___x_2898_);
v___x_2900_ = v___x_2896_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_scheme_2891_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_authority_2892_);
lean_ctor_set(v_reuseFailAlloc_2901_, 2, v_path_2893_);
lean_ctor_set(v_reuseFailAlloc_2901_, 3, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2901_, 4, v_fragment_2894_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withFragment(lean_object* v_uri_2904_, lean_object* v_fragment_2905_){
_start:
{
lean_object* v_scheme_2906_; lean_object* v_authority_2907_; lean_object* v_path_2908_; lean_object* v_query_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
v_scheme_2906_ = lean_ctor_get(v_uri_2904_, 0);
v_authority_2907_ = lean_ctor_get(v_uri_2904_, 1);
v_path_2908_ = lean_ctor_get(v_uri_2904_, 2);
v_query_2909_ = lean_ctor_get(v_uri_2904_, 3);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_uri_2904_);
if (v_isSharedCheck_2916_ == 0)
{
lean_object* v_unused_2917_; 
v_unused_2917_ = lean_ctor_get(v_uri_2904_, 4);
lean_dec(v_unused_2917_);
v___x_2911_ = v_uri_2904_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_query_2909_);
lean_inc(v_path_2908_);
lean_inc(v_authority_2907_);
lean_inc(v_scheme_2906_);
lean_dec(v_uri_2904_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 4, v_fragment_2905_);
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_scheme_2906_);
lean_ctor_set(v_reuseFailAlloc_2915_, 1, v_authority_2907_);
lean_ctor_set(v_reuseFailAlloc_2915_, 2, v_path_2908_);
lean_ctor_set(v_reuseFailAlloc_2915_, 3, v_query_2909_);
lean_ctor_set(v_reuseFailAlloc_2915_, 4, v_fragment_2905_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_normalize(lean_object* v_uri_2918_){
_start:
{
lean_object* v_scheme_2919_; lean_object* v_authority_2920_; lean_object* v_path_2921_; lean_object* v_query_2922_; lean_object* v_fragment_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2931_; 
v_scheme_2919_ = lean_ctor_get(v_uri_2918_, 0);
v_authority_2920_ = lean_ctor_get(v_uri_2918_, 1);
v_path_2921_ = lean_ctor_get(v_uri_2918_, 2);
v_query_2922_ = lean_ctor_get(v_uri_2918_, 3);
v_fragment_2923_ = lean_ctor_get(v_uri_2918_, 4);
v_isSharedCheck_2931_ = !lean_is_exclusive(v_uri_2918_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2925_ = v_uri_2918_;
v_isShared_2926_ = v_isSharedCheck_2931_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_fragment_2923_);
lean_inc(v_query_2922_);
lean_inc(v_path_2921_);
lean_inc(v_authority_2920_);
lean_inc(v_scheme_2919_);
lean_dec(v_uri_2918_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2931_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2927_; lean_object* v___x_2929_; 
v___x_2927_ = l_Std_Http_URI_Path_normalize(v_path_2921_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 2, v___x_2927_);
v___x_2929_ = v___x_2925_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_scheme_2919_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_authority_2920_);
lean_ctor_set(v_reuseFailAlloc_2930_, 2, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_2930_, 3, v_query_2922_);
lean_ctor_set(v_reuseFailAlloc_2930_, 4, v_fragment_2923_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___redArg(lean_object* v_x_2932_){
_start:
{
lean_object* v_scheme_2933_; lean_object* v_host_2934_; uint16_t v_port_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; uint8_t v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v_ctr_2956_; lean_object* v_a_2957_; 
v_scheme_2933_ = lean_ctor_get(v_x_2932_, 0);
lean_inc_ref(v_scheme_2933_);
v_host_2934_ = lean_ctor_get(v_x_2932_, 1);
lean_inc_ref(v_host_2934_);
v_port_2935_ = lean_ctor_get_uint16(v_x_2932_, sizeof(void*)*2);
lean_dec_ref(v_x_2932_);
v___x_2936_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2937_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2938_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2939_ = l_String_quote(v_scheme_2933_);
v___x_2940_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
v___x_2941_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2938_);
lean_ctor_set(v___x_2941_, 1, v___x_2940_);
v___x_2942_ = 0;
v___x_2943_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2943_, 0, v___x_2941_);
lean_ctor_set_uint8(v___x_2943_, sizeof(void*)*1, v___x_2942_);
v___x_2944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2937_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v___x_2945_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2944_);
lean_ctor_set(v___x_2946_, 1, v___x_2945_);
v___x_2947_ = lean_box(1);
v___x_2948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2946_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
v___x_2949_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_2950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2948_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v___x_2936_);
v___x_2952_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2953_ = lean_unsigned_to_nat(0u);
v___x_2954_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_2934_))
{
case 0:
{
lean_object* v_name_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2996_; 
v_name_2987_ = lean_ctor_get(v_host_2934_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v_host_2934_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2989_ = v_host_2934_;
v_isShared_2990_ = v_isSharedCheck_2996_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_name_2987_);
lean_dec(v_host_2934_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2996_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
v___x_2991_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_2992_ = l_String_quote(v_name_2987_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set_tag(v___x_2989_, 3);
lean_ctor_set(v___x_2989_, 0, v___x_2992_);
v___x_2994_ = v___x_2989_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
v_ctr_2956_ = v___x_2991_;
v_a_2957_ = v___x_2994_;
goto v___jp_2955_;
}
}
}
case 1:
{
lean_object* v_ipv4_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3006_; 
v_ipv4_2997_ = lean_ctor_get(v_host_2934_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v_host_2934_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2999_ = v_host_2934_;
v_isShared_3000_ = v_isSharedCheck_3006_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_ipv4_2997_);
lean_dec(v_host_2934_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3006_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3004_; 
v___x_3001_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_3002_ = lean_uv_ntop_v4(v_ipv4_2997_);
lean_dec_ref(v_ipv4_2997_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set_tag(v___x_2999_, 3);
lean_ctor_set(v___x_2999_, 0, v___x_3002_);
v___x_3004_ = v___x_2999_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_3002_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
v_ctr_2956_ = v___x_3001_;
v_a_2957_ = v___x_3004_;
goto v___jp_2955_;
}
}
}
default: 
{
lean_object* v_ipv6_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3016_; 
v_ipv6_3007_ = lean_ctor_get(v_host_2934_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v_host_2934_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3009_ = v_host_2934_;
v_isShared_3010_ = v_isSharedCheck_3016_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_ipv6_3007_);
lean_dec(v_host_2934_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3016_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3014_; 
v___x_3011_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_3012_ = lean_uv_ntop_v6(v_ipv6_3007_);
lean_dec_ref(v_ipv6_3007_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set_tag(v___x_3009_, 3);
lean_ctor_set(v___x_3009_, 0, v___x_3012_);
v___x_3014_ = v___x_3009_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
v_ctr_2956_ = v___x_3011_;
v_a_2957_ = v___x_3014_;
goto v___jp_2955_;
}
}
}
}
v___jp_2955_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2958_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_2959_ = lean_string_append(v___x_2958_, v_ctr_2956_);
v___x_2960_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
v___x_2961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
lean_ctor_set(v___x_2961_, 1, v___x_2947_);
v___x_2962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
lean_ctor_set(v___x_2962_, 1, v_a_2957_);
v___x_2963_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2954_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
v___x_2964_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
lean_ctor_set_uint8(v___x_2964_, sizeof(void*)*1, v___x_2942_);
v___x_2965_ = l_Repr_addAppParen(v___x_2964_, v___x_2953_);
v___x_2966_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2952_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
v___x_2967_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
lean_ctor_set_uint8(v___x_2967_, sizeof(void*)*1, v___x_2942_);
v___x_2968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2951_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2968_);
lean_ctor_set(v___x_2969_, 1, v___x_2945_);
v___x_2970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
lean_ctor_set(v___x_2970_, 1, v___x_2947_);
v___x_2971_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_2972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2970_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
lean_ctor_set(v___x_2973_, 1, v___x_2936_);
v___x_2974_ = lean_uint16_to_nat(v_port_2935_);
v___x_2975_ = l_Nat_reprFast(v___x_2974_);
v___x_2976_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
v___x_2977_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2952_);
lean_ctor_set(v___x_2977_, 1, v___x_2976_);
v___x_2978_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
lean_ctor_set_uint8(v___x_2978_, sizeof(void*)*1, v___x_2942_);
v___x_2979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2973_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
v___x_2980_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2981_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2981_);
lean_ctor_set(v___x_2982_, 1, v___x_2979_);
v___x_2983_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2982_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2980_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
v___x_2986_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
lean_ctor_set_uint8(v___x_2986_, sizeof(void*)*1, v___x_2942_);
return v___x_2986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr(lean_object* v_x_3017_, lean_object* v_prec_3018_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = l_Std_Http_URI_instReprOrigin_repr___redArg(v_x_3017_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___boxed(lean_object* v_x_3020_, lean_object* v_prec_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Std_Http_URI_instReprOrigin_repr(v_x_3020_, v_prec_3021_);
lean_dec(v_prec_3021_);
return v_res_3022_;
}
}
uint8_t l_Std_Http_URI_instBEqOrigin_beq(lean_object* v_x_3025_, lean_object* v_x_3026_){
_start:
{
lean_object* v_scheme_3027_; lean_object* v_host_3028_; uint16_t v_port_3029_; lean_object* v_scheme_3030_; lean_object* v_host_3031_; uint16_t v_port_3032_; uint8_t v___x_3033_; 
v_scheme_3027_ = lean_ctor_get(v_x_3025_, 0);
v_host_3028_ = lean_ctor_get(v_x_3025_, 1);
v_port_3029_ = lean_ctor_get_uint16(v_x_3025_, sizeof(void*)*2);
v_scheme_3030_ = lean_ctor_get(v_x_3026_, 0);
v_host_3031_ = lean_ctor_get(v_x_3026_, 1);
v_port_3032_ = lean_ctor_get_uint16(v_x_3026_, sizeof(void*)*2);
v___x_3033_ = lean_string_dec_eq(v_scheme_3027_, v_scheme_3030_);
if (v___x_3033_ == 0)
{
return v___x_3033_;
}
else
{
uint8_t v___x_3034_; 
v___x_3034_ = l_Std_Http_URI_instBEqHost_beq(v_host_3028_, v_host_3031_);
if (v___x_3034_ == 0)
{
return v___x_3034_;
}
else
{
uint8_t v___x_3035_; 
v___x_3035_ = lean_uint16_dec_eq(v_port_3029_, v_port_3032_);
return v___x_3035_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_instBEqOrigin_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3025_ = stack[0].m_obj;
lean_object* v_x_3026_ = stack[1].m_obj;
uint8_t v_res_3036_;
v_res_3036_ = l_Std_Http_URI_instBEqOrigin_beq(v_x_3025_, v_x_3026_);
stack->m_num = v_res_3036_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqOrigin_beq___boxed(lean_object* v_x_3037_, lean_object* v_x_3038_){
_start:
{
uint8_t v_res_3039_; lean_object* v_r_3040_; 
v_res_3039_ = l_Std_Http_URI_instBEqOrigin_beq(v_x_3037_, v_x_3038_);
lean_dec_ref(v_x_3038_);
lean_dec_ref(v_x_3037_);
v_r_3040_ = lean_box(v_res_3039_);
return v_r_3040_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Origin_hostHeader(lean_object* v_o_3043_){
_start:
{
lean_object* v_scheme_3044_; lean_object* v_host_3045_; uint16_t v_port_3046_; lean_object* v___y_3048_; uint16_t v_defaultPort_3054_; uint8_t v___x_3055_; 
v_scheme_3044_ = lean_ctor_get(v_o_3043_, 0);
lean_inc_ref(v_scheme_3044_);
v_host_3045_ = lean_ctor_get(v_o_3043_, 1);
lean_inc_ref(v_host_3045_);
v_port_3046_ = lean_ctor_get_uint16(v_o_3043_, sizeof(void*)*2);
lean_dec_ref(v_o_3043_);
v_defaultPort_3054_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_3044_);
lean_dec_ref(v_scheme_3044_);
v___x_3055_ = lean_uint16_dec_eq(v_port_3046_, v_defaultPort_3054_);
if (v___x_3055_ == 0)
{
switch(lean_obj_tag(v_host_3045_))
{
case 0:
{
lean_object* v_name_3056_; 
v_name_3056_ = lean_ctor_get(v_host_3045_, 0);
lean_inc_ref(v_name_3056_);
lean_dec_ref_known(v_host_3045_, 1);
v___y_3048_ = v_name_3056_;
goto v___jp_3047_;
}
case 1:
{
lean_object* v_ipv4_3057_; lean_object* v___x_3058_; 
v_ipv4_3057_ = lean_ctor_get(v_host_3045_, 0);
lean_inc_ref(v_ipv4_3057_);
lean_dec_ref_known(v_host_3045_, 1);
v___x_3058_ = lean_uv_ntop_v4(v_ipv4_3057_);
lean_dec_ref(v_ipv4_3057_);
v___y_3048_ = v___x_3058_;
goto v___jp_3047_;
}
default: 
{
lean_object* v_ipv6_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v_ipv6_3059_ = lean_ctor_get(v_host_3045_, 0);
lean_inc_ref(v_ipv6_3059_);
lean_dec_ref_known(v_host_3045_, 1);
v___x_3060_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3061_ = lean_uv_ntop_v6(v_ipv6_3059_);
lean_dec_ref(v_ipv6_3059_);
v___x_3062_ = lean_string_append(v___x_3060_, v___x_3061_);
lean_dec_ref(v___x_3061_);
v___x_3063_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3064_ = lean_string_append(v___x_3062_, v___x_3063_);
v___y_3048_ = v___x_3064_;
goto v___jp_3047_;
}
}
}
else
{
switch(lean_obj_tag(v_host_3045_))
{
case 0:
{
lean_object* v_name_3065_; 
v_name_3065_ = lean_ctor_get(v_host_3045_, 0);
lean_inc_ref(v_name_3065_);
lean_dec_ref_known(v_host_3045_, 1);
return v_name_3065_;
}
case 1:
{
lean_object* v_ipv4_3066_; lean_object* v___x_3067_; 
v_ipv4_3066_ = lean_ctor_get(v_host_3045_, 0);
lean_inc_ref(v_ipv4_3066_);
lean_dec_ref_known(v_host_3045_, 1);
v___x_3067_ = lean_uv_ntop_v4(v_ipv4_3066_);
lean_dec_ref(v_ipv4_3066_);
return v___x_3067_;
}
default: 
{
lean_object* v_ipv6_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v_ipv6_3068_ = lean_ctor_get(v_host_3045_, 0);
lean_inc_ref(v_ipv6_3068_);
lean_dec_ref_known(v_host_3045_, 1);
v___x_3069_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3070_ = lean_uv_ntop_v6(v_ipv6_3068_);
lean_dec_ref(v_ipv6_3068_);
v___x_3071_ = lean_string_append(v___x_3069_, v___x_3070_);
lean_dec_ref(v___x_3070_);
v___x_3072_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3073_ = lean_string_append(v___x_3071_, v___x_3072_);
return v___x_3073_;
}
}
}
v___jp_3047_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3049_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3050_ = lean_string_append(v___y_3048_, v___x_3049_);
v___x_3051_ = lean_uint16_to_nat(v_port_3046_);
v___x_3052_ = l_Nat_reprFast(v___x_3051_);
v___x_3053_ = lean_string_append(v___x_3050_, v___x_3052_);
lean_dec_ref(v___x_3052_);
return v___x_3053_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___redArg(lean_object* v_x_3080_){
_start:
{
lean_object* v_authority_3081_; lean_object* v_path_3082_; lean_object* v_query_3083_; lean_object* v_fragment_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; uint8_t v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v_authority_3081_ = lean_ctor_get(v_x_3080_, 0);
lean_inc(v_authority_3081_);
v_path_3082_ = lean_ctor_get(v_x_3080_, 1);
lean_inc_ref(v_path_3082_);
v_query_3083_ = lean_ctor_get(v_x_3080_, 2);
lean_inc(v_query_3083_);
v_fragment_3084_ = lean_ctor_get(v_x_3080_, 3);
lean_inc(v_fragment_3084_);
lean_dec_ref(v_x_3080_);
v___x_3085_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_3086_ = ((lean_object*)(l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__1));
v___x_3087_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_3088_ = lean_unsigned_to_nat(0u);
v___x_3089_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_3081_, v___x_3088_);
v___x_3090_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3087_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
v___x_3091_ = 0;
v___x_3092_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3092_, 0, v___x_3090_);
lean_ctor_set_uint8(v___x_3092_, sizeof(void*)*1, v___x_3091_);
v___x_3093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3086_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_3095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3093_);
lean_ctor_set(v___x_3095_, 1, v___x_3094_);
v___x_3096_ = lean_box(1);
v___x_3097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3095_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
v___x_3098_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_3099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3097_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3099_);
lean_ctor_set(v___x_3100_, 1, v___x_3085_);
v___x_3101_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_3102_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3082_);
v___x_3103_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3101_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
v___x_3104_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
lean_ctor_set_uint8(v___x_3104_, sizeof(void*)*1, v___x_3091_);
v___x_3105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3100_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
v___x_3106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
lean_ctor_set(v___x_3106_, 1, v___x_3094_);
v___x_3107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
lean_ctor_set(v___x_3107_, 1, v___x_3096_);
v___x_3108_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_3109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3107_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
v___x_3110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
lean_ctor_set(v___x_3110_, 1, v___x_3085_);
v___x_3111_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_3112_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3083_, v___x_3088_);
v___x_3113_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3111_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*1, v___x_3091_);
v___x_3115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3110_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
v___x_3116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
lean_ctor_set(v___x_3116_, 1, v___x_3094_);
v___x_3117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
lean_ctor_set(v___x_3117_, 1, v___x_3096_);
v___x_3118_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_3119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3117_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v___x_3120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
lean_ctor_set(v___x_3120_, 1, v___x_3085_);
v___x_3121_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_3122_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_3084_, v___x_3088_);
v___x_3123_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3121_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
lean_ctor_set_uint8(v___x_3124_, sizeof(void*)*1, v___x_3091_);
v___x_3125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3120_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_3127_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_3128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
lean_ctor_set(v___x_3128_, 1, v___x_3125_);
v___x_3129_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_3130_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3128_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v___x_3131_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3126_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
v___x_3132_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
lean_ctor_set_uint8(v___x_3132_, sizeof(void*)*1, v___x_3091_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr(lean_object* v_x_3133_, lean_object* v_prec_3134_){
_start:
{
lean_object* v___x_3135_; 
v___x_3135_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_x_3133_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___boxed(lean_object* v_x_3136_, lean_object* v_prec_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_Std_Http_URI_instReprRelativeRef_repr(v_x_3136_, v_prec_3137_);
lean_dec(v_prec_3137_);
return v_res_3138_;
}
}
uint8_t l_Std_Http_URI_instBEqRelativeRef_beq(lean_object* v_x_3146_, lean_object* v_x_3147_){
_start:
{
lean_object* v_authority_3148_; lean_object* v_path_3149_; lean_object* v_query_3150_; lean_object* v_fragment_3151_; lean_object* v_authority_3152_; lean_object* v_path_3153_; lean_object* v_query_3154_; lean_object* v_fragment_3155_; uint8_t v___x_3156_; 
v_authority_3148_ = lean_ctor_get(v_x_3146_, 0);
v_path_3149_ = lean_ctor_get(v_x_3146_, 1);
v_query_3150_ = lean_ctor_get(v_x_3146_, 2);
v_fragment_3151_ = lean_ctor_get(v_x_3146_, 3);
v_authority_3152_ = lean_ctor_get(v_x_3147_, 0);
v_path_3153_ = lean_ctor_get(v_x_3147_, 1);
v_query_3154_ = lean_ctor_get(v_x_3147_, 2);
v_fragment_3155_ = lean_ctor_get(v_x_3147_, 3);
v___x_3156_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_3148_, v_authority_3152_);
if (v___x_3156_ == 0)
{
return v___x_3156_;
}
else
{
uint8_t v___x_3157_; 
v___x_3157_ = l_Std_Http_URI_instBEqPath_beq(v_path_3149_, v_path_3153_);
if (v___x_3157_ == 0)
{
return v___x_3157_;
}
else
{
uint8_t v___x_3158_; 
v___x_3158_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_3150_, v_query_3154_);
if (v___x_3158_ == 0)
{
return v___x_3158_;
}
else
{
uint8_t v___x_3159_; 
v___x_3159_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_3151_, v_fragment_3155_);
return v___x_3159_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_instBEqRelativeRef_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3146_ = stack[0].m_obj;
lean_object* v_x_3147_ = stack[1].m_obj;
uint8_t v_res_3160_;
v_res_3160_ = l_Std_Http_URI_instBEqRelativeRef_beq(v_x_3146_, v_x_3147_);
stack->m_num = v_res_3160_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqRelativeRef_beq___boxed(lean_object* v_x_3161_, lean_object* v_x_3162_){
_start:
{
uint8_t v_res_3163_; lean_object* v_r_3164_; 
v_res_3163_ = l_Std_Http_URI_instBEqRelativeRef_beq(v_x_3161_, v_x_3162_);
lean_dec_ref(v_x_3162_);
lean_dec_ref(v_x_3161_);
v_r_3164_ = lean_box(v_res_3163_);
return v_r_3164_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringRelativeRef___lam__1(lean_object* v___f_3167_, lean_object* v_ref_3168_){
_start:
{
lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v_authority_3177_; lean_object* v_path_3178_; lean_object* v_query_3179_; lean_object* v_fragment_3180_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3192_; 
v_authority_3177_ = lean_ctor_get(v_ref_3168_, 0);
lean_inc(v_authority_3177_);
v_path_3178_ = lean_ctor_get(v_ref_3168_, 1);
lean_inc_ref(v_path_3178_);
v_query_3179_ = lean_ctor_get(v_ref_3168_, 2);
lean_inc(v_query_3179_);
v_fragment_3180_ = lean_ctor_get(v_ref_3168_, 3);
lean_inc(v_fragment_3180_);
lean_dec_ref(v_ref_3168_);
if (lean_obj_tag(v_authority_3177_) == 0)
{
lean_object* v___x_3203_; 
v___x_3203_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3192_ = v___x_3203_;
goto v___jp_3191_;
}
else
{
lean_object* v_val_3204_; lean_object* v_userInfo_3205_; lean_object* v_host_3206_; lean_object* v_port_3207_; lean_object* v___x_3208_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3227_; 
v_val_3204_ = lean_ctor_get(v_authority_3177_, 0);
lean_inc(v_val_3204_);
lean_dec_ref_known(v_authority_3177_, 1);
v_userInfo_3205_ = lean_ctor_get(v_val_3204_, 0);
lean_inc(v_userInfo_3205_);
v_host_3206_ = lean_ctor_get(v_val_3204_, 1);
lean_inc_ref(v_host_3206_);
v_port_3207_ = lean_ctor_get(v_val_3204_, 2);
lean_inc(v_port_3207_);
lean_dec(v_val_3204_);
v___x_3208_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3205_) == 0)
{
lean_object* v___x_3237_; 
v___x_3237_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3227_ = v___x_3237_;
goto v___jp_3226_;
}
else
{
lean_object* v_val_3238_; lean_object* v_password_3239_; 
v_val_3238_ = lean_ctor_get(v_userInfo_3205_, 0);
lean_inc(v_val_3238_);
lean_dec_ref_known(v_userInfo_3205_, 1);
v_password_3239_ = lean_ctor_get(v_val_3238_, 1);
if (lean_obj_tag(v_password_3239_) == 0)
{
lean_object* v_username_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
v_username_3240_ = lean_ctor_get(v_val_3238_, 0);
lean_inc_ref(v_username_3240_);
lean_dec(v_val_3238_);
v___x_3241_ = lean_string_from_utf8_unchecked(v_username_3240_);
v___x_3242_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3243_ = lean_string_append(v___x_3241_, v___x_3242_);
v___y_3227_ = v___x_3243_;
goto v___jp_3226_;
}
else
{
lean_object* v_username_3244_; lean_object* v_val_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
lean_inc_ref(v_password_3239_);
v_username_3244_ = lean_ctor_get(v_val_3238_, 0);
lean_inc_ref(v_username_3244_);
lean_dec(v_val_3238_);
v_val_3245_ = lean_ctor_get(v_password_3239_, 0);
lean_inc(v_val_3245_);
lean_dec_ref_known(v_password_3239_, 1);
v___x_3246_ = lean_string_from_utf8_unchecked(v_username_3244_);
v___x_3247_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3248_ = lean_string_append(v___x_3246_, v___x_3247_);
v___x_3249_ = lean_string_from_utf8_unchecked(v_val_3245_);
v___x_3250_ = lean_string_append(v___x_3248_, v___x_3249_);
lean_dec_ref(v___x_3249_);
v___x_3251_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3252_ = lean_string_append(v___x_3250_, v___x_3251_);
v___y_3227_ = v___x_3252_;
goto v___jp_3226_;
}
}
v___jp_3209_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3213_ = lean_string_append(v___y_3210_, v___y_3211_);
lean_dec_ref(v___y_3211_);
v___x_3214_ = lean_string_append(v___x_3213_, v___y_3212_);
lean_dec_ref(v___y_3212_);
v___x_3215_ = lean_string_append(v___x_3208_, v___x_3214_);
lean_dec_ref(v___x_3214_);
v___y_3192_ = v___x_3215_;
goto v___jp_3191_;
}
v___jp_3216_:
{
switch(lean_obj_tag(v_port_3207_))
{
case 0:
{
lean_object* v___x_3219_; 
v___x_3219_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3210_ = v___y_3217_;
v___y_3211_ = v___y_3218_;
v___y_3212_ = v___x_3219_;
goto v___jp_3209_;
}
case 1:
{
lean_object* v___x_3220_; 
v___x_3220_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3210_ = v___y_3217_;
v___y_3211_ = v___y_3218_;
v___y_3212_ = v___x_3220_;
goto v___jp_3209_;
}
default: 
{
uint16_t v_port_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v_port_3221_ = lean_ctor_get_uint16(v_port_3207_, 0);
lean_dec_ref_known(v_port_3207_, 0);
v___x_3222_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3223_ = lean_uint16_to_nat(v_port_3221_);
v___x_3224_ = l_Nat_reprFast(v___x_3223_);
v___x_3225_ = lean_string_append(v___x_3222_, v___x_3224_);
lean_dec_ref(v___x_3224_);
v___y_3210_ = v___y_3217_;
v___y_3211_ = v___y_3218_;
v___y_3212_ = v___x_3225_;
goto v___jp_3209_;
}
}
}
v___jp_3226_:
{
switch(lean_obj_tag(v_host_3206_))
{
case 0:
{
lean_object* v_name_3228_; 
v_name_3228_ = lean_ctor_get(v_host_3206_, 0);
lean_inc_ref(v_name_3228_);
lean_dec_ref_known(v_host_3206_, 1);
v___y_3217_ = v___y_3227_;
v___y_3218_ = v_name_3228_;
goto v___jp_3216_;
}
case 1:
{
lean_object* v_ipv4_3229_; lean_object* v___x_3230_; 
v_ipv4_3229_ = lean_ctor_get(v_host_3206_, 0);
lean_inc_ref(v_ipv4_3229_);
lean_dec_ref_known(v_host_3206_, 1);
v___x_3230_ = lean_uv_ntop_v4(v_ipv4_3229_);
lean_dec_ref(v_ipv4_3229_);
v___y_3217_ = v___y_3227_;
v___y_3218_ = v___x_3230_;
goto v___jp_3216_;
}
default: 
{
lean_object* v_ipv6_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v_ipv6_3231_ = lean_ctor_get(v_host_3206_, 0);
lean_inc_ref(v_ipv6_3231_);
lean_dec_ref_known(v_host_3206_, 1);
v___x_3232_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3233_ = lean_uv_ntop_v6(v_ipv6_3231_);
lean_dec_ref(v_ipv6_3231_);
v___x_3234_ = lean_string_append(v___x_3232_, v___x_3233_);
lean_dec_ref(v___x_3233_);
v___x_3235_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3236_ = lean_string_append(v___x_3234_, v___x_3235_);
v___y_3217_ = v___y_3227_;
v___y_3218_ = v___x_3236_;
goto v___jp_3216_;
}
}
}
}
v___jp_3169_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3174_ = lean_string_append(v___y_3171_, v___y_3172_);
lean_dec_ref(v___y_3172_);
v___x_3175_ = lean_string_append(v___x_3174_, v___y_3170_);
lean_dec_ref(v___y_3170_);
v___x_3176_ = lean_string_append(v___x_3175_, v___y_3173_);
lean_dec_ref(v___y_3173_);
return v___x_3176_;
}
v___jp_3181_:
{
lean_object* v_queryPart_3184_; 
v_queryPart_3184_ = l_Std_Http_URI_Query_formatOption(v_query_3179_);
if (lean_obj_tag(v_fragment_3180_) == 0)
{
lean_object* v___x_3185_; 
v___x_3185_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3170_ = v_queryPart_3184_;
v___y_3171_ = v___y_3182_;
v___y_3172_ = v___y_3183_;
v___y_3173_ = v___x_3185_;
goto v___jp_3169_;
}
else
{
lean_object* v_val_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v_val_3186_ = lean_ctor_get(v_fragment_3180_, 0);
lean_inc(v_val_3186_);
lean_dec_ref_known(v_fragment_3180_, 1);
v___x_3187_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3188_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3186_);
lean_dec(v_val_3186_);
v___x_3189_ = lean_string_from_utf8_unchecked(v___x_3188_);
v___x_3190_ = lean_string_append(v___x_3187_, v___x_3189_);
lean_dec_ref(v___x_3189_);
v___y_3170_ = v_queryPart_3184_;
v___y_3171_ = v___y_3182_;
v___y_3172_ = v___y_3183_;
v___y_3173_ = v___x_3190_;
goto v___jp_3169_;
}
}
v___jp_3191_:
{
lean_object* v_segments_3193_; uint8_t v_absolute_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; size_t v_sz_3197_; size_t v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v_result_3201_; 
v_segments_3193_ = lean_ctor_get(v_path_3178_, 0);
lean_inc_ref(v_segments_3193_);
v_absolute_3194_ = lean_ctor_get_uint8(v_path_3178_, sizeof(void*)*1);
lean_dec_ref(v_path_3178_);
v___x_3195_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3196_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3197_ = lean_array_size(v_segments_3193_);
v___x_3198_ = ((size_t)0ULL);
v___x_3199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3196_, v___f_3167_, v_sz_3197_, v___x_3198_, v_segments_3193_);
v___x_3200_ = lean_array_to_list(v___x_3199_);
v_result_3201_ = l_String_intercalate(v___x_3195_, v___x_3200_);
if (v_absolute_3194_ == 0)
{
v___y_3182_ = v___y_3192_;
v___y_3183_ = v_result_3201_;
goto v___jp_3181_;
}
else
{
lean_object* v___x_3202_; 
v___x_3202_ = lean_string_append(v___x_3195_, v_result_3201_);
lean_dec_ref(v_result_3201_);
v___y_3182_ = v___y_3192_;
v___y_3183_ = v___x_3202_;
goto v___jp_3181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___impl(lean_object* v_x_3256_){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = lean_obj_tag_nat(v_x_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___impl___boxed(lean_object* v_x_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_Std_Http_URIReference_ctorIdx___impl(v_x_3258_);
lean_dec_ref(v_x_3258_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___redArg(lean_object* v_t_3260_, lean_object* v_k_3261_){
_start:
{
lean_object* v_uri_3262_; lean_object* v___x_3263_; 
v_uri_3262_ = lean_ctor_get(v_t_3260_, 0);
lean_inc_ref(v_uri_3262_);
lean_dec_ref(v_t_3260_);
v___x_3263_ = lean_apply_1(v_k_3261_, v_uri_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim(lean_object* v_motive_3264_, lean_object* v_ctorIdx_3265_, lean_object* v_t_3266_, lean_object* v_h_3267_, lean_object* v_k_3268_){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3266_, v_k_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___boxed(lean_object* v_motive_3270_, lean_object* v_ctorIdx_3271_, lean_object* v_t_3272_, lean_object* v_h_3273_, lean_object* v_k_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_Std_Http_URIReference_ctorElim(v_motive_3270_, v_ctorIdx_3271_, v_t_3272_, v_h_3273_, v_k_3274_);
lean_dec(v_ctorIdx_3271_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim___redArg(lean_object* v_t_3276_, lean_object* v_absolute_3277_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3276_, v_absolute_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim(lean_object* v_motive_3279_, lean_object* v_t_3280_, lean_object* v_h_3281_, lean_object* v_absolute_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3280_, v_absolute_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim___redArg(lean_object* v_t_3284_, lean_object* v_relative_3285_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3284_, v_relative_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim(lean_object* v_motive_3287_, lean_object* v_t_3288_, lean_object* v_h_3289_, lean_object* v_relative_3290_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3288_, v_relative_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr(lean_object* v_x_3304_, lean_object* v_prec_3305_){
_start:
{
if (lean_obj_tag(v_x_3304_) == 0)
{
lean_object* v_uri_3306_; lean_object* v___y_3308_; lean_object* v___x_3316_; uint8_t v___x_3317_; 
v_uri_3306_ = lean_ctor_get(v_x_3304_, 0);
lean_inc_ref(v_uri_3306_);
lean_dec_ref_known(v_x_3304_, 1);
v___x_3316_ = lean_unsigned_to_nat(1024u);
v___x_3317_ = lean_nat_dec_le(v___x_3316_, v_prec_3305_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; 
v___x_3318_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3308_ = v___x_3318_;
goto v___jp_3307_;
}
else
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3308_ = v___x_3319_;
goto v___jp_3307_;
}
v___jp_3307_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; uint8_t v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3309_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__2));
v___x_3310_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3306_);
v___x_3311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3309_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
lean_inc(v___y_3308_);
v___x_3312_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___y_3308_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
v___x_3313_ = 0;
v___x_3314_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3314_, 0, v___x_3312_);
lean_ctor_set_uint8(v___x_3314_, sizeof(void*)*1, v___x_3313_);
v___x_3315_ = l_Repr_addAppParen(v___x_3314_, v_prec_3305_);
return v___x_3315_;
}
}
else
{
lean_object* v_ref_3320_; lean_object* v___y_3322_; lean_object* v___x_3330_; uint8_t v___x_3331_; 
v_ref_3320_ = lean_ctor_get(v_x_3304_, 0);
lean_inc_ref(v_ref_3320_);
lean_dec_ref_known(v_x_3304_, 1);
v___x_3330_ = lean_unsigned_to_nat(1024u);
v___x_3331_ = lean_nat_dec_le(v___x_3330_, v_prec_3305_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; 
v___x_3332_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3322_ = v___x_3332_;
goto v___jp_3321_;
}
else
{
lean_object* v___x_3333_; 
v___x_3333_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3322_ = v___x_3333_;
goto v___jp_3321_;
}
v___jp_3321_:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3323_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__5));
v___x_3324_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_ref_3320_);
v___x_3325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3323_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
lean_inc(v___y_3322_);
v___x_3326_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___y_3322_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
v___x_3327_ = 0;
v___x_3328_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3328_, 0, v___x_3326_);
lean_ctor_set_uint8(v___x_3328_, sizeof(void*)*1, v___x_3327_);
v___x_3329_ = l_Repr_addAppParen(v___x_3328_, v_prec_3305_);
return v___x_3329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr___boxed(lean_object* v_x_3334_, lean_object* v_prec_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Std_Http_instReprURIReference_repr(v_x_3334_, v_prec_3335_);
lean_dec(v_prec_3335_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURIReference___lam__2(lean_object* v___f_3343_, lean_object* v___f_3344_, lean_object* v_x_3345_){
_start:
{
lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; 
if (lean_obj_tag(v_x_3345_) == 0)
{
lean_object* v_uri_3354_; lean_object* v_scheme_3355_; lean_object* v_authority_3356_; lean_object* v_path_3357_; lean_object* v_query_3358_; lean_object* v_fragment_3359_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3382_; 
lean_dec_ref(v___f_3344_);
v_uri_3354_ = lean_ctor_get(v_x_3345_, 0);
lean_inc_ref(v_uri_3354_);
lean_dec_ref_known(v_x_3345_, 1);
v_scheme_3355_ = lean_ctor_get(v_uri_3354_, 0);
lean_inc_ref(v_scheme_3355_);
v_authority_3356_ = lean_ctor_get(v_uri_3354_, 1);
lean_inc(v_authority_3356_);
v_path_3357_ = lean_ctor_get(v_uri_3354_, 2);
lean_inc_ref(v_path_3357_);
v_query_3358_ = lean_ctor_get(v_uri_3354_, 3);
lean_inc(v_query_3358_);
v_fragment_3359_ = lean_ctor_get(v_uri_3354_, 4);
lean_inc(v_fragment_3359_);
lean_dec_ref(v_uri_3354_);
if (lean_obj_tag(v_authority_3356_) == 0)
{
lean_object* v___x_3393_; 
v___x_3393_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3382_ = v___x_3393_;
goto v___jp_3381_;
}
else
{
lean_object* v_val_3394_; lean_object* v_userInfo_3395_; lean_object* v_host_3396_; lean_object* v_port_3397_; lean_object* v___x_3398_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3417_; 
v_val_3394_ = lean_ctor_get(v_authority_3356_, 0);
lean_inc(v_val_3394_);
lean_dec_ref_known(v_authority_3356_, 1);
v_userInfo_3395_ = lean_ctor_get(v_val_3394_, 0);
lean_inc(v_userInfo_3395_);
v_host_3396_ = lean_ctor_get(v_val_3394_, 1);
lean_inc_ref(v_host_3396_);
v_port_3397_ = lean_ctor_get(v_val_3394_, 2);
lean_inc(v_port_3397_);
lean_dec(v_val_3394_);
v___x_3398_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3395_) == 0)
{
lean_object* v___x_3427_; 
v___x_3427_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3417_ = v___x_3427_;
goto v___jp_3416_;
}
else
{
lean_object* v_val_3428_; lean_object* v_password_3429_; 
v_val_3428_ = lean_ctor_get(v_userInfo_3395_, 0);
lean_inc(v_val_3428_);
lean_dec_ref_known(v_userInfo_3395_, 1);
v_password_3429_ = lean_ctor_get(v_val_3428_, 1);
if (lean_obj_tag(v_password_3429_) == 0)
{
lean_object* v_username_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v_username_3430_ = lean_ctor_get(v_val_3428_, 0);
lean_inc_ref(v_username_3430_);
lean_dec(v_val_3428_);
v___x_3431_ = lean_string_from_utf8_unchecked(v_username_3430_);
v___x_3432_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3433_ = lean_string_append(v___x_3431_, v___x_3432_);
v___y_3417_ = v___x_3433_;
goto v___jp_3416_;
}
else
{
lean_object* v_username_3434_; lean_object* v_val_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
lean_inc_ref(v_password_3429_);
v_username_3434_ = lean_ctor_get(v_val_3428_, 0);
lean_inc_ref(v_username_3434_);
lean_dec(v_val_3428_);
v_val_3435_ = lean_ctor_get(v_password_3429_, 0);
lean_inc(v_val_3435_);
lean_dec_ref_known(v_password_3429_, 1);
v___x_3436_ = lean_string_from_utf8_unchecked(v_username_3434_);
v___x_3437_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3438_ = lean_string_append(v___x_3436_, v___x_3437_);
v___x_3439_ = lean_string_from_utf8_unchecked(v_val_3435_);
v___x_3440_ = lean_string_append(v___x_3438_, v___x_3439_);
lean_dec_ref(v___x_3439_);
v___x_3441_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3442_ = lean_string_append(v___x_3440_, v___x_3441_);
v___y_3417_ = v___x_3442_;
goto v___jp_3416_;
}
}
v___jp_3399_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3403_ = lean_string_append(v___y_3400_, v___y_3401_);
lean_dec_ref(v___y_3401_);
v___x_3404_ = lean_string_append(v___x_3403_, v___y_3402_);
lean_dec_ref(v___y_3402_);
v___x_3405_ = lean_string_append(v___x_3398_, v___x_3404_);
lean_dec_ref(v___x_3404_);
v___y_3382_ = v___x_3405_;
goto v___jp_3381_;
}
v___jp_3406_:
{
switch(lean_obj_tag(v_port_3397_))
{
case 0:
{
lean_object* v___x_3409_; 
v___x_3409_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3400_ = v___y_3407_;
v___y_3401_ = v___y_3408_;
v___y_3402_ = v___x_3409_;
goto v___jp_3399_;
}
case 1:
{
lean_object* v___x_3410_; 
v___x_3410_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3400_ = v___y_3407_;
v___y_3401_ = v___y_3408_;
v___y_3402_ = v___x_3410_;
goto v___jp_3399_;
}
default: 
{
uint16_t v_port_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v_port_3411_ = lean_ctor_get_uint16(v_port_3397_, 0);
lean_dec_ref_known(v_port_3397_, 0);
v___x_3412_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3413_ = lean_uint16_to_nat(v_port_3411_);
v___x_3414_ = l_Nat_reprFast(v___x_3413_);
v___x_3415_ = lean_string_append(v___x_3412_, v___x_3414_);
lean_dec_ref(v___x_3414_);
v___y_3400_ = v___y_3407_;
v___y_3401_ = v___y_3408_;
v___y_3402_ = v___x_3415_;
goto v___jp_3399_;
}
}
}
v___jp_3416_:
{
switch(lean_obj_tag(v_host_3396_))
{
case 0:
{
lean_object* v_name_3418_; 
v_name_3418_ = lean_ctor_get(v_host_3396_, 0);
lean_inc_ref(v_name_3418_);
lean_dec_ref_known(v_host_3396_, 1);
v___y_3407_ = v___y_3417_;
v___y_3408_ = v_name_3418_;
goto v___jp_3406_;
}
case 1:
{
lean_object* v_ipv4_3419_; lean_object* v___x_3420_; 
v_ipv4_3419_ = lean_ctor_get(v_host_3396_, 0);
lean_inc_ref(v_ipv4_3419_);
lean_dec_ref_known(v_host_3396_, 1);
v___x_3420_ = lean_uv_ntop_v4(v_ipv4_3419_);
lean_dec_ref(v_ipv4_3419_);
v___y_3407_ = v___y_3417_;
v___y_3408_ = v___x_3420_;
goto v___jp_3406_;
}
default: 
{
lean_object* v_ipv6_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v_ipv6_3421_ = lean_ctor_get(v_host_3396_, 0);
lean_inc_ref(v_ipv6_3421_);
lean_dec_ref_known(v_host_3396_, 1);
v___x_3422_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3423_ = lean_uv_ntop_v6(v_ipv6_3421_);
lean_dec_ref(v_ipv6_3421_);
v___x_3424_ = lean_string_append(v___x_3422_, v___x_3423_);
lean_dec_ref(v___x_3423_);
v___x_3425_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3426_ = lean_string_append(v___x_3424_, v___x_3425_);
v___y_3407_ = v___y_3417_;
v___y_3408_ = v___x_3426_;
goto v___jp_3406_;
}
}
}
}
v___jp_3360_:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3365_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3366_ = lean_string_append(v_scheme_3355_, v___x_3365_);
v___x_3367_ = lean_string_append(v___x_3366_, v___y_3361_);
lean_dec_ref(v___y_3361_);
v___x_3368_ = lean_string_append(v___x_3367_, v___y_3363_);
lean_dec_ref(v___y_3363_);
v___x_3369_ = lean_string_append(v___x_3368_, v___y_3362_);
lean_dec_ref(v___y_3362_);
v___x_3370_ = lean_string_append(v___x_3369_, v___y_3364_);
lean_dec_ref(v___y_3364_);
return v___x_3370_;
}
v___jp_3371_:
{
lean_object* v_queryPart_3374_; 
v_queryPart_3374_ = l_Std_Http_URI_Query_formatOption(v_query_3358_);
if (lean_obj_tag(v_fragment_3359_) == 0)
{
lean_object* v___x_3375_; 
v___x_3375_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3361_ = v___y_3372_;
v___y_3362_ = v_queryPart_3374_;
v___y_3363_ = v___y_3373_;
v___y_3364_ = v___x_3375_;
goto v___jp_3360_;
}
else
{
lean_object* v_val_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v_val_3376_ = lean_ctor_get(v_fragment_3359_, 0);
lean_inc(v_val_3376_);
lean_dec_ref_known(v_fragment_3359_, 1);
v___x_3377_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3378_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3376_);
lean_dec(v_val_3376_);
v___x_3379_ = lean_string_from_utf8_unchecked(v___x_3378_);
v___x_3380_ = lean_string_append(v___x_3377_, v___x_3379_);
lean_dec_ref(v___x_3379_);
v___y_3361_ = v___y_3372_;
v___y_3362_ = v_queryPart_3374_;
v___y_3363_ = v___y_3373_;
v___y_3364_ = v___x_3380_;
goto v___jp_3360_;
}
}
v___jp_3381_:
{
lean_object* v_segments_3383_; uint8_t v_absolute_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; size_t v_sz_3387_; size_t v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v_result_3391_; 
v_segments_3383_ = lean_ctor_get(v_path_3357_, 0);
lean_inc_ref(v_segments_3383_);
v_absolute_3384_ = lean_ctor_get_uint8(v_path_3357_, sizeof(void*)*1);
lean_dec_ref(v_path_3357_);
v___x_3385_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3386_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3387_ = lean_array_size(v_segments_3383_);
v___x_3388_ = ((size_t)0ULL);
v___x_3389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3386_, v___f_3343_, v_sz_3387_, v___x_3388_, v_segments_3383_);
v___x_3390_ = lean_array_to_list(v___x_3389_);
v_result_3391_ = l_String_intercalate(v___x_3385_, v___x_3390_);
if (v_absolute_3384_ == 0)
{
v___y_3372_ = v___y_3382_;
v___y_3373_ = v_result_3391_;
goto v___jp_3371_;
}
else
{
lean_object* v___x_3392_; 
v___x_3392_ = lean_string_append(v___x_3385_, v_result_3391_);
lean_dec_ref(v_result_3391_);
v___y_3372_ = v___y_3382_;
v___y_3373_ = v___x_3392_;
goto v___jp_3371_;
}
}
}
else
{
lean_object* v_ref_3443_; lean_object* v_authority_3444_; lean_object* v_path_3445_; lean_object* v_query_3446_; lean_object* v_fragment_3447_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3459_; 
lean_dec_ref(v___f_3343_);
v_ref_3443_ = lean_ctor_get(v_x_3345_, 0);
lean_inc_ref(v_ref_3443_);
lean_dec_ref_known(v_x_3345_, 1);
v_authority_3444_ = lean_ctor_get(v_ref_3443_, 0);
lean_inc(v_authority_3444_);
v_path_3445_ = lean_ctor_get(v_ref_3443_, 1);
lean_inc_ref(v_path_3445_);
v_query_3446_ = lean_ctor_get(v_ref_3443_, 2);
lean_inc(v_query_3446_);
v_fragment_3447_ = lean_ctor_get(v_ref_3443_, 3);
lean_inc(v_fragment_3447_);
lean_dec_ref(v_ref_3443_);
if (lean_obj_tag(v_authority_3444_) == 0)
{
lean_object* v___x_3470_; 
v___x_3470_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3459_ = v___x_3470_;
goto v___jp_3458_;
}
else
{
lean_object* v_val_3471_; lean_object* v_userInfo_3472_; lean_object* v_host_3473_; lean_object* v_port_3474_; lean_object* v___x_3475_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3494_; 
v_val_3471_ = lean_ctor_get(v_authority_3444_, 0);
lean_inc(v_val_3471_);
lean_dec_ref_known(v_authority_3444_, 1);
v_userInfo_3472_ = lean_ctor_get(v_val_3471_, 0);
lean_inc(v_userInfo_3472_);
v_host_3473_ = lean_ctor_get(v_val_3471_, 1);
lean_inc_ref(v_host_3473_);
v_port_3474_ = lean_ctor_get(v_val_3471_, 2);
lean_inc(v_port_3474_);
lean_dec(v_val_3471_);
v___x_3475_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3472_) == 0)
{
lean_object* v___x_3504_; 
v___x_3504_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3494_ = v___x_3504_;
goto v___jp_3493_;
}
else
{
lean_object* v_val_3505_; lean_object* v_password_3506_; 
v_val_3505_ = lean_ctor_get(v_userInfo_3472_, 0);
lean_inc(v_val_3505_);
lean_dec_ref_known(v_userInfo_3472_, 1);
v_password_3506_ = lean_ctor_get(v_val_3505_, 1);
if (lean_obj_tag(v_password_3506_) == 0)
{
lean_object* v_username_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v_username_3507_ = lean_ctor_get(v_val_3505_, 0);
lean_inc_ref(v_username_3507_);
lean_dec(v_val_3505_);
v___x_3508_ = lean_string_from_utf8_unchecked(v_username_3507_);
v___x_3509_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3510_ = lean_string_append(v___x_3508_, v___x_3509_);
v___y_3494_ = v___x_3510_;
goto v___jp_3493_;
}
else
{
lean_object* v_username_3511_; lean_object* v_val_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
lean_inc_ref(v_password_3506_);
v_username_3511_ = lean_ctor_get(v_val_3505_, 0);
lean_inc_ref(v_username_3511_);
lean_dec(v_val_3505_);
v_val_3512_ = lean_ctor_get(v_password_3506_, 0);
lean_inc(v_val_3512_);
lean_dec_ref_known(v_password_3506_, 1);
v___x_3513_ = lean_string_from_utf8_unchecked(v_username_3511_);
v___x_3514_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3515_ = lean_string_append(v___x_3513_, v___x_3514_);
v___x_3516_ = lean_string_from_utf8_unchecked(v_val_3512_);
v___x_3517_ = lean_string_append(v___x_3515_, v___x_3516_);
lean_dec_ref(v___x_3516_);
v___x_3518_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3519_ = lean_string_append(v___x_3517_, v___x_3518_);
v___y_3494_ = v___x_3519_;
goto v___jp_3493_;
}
}
v___jp_3476_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3480_ = lean_string_append(v___y_3477_, v___y_3478_);
lean_dec_ref(v___y_3478_);
v___x_3481_ = lean_string_append(v___x_3480_, v___y_3479_);
lean_dec_ref(v___y_3479_);
v___x_3482_ = lean_string_append(v___x_3475_, v___x_3481_);
lean_dec_ref(v___x_3481_);
v___y_3459_ = v___x_3482_;
goto v___jp_3458_;
}
v___jp_3483_:
{
switch(lean_obj_tag(v_port_3474_))
{
case 0:
{
lean_object* v___x_3486_; 
v___x_3486_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3477_ = v___y_3484_;
v___y_3478_ = v___y_3485_;
v___y_3479_ = v___x_3486_;
goto v___jp_3476_;
}
case 1:
{
lean_object* v___x_3487_; 
v___x_3487_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3477_ = v___y_3484_;
v___y_3478_ = v___y_3485_;
v___y_3479_ = v___x_3487_;
goto v___jp_3476_;
}
default: 
{
uint16_t v_port_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v_port_3488_ = lean_ctor_get_uint16(v_port_3474_, 0);
lean_dec_ref_known(v_port_3474_, 0);
v___x_3489_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3490_ = lean_uint16_to_nat(v_port_3488_);
v___x_3491_ = l_Nat_reprFast(v___x_3490_);
v___x_3492_ = lean_string_append(v___x_3489_, v___x_3491_);
lean_dec_ref(v___x_3491_);
v___y_3477_ = v___y_3484_;
v___y_3478_ = v___y_3485_;
v___y_3479_ = v___x_3492_;
goto v___jp_3476_;
}
}
}
v___jp_3493_:
{
switch(lean_obj_tag(v_host_3473_))
{
case 0:
{
lean_object* v_name_3495_; 
v_name_3495_ = lean_ctor_get(v_host_3473_, 0);
lean_inc_ref(v_name_3495_);
lean_dec_ref_known(v_host_3473_, 1);
v___y_3484_ = v___y_3494_;
v___y_3485_ = v_name_3495_;
goto v___jp_3483_;
}
case 1:
{
lean_object* v_ipv4_3496_; lean_object* v___x_3497_; 
v_ipv4_3496_ = lean_ctor_get(v_host_3473_, 0);
lean_inc_ref(v_ipv4_3496_);
lean_dec_ref_known(v_host_3473_, 1);
v___x_3497_ = lean_uv_ntop_v4(v_ipv4_3496_);
lean_dec_ref(v_ipv4_3496_);
v___y_3484_ = v___y_3494_;
v___y_3485_ = v___x_3497_;
goto v___jp_3483_;
}
default: 
{
lean_object* v_ipv6_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v_ipv6_3498_ = lean_ctor_get(v_host_3473_, 0);
lean_inc_ref(v_ipv6_3498_);
lean_dec_ref_known(v_host_3473_, 1);
v___x_3499_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3500_ = lean_uv_ntop_v6(v_ipv6_3498_);
lean_dec_ref(v_ipv6_3498_);
v___x_3501_ = lean_string_append(v___x_3499_, v___x_3500_);
lean_dec_ref(v___x_3500_);
v___x_3502_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3503_ = lean_string_append(v___x_3501_, v___x_3502_);
v___y_3484_ = v___y_3494_;
v___y_3485_ = v___x_3503_;
goto v___jp_3483_;
}
}
}
}
v___jp_3448_:
{
lean_object* v_queryPart_3451_; 
v_queryPart_3451_ = l_Std_Http_URI_Query_formatOption(v_query_3446_);
if (lean_obj_tag(v_fragment_3447_) == 0)
{
lean_object* v___x_3452_; 
v___x_3452_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3347_ = v_queryPart_3451_;
v___y_3348_ = v___y_3449_;
v___y_3349_ = v___y_3450_;
v___y_3350_ = v___x_3452_;
goto v___jp_3346_;
}
else
{
lean_object* v_val_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v_val_3453_ = lean_ctor_get(v_fragment_3447_, 0);
lean_inc(v_val_3453_);
lean_dec_ref_known(v_fragment_3447_, 1);
v___x_3454_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3455_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3453_);
lean_dec(v_val_3453_);
v___x_3456_ = lean_string_from_utf8_unchecked(v___x_3455_);
v___x_3457_ = lean_string_append(v___x_3454_, v___x_3456_);
lean_dec_ref(v___x_3456_);
v___y_3347_ = v_queryPart_3451_;
v___y_3348_ = v___y_3449_;
v___y_3349_ = v___y_3450_;
v___y_3350_ = v___x_3457_;
goto v___jp_3346_;
}
}
v___jp_3458_:
{
lean_object* v_segments_3460_; uint8_t v_absolute_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; size_t v_sz_3464_; size_t v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v_result_3468_; 
v_segments_3460_ = lean_ctor_get(v_path_3445_, 0);
lean_inc_ref(v_segments_3460_);
v_absolute_3461_ = lean_ctor_get_uint8(v_path_3445_, sizeof(void*)*1);
lean_dec_ref(v_path_3445_);
v___x_3462_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3463_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3464_ = lean_array_size(v_segments_3460_);
v___x_3465_ = ((size_t)0ULL);
v___x_3466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3463_, v___f_3344_, v_sz_3464_, v___x_3465_, v_segments_3460_);
v___x_3467_ = lean_array_to_list(v___x_3466_);
v_result_3468_ = l_String_intercalate(v___x_3462_, v___x_3467_);
if (v_absolute_3461_ == 0)
{
v___y_3449_ = v___y_3459_;
v___y_3450_ = v_result_3468_;
goto v___jp_3448_;
}
else
{
lean_object* v___x_3469_; 
v___x_3469_ = lean_string_append(v___x_3462_, v_result_3468_);
lean_dec_ref(v_result_3468_);
v___y_3449_ = v___y_3459_;
v___y_3450_ = v___x_3469_;
goto v___jp_3448_;
}
}
}
v___jp_3346_:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3351_ = lean_string_append(v___y_3348_, v___y_3349_);
lean_dec_ref(v___y_3349_);
v___x_3352_ = lean_string_append(v___x_3351_, v___y_3347_);
lean_dec_ref(v___y_3347_);
v___x_3353_ = lean_string_append(v___x_3352_, v___y_3350_);
lean_dec_ref(v___y_3350_);
return v___x_3353_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___impl(lean_object* v_x_3523_){
_start:
{
lean_object* v___x_3524_; 
v___x_3524_ = lean_obj_tag_nat(v_x_3523_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___impl___boxed(lean_object* v_x_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Std_Http_RequestTarget_ctorIdx___impl(v_x_3525_);
lean_dec(v_x_3525_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___redArg(lean_object* v_t_3527_, lean_object* v_k_3528_){
_start:
{
switch(lean_obj_tag(v_t_3527_))
{
case 0:
{
lean_object* v_path_3529_; lean_object* v_query_3530_; lean_object* v___x_3531_; 
v_path_3529_ = lean_ctor_get(v_t_3527_, 0);
lean_inc_ref(v_path_3529_);
v_query_3530_ = lean_ctor_get(v_t_3527_, 1);
lean_inc(v_query_3530_);
lean_dec_ref_known(v_t_3527_, 2);
v___x_3531_ = lean_apply_2(v_k_3528_, v_path_3529_, v_query_3530_);
return v___x_3531_;
}
case 3:
{
return v_k_3528_;
}
default: 
{
lean_object* v_uri_3532_; lean_object* v___x_3533_; 
v_uri_3532_ = lean_ctor_get(v_t_3527_, 0);
lean_inc_ref(v_uri_3532_);
lean_dec(v_t_3527_);
v___x_3533_ = lean_apply_1(v_k_3528_, v_uri_3532_);
return v___x_3533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim(lean_object* v_motive_3534_, lean_object* v_ctorIdx_3535_, lean_object* v_t_3536_, lean_object* v_h_3537_, lean_object* v_k_3538_){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3536_, v_k_3538_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___boxed(lean_object* v_motive_3540_, lean_object* v_ctorIdx_3541_, lean_object* v_t_3542_, lean_object* v_h_3543_, lean_object* v_k_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l_Std_Http_RequestTarget_ctorElim(v_motive_3540_, v_ctorIdx_3541_, v_t_3542_, v_h_3543_, v_k_3544_);
lean_dec(v_ctorIdx_3541_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim___redArg(lean_object* v_t_3546_, lean_object* v_originForm_3547_){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3546_, v_originForm_3547_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim(lean_object* v_motive_3549_, lean_object* v_t_3550_, lean_object* v_h_3551_, lean_object* v_originForm_3552_){
_start:
{
lean_object* v___x_3553_; 
v___x_3553_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3550_, v_originForm_3552_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim___redArg(lean_object* v_t_3554_, lean_object* v_absoluteForm_3555_){
_start:
{
lean_object* v___x_3556_; 
v___x_3556_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3554_, v_absoluteForm_3555_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim(lean_object* v_motive_3557_, lean_object* v_t_3558_, lean_object* v_h_3559_, lean_object* v_absoluteForm_3560_){
_start:
{
lean_object* v___x_3561_; 
v___x_3561_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3558_, v_absoluteForm_3560_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim___redArg(lean_object* v_t_3562_, lean_object* v_authorityForm_3563_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3562_, v_authorityForm_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim(lean_object* v_motive_3565_, lean_object* v_t_3566_, lean_object* v_h_3567_, lean_object* v_authorityForm_3568_){
_start:
{
lean_object* v___x_3569_; 
v___x_3569_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3566_, v_authorityForm_3568_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim___redArg(lean_object* v_t_3570_, lean_object* v_asteriskForm_3571_){
_start:
{
lean_object* v___x_3572_; 
v___x_3572_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3570_, v_asteriskForm_3571_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim(lean_object* v_motive_3573_, lean_object* v_t_3574_, lean_object* v_h_3575_, lean_object* v_asteriskForm_3576_){
_start:
{
lean_object* v___x_3577_; 
v___x_3577_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3574_, v_asteriskForm_3576_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object* v_x_3604_, lean_object* v_prec_3605_){
_start:
{
lean_object* v___y_3607_; 
switch(lean_obj_tag(v_x_3604_))
{
case 0:
{
lean_object* v_path_3613_; lean_object* v_query_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3638_; 
v_path_3613_ = lean_ctor_get(v_x_3604_, 0);
v_query_3614_ = lean_ctor_get(v_x_3604_, 1);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_x_3604_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3616_ = v_x_3604_;
v_isShared_3617_ = v_isSharedCheck_3638_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_query_3614_);
lean_inc(v_path_3613_);
lean_dec(v_x_3604_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3638_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___y_3619_; lean_object* v___x_3634_; uint8_t v___x_3635_; 
v___x_3634_ = lean_unsigned_to_nat(1024u);
v___x_3635_ = lean_nat_dec_le(v___x_3634_, v_prec_3605_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; 
v___x_3636_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3619_ = v___x_3636_;
goto v___jp_3618_;
}
else
{
lean_object* v___x_3637_; 
v___x_3637_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3619_ = v___x_3637_;
goto v___jp_3618_;
}
v___jp_3618_:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3625_; 
v___x_3620_ = lean_box(1);
v___x_3621_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__4));
v___x_3622_ = lean_unsigned_to_nat(1024u);
v___x_3623_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3613_);
if (v_isShared_3617_ == 0)
{
lean_ctor_set_tag(v___x_3616_, 5);
lean_ctor_set(v___x_3616_, 1, v___x_3623_);
lean_ctor_set(v___x_3616_, 0, v___x_3621_);
v___x_3625_ = v___x_3616_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3621_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v___x_3623_);
v___x_3625_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; uint8_t v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3625_);
lean_ctor_set(v___x_3626_, 1, v___x_3620_);
v___x_3627_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3614_, v___x_3622_);
v___x_3628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3626_);
lean_ctor_set(v___x_3628_, 1, v___x_3627_);
lean_inc(v___y_3619_);
v___x_3629_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3629_, 0, v___y_3619_);
lean_ctor_set(v___x_3629_, 1, v___x_3628_);
v___x_3630_ = 0;
v___x_3631_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3631_, 0, v___x_3629_);
lean_ctor_set_uint8(v___x_3631_, sizeof(void*)*1, v___x_3630_);
v___x_3632_ = l_Repr_addAppParen(v___x_3631_, v_prec_3605_);
return v___x_3632_;
}
}
}
}
case 1:
{
lean_object* v_uri_3639_; lean_object* v___y_3641_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v_uri_3639_ = lean_ctor_get(v_x_3604_, 0);
lean_inc_ref(v_uri_3639_);
lean_dec_ref_known(v_x_3604_, 1);
v___x_3649_ = lean_unsigned_to_nat(1024u);
v___x_3650_ = lean_nat_dec_le(v___x_3649_, v_prec_3605_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; 
v___x_3651_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3641_ = v___x_3651_;
goto v___jp_3640_;
}
else
{
lean_object* v___x_3652_; 
v___x_3652_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3641_ = v___x_3652_;
goto v___jp_3640_;
}
v___jp_3640_:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; uint8_t v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3642_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__7));
v___x_3643_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3639_);
v___x_3644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3642_);
lean_ctor_set(v___x_3644_, 1, v___x_3643_);
lean_inc(v___y_3641_);
v___x_3645_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___y_3641_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = 0;
v___x_3647_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3647_, 0, v___x_3645_);
lean_ctor_set_uint8(v___x_3647_, sizeof(void*)*1, v___x_3646_);
v___x_3648_ = l_Repr_addAppParen(v___x_3647_, v_prec_3605_);
return v___x_3648_;
}
}
case 2:
{
lean_object* v_authority_3653_; lean_object* v___y_3655_; lean_object* v___x_3663_; uint8_t v___x_3664_; 
v_authority_3653_ = lean_ctor_get(v_x_3604_, 0);
lean_inc_ref(v_authority_3653_);
lean_dec_ref_known(v_x_3604_, 1);
v___x_3663_ = lean_unsigned_to_nat(1024u);
v___x_3664_ = lean_nat_dec_le(v___x_3663_, v_prec_3605_);
if (v___x_3664_ == 0)
{
lean_object* v___x_3665_; 
v___x_3665_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3655_ = v___x_3665_;
goto v___jp_3654_;
}
else
{
lean_object* v___x_3666_; 
v___x_3666_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3655_ = v___x_3666_;
goto v___jp_3654_;
}
v___jp_3654_:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; uint8_t v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3656_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__10));
v___x_3657_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_authority_3653_);
v___x_3658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3656_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
lean_inc(v___y_3655_);
v___x_3659_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___y_3655_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = 0;
v___x_3661_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3661_, 0, v___x_3659_);
lean_ctor_set_uint8(v___x_3661_, sizeof(void*)*1, v___x_3660_);
v___x_3662_ = l_Repr_addAppParen(v___x_3661_, v_prec_3605_);
return v___x_3662_;
}
}
default: 
{
lean_object* v___x_3667_; uint8_t v___x_3668_; 
v___x_3667_ = lean_unsigned_to_nat(1024u);
v___x_3668_ = lean_nat_dec_le(v___x_3667_, v_prec_3605_);
if (v___x_3668_ == 0)
{
lean_object* v___x_3669_; 
v___x_3669_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3607_ = v___x_3669_;
goto v___jp_3606_;
}
else
{
lean_object* v___x_3670_; 
v___x_3670_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3607_ = v___x_3670_;
goto v___jp_3606_;
}
}
}
v___jp_3606_:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3608_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__1));
lean_inc(v___y_3607_);
v___x_3609_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___y_3607_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = 0;
v___x_3611_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3611_, 0, v___x_3609_);
lean_ctor_set_uint8(v___x_3611_, sizeof(void*)*1, v___x_3610_);
v___x_3612_ = l_Repr_addAppParen(v___x_3611_, v_prec_3605_);
return v___x_3612_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr___boxed(lean_object* v_x_3671_, lean_object* v_prec_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l_Std_Http_instReprRequestTarget_repr(v_x_3671_, v_prec_3672_);
lean_dec(v_prec_3672_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path(lean_object* v_x_3681_){
_start:
{
switch(lean_obj_tag(v_x_3681_))
{
case 0:
{
lean_object* v_path_3682_; 
v_path_3682_ = lean_ctor_get(v_x_3681_, 0);
lean_inc_ref(v_path_3682_);
return v_path_3682_;
}
case 1:
{
lean_object* v_uri_3683_; lean_object* v_path_3684_; 
v_uri_3683_ = lean_ctor_get(v_x_3681_, 0);
v_path_3684_ = lean_ctor_get(v_uri_3683_, 2);
lean_inc_ref(v_path_3684_);
return v_path_3684_;
}
default: 
{
lean_object* v___x_3685_; 
v___x_3685_ = ((lean_object*)(l_Std_Http_RequestTarget_path___closed__1));
return v___x_3685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path___boxed(lean_object* v_x_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Std_Http_RequestTarget_path(v_x_3686_);
lean_dec(v_x_3686_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query(lean_object* v_x_3688_){
_start:
{
switch(lean_obj_tag(v_x_3688_))
{
case 0:
{
lean_object* v_query_3689_; 
v_query_3689_ = lean_ctor_get(v_x_3688_, 1);
if (lean_obj_tag(v_query_3689_) == 0)
{
lean_object* v___x_3690_; 
v___x_3690_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3690_;
}
else
{
lean_object* v_val_3691_; 
v_val_3691_ = lean_ctor_get(v_query_3689_, 0);
lean_inc(v_val_3691_);
return v_val_3691_;
}
}
case 1:
{
lean_object* v_uri_3692_; lean_object* v_query_3693_; 
v_uri_3692_ = lean_ctor_get(v_x_3688_, 0);
v_query_3693_ = lean_ctor_get(v_uri_3692_, 3);
if (lean_obj_tag(v_query_3693_) == 0)
{
lean_object* v___x_3694_; 
v___x_3694_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3694_;
}
else
{
lean_object* v_val_3695_; 
v_val_3695_ = lean_ctor_get(v_query_3693_, 0);
lean_inc(v_val_3695_);
return v_val_3695_;
}
}
default: 
{
lean_object* v___x_3696_; 
v___x_3696_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query___boxed(lean_object* v_x_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l_Std_Http_RequestTarget_query(v_x_3697_);
lean_dec(v_x_3697_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authority_x3f(lean_object* v_x_3699_){
_start:
{
switch(lean_obj_tag(v_x_3699_))
{
case 2:
{
lean_object* v_authority_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
v_authority_3700_ = lean_ctor_get(v_x_3699_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v_x_3699_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v_x_3699_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_authority_3700_);
lean_dec(v_x_3699_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
lean_ctor_set_tag(v___x_3702_, 1);
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_authority_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
case 1:
{
lean_object* v_uri_3708_; lean_object* v_authority_3709_; 
v_uri_3708_ = lean_ctor_get(v_x_3699_, 0);
lean_inc_ref(v_uri_3708_);
lean_dec_ref_known(v_x_3699_, 1);
v_authority_3709_ = lean_ctor_get(v_uri_3708_, 1);
lean_inc(v_authority_3709_);
lean_dec_ref(v_uri_3708_);
return v_authority_3709_;
}
default: 
{
lean_object* v___x_3710_; 
lean_dec(v_x_3699_);
v___x_3710_ = lean_box(0);
return v___x_3710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__2(lean_object* v___f_3712_, lean_object* v___f_3713_, lean_object* v_x_3714_){
_start:
{
lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; 
switch(lean_obj_tag(v_x_3714_))
{
case 0:
{
lean_object* v_path_3721_; lean_object* v_query_3722_; lean_object* v___y_3724_; lean_object* v_segments_3727_; uint8_t v_absolute_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; size_t v_sz_3731_; size_t v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v_result_3735_; 
lean_dec_ref(v___f_3713_);
v_path_3721_ = lean_ctor_get(v_x_3714_, 0);
lean_inc_ref(v_path_3721_);
v_query_3722_ = lean_ctor_get(v_x_3714_, 1);
lean_inc(v_query_3722_);
lean_dec_ref_known(v_x_3714_, 2);
v_segments_3727_ = lean_ctor_get(v_path_3721_, 0);
lean_inc_ref(v_segments_3727_);
v_absolute_3728_ = lean_ctor_get_uint8(v_path_3721_, sizeof(void*)*1);
lean_dec_ref(v_path_3721_);
v___x_3729_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3730_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3731_ = lean_array_size(v_segments_3727_);
v___x_3732_ = ((size_t)0ULL);
v___x_3733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3730_, v___f_3712_, v_sz_3731_, v___x_3732_, v_segments_3727_);
v___x_3734_ = lean_array_to_list(v___x_3733_);
v_result_3735_ = l_String_intercalate(v___x_3729_, v___x_3734_);
if (v_absolute_3728_ == 0)
{
v___y_3724_ = v_result_3735_;
goto v___jp_3723_;
}
else
{
lean_object* v___x_3736_; 
v___x_3736_ = lean_string_append(v___x_3729_, v_result_3735_);
lean_dec_ref(v_result_3735_);
v___y_3724_ = v___x_3736_;
goto v___jp_3723_;
}
v___jp_3723_:
{
lean_object* v_queryStr_3725_; lean_object* v___x_3726_; 
v_queryStr_3725_ = l_Std_Http_URI_Query_formatOption(v_query_3722_);
v___x_3726_ = lean_string_append(v___y_3724_, v_queryStr_3725_);
lean_dec_ref(v_queryStr_3725_);
return v___x_3726_;
}
}
case 1:
{
lean_object* v_uri_3737_; lean_object* v_scheme_3738_; lean_object* v_authority_3739_; lean_object* v_path_3740_; lean_object* v_query_3741_; lean_object* v_fragment_3742_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3765_; 
lean_dec_ref(v___f_3712_);
v_uri_3737_ = lean_ctor_get(v_x_3714_, 0);
lean_inc_ref(v_uri_3737_);
lean_dec_ref_known(v_x_3714_, 1);
v_scheme_3738_ = lean_ctor_get(v_uri_3737_, 0);
lean_inc_ref(v_scheme_3738_);
v_authority_3739_ = lean_ctor_get(v_uri_3737_, 1);
lean_inc(v_authority_3739_);
v_path_3740_ = lean_ctor_get(v_uri_3737_, 2);
lean_inc_ref(v_path_3740_);
v_query_3741_ = lean_ctor_get(v_uri_3737_, 3);
lean_inc(v_query_3741_);
v_fragment_3742_ = lean_ctor_get(v_uri_3737_, 4);
lean_inc(v_fragment_3742_);
lean_dec_ref(v_uri_3737_);
if (lean_obj_tag(v_authority_3739_) == 0)
{
lean_object* v___x_3776_; 
v___x_3776_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3765_ = v___x_3776_;
goto v___jp_3764_;
}
else
{
lean_object* v_val_3777_; lean_object* v_userInfo_3778_; lean_object* v_host_3779_; lean_object* v_port_3780_; lean_object* v___x_3781_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3800_; 
v_val_3777_ = lean_ctor_get(v_authority_3739_, 0);
lean_inc(v_val_3777_);
lean_dec_ref_known(v_authority_3739_, 1);
v_userInfo_3778_ = lean_ctor_get(v_val_3777_, 0);
lean_inc(v_userInfo_3778_);
v_host_3779_ = lean_ctor_get(v_val_3777_, 1);
lean_inc_ref(v_host_3779_);
v_port_3780_ = lean_ctor_get(v_val_3777_, 2);
lean_inc(v_port_3780_);
lean_dec(v_val_3777_);
v___x_3781_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3778_) == 0)
{
lean_object* v___x_3810_; 
v___x_3810_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3800_ = v___x_3810_;
goto v___jp_3799_;
}
else
{
lean_object* v_val_3811_; lean_object* v_password_3812_; 
v_val_3811_ = lean_ctor_get(v_userInfo_3778_, 0);
lean_inc(v_val_3811_);
lean_dec_ref_known(v_userInfo_3778_, 1);
v_password_3812_ = lean_ctor_get(v_val_3811_, 1);
if (lean_obj_tag(v_password_3812_) == 0)
{
lean_object* v_username_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v_username_3813_ = lean_ctor_get(v_val_3811_, 0);
lean_inc_ref(v_username_3813_);
lean_dec(v_val_3811_);
v___x_3814_ = lean_string_from_utf8_unchecked(v_username_3813_);
v___x_3815_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3816_ = lean_string_append(v___x_3814_, v___x_3815_);
v___y_3800_ = v___x_3816_;
goto v___jp_3799_;
}
else
{
lean_object* v_username_3817_; lean_object* v_val_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
lean_inc_ref(v_password_3812_);
v_username_3817_ = lean_ctor_get(v_val_3811_, 0);
lean_inc_ref(v_username_3817_);
lean_dec(v_val_3811_);
v_val_3818_ = lean_ctor_get(v_password_3812_, 0);
lean_inc(v_val_3818_);
lean_dec_ref_known(v_password_3812_, 1);
v___x_3819_ = lean_string_from_utf8_unchecked(v_username_3817_);
v___x_3820_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3821_ = lean_string_append(v___x_3819_, v___x_3820_);
v___x_3822_ = lean_string_from_utf8_unchecked(v_val_3818_);
v___x_3823_ = lean_string_append(v___x_3821_, v___x_3822_);
lean_dec_ref(v___x_3822_);
v___x_3824_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3825_ = lean_string_append(v___x_3823_, v___x_3824_);
v___y_3800_ = v___x_3825_;
goto v___jp_3799_;
}
}
v___jp_3782_:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3786_ = lean_string_append(v___y_3783_, v___y_3784_);
lean_dec_ref(v___y_3784_);
v___x_3787_ = lean_string_append(v___x_3786_, v___y_3785_);
lean_dec_ref(v___y_3785_);
v___x_3788_ = lean_string_append(v___x_3781_, v___x_3787_);
lean_dec_ref(v___x_3787_);
v___y_3765_ = v___x_3788_;
goto v___jp_3764_;
}
v___jp_3789_:
{
switch(lean_obj_tag(v_port_3780_))
{
case 0:
{
lean_object* v___x_3792_; 
v___x_3792_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3783_ = v___y_3790_;
v___y_3784_ = v___y_3791_;
v___y_3785_ = v___x_3792_;
goto v___jp_3782_;
}
case 1:
{
lean_object* v___x_3793_; 
v___x_3793_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3783_ = v___y_3790_;
v___y_3784_ = v___y_3791_;
v___y_3785_ = v___x_3793_;
goto v___jp_3782_;
}
default: 
{
uint16_t v_port_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v_port_3794_ = lean_ctor_get_uint16(v_port_3780_, 0);
lean_dec_ref_known(v_port_3780_, 0);
v___x_3795_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3796_ = lean_uint16_to_nat(v_port_3794_);
v___x_3797_ = l_Nat_reprFast(v___x_3796_);
v___x_3798_ = lean_string_append(v___x_3795_, v___x_3797_);
lean_dec_ref(v___x_3797_);
v___y_3783_ = v___y_3790_;
v___y_3784_ = v___y_3791_;
v___y_3785_ = v___x_3798_;
goto v___jp_3782_;
}
}
}
v___jp_3799_:
{
switch(lean_obj_tag(v_host_3779_))
{
case 0:
{
lean_object* v_name_3801_; 
v_name_3801_ = lean_ctor_get(v_host_3779_, 0);
lean_inc_ref(v_name_3801_);
lean_dec_ref_known(v_host_3779_, 1);
v___y_3790_ = v___y_3800_;
v___y_3791_ = v_name_3801_;
goto v___jp_3789_;
}
case 1:
{
lean_object* v_ipv4_3802_; lean_object* v___x_3803_; 
v_ipv4_3802_ = lean_ctor_get(v_host_3779_, 0);
lean_inc_ref(v_ipv4_3802_);
lean_dec_ref_known(v_host_3779_, 1);
v___x_3803_ = lean_uv_ntop_v4(v_ipv4_3802_);
lean_dec_ref(v_ipv4_3802_);
v___y_3790_ = v___y_3800_;
v___y_3791_ = v___x_3803_;
goto v___jp_3789_;
}
default: 
{
lean_object* v_ipv6_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v_ipv6_3804_ = lean_ctor_get(v_host_3779_, 0);
lean_inc_ref(v_ipv6_3804_);
lean_dec_ref_known(v_host_3779_, 1);
v___x_3805_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3806_ = lean_uv_ntop_v6(v_ipv6_3804_);
lean_dec_ref(v_ipv6_3804_);
v___x_3807_ = lean_string_append(v___x_3805_, v___x_3806_);
lean_dec_ref(v___x_3806_);
v___x_3808_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3809_ = lean_string_append(v___x_3807_, v___x_3808_);
v___y_3790_ = v___y_3800_;
v___y_3791_ = v___x_3809_;
goto v___jp_3789_;
}
}
}
}
v___jp_3743_:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3748_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3749_ = lean_string_append(v_scheme_3738_, v___x_3748_);
v___x_3750_ = lean_string_append(v___x_3749_, v___y_3744_);
lean_dec_ref(v___y_3744_);
v___x_3751_ = lean_string_append(v___x_3750_, v___y_3745_);
lean_dec_ref(v___y_3745_);
v___x_3752_ = lean_string_append(v___x_3751_, v___y_3746_);
lean_dec_ref(v___y_3746_);
v___x_3753_ = lean_string_append(v___x_3752_, v___y_3747_);
lean_dec_ref(v___y_3747_);
return v___x_3753_;
}
v___jp_3754_:
{
lean_object* v_queryPart_3757_; 
v_queryPart_3757_ = l_Std_Http_URI_Query_formatOption(v_query_3741_);
if (lean_obj_tag(v_fragment_3742_) == 0)
{
lean_object* v___x_3758_; 
v___x_3758_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3744_ = v___y_3755_;
v___y_3745_ = v___y_3756_;
v___y_3746_ = v_queryPart_3757_;
v___y_3747_ = v___x_3758_;
goto v___jp_3743_;
}
else
{
lean_object* v_val_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v_val_3759_ = lean_ctor_get(v_fragment_3742_, 0);
lean_inc(v_val_3759_);
lean_dec_ref_known(v_fragment_3742_, 1);
v___x_3760_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3761_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3759_);
lean_dec(v_val_3759_);
v___x_3762_ = lean_string_from_utf8_unchecked(v___x_3761_);
v___x_3763_ = lean_string_append(v___x_3760_, v___x_3762_);
lean_dec_ref(v___x_3762_);
v___y_3744_ = v___y_3755_;
v___y_3745_ = v___y_3756_;
v___y_3746_ = v_queryPart_3757_;
v___y_3747_ = v___x_3763_;
goto v___jp_3743_;
}
}
v___jp_3764_:
{
lean_object* v_segments_3766_; uint8_t v_absolute_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; size_t v_sz_3770_; size_t v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v_result_3774_; 
v_segments_3766_ = lean_ctor_get(v_path_3740_, 0);
lean_inc_ref(v_segments_3766_);
v_absolute_3767_ = lean_ctor_get_uint8(v_path_3740_, sizeof(void*)*1);
lean_dec_ref(v_path_3740_);
v___x_3768_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3769_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3770_ = lean_array_size(v_segments_3766_);
v___x_3771_ = ((size_t)0ULL);
v___x_3772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3769_, v___f_3713_, v_sz_3770_, v___x_3771_, v_segments_3766_);
v___x_3773_ = lean_array_to_list(v___x_3772_);
v_result_3774_ = l_String_intercalate(v___x_3768_, v___x_3773_);
if (v_absolute_3767_ == 0)
{
v___y_3755_ = v___y_3765_;
v___y_3756_ = v_result_3774_;
goto v___jp_3754_;
}
else
{
lean_object* v___x_3775_; 
v___x_3775_ = lean_string_append(v___x_3768_, v_result_3774_);
lean_dec_ref(v_result_3774_);
v___y_3755_ = v___y_3765_;
v___y_3756_ = v___x_3775_;
goto v___jp_3754_;
}
}
}
case 2:
{
lean_object* v_authority_3826_; lean_object* v_userInfo_3827_; lean_object* v_host_3828_; lean_object* v_port_3829_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3841_; 
lean_dec_ref(v___f_3713_);
lean_dec_ref(v___f_3712_);
v_authority_3826_ = lean_ctor_get(v_x_3714_, 0);
lean_inc_ref(v_authority_3826_);
lean_dec_ref_known(v_x_3714_, 1);
v_userInfo_3827_ = lean_ctor_get(v_authority_3826_, 0);
lean_inc(v_userInfo_3827_);
v_host_3828_ = lean_ctor_get(v_authority_3826_, 1);
lean_inc_ref(v_host_3828_);
v_port_3829_ = lean_ctor_get(v_authority_3826_, 2);
lean_inc(v_port_3829_);
lean_dec_ref(v_authority_3826_);
if (lean_obj_tag(v_userInfo_3827_) == 0)
{
lean_object* v___x_3851_; 
v___x_3851_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3841_ = v___x_3851_;
goto v___jp_3840_;
}
else
{
lean_object* v_val_3852_; lean_object* v_password_3853_; 
v_val_3852_ = lean_ctor_get(v_userInfo_3827_, 0);
lean_inc(v_val_3852_);
lean_dec_ref_known(v_userInfo_3827_, 1);
v_password_3853_ = lean_ctor_get(v_val_3852_, 1);
if (lean_obj_tag(v_password_3853_) == 0)
{
lean_object* v_username_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v_username_3854_ = lean_ctor_get(v_val_3852_, 0);
lean_inc_ref(v_username_3854_);
lean_dec(v_val_3852_);
v___x_3855_ = lean_string_from_utf8_unchecked(v_username_3854_);
v___x_3856_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3857_ = lean_string_append(v___x_3855_, v___x_3856_);
v___y_3841_ = v___x_3857_;
goto v___jp_3840_;
}
else
{
lean_object* v_username_3858_; lean_object* v_val_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
lean_inc_ref(v_password_3853_);
v_username_3858_ = lean_ctor_get(v_val_3852_, 0);
lean_inc_ref(v_username_3858_);
lean_dec(v_val_3852_);
v_val_3859_ = lean_ctor_get(v_password_3853_, 0);
lean_inc(v_val_3859_);
lean_dec_ref_known(v_password_3853_, 1);
v___x_3860_ = lean_string_from_utf8_unchecked(v_username_3858_);
v___x_3861_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3862_ = lean_string_append(v___x_3860_, v___x_3861_);
v___x_3863_ = lean_string_from_utf8_unchecked(v_val_3859_);
v___x_3864_ = lean_string_append(v___x_3862_, v___x_3863_);
lean_dec_ref(v___x_3863_);
v___x_3865_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3866_ = lean_string_append(v___x_3864_, v___x_3865_);
v___y_3841_ = v___x_3866_;
goto v___jp_3840_;
}
}
v___jp_3830_:
{
switch(lean_obj_tag(v_port_3829_))
{
case 0:
{
lean_object* v___x_3833_; 
v___x_3833_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3716_ = v___y_3832_;
v___y_3717_ = v___y_3831_;
v___y_3718_ = v___x_3833_;
goto v___jp_3715_;
}
case 1:
{
lean_object* v___x_3834_; 
v___x_3834_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3716_ = v___y_3832_;
v___y_3717_ = v___y_3831_;
v___y_3718_ = v___x_3834_;
goto v___jp_3715_;
}
default: 
{
uint16_t v_port_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v_port_3835_ = lean_ctor_get_uint16(v_port_3829_, 0);
lean_dec_ref_known(v_port_3829_, 0);
v___x_3836_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3837_ = lean_uint16_to_nat(v_port_3835_);
v___x_3838_ = l_Nat_reprFast(v___x_3837_);
v___x_3839_ = lean_string_append(v___x_3836_, v___x_3838_);
lean_dec_ref(v___x_3838_);
v___y_3716_ = v___y_3832_;
v___y_3717_ = v___y_3831_;
v___y_3718_ = v___x_3839_;
goto v___jp_3715_;
}
}
}
v___jp_3840_:
{
switch(lean_obj_tag(v_host_3828_))
{
case 0:
{
lean_object* v_name_3842_; 
v_name_3842_ = lean_ctor_get(v_host_3828_, 0);
lean_inc_ref(v_name_3842_);
lean_dec_ref_known(v_host_3828_, 1);
v___y_3831_ = v___y_3841_;
v___y_3832_ = v_name_3842_;
goto v___jp_3830_;
}
case 1:
{
lean_object* v_ipv4_3843_; lean_object* v___x_3844_; 
v_ipv4_3843_ = lean_ctor_get(v_host_3828_, 0);
lean_inc_ref(v_ipv4_3843_);
lean_dec_ref_known(v_host_3828_, 1);
v___x_3844_ = lean_uv_ntop_v4(v_ipv4_3843_);
lean_dec_ref(v_ipv4_3843_);
v___y_3831_ = v___y_3841_;
v___y_3832_ = v___x_3844_;
goto v___jp_3830_;
}
default: 
{
lean_object* v_ipv6_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v_ipv6_3845_ = lean_ctor_get(v_host_3828_, 0);
lean_inc_ref(v_ipv6_3845_);
lean_dec_ref_known(v_host_3828_, 1);
v___x_3846_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3847_ = lean_uv_ntop_v6(v_ipv6_3845_);
lean_dec_ref(v_ipv6_3845_);
v___x_3848_ = lean_string_append(v___x_3846_, v___x_3847_);
lean_dec_ref(v___x_3847_);
v___x_3849_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3850_ = lean_string_append(v___x_3848_, v___x_3849_);
v___y_3831_ = v___y_3841_;
v___y_3832_ = v___x_3850_;
goto v___jp_3830_;
}
}
}
}
default: 
{
lean_object* v___x_3867_; 
lean_dec_ref(v___f_3713_);
lean_dec_ref(v___f_3712_);
v___x_3867_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__2___closed__0));
return v___x_3867_;
}
}
v___jp_3715_:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = lean_string_append(v___y_3717_, v___y_3716_);
lean_dec_ref(v___y_3716_);
v___x_3720_ = lean_string_append(v___x_3719_, v___y_3718_);
lean_dec_ref(v___y_3718_);
return v___x_3720_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__2(lean_object* v___f_3871_, lean_object* v___f_3872_, lean_object* v_buffer_3873_, lean_object* v_target_3874_){
_start:
{
lean_object* v___y_3876_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; 
switch(lean_obj_tag(v_target_3874_))
{
case 0:
{
lean_object* v_path_3896_; lean_object* v_query_3897_; lean_object* v___y_3899_; lean_object* v_segments_3902_; uint8_t v_absolute_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; size_t v_sz_3906_; size_t v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v_result_3910_; 
lean_dec_ref(v___f_3872_);
v_path_3896_ = lean_ctor_get(v_target_3874_, 0);
lean_inc_ref(v_path_3896_);
v_query_3897_ = lean_ctor_get(v_target_3874_, 1);
lean_inc(v_query_3897_);
lean_dec_ref_known(v_target_3874_, 2);
v_segments_3902_ = lean_ctor_get(v_path_3896_, 0);
lean_inc_ref(v_segments_3902_);
v_absolute_3903_ = lean_ctor_get_uint8(v_path_3896_, sizeof(void*)*1);
lean_dec_ref(v_path_3896_);
v___x_3904_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3905_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3906_ = lean_array_size(v_segments_3902_);
v___x_3907_ = ((size_t)0ULL);
v___x_3908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3905_, v___f_3871_, v_sz_3906_, v___x_3907_, v_segments_3902_);
v___x_3909_ = lean_array_to_list(v___x_3908_);
v_result_3910_ = l_String_intercalate(v___x_3904_, v___x_3909_);
if (v_absolute_3903_ == 0)
{
v___y_3899_ = v_result_3910_;
goto v___jp_3898_;
}
else
{
lean_object* v___x_3911_; 
v___x_3911_ = lean_string_append(v___x_3904_, v_result_3910_);
lean_dec_ref(v_result_3910_);
v___y_3899_ = v___x_3911_;
goto v___jp_3898_;
}
v___jp_3898_:
{
lean_object* v_queryStr_3900_; lean_object* v___x_3901_; 
v_queryStr_3900_ = l_Std_Http_URI_Query_formatOption(v_query_3897_);
v___x_3901_ = lean_string_append(v___y_3899_, v_queryStr_3900_);
lean_dec_ref(v_queryStr_3900_);
v___y_3876_ = v___x_3901_;
goto v___jp_3875_;
}
}
case 1:
{
lean_object* v_uri_3912_; lean_object* v_scheme_3913_; lean_object* v_authority_3914_; lean_object* v_path_3915_; lean_object* v_query_3916_; lean_object* v_fragment_3917_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3940_; 
lean_dec_ref(v___f_3871_);
v_uri_3912_ = lean_ctor_get(v_target_3874_, 0);
lean_inc_ref(v_uri_3912_);
lean_dec_ref_known(v_target_3874_, 1);
v_scheme_3913_ = lean_ctor_get(v_uri_3912_, 0);
lean_inc_ref(v_scheme_3913_);
v_authority_3914_ = lean_ctor_get(v_uri_3912_, 1);
lean_inc(v_authority_3914_);
v_path_3915_ = lean_ctor_get(v_uri_3912_, 2);
lean_inc_ref(v_path_3915_);
v_query_3916_ = lean_ctor_get(v_uri_3912_, 3);
lean_inc(v_query_3916_);
v_fragment_3917_ = lean_ctor_get(v_uri_3912_, 4);
lean_inc(v_fragment_3917_);
lean_dec_ref(v_uri_3912_);
if (lean_obj_tag(v_authority_3914_) == 0)
{
lean_object* v___x_3951_; 
v___x_3951_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3940_ = v___x_3951_;
goto v___jp_3939_;
}
else
{
lean_object* v_val_3952_; lean_object* v_userInfo_3953_; lean_object* v_host_3954_; lean_object* v_port_3955_; lean_object* v___x_3956_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3975_; 
v_val_3952_ = lean_ctor_get(v_authority_3914_, 0);
lean_inc(v_val_3952_);
lean_dec_ref_known(v_authority_3914_, 1);
v_userInfo_3953_ = lean_ctor_get(v_val_3952_, 0);
lean_inc(v_userInfo_3953_);
v_host_3954_ = lean_ctor_get(v_val_3952_, 1);
lean_inc_ref(v_host_3954_);
v_port_3955_ = lean_ctor_get(v_val_3952_, 2);
lean_inc(v_port_3955_);
lean_dec(v_val_3952_);
v___x_3956_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3953_) == 0)
{
lean_object* v___x_3985_; 
v___x_3985_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3975_ = v___x_3985_;
goto v___jp_3974_;
}
else
{
lean_object* v_val_3986_; lean_object* v_password_3987_; 
v_val_3986_ = lean_ctor_get(v_userInfo_3953_, 0);
lean_inc(v_val_3986_);
lean_dec_ref_known(v_userInfo_3953_, 1);
v_password_3987_ = lean_ctor_get(v_val_3986_, 1);
if (lean_obj_tag(v_password_3987_) == 0)
{
lean_object* v_username_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v_username_3988_ = lean_ctor_get(v_val_3986_, 0);
lean_inc_ref(v_username_3988_);
lean_dec(v_val_3986_);
v___x_3989_ = lean_string_from_utf8_unchecked(v_username_3988_);
v___x_3990_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3991_ = lean_string_append(v___x_3989_, v___x_3990_);
v___y_3975_ = v___x_3991_;
goto v___jp_3974_;
}
else
{
lean_object* v_username_3992_; lean_object* v_val_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
lean_inc_ref(v_password_3987_);
v_username_3992_ = lean_ctor_get(v_val_3986_, 0);
lean_inc_ref(v_username_3992_);
lean_dec(v_val_3986_);
v_val_3993_ = lean_ctor_get(v_password_3987_, 0);
lean_inc(v_val_3993_);
lean_dec_ref_known(v_password_3987_, 1);
v___x_3994_ = lean_string_from_utf8_unchecked(v_username_3992_);
v___x_3995_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3996_ = lean_string_append(v___x_3994_, v___x_3995_);
v___x_3997_ = lean_string_from_utf8_unchecked(v_val_3993_);
v___x_3998_ = lean_string_append(v___x_3996_, v___x_3997_);
lean_dec_ref(v___x_3997_);
v___x_3999_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4000_ = lean_string_append(v___x_3998_, v___x_3999_);
v___y_3975_ = v___x_4000_;
goto v___jp_3974_;
}
}
v___jp_3957_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3961_ = lean_string_append(v___y_3959_, v___y_3958_);
lean_dec_ref(v___y_3958_);
v___x_3962_ = lean_string_append(v___x_3961_, v___y_3960_);
lean_dec_ref(v___y_3960_);
v___x_3963_ = lean_string_append(v___x_3956_, v___x_3962_);
lean_dec_ref(v___x_3962_);
v___y_3940_ = v___x_3963_;
goto v___jp_3939_;
}
v___jp_3964_:
{
switch(lean_obj_tag(v_port_3955_))
{
case 0:
{
lean_object* v___x_3967_; 
v___x_3967_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3958_ = v___y_3966_;
v___y_3959_ = v___y_3965_;
v___y_3960_ = v___x_3967_;
goto v___jp_3957_;
}
case 1:
{
lean_object* v___x_3968_; 
v___x_3968_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3958_ = v___y_3966_;
v___y_3959_ = v___y_3965_;
v___y_3960_ = v___x_3968_;
goto v___jp_3957_;
}
default: 
{
uint16_t v_port_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v_port_3969_ = lean_ctor_get_uint16(v_port_3955_, 0);
lean_dec_ref_known(v_port_3955_, 0);
v___x_3970_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3971_ = lean_uint16_to_nat(v_port_3969_);
v___x_3972_ = l_Nat_reprFast(v___x_3971_);
v___x_3973_ = lean_string_append(v___x_3970_, v___x_3972_);
lean_dec_ref(v___x_3972_);
v___y_3958_ = v___y_3966_;
v___y_3959_ = v___y_3965_;
v___y_3960_ = v___x_3973_;
goto v___jp_3957_;
}
}
}
v___jp_3974_:
{
switch(lean_obj_tag(v_host_3954_))
{
case 0:
{
lean_object* v_name_3976_; 
v_name_3976_ = lean_ctor_get(v_host_3954_, 0);
lean_inc_ref(v_name_3976_);
lean_dec_ref_known(v_host_3954_, 1);
v___y_3965_ = v___y_3975_;
v___y_3966_ = v_name_3976_;
goto v___jp_3964_;
}
case 1:
{
lean_object* v_ipv4_3977_; lean_object* v___x_3978_; 
v_ipv4_3977_ = lean_ctor_get(v_host_3954_, 0);
lean_inc_ref(v_ipv4_3977_);
lean_dec_ref_known(v_host_3954_, 1);
v___x_3978_ = lean_uv_ntop_v4(v_ipv4_3977_);
lean_dec_ref(v_ipv4_3977_);
v___y_3965_ = v___y_3975_;
v___y_3966_ = v___x_3978_;
goto v___jp_3964_;
}
default: 
{
lean_object* v_ipv6_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v_ipv6_3979_ = lean_ctor_get(v_host_3954_, 0);
lean_inc_ref(v_ipv6_3979_);
lean_dec_ref_known(v_host_3954_, 1);
v___x_3980_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3981_ = lean_uv_ntop_v6(v_ipv6_3979_);
lean_dec_ref(v_ipv6_3979_);
v___x_3982_ = lean_string_append(v___x_3980_, v___x_3981_);
lean_dec_ref(v___x_3981_);
v___x_3983_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3984_ = lean_string_append(v___x_3982_, v___x_3983_);
v___y_3965_ = v___y_3975_;
v___y_3966_ = v___x_3984_;
goto v___jp_3964_;
}
}
}
}
v___jp_3918_:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3923_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3924_ = lean_string_append(v_scheme_3913_, v___x_3923_);
v___x_3925_ = lean_string_append(v___x_3924_, v___y_3920_);
lean_dec_ref(v___y_3920_);
v___x_3926_ = lean_string_append(v___x_3925_, v___y_3921_);
lean_dec_ref(v___y_3921_);
v___x_3927_ = lean_string_append(v___x_3926_, v___y_3919_);
lean_dec_ref(v___y_3919_);
v___x_3928_ = lean_string_append(v___x_3927_, v___y_3922_);
lean_dec_ref(v___y_3922_);
v___y_3876_ = v___x_3928_;
goto v___jp_3875_;
}
v___jp_3929_:
{
lean_object* v_queryPart_3932_; 
v_queryPart_3932_ = l_Std_Http_URI_Query_formatOption(v_query_3916_);
if (lean_obj_tag(v_fragment_3917_) == 0)
{
lean_object* v___x_3933_; 
v___x_3933_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3919_ = v_queryPart_3932_;
v___y_3920_ = v___y_3930_;
v___y_3921_ = v___y_3931_;
v___y_3922_ = v___x_3933_;
goto v___jp_3918_;
}
else
{
lean_object* v_val_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v_val_3934_ = lean_ctor_get(v_fragment_3917_, 0);
lean_inc(v_val_3934_);
lean_dec_ref_known(v_fragment_3917_, 1);
v___x_3935_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3936_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3934_);
lean_dec(v_val_3934_);
v___x_3937_ = lean_string_from_utf8_unchecked(v___x_3936_);
v___x_3938_ = lean_string_append(v___x_3935_, v___x_3937_);
lean_dec_ref(v___x_3937_);
v___y_3919_ = v_queryPart_3932_;
v___y_3920_ = v___y_3930_;
v___y_3921_ = v___y_3931_;
v___y_3922_ = v___x_3938_;
goto v___jp_3918_;
}
}
v___jp_3939_:
{
lean_object* v_segments_3941_; uint8_t v_absolute_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; size_t v_sz_3945_; size_t v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v_result_3949_; 
v_segments_3941_ = lean_ctor_get(v_path_3915_, 0);
lean_inc_ref(v_segments_3941_);
v_absolute_3942_ = lean_ctor_get_uint8(v_path_3915_, sizeof(void*)*1);
lean_dec_ref(v_path_3915_);
v___x_3943_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3944_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3945_ = lean_array_size(v_segments_3941_);
v___x_3946_ = ((size_t)0ULL);
v___x_3947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3944_, v___f_3872_, v_sz_3945_, v___x_3946_, v_segments_3941_);
v___x_3948_ = lean_array_to_list(v___x_3947_);
v_result_3949_ = l_String_intercalate(v___x_3943_, v___x_3948_);
if (v_absolute_3942_ == 0)
{
v___y_3930_ = v___y_3940_;
v___y_3931_ = v_result_3949_;
goto v___jp_3929_;
}
else
{
lean_object* v___x_3950_; 
v___x_3950_ = lean_string_append(v___x_3943_, v_result_3949_);
lean_dec_ref(v_result_3949_);
v___y_3930_ = v___y_3940_;
v___y_3931_ = v___x_3950_;
goto v___jp_3929_;
}
}
}
case 2:
{
lean_object* v_authority_4001_; lean_object* v_userInfo_4002_; lean_object* v_host_4003_; lean_object* v_port_4004_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4016_; 
lean_dec_ref(v___f_3872_);
lean_dec_ref(v___f_3871_);
v_authority_4001_ = lean_ctor_get(v_target_3874_, 0);
lean_inc_ref(v_authority_4001_);
lean_dec_ref_known(v_target_3874_, 1);
v_userInfo_4002_ = lean_ctor_get(v_authority_4001_, 0);
lean_inc(v_userInfo_4002_);
v_host_4003_ = lean_ctor_get(v_authority_4001_, 1);
lean_inc_ref(v_host_4003_);
v_port_4004_ = lean_ctor_get(v_authority_4001_, 2);
lean_inc(v_port_4004_);
lean_dec_ref(v_authority_4001_);
if (lean_obj_tag(v_userInfo_4002_) == 0)
{
lean_object* v___x_4026_; 
v___x_4026_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4016_ = v___x_4026_;
goto v___jp_4015_;
}
else
{
lean_object* v_val_4027_; lean_object* v_password_4028_; 
v_val_4027_ = lean_ctor_get(v_userInfo_4002_, 0);
lean_inc(v_val_4027_);
lean_dec_ref_known(v_userInfo_4002_, 1);
v_password_4028_ = lean_ctor_get(v_val_4027_, 1);
if (lean_obj_tag(v_password_4028_) == 0)
{
lean_object* v_username_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v_username_4029_ = lean_ctor_get(v_val_4027_, 0);
lean_inc_ref(v_username_4029_);
lean_dec(v_val_4027_);
v___x_4030_ = lean_string_from_utf8_unchecked(v_username_4029_);
v___x_4031_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4032_ = lean_string_append(v___x_4030_, v___x_4031_);
v___y_4016_ = v___x_4032_;
goto v___jp_4015_;
}
else
{
lean_object* v_username_4033_; lean_object* v_val_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
lean_inc_ref(v_password_4028_);
v_username_4033_ = lean_ctor_get(v_val_4027_, 0);
lean_inc_ref(v_username_4033_);
lean_dec(v_val_4027_);
v_val_4034_ = lean_ctor_get(v_password_4028_, 0);
lean_inc(v_val_4034_);
lean_dec_ref_known(v_password_4028_, 1);
v___x_4035_ = lean_string_from_utf8_unchecked(v_username_4033_);
v___x_4036_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4037_ = lean_string_append(v___x_4035_, v___x_4036_);
v___x_4038_ = lean_string_from_utf8_unchecked(v_val_4034_);
v___x_4039_ = lean_string_append(v___x_4037_, v___x_4038_);
lean_dec_ref(v___x_4038_);
v___x_4040_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4041_ = lean_string_append(v___x_4039_, v___x_4040_);
v___y_4016_ = v___x_4041_;
goto v___jp_4015_;
}
}
v___jp_4005_:
{
switch(lean_obj_tag(v_port_4004_))
{
case 0:
{
lean_object* v___x_4008_; 
v___x_4008_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3891_ = v___y_4007_;
v___y_3892_ = v___y_4006_;
v___y_3893_ = v___x_4008_;
goto v___jp_3890_;
}
case 1:
{
lean_object* v___x_4009_; 
v___x_4009_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3891_ = v___y_4007_;
v___y_3892_ = v___y_4006_;
v___y_3893_ = v___x_4009_;
goto v___jp_3890_;
}
default: 
{
uint16_t v_port_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v_port_4010_ = lean_ctor_get_uint16(v_port_4004_, 0);
lean_dec_ref_known(v_port_4004_, 0);
v___x_4011_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4012_ = lean_uint16_to_nat(v_port_4010_);
v___x_4013_ = l_Nat_reprFast(v___x_4012_);
v___x_4014_ = lean_string_append(v___x_4011_, v___x_4013_);
lean_dec_ref(v___x_4013_);
v___y_3891_ = v___y_4007_;
v___y_3892_ = v___y_4006_;
v___y_3893_ = v___x_4014_;
goto v___jp_3890_;
}
}
}
v___jp_4015_:
{
switch(lean_obj_tag(v_host_4003_))
{
case 0:
{
lean_object* v_name_4017_; 
v_name_4017_ = lean_ctor_get(v_host_4003_, 0);
lean_inc_ref(v_name_4017_);
lean_dec_ref_known(v_host_4003_, 1);
v___y_4006_ = v___y_4016_;
v___y_4007_ = v_name_4017_;
goto v___jp_4005_;
}
case 1:
{
lean_object* v_ipv4_4018_; lean_object* v___x_4019_; 
v_ipv4_4018_ = lean_ctor_get(v_host_4003_, 0);
lean_inc_ref(v_ipv4_4018_);
lean_dec_ref_known(v_host_4003_, 1);
v___x_4019_ = lean_uv_ntop_v4(v_ipv4_4018_);
lean_dec_ref(v_ipv4_4018_);
v___y_4006_ = v___y_4016_;
v___y_4007_ = v___x_4019_;
goto v___jp_4005_;
}
default: 
{
lean_object* v_ipv6_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v_ipv6_4020_ = lean_ctor_get(v_host_4003_, 0);
lean_inc_ref(v_ipv6_4020_);
lean_dec_ref_known(v_host_4003_, 1);
v___x_4021_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4022_ = lean_uv_ntop_v6(v_ipv6_4020_);
lean_dec_ref(v_ipv6_4020_);
v___x_4023_ = lean_string_append(v___x_4021_, v___x_4022_);
lean_dec_ref(v___x_4022_);
v___x_4024_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4025_ = lean_string_append(v___x_4023_, v___x_4024_);
v___y_4006_ = v___y_4016_;
v___y_4007_ = v___x_4025_;
goto v___jp_4005_;
}
}
}
}
default: 
{
lean_object* v___x_4042_; 
lean_dec_ref(v___f_3872_);
lean_dec_ref(v___f_3871_);
v___x_4042_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__2___closed__0));
v___y_3876_ = v___x_4042_;
goto v___jp_3875_;
}
}
v___jp_3875_:
{
lean_object* v_data_3877_; lean_object* v_size_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3889_; 
v_data_3877_ = lean_ctor_get(v_buffer_3873_, 0);
v_size_3878_ = lean_ctor_get(v_buffer_3873_, 1);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_buffer_3873_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3880_ = v_buffer_3873_;
v_isShared_3881_ = v_isSharedCheck_3889_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_size_3878_);
lean_inc(v_data_3877_);
lean_dec(v_buffer_3873_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3889_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3887_; 
v___x_3882_ = lean_string_to_utf8(v___y_3876_);
lean_dec_ref(v___y_3876_);
lean_inc_ref(v___x_3882_);
v___x_3883_ = lean_array_push(v_data_3877_, v___x_3882_);
v___x_3884_ = lean_byte_array_size(v___x_3882_);
lean_dec_ref(v___x_3882_);
v___x_3885_ = lean_nat_add(v_size_3878_, v___x_3884_);
lean_dec(v_size_3878_);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 1, v___x_3885_);
lean_ctor_set(v___x_3880_, 0, v___x_3883_);
v___x_3887_ = v___x_3880_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3883_);
lean_ctor_set(v_reuseFailAlloc_3888_, 1, v___x_3885_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
v___jp_3890_:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = lean_string_append(v___y_3892_, v___y_3891_);
lean_dec_ref(v___y_3891_);
v___x_3895_ = lean_string_append(v___x_3894_, v___y_3893_);
lean_dec_ref(v___y_3893_);
v___y_3876_ = v___x_3895_;
goto v___jp_3875_;
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
