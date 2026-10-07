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
lean_object* lean_string_data(lean_object*);
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
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(lean_object* v_x_20_){
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
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1___boxed(lean_object* v_x_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(v_x_64_);
lean_dec(v_x_64_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x3f(lean_object* v_s_67_){
_start:
{
lean_object* v___x_68_; lean_object* v_lower_69_; uint8_t v___y_71_; uint8_t v___x_74_; 
v___x_68_ = lean_unsigned_to_nat(0u);
v_lower_69_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_67_, v___x_68_);
lean_inc_ref(v_lower_69_);
v___x_74_ = l_Std_Http_Internal_instDecidableIsLowerCase(v_lower_69_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
lean_dec_ref(v_lower_69_);
v___x_75_ = lean_box(0);
return v___x_75_;
}
else
{
lean_object* v___x_76_; uint8_t v___x_77_; 
lean_inc_ref(v_lower_69_);
v___x_76_ = lean_string_data(v_lower_69_);
v___x_77_ = l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(v___x_76_);
if (v___x_77_ == 0)
{
lean_dec(v___x_76_);
v___y_71_ = v___x_77_;
goto v___jp_70_;
}
else
{
lean_object* v___x_78_; 
v___x_78_ = l_List_head_x3f___redArg(v___x_76_);
lean_dec(v___x_76_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v___x_79_; 
lean_dec_ref(v_lower_69_);
v___x_79_ = lean_box(0);
return v___x_79_;
}
else
{
lean_object* v_val_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_101_; 
v_val_80_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_101_ == 0)
{
v___x_82_ = v___x_78_;
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_val_80_);
lean_dec(v___x_78_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
uint32_t v___x_92_; uint32_t v___x_93_; uint8_t v___x_94_; 
v___x_92_ = 65;
v___x_93_ = lean_unbox_uint32(v_val_80_);
v___x_94_ = lean_uint32_dec_le(v___x_92_, v___x_93_);
if (v___x_94_ == 0)
{
lean_del_object(v___x_82_);
goto v___jp_84_;
}
else
{
uint32_t v___x_95_; uint32_t v___x_96_; uint8_t v___x_97_; 
v___x_95_ = 90;
v___x_96_ = lean_unbox_uint32(v_val_80_);
v___x_97_ = lean_uint32_dec_le(v___x_96_, v___x_95_);
if (v___x_97_ == 0)
{
lean_del_object(v___x_82_);
goto v___jp_84_;
}
else
{
lean_object* v___x_99_; 
lean_dec(v_val_80_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v_lower_69_);
v___x_99_ = v___x_82_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_lower_69_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
v___jp_84_:
{
uint32_t v___x_85_; uint32_t v___x_86_; uint8_t v___x_87_; 
v___x_85_ = 97;
v___x_86_ = lean_unbox_uint32(v_val_80_);
v___x_87_ = lean_uint32_dec_le(v___x_85_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; 
lean_dec(v_val_80_);
lean_dec_ref(v_lower_69_);
v___x_88_ = lean_box(0);
return v___x_88_;
}
else
{
uint32_t v___x_89_; uint32_t v___x_90_; uint8_t v___x_91_; 
v___x_89_ = 122;
v___x_90_ = lean_unbox_uint32(v_val_80_);
lean_dec(v_val_80_);
v___x_91_ = lean_uint32_dec_le(v___x_90_, v___x_89_);
v___y_71_ = v___x_91_;
goto v___jp_70_;
}
}
}
}
}
}
v___jp_70_:
{
if (v___y_71_ == 0)
{
lean_object* v___x_72_; 
lean_dec_ref(v_lower_69_);
v___x_72_ = lean_box(0);
return v___x_72_;
}
else
{
lean_object* v___x_73_; 
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v_lower_69_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(lean_object* v_msg_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = ((lean_object*)(l_Std_Http_URI_instInhabitedScheme___closed__0));
v___x_104_ = lean_panic_fn_borrowed(v___x_103_, v_msg_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x21(lean_object* v_s_108_){
_start:
{
lean_object* v___x_109_; 
lean_inc_ref(v_s_108_);
v___x_109_ = l_Std_Http_URI_Scheme_ofString_x3f(v_s_108_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_110_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_111_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__1));
v___x_112_ = lean_unsigned_to_nat(84u);
v___x_113_ = lean_unsigned_to_nat(12u);
v___x_114_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_115_ = l_String_quote(v_s_108_);
v___x_116_ = lean_string_append(v___x_114_, v___x_115_);
lean_dec_ref(v___x_115_);
v___x_117_ = l_mkPanicMessageWithDecl(v___x_110_, v___x_111_, v___x_112_, v___x_113_, v___x_116_);
lean_dec_ref(v___x_116_);
v___x_118_ = l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(v___x_117_);
return v___x_118_;
}
else
{
lean_object* v_val_119_; 
lean_dec_ref(v_s_108_);
v_val_119_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_val_119_);
lean_dec_ref_known(v___x_109_, 1);
return v_val_119_;
}
}
}
LEAN_EXPORT uint16_t l_Std_Http_URI_Scheme_defaultPort(lean_object* v_scheme_121_){
_start:
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___x_123_ = lean_string_dec_eq(v_scheme_121_, v___x_122_);
if (v___x_123_ == 0)
{
uint16_t v___x_124_; 
v___x_124_ = 80;
return v___x_124_;
}
else
{
uint16_t v___x_125_; 
v___x_125_ = 443;
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_defaultPort___boxed(lean_object* v_scheme_126_){
_start:
{
uint16_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_126_);
lean_dec_ref(v_scheme_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofPort(uint16_t v_port_129_){
_start:
{
uint16_t v___x_130_; uint8_t v___x_131_; 
v___x_130_ = 443;
v___x_131_ = lean_uint16_dec_eq(v_port_129_, v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; 
v___x_132_ = ((lean_object*)(l_Std_Http_URI_instInhabitedScheme___closed__0));
return v___x_132_;
}
else
{
lean_object* v___x_133_; 
v___x_133_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofPort___boxed(lean_object* v_port_134_){
_start:
{
uint16_t v_port_boxed_135_; lean_object* v_res_136_; 
v_port_boxed_135_ = lean_unbox(v_port_134_);
v_res_136_ = l_Std_Http_URI_Scheme_ofPort(v_port_boxed_135_);
return v_res_136_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__0(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_box(0);
v___x_138_ = l_ByteArray_empty;
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_137_);
return v___x_139_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default(void){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_Std_Http_URI_instInhabitedUserInfo_default___closed__0, &l_Std_Http_URI_instInhabitedUserInfo_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__0);
return v___x_140_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo(void){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Std_Http_URI_instInhabitedUserInfo_default;
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_148_) == 0)
{
lean_object* v___x_150_; 
v___x_150_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_150_;
}
else
{
lean_object* v_val_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_163_; 
v_val_151_ = lean_ctor_get(v_x_148_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v_x_148_);
if (v_isSharedCheck_163_ == 0)
{
v___x_153_ = v_x_148_;
v_isShared_154_ = v_isSharedCheck_163_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_val_151_);
lean_dec(v_x_148_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_163_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_155_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_156_ = lean_string_from_utf8_unchecked(v_val_151_);
v___x_157_ = l_String_quote(v___x_156_);
if (v_isShared_154_ == 0)
{
lean_ctor_set_tag(v___x_153_, 3);
lean_ctor_set(v___x_153_, 0, v___x_157_);
v___x_159_ = v___x_153_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_162_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_155_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = l_Repr_addAppParen(v___x_160_, v_x_149_);
return v___x_161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___boxed(lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_x_164_, v_x_165_);
lean_dec(v_x_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_URI_instReprUserInfo_repr_spec__1(lean_object* v_a_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_nat_to_int(v_a_167_);
return v___x_168_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(12u);
v___x_183_ = lean_nat_to_int(v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0));
v___x_192_ = lean_string_length(v___x_191_);
return v___x_192_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13);
v___x_194_ = lean_nat_to_int(v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg(lean_object* v_x_199_){
_start:
{
lean_object* v_username_200_; lean_object* v_password_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_236_; 
v_username_200_ = lean_ctor_get(v_x_199_, 0);
v_password_201_ = lean_ctor_get(v_x_199_, 1);
v_isSharedCheck_236_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_236_ == 0)
{
v___x_203_ = v_x_199_;
v_isShared_204_ = v_isSharedCheck_236_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_password_201_);
lean_inc(v_username_200_);
lean_dec(v_x_199_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_236_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_205_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_206_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__6));
v___x_207_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_208_ = lean_string_from_utf8_unchecked(v_username_200_);
v___x_209_ = l_String_quote(v___x_208_);
v___x_210_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
if (v_isShared_204_ == 0)
{
lean_ctor_set_tag(v___x_203_, 4);
lean_ctor_set(v___x_203_, 1, v___x_210_);
lean_ctor_set(v___x_203_, 0, v___x_207_);
v___x_212_ = v___x_203_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_210_);
v___x_212_ = v_reuseFailAlloc_235_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_213_ = 0;
v___x_214_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*1, v___x_213_);
v___x_215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_206_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v___x_216_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = lean_box(1);
v___x_219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__11));
v___x_221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_205_);
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_password_201_, v___x_223_);
v___x_225_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_207_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*1, v___x_213_);
v___x_227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_222_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_229_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_227_);
v___x_231_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_228_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*1, v___x_213_);
return v___x_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr(lean_object* v_x_237_, lean_object* v_prec_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_x_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___boxed(lean_object* v_x_240_, lean_object* v_prec_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_Http_URI_instReprUserInfo_repr(v_x_240_, v_prec_241_);
lean_dec(v_prec_241_);
return v_res_242_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
if (lean_obj_tag(v_x_246_) == 0)
{
uint8_t v___x_247_; 
v___x_247_ = 1;
return v___x_247_;
}
else
{
uint8_t v___x_248_; 
v___x_248_ = 0;
return v___x_248_;
}
}
else
{
if (lean_obj_tag(v_x_246_) == 0)
{
uint8_t v___x_249_; 
v___x_249_ = 0;
return v___x_249_;
}
else
{
lean_object* v_val_250_; lean_object* v_val_251_; uint8_t v___x_252_; 
v_val_250_ = lean_ctor_get(v_x_245_, 0);
v_val_251_ = lean_ctor_get(v_x_246_, 0);
v___x_252_ = lean_sarray_dec_eq(v_val_250_, v_val_251_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0___boxed(lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_x_253_, v_x_254_);
lean_dec(v_x_254_);
lean_dec(v_x_253_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqUserInfo_beq(lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
lean_object* v_username_259_; lean_object* v_password_260_; lean_object* v_username_261_; lean_object* v_password_262_; uint8_t v___x_263_; 
v_username_259_ = lean_ctor_get(v_x_257_, 0);
v_password_260_ = lean_ctor_get(v_x_257_, 1);
v_username_261_ = lean_ctor_get(v_x_258_, 0);
v_password_262_ = lean_ctor_get(v_x_258_, 1);
v___x_263_ = lean_sarray_dec_eq(v_username_259_, v_username_261_);
if (v___x_263_ == 0)
{
return v___x_263_;
}
else
{
uint8_t v___x_264_; 
v___x_264_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_password_260_, v_password_262_);
return v___x_264_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqUserInfo_beq___boxed(lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
uint8_t v_res_267_; lean_object* v_r_268_; 
v_res_267_ = l_Std_Http_URI_instBEqUserInfo_beq(v_x_265_, v_x_266_);
lean_dec_ref(v_x_266_);
lean_dec_ref(v_x_265_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings(lean_object* v_username_271_, lean_object* v_password_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_271_);
if (lean_obj_tag(v_password_272_) == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_box(0);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_273_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
return v___x_275_;
}
else
{
lean_object* v_val_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_285_; 
v_val_276_ = lean_ctor_get(v_password_272_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v_password_272_);
if (v_isSharedCheck_285_ == 0)
{
v___x_278_ = v_password_272_;
v_isShared_279_ = v_isSharedCheck_285_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_val_276_);
lean_dec(v_password_272_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_285_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_276_);
lean_dec(v_val_276_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_280_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_284_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; 
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_273_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
return v___x_283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings___boxed(lean_object* v_username_286_, lean_object* v_password_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Std_Http_URI_UserInfo_ofStrings(v_username_286_, v_password_287_);
lean_dec_ref(v_username_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f(lean_object* v_ui_289_){
_start:
{
lean_object* v_username_290_; lean_object* v___x_291_; 
v_username_290_ = lean_ctor_get(v_ui_289_, 0);
v___x_291_ = l_Std_Http_URI_EncodedUserInfo_decode(v_username_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f___boxed(lean_object* v_ui_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Std_Http_URI_UserInfo_username_x3f(v_ui_292_);
lean_dec_ref(v_ui_292_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f(lean_object* v_ui_294_){
_start:
{
lean_object* v_password_295_; 
v_password_295_ = lean_ctor_get(v_ui_294_, 1);
if (lean_obj_tag(v_password_295_) == 0)
{
lean_object* v___x_296_; 
v___x_296_ = lean_box(0);
return v___x_296_;
}
else
{
lean_object* v_val_297_; lean_object* v___x_298_; 
v_val_297_ = lean_ctor_get(v_password_295_, 0);
v___x_298_ = l_Std_Http_URI_EncodedUserInfo_decode(v_val_297_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f___boxed(lean_object* v_ui_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_Http_URI_UserInfo_password_x3f(v_ui_299_);
lean_dec_ref(v_ui_299_);
return v_res_300_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(lean_object* v_x_301_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
uint8_t v___x_302_; 
v___x_302_ = 1;
return v___x_302_;
}
else
{
lean_object* v_head_303_; lean_object* v_tail_304_; uint32_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_head_303_ = lean_ctor_get(v_x_301_, 0);
v_tail_304_ = lean_ctor_get(v_x_301_, 1);
v___x_326_ = lean_unbox_uint32(v_head_303_);
v___x_327_ = lean_uint32_to_nat(v___x_326_);
v___x_328_ = lean_unsigned_to_nat(128u);
v___x_329_ = lean_nat_dec_lt(v___x_327_, v___x_328_);
lean_dec(v___x_327_);
if (v___x_329_ == 0)
{
goto v___jp_305_;
}
else
{
uint32_t v___x_330_; uint32_t v___x_331_; uint8_t v___x_332_; 
v___x_330_ = 48;
v___x_331_ = lean_unbox_uint32(v_head_303_);
v___x_332_ = lean_uint32_dec_le(v___x_330_, v___x_331_);
if (v___x_332_ == 0)
{
goto v___jp_318_;
}
else
{
uint32_t v___x_333_; uint32_t v___x_334_; uint8_t v___x_335_; 
v___x_333_ = 57;
v___x_334_ = lean_unbox_uint32(v_head_303_);
v___x_335_ = lean_uint32_dec_le(v___x_334_, v___x_333_);
if (v___x_335_ == 0)
{
goto v___jp_318_;
}
else
{
v_x_301_ = v_tail_304_;
goto _start;
}
}
}
v___jp_305_:
{
uint32_t v___x_306_; uint32_t v___x_307_; uint8_t v___x_308_; 
v___x_306_ = 45;
v___x_307_ = lean_unbox_uint32(v_head_303_);
v___x_308_ = lean_uint32_dec_eq(v___x_307_, v___x_306_);
if (v___x_308_ == 0)
{
return v___x_308_;
}
else
{
v_x_301_ = v_tail_304_;
goto _start;
}
}
v___jp_310_:
{
uint32_t v___x_311_; uint32_t v___x_312_; uint8_t v___x_313_; 
v___x_311_ = 97;
v___x_312_ = lean_unbox_uint32(v_head_303_);
v___x_313_ = lean_uint32_dec_le(v___x_311_, v___x_312_);
if (v___x_313_ == 0)
{
goto v___jp_305_;
}
else
{
uint32_t v___x_314_; uint32_t v___x_315_; uint8_t v___x_316_; 
v___x_314_ = 122;
v___x_315_ = lean_unbox_uint32(v_head_303_);
v___x_316_ = lean_uint32_dec_le(v___x_315_, v___x_314_);
if (v___x_316_ == 0)
{
goto v___jp_305_;
}
else
{
v_x_301_ = v_tail_304_;
goto _start;
}
}
}
v___jp_318_:
{
uint32_t v___x_319_; uint32_t v___x_320_; uint8_t v___x_321_; 
v___x_319_ = 65;
v___x_320_ = lean_unbox_uint32(v_head_303_);
v___x_321_ = lean_uint32_dec_le(v___x_319_, v___x_320_);
if (v___x_321_ == 0)
{
goto v___jp_310_;
}
else
{
uint32_t v___x_322_; uint32_t v___x_323_; uint8_t v___x_324_; 
v___x_322_ = 90;
v___x_323_ = lean_unbox_uint32(v_head_303_);
v___x_324_ = lean_uint32_dec_le(v___x_323_, v___x_322_);
if (v___x_324_ == 0)
{
goto v___jp_310_;
}
else
{
v_x_301_ = v_tail_304_;
goto _start;
}
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
uint32_t v___y_342_; uint32_t v___y_348_; lean_object* v_chars_353_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v_chars_353_ = lean_string_data(v_s_340_);
v___x_370_ = l_List_lengthTR___redArg(v_chars_353_);
v___x_371_ = lean_unsigned_to_nat(63u);
v___x_372_ = lean_nat_dec_le(v___x_370_, v___x_371_);
lean_dec(v___x_370_);
if (v___x_372_ == 0)
{
lean_dec(v_chars_353_);
return v___x_372_;
}
else
{
uint8_t v___x_373_; 
v___x_373_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v_chars_353_);
if (v___x_373_ == 0)
{
lean_dec(v_chars_353_);
return v___x_373_;
}
else
{
lean_object* v___x_374_; 
v___x_374_ = l_List_head_x3f___redArg(v_chars_353_);
if (lean_obj_tag(v___x_374_) == 0)
{
uint8_t v___x_375_; 
lean_dec(v_chars_353_);
v___x_375_ = 0;
return v___x_375_;
}
else
{
lean_object* v_val_376_; uint32_t v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v_val_376_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_val_376_);
lean_dec_ref_known(v___x_374_, 1);
v___x_391_ = lean_unbox_uint32(v_val_376_);
v___x_392_ = lean_uint32_to_nat(v___x_391_);
v___x_393_ = lean_unsigned_to_nat(128u);
v___x_394_ = lean_nat_dec_lt(v___x_392_, v___x_393_);
lean_dec(v___x_392_);
if (v___x_394_ == 0)
{
lean_dec(v_val_376_);
lean_dec(v_chars_353_);
return v___x_394_;
}
else
{
uint32_t v___x_395_; uint32_t v___x_396_; uint8_t v___x_397_; 
v___x_395_ = 48;
v___x_396_ = lean_unbox_uint32(v_val_376_);
v___x_397_ = lean_uint32_dec_le(v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
goto v___jp_384_;
}
else
{
uint32_t v___x_398_; uint32_t v___x_399_; uint8_t v___x_400_; 
v___x_398_ = 57;
v___x_399_ = lean_unbox_uint32(v_val_376_);
v___x_400_ = lean_uint32_dec_le(v___x_399_, v___x_398_);
if (v___x_400_ == 0)
{
goto v___jp_384_;
}
else
{
lean_dec(v_val_376_);
goto v___jp_354_;
}
}
}
v___jp_377_:
{
uint32_t v___x_378_; uint32_t v___x_379_; uint8_t v___x_380_; 
v___x_378_ = 97;
v___x_379_ = lean_unbox_uint32(v_val_376_);
v___x_380_ = lean_uint32_dec_le(v___x_378_, v___x_379_);
if (v___x_380_ == 0)
{
lean_dec(v_val_376_);
lean_dec(v_chars_353_);
return v___x_380_;
}
else
{
uint32_t v___x_381_; uint32_t v___x_382_; uint8_t v___x_383_; 
v___x_381_ = 122;
v___x_382_ = lean_unbox_uint32(v_val_376_);
lean_dec(v_val_376_);
v___x_383_ = lean_uint32_dec_le(v___x_382_, v___x_381_);
if (v___x_383_ == 0)
{
lean_dec(v_chars_353_);
return v___x_383_;
}
else
{
goto v___jp_354_;
}
}
}
v___jp_384_:
{
uint32_t v___x_385_; uint32_t v___x_386_; uint8_t v___x_387_; 
v___x_385_ = 65;
v___x_386_ = lean_unbox_uint32(v_val_376_);
v___x_387_ = lean_uint32_dec_le(v___x_385_, v___x_386_);
if (v___x_387_ == 0)
{
goto v___jp_377_;
}
else
{
uint32_t v___x_388_; uint32_t v___x_389_; uint8_t v___x_390_; 
v___x_388_ = 90;
v___x_389_ = lean_unbox_uint32(v_val_376_);
v___x_390_ = lean_uint32_dec_le(v___x_389_, v___x_388_);
if (v___x_390_ == 0)
{
goto v___jp_377_;
}
else
{
lean_dec(v_val_376_);
goto v___jp_354_;
}
}
}
}
}
}
v___jp_341_:
{
uint32_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = 97;
v___x_344_ = lean_uint32_dec_le(v___x_343_, v___y_342_);
if (v___x_344_ == 0)
{
return v___x_344_;
}
else
{
uint32_t v___x_345_; uint8_t v___x_346_; 
v___x_345_ = 122;
v___x_346_ = lean_uint32_dec_le(v___y_342_, v___x_345_);
return v___x_346_;
}
}
v___jp_347_:
{
uint32_t v___x_349_; uint8_t v___x_350_; 
v___x_349_ = 65;
v___x_350_ = lean_uint32_dec_le(v___x_349_, v___y_348_);
if (v___x_350_ == 0)
{
v___y_342_ = v___y_348_;
goto v___jp_341_;
}
else
{
uint32_t v___x_351_; uint8_t v___x_352_; 
v___x_351_ = 90;
v___x_352_ = lean_uint32_dec_le(v___y_348_, v___x_351_);
if (v___x_352_ == 0)
{
v___y_342_ = v___y_348_;
goto v___jp_341_;
}
else
{
return v___x_352_;
}
}
}
v___jp_354_:
{
lean_object* v___x_355_; 
v___x_355_ = l_List_getLast_x3f___redArg(v_chars_353_);
lean_dec(v_chars_353_);
if (lean_obj_tag(v___x_355_) == 0)
{
uint8_t v___x_356_; 
v___x_356_ = 0;
return v___x_356_;
}
else
{
lean_object* v_val_357_; uint32_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v_val_357_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_val_357_);
lean_dec_ref_known(v___x_355_, 1);
v___x_358_ = lean_unbox_uint32(v_val_357_);
v___x_359_ = lean_uint32_to_nat(v___x_358_);
v___x_360_ = lean_unsigned_to_nat(128u);
v___x_361_ = lean_nat_dec_lt(v___x_359_, v___x_360_);
lean_dec(v___x_359_);
if (v___x_361_ == 0)
{
lean_dec(v_val_357_);
return v___x_361_;
}
else
{
uint32_t v___x_362_; uint32_t v___x_363_; uint8_t v___x_364_; 
v___x_362_ = 48;
v___x_363_ = lean_unbox_uint32(v_val_357_);
v___x_364_ = lean_uint32_dec_le(v___x_362_, v___x_363_);
if (v___x_364_ == 0)
{
uint32_t v___x_365_; 
v___x_365_ = lean_unbox_uint32(v_val_357_);
lean_dec(v_val_357_);
v___y_348_ = v___x_365_;
goto v___jp_347_;
}
else
{
uint32_t v___x_366_; uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_366_ = 57;
v___x_367_ = lean_unbox_uint32(v_val_357_);
v___x_368_ = lean_uint32_dec_le(v___x_367_, v___x_366_);
if (v___x_368_ == 0)
{
uint32_t v___x_369_; 
v___x_369_ = lean_unbox_uint32(v_val_357_);
lean_dec(v_val_357_);
v___y_348_ = v___x_369_;
goto v___jp_347_;
}
else
{
lean_dec(v_val_357_);
return v___x_368_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidDomainLabel___boxed(lean_object* v_s_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Std_Http_URI_isValidDomainLabel(v_s_401_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg(){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___closed__0));
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___boxed(lean_object* v___dummy_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg();
return v_res_409_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg();
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(lean_object* v_s_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___boxed(lean_object* v_s_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(v_s_413_);
lean_dec_ref(v_s_413_);
return v_res_414_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(uint8_t v___x_415_, lean_object* v_lower_416_, lean_object* v___x_417_, lean_object* v___x_418_, lean_object* v_a_419_, uint8_t v_b_420_){
_start:
{
uint8_t v___y_422_; lean_object* v_it_423_; lean_object* v_startInclusive_424_; lean_object* v_endExclusive_425_; uint8_t v___y_430_; 
if (v___x_415_ == 0)
{
uint8_t v___x_456_; 
v___x_456_ = 1;
v___y_430_ = v___x_456_;
goto v___jp_429_;
}
else
{
uint8_t v___x_457_; 
v___x_457_ = 0;
v___y_430_ = v___x_457_;
goto v___jp_429_;
}
v___jp_421_:
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = lean_string_utf8_extract_fast(v_lower_416_, v_startInclusive_424_, v_endExclusive_425_);
lean_dec(v_endExclusive_425_);
lean_dec(v_startInclusive_424_);
v___x_427_ = l_Std_Http_URI_isValidDomainLabel(v___x_426_);
if (v___x_427_ == 0)
{
lean_dec(v_it_423_);
lean_dec(v___x_418_);
return v___x_427_;
}
else
{
v_a_419_ = v_it_423_;
v_b_420_ = v___y_422_;
goto _start;
}
}
v___jp_429_:
{
if (lean_obj_tag(v_a_419_) == 0)
{
lean_object* v_currPos_431_; lean_object* v_searcher_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_455_; 
v_currPos_431_ = lean_ctor_get(v_a_419_, 0);
v_searcher_432_ = lean_ctor_get(v_a_419_, 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v_a_419_);
if (v_isSharedCheck_455_ == 0)
{
v___x_434_ = v_a_419_;
v_isShared_435_ = v_isSharedCheck_455_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_searcher_432_);
lean_inc(v_currPos_431_);
lean_dec(v_a_419_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_455_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
uint8_t v_decide_436_; 
v_decide_436_ = lean_nat_dec_eq(v_searcher_432_, v___x_418_);
if (v_decide_436_ == 0)
{
uint32_t v___x_437_; uint32_t v___x_438_; uint8_t v___x_439_; 
v___x_437_ = 46;
v___x_438_ = lean_string_utf8_get_fast(v_lower_416_, v_searcher_432_);
v___x_439_ = lean_uint32_dec_eq(v___x_438_, v___x_437_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_440_ = lean_string_utf8_next_fast(v_lower_416_, v_searcher_432_);
lean_dec(v_searcher_432_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_440_);
v___x_442_ = v___x_434_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_currPos_431_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_440_);
v___x_442_ = v_reuseFailAlloc_444_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
v_a_419_ = v___x_442_;
goto _start;
}
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v_slice_448_; lean_object* v_nextIt_450_; 
v___x_445_ = lean_string_utf8_next_fast(v_lower_416_, v_searcher_432_);
v___x_446_ = lean_nat_sub(v___x_445_, v_searcher_432_);
v___x_447_ = lean_nat_add(v_searcher_432_, v___x_446_);
lean_dec(v___x_446_);
v_slice_448_ = l_String_Slice_subslice_x21(v___x_417_, v_currPos_431_, v_searcher_432_);
lean_inc(v___x_447_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_447_);
lean_ctor_set(v___x_434_, 0, v___x_447_);
v_nextIt_450_ = v___x_434_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v___x_447_);
v_nextIt_450_ = v_reuseFailAlloc_453_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v_startInclusive_451_; lean_object* v_endExclusive_452_; 
v_startInclusive_451_ = lean_ctor_get(v_slice_448_, 0);
lean_inc(v_startInclusive_451_);
v_endExclusive_452_ = lean_ctor_get(v_slice_448_, 1);
lean_inc(v_endExclusive_452_);
lean_dec_ref(v_slice_448_);
v___y_422_ = v___y_430_;
v_it_423_ = v_nextIt_450_;
v_startInclusive_424_ = v_startInclusive_451_;
v_endExclusive_425_ = v_endExclusive_452_;
goto v___jp_421_;
}
}
}
else
{
lean_object* v___x_454_; 
lean_del_object(v___x_434_);
lean_dec(v_searcher_432_);
v___x_454_ = lean_box(1);
lean_inc(v___x_418_);
v___y_422_ = v___y_430_;
v_it_423_ = v___x_454_;
v_startInclusive_424_ = v_currPos_431_;
v_endExclusive_425_ = v___x_418_;
goto v___jp_421_;
}
}
}
else
{
lean_dec(v___x_418_);
return v_b_420_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg___boxed(lean_object* v___x_458_, lean_object* v_lower_459_, lean_object* v___x_460_, lean_object* v___x_461_, lean_object* v_a_462_, lean_object* v_b_463_){
_start:
{
uint8_t v___x_3750__boxed_464_; uint8_t v_b_boxed_465_; uint8_t v_res_466_; lean_object* v_r_467_; 
v___x_3750__boxed_464_ = lean_unbox(v___x_458_);
v_b_boxed_465_ = lean_unbox(v_b_463_);
v_res_466_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_3750__boxed_464_, v_lower_459_, v___x_460_, v___x_461_, v_a_462_, v_b_boxed_465_);
lean_dec_ref(v___x_460_);
lean_dec_ref(v_lower_459_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(lean_object* v___x_468_, lean_object* v_lower_469_, lean_object* v___x_470_, lean_object* v_a_471_, uint8_t v_b_472_){
_start:
{
if (lean_obj_tag(v_a_471_) == 0)
{
lean_object* v_currPos_473_; lean_object* v_searcher_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_489_; 
v_currPos_473_ = lean_ctor_get(v_a_471_, 0);
v_searcher_474_ = lean_ctor_get(v_a_471_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v_a_471_);
if (v_isSharedCheck_489_ == 0)
{
v___x_476_ = v_a_471_;
v_isShared_477_ = v_isSharedCheck_489_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_searcher_474_);
lean_inc(v_currPos_473_);
lean_dec(v_a_471_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_489_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; uint8_t v___x_479_; uint8_t v_decide_480_; 
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = lean_nat_dec_eq(v___x_468_, v___x_478_);
v_decide_480_ = lean_nat_dec_eq(v_searcher_474_, v___x_470_);
if (v_decide_480_ == 0)
{
uint32_t v___x_481_; uint32_t v___x_482_; uint8_t v___x_483_; 
v___x_481_ = 46;
v___x_482_ = lean_string_utf8_get_fast(v_lower_469_, v_searcher_474_);
v___x_483_ = lean_uint32_dec_eq(v___x_482_, v___x_481_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = lean_string_utf8_next_fast(v_lower_469_, v_searcher_474_);
lean_dec(v_searcher_474_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v___x_484_);
v___x_486_ = v___x_476_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_currPos_473_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_488_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
v_a_471_ = v___x_486_;
goto _start;
}
}
else
{
lean_del_object(v___x_476_);
lean_dec(v_searcher_474_);
lean_dec(v_currPos_473_);
return v___x_479_;
}
}
else
{
lean_del_object(v___x_476_);
lean_dec(v_searcher_474_);
lean_dec(v_currPos_473_);
return v___x_479_;
}
}
}
else
{
return v_b_472_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg___boxed(lean_object* v___x_490_, lean_object* v_lower_491_, lean_object* v___x_492_, lean_object* v_a_493_, lean_object* v_b_494_){
_start:
{
uint8_t v_b_boxed_495_; uint8_t v_res_496_; lean_object* v_r_497_; 
v_b_boxed_495_ = lean_unbox(v_b_494_);
v_res_496_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_490_, v_lower_491_, v___x_492_, v_a_493_, v_b_boxed_495_);
lean_dec(v___x_492_);
lean_dec_ref(v_lower_491_);
lean_dec(v___x_490_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_DomainName_ofString_x3f(lean_object* v_s_498_){
_start:
{
lean_object* v___x_499_; lean_object* v_lower_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v_lower_500_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_498_, v___x_499_);
v___x_501_ = lean_string_utf8_byte_size(v_lower_500_);
v___x_502_ = lean_nat_dec_eq(v___x_501_, v___x_499_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; uint8_t v___x_506_; uint8_t v___y_508_; 
lean_inc_ref(v_lower_500_);
v___x_503_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_503_, 0, v_lower_500_);
lean_ctor_set(v___x_503_, 1, v___x_499_);
lean_ctor_set(v___x_503_, 2, v___x_501_);
v___x_504_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0);
v___x_505_ = 1;
v___x_506_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_501_, v_lower_500_, v___x_501_, v___x_504_, v___x_505_);
if (v___x_506_ == 0)
{
v___y_508_ = v___x_505_;
goto v___jp_507_;
}
else
{
if (v___x_502_ == 0)
{
lean_object* v___x_516_; 
lean_dec_ref_known(v___x_503_, 3);
lean_dec_ref(v_lower_500_);
v___x_516_ = lean_box(0);
return v___x_516_;
}
else
{
v___y_508_ = v___x_502_;
goto v___jp_507_;
}
}
v___jp_507_:
{
uint8_t v___x_509_; 
v___x_509_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_506_, v_lower_500_, v___x_503_, v___x_501_, v___x_504_, v___y_508_);
lean_dec_ref_known(v___x_503_, 3);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
lean_dec_ref(v_lower_500_);
v___x_510_ = lean_box(0);
return v___x_510_;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_511_ = lean_string_length(v_lower_500_);
v___x_512_ = lean_unsigned_to_nat(255u);
v___x_513_ = lean_nat_dec_le(v___x_511_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
lean_dec_ref(v_lower_500_);
v___x_514_ = lean_box(0);
return v___x_514_;
}
else
{
lean_object* v___x_515_; 
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v_lower_500_);
return v___x_515_;
}
}
}
}
else
{
lean_object* v___x_517_; 
lean_dec_ref(v_lower_500_);
v___x_517_ = lean_box(0);
return v___x_517_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(lean_object* v___x_518_, lean_object* v_lower_519_, lean_object* v___x_520_, lean_object* v___x_521_, lean_object* v_inst_522_, lean_object* v_R_523_, lean_object* v_a_524_, uint8_t v_b_525_, lean_object* v_c_526_){
_start:
{
uint8_t v___x_527_; 
v___x_527_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_518_, v_lower_519_, v___x_521_, v_a_524_, v_b_525_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___boxed(lean_object* v___x_528_, lean_object* v_lower_529_, lean_object* v___x_530_, lean_object* v___x_531_, lean_object* v_inst_532_, lean_object* v_R_533_, lean_object* v_a_534_, lean_object* v_b_535_, lean_object* v_c_536_){
_start:
{
uint8_t v_b_boxed_537_; uint8_t v_res_538_; lean_object* v_r_539_; 
v_b_boxed_537_ = lean_unbox(v_b_535_);
v_res_538_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(v___x_528_, v_lower_529_, v___x_530_, v___x_531_, v_inst_532_, v_R_533_, v_a_534_, v_b_boxed_537_, v_c_536_);
lean_dec(v___x_531_);
lean_dec_ref(v___x_530_);
lean_dec_ref(v_lower_529_);
lean_dec(v___x_528_);
v_r_539_ = lean_box(v_res_538_);
return v_r_539_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(uint8_t v___x_540_, lean_object* v_lower_541_, lean_object* v___x_542_, lean_object* v___x_543_, lean_object* v_inst_544_, lean_object* v_R_545_, lean_object* v_a_546_, uint8_t v_b_547_, lean_object* v_c_548_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_540_, v_lower_541_, v___x_542_, v___x_543_, v_a_546_, v_b_547_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___boxed(lean_object* v___x_550_, lean_object* v_lower_551_, lean_object* v___x_552_, lean_object* v___x_553_, lean_object* v_inst_554_, lean_object* v_R_555_, lean_object* v_a_556_, lean_object* v_b_557_, lean_object* v_c_558_){
_start:
{
uint8_t v___x_3912__boxed_559_; uint8_t v_b_boxed_560_; uint8_t v_res_561_; lean_object* v_r_562_; 
v___x_3912__boxed_559_ = lean_unbox(v___x_550_);
v_b_boxed_560_ = lean_unbox(v_b_557_);
v_res_561_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(v___x_3912__boxed_559_, v_lower_551_, v___x_552_, v___x_553_, v_inst_554_, v_R_555_, v_a_556_, v_b_boxed_560_, v_c_558_);
lean_dec_ref(v___x_552_);
lean_dec_ref(v_lower_551_);
v_r_562_ = lean_box(v_res_561_);
return v_r_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx___impl(lean_object* v_x_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = lean_obj_tag_nat(v_x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx___impl___boxed(lean_object* v_x_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Std_Http_URI_Host_ctorIdx___impl(v_x_565_);
lean_dec_ref(v_x_565_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___redArg(lean_object* v_t_567_, lean_object* v_k_568_){
_start:
{
lean_object* v_name_569_; lean_object* v___x_570_; 
v_name_569_ = lean_ctor_get(v_t_567_, 0);
lean_inc_ref(v_name_569_);
lean_dec_ref(v_t_567_);
v___x_570_ = lean_apply_1(v_k_568_, v_name_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim(lean_object* v_motive_571_, lean_object* v_ctorIdx_572_, lean_object* v_t_573_, lean_object* v_h_574_, lean_object* v_k_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_573_, v_k_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___boxed(lean_object* v_motive_577_, lean_object* v_ctorIdx_578_, lean_object* v_t_579_, lean_object* v_h_580_, lean_object* v_k_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Std_Http_URI_Host_ctorElim(v_motive_577_, v_ctorIdx_578_, v_t_579_, v_h_580_, v_k_581_);
lean_dec(v_ctorIdx_578_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim___redArg(lean_object* v_t_583_, lean_object* v_name_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_583_, v_name_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim(lean_object* v_motive_586_, lean_object* v_t_587_, lean_object* v_h_588_, lean_object* v_name_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_587_, v_name_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim___redArg(lean_object* v_t_591_, lean_object* v_ipv4_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_591_, v_ipv4_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim(lean_object* v_motive_594_, lean_object* v_t_595_, lean_object* v_h_596_, lean_object* v_ipv4_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_595_, v_ipv4_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim___redArg(lean_object* v_t_599_, lean_object* v_ipv6_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_599_, v_ipv6_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim(lean_object* v_motive_602_, lean_object* v_t_603_, lean_object* v_h_604_, lean_object* v_ipv6_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_603_, v_ipv6_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default___closed__0(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
return v___x_608_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default(void){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = lean_obj_once(&l_Std_Http_URI_instInhabitedHost_default___closed__0, &l_Std_Http_URI_instInhabitedHost_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedHost_default___closed__0);
return v___x_609_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost(void){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_Http_URI_instInhabitedHost_default;
return v___x_610_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqHost_beq(lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
switch(lean_obj_tag(v_x_611_))
{
case 0:
{
if (lean_obj_tag(v_x_612_) == 0)
{
lean_object* v_name_613_; lean_object* v_name_614_; uint8_t v___x_615_; 
v_name_613_ = lean_ctor_get(v_x_611_, 0);
v_name_614_ = lean_ctor_get(v_x_612_, 0);
v___x_615_ = lean_string_dec_eq(v_name_613_, v_name_614_);
return v___x_615_;
}
else
{
uint8_t v___x_616_; 
v___x_616_ = 0;
return v___x_616_;
}
}
case 1:
{
if (lean_obj_tag(v_x_612_) == 1)
{
lean_object* v_ipv4_617_; lean_object* v_ipv4_618_; uint8_t v___x_619_; 
v_ipv4_617_ = lean_ctor_get(v_x_611_, 0);
v_ipv4_618_ = lean_ctor_get(v_x_612_, 0);
v___x_619_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_ipv4_617_, v_ipv4_618_);
return v___x_619_;
}
else
{
uint8_t v___x_620_; 
v___x_620_ = 0;
return v___x_620_;
}
}
default: 
{
if (lean_obj_tag(v_x_612_) == 2)
{
lean_object* v_ipv6_621_; lean_object* v_ipv6_622_; uint8_t v___x_623_; 
v_ipv6_621_ = lean_ctor_get(v_x_611_, 0);
v_ipv6_622_ = lean_ctor_get(v_x_612_, 0);
v___x_623_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_ipv6_621_, v_ipv6_622_);
return v___x_623_;
}
else
{
uint8_t v___x_624_; 
v___x_624_ = 0;
return v___x_624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqHost_beq___boxed(lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
uint8_t v_res_627_; lean_object* v_r_628_; 
v_res_627_ = l_Std_Http_URI_instBEqHost_beq(v_x_625_, v_x_626_);
lean_dec_ref(v_x_626_);
lean_dec_ref(v_x_625_);
v_r_628_ = lean_box(v_res_627_);
return v_r_628_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__4(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_unsigned_to_nat(2u);
v___x_636_ = lean_nat_to_int(v___x_635_);
return v___x_636_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__5(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = lean_nat_to_int(v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0(lean_object* v_x_639_, lean_object* v_prec_640_){
_start:
{
lean_object* v___y_642_; lean_object* v_ctr_643_; lean_object* v_a_644_; lean_object* v___y_656_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = lean_unsigned_to_nat(1024u);
v___x_688_ = lean_nat_dec_le(v___x_687_, v_prec_640_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
v___x_689_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_656_ = v___x_689_;
goto v___jp_655_;
}
else
{
lean_object* v___x_690_; 
v___x_690_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_656_ = v___x_690_;
goto v___jp_655_;
}
v___jp_641_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_645_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_646_ = lean_string_append(v___x_645_, v_ctr_643_);
v___x_647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
v___x_648_ = lean_box(1);
v___x_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set(v___x_650_, 1, v_a_644_);
lean_inc(v___y_642_);
v___x_651_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_651_, 0, v___y_642_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = 0;
v___x_653_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set_uint8(v___x_653_, sizeof(void*)*1, v___x_652_);
v___x_654_ = l_Repr_addAppParen(v___x_653_, v_prec_640_);
return v___x_654_;
}
v___jp_655_:
{
switch(lean_obj_tag(v_x_639_))
{
case 0:
{
lean_object* v_name_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_666_; 
v_name_657_ = lean_ctor_get(v_x_639_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v_x_639_);
if (v_isSharedCheck_666_ == 0)
{
v___x_659_ = v_x_639_;
v_isShared_660_ = v_isSharedCheck_666_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_name_657_);
lean_dec(v_x_639_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_666_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_661_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_662_ = l_String_quote(v_name_657_);
if (v_isShared_660_ == 0)
{
lean_ctor_set_tag(v___x_659_, 3);
lean_ctor_set(v___x_659_, 0, v___x_662_);
v___x_664_ = v___x_659_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
v___y_642_ = v___y_656_;
v_ctr_643_ = v___x_661_;
v_a_644_ = v___x_664_;
goto v___jp_641_;
}
}
}
case 1:
{
lean_object* v_ipv4_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_676_; 
v_ipv4_667_ = lean_ctor_get(v_x_639_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v_x_639_);
if (v_isSharedCheck_676_ == 0)
{
v___x_669_ = v_x_639_;
v_isShared_670_ = v_isSharedCheck_676_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_ipv4_667_);
lean_dec(v_x_639_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_676_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_671_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_672_ = lean_uv_ntop_v4(v_ipv4_667_);
lean_dec_ref(v_ipv4_667_);
if (v_isShared_670_ == 0)
{
lean_ctor_set_tag(v___x_669_, 3);
lean_ctor_set(v___x_669_, 0, v___x_672_);
v___x_674_ = v___x_669_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
v___y_642_ = v___y_656_;
v_ctr_643_ = v___x_671_;
v_a_644_ = v___x_674_;
goto v___jp_641_;
}
}
}
default: 
{
lean_object* v_ipv6_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_686_; 
v_ipv6_677_ = lean_ctor_get(v_x_639_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v_x_639_);
if (v_isSharedCheck_686_ == 0)
{
v___x_679_ = v_x_639_;
v_isShared_680_ = v_isSharedCheck_686_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_ipv6_677_);
lean_dec(v_x_639_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_686_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_681_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_682_ = lean_uv_ntop_v6(v_ipv6_677_);
lean_dec_ref(v_ipv6_677_);
if (v_isShared_680_ == 0)
{
lean_ctor_set_tag(v___x_679_, 3);
lean_ctor_set(v___x_679_, 0, v___x_682_);
v___x_684_ = v___x_679_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
v___y_642_ = v___y_656_;
v_ctr_643_ = v___x_681_;
v_a_644_ = v___x_684_;
goto v___jp_641_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0___boxed(lean_object* v_x_691_, lean_object* v_prec_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_Http_URI_instReprHost___lam__0(v_x_691_, v_prec_692_);
lean_dec(v_prec_692_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0(lean_object* v_x_698_){
_start:
{
switch(lean_obj_tag(v_x_698_))
{
case 0:
{
lean_object* v_name_699_; 
v_name_699_ = lean_ctor_get(v_x_698_, 0);
lean_inc_ref(v_name_699_);
return v_name_699_;
}
case 1:
{
lean_object* v_ipv4_700_; lean_object* v___x_701_; 
v_ipv4_700_ = lean_ctor_get(v_x_698_, 0);
v___x_701_ = lean_uv_ntop_v4(v_ipv4_700_);
return v___x_701_;
}
default: 
{
lean_object* v_ipv6_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_ipv6_702_ = lean_ctor_get(v_x_698_, 0);
v___x_703_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_704_ = lean_uv_ntop_v6(v_ipv6_702_);
v___x_705_ = lean_string_append(v___x_703_, v___x_704_);
lean_dec_ref(v___x_704_);
v___x_706_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_707_ = lean_string_append(v___x_705_, v___x_706_);
return v___x_707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0___boxed(lean_object* v_x_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Std_Http_URI_instToStringHost___lam__0(v_x_708_);
lean_dec_ref(v_x_708_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___impl(lean_object* v_x_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_tag_nat(v_x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___impl___boxed(lean_object* v_x_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Std_Http_URI_Port_ctorIdx___impl(v_x_714_);
lean_dec(v_x_714_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg(lean_object* v_t_716_, lean_object* v_k_717_){
_start:
{
if (lean_obj_tag(v_t_716_) == 2)
{
uint16_t v_port_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_port_718_ = lean_ctor_get_uint16(v_t_716_, 0);
v___x_719_ = lean_box(v_port_718_);
v___x_720_ = lean_apply_1(v_k_717_, v___x_719_);
return v___x_720_;
}
else
{
return v_k_717_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg___boxed(lean_object* v_t_721_, lean_object* v_k_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_721_, v_k_722_);
lean_dec(v_t_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim(lean_object* v_motive_724_, lean_object* v_ctorIdx_725_, lean_object* v_t_726_, lean_object* v_h_727_, lean_object* v_k_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_726_, v_k_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___boxed(lean_object* v_motive_730_, lean_object* v_ctorIdx_731_, lean_object* v_t_732_, lean_object* v_h_733_, lean_object* v_k_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_Http_URI_Port_ctorElim(v_motive_730_, v_ctorIdx_731_, v_t_732_, v_h_733_, v_k_734_);
lean_dec(v_t_732_);
lean_dec(v_ctorIdx_731_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg(lean_object* v_t_736_, lean_object* v_omitted_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_736_, v_omitted_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg___boxed(lean_object* v_t_739_, lean_object* v_omitted_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Std_Http_URI_Port_omitted_elim___redArg(v_t_739_, v_omitted_740_);
lean_dec(v_t_739_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim(lean_object* v_motive_742_, lean_object* v_t_743_, lean_object* v_h_744_, lean_object* v_omitted_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_743_, v_omitted_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___boxed(lean_object* v_motive_747_, lean_object* v_t_748_, lean_object* v_h_749_, lean_object* v_omitted_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_Http_URI_Port_omitted_elim(v_motive_747_, v_t_748_, v_h_749_, v_omitted_750_);
lean_dec(v_t_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg(lean_object* v_t_752_, lean_object* v_empty_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_752_, v_empty_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg___boxed(lean_object* v_t_755_, lean_object* v_empty_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Std_Http_URI_Port_empty_elim___redArg(v_t_755_, v_empty_756_);
lean_dec(v_t_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim(lean_object* v_motive_758_, lean_object* v_t_759_, lean_object* v_h_760_, lean_object* v_empty_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_759_, v_empty_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___boxed(lean_object* v_motive_763_, lean_object* v_t_764_, lean_object* v_h_765_, lean_object* v_empty_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_Http_URI_Port_empty_elim(v_motive_763_, v_t_764_, v_h_765_, v_empty_766_);
lean_dec(v_t_764_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg(lean_object* v_t_768_, lean_object* v_value_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_768_, v_value_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg___boxed(lean_object* v_t_771_, lean_object* v_value_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Std_Http_URI_Port_value_elim___redArg(v_t_771_, v_value_772_);
lean_dec(v_t_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim(lean_object* v_motive_774_, lean_object* v_t_775_, lean_object* v_h_776_, lean_object* v_value_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_775_, v_value_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___boxed(lean_object* v_motive_779_, lean_object* v_t_780_, lean_object* v_h_781_, lean_object* v_value_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Std_Http_URI_Port_value_elim(v_motive_779_, v_t_780_, v_h_781_, v_value_782_);
lean_dec(v_t_780_);
return v_res_783_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort_default(void){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = lean_box(0);
return v___x_784_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort(void){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = lean_box(0);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr(lean_object* v_x_798_, lean_object* v_prec_799_){
_start:
{
lean_object* v___y_801_; lean_object* v___y_808_; 
switch(lean_obj_tag(v_x_798_))
{
case 0:
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = lean_unsigned_to_nat(1024u);
v___x_815_ = lean_nat_dec_le(v___x_814_, v_prec_799_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; 
v___x_816_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_808_ = v___x_816_;
goto v___jp_807_;
}
else
{
lean_object* v___x_817_; 
v___x_817_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_808_ = v___x_817_;
goto v___jp_807_;
}
}
case 1:
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = lean_unsigned_to_nat(1024u);
v___x_819_ = lean_nat_dec_le(v___x_818_, v_prec_799_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
v___x_820_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_801_ = v___x_820_;
goto v___jp_800_;
}
else
{
lean_object* v___x_821_; 
v___x_821_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_801_ = v___x_821_;
goto v___jp_800_;
}
}
default: 
{
uint16_t v_port_822_; lean_object* v___y_824_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_port_822_ = lean_ctor_get_uint16(v_x_798_, 0);
v___x_834_ = lean_unsigned_to_nat(1024u);
v___x_835_ = lean_nat_dec_le(v___x_834_, v_prec_799_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
v___x_836_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_824_ = v___x_836_;
goto v___jp_823_;
}
else
{
lean_object* v___x_837_; 
v___x_837_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_824_ = v___x_837_;
goto v___jp_823_;
}
v___jp_823_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_825_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__6));
v___x_826_ = lean_uint16_to_nat(v_port_822_);
v___x_827_ = l_Nat_reprFast(v___x_826_);
v___x_828_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
v___x_829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_825_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
lean_inc(v___y_824_);
v___x_830_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_830_, 0, v___y_824_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = 0;
v___x_832_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*1, v___x_831_);
v___x_833_ = l_Repr_addAppParen(v___x_832_, v_prec_799_);
return v___x_833_;
}
}
}
v___jp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_802_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__1));
lean_inc(v___y_801_);
v___x_803_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_803_, 0, v___y_801_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = 0;
v___x_805_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*1, v___x_804_);
v___x_806_ = l_Repr_addAppParen(v___x_805_, v_prec_799_);
return v___x_806_;
}
v___jp_807_:
{
lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_809_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__3));
lean_inc(v___y_808_);
v___x_810_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_810_, 0, v___y_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = 0;
v___x_812_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set_uint8(v___x_812_, sizeof(void*)*1, v___x_811_);
v___x_813_ = l_Repr_addAppParen(v___x_812_, v_prec_799_);
return v___x_813_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr___boxed(lean_object* v_x_838_, lean_object* v_prec_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_Http_URI_instReprPort_repr(v_x_838_, v_prec_839_);
lean_dec(v_prec_839_);
lean_dec(v_x_838_);
return v_res_840_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort_decEq(lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
switch(lean_obj_tag(v_x_843_))
{
case 0:
{
if (lean_obj_tag(v_x_844_) == 0)
{
uint8_t v___x_845_; 
v___x_845_ = 1;
return v___x_845_;
}
else
{
uint8_t v___x_846_; 
v___x_846_ = 0;
return v___x_846_;
}
}
case 1:
{
if (lean_obj_tag(v_x_844_) == 1)
{
uint8_t v___x_847_; 
v___x_847_ = 1;
return v___x_847_;
}
else
{
uint8_t v___x_848_; 
v___x_848_ = 0;
return v___x_848_;
}
}
default: 
{
if (lean_obj_tag(v_x_844_) == 2)
{
uint16_t v_port_849_; uint16_t v_port_850_; uint8_t v___x_851_; 
v_port_849_ = lean_ctor_get_uint16(v_x_843_, 0);
v_port_850_ = lean_ctor_get_uint16(v_x_844_, 0);
v___x_851_ = lean_uint16_dec_eq(v_port_849_, v_port_850_);
return v___x_851_;
}
else
{
uint8_t v___x_852_; 
v___x_852_ = 0;
return v___x_852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort_decEq___boxed(lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
uint8_t v_res_855_; lean_object* v_r_856_; 
v_res_855_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_853_, v_x_854_);
lean_dec(v_x_854_);
lean_dec(v_x_853_);
v_r_856_ = lean_box(v_res_855_);
return v_r_856_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort(lean_object* v_x_857_, lean_object* v_x_858_){
_start:
{
uint8_t v___x_859_; 
v___x_859_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_857_, v_x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort___boxed(lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
uint8_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l_Std_Http_URI_instDecidableEqPort(v_x_860_, v_x_861_);
lean_dec(v_x_861_);
lean_dec(v_x_860_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_864_ = lean_box(0);
v___x_865_ = l_Std_Http_URI_instInhabitedHost_default;
v___x_866_ = lean_box(0);
v___x_867_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v___x_865_);
lean_ctor_set(v___x_867_, 2, v___x_864_);
return v___x_867_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default(void){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = lean_obj_once(&l_Std_Http_URI_instInhabitedAuthority_default___closed__0, &l_Std_Http_URI_instInhabitedAuthority_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0);
return v___x_868_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority(void){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Std_Http_URI_instInhabitedAuthority_default;
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
if (lean_obj_tag(v_x_870_) == 0)
{
lean_object* v___x_872_; 
v___x_872_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_872_;
}
else
{
lean_object* v_val_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_val_873_ = lean_ctor_get(v_x_870_, 0);
lean_inc(v_val_873_);
lean_dec_ref_known(v_x_870_, 1);
v___x_874_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_875_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_val_873_);
v___x_876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = l_Repr_addAppParen(v___x_876_, v_x_871_);
return v___x_877_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0___boxed(lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_x_878_, v_x_879_);
lean_dec(v_x_879_);
return v_res_880_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_unsigned_to_nat(8u);
v___x_894_ = lean_nat_to_int(v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg(lean_object* v_x_898_){
_start:
{
lean_object* v_userInfo_899_; lean_object* v_host_900_; lean_object* v_port_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v_ctr_921_; lean_object* v_a_922_; 
v_userInfo_899_ = lean_ctor_get(v_x_898_, 0);
lean_inc(v_userInfo_899_);
v_host_900_ = lean_ctor_get(v_x_898_, 1);
lean_inc_ref(v_host_900_);
v_port_901_ = lean_ctor_get(v_x_898_, 2);
lean_inc(v_port_901_);
lean_dec_ref(v_x_898_);
v___x_902_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_903_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3));
v___x_904_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_userInfo_899_, v___x_905_);
v___x_907_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_904_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = 0;
v___x_909_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set_uint8(v___x_909_, sizeof(void*)*1, v___x_908_);
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_903_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_910_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_box(1);
v___x_914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v___x_902_);
v___x_918_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_919_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_900_))
{
case 0:
{
lean_object* v_name_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_959_; 
v_name_950_ = lean_ctor_get(v_host_900_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v_host_900_);
if (v_isSharedCheck_959_ == 0)
{
v___x_952_ = v_host_900_;
v_isShared_953_ = v_isSharedCheck_959_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_name_950_);
lean_dec(v_host_900_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_959_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_954_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_955_ = l_String_quote(v_name_950_);
if (v_isShared_953_ == 0)
{
lean_ctor_set_tag(v___x_952_, 3);
lean_ctor_set(v___x_952_, 0, v___x_955_);
v___x_957_ = v___x_952_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
v_ctr_921_ = v___x_954_;
v_a_922_ = v___x_957_;
goto v___jp_920_;
}
}
}
case 1:
{
lean_object* v_ipv4_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_969_; 
v_ipv4_960_ = lean_ctor_get(v_host_900_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v_host_900_);
if (v_isSharedCheck_969_ == 0)
{
v___x_962_ = v_host_900_;
v_isShared_963_ = v_isSharedCheck_969_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_ipv4_960_);
lean_dec(v_host_900_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_969_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_964_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_965_ = lean_uv_ntop_v4(v_ipv4_960_);
lean_dec_ref(v_ipv4_960_);
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 3);
lean_ctor_set(v___x_962_, 0, v___x_965_);
v___x_967_ = v___x_962_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
v_ctr_921_ = v___x_964_;
v_a_922_ = v___x_967_;
goto v___jp_920_;
}
}
}
default: 
{
lean_object* v_ipv6_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_979_; 
v_ipv6_970_ = lean_ctor_get(v_host_900_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v_host_900_);
if (v_isSharedCheck_979_ == 0)
{
v___x_972_ = v_host_900_;
v_isShared_973_ = v_isSharedCheck_979_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_ipv6_970_);
lean_dec(v_host_900_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_979_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_974_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_975_ = lean_uv_ntop_v6(v_ipv6_970_);
lean_dec_ref(v_ipv6_970_);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 3);
lean_ctor_set(v___x_972_, 0, v___x_975_);
v___x_977_ = v___x_972_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
v_ctr_921_ = v___x_974_;
v_a_922_ = v___x_977_;
goto v___jp_920_;
}
}
}
}
v___jp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_923_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_924_ = lean_string_append(v___x_923_, v_ctr_921_);
v___x_925_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_913_);
v___x_927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v_a_922_);
v___x_928_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_919_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*1, v___x_908_);
v___x_930_ = l_Repr_addAppParen(v___x_929_, v___x_905_);
v___x_931_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_918_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*1, v___x_908_);
v___x_933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_917_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_911_);
v___x_935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___x_913_);
v___x_936_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_902_);
v___x_939_ = l_Std_Http_URI_instReprPort_repr(v_port_901_, v___x_905_);
lean_dec(v_port_901_);
v___x_940_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_918_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*1, v___x_908_);
v___x_942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_938_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_944_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_942_);
v___x_946_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_945_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_943_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*1, v___x_908_);
return v___x_949_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr(lean_object* v_x_980_, lean_object* v_prec_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_x_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___boxed(lean_object* v_x_983_, lean_object* v_prec_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Std_Http_URI_instReprAuthority_repr(v_x_983_, v_prec_984_);
lean_dec(v_prec_984_);
return v_res_985_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(lean_object* v_x_988_, lean_object* v_x_989_){
_start:
{
if (lean_obj_tag(v_x_988_) == 0)
{
if (lean_obj_tag(v_x_989_) == 0)
{
uint8_t v___x_990_; 
v___x_990_ = 1;
return v___x_990_;
}
else
{
uint8_t v___x_991_; 
v___x_991_ = 0;
return v___x_991_;
}
}
else
{
if (lean_obj_tag(v_x_989_) == 0)
{
uint8_t v___x_992_; 
v___x_992_ = 0;
return v___x_992_;
}
else
{
lean_object* v_val_993_; lean_object* v_val_994_; uint8_t v___x_995_; 
v_val_993_ = lean_ctor_get(v_x_988_, 0);
v_val_994_ = lean_ctor_get(v_x_989_, 0);
v___x_995_ = l_Std_Http_URI_instBEqUserInfo_beq(v_val_993_, v_val_994_);
return v___x_995_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0___boxed(lean_object* v_x_996_, lean_object* v_x_997_){
_start:
{
uint8_t v_res_998_; lean_object* v_r_999_; 
v_res_998_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_x_996_, v_x_997_);
lean_dec(v_x_997_);
lean_dec(v_x_996_);
v_r_999_ = lean_box(v_res_998_);
return v_r_999_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqAuthority_beq(lean_object* v_x_1000_, lean_object* v_x_1001_){
_start:
{
lean_object* v_userInfo_1002_; lean_object* v_host_1003_; lean_object* v_port_1004_; lean_object* v_userInfo_1005_; lean_object* v_host_1006_; lean_object* v_port_1007_; uint8_t v___x_1008_; 
v_userInfo_1002_ = lean_ctor_get(v_x_1000_, 0);
v_host_1003_ = lean_ctor_get(v_x_1000_, 1);
v_port_1004_ = lean_ctor_get(v_x_1000_, 2);
v_userInfo_1005_ = lean_ctor_get(v_x_1001_, 0);
v_host_1006_ = lean_ctor_get(v_x_1001_, 1);
v_port_1007_ = lean_ctor_get(v_x_1001_, 2);
v___x_1008_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_userInfo_1002_, v_userInfo_1005_);
if (v___x_1008_ == 0)
{
return v___x_1008_;
}
else
{
uint8_t v___x_1009_; 
v___x_1009_ = l_Std_Http_URI_instBEqHost_beq(v_host_1003_, v_host_1006_);
if (v___x_1009_ == 0)
{
return v___x_1009_;
}
else
{
uint8_t v___x_1010_; 
v___x_1010_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1004_, v_port_1007_);
return v___x_1010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqAuthority_beq___boxed(lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
uint8_t v_res_1013_; lean_object* v_r_1014_; 
v_res_1013_ = l_Std_Http_URI_instBEqAuthority_beq(v_x_1011_, v_x_1012_);
lean_dec_ref(v_x_1012_);
lean_dec_ref(v_x_1011_);
v_r_1014_ = lean_box(v_res_1013_);
return v_r_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringAuthority___lam__0(lean_object* v_auth_1020_){
_start:
{
lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v_userInfo_1027_; lean_object* v_host_1028_; lean_object* v_port_1029_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1041_; 
v_userInfo_1027_ = lean_ctor_get(v_auth_1020_, 0);
lean_inc(v_userInfo_1027_);
v_host_1028_ = lean_ctor_get(v_auth_1020_, 1);
lean_inc_ref(v_host_1028_);
v_port_1029_ = lean_ctor_get(v_auth_1020_, 2);
lean_inc(v_port_1029_);
lean_dec_ref(v_auth_1020_);
if (lean_obj_tag(v_userInfo_1027_) == 0)
{
lean_object* v___x_1051_; 
v___x_1051_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1041_ = v___x_1051_;
goto v___jp_1040_;
}
else
{
lean_object* v_val_1052_; lean_object* v_password_1053_; 
v_val_1052_ = lean_ctor_get(v_userInfo_1027_, 0);
lean_inc(v_val_1052_);
lean_dec_ref_known(v_userInfo_1027_, 1);
v_password_1053_ = lean_ctor_get(v_val_1052_, 1);
if (lean_obj_tag(v_password_1053_) == 0)
{
lean_object* v_username_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v_username_1054_ = lean_ctor_get(v_val_1052_, 0);
lean_inc_ref(v_username_1054_);
lean_dec(v_val_1052_);
v___x_1055_ = lean_string_from_utf8_unchecked(v_username_1054_);
v___x_1056_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1057_ = lean_string_append(v___x_1055_, v___x_1056_);
v___y_1041_ = v___x_1057_;
goto v___jp_1040_;
}
else
{
lean_object* v_username_1058_; lean_object* v_val_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_inc_ref(v_password_1053_);
v_username_1058_ = lean_ctor_get(v_val_1052_, 0);
lean_inc_ref(v_username_1058_);
lean_dec(v_val_1052_);
v_val_1059_ = lean_ctor_get(v_password_1053_, 0);
lean_inc(v_val_1059_);
lean_dec_ref_known(v_password_1053_, 1);
v___x_1060_ = lean_string_from_utf8_unchecked(v_username_1058_);
v___x_1061_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1062_ = lean_string_append(v___x_1060_, v___x_1061_);
v___x_1063_ = lean_string_from_utf8_unchecked(v_val_1059_);
v___x_1064_ = lean_string_append(v___x_1062_, v___x_1063_);
lean_dec_ref(v___x_1063_);
v___x_1065_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1066_ = lean_string_append(v___x_1064_, v___x_1065_);
v___y_1041_ = v___x_1066_;
goto v___jp_1040_;
}
}
v___jp_1021_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_string_append(v___y_1022_, v___y_1023_);
lean_dec_ref(v___y_1023_);
v___x_1026_ = lean_string_append(v___x_1025_, v___y_1024_);
lean_dec_ref(v___y_1024_);
return v___x_1026_;
}
v___jp_1030_:
{
switch(lean_obj_tag(v_port_1029_))
{
case 0:
{
lean_object* v___x_1033_; 
v___x_1033_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1022_ = v___y_1031_;
v___y_1023_ = v___y_1032_;
v___y_1024_ = v___x_1033_;
goto v___jp_1021_;
}
case 1:
{
lean_object* v___x_1034_; 
v___x_1034_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_1022_ = v___y_1031_;
v___y_1023_ = v___y_1032_;
v___y_1024_ = v___x_1034_;
goto v___jp_1021_;
}
default: 
{
uint16_t v_port_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_port_1035_ = lean_ctor_get_uint16(v_port_1029_, 0);
lean_dec_ref_known(v_port_1029_, 0);
v___x_1036_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1037_ = lean_uint16_to_nat(v_port_1035_);
v___x_1038_ = l_Nat_reprFast(v___x_1037_);
v___x_1039_ = lean_string_append(v___x_1036_, v___x_1038_);
lean_dec_ref(v___x_1038_);
v___y_1022_ = v___y_1031_;
v___y_1023_ = v___y_1032_;
v___y_1024_ = v___x_1039_;
goto v___jp_1021_;
}
}
}
v___jp_1040_:
{
switch(lean_obj_tag(v_host_1028_))
{
case 0:
{
lean_object* v_name_1042_; 
v_name_1042_ = lean_ctor_get(v_host_1028_, 0);
lean_inc_ref(v_name_1042_);
lean_dec_ref_known(v_host_1028_, 1);
v___y_1031_ = v___y_1041_;
v___y_1032_ = v_name_1042_;
goto v___jp_1030_;
}
case 1:
{
lean_object* v_ipv4_1043_; lean_object* v___x_1044_; 
v_ipv4_1043_ = lean_ctor_get(v_host_1028_, 0);
lean_inc_ref(v_ipv4_1043_);
lean_dec_ref_known(v_host_1028_, 1);
v___x_1044_ = lean_uv_ntop_v4(v_ipv4_1043_);
lean_dec_ref(v_ipv4_1043_);
v___y_1031_ = v___y_1041_;
v___y_1032_ = v___x_1044_;
goto v___jp_1030_;
}
default: 
{
lean_object* v_ipv6_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_ipv6_1045_ = lean_ctor_get(v_host_1028_, 0);
lean_inc_ref(v_ipv6_1045_);
lean_dec_ref_known(v_host_1028_, 1);
v___x_1046_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_1047_ = lean_uv_ntop_v6(v_ipv6_1045_);
lean_dec_ref(v_ipv6_1045_);
v___x_1048_ = lean_string_append(v___x_1046_, v___x_1047_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_1050_ = lean_string_append(v___x_1048_, v___x_1049_);
v___y_1031_ = v___y_1041_;
v___y_1032_ = v___x_1050_;
goto v___jp_1030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
if (lean_obj_tag(v_x_1078_) == 0)
{
lean_dec(v_x_1076_);
return v_x_1077_;
}
else
{
lean_object* v_head_1079_; lean_object* v_tail_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1092_; 
v_head_1079_ = lean_ctor_get(v_x_1078_, 0);
v_tail_1080_ = lean_ctor_get(v_x_1078_, 1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_x_1078_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1082_ = v_x_1078_;
v_isShared_1083_ = v_isSharedCheck_1092_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_tail_1080_);
lean_inc(v_head_1079_);
lean_dec(v_x_1078_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1092_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
lean_inc(v_x_1076_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 5);
lean_ctor_set(v___x_1082_, 1, v_x_1076_);
lean_ctor_set(v___x_1082_, 0, v_x_1077_);
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_x_1077_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_x_1076_);
v___x_1085_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1086_ = lean_string_from_utf8_unchecked(v_head_1079_);
v___x_1087_ = l_String_quote(v___x_1086_);
v___x_1088_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1085_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v_x_1077_ = v___x_1089_;
v_x_1078_ = v_tail_1080_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(lean_object* v_x_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_){
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
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1103_ = lean_string_from_utf8_unchecked(v_head_1096_);
v___x_1104_ = l_String_quote(v___x_1103_);
v___x_1105_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
v___x_1106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1102_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(v_x_1093_, v___x_1106_, v_tail_1097_);
return v___x_1107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(lean_object* v___y_1110_){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = lean_string_from_utf8_unchecked(v___y_1110_);
v___x_1112_ = l_String_quote(v___x_1111_);
v___x_1113_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
if (lean_obj_tag(v_x_1114_) == 0)
{
lean_object* v___x_1116_; 
lean_dec(v_x_1115_);
v___x_1116_ = lean_box(0);
return v___x_1116_;
}
else
{
lean_object* v_tail_1117_; 
v_tail_1117_ = lean_ctor_get(v_x_1114_, 1);
if (lean_obj_tag(v_tail_1117_) == 0)
{
lean_object* v_head_1118_; lean_object* v___x_1119_; 
lean_dec(v_x_1115_);
v_head_1118_ = lean_ctor_get(v_x_1114_, 0);
lean_inc(v_head_1118_);
lean_dec_ref_known(v_x_1114_, 2);
v___x_1119_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1118_);
return v___x_1119_;
}
else
{
lean_object* v_head_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_inc(v_tail_1117_);
v_head_1120_ = lean_ctor_get(v_x_1114_, 0);
lean_inc(v_head_1120_);
lean_dec_ref_known(v_x_1114_, 2);
v___x_1121_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1120_);
v___x_1122_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(v_x_1115_, v___x_1121_, v_tail_1117_);
return v___x_1122_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0));
v___x_1128_ = lean_string_length(v___x_1127_);
return v___x_1128_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2);
v___x_1130_ = lean_nat_to_int(v___x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(lean_object* v_xs_1138_){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1139_ = lean_array_get_size(v_xs_1138_);
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = lean_nat_dec_eq(v___x_1139_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1142_ = lean_array_to_list(v_xs_1138_);
v___x_1143_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1144_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(v___x_1142_, v___x_1143_);
v___x_1145_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1146_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v___x_1144_);
v___x_1148_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1145_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = l_Std_Format_fill(v___x_1150_);
return v___x_1151_;
}
else
{
lean_object* v___x_1152_; 
lean_dec_ref(v_xs_1138_);
v___x_1152_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1152_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___redArg(lean_object* v_x_1165_){
_start:
{
lean_object* v_segments_1166_; uint8_t v_absolute_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1199_; 
v_segments_1166_ = lean_ctor_get(v_x_1165_, 0);
v_absolute_1167_ = lean_ctor_get_uint8(v_x_1165_, sizeof(void*)*1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_x_1165_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1169_ = v_x_1165_;
v_isShared_1170_ = v_isSharedCheck_1199_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_segments_1166_);
lean_dec(v_x_1165_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1199_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; lean_object* v___x_1178_; 
v___x_1171_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1172_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__3));
v___x_1173_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_1174_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(v_segments_1166_);
v___x_1175_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = 0;
if (v_isShared_1170_ == 0)
{
lean_ctor_set_tag(v___x_1169_, 6);
lean_ctor_set(v___x_1169_, 0, v___x_1175_);
v___x_1178_ = v___x_1169_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1175_);
v___x_1178_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_ctor_set_uint8(v___x_1178_, sizeof(void*)*1, v___x_1176_);
v___x_1179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1172_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = lean_box(1);
v___x_1183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__5));
v___x_1185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set(v___x_1186_, 1, v___x_1171_);
v___x_1187_ = l_Bool_repr___redArg(v_absolute_1167_);
v___x_1188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1173_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
lean_ctor_set_uint8(v___x_1189_, sizeof(void*)*1, v___x_1176_);
v___x_1190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1186_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___x_1191_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1192_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v___x_1190_);
v___x_1194_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1191_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set_uint8(v___x_1197_, sizeof(void*)*1, v___x_1176_);
return v___x_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr(lean_object* v_x_1200_, lean_object* v_prec_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Std_Http_URI_instReprPath_repr___redArg(v_x_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___boxed(lean_object* v_x_1203_, lean_object* v_prec_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Std_Http_URI_instReprPath_repr(v_x_1203_, v_prec_1204_);
lean_dec(v_prec_1204_);
return v_res_1205_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(lean_object* v_xs_1208_, lean_object* v_ys_1209_, lean_object* v_x_1210_){
_start:
{
lean_object* v_zero_1211_; uint8_t v_isZero_1212_; 
v_zero_1211_ = lean_unsigned_to_nat(0u);
v_isZero_1212_ = lean_nat_dec_eq(v_x_1210_, v_zero_1211_);
if (v_isZero_1212_ == 1)
{
lean_dec(v_x_1210_);
return v_isZero_1212_;
}
else
{
lean_object* v_one_1213_; lean_object* v_n_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v_one_1213_ = lean_unsigned_to_nat(1u);
v_n_1214_ = lean_nat_sub(v_x_1210_, v_one_1213_);
lean_dec(v_x_1210_);
v___x_1215_ = lean_array_fget_borrowed(v_xs_1208_, v_n_1214_);
v___x_1216_ = lean_array_fget_borrowed(v_ys_1209_, v_n_1214_);
v___x_1217_ = lean_sarray_dec_eq(v___x_1215_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_dec(v_n_1214_);
return v___x_1217_;
}
else
{
v_x_1210_ = v_n_1214_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg___boxed(lean_object* v_xs_1219_, lean_object* v_ys_1220_, lean_object* v_x_1221_){
_start:
{
uint8_t v_res_1222_; lean_object* v_r_1223_; 
v_res_1222_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1219_, v_ys_1220_, v_x_1221_);
lean_dec_ref(v_ys_1220_);
lean_dec_ref(v_xs_1219_);
v_r_1223_ = lean_box(v_res_1222_);
return v_r_1223_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqPath_beq(lean_object* v_x_1224_, lean_object* v_x_1225_){
_start:
{
lean_object* v_segments_1226_; uint8_t v_absolute_1227_; lean_object* v_segments_1228_; uint8_t v_absolute_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_segments_1226_ = lean_ctor_get(v_x_1224_, 0);
v_absolute_1227_ = lean_ctor_get_uint8(v_x_1224_, sizeof(void*)*1);
v_segments_1228_ = lean_ctor_get(v_x_1225_, 0);
v_absolute_1229_ = lean_ctor_get_uint8(v_x_1225_, sizeof(void*)*1);
v___x_1230_ = lean_array_get_size(v_segments_1226_);
v___x_1231_ = lean_array_get_size(v_segments_1228_);
v___x_1232_ = lean_nat_dec_eq(v___x_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
return v___x_1232_;
}
else
{
uint8_t v___x_1233_; 
v___x_1233_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_segments_1226_, v_segments_1228_, v___x_1230_);
if (v___x_1233_ == 0)
{
return v___x_1233_;
}
else
{
if (v_absolute_1229_ == 0)
{
if (v_absolute_1227_ == 0)
{
return v___x_1233_;
}
else
{
return v_absolute_1229_;
}
}
else
{
return v_absolute_1227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqPath_beq___boxed(lean_object* v_x_1234_, lean_object* v_x_1235_){
_start:
{
uint8_t v_res_1236_; lean_object* v_r_1237_; 
v_res_1236_ = l_Std_Http_URI_instBEqPath_beq(v_x_1234_, v_x_1235_);
lean_dec_ref(v_x_1235_);
lean_dec_ref(v_x_1234_);
v_r_1237_ = lean_box(v_res_1236_);
return v_r_1237_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(lean_object* v_xs_1238_, lean_object* v_ys_1239_, lean_object* v_hsz_1240_, lean_object* v_x_1241_, lean_object* v_x_1242_){
_start:
{
uint8_t v___x_1243_; 
v___x_1243_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1238_, v_ys_1239_, v_x_1241_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___boxed(lean_object* v_xs_1244_, lean_object* v_ys_1245_, lean_object* v_hsz_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
uint8_t v_res_1249_; lean_object* v_r_1250_; 
v_res_1249_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(v_xs_1244_, v_ys_1245_, v_hsz_1246_, v_x_1247_, v_x_1248_);
lean_dec_ref(v_ys_1245_);
lean_dec_ref(v_xs_1244_);
v_r_1250_ = lean_box(v_res_1249_);
return v_r_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__0(lean_object* v_x_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_string_from_utf8_unchecked(v_x_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__1(lean_object* v___f_1275_, lean_object* v_path_1276_){
_start:
{
lean_object* v_segments_1277_; uint8_t v_absolute_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; size_t v_sz_1281_; size_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v_result_1285_; 
v_segments_1277_ = lean_ctor_get(v_path_1276_, 0);
lean_inc_ref(v_segments_1277_);
v_absolute_1278_ = lean_ctor_get_uint8(v_path_1276_, sizeof(void*)*1);
lean_dec_ref(v_path_1276_);
v___x_1279_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_1280_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_1281_ = lean_array_size(v_segments_1277_);
v___x_1282_ = ((size_t)0ULL);
v___x_1283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1280_, v___f_1275_, v_sz_1281_, v___x_1282_, v_segments_1277_);
v___x_1284_ = lean_array_to_list(v___x_1283_);
v_result_1285_ = l_String_intercalate(v___x_1279_, v___x_1284_);
if (v_absolute_1278_ == 0)
{
return v_result_1285_;
}
else
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_string_append(v___x_1279_, v_result_1285_);
lean_dec_ref(v_result_1285_);
return v___x_1286_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Path_isEmpty(lean_object* v_p_1291_){
_start:
{
lean_object* v_segments_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v_segments_1292_ = lean_ctor_get(v_p_1291_, 0);
v___x_1293_ = lean_array_get_size(v_segments_1292_);
v___x_1294_ = lean_unsigned_to_nat(0u);
v___x_1295_ = lean_nat_dec_eq(v___x_1293_, v___x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_isEmpty___boxed(lean_object* v_p_1296_){
_start:
{
uint8_t v_res_1297_; lean_object* v_r_1298_; 
v_res_1297_ = l_Std_Http_URI_Path_isEmpty(v_p_1296_);
lean_dec_ref(v_p_1296_);
v_r_1298_ = lean_box(v_res_1297_);
return v_r_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parent(lean_object* v_p_1299_){
_start:
{
lean_object* v_segments_1300_; uint8_t v_absolute_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v_segments_1300_ = lean_ctor_get(v_p_1299_, 0);
v_absolute_1301_ = lean_ctor_get_uint8(v_p_1299_, sizeof(void*)*1);
v___x_1302_ = lean_array_get_size(v_segments_1300_);
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = lean_nat_dec_eq(v___x_1302_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1312_; 
lean_inc_ref(v_segments_1300_);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_p_1299_);
if (v_isSharedCheck_1312_ == 0)
{
lean_object* v_unused_1313_; 
v_unused_1313_ = lean_ctor_get(v_p_1299_, 0);
lean_dec(v_unused_1313_);
v___x_1306_ = v_p_1299_;
v_isShared_1307_ = v_isSharedCheck_1312_;
goto v_resetjp_1305_;
}
else
{
lean_dec(v_p_1299_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1312_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1308_ = lean_array_pop(v_segments_1300_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1308_);
v___x_1310_ = v___x_1306_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
lean_ctor_set_uint8(v_reuseFailAlloc_1311_, sizeof(void*)*1, v_absolute_1301_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
else
{
return v_p_1299_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join(lean_object* v_p1_1314_, lean_object* v_p2_1315_){
_start:
{
uint8_t v_absolute_1316_; 
v_absolute_1316_ = lean_ctor_get_uint8(v_p2_1315_, sizeof(void*)*1);
if (v_absolute_1316_ == 0)
{
lean_object* v_segments_1317_; lean_object* v_segments_1318_; uint8_t v_absolute_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1327_; 
v_segments_1317_ = lean_ctor_get(v_p2_1315_, 0);
v_segments_1318_ = lean_ctor_get(v_p1_1314_, 0);
v_absolute_1319_ = lean_ctor_get_uint8(v_p1_1314_, sizeof(void*)*1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_p1_1314_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1321_ = v_p1_1314_;
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_segments_1318_);
lean_dec(v_p1_1314_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1323_ = l_Array_append___redArg(v_segments_1318_, v_segments_1317_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1323_);
v___x_1325_ = v___x_1321_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
lean_ctor_set_uint8(v_reuseFailAlloc_1326_, sizeof(void*)*1, v_absolute_1319_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
else
{
lean_dec_ref(v_p1_1314_);
lean_inc_ref(v_p2_1315_);
return v_p2_1315_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join___boxed(lean_object* v_p1_1328_, lean_object* v_p2_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Std_Http_URI_Path_join(v_p1_1328_, v_p2_1329_);
lean_dec_ref(v_p2_1329_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append(lean_object* v_p_1331_, lean_object* v_segment_1332_){
_start:
{
lean_object* v_segments_1333_; uint8_t v_absolute_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1343_; 
v_segments_1333_ = lean_ctor_get(v_p_1331_, 0);
v_absolute_1334_ = lean_ctor_get_uint8(v_p_1331_, sizeof(void*)*1);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_p_1331_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1336_ = v_p_1331_;
v_isShared_1337_ = v_isSharedCheck_1343_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_segments_1333_);
lean_dec(v_p_1331_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1343_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1338_ = l_Std_Http_URI_EncodedSegment_encode(v_segment_1332_);
v___x_1339_ = lean_array_push(v_segments_1333_, v___x_1338_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1339_);
v___x_1341_ = v___x_1336_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*1, v_absolute_1334_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append___boxed(lean_object* v_p_1344_, lean_object* v_segment_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Std_Http_URI_Path_append(v_p_1344_, v_segment_1345_);
lean_dec_ref(v_segment_1345_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_appendEncoded(lean_object* v_p_1347_, lean_object* v_segment_1348_){
_start:
{
lean_object* v_segments_1349_; uint8_t v_absolute_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1358_; 
v_segments_1349_ = lean_ctor_get(v_p_1347_, 0);
v_absolute_1350_ = lean_ctor_get_uint8(v_p_1347_, sizeof(void*)*1);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_p_1347_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1352_ = v_p_1347_;
v_isShared_1353_ = v_isSharedCheck_1358_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_segments_1349_);
lean_dec(v_p_1347_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1358_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1354_ = lean_array_push(v_segments_1349_, v_segment_1348_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1354_);
v___x_1356_ = v___x_1352_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
lean_ctor_set_uint8(v_reuseFailAlloc_1357_, sizeof(void*)*1, v_absolute_1350_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(lean_object* v_input_1361_, lean_object* v_output_1362_){
_start:
{
if (lean_obj_tag(v_input_1361_) == 0)
{
lean_object* v___x_1363_; 
v___x_1363_ = l_List_reverse___redArg(v_output_1362_);
return v___x_1363_;
}
else
{
lean_object* v_head_1364_; lean_object* v_tail_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1382_; 
v_head_1364_ = lean_ctor_get(v_input_1361_, 0);
v_tail_1365_ = lean_ctor_get(v_input_1361_, 1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_input_1361_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1367_ = v_input_1361_;
v_isShared_1368_ = v_isSharedCheck_1382_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_tail_1365_);
lean_inc(v_head_1364_);
lean_dec(v_input_1361_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1382_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
lean_inc(v_head_1364_);
v___x_1369_ = lean_string_from_utf8_unchecked(v_head_1364_);
v___x_1370_ = ((lean_object*)(l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0));
v___x_1371_ = lean_string_dec_eq(v___x_1369_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; uint8_t v___x_1373_; 
v___x_1372_ = ((lean_object*)(l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1));
v___x_1373_ = lean_string_dec_eq(v___x_1369_, v___x_1372_);
lean_dec_ref(v___x_1369_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1375_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 1, v_output_1362_);
v___x_1375_ = v___x_1367_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_head_1364_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_output_1362_);
v___x_1375_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
v_input_1361_ = v_tail_1365_;
v_output_1362_ = v___x_1375_;
goto _start;
}
}
else
{
lean_del_object(v___x_1367_);
lean_dec(v_head_1364_);
if (lean_obj_tag(v_output_1362_) == 0)
{
v_input_1361_ = v_tail_1365_;
goto _start;
}
else
{
lean_object* v_tail_1379_; 
v_tail_1379_ = lean_ctor_get(v_output_1362_, 1);
lean_inc(v_tail_1379_);
lean_dec_ref_known(v_output_1362_, 2);
v_input_1361_ = v_tail_1365_;
v_output_1362_ = v_tail_1379_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_1369_);
lean_del_object(v___x_1367_);
lean_dec(v_head_1364_);
v_input_1361_ = v_tail_1365_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_normalize(lean_object* v_p_1383_){
_start:
{
lean_object* v_segments_1384_; uint8_t v_absolute_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1396_; 
v_segments_1384_ = lean_ctor_get(v_p_1383_, 0);
v_absolute_1385_ = lean_ctor_get_uint8(v_p_1383_, sizeof(void*)*1);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_p_1383_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1387_ = v_p_1383_;
v_isShared_1388_ = v_isSharedCheck_1396_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_segments_1384_);
lean_dec(v_p_1383_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1396_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1389_ = lean_array_to_list(v_segments_1384_);
v___x_1390_ = lean_box(0);
v___x_1391_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(v___x_1389_, v___x_1390_);
v___x_1392_ = lean_array_mk(v___x_1391_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1392_);
v___x_1394_ = v___x_1387_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1395_, sizeof(void*)*1, v_absolute_1385_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(size_t v_sz_1397_, size_t v_i_1398_, lean_object* v_bs_1399_){
_start:
{
uint8_t v___x_1400_; 
v___x_1400_ = lean_usize_dec_lt(v_i_1398_, v_sz_1397_);
if (v___x_1400_ == 0)
{
return v_bs_1399_;
}
else
{
lean_object* v_v_1401_; lean_object* v___x_1402_; lean_object* v_bs_x27_1403_; lean_object* v___y_1405_; lean_object* v___x_1410_; 
v_v_1401_ = lean_array_uget(v_bs_1399_, v_i_1398_);
v___x_1402_ = lean_unsigned_to_nat(0u);
v_bs_x27_1403_ = lean_array_uset(v_bs_1399_, v_i_1398_, v___x_1402_);
v___x_1410_ = l_Std_Http_URI_EncodedSegment_decode(v_v_1401_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_string_from_utf8_unchecked(v_v_1401_);
v___y_1405_ = v___x_1411_;
goto v___jp_1404_;
}
else
{
lean_object* v_val_1412_; 
lean_dec(v_v_1401_);
v_val_1412_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_val_1412_);
lean_dec_ref_known(v___x_1410_, 1);
v___y_1405_ = v_val_1412_;
goto v___jp_1404_;
}
v___jp_1404_:
{
size_t v___x_1406_; size_t v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = ((size_t)1ULL);
v___x_1407_ = lean_usize_add(v_i_1398_, v___x_1406_);
v___x_1408_ = lean_array_uset(v_bs_x27_1403_, v_i_1398_, v___y_1405_);
v_i_1398_ = v___x_1407_;
v_bs_1399_ = v___x_1408_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0___boxed(lean_object* v_sz_1413_, lean_object* v_i_1414_, lean_object* v_bs_1415_){
_start:
{
size_t v_sz_boxed_1416_; size_t v_i_boxed_1417_; lean_object* v_res_1418_; 
v_sz_boxed_1416_ = lean_unbox_usize(v_sz_1413_);
lean_dec(v_sz_1413_);
v_i_boxed_1417_ = lean_unbox_usize(v_i_1414_);
lean_dec(v_i_1414_);
v_res_1418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_boxed_1416_, v_i_boxed_1417_, v_bs_1415_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_toDecodedSegments(lean_object* v_p_1419_){
_start:
{
lean_object* v_segments_1420_; size_t v_sz_1421_; size_t v___x_1422_; lean_object* v___x_1423_; 
v_segments_1420_ = lean_ctor_get(v_p_1419_, 0);
lean_inc_ref(v_segments_1420_);
lean_dec_ref(v_p_1419_);
v_sz_1421_ = lean_array_size(v_segments_1420_);
v___x_1422_ = ((size_t)0ULL);
v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_1421_, v___x_1422_, v_segments_1420_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___redArg(lean_object* v_xs_1432_){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1434_ = l_Array_repr___redArg(v___x_1433_, v_xs_1432_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1(lean_object* v_xs_1435_, lean_object* v_x_1436_){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1438_ = l_Array_repr___redArg(v___x_1437_, v_xs_1435_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___boxed(lean_object* v_xs_1439_, lean_object* v_x_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Std_Http_URI_instReprQuery___aux__1(v_xs_1439_, v_x_1440_);
lean_dec(v_x_1440_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_1442_, lean_object* v_x_1443_, lean_object* v_x_1444_){
_start:
{
if (lean_obj_tag(v_x_1444_) == 0)
{
lean_dec(v_x_1442_);
return v_x_1443_;
}
else
{
lean_object* v_head_1445_; lean_object* v_tail_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1455_; 
v_head_1445_ = lean_ctor_get(v_x_1444_, 0);
v_tail_1446_ = lean_ctor_get(v_x_1444_, 1);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_x_1444_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1448_ = v_x_1444_;
v_isShared_1449_ = v_isSharedCheck_1455_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_tail_1446_);
lean_inc(v_head_1445_);
lean_dec(v_x_1444_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1455_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
lean_inc(v_x_1442_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set_tag(v___x_1448_, 5);
lean_ctor_set(v___x_1448_, 1, v_x_1442_);
lean_ctor_set(v___x_1448_, 0, v_x_1443_);
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_x_1443_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_x_1442_);
v___x_1451_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
lean_ctor_set(v___x_1452_, 1, v_head_1445_);
v_x_1443_ = v___x_1452_;
v_x_1444_ = v_tail_1446_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(lean_object* v_x_1456_, lean_object* v_x_1457_){
_start:
{
if (lean_obj_tag(v_x_1456_) == 0)
{
lean_object* v___x_1458_; 
lean_dec(v_x_1457_);
v___x_1458_ = lean_box(0);
return v___x_1458_;
}
else
{
lean_object* v_tail_1459_; 
v_tail_1459_ = lean_ctor_get(v_x_1456_, 1);
if (lean_obj_tag(v_tail_1459_) == 0)
{
lean_object* v_head_1460_; 
lean_dec(v_x_1457_);
v_head_1460_ = lean_ctor_get(v_x_1456_, 0);
lean_inc(v_head_1460_);
lean_dec_ref_known(v_x_1456_, 2);
return v_head_1460_;
}
else
{
lean_object* v_head_1461_; lean_object* v___x_1462_; 
lean_inc(v_tail_1459_);
v_head_1461_ = lean_ctor_get(v_x_1456_, 0);
lean_inc(v_head_1461_);
lean_dec_ref_known(v_x_1456_, 2);
v___x_1462_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(v_x_1457_, v_head_1461_, v_tail_1459_);
return v___x_1462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(lean_object* v_x_1463_, lean_object* v_x_1464_){
_start:
{
if (lean_obj_tag(v_x_1463_) == 0)
{
lean_object* v___x_1465_; 
v___x_1465_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1465_;
}
else
{
lean_object* v_val_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1478_; 
v_val_1466_ = lean_ctor_get(v_x_1463_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_x_1463_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1468_ = v_x_1463_;
v_isShared_1469_ = v_isSharedCheck_1478_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_val_1466_);
lean_dec(v_x_1463_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1478_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1470_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1471_ = lean_string_from_utf8_unchecked(v_val_1466_);
v___x_1472_ = l_String_quote(v___x_1471_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set_tag(v___x_1468_, 3);
lean_ctor_set(v___x_1468_, 0, v___x_1472_);
v___x_1474_ = v___x_1468_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1470_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = l_Repr_addAppParen(v___x_1475_, v_x_1464_);
return v___x_1476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1479_, lean_object* v_x_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_x_1479_, v_x_1480_);
lean_dec(v_x_1480_);
return v_res_1481_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0));
v___x_1485_ = lean_string_length(v___x_1484_);
return v___x_1485_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2);
v___x_1487_ = lean_nat_to_int(v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(lean_object* v_x_1492_){
_start:
{
lean_object* v_fst_1493_; lean_object* v_snd_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1519_; 
v_fst_1493_ = lean_ctor_get(v_x_1492_, 0);
v_snd_1494_ = lean_ctor_get(v_x_1492_, 1);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_x_1492_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1496_ = v_x_1492_;
v_isShared_1497_ = v_isSharedCheck_1519_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_snd_1494_);
lean_inc(v_fst_1493_);
lean_dec(v_x_1492_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1519_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1498_ = lean_string_from_utf8_unchecked(v_fst_1493_);
v___x_1499_ = l_String_quote(v___x_1498_);
v___x_1500_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
v___x_1501_ = lean_box(0);
if (v_isShared_1497_ == 0)
{
lean_ctor_set_tag(v___x_1496_, 1);
lean_ctor_set(v___x_1496_, 1, v___x_1501_);
lean_ctor_set(v___x_1496_, 0, v___x_1500_);
v___x_1503_ = v___x_1496_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; uint8_t v___x_1516_; lean_object* v___x_1517_; 
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_snd_1494_, v___x_1504_);
v___x_1506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v___x_1503_);
v___x_1507_ = l_List_reverse___redArg(v___x_1506_);
v___x_1508_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1509_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(v___x_1507_, v___x_1508_);
v___x_1510_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3);
v___x_1511_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4));
v___x_1512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
lean_ctor_set(v___x_1512_, 1, v___x_1509_);
v___x_1513_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5));
v___x_1514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1510_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___x_1516_ = 0;
v___x_1517_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1517_, 0, v___x_1515_);
lean_ctor_set_uint8(v___x_1517_, sizeof(void*)*1, v___x_1516_);
return v___x_1517_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(lean_object* v_x_1520_, lean_object* v_x_1521_, lean_object* v_x_1522_){
_start:
{
if (lean_obj_tag(v_x_1522_) == 0)
{
lean_dec(v_x_1520_);
return v_x_1521_;
}
else
{
lean_object* v_head_1523_; lean_object* v_tail_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1534_; 
v_head_1523_ = lean_ctor_get(v_x_1522_, 0);
v_tail_1524_ = lean_ctor_get(v_x_1522_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_x_1522_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1526_ = v_x_1522_;
v_isShared_1527_ = v_isSharedCheck_1534_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_tail_1524_);
lean_inc(v_head_1523_);
lean_dec(v_x_1522_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1534_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
lean_inc(v_x_1520_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set_tag(v___x_1526_, 5);
lean_ctor_set(v___x_1526_, 1, v_x_1520_);
lean_ctor_set(v___x_1526_, 0, v_x_1521_);
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_x_1521_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_x_1520_);
v___x_1529_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1523_);
v___x_1531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v_x_1521_ = v___x_1531_;
v_x_1522_ = v_tail_1524_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(lean_object* v_x_1535_, lean_object* v_x_1536_, lean_object* v_x_1537_){
_start:
{
if (lean_obj_tag(v_x_1537_) == 0)
{
lean_dec(v_x_1535_);
return v_x_1536_;
}
else
{
lean_object* v_head_1538_; lean_object* v_tail_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1549_; 
v_head_1538_ = lean_ctor_get(v_x_1537_, 0);
v_tail_1539_ = lean_ctor_get(v_x_1537_, 1);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_x_1537_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1541_ = v_x_1537_;
v_isShared_1542_ = v_isSharedCheck_1549_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_tail_1539_);
lean_inc(v_head_1538_);
lean_dec(v_x_1537_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1549_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
lean_inc(v_x_1535_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set_tag(v___x_1541_, 5);
lean_ctor_set(v___x_1541_, 1, v_x_1535_);
lean_ctor_set(v___x_1541_, 0, v_x_1536_);
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_x_1536_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_x_1535_);
v___x_1544_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1538_);
v___x_1546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(v_x_1535_, v___x_1546_, v_tail_1539_);
return v___x_1547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(lean_object* v_x_1550_, lean_object* v_x_1551_){
_start:
{
if (lean_obj_tag(v_x_1550_) == 0)
{
lean_object* v___x_1552_; 
lean_dec(v_x_1551_);
v___x_1552_ = lean_box(0);
return v___x_1552_;
}
else
{
lean_object* v_tail_1553_; 
v_tail_1553_ = lean_ctor_get(v_x_1550_, 1);
if (lean_obj_tag(v_tail_1553_) == 0)
{
lean_object* v_head_1554_; lean_object* v___x_1555_; 
lean_dec(v_x_1551_);
v_head_1554_ = lean_ctor_get(v_x_1550_, 0);
lean_inc(v_head_1554_);
lean_dec_ref_known(v_x_1550_, 2);
v___x_1555_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1554_);
return v___x_1555_;
}
else
{
lean_object* v_head_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_inc(v_tail_1553_);
v_head_1556_ = lean_ctor_get(v_x_1550_, 0);
lean_inc(v_head_1556_);
lean_dec_ref_known(v_x_1550_, 2);
v___x_1557_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1556_);
v___x_1558_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(v_x_1551_, v___x_1557_, v_tail_1553_);
return v___x_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(lean_object* v_xs_1559_){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; 
v___x_1560_ = lean_array_get_size(v_xs_1559_);
v___x_1561_ = lean_unsigned_to_nat(0u);
v___x_1562_ = lean_nat_dec_eq(v___x_1560_, v___x_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1563_ = lean_array_to_list(v_xs_1559_);
v___x_1564_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1565_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(v___x_1563_, v___x_1564_);
v___x_1566_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1567_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v___x_1565_);
v___x_1569_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1566_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = l_Std_Format_fill(v___x_1571_);
return v___x_1572_;
}
else
{
lean_object* v___x_1573_; 
lean_dec_ref(v_xs_1559_);
v___x_1573_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0(lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v___y_1574_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0___boxed(lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Std_Http_URI_instReprQuery___lam__0(v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(lean_object* v_x_1582_, lean_object* v_x_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_x_1582_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___boxed(lean_object* v_x_1585_, lean_object* v_x_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(v_x_1585_, v_x_1586_);
lean_dec(v_x_1586_);
return v_res_1587_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1___lam__0(lean_object* v___f_1592_, lean_object* v_x_1593_, lean_object* v_x_1594_){
_start:
{
lean_object* v_fst_1595_; lean_object* v_snd_1596_; lean_object* v_fst_1597_; lean_object* v_snd_1598_; uint8_t v___x_1599_; 
v_fst_1595_ = lean_ctor_get(v_x_1593_, 0);
lean_inc(v_fst_1595_);
v_snd_1596_ = lean_ctor_get(v_x_1593_, 1);
lean_inc(v_snd_1596_);
lean_dec_ref(v_x_1593_);
v_fst_1597_ = lean_ctor_get(v_x_1594_, 0);
lean_inc(v_fst_1597_);
v_snd_1598_ = lean_ctor_get(v_x_1594_, 1);
lean_inc(v_snd_1598_);
lean_dec_ref(v_x_1594_);
v___x_1599_ = lean_sarray_dec_eq(v_fst_1595_, v_fst_1597_);
lean_dec(v_fst_1597_);
lean_dec(v_fst_1595_);
if (v___x_1599_ == 0)
{
lean_dec(v_snd_1598_);
lean_dec(v_snd_1596_);
lean_dec_ref(v___f_1592_);
return v___x_1599_;
}
else
{
uint8_t v___x_1600_; 
v___x_1600_ = l_instBEqOption_beq___redArg(v___f_1592_, v_snd_1596_, v_snd_1598_);
return v___x_1600_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___lam__0___boxed(lean_object* v___f_1601_, lean_object* v_x_1602_, lean_object* v_x_1603_){
_start:
{
uint8_t v_res_1604_; lean_object* v_r_1605_; 
v_res_1604_ = l_Std_Http_URI_instBEqQuery___aux__1___lam__0(v___f_1601_, v_x_1602_, v_x_1603_);
v_r_1605_ = lean_box(v_res_1604_);
return v_r_1605_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1(lean_object* v_xs_1609_, lean_object* v_ys_1610_){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1611_ = lean_array_get_size(v_xs_1609_);
v___x_1612_ = lean_array_get_size(v_ys_1610_);
v___x_1613_ = lean_nat_dec_eq(v___x_1611_, v___x_1612_);
if (v___x_1613_ == 0)
{
return v___x_1613_;
}
else
{
lean_object* v___f_1614_; uint8_t v___x_1615_; 
v___f_1614_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__1));
v___x_1615_ = l_Array_isEqvAux___redArg(v_xs_1609_, v_ys_1610_, v___f_1614_, v___x_1611_);
return v___x_1615_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___boxed(lean_object* v_xs_1616_, lean_object* v_ys_1617_){
_start:
{
uint8_t v_res_1618_; lean_object* v_r_1619_; 
v_res_1618_ = l_Std_Http_URI_instBEqQuery___aux__1(v_xs_1616_, v_ys_1617_);
lean_dec_ref(v_ys_1617_);
lean_dec_ref(v_xs_1616_);
v_r_1619_ = lean_box(v_res_1618_);
return v_r_1619_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(lean_object* v_x_1620_, lean_object* v_x_1621_){
_start:
{
if (lean_obj_tag(v_x_1620_) == 0)
{
if (lean_obj_tag(v_x_1621_) == 0)
{
uint8_t v___x_1622_; 
v___x_1622_ = 1;
return v___x_1622_;
}
else
{
uint8_t v___x_1623_; 
v___x_1623_ = 0;
return v___x_1623_;
}
}
else
{
if (lean_obj_tag(v_x_1621_) == 0)
{
uint8_t v___x_1624_; 
v___x_1624_ = 0;
return v___x_1624_;
}
else
{
lean_object* v_val_1625_; lean_object* v_val_1626_; uint8_t v___x_1627_; 
v_val_1625_ = lean_ctor_get(v_x_1620_, 0);
v_val_1626_ = lean_ctor_get(v_x_1621_, 0);
v___x_1627_ = lean_sarray_dec_eq(v_val_1625_, v_val_1626_);
return v___x_1627_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0___boxed(lean_object* v_x_1628_, lean_object* v_x_1629_){
_start:
{
uint8_t v_res_1630_; lean_object* v_r_1631_; 
v_res_1630_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_x_1628_, v_x_1629_);
lean_dec(v_x_1629_);
lean_dec(v_x_1628_);
v_r_1631_ = lean_box(v_res_1630_);
return v_r_1631_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(lean_object* v_xs_1632_, lean_object* v_ys_1633_, lean_object* v_x_1634_){
_start:
{
lean_object* v_zero_1635_; uint8_t v_isZero_1636_; 
v_zero_1635_ = lean_unsigned_to_nat(0u);
v_isZero_1636_ = lean_nat_dec_eq(v_x_1634_, v_zero_1635_);
if (v_isZero_1636_ == 1)
{
lean_dec(v_x_1634_);
return v_isZero_1636_;
}
else
{
lean_object* v_one_1637_; lean_object* v_n_1638_; lean_object* v___x_1639_; lean_object* v_fst_1640_; lean_object* v_snd_1641_; lean_object* v___x_1642_; lean_object* v_fst_1643_; lean_object* v_snd_1644_; uint8_t v___x_1645_; 
v_one_1637_ = lean_unsigned_to_nat(1u);
v_n_1638_ = lean_nat_sub(v_x_1634_, v_one_1637_);
lean_dec(v_x_1634_);
v___x_1639_ = lean_array_fget_borrowed(v_xs_1632_, v_n_1638_);
v_fst_1640_ = lean_ctor_get(v___x_1639_, 0);
v_snd_1641_ = lean_ctor_get(v___x_1639_, 1);
v___x_1642_ = lean_array_fget_borrowed(v_ys_1633_, v_n_1638_);
v_fst_1643_ = lean_ctor_get(v___x_1642_, 0);
v_snd_1644_ = lean_ctor_get(v___x_1642_, 1);
v___x_1645_ = lean_sarray_dec_eq(v_fst_1640_, v_fst_1643_);
if (v___x_1645_ == 0)
{
lean_dec(v_n_1638_);
return v___x_1645_;
}
else
{
uint8_t v___x_1646_; 
v___x_1646_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_snd_1641_, v_snd_1644_);
if (v___x_1646_ == 0)
{
lean_dec(v_n_1638_);
return v___x_1646_;
}
else
{
v_x_1634_ = v_n_1638_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg___boxed(lean_object* v_xs_1648_, lean_object* v_ys_1649_, lean_object* v_x_1650_){
_start:
{
uint8_t v_res_1651_; lean_object* v_r_1652_; 
v_res_1651_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1648_, v_ys_1649_, v_x_1650_);
lean_dec_ref(v_ys_1649_);
lean_dec_ref(v_xs_1648_);
v_r_1652_ = lean_box(v_res_1651_);
return v_r_1652_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___lam__0(lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1655_ = lean_array_get_size(v___y_1653_);
v___x_1656_ = lean_array_get_size(v___y_1654_);
v___x_1657_ = lean_nat_dec_eq(v___x_1655_, v___x_1656_);
if (v___x_1657_ == 0)
{
return v___x_1657_;
}
else
{
uint8_t v___x_1658_; 
v___x_1658_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v___y_1653_, v___y_1654_, v___x_1655_);
return v___x_1658_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___lam__0___boxed(lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
uint8_t v_res_1661_; lean_object* v_r_1662_; 
v_res_1661_ = l_Std_Http_URI_instBEqQuery___lam__0(v___y_1659_, v___y_1660_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v___y_1659_);
v_r_1662_ = lean_box(v_res_1661_);
return v_r_1662_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(lean_object* v_xs_1665_, lean_object* v_ys_1666_, lean_object* v_hsz_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_){
_start:
{
uint8_t v___x_1670_; 
v___x_1670_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1665_, v_ys_1666_, v_x_1668_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___boxed(lean_object* v_xs_1671_, lean_object* v_ys_1672_, lean_object* v_hsz_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_){
_start:
{
uint8_t v_res_1676_; lean_object* v_r_1677_; 
v_res_1676_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(v_xs_1671_, v_ys_1672_, v_hsz_1673_, v_x_1674_, v_x_1675_);
lean_dec_ref(v_ys_1672_);
lean_dec_ref(v_xs_1671_);
v_r_1677_ = lean_box(v_res_1676_);
return v_r_1677_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(lean_object* v_as_1678_){
_start:
{
lean_object* v___f_1679_; lean_object* v___x_1680_; 
v___f_1679_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__0));
v___x_1680_ = l_List_eraseDupsBy___redArg(v___f_1679_, v_as_1678_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(size_t v_sz_1681_, size_t v_i_1682_, lean_object* v_bs_1683_){
_start:
{
uint8_t v___x_1684_; 
v___x_1684_ = lean_usize_dec_lt(v_i_1682_, v_sz_1681_);
if (v___x_1684_ == 0)
{
return v_bs_1683_;
}
else
{
lean_object* v_v_1685_; lean_object* v_fst_1686_; lean_object* v___x_1687_; lean_object* v_bs_x27_1688_; size_t v___x_1689_; size_t v___x_1690_; lean_object* v___x_1691_; 
v_v_1685_ = lean_array_uget_borrowed(v_bs_1683_, v_i_1682_);
v_fst_1686_ = lean_ctor_get(v_v_1685_, 0);
lean_inc(v_fst_1686_);
v___x_1687_ = lean_unsigned_to_nat(0u);
v_bs_x27_1688_ = lean_array_uset(v_bs_1683_, v_i_1682_, v___x_1687_);
v___x_1689_ = ((size_t)1ULL);
v___x_1690_ = lean_usize_add(v_i_1682_, v___x_1689_);
v___x_1691_ = lean_array_uset(v_bs_x27_1688_, v_i_1682_, v_fst_1686_);
v_i_1682_ = v___x_1690_;
v_bs_1683_ = v___x_1691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0___boxed(lean_object* v_sz_1693_, lean_object* v_i_1694_, lean_object* v_bs_1695_){
_start:
{
size_t v_sz_boxed_1696_; size_t v_i_boxed_1697_; lean_object* v_res_1698_; 
v_sz_boxed_1696_ = lean_unbox_usize(v_sz_1693_);
lean_dec(v_sz_1693_);
v_i_boxed_1697_ = lean_unbox_usize(v_i_1694_);
lean_dec(v_i_1694_);
v_res_1698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_boxed_1696_, v_i_boxed_1697_, v_bs_1695_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names(lean_object* v_query_1699_){
_start:
{
size_t v_sz_1700_; size_t v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_sz_1700_ = lean_array_size(v_query_1699_);
v___x_1701_ = ((size_t)0ULL);
v___x_1702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_1700_, v___x_1701_, v_query_1699_);
v___x_1703_ = lean_array_to_list(v___x_1702_);
v___x_1704_ = l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(v___x_1703_);
v___x_1705_ = lean_array_mk(v___x_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(size_t v_sz_1706_, size_t v_i_1707_, lean_object* v_bs_1708_){
_start:
{
uint8_t v___x_1709_; 
v___x_1709_ = lean_usize_dec_lt(v_i_1707_, v_sz_1706_);
if (v___x_1709_ == 0)
{
return v_bs_1708_;
}
else
{
lean_object* v_v_1710_; lean_object* v_snd_1711_; lean_object* v___x_1712_; lean_object* v_bs_x27_1713_; size_t v___x_1714_; size_t v___x_1715_; lean_object* v___x_1716_; 
v_v_1710_ = lean_array_uget_borrowed(v_bs_1708_, v_i_1707_);
v_snd_1711_ = lean_ctor_get(v_v_1710_, 1);
lean_inc(v_snd_1711_);
v___x_1712_ = lean_unsigned_to_nat(0u);
v_bs_x27_1713_ = lean_array_uset(v_bs_1708_, v_i_1707_, v___x_1712_);
v___x_1714_ = ((size_t)1ULL);
v___x_1715_ = lean_usize_add(v_i_1707_, v___x_1714_);
v___x_1716_ = lean_array_uset(v_bs_x27_1713_, v_i_1707_, v_snd_1711_);
v_i_1707_ = v___x_1715_;
v_bs_1708_ = v___x_1716_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0___boxed(lean_object* v_sz_1718_, lean_object* v_i_1719_, lean_object* v_bs_1720_){
_start:
{
size_t v_sz_boxed_1721_; size_t v_i_boxed_1722_; lean_object* v_res_1723_; 
v_sz_boxed_1721_ = lean_unbox_usize(v_sz_1718_);
lean_dec(v_sz_1718_);
v_i_boxed_1722_ = lean_unbox_usize(v_i_1719_);
lean_dec(v_i_1719_);
v_res_1723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_boxed_1721_, v_i_boxed_1722_, v_bs_1720_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_values(lean_object* v_query_1724_){
_start:
{
size_t v_sz_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
v_sz_1725_ = lean_array_size(v_query_1724_);
v___x_1726_ = ((size_t)0ULL);
v___x_1727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_1725_, v___x_1726_, v_query_1724_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray(lean_object* v_query_1728_){
_start:
{
lean_inc_ref(v_query_1728_);
return v_query_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray___boxed(lean_object* v_query_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Std_Http_URI_Query_toArray(v_query_1729_);
lean_dec_ref(v_query_1729_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object* v_key_1732_, lean_object* v_value_1733_){
_start:
{
if (lean_obj_tag(v_value_1733_) == 0)
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_string_from_utf8_unchecked(v_key_1732_);
return v___x_1734_;
}
else
{
lean_object* v_val_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_val_1735_ = lean_ctor_get(v_value_1733_, 0);
lean_inc(v_val_1735_);
lean_dec_ref_known(v_value_1733_, 1);
v___x_1736_ = lean_string_from_utf8_unchecked(v_key_1732_);
v___x_1737_ = ((lean_object*)(l_Std_Http_URI_Query_formatQueryParam___closed__0));
v___x_1738_ = lean_string_append(v___x_1736_, v___x_1737_);
v___x_1739_ = lean_string_from_utf8_unchecked(v_val_1735_);
v___x_1740_ = lean_string_append(v___x_1738_, v___x_1739_);
lean_dec_ref(v___x_1739_);
return v___x_1740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(lean_object* v_key_1744_, lean_object* v_as_1745_, size_t v_sz_1746_, size_t v_i_1747_, lean_object* v_b_1748_){
_start:
{
uint8_t v___x_1749_; 
v___x_1749_ = lean_usize_dec_lt(v_i_1747_, v_sz_1746_);
if (v___x_1749_ == 0)
{
lean_inc_ref(v_b_1748_);
return v_b_1748_;
}
else
{
lean_object* v_a_1750_; lean_object* v_fst_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; 
v_a_1750_ = lean_array_uget_borrowed(v_as_1745_, v_i_1747_);
v_fst_1751_ = lean_ctor_get(v_a_1750_, 0);
v___x_1752_ = lean_box(0);
v___x_1753_ = lean_sarray_dec_eq(v_fst_1751_, v_key_1744_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; size_t v___x_1755_; size_t v___x_1756_; 
v___x_1754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v___x_1755_ = ((size_t)1ULL);
v___x_1756_ = lean_usize_add(v_i_1747_, v___x_1755_);
v_i_1747_ = v___x_1756_;
v_b_1748_ = v___x_1754_;
goto _start;
}
else
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_inc(v_a_1750_);
v___x_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1758_, 0, v_a_1750_);
v___x_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
v___x_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
lean_ctor_set(v___x_1760_, 1, v___x_1752_);
return v___x_1760_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___boxed(lean_object* v_key_1761_, lean_object* v_as_1762_, lean_object* v_sz_1763_, lean_object* v_i_1764_, lean_object* v_b_1765_){
_start:
{
size_t v_sz_boxed_1766_; size_t v_i_boxed_1767_; lean_object* v_res_1768_; 
v_sz_boxed_1766_ = lean_unbox_usize(v_sz_1763_);
lean_dec(v_sz_1763_);
v_i_boxed_1767_ = lean_unbox_usize(v_i_1764_);
lean_dec(v_i_1764_);
v_res_1768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1761_, v_as_1762_, v_sz_boxed_1766_, v_i_boxed_1767_, v_b_1765_);
lean_dec_ref(v_b_1765_);
lean_dec_ref(v_as_1762_);
lean_dec_ref(v_key_1761_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f(lean_object* v_query_1769_, lean_object* v_key_1770_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; size_t v_sz_1773_; size_t v___x_1774_; lean_object* v___x_1775_; lean_object* v_fst_1776_; 
v___x_1771_ = lean_box(0);
v___x_1772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v_sz_1773_ = lean_array_size(v_query_1769_);
v___x_1774_ = ((size_t)0ULL);
v___x_1775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1770_, v_query_1769_, v_sz_1773_, v___x_1774_, v___x_1772_);
v_fst_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_fst_1776_);
lean_dec_ref(v___x_1775_);
if (lean_obj_tag(v_fst_1776_) == 0)
{
return v___x_1771_;
}
else
{
lean_object* v_val_1777_; 
v_val_1777_ = lean_ctor_get(v_fst_1776_, 0);
lean_inc(v_val_1777_);
lean_dec_ref_known(v_fst_1776_, 1);
if (lean_obj_tag(v_val_1777_) == 0)
{
return v___x_1771_;
}
else
{
lean_object* v_val_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1786_; 
v_val_1778_ = lean_ctor_get(v_val_1777_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_val_1777_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1780_ = v_val_1777_;
v_isShared_1781_ = v_isSharedCheck_1786_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_val_1778_);
lean_dec(v_val_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1786_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v_snd_1782_; lean_object* v___x_1784_; 
v_snd_1782_ = lean_ctor_get(v_val_1778_, 1);
lean_inc(v_snd_1782_);
lean_dec(v_val_1778_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v_snd_1782_);
v___x_1784_ = v___x_1780_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_snd_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f___boxed(lean_object* v_query_1787_, lean_object* v_key_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1787_, v_key_1788_);
lean_dec_ref(v_key_1788_);
lean_dec_ref(v_query_1787_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f(lean_object* v_query_1790_, lean_object* v_key_1791_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1791_);
v___x_1793_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1790_, v___x_1792_);
lean_dec_ref(v___x_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f___boxed(lean_object* v_query_1794_, lean_object* v_key_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Std_Http_URI_Query_find_x3f(v_query_1794_, v_key_1795_);
lean_dec_ref(v_key_1795_);
lean_dec_ref(v_query_1794_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(lean_object* v_key_1797_, lean_object* v_as_1798_, size_t v_i_1799_, size_t v_stop_1800_, lean_object* v_b_1801_){
_start:
{
lean_object* v___y_1803_; uint8_t v___x_1807_; 
v___x_1807_ = lean_usize_dec_eq(v_i_1799_, v_stop_1800_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v_fst_1809_; lean_object* v_snd_1810_; uint8_t v___x_1811_; 
v___x_1808_ = lean_array_uget_borrowed(v_as_1798_, v_i_1799_);
v_fst_1809_ = lean_ctor_get(v___x_1808_, 0);
v_snd_1810_ = lean_ctor_get(v___x_1808_, 1);
v___x_1811_ = lean_sarray_dec_eq(v_fst_1809_, v_key_1797_);
if (v___x_1811_ == 0)
{
v___y_1803_ = v_b_1801_;
goto v___jp_1802_;
}
else
{
lean_object* v___x_1812_; 
lean_inc(v_snd_1810_);
v___x_1812_ = lean_array_push(v_b_1801_, v_snd_1810_);
v___y_1803_ = v___x_1812_;
goto v___jp_1802_;
}
}
else
{
return v_b_1801_;
}
v___jp_1802_:
{
size_t v___x_1804_; size_t v___x_1805_; 
v___x_1804_ = ((size_t)1ULL);
v___x_1805_ = lean_usize_add(v_i_1799_, v___x_1804_);
v_i_1799_ = v___x_1805_;
v_b_1801_ = v___y_1803_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0___boxed(lean_object* v_key_1813_, lean_object* v_as_1814_, lean_object* v_i_1815_, lean_object* v_stop_1816_, lean_object* v_b_1817_){
_start:
{
size_t v_i_boxed_1818_; size_t v_stop_boxed_1819_; lean_object* v_res_1820_; 
v_i_boxed_1818_ = lean_unbox_usize(v_i_1815_);
lean_dec(v_i_1815_);
v_stop_boxed_1819_ = lean_unbox_usize(v_stop_1816_);
lean_dec(v_stop_1816_);
v_res_1820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1813_, v_as_1814_, v_i_boxed_1818_, v_stop_boxed_1819_, v_b_1817_);
lean_dec_ref(v_as_1814_);
lean_dec_ref(v_key_1813_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(lean_object* v_key_1823_, lean_object* v_as_1824_, lean_object* v_start_1825_, lean_object* v_stop_1826_){
_start:
{
lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1827_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_1828_ = lean_nat_dec_lt(v_start_1825_, v_stop_1826_);
if (v___x_1828_ == 0)
{
return v___x_1827_;
}
else
{
lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1829_ = lean_array_get_size(v_as_1824_);
v___x_1830_ = lean_nat_dec_le(v_stop_1826_, v___x_1829_);
if (v___x_1830_ == 0)
{
uint8_t v___x_1831_; 
v___x_1831_ = lean_nat_dec_lt(v_start_1825_, v___x_1829_);
if (v___x_1831_ == 0)
{
return v___x_1827_;
}
else
{
size_t v___x_1832_; size_t v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = lean_usize_of_nat(v_start_1825_);
v___x_1833_ = lean_usize_of_nat(v___x_1829_);
v___x_1834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1823_, v_as_1824_, v___x_1832_, v___x_1833_, v___x_1827_);
return v___x_1834_;
}
}
else
{
size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = lean_usize_of_nat(v_start_1825_);
v___x_1836_ = lean_usize_of_nat(v_stop_1826_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1823_, v_as_1824_, v___x_1835_, v___x_1836_, v___x_1827_);
return v___x_1837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___boxed(lean_object* v_key_1838_, lean_object* v_as_1839_, lean_object* v_start_1840_, lean_object* v_stop_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1838_, v_as_1839_, v_start_1840_, v_stop_1841_);
lean_dec(v_stop_1841_);
lean_dec(v_start_1840_);
lean_dec_ref(v_as_1839_);
lean_dec_ref(v_key_1838_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded(lean_object* v_query_1843_, lean_object* v_key_1844_){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = lean_unsigned_to_nat(0u);
v___x_1846_ = lean_array_get_size(v_query_1843_);
v___x_1847_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1844_, v_query_1843_, v___x_1845_, v___x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded___boxed(lean_object* v_query_1848_, lean_object* v_key_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1848_, v_key_1849_);
lean_dec_ref(v_key_1849_);
lean_dec_ref(v_query_1848_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll(lean_object* v_query_1851_, lean_object* v_key_1852_){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1852_);
v___x_1854_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1851_, v___x_1853_);
lean_dec_ref(v___x_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll___boxed(lean_object* v_query_1855_, lean_object* v_key_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Std_Http_URI_Query_findAll(v_query_1855_, v_key_1856_);
lean_dec_ref(v_key_1856_);
lean_dec_ref(v_query_1855_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert(lean_object* v_query_1858_, lean_object* v_key_1859_, lean_object* v_value_1860_){
_start:
{
lean_object* v_encodedKey_1861_; lean_object* v_encodedValue_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v_encodedKey_1861_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1859_);
v_encodedValue_1862_ = l_Std_Http_URI_EncodedQueryParam_encode(v_value_1860_);
v___x_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1863_, 0, v_encodedValue_1862_);
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v_encodedKey_1861_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_array_push(v_query_1858_, v___x_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert___boxed(lean_object* v_query_1866_, lean_object* v_key_1867_, lean_object* v_value_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Std_Http_URI_Query_insert(v_query_1866_, v_key_1867_, v_value_1868_);
lean_dec_ref(v_value_1868_);
lean_dec_ref(v_key_1867_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object* v_query_1870_, lean_object* v_key_1871_, lean_object* v_value_1872_){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1873_, 0, v_key_1871_);
lean_ctor_set(v___x_1873_, 1, v_value_1872_);
v___x_1874_ = lean_array_push(v_query_1870_, v___x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_ofList(lean_object* v_pairs_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_array_mk(v_pairs_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(lean_object* v_key_1880_, lean_object* v_as_1881_, size_t v_i_1882_, size_t v_stop_1883_){
_start:
{
uint8_t v___x_1884_; 
v___x_1884_ = lean_usize_dec_eq(v_i_1882_, v_stop_1883_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; lean_object* v_fst_1886_; uint8_t v___x_1887_; 
v___x_1885_ = lean_array_uget_borrowed(v_as_1881_, v_i_1882_);
v_fst_1886_ = lean_ctor_get(v___x_1885_, 0);
v___x_1887_ = lean_sarray_dec_eq(v_fst_1886_, v_key_1880_);
if (v___x_1887_ == 0)
{
size_t v___x_1888_; size_t v___x_1889_; 
v___x_1888_ = ((size_t)1ULL);
v___x_1889_ = lean_usize_add(v_i_1882_, v___x_1888_);
v_i_1882_ = v___x_1889_;
goto _start;
}
else
{
return v___x_1887_;
}
}
else
{
uint8_t v___x_1891_; 
v___x_1891_ = 0;
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(lean_object* v_key_1892_, lean_object* v_as_1893_, lean_object* v_i_1894_, lean_object* v_stop_1895_){
_start:
{
size_t v_i_boxed_1896_; size_t v_stop_boxed_1897_; uint8_t v_res_1898_; lean_object* v_r_1899_; 
v_i_boxed_1896_ = lean_unbox_usize(v_i_1894_);
lean_dec(v_i_1894_);
v_stop_boxed_1897_ = lean_unbox_usize(v_stop_1895_);
lean_dec(v_stop_1895_);
v_res_1898_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1892_, v_as_1893_, v_i_boxed_1896_, v_stop_boxed_1897_);
lean_dec_ref(v_as_1893_);
lean_dec_ref(v_key_1892_);
v_r_1899_ = lean_box(v_res_1898_);
return v_r_1899_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_containsEncoded(lean_object* v_query_1900_, lean_object* v_key_1901_){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1902_ = lean_unsigned_to_nat(0u);
v___x_1903_ = lean_array_get_size(v_query_1900_);
v___x_1904_ = lean_nat_dec_lt(v___x_1902_, v___x_1903_);
if (v___x_1904_ == 0)
{
return v___x_1904_;
}
else
{
if (v___x_1904_ == 0)
{
return v___x_1904_;
}
else
{
size_t v___x_1905_; size_t v___x_1906_; uint8_t v___x_1907_; 
v___x_1905_ = ((size_t)0ULL);
v___x_1906_ = lean_usize_of_nat(v___x_1903_);
v___x_1907_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1901_, v_query_1900_, v___x_1905_, v___x_1906_);
return v___x_1907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_containsEncoded___boxed(lean_object* v_query_1908_, lean_object* v_key_1909_){
_start:
{
uint8_t v_res_1910_; lean_object* v_r_1911_; 
v_res_1910_ = l_Std_Http_URI_Query_containsEncoded(v_query_1908_, v_key_1909_);
lean_dec_ref(v_key_1909_);
lean_dec_ref(v_query_1908_);
v_r_1911_ = lean_box(v_res_1910_);
return v_r_1911_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_contains(lean_object* v_query_1912_, lean_object* v_key_1913_){
_start:
{
lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1914_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1913_);
v___x_1915_ = l_Std_Http_URI_Query_containsEncoded(v_query_1912_, v___x_1914_);
lean_dec_ref(v___x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_contains___boxed(lean_object* v_query_1916_, lean_object* v_key_1917_){
_start:
{
uint8_t v_res_1918_; lean_object* v_r_1919_; 
v_res_1918_ = l_Std_Http_URI_Query_contains(v_query_1916_, v_key_1917_);
lean_dec_ref(v_key_1917_);
lean_dec_ref(v_query_1916_);
v_r_1919_ = lean_box(v_res_1918_);
return v_r_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(lean_object* v_key_1920_, lean_object* v_as_1921_, size_t v_i_1922_, size_t v_stop_1923_, lean_object* v_b_1924_){
_start:
{
lean_object* v___y_1926_; uint8_t v___x_1930_; 
v___x_1930_ = lean_usize_dec_eq(v_i_1922_, v_stop_1923_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v_fst_1934_; uint8_t v___x_1935_; 
v___x_1931_ = lean_array_uget_borrowed(v_as_1921_, v_i_1922_);
v_fst_1934_ = lean_ctor_get(v___x_1931_, 0);
v___x_1935_ = lean_sarray_dec_eq(v_fst_1934_, v_key_1920_);
if (v___x_1935_ == 0)
{
goto v___jp_1932_;
}
else
{
if (v___x_1930_ == 0)
{
v___y_1926_ = v_b_1924_;
goto v___jp_1925_;
}
else
{
goto v___jp_1932_;
}
}
v___jp_1932_:
{
lean_object* v___x_1933_; 
lean_inc(v___x_1931_);
v___x_1933_ = lean_array_push(v_b_1924_, v___x_1931_);
v___y_1926_ = v___x_1933_;
goto v___jp_1925_;
}
}
else
{
return v_b_1924_;
}
v___jp_1925_:
{
size_t v___x_1927_; size_t v___x_1928_; 
v___x_1927_ = ((size_t)1ULL);
v___x_1928_ = lean_usize_add(v_i_1922_, v___x_1927_);
v_i_1922_ = v___x_1928_;
v_b_1924_ = v___y_1926_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(lean_object* v_key_1936_, lean_object* v_as_1937_, lean_object* v_i_1938_, lean_object* v_stop_1939_, lean_object* v_b_1940_){
_start:
{
size_t v_i_boxed_1941_; size_t v_stop_boxed_1942_; lean_object* v_res_1943_; 
v_i_boxed_1941_ = lean_unbox_usize(v_i_1938_);
lean_dec(v_i_1938_);
v_stop_boxed_1942_ = lean_unbox_usize(v_stop_1939_);
lean_dec(v_stop_1939_);
v_res_1943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1936_, v_as_1937_, v_i_boxed_1941_, v_stop_boxed_1942_, v_b_1940_);
lean_dec_ref(v_as_1937_);
lean_dec_ref(v_key_1936_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded(lean_object* v_query_1944_, lean_object* v_key_1945_){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
v___x_1946_ = lean_unsigned_to_nat(0u);
v___x_1947_ = lean_array_get_size(v_query_1944_);
v___x_1948_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_1949_ = lean_nat_dec_lt(v___x_1946_, v___x_1947_);
if (v___x_1949_ == 0)
{
return v___x_1948_;
}
else
{
uint8_t v___x_1950_; 
v___x_1950_ = lean_nat_dec_le(v___x_1947_, v___x_1947_);
if (v___x_1950_ == 0)
{
if (v___x_1949_ == 0)
{
return v___x_1948_;
}
else
{
size_t v___x_1951_; size_t v___x_1952_; lean_object* v___x_1953_; 
v___x_1951_ = ((size_t)0ULL);
v___x_1952_ = lean_usize_of_nat(v___x_1947_);
v___x_1953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1945_, v_query_1944_, v___x_1951_, v___x_1952_, v___x_1948_);
return v___x_1953_;
}
}
else
{
size_t v___x_1954_; size_t v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = ((size_t)0ULL);
v___x_1955_ = lean_usize_of_nat(v___x_1947_);
v___x_1956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1945_, v_query_1944_, v___x_1954_, v___x_1955_, v___x_1948_);
return v___x_1956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded___boxed(lean_object* v_query_1957_, lean_object* v_key_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Std_Http_URI_Query_eraseEncoded(v_query_1957_, v_key_1958_);
lean_dec_ref(v_key_1958_);
lean_dec_ref(v_query_1957_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase(lean_object* v_query_1960_, lean_object* v_key_1961_){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1961_);
v___x_1963_ = l_Std_Http_URI_Query_eraseEncoded(v_query_1960_, v___x_1962_);
lean_dec_ref(v___x_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase___boxed(lean_object* v_query_1964_, lean_object* v_key_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Std_Http_URI_Query_erase(v_query_1964_, v_key_1965_);
lean_dec_ref(v_key_1965_);
lean_dec_ref(v_query_1964_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get(lean_object* v_query_1969_, lean_object* v_key_1970_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Std_Http_URI_Query_find_x3f(v_query_1969_, v_key_1970_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v___x_1972_; 
v___x_1972_ = lean_box(0);
return v___x_1972_;
}
else
{
lean_object* v_val_1973_; 
v_val_1973_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_val_1973_);
lean_dec_ref_known(v___x_1971_, 1);
if (lean_obj_tag(v_val_1973_) == 0)
{
lean_object* v___x_1974_; 
v___x_1974_ = ((lean_object*)(l_Std_Http_URI_Query_get___closed__0));
return v___x_1974_;
}
else
{
lean_object* v_val_1975_; lean_object* v___x_1976_; 
v_val_1975_ = lean_ctor_get(v_val_1973_, 0);
lean_inc(v_val_1975_);
lean_dec_ref_known(v_val_1973_, 1);
v___x_1976_ = l_Std_Http_URI_EncodedQueryParam_decode(v_val_1975_);
lean_dec(v_val_1975_);
return v___x_1976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get___boxed(lean_object* v_query_1977_, lean_object* v_key_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Std_Http_URI_Query_get(v_query_1977_, v_key_1978_);
lean_dec_ref(v_key_1978_);
lean_dec_ref(v_query_1977_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD(lean_object* v_query_1980_, lean_object* v_key_1981_, lean_object* v_default_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Std_Http_URI_Query_get(v_query_1980_, v_key_1981_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_inc_ref(v_default_1982_);
return v_default_1982_;
}
else
{
lean_object* v_val_1984_; 
v_val_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_val_1984_);
lean_dec_ref_known(v___x_1983_, 1);
return v_val_1984_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD___boxed(lean_object* v_query_1985_, lean_object* v_key_1986_, lean_object* v_default_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Std_Http_URI_Query_getD(v_query_1985_, v_key_1986_, v_default_1987_);
lean_dec_ref(v_default_1987_);
lean_dec_ref(v_key_1986_);
lean_dec_ref(v_query_1985_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set(lean_object* v_query_1989_, lean_object* v_key_1990_, lean_object* v_value_1991_){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = l_Std_Http_URI_Query_erase(v_query_1989_, v_key_1990_);
v___x_1993_ = l_Std_Http_URI_Query_insert(v___x_1992_, v_key_1990_, v_value_1991_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set___boxed(lean_object* v_query_1994_, lean_object* v_key_1995_, lean_object* v_value_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Std_Http_URI_Query_set(v_query_1994_, v_key_1995_, v_value_1996_);
lean_dec_ref(v_value_1996_);
lean_dec_ref(v_key_1995_);
lean_dec_ref(v_query_1994_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(size_t v_sz_1998_, size_t v_i_1999_, lean_object* v_bs_2000_){
_start:
{
uint8_t v___x_2001_; 
v___x_2001_ = lean_usize_dec_lt(v_i_1999_, v_sz_1998_);
if (v___x_2001_ == 0)
{
return v_bs_2000_;
}
else
{
lean_object* v_v_2002_; lean_object* v_fst_2003_; lean_object* v_snd_2004_; lean_object* v___x_2005_; lean_object* v_bs_x27_2006_; lean_object* v___x_2007_; size_t v___x_2008_; size_t v___x_2009_; lean_object* v___x_2010_; 
v_v_2002_ = lean_array_uget_borrowed(v_bs_2000_, v_i_1999_);
v_fst_2003_ = lean_ctor_get(v_v_2002_, 0);
lean_inc(v_fst_2003_);
v_snd_2004_ = lean_ctor_get(v_v_2002_, 1);
lean_inc(v_snd_2004_);
v___x_2005_ = lean_unsigned_to_nat(0u);
v_bs_x27_2006_ = lean_array_uset(v_bs_2000_, v_i_1999_, v___x_2005_);
v___x_2007_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2003_, v_snd_2004_);
v___x_2008_ = ((size_t)1ULL);
v___x_2009_ = lean_usize_add(v_i_1999_, v___x_2008_);
v___x_2010_ = lean_array_uset(v_bs_x27_2006_, v_i_1999_, v___x_2007_);
v_i_1999_ = v___x_2009_;
v_bs_2000_ = v___x_2010_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0___boxed(lean_object* v_sz_2012_, lean_object* v_i_2013_, lean_object* v_bs_2014_){
_start:
{
size_t v_sz_boxed_2015_; size_t v_i_boxed_2016_; lean_object* v_res_2017_; 
v_sz_boxed_2015_ = lean_unbox_usize(v_sz_2012_);
lean_dec(v_sz_2012_);
v_i_boxed_2016_ = lean_unbox_usize(v_i_2013_);
lean_dec(v_i_2013_);
v_res_2017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_boxed_2015_, v_i_boxed_2016_, v_bs_2014_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toRawString(lean_object* v_query_2019_){
_start:
{
size_t v_sz_2020_; size_t v___x_2021_; lean_object* v_params_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v_sz_2020_ = lean_array_size(v_query_2019_);
v___x_2021_ = ((size_t)0ULL);
v_params_2022_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_2020_, v___x_2021_, v_query_2019_);
v___x_2023_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2024_ = lean_array_to_list(v_params_2022_);
v___x_2025_ = l_String_intercalate(v___x_2023_, v___x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0(lean_object* v_x_2027_){
_start:
{
lean_object* v_fst_2028_; lean_object* v_snd_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v_fst_2028_ = lean_ctor_get(v_x_2027_, 0);
v_snd_2029_ = lean_ctor_get(v_x_2027_, 1);
v___x_2030_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
v___x_2031_ = l_Std_Http_URI_Query_insert(v___x_2030_, v_fst_2028_, v_snd_2029_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0___boxed(lean_object* v_x_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Std_Http_URI_Query_instSingletonProdString___lam__0(v_x_2032_);
lean_dec_ref(v_x_2032_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0(lean_object* v_x_2036_, lean_object* v_q_2037_){
_start:
{
lean_object* v_fst_2038_; lean_object* v_snd_2039_; lean_object* v___x_2040_; 
v_fst_2038_ = lean_ctor_get(v_x_2036_, 0);
v_snd_2039_ = lean_ctor_get(v_x_2036_, 1);
v___x_2040_ = l_Std_Http_URI_Query_insert(v_q_2037_, v_fst_2038_, v_snd_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0___boxed(lean_object* v_x_2041_, lean_object* v_q_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Std_Http_URI_Query_instInsertProdString___lam__0(v_x_2041_, v_q_2042_);
lean_dec_ref(v_x_2041_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__0(lean_object* v_x_2046_){
_start:
{
lean_object* v_fst_2047_; lean_object* v_snd_2048_; lean_object* v___x_2049_; 
v_fst_2047_ = lean_ctor_get(v_x_2046_, 0);
lean_inc(v_fst_2047_);
v_snd_2048_ = lean_ctor_get(v_x_2046_, 1);
lean_inc(v_snd_2048_);
lean_dec_ref(v_x_2046_);
v___x_2049_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2047_, v_snd_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__1(lean_object* v___f_2051_, lean_object* v_q_2052_){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2053_ = lean_array_get_size(v_q_2052_);
v___x_2054_ = lean_unsigned_to_nat(0u);
v___x_2055_ = lean_nat_dec_eq(v___x_2053_, v___x_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v_encodedParams_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2056_ = lean_array_to_list(v_q_2052_);
v___x_2057_ = lean_box(0);
v_encodedParams_2058_ = l_List_mapTR_loop___redArg(v___f_2051_, v___x_2056_, v___x_2057_);
v___x_2059_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2060_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2061_ = l_String_intercalate(v___x_2060_, v_encodedParams_2058_);
v___x_2062_ = lean_string_append(v___x_2059_, v___x_2061_);
lean_dec_ref(v___x_2061_);
return v___x_2062_;
}
else
{
lean_object* v___x_2063_; 
lean_dec_ref(v_q_2052_);
lean_dec_ref(v___f_2051_);
v___x_2063_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2063_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(lean_object* v_a_2068_, lean_object* v_a_2069_){
_start:
{
if (lean_obj_tag(v_a_2068_) == 0)
{
lean_object* v___x_2070_; 
v___x_2070_ = l_List_reverse___redArg(v_a_2069_);
return v___x_2070_;
}
else
{
lean_object* v_head_2071_; lean_object* v_tail_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2083_; 
v_head_2071_ = lean_ctor_get(v_a_2068_, 0);
v_tail_2072_ = lean_ctor_get(v_a_2068_, 1);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_a_2068_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2074_ = v_a_2068_;
v_isShared_2075_ = v_isSharedCheck_2083_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_tail_2072_);
lean_inc(v_head_2071_);
lean_dec(v_a_2068_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2083_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v_fst_2076_; lean_object* v_snd_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
v_fst_2076_ = lean_ctor_get(v_head_2071_, 0);
lean_inc(v_fst_2076_);
v_snd_2077_ = lean_ctor_get(v_head_2071_, 1);
lean_inc(v_snd_2077_);
lean_dec(v_head_2071_);
v___x_2078_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2076_, v_snd_2077_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 1, v_a_2069_);
lean_ctor_set(v___x_2074_, 0, v___x_2078_);
v___x_2080_ = v___x_2074_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_a_2069_);
v___x_2080_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
v_a_2068_ = v_tail_2072_;
v_a_2069_ = v___x_2080_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatOption(lean_object* v_x_2084_){
_start:
{
if (lean_obj_tag(v_x_2084_) == 0)
{
lean_object* v___x_2085_; 
v___x_2085_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2085_;
}
else
{
lean_object* v_val_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v_val_2086_ = lean_ctor_get(v_x_2084_, 0);
lean_inc(v_val_2086_);
lean_dec_ref_known(v_x_2084_, 1);
v___x_2087_ = lean_array_get_size(v_val_2086_);
v___x_2088_ = lean_unsigned_to_nat(0u);
v___x_2089_ = lean_nat_dec_eq(v___x_2087_, v___x_2088_);
if (v___x_2089_ == 0)
{
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v_encodedParams_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2090_ = lean_array_to_list(v_val_2086_);
v___x_2091_ = lean_box(0);
v_encodedParams_2092_ = l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(v___x_2090_, v___x_2091_);
v___x_2093_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2094_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2095_ = l_String_intercalate(v___x_2094_, v_encodedParams_2092_);
v___x_2096_ = lean_string_append(v___x_2093_, v___x_2095_);
lean_dec_ref(v___x_2095_);
return v___x_2096_;
}
else
{
lean_object* v___x_2097_; 
lean_dec(v_val_2086_);
v___x_2097_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2097_;
}
}
else
{
lean_object* v___x_2098_; 
lean_dec(v_val_2086_);
v___x_2098_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
return v___x_2098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(lean_object* v_x_2099_, lean_object* v_x_2100_){
_start:
{
if (lean_obj_tag(v_x_2099_) == 0)
{
lean_object* v___x_2101_; 
v___x_2101_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2101_;
}
else
{
lean_object* v_val_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v_val_2102_ = lean_ctor_get(v_x_2099_, 0);
lean_inc(v_val_2102_);
lean_dec_ref_known(v_x_2099_, 1);
v___x_2103_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2104_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_val_2102_);
v___x_2105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2103_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = l_Repr_addAppParen(v___x_2105_, v_x_2100_);
return v___x_2106_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(lean_object* v_x_2107_, lean_object* v_x_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_x_2107_, v_x_2108_);
lean_dec(v_x_2108_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object* v_x_2110_, lean_object* v_x_2111_){
_start:
{
if (lean_obj_tag(v_x_2110_) == 0)
{
lean_object* v___x_2112_; 
v___x_2112_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2112_;
}
else
{
lean_object* v_val_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v_val_2113_ = lean_ctor_get(v_x_2110_, 0);
lean_inc(v_val_2113_);
lean_dec_ref_known(v_x_2110_, 1);
v___x_2114_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2115_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_val_2113_);
v___x_2116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = l_Repr_addAppParen(v___x_2116_, v_x_2111_);
return v___x_2117_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1___boxed(lean_object* v_x_2118_, lean_object* v_x_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_x_2118_, v_x_2119_);
lean_dec(v_x_2119_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(lean_object* v_x_2121_, lean_object* v_x_2122_){
_start:
{
if (lean_obj_tag(v_x_2121_) == 0)
{
lean_object* v___x_2123_; 
v___x_2123_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2123_;
}
else
{
lean_object* v_val_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2135_; 
v_val_2124_ = lean_ctor_get(v_x_2121_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v_x_2121_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2126_ = v_x_2121_;
v_isShared_2127_ = v_isSharedCheck_2135_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_val_2124_);
lean_dec(v_x_2121_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2135_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2128_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2129_ = l_String_quote(v_val_2124_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set_tag(v___x_2126_, 3);
lean_ctor_set(v___x_2126_, 0, v___x_2129_);
v___x_2131_ = v___x_2126_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2128_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = l_Repr_addAppParen(v___x_2132_, v_x_2122_);
return v___x_2133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2___boxed(lean_object* v_x_2136_, lean_object* v_x_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_x_2136_, v_x_2137_);
lean_dec(v_x_2137_);
return v_res_2138_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = lean_unsigned_to_nat(10u);
v___x_2149_ = lean_nat_to_int(v___x_2148_);
return v___x_2149_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = lean_unsigned_to_nat(13u);
v___x_2154_ = lean_nat_to_int(v___x_2153_);
return v___x_2154_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = lean_unsigned_to_nat(9u);
v___x_2162_ = lean_nat_to_int(v___x_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___redArg(lean_object* v_x_2166_){
_start:
{
lean_object* v_scheme_2167_; lean_object* v_authority_2168_; lean_object* v_path_2169_; lean_object* v_query_2170_; lean_object* v_fragment_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v_scheme_2167_ = lean_ctor_get(v_x_2166_, 0);
lean_inc_ref(v_scheme_2167_);
v_authority_2168_ = lean_ctor_get(v_x_2166_, 1);
lean_inc(v_authority_2168_);
v_path_2169_ = lean_ctor_get(v_x_2166_, 2);
lean_inc_ref(v_path_2169_);
v_query_2170_ = lean_ctor_get(v_x_2166_, 3);
lean_inc(v_query_2170_);
v_fragment_2171_ = lean_ctor_get(v_x_2166_, 4);
lean_inc(v_fragment_2171_);
lean_dec_ref(v_x_2166_);
v___x_2172_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2173_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2174_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2175_ = l_String_quote(v_scheme_2167_);
v___x_2176_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
v___x_2177_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2174_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = 0;
v___x_2179_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2179_, 0, v___x_2177_);
lean_ctor_set_uint8(v___x_2179_, sizeof(void*)*1, v___x_2178_);
v___x_2180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2173_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2180_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
v___x_2183_ = lean_box(1);
v___x_2184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2182_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
v___x_2185_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__6));
v___x_2186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2184_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___x_2187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
lean_ctor_set(v___x_2187_, 1, v___x_2172_);
v___x_2188_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_2168_, v___x_2189_);
v___x_2191_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2188_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
lean_ctor_set_uint8(v___x_2192_, sizeof(void*)*1, v___x_2178_);
v___x_2193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2187_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
lean_ctor_set(v___x_2194_, 1, v___x_2181_);
v___x_2195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
lean_ctor_set(v___x_2195_, 1, v___x_2183_);
v___x_2196_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_2197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
lean_ctor_set(v___x_2198_, 1, v___x_2172_);
v___x_2199_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2200_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_2169_);
v___x_2201_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2199_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set_uint8(v___x_2202_, sizeof(void*)*1, v___x_2178_);
v___x_2203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2198_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set(v___x_2204_, 1, v___x_2181_);
v___x_2205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
lean_ctor_set(v___x_2205_, 1, v___x_2183_);
v___x_2206_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_2207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___x_2172_);
v___x_2209_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_2210_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_2170_, v___x_2189_);
v___x_2211_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2209_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set_uint8(v___x_2212_, sizeof(void*)*1, v___x_2178_);
v___x_2213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2208_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
lean_ctor_set(v___x_2214_, 1, v___x_2181_);
v___x_2215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
lean_ctor_set(v___x_2215_, 1, v___x_2183_);
v___x_2216_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_2217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2215_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
v___x_2218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set(v___x_2218_, 1, v___x_2172_);
v___x_2219_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_2220_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_2171_, v___x_2189_);
v___x_2221_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2219_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set_uint8(v___x_2222_, sizeof(void*)*1, v___x_2178_);
v___x_2223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2218_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
v___x_2224_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2225_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
lean_ctor_set(v___x_2226_, 1, v___x_2223_);
v___x_2227_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2226_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
v___x_2229_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2224_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
v___x_2230_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set_uint8(v___x_2230_, sizeof(void*)*1, v___x_2178_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr(lean_object* v_x_2231_, lean_object* v_prec_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Std_Http_instReprURI_repr___redArg(v_x_2231_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___boxed(lean_object* v_x_2234_, lean_object* v_prec_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Std_Http_instReprURI_repr(v_x_2234_, v_prec_2235_);
lean_dec(v_prec_2235_);
return v_res_2236_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object* v_x_2245_, lean_object* v_x_2246_){
_start:
{
if (lean_obj_tag(v_x_2245_) == 0)
{
if (lean_obj_tag(v_x_2246_) == 0)
{
uint8_t v___x_2247_; 
v___x_2247_ = 1;
return v___x_2247_;
}
else
{
uint8_t v___x_2248_; 
v___x_2248_ = 0;
return v___x_2248_;
}
}
else
{
if (lean_obj_tag(v_x_2246_) == 0)
{
uint8_t v___x_2249_; 
v___x_2249_ = 0;
return v___x_2249_;
}
else
{
lean_object* v_val_2250_; lean_object* v_val_2251_; uint8_t v___x_2252_; 
v_val_2250_ = lean_ctor_get(v_x_2245_, 0);
v_val_2251_ = lean_ctor_get(v_x_2246_, 0);
v___x_2252_ = l_Std_Http_URI_instBEqAuthority_beq(v_val_2250_, v_val_2251_);
return v___x_2252_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object* v_x_2253_, lean_object* v_x_2254_){
_start:
{
uint8_t v_res_2255_; lean_object* v_r_2256_; 
v_res_2255_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_x_2253_, v_x_2254_);
lean_dec(v_x_2254_);
lean_dec(v_x_2253_);
v_r_2256_ = lean_box(v_res_2255_);
return v_r_2256_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object* v_x_2257_, lean_object* v_x_2258_){
_start:
{
if (lean_obj_tag(v_x_2257_) == 0)
{
if (lean_obj_tag(v_x_2258_) == 0)
{
uint8_t v___x_2259_; 
v___x_2259_ = 1;
return v___x_2259_;
}
else
{
uint8_t v___x_2260_; 
v___x_2260_ = 0;
return v___x_2260_;
}
}
else
{
if (lean_obj_tag(v_x_2258_) == 0)
{
uint8_t v___x_2261_; 
v___x_2261_ = 0;
return v___x_2261_;
}
else
{
lean_object* v_val_2262_; lean_object* v_val_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; 
v_val_2262_ = lean_ctor_get(v_x_2257_, 0);
v_val_2263_ = lean_ctor_get(v_x_2258_, 0);
v___x_2264_ = lean_array_get_size(v_val_2262_);
v___x_2265_ = lean_array_get_size(v_val_2263_);
v___x_2266_ = lean_nat_dec_eq(v___x_2264_, v___x_2265_);
if (v___x_2266_ == 0)
{
return v___x_2266_;
}
else
{
uint8_t v___x_2267_; 
v___x_2267_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_val_2262_, v_val_2263_, v___x_2264_);
return v___x_2267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object* v_x_2268_, lean_object* v_x_2269_){
_start:
{
uint8_t v_res_2270_; lean_object* v_r_2271_; 
v_res_2270_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_x_2268_, v_x_2269_);
lean_dec(v_x_2269_);
lean_dec(v_x_2268_);
v_r_2271_ = lean_box(v_res_2270_);
return v_r_2271_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(lean_object* v_x_2272_, lean_object* v_x_2273_){
_start:
{
if (lean_obj_tag(v_x_2272_) == 0)
{
if (lean_obj_tag(v_x_2273_) == 0)
{
uint8_t v___x_2274_; 
v___x_2274_ = 1;
return v___x_2274_;
}
else
{
uint8_t v___x_2275_; 
v___x_2275_ = 0;
return v___x_2275_;
}
}
else
{
if (lean_obj_tag(v_x_2273_) == 0)
{
uint8_t v___x_2276_; 
v___x_2276_ = 0;
return v___x_2276_;
}
else
{
lean_object* v_val_2277_; lean_object* v_val_2278_; uint8_t v___x_2279_; 
v_val_2277_ = lean_ctor_get(v_x_2272_, 0);
v_val_2278_ = lean_ctor_get(v_x_2273_, 0);
v___x_2279_ = lean_string_dec_eq(v_val_2277_, v_val_2278_);
return v___x_2279_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2___boxed(lean_object* v_x_2280_, lean_object* v_x_2281_){
_start:
{
uint8_t v_res_2282_; lean_object* v_r_2283_; 
v_res_2282_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_x_2280_, v_x_2281_);
lean_dec(v_x_2281_);
lean_dec(v_x_2280_);
v_r_2283_ = lean_box(v_res_2282_);
return v_r_2283_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object* v_x_2284_, lean_object* v_x_2285_){
_start:
{
lean_object* v_scheme_2286_; lean_object* v_authority_2287_; lean_object* v_path_2288_; lean_object* v_query_2289_; lean_object* v_fragment_2290_; lean_object* v_scheme_2291_; lean_object* v_authority_2292_; lean_object* v_path_2293_; lean_object* v_query_2294_; lean_object* v_fragment_2295_; uint8_t v___x_2296_; 
v_scheme_2286_ = lean_ctor_get(v_x_2284_, 0);
v_authority_2287_ = lean_ctor_get(v_x_2284_, 1);
v_path_2288_ = lean_ctor_get(v_x_2284_, 2);
v_query_2289_ = lean_ctor_get(v_x_2284_, 3);
v_fragment_2290_ = lean_ctor_get(v_x_2284_, 4);
v_scheme_2291_ = lean_ctor_get(v_x_2285_, 0);
v_authority_2292_ = lean_ctor_get(v_x_2285_, 1);
v_path_2293_ = lean_ctor_get(v_x_2285_, 2);
v_query_2294_ = lean_ctor_get(v_x_2285_, 3);
v_fragment_2295_ = lean_ctor_get(v_x_2285_, 4);
v___x_2296_ = lean_string_dec_eq(v_scheme_2286_, v_scheme_2291_);
if (v___x_2296_ == 0)
{
return v___x_2296_;
}
else
{
uint8_t v___x_2297_; 
v___x_2297_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_2287_, v_authority_2292_);
if (v___x_2297_ == 0)
{
return v___x_2297_;
}
else
{
uint8_t v___x_2298_; 
v___x_2298_ = l_Std_Http_URI_instBEqPath_beq(v_path_2288_, v_path_2293_);
if (v___x_2298_ == 0)
{
return v___x_2298_;
}
else
{
uint8_t v___x_2299_; 
v___x_2299_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_2289_, v_query_2294_);
if (v___x_2299_ == 0)
{
return v___x_2299_;
}
else
{
uint8_t v___x_2300_; 
v___x_2300_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_2290_, v_fragment_2295_);
return v___x_2300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object* v_x_2301_, lean_object* v_x_2302_){
_start:
{
uint8_t v_res_2303_; lean_object* v_r_2304_; 
v_res_2303_ = l_Std_Http_instBEqURI_beq(v_x_2301_, v_x_2302_);
lean_dec_ref(v_x_2302_);
lean_dec_ref(v_x_2301_);
v_r_2304_ = lean_box(v_res_2303_);
return v_r_2304_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__1(lean_object* v___f_2309_, lean_object* v_uri_2310_){
_start:
{
lean_object* v_scheme_2311_; lean_object* v_authority_2312_; lean_object* v_path_2313_; lean_object* v_query_2314_; lean_object* v_fragment_2315_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2338_; 
v_scheme_2311_ = lean_ctor_get(v_uri_2310_, 0);
lean_inc_ref(v_scheme_2311_);
v_authority_2312_ = lean_ctor_get(v_uri_2310_, 1);
lean_inc(v_authority_2312_);
v_path_2313_ = lean_ctor_get(v_uri_2310_, 2);
lean_inc_ref(v_path_2313_);
v_query_2314_ = lean_ctor_get(v_uri_2310_, 3);
lean_inc(v_query_2314_);
v_fragment_2315_ = lean_ctor_get(v_uri_2310_, 4);
lean_inc(v_fragment_2315_);
lean_dec_ref(v_uri_2310_);
if (lean_obj_tag(v_authority_2312_) == 0)
{
lean_object* v___x_2349_; 
v___x_2349_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2338_ = v___x_2349_;
goto v___jp_2337_;
}
else
{
lean_object* v_val_2350_; lean_object* v_userInfo_2351_; lean_object* v_host_2352_; lean_object* v_port_2353_; lean_object* v___x_2354_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2373_; 
v_val_2350_ = lean_ctor_get(v_authority_2312_, 0);
lean_inc(v_val_2350_);
lean_dec_ref_known(v_authority_2312_, 1);
v_userInfo_2351_ = lean_ctor_get(v_val_2350_, 0);
lean_inc(v_userInfo_2351_);
v_host_2352_ = lean_ctor_get(v_val_2350_, 1);
lean_inc_ref(v_host_2352_);
v_port_2353_ = lean_ctor_get(v_val_2350_, 2);
lean_inc(v_port_2353_);
lean_dec(v_val_2350_);
v___x_2354_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_2351_) == 0)
{
lean_object* v___x_2383_; 
v___x_2383_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2373_ = v___x_2383_;
goto v___jp_2372_;
}
else
{
lean_object* v_val_2384_; lean_object* v_password_2385_; 
v_val_2384_ = lean_ctor_get(v_userInfo_2351_, 0);
lean_inc(v_val_2384_);
lean_dec_ref_known(v_userInfo_2351_, 1);
v_password_2385_ = lean_ctor_get(v_val_2384_, 1);
if (lean_obj_tag(v_password_2385_) == 0)
{
lean_object* v_username_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v_username_2386_ = lean_ctor_get(v_val_2384_, 0);
lean_inc_ref(v_username_2386_);
lean_dec(v_val_2384_);
v___x_2387_ = lean_string_from_utf8_unchecked(v_username_2386_);
v___x_2388_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2389_ = lean_string_append(v___x_2387_, v___x_2388_);
v___y_2373_ = v___x_2389_;
goto v___jp_2372_;
}
else
{
lean_object* v_username_2390_; lean_object* v_val_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
lean_inc_ref(v_password_2385_);
v_username_2390_ = lean_ctor_get(v_val_2384_, 0);
lean_inc_ref(v_username_2390_);
lean_dec(v_val_2384_);
v_val_2391_ = lean_ctor_get(v_password_2385_, 0);
lean_inc(v_val_2391_);
lean_dec_ref_known(v_password_2385_, 1);
v___x_2392_ = lean_string_from_utf8_unchecked(v_username_2390_);
v___x_2393_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2394_ = lean_string_append(v___x_2392_, v___x_2393_);
v___x_2395_ = lean_string_from_utf8_unchecked(v_val_2391_);
v___x_2396_ = lean_string_append(v___x_2394_, v___x_2395_);
lean_dec_ref(v___x_2395_);
v___x_2397_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2398_ = lean_string_append(v___x_2396_, v___x_2397_);
v___y_2373_ = v___x_2398_;
goto v___jp_2372_;
}
}
v___jp_2355_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2359_ = lean_string_append(v___y_2357_, v___y_2356_);
lean_dec_ref(v___y_2356_);
v___x_2360_ = lean_string_append(v___x_2359_, v___y_2358_);
lean_dec_ref(v___y_2358_);
v___x_2361_ = lean_string_append(v___x_2354_, v___x_2360_);
lean_dec_ref(v___x_2360_);
v___y_2338_ = v___x_2361_;
goto v___jp_2337_;
}
v___jp_2362_:
{
switch(lean_obj_tag(v_port_2353_))
{
case 0:
{
lean_object* v___x_2365_; 
v___x_2365_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2356_ = v___y_2364_;
v___y_2357_ = v___y_2363_;
v___y_2358_ = v___x_2365_;
goto v___jp_2355_;
}
case 1:
{
lean_object* v___x_2366_; 
v___x_2366_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_2356_ = v___y_2364_;
v___y_2357_ = v___y_2363_;
v___y_2358_ = v___x_2366_;
goto v___jp_2355_;
}
default: 
{
uint16_t v_port_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v_port_2367_ = lean_ctor_get_uint16(v_port_2353_, 0);
lean_dec_ref_known(v_port_2353_, 0);
v___x_2368_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2369_ = lean_uint16_to_nat(v_port_2367_);
v___x_2370_ = l_Nat_reprFast(v___x_2369_);
v___x_2371_ = lean_string_append(v___x_2368_, v___x_2370_);
lean_dec_ref(v___x_2370_);
v___y_2356_ = v___y_2364_;
v___y_2357_ = v___y_2363_;
v___y_2358_ = v___x_2371_;
goto v___jp_2355_;
}
}
}
v___jp_2372_:
{
switch(lean_obj_tag(v_host_2352_))
{
case 0:
{
lean_object* v_name_2374_; 
v_name_2374_ = lean_ctor_get(v_host_2352_, 0);
lean_inc_ref(v_name_2374_);
lean_dec_ref_known(v_host_2352_, 1);
v___y_2363_ = v___y_2373_;
v___y_2364_ = v_name_2374_;
goto v___jp_2362_;
}
case 1:
{
lean_object* v_ipv4_2375_; lean_object* v___x_2376_; 
v_ipv4_2375_ = lean_ctor_get(v_host_2352_, 0);
lean_inc_ref(v_ipv4_2375_);
lean_dec_ref_known(v_host_2352_, 1);
v___x_2376_ = lean_uv_ntop_v4(v_ipv4_2375_);
lean_dec_ref(v_ipv4_2375_);
v___y_2363_ = v___y_2373_;
v___y_2364_ = v___x_2376_;
goto v___jp_2362_;
}
default: 
{
lean_object* v_ipv6_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v_ipv6_2377_ = lean_ctor_get(v_host_2352_, 0);
lean_inc_ref(v_ipv6_2377_);
lean_dec_ref_known(v_host_2352_, 1);
v___x_2378_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_2379_ = lean_uv_ntop_v6(v_ipv6_2377_);
lean_dec_ref(v_ipv6_2377_);
v___x_2380_ = lean_string_append(v___x_2378_, v___x_2379_);
lean_dec_ref(v___x_2379_);
v___x_2381_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_2382_ = lean_string_append(v___x_2380_, v___x_2381_);
v___y_2363_ = v___y_2373_;
v___y_2364_ = v___x_2382_;
goto v___jp_2362_;
}
}
}
}
v___jp_2316_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2321_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2322_ = lean_string_append(v_scheme_2311_, v___x_2321_);
v___x_2323_ = lean_string_append(v___x_2322_, v___y_2319_);
lean_dec_ref(v___y_2319_);
v___x_2324_ = lean_string_append(v___x_2323_, v___y_2317_);
lean_dec_ref(v___y_2317_);
v___x_2325_ = lean_string_append(v___x_2324_, v___y_2318_);
lean_dec_ref(v___y_2318_);
v___x_2326_ = lean_string_append(v___x_2325_, v___y_2320_);
lean_dec_ref(v___y_2320_);
return v___x_2326_;
}
v___jp_2327_:
{
lean_object* v_queryPart_2330_; 
v_queryPart_2330_ = l_Std_Http_URI_Query_formatOption(v_query_2314_);
if (lean_obj_tag(v_fragment_2315_) == 0)
{
lean_object* v___x_2331_; 
v___x_2331_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2317_ = v___y_2329_;
v___y_2318_ = v_queryPart_2330_;
v___y_2319_ = v___y_2328_;
v___y_2320_ = v___x_2331_;
goto v___jp_2316_;
}
else
{
lean_object* v_val_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_val_2332_ = lean_ctor_get(v_fragment_2315_, 0);
lean_inc(v_val_2332_);
lean_dec_ref_known(v_fragment_2315_, 1);
v___x_2333_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_2334_ = l_Std_Http_URI_EncodedFragment_encode(v_val_2332_);
lean_dec(v_val_2332_);
v___x_2335_ = lean_string_from_utf8_unchecked(v___x_2334_);
v___x_2336_ = lean_string_append(v___x_2333_, v___x_2335_);
lean_dec_ref(v___x_2335_);
v___y_2317_ = v___y_2329_;
v___y_2318_ = v_queryPart_2330_;
v___y_2319_ = v___y_2328_;
v___y_2320_ = v___x_2336_;
goto v___jp_2316_;
}
}
v___jp_2337_:
{
lean_object* v_segments_2339_; uint8_t v_absolute_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; size_t v_sz_2343_; size_t v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v_result_2347_; 
v_segments_2339_ = lean_ctor_get(v_path_2313_, 0);
lean_inc_ref(v_segments_2339_);
v_absolute_2340_ = lean_ctor_get_uint8(v_path_2313_, sizeof(void*)*1);
lean_dec_ref(v_path_2313_);
v___x_2341_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_2342_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_2343_ = lean_array_size(v_segments_2339_);
v___x_2344_ = ((size_t)0ULL);
v___x_2345_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2342_, v___f_2309_, v_sz_2343_, v___x_2344_, v_segments_2339_);
v___x_2346_ = lean_array_to_list(v___x_2345_);
v_result_2347_ = l_String_intercalate(v___x_2341_, v___x_2346_);
if (v_absolute_2340_ == 0)
{
v___y_2328_ = v___y_2338_;
v___y_2329_ = v_result_2347_;
goto v___jp_2327_;
}
else
{
lean_object* v___x_2348_; 
v___x_2348_ = lean_string_append(v___x_2341_, v_result_2347_);
lean_dec_ref(v_result_2347_);
v___y_2328_ = v___y_2338_;
v___y_2329_ = v___x_2348_;
goto v___jp_2327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x3f(lean_object* v_b_2411_, lean_object* v_scheme_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Std_Http_URI_Scheme_ofString_x3f(v_scheme_2412_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v___x_2414_; 
lean_dec_ref(v_b_2411_);
v___x_2414_ = lean_box(0);
return v___x_2414_;
}
else
{
lean_object* v_userInfo_2415_; lean_object* v_host_2416_; lean_object* v_port_2417_; lean_object* v_pathSegments_2418_; lean_object* v_query_2419_; lean_object* v_fragment_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2435_; 
v_userInfo_2415_ = lean_ctor_get(v_b_2411_, 1);
v_host_2416_ = lean_ctor_get(v_b_2411_, 2);
v_port_2417_ = lean_ctor_get(v_b_2411_, 3);
v_pathSegments_2418_ = lean_ctor_get(v_b_2411_, 4);
v_query_2419_ = lean_ctor_get(v_b_2411_, 5);
v_fragment_2420_ = lean_ctor_get(v_b_2411_, 6);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_b_2411_);
if (v_isSharedCheck_2435_ == 0)
{
lean_object* v_unused_2436_; 
v_unused_2436_ = lean_ctor_get(v_b_2411_, 0);
lean_dec(v_unused_2436_);
v___x_2422_ = v_b_2411_;
v_isShared_2423_ = v_isSharedCheck_2435_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_fragment_2420_);
lean_inc(v_query_2419_);
lean_inc(v_pathSegments_2418_);
lean_inc(v_port_2417_);
lean_inc(v_host_2416_);
lean_inc(v_userInfo_2415_);
lean_dec(v_b_2411_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2435_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
lean_inc_ref(v___x_2413_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2413_);
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v_userInfo_2415_);
lean_ctor_set(v_reuseFailAlloc_2434_, 2, v_host_2416_);
lean_ctor_set(v_reuseFailAlloc_2434_, 3, v_port_2417_);
lean_ctor_set(v_reuseFailAlloc_2434_, 4, v_pathSegments_2418_);
lean_ctor_set(v_reuseFailAlloc_2434_, 5, v_query_2419_);
lean_ctor_set(v_reuseFailAlloc_2434_, 6, v_fragment_2420_);
v___x_2425_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; 
v_unused_2433_ = lean_ctor_get(v___x_2413_, 0);
lean_dec(v_unused_2433_);
v___x_2427_ = v___x_2413_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_dec(v___x_2413_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(lean_object* v_msg_2437_){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = ((lean_object*)(l_Std_Http_URI_instInhabitedBuilder_default));
v___x_2439_ = lean_panic_fn_borrowed(v___x_2438_, v_msg_2437_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x21(lean_object* v_b_2441_, lean_object* v_scheme_2442_){
_start:
{
lean_object* v___x_2443_; 
lean_inc_ref(v_scheme_2442_);
v___x_2443_ = l_Std_Http_URI_Builder_setScheme_x3f(v_b_2441_, v_scheme_2442_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2444_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2445_ = ((lean_object*)(l_Std_Http_URI_Builder_setScheme_x21___closed__0));
v___x_2446_ = lean_unsigned_to_nat(687u);
v___x_2447_ = lean_unsigned_to_nat(14u);
v___x_2448_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_2449_ = l_String_quote(v_scheme_2442_);
v___x_2450_ = lean_string_append(v___x_2448_, v___x_2449_);
lean_dec_ref(v___x_2449_);
v___x_2451_ = l_mkPanicMessageWithDecl(v___x_2444_, v___x_2445_, v___x_2446_, v___x_2447_, v___x_2450_);
lean_dec_ref(v___x_2450_);
v___x_2452_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2451_);
return v___x_2452_;
}
else
{
lean_object* v_val_2453_; 
lean_dec_ref(v_scheme_2442_);
v_val_2453_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_val_2453_);
lean_dec_ref_known(v___x_2443_, 1);
return v_val_2453_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo(lean_object* v_b_2454_, lean_object* v_username_2455_, lean_object* v_password_2456_){
_start:
{
lean_object* v_scheme_2457_; lean_object* v_host_2458_; lean_object* v_port_2459_; lean_object* v_pathSegments_2460_; lean_object* v_query_2461_; lean_object* v_fragment_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2485_; 
v_scheme_2457_ = lean_ctor_get(v_b_2454_, 0);
v_host_2458_ = lean_ctor_get(v_b_2454_, 2);
v_port_2459_ = lean_ctor_get(v_b_2454_, 3);
v_pathSegments_2460_ = lean_ctor_get(v_b_2454_, 4);
v_query_2461_ = lean_ctor_get(v_b_2454_, 5);
v_fragment_2462_ = lean_ctor_get(v_b_2454_, 6);
v_isSharedCheck_2485_ = !lean_is_exclusive(v_b_2454_);
if (v_isSharedCheck_2485_ == 0)
{
lean_object* v_unused_2486_; 
v_unused_2486_ = lean_ctor_get(v_b_2454_, 1);
lean_dec(v_unused_2486_);
v___x_2464_ = v_b_2454_;
v_isShared_2465_ = v_isSharedCheck_2485_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_fragment_2462_);
lean_inc(v_query_2461_);
lean_inc(v_pathSegments_2460_);
lean_inc(v_port_2459_);
lean_inc(v_host_2458_);
lean_inc(v_scheme_2457_);
lean_dec(v_b_2454_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2485_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___y_2467_; lean_object* v___x_2472_; 
v___x_2472_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_2455_);
if (lean_obj_tag(v_password_2456_) == 0)
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = lean_box(0);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2472_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___y_2467_ = v___x_2474_;
goto v___jp_2466_;
}
else
{
lean_object* v_val_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2484_; 
v_val_2475_ = lean_ctor_get(v_password_2456_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v_password_2456_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2477_ = v_password_2456_;
v_isShared_2478_ = v_isSharedCheck_2484_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_val_2475_);
lean_dec(v_password_2456_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2484_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2479_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_2475_);
lean_dec(v_val_2475_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v___x_2479_);
v___x_2481_ = v___x_2477_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
lean_object* v___x_2482_; 
v___x_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2472_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___y_2467_ = v___x_2482_;
goto v___jp_2466_;
}
}
}
v___jp_2466_:
{
lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2468_, 0, v___y_2467_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 1, v___x_2468_);
v___x_2470_ = v___x_2464_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_scheme_2457_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2471_, 2, v_host_2458_);
lean_ctor_set(v_reuseFailAlloc_2471_, 3, v_port_2459_);
lean_ctor_set(v_reuseFailAlloc_2471_, 4, v_pathSegments_2460_);
lean_ctor_set(v_reuseFailAlloc_2471_, 5, v_query_2461_);
lean_ctor_set(v_reuseFailAlloc_2471_, 6, v_fragment_2462_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo___boxed(lean_object* v_b_2487_, lean_object* v_username_2488_, lean_object* v_password_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Std_Http_URI_Builder_setUserInfo(v_b_2487_, v_username_2488_, v_password_2489_);
lean_dec_ref(v_username_2488_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x3f(lean_object* v_b_2491_, lean_object* v_name_2492_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Std_Http_URI_DomainName_ofString_x3f(v_name_2492_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v___x_2494_; 
lean_dec_ref(v_b_2491_);
v___x_2494_ = lean_box(0);
return v___x_2494_;
}
else
{
lean_object* v_val_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2518_; 
v_val_2495_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2497_ = v___x_2493_;
v_isShared_2498_ = v_isSharedCheck_2518_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_val_2495_);
lean_dec(v___x_2493_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2518_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v_scheme_2499_; lean_object* v_userInfo_2500_; lean_object* v_port_2501_; lean_object* v_pathSegments_2502_; lean_object* v_query_2503_; lean_object* v_fragment_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2516_; 
v_scheme_2499_ = lean_ctor_get(v_b_2491_, 0);
v_userInfo_2500_ = lean_ctor_get(v_b_2491_, 1);
v_port_2501_ = lean_ctor_get(v_b_2491_, 3);
v_pathSegments_2502_ = lean_ctor_get(v_b_2491_, 4);
v_query_2503_ = lean_ctor_get(v_b_2491_, 5);
v_fragment_2504_ = lean_ctor_get(v_b_2491_, 6);
v_isSharedCheck_2516_ = !lean_is_exclusive(v_b_2491_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; 
v_unused_2517_ = lean_ctor_get(v_b_2491_, 2);
lean_dec(v_unused_2517_);
v___x_2506_ = v_b_2491_;
v_isShared_2507_ = v_isSharedCheck_2516_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_fragment_2504_);
lean_inc(v_query_2503_);
lean_inc(v_pathSegments_2502_);
lean_inc(v_port_2501_);
lean_inc(v_userInfo_2500_);
lean_inc(v_scheme_2499_);
lean_dec(v_b_2491_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2516_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v_val_2495_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 0, v___x_2508_);
v___x_2510_ = v___x_2497_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2512_; 
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 2, v___x_2510_);
v___x_2512_ = v___x_2506_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_scheme_2499_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_userInfo_2500_);
lean_ctor_set(v_reuseFailAlloc_2514_, 2, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2514_, 3, v_port_2501_);
lean_ctor_set(v_reuseFailAlloc_2514_, 4, v_pathSegments_2502_);
lean_ctor_set(v_reuseFailAlloc_2514_, 5, v_query_2503_);
lean_ctor_set(v_reuseFailAlloc_2514_, 6, v_fragment_2504_);
v___x_2512_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2513_; 
v___x_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
return v___x_2513_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x21(lean_object* v_b_2521_, lean_object* v_name_2522_){
_start:
{
lean_object* v___x_2523_; 
lean_inc_ref(v_name_2522_);
v___x_2523_ = l_Std_Http_URI_Builder_setHost_x3f(v_b_2521_, v_name_2522_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2524_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2525_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__0));
v___x_2526_ = lean_unsigned_to_nat(716u);
v___x_2527_ = lean_unsigned_to_nat(14u);
v___x_2528_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__1));
v___x_2529_ = l_String_quote(v_name_2522_);
v___x_2530_ = lean_string_append(v___x_2528_, v___x_2529_);
lean_dec_ref(v___x_2529_);
v___x_2531_ = l_mkPanicMessageWithDecl(v___x_2524_, v___x_2525_, v___x_2526_, v___x_2527_, v___x_2530_);
lean_dec_ref(v___x_2530_);
v___x_2532_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2531_);
return v___x_2532_;
}
else
{
lean_object* v_val_2533_; 
lean_dec_ref(v_name_2522_);
v_val_2533_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_val_2533_);
lean_dec_ref_known(v___x_2523_, 1);
return v_val_2533_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv4(lean_object* v_b_2534_, lean_object* v_addr_2535_){
_start:
{
lean_object* v_scheme_2536_; lean_object* v_userInfo_2537_; lean_object* v_port_2538_; lean_object* v_pathSegments_2539_; lean_object* v_query_2540_; lean_object* v_fragment_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2550_; 
v_scheme_2536_ = lean_ctor_get(v_b_2534_, 0);
v_userInfo_2537_ = lean_ctor_get(v_b_2534_, 1);
v_port_2538_ = lean_ctor_get(v_b_2534_, 3);
v_pathSegments_2539_ = lean_ctor_get(v_b_2534_, 4);
v_query_2540_ = lean_ctor_get(v_b_2534_, 5);
v_fragment_2541_ = lean_ctor_get(v_b_2534_, 6);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_b_2534_);
if (v_isSharedCheck_2550_ == 0)
{
lean_object* v_unused_2551_; 
v_unused_2551_ = lean_ctor_get(v_b_2534_, 2);
lean_dec(v_unused_2551_);
v___x_2543_ = v_b_2534_;
v_isShared_2544_ = v_isSharedCheck_2550_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_fragment_2541_);
lean_inc(v_query_2540_);
lean_inc(v_pathSegments_2539_);
lean_inc(v_port_2538_);
lean_inc(v_userInfo_2537_);
lean_inc(v_scheme_2536_);
lean_dec(v_b_2534_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2550_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2548_; 
v___x_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2545_, 0, v_addr_2535_);
v___x_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 2, v___x_2546_);
v___x_2548_ = v___x_2543_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_scheme_2536_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v_userInfo_2537_);
lean_ctor_set(v_reuseFailAlloc_2549_, 2, v___x_2546_);
lean_ctor_set(v_reuseFailAlloc_2549_, 3, v_port_2538_);
lean_ctor_set(v_reuseFailAlloc_2549_, 4, v_pathSegments_2539_);
lean_ctor_set(v_reuseFailAlloc_2549_, 5, v_query_2540_);
lean_ctor_set(v_reuseFailAlloc_2549_, 6, v_fragment_2541_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv6(lean_object* v_b_2552_, lean_object* v_addr_2553_){
_start:
{
lean_object* v_scheme_2554_; lean_object* v_userInfo_2555_; lean_object* v_port_2556_; lean_object* v_pathSegments_2557_; lean_object* v_query_2558_; lean_object* v_fragment_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2568_; 
v_scheme_2554_ = lean_ctor_get(v_b_2552_, 0);
v_userInfo_2555_ = lean_ctor_get(v_b_2552_, 1);
v_port_2556_ = lean_ctor_get(v_b_2552_, 3);
v_pathSegments_2557_ = lean_ctor_get(v_b_2552_, 4);
v_query_2558_ = lean_ctor_get(v_b_2552_, 5);
v_fragment_2559_ = lean_ctor_get(v_b_2552_, 6);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_b_2552_);
if (v_isSharedCheck_2568_ == 0)
{
lean_object* v_unused_2569_; 
v_unused_2569_ = lean_ctor_get(v_b_2552_, 2);
lean_dec(v_unused_2569_);
v___x_2561_ = v_b_2552_;
v_isShared_2562_ = v_isSharedCheck_2568_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_fragment_2559_);
lean_inc(v_query_2558_);
lean_inc(v_pathSegments_2557_);
lean_inc(v_port_2556_);
lean_inc(v_userInfo_2555_);
lean_inc(v_scheme_2554_);
lean_dec(v_b_2552_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2568_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2566_; 
v___x_2563_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2563_, 0, v_addr_2553_);
v___x_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 2, v___x_2564_);
v___x_2566_ = v___x_2561_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_scheme_2554_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_userInfo_2555_);
lean_ctor_set(v_reuseFailAlloc_2567_, 2, v___x_2564_);
lean_ctor_set(v_reuseFailAlloc_2567_, 3, v_port_2556_);
lean_ctor_set(v_reuseFailAlloc_2567_, 4, v_pathSegments_2557_);
lean_ctor_set(v_reuseFailAlloc_2567_, 5, v_query_2558_);
lean_ctor_set(v_reuseFailAlloc_2567_, 6, v_fragment_2559_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort(lean_object* v_b_2570_, uint16_t v_port_2571_){
_start:
{
lean_object* v_scheme_2572_; lean_object* v_userInfo_2573_; lean_object* v_host_2574_; lean_object* v_pathSegments_2575_; lean_object* v_query_2576_; lean_object* v_fragment_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2585_; 
v_scheme_2572_ = lean_ctor_get(v_b_2570_, 0);
v_userInfo_2573_ = lean_ctor_get(v_b_2570_, 1);
v_host_2574_ = lean_ctor_get(v_b_2570_, 2);
v_pathSegments_2575_ = lean_ctor_get(v_b_2570_, 4);
v_query_2576_ = lean_ctor_get(v_b_2570_, 5);
v_fragment_2577_ = lean_ctor_get(v_b_2570_, 6);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_b_2570_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; 
v_unused_2586_ = lean_ctor_get(v_b_2570_, 3);
lean_dec(v_unused_2586_);
v___x_2579_ = v_b_2570_;
v_isShared_2580_ = v_isSharedCheck_2585_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_fragment_2577_);
lean_inc(v_query_2576_);
lean_inc(v_pathSegments_2575_);
lean_inc(v_host_2574_);
lean_inc(v_userInfo_2573_);
lean_inc(v_scheme_2572_);
lean_dec(v_b_2570_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2585_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2581_ = lean_alloc_ctor(2, 0, 2);
lean_ctor_set_uint16(v___x_2581_, 0, v_port_2571_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 3, v___x_2581_);
v___x_2583_ = v___x_2579_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_scheme_2572_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_userInfo_2573_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v_host_2574_);
lean_ctor_set(v_reuseFailAlloc_2584_, 3, v___x_2581_);
lean_ctor_set(v_reuseFailAlloc_2584_, 4, v_pathSegments_2575_);
lean_ctor_set(v_reuseFailAlloc_2584_, 5, v_query_2576_);
lean_ctor_set(v_reuseFailAlloc_2584_, 6, v_fragment_2577_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort___boxed(lean_object* v_b_2587_, lean_object* v_port_2588_){
_start:
{
uint16_t v_port_boxed_2589_; lean_object* v_res_2590_; 
v_port_boxed_2589_ = lean_unbox(v_port_2588_);
v_res_2590_ = l_Std_Http_URI_Builder_setPort(v_b_2587_, v_port_boxed_2589_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPath(lean_object* v_b_2591_, lean_object* v_segments_2592_){
_start:
{
lean_object* v_scheme_2593_; lean_object* v_userInfo_2594_; lean_object* v_host_2595_; lean_object* v_port_2596_; lean_object* v_query_2597_; lean_object* v_fragment_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
v_scheme_2593_ = lean_ctor_get(v_b_2591_, 0);
v_userInfo_2594_ = lean_ctor_get(v_b_2591_, 1);
v_host_2595_ = lean_ctor_get(v_b_2591_, 2);
v_port_2596_ = lean_ctor_get(v_b_2591_, 3);
v_query_2597_ = lean_ctor_get(v_b_2591_, 5);
v_fragment_2598_ = lean_ctor_get(v_b_2591_, 6);
v_isSharedCheck_2605_ = !lean_is_exclusive(v_b_2591_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; 
v_unused_2606_ = lean_ctor_get(v_b_2591_, 4);
lean_dec(v_unused_2606_);
v___x_2600_ = v_b_2591_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_fragment_2598_);
lean_inc(v_query_2597_);
lean_inc(v_port_2596_);
lean_inc(v_host_2595_);
lean_inc(v_userInfo_2594_);
lean_inc(v_scheme_2593_);
lean_dec(v_b_2591_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 4, v_segments_2592_);
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_scheme_2593_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_userInfo_2594_);
lean_ctor_set(v_reuseFailAlloc_2604_, 2, v_host_2595_);
lean_ctor_set(v_reuseFailAlloc_2604_, 3, v_port_2596_);
lean_ctor_set(v_reuseFailAlloc_2604_, 4, v_segments_2592_);
lean_ctor_set(v_reuseFailAlloc_2604_, 5, v_query_2597_);
lean_ctor_set(v_reuseFailAlloc_2604_, 6, v_fragment_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_appendPathSegment(lean_object* v_b_2607_, lean_object* v_segment_2608_){
_start:
{
lean_object* v_scheme_2609_; lean_object* v_userInfo_2610_; lean_object* v_host_2611_; lean_object* v_port_2612_; lean_object* v_pathSegments_2613_; lean_object* v_query_2614_; lean_object* v_fragment_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2623_; 
v_scheme_2609_ = lean_ctor_get(v_b_2607_, 0);
v_userInfo_2610_ = lean_ctor_get(v_b_2607_, 1);
v_host_2611_ = lean_ctor_get(v_b_2607_, 2);
v_port_2612_ = lean_ctor_get(v_b_2607_, 3);
v_pathSegments_2613_ = lean_ctor_get(v_b_2607_, 4);
v_query_2614_ = lean_ctor_get(v_b_2607_, 5);
v_fragment_2615_ = lean_ctor_get(v_b_2607_, 6);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_b_2607_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2617_ = v_b_2607_;
v_isShared_2618_ = v_isSharedCheck_2623_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_fragment_2615_);
lean_inc(v_query_2614_);
lean_inc(v_pathSegments_2613_);
lean_inc(v_port_2612_);
lean_inc(v_host_2611_);
lean_inc(v_userInfo_2610_);
lean_inc(v_scheme_2609_);
lean_dec(v_b_2607_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2623_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2619_ = lean_array_push(v_pathSegments_2613_, v_segment_2608_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 4, v___x_2619_);
v___x_2621_ = v___x_2617_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_scheme_2609_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_userInfo_2610_);
lean_ctor_set(v_reuseFailAlloc_2622_, 2, v_host_2611_);
lean_ctor_set(v_reuseFailAlloc_2622_, 3, v_port_2612_);
lean_ctor_set(v_reuseFailAlloc_2622_, 4, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2622_, 5, v_query_2614_);
lean_ctor_set(v_reuseFailAlloc_2622_, 6, v_fragment_2615_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryParam(lean_object* v_b_2624_, lean_object* v_key_2625_, lean_object* v_value_2626_){
_start:
{
lean_object* v_scheme_2627_; lean_object* v_userInfo_2628_; lean_object* v_host_2629_; lean_object* v_port_2630_; lean_object* v_pathSegments_2631_; lean_object* v_query_2632_; lean_object* v_fragment_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2643_; 
v_scheme_2627_ = lean_ctor_get(v_b_2624_, 0);
v_userInfo_2628_ = lean_ctor_get(v_b_2624_, 1);
v_host_2629_ = lean_ctor_get(v_b_2624_, 2);
v_port_2630_ = lean_ctor_get(v_b_2624_, 3);
v_pathSegments_2631_ = lean_ctor_get(v_b_2624_, 4);
v_query_2632_ = lean_ctor_get(v_b_2624_, 5);
v_fragment_2633_ = lean_ctor_get(v_b_2624_, 6);
v_isSharedCheck_2643_ = !lean_is_exclusive(v_b_2624_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2635_ = v_b_2624_;
v_isShared_2636_ = v_isSharedCheck_2643_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_fragment_2633_);
lean_inc(v_query_2632_);
lean_inc(v_pathSegments_2631_);
lean_inc(v_port_2630_);
lean_inc(v_host_2629_);
lean_inc(v_userInfo_2628_);
lean_inc(v_scheme_2627_);
lean_dec(v_b_2624_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2643_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2637_, 0, v_value_2626_);
v___x_2638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2638_, 0, v_key_2625_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
v___x_2639_ = lean_array_push(v_query_2632_, v___x_2638_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 5, v___x_2639_);
v___x_2641_ = v___x_2635_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_scheme_2627_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_userInfo_2628_);
lean_ctor_set(v_reuseFailAlloc_2642_, 2, v_host_2629_);
lean_ctor_set(v_reuseFailAlloc_2642_, 3, v_port_2630_);
lean_ctor_set(v_reuseFailAlloc_2642_, 4, v_pathSegments_2631_);
lean_ctor_set(v_reuseFailAlloc_2642_, 5, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2642_, 6, v_fragment_2633_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryFlag(lean_object* v_b_2644_, lean_object* v_key_2645_){
_start:
{
lean_object* v_scheme_2646_; lean_object* v_userInfo_2647_; lean_object* v_host_2648_; lean_object* v_port_2649_; lean_object* v_pathSegments_2650_; lean_object* v_query_2651_; lean_object* v_fragment_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2662_; 
v_scheme_2646_ = lean_ctor_get(v_b_2644_, 0);
v_userInfo_2647_ = lean_ctor_get(v_b_2644_, 1);
v_host_2648_ = lean_ctor_get(v_b_2644_, 2);
v_port_2649_ = lean_ctor_get(v_b_2644_, 3);
v_pathSegments_2650_ = lean_ctor_get(v_b_2644_, 4);
v_query_2651_ = lean_ctor_get(v_b_2644_, 5);
v_fragment_2652_ = lean_ctor_get(v_b_2644_, 6);
v_isSharedCheck_2662_ = !lean_is_exclusive(v_b_2644_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2654_ = v_b_2644_;
v_isShared_2655_ = v_isSharedCheck_2662_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_fragment_2652_);
lean_inc(v_query_2651_);
lean_inc(v_pathSegments_2650_);
lean_inc(v_port_2649_);
lean_inc(v_host_2648_);
lean_inc(v_userInfo_2647_);
lean_inc(v_scheme_2646_);
lean_dec(v_b_2644_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2662_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2656_ = lean_box(0);
v___x_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2657_, 0, v_key_2645_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = lean_array_push(v_query_2651_, v___x_2657_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 5, v___x_2658_);
v___x_2660_ = v___x_2654_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_scheme_2646_);
lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_userInfo_2647_);
lean_ctor_set(v_reuseFailAlloc_2661_, 2, v_host_2648_);
lean_ctor_set(v_reuseFailAlloc_2661_, 3, v_port_2649_);
lean_ctor_set(v_reuseFailAlloc_2661_, 4, v_pathSegments_2650_);
lean_ctor_set(v_reuseFailAlloc_2661_, 5, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2661_, 6, v_fragment_2652_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setQuery(lean_object* v_b_2663_, lean_object* v_query_2664_){
_start:
{
lean_object* v_scheme_2665_; lean_object* v_userInfo_2666_; lean_object* v_host_2667_; lean_object* v_port_2668_; lean_object* v_pathSegments_2669_; lean_object* v_fragment_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
v_scheme_2665_ = lean_ctor_get(v_b_2663_, 0);
v_userInfo_2666_ = lean_ctor_get(v_b_2663_, 1);
v_host_2667_ = lean_ctor_get(v_b_2663_, 2);
v_port_2668_ = lean_ctor_get(v_b_2663_, 3);
v_pathSegments_2669_ = lean_ctor_get(v_b_2663_, 4);
v_fragment_2670_ = lean_ctor_get(v_b_2663_, 6);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_b_2663_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; 
v_unused_2678_ = lean_ctor_get(v_b_2663_, 5);
lean_dec(v_unused_2678_);
v___x_2672_ = v_b_2663_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_fragment_2670_);
lean_inc(v_pathSegments_2669_);
lean_inc(v_port_2668_);
lean_inc(v_host_2667_);
lean_inc(v_userInfo_2666_);
lean_inc(v_scheme_2665_);
lean_dec(v_b_2663_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 5, v_query_2664_);
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_scheme_2665_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_userInfo_2666_);
lean_ctor_set(v_reuseFailAlloc_2676_, 2, v_host_2667_);
lean_ctor_set(v_reuseFailAlloc_2676_, 3, v_port_2668_);
lean_ctor_set(v_reuseFailAlloc_2676_, 4, v_pathSegments_2669_);
lean_ctor_set(v_reuseFailAlloc_2676_, 5, v_query_2664_);
lean_ctor_set(v_reuseFailAlloc_2676_, 6, v_fragment_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setFragment(lean_object* v_b_2679_, lean_object* v_fragment_2680_){
_start:
{
lean_object* v_scheme_2681_; lean_object* v_userInfo_2682_; lean_object* v_host_2683_; lean_object* v_port_2684_; lean_object* v_pathSegments_2685_; lean_object* v_query_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2694_; 
v_scheme_2681_ = lean_ctor_get(v_b_2679_, 0);
v_userInfo_2682_ = lean_ctor_get(v_b_2679_, 1);
v_host_2683_ = lean_ctor_get(v_b_2679_, 2);
v_port_2684_ = lean_ctor_get(v_b_2679_, 3);
v_pathSegments_2685_ = lean_ctor_get(v_b_2679_, 4);
v_query_2686_ = lean_ctor_get(v_b_2679_, 5);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_b_2679_);
if (v_isSharedCheck_2694_ == 0)
{
lean_object* v_unused_2695_; 
v_unused_2695_ = lean_ctor_get(v_b_2679_, 6);
lean_dec(v_unused_2695_);
v___x_2688_ = v_b_2679_;
v_isShared_2689_ = v_isSharedCheck_2694_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_query_2686_);
lean_inc(v_pathSegments_2685_);
lean_inc(v_port_2684_);
lean_inc(v_host_2683_);
lean_inc(v_userInfo_2682_);
lean_inc(v_scheme_2681_);
lean_dec(v_b_2679_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2694_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2690_, 0, v_fragment_2680_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 6, v___x_2690_);
v___x_2692_ = v___x_2688_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_scheme_2681_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v_userInfo_2682_);
lean_ctor_set(v_reuseFailAlloc_2693_, 2, v_host_2683_);
lean_ctor_set(v_reuseFailAlloc_2693_, 3, v_port_2684_);
lean_ctor_set(v_reuseFailAlloc_2693_, 4, v_pathSegments_2685_);
lean_ctor_set(v_reuseFailAlloc_2693_, 5, v_query_2686_);
lean_ctor_set(v_reuseFailAlloc_2693_, 6, v___x_2690_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(size_t v_sz_2696_, size_t v_i_2697_, lean_object* v_bs_2698_){
_start:
{
uint8_t v___x_2699_; 
v___x_2699_ = lean_usize_dec_lt(v_i_2697_, v_sz_2696_);
if (v___x_2699_ == 0)
{
return v_bs_2698_;
}
else
{
lean_object* v_v_2700_; lean_object* v___x_2701_; lean_object* v_bs_x27_2702_; lean_object* v___x_2703_; size_t v___x_2704_; size_t v___x_2705_; lean_object* v___x_2706_; 
v_v_2700_ = lean_array_uget(v_bs_2698_, v_i_2697_);
v___x_2701_ = lean_unsigned_to_nat(0u);
v_bs_x27_2702_ = lean_array_uset(v_bs_2698_, v_i_2697_, v___x_2701_);
v___x_2703_ = l_Std_Http_URI_EncodedSegment_encode(v_v_2700_);
lean_dec(v_v_2700_);
v___x_2704_ = ((size_t)1ULL);
v___x_2705_ = lean_usize_add(v_i_2697_, v___x_2704_);
v___x_2706_ = lean_array_uset(v_bs_x27_2702_, v_i_2697_, v___x_2703_);
v_i_2697_ = v___x_2705_;
v_bs_2698_ = v___x_2706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0___boxed(lean_object* v_sz_2708_, lean_object* v_i_2709_, lean_object* v_bs_2710_){
_start:
{
size_t v_sz_boxed_2711_; size_t v_i_boxed_2712_; lean_object* v_res_2713_; 
v_sz_boxed_2711_ = lean_unbox_usize(v_sz_2708_);
lean_dec(v_sz_2708_);
v_i_boxed_2712_ = lean_unbox_usize(v_i_2709_);
lean_dec(v_i_2709_);
v_res_2713_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_boxed_2711_, v_i_boxed_2712_, v_bs_2710_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(size_t v_sz_2714_, size_t v_i_2715_, lean_object* v_bs_2716_){
_start:
{
uint8_t v___x_2717_; 
v___x_2717_ = lean_usize_dec_lt(v_i_2715_, v_sz_2714_);
if (v___x_2717_ == 0)
{
return v_bs_2716_;
}
else
{
lean_object* v_v_2718_; lean_object* v_fst_2719_; lean_object* v_snd_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2749_; 
v_v_2718_ = lean_array_uget(v_bs_2716_, v_i_2715_);
v_fst_2719_ = lean_ctor_get(v_v_2718_, 0);
v_snd_2720_ = lean_ctor_get(v_v_2718_, 1);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_v_2718_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2722_ = v_v_2718_;
v_isShared_2723_ = v_isSharedCheck_2749_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_snd_2720_);
lean_inc(v_fst_2719_);
lean_dec(v_v_2718_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2749_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; lean_object* v_bs_x27_2725_; lean_object* v___y_2727_; lean_object* v___x_2732_; 
v___x_2724_ = lean_unsigned_to_nat(0u);
v_bs_x27_2725_ = lean_array_uset(v_bs_2716_, v_i_2715_, v___x_2724_);
v___x_2732_ = l_Std_Http_URI_EncodedQueryParam_encode(v_fst_2719_);
lean_dec(v_fst_2719_);
if (lean_obj_tag(v_snd_2720_) == 0)
{
lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2733_ = lean_box(0);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 1, v___x_2733_);
lean_ctor_set(v___x_2722_, 0, v___x_2732_);
v___x_2735_ = v___x_2722_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2732_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
v___y_2727_ = v___x_2735_;
goto v___jp_2726_;
}
}
else
{
lean_object* v_val_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2748_; 
v_val_2737_ = lean_ctor_get(v_snd_2720_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_snd_2720_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2739_ = v_snd_2720_;
v_isShared_2740_ = v_isSharedCheck_2748_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_val_2737_);
lean_dec(v_snd_2720_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2748_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2741_ = l_Std_Http_URI_EncodedQueryParam_encode(v_val_2737_);
lean_dec(v_val_2737_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 0, v___x_2741_);
v___x_2743_ = v___x_2739_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
lean_object* v___x_2745_; 
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 1, v___x_2743_);
lean_ctor_set(v___x_2722_, 0, v___x_2732_);
v___x_2745_ = v___x_2722_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2732_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v___x_2743_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
v___y_2727_ = v___x_2745_;
goto v___jp_2726_;
}
}
}
}
v___jp_2726_:
{
size_t v___x_2728_; size_t v___x_2729_; lean_object* v___x_2730_; 
v___x_2728_ = ((size_t)1ULL);
v___x_2729_ = lean_usize_add(v_i_2715_, v___x_2728_);
v___x_2730_ = lean_array_uset(v_bs_x27_2725_, v_i_2715_, v___y_2727_);
v_i_2715_ = v___x_2729_;
v_bs_2716_ = v___x_2730_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1___boxed(lean_object* v_sz_2750_, lean_object* v_i_2751_, lean_object* v_bs_2752_){
_start:
{
size_t v_sz_boxed_2753_; size_t v_i_boxed_2754_; lean_object* v_res_2755_; 
v_sz_boxed_2753_ = lean_unbox_usize(v_sz_2750_);
lean_dec(v_sz_2750_);
v_i_boxed_2754_ = lean_unbox_usize(v_i_2751_);
lean_dec(v_i_2751_);
v_res_2755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_boxed_2753_, v_i_boxed_2754_, v_bs_2752_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_build(lean_object* v_b_2756_){
_start:
{
lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; uint8_t v___y_2762_; lean_object* v___y_2763_; lean_object* v_scheme_2779_; lean_object* v_userInfo_2780_; lean_object* v_host_2781_; lean_object* v_port_2782_; lean_object* v_pathSegments_2783_; lean_object* v_query_2784_; lean_object* v_fragment_2785_; lean_object* v___y_2787_; 
v_scheme_2779_ = lean_ctor_get(v_b_2756_, 0);
lean_inc(v_scheme_2779_);
v_userInfo_2780_ = lean_ctor_get(v_b_2756_, 1);
lean_inc(v_userInfo_2780_);
v_host_2781_ = lean_ctor_get(v_b_2756_, 2);
lean_inc(v_host_2781_);
v_port_2782_ = lean_ctor_get(v_b_2756_, 3);
lean_inc(v_port_2782_);
v_pathSegments_2783_ = lean_ctor_get(v_b_2756_, 4);
lean_inc_ref(v_pathSegments_2783_);
v_query_2784_ = lean_ctor_get(v_b_2756_, 5);
lean_inc_ref(v_query_2784_);
v_fragment_2785_ = lean_ctor_get(v_b_2756_, 6);
lean_inc(v_fragment_2785_);
lean_dec_ref(v_b_2756_);
if (lean_obj_tag(v_scheme_2779_) == 0)
{
lean_object* v___x_2800_; 
v___x_2800_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___y_2787_ = v___x_2800_;
goto v___jp_2786_;
}
else
{
lean_object* v_val_2801_; 
v_val_2801_ = lean_ctor_get(v_scheme_2779_, 0);
lean_inc(v_val_2801_);
lean_dec_ref_known(v_scheme_2779_, 1);
v___y_2787_ = v_val_2801_;
goto v___jp_2786_;
}
v___jp_2757_:
{
size_t v_sz_2764_; size_t v___x_2765_; lean_object* v___x_2766_; lean_object* v_path_2767_; size_t v_sz_2768_; lean_object* v_query_2769_; lean_object* v___x_2770_; lean_object* v_query_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; 
v_sz_2764_ = lean_array_size(v___y_2759_);
v___x_2765_ = ((size_t)0ULL);
v___x_2766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_2764_, v___x_2765_, v___y_2759_);
v_path_2767_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_path_2767_, 0, v___x_2766_);
lean_ctor_set_uint8(v_path_2767_, sizeof(void*)*1, v___y_2762_);
v_sz_2768_ = lean_array_size(v___y_2760_);
v_query_2769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_2768_, v___x_2765_, v___y_2760_);
v___x_2770_ = lean_array_to_list(v_query_2769_);
v_query_2771_ = lean_array_mk(v___x_2770_);
v___x_2772_ = lean_array_get_size(v_query_2771_);
v___x_2773_ = lean_unsigned_to_nat(0u);
v___x_2774_ = lean_nat_dec_eq(v___x_2772_, v___x_2773_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2775_, 0, v_query_2771_);
v___x_2776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2776_, 0, v___y_2758_);
lean_ctor_set(v___x_2776_, 1, v___y_2763_);
lean_ctor_set(v___x_2776_, 2, v_path_2767_);
lean_ctor_set(v___x_2776_, 3, v___x_2775_);
lean_ctor_set(v___x_2776_, 4, v___y_2761_);
return v___x_2776_;
}
else
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
lean_dec_ref(v_query_2771_);
v___x_2777_ = lean_box(0);
v___x_2778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2778_, 0, v___y_2758_);
lean_ctor_set(v___x_2778_, 1, v___y_2763_);
lean_ctor_set(v___x_2778_, 2, v_path_2767_);
lean_ctor_set(v___x_2778_, 3, v___x_2777_);
lean_ctor_set(v___x_2778_, 4, v___y_2761_);
return v___x_2778_;
}
}
v___jp_2786_:
{
if (lean_obj_tag(v_host_2781_) == 0)
{
uint8_t v___x_2788_; lean_object* v___x_2789_; 
lean_dec(v_port_2782_);
lean_dec(v_userInfo_2780_);
v___x_2788_ = 1;
v___x_2789_ = lean_box(0);
v___y_2758_ = v___y_2787_;
v___y_2759_ = v_pathSegments_2783_;
v___y_2760_ = v_query_2784_;
v___y_2761_ = v_fragment_2785_;
v___y_2762_ = v___x_2788_;
v___y_2763_ = v___x_2789_;
goto v___jp_2757_;
}
else
{
lean_object* v_val_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2799_; 
v_val_2790_ = lean_ctor_get(v_host_2781_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_host_2781_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2792_ = v_host_2781_;
v_isShared_2793_ = v_isSharedCheck_2799_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_val_2790_);
lean_dec(v_host_2781_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2799_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
uint8_t v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2797_; 
v___x_2794_ = 1;
v___x_2795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2795_, 0, v_userInfo_2780_);
lean_ctor_set(v___x_2795_, 1, v_val_2790_);
lean_ctor_set(v___x_2795_, 2, v_port_2782_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v___x_2795_);
v___x_2797_ = v___x_2792_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
v___y_2758_ = v___y_2787_;
v___y_2759_ = v_pathSegments_2783_;
v___y_2760_ = v_query_2784_;
v___y_2761_ = v_fragment_2785_;
v___y_2762_ = v___x_2794_;
v___y_2763_ = v___x_2797_;
goto v___jp_2757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withScheme_x21(lean_object* v_uri_2802_, lean_object* v_scheme_2803_){
_start:
{
lean_object* v_authority_2804_; lean_object* v_path_2805_; lean_object* v_query_2806_; lean_object* v_fragment_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2815_; 
v_authority_2804_ = lean_ctor_get(v_uri_2802_, 1);
v_path_2805_ = lean_ctor_get(v_uri_2802_, 2);
v_query_2806_ = lean_ctor_get(v_uri_2802_, 3);
v_fragment_2807_ = lean_ctor_get(v_uri_2802_, 4);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_uri_2802_);
if (v_isSharedCheck_2815_ == 0)
{
lean_object* v_unused_2816_; 
v_unused_2816_ = lean_ctor_get(v_uri_2802_, 0);
lean_dec(v_unused_2816_);
v___x_2809_ = v_uri_2802_;
v_isShared_2810_ = v_isSharedCheck_2815_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_fragment_2807_);
lean_inc(v_query_2806_);
lean_inc(v_path_2805_);
lean_inc(v_authority_2804_);
lean_dec(v_uri_2802_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2815_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2811_; lean_object* v___x_2813_; 
v___x_2811_ = l_Std_Http_URI_Scheme_ofString_x21(v_scheme_2803_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v___x_2811_);
v___x_2813_ = v___x_2809_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_authority_2804_);
lean_ctor_set(v_reuseFailAlloc_2814_, 2, v_path_2805_);
lean_ctor_set(v_reuseFailAlloc_2814_, 3, v_query_2806_);
lean_ctor_set(v_reuseFailAlloc_2814_, 4, v_fragment_2807_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withAuthority(lean_object* v_uri_2817_, lean_object* v_authority_2818_){
_start:
{
lean_object* v_scheme_2819_; lean_object* v_path_2820_; lean_object* v_query_2821_; lean_object* v_fragment_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
v_scheme_2819_ = lean_ctor_get(v_uri_2817_, 0);
v_path_2820_ = lean_ctor_get(v_uri_2817_, 2);
v_query_2821_ = lean_ctor_get(v_uri_2817_, 3);
v_fragment_2822_ = lean_ctor_get(v_uri_2817_, 4);
v_isSharedCheck_2829_ = !lean_is_exclusive(v_uri_2817_);
if (v_isSharedCheck_2829_ == 0)
{
lean_object* v_unused_2830_; 
v_unused_2830_ = lean_ctor_get(v_uri_2817_, 1);
lean_dec(v_unused_2830_);
v___x_2824_ = v_uri_2817_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_fragment_2822_);
lean_inc(v_query_2821_);
lean_inc(v_path_2820_);
lean_inc(v_scheme_2819_);
lean_dec(v_uri_2817_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 1, v_authority_2818_);
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_scheme_2819_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_authority_2818_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_path_2820_);
lean_ctor_set(v_reuseFailAlloc_2828_, 3, v_query_2821_);
lean_ctor_set(v_reuseFailAlloc_2828_, 4, v_fragment_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withPath(lean_object* v_uri_2831_, lean_object* v_path_2832_){
_start:
{
lean_object* v_scheme_2833_; lean_object* v_authority_2834_; lean_object* v_query_2835_; lean_object* v_fragment_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
v_scheme_2833_ = lean_ctor_get(v_uri_2831_, 0);
v_authority_2834_ = lean_ctor_get(v_uri_2831_, 1);
v_query_2835_ = lean_ctor_get(v_uri_2831_, 3);
v_fragment_2836_ = lean_ctor_get(v_uri_2831_, 4);
v_isSharedCheck_2843_ = !lean_is_exclusive(v_uri_2831_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; 
v_unused_2844_ = lean_ctor_get(v_uri_2831_, 2);
lean_dec(v_unused_2844_);
v___x_2838_ = v_uri_2831_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_fragment_2836_);
lean_inc(v_query_2835_);
lean_inc(v_authority_2834_);
lean_inc(v_scheme_2833_);
lean_dec(v_uri_2831_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 2, v_path_2832_);
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_scheme_2833_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_authority_2834_);
lean_ctor_set(v_reuseFailAlloc_2842_, 2, v_path_2832_);
lean_ctor_set(v_reuseFailAlloc_2842_, 3, v_query_2835_);
lean_ctor_set(v_reuseFailAlloc_2842_, 4, v_fragment_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withQuery(lean_object* v_uri_2845_, lean_object* v_query_2846_){
_start:
{
lean_object* v_scheme_2847_; lean_object* v_authority_2848_; lean_object* v_path_2849_; lean_object* v_fragment_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2858_; 
v_scheme_2847_ = lean_ctor_get(v_uri_2845_, 0);
v_authority_2848_ = lean_ctor_get(v_uri_2845_, 1);
v_path_2849_ = lean_ctor_get(v_uri_2845_, 2);
v_fragment_2850_ = lean_ctor_get(v_uri_2845_, 4);
v_isSharedCheck_2858_ = !lean_is_exclusive(v_uri_2845_);
if (v_isSharedCheck_2858_ == 0)
{
lean_object* v_unused_2859_; 
v_unused_2859_ = lean_ctor_get(v_uri_2845_, 3);
lean_dec(v_unused_2859_);
v___x_2852_ = v_uri_2845_;
v_isShared_2853_ = v_isSharedCheck_2858_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_fragment_2850_);
lean_inc(v_path_2849_);
lean_inc(v_authority_2848_);
lean_inc(v_scheme_2847_);
lean_dec(v_uri_2845_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2858_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2854_; lean_object* v___x_2856_; 
v___x_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2854_, 0, v_query_2846_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 3, v___x_2854_);
v___x_2856_ = v___x_2852_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_scheme_2847_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_authority_2848_);
lean_ctor_set(v_reuseFailAlloc_2857_, 2, v_path_2849_);
lean_ctor_set(v_reuseFailAlloc_2857_, 3, v___x_2854_);
lean_ctor_set(v_reuseFailAlloc_2857_, 4, v_fragment_2850_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withFragment(lean_object* v_uri_2860_, lean_object* v_fragment_2861_){
_start:
{
lean_object* v_scheme_2862_; lean_object* v_authority_2863_; lean_object* v_path_2864_; lean_object* v_query_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
v_scheme_2862_ = lean_ctor_get(v_uri_2860_, 0);
v_authority_2863_ = lean_ctor_get(v_uri_2860_, 1);
v_path_2864_ = lean_ctor_get(v_uri_2860_, 2);
v_query_2865_ = lean_ctor_get(v_uri_2860_, 3);
v_isSharedCheck_2872_ = !lean_is_exclusive(v_uri_2860_);
if (v_isSharedCheck_2872_ == 0)
{
lean_object* v_unused_2873_; 
v_unused_2873_ = lean_ctor_get(v_uri_2860_, 4);
lean_dec(v_unused_2873_);
v___x_2867_ = v_uri_2860_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_query_2865_);
lean_inc(v_path_2864_);
lean_inc(v_authority_2863_);
lean_inc(v_scheme_2862_);
lean_dec(v_uri_2860_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 4, v_fragment_2861_);
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_scheme_2862_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_authority_2863_);
lean_ctor_set(v_reuseFailAlloc_2871_, 2, v_path_2864_);
lean_ctor_set(v_reuseFailAlloc_2871_, 3, v_query_2865_);
lean_ctor_set(v_reuseFailAlloc_2871_, 4, v_fragment_2861_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_normalize(lean_object* v_uri_2874_){
_start:
{
lean_object* v_scheme_2875_; lean_object* v_authority_2876_; lean_object* v_path_2877_; lean_object* v_query_2878_; lean_object* v_fragment_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2887_; 
v_scheme_2875_ = lean_ctor_get(v_uri_2874_, 0);
v_authority_2876_ = lean_ctor_get(v_uri_2874_, 1);
v_path_2877_ = lean_ctor_get(v_uri_2874_, 2);
v_query_2878_ = lean_ctor_get(v_uri_2874_, 3);
v_fragment_2879_ = lean_ctor_get(v_uri_2874_, 4);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_uri_2874_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2881_ = v_uri_2874_;
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_fragment_2879_);
lean_inc(v_query_2878_);
lean_inc(v_path_2877_);
lean_inc(v_authority_2876_);
lean_inc(v_scheme_2875_);
lean_dec(v_uri_2874_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___x_2883_ = l_Std_Http_URI_Path_normalize(v_path_2877_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 2, v___x_2883_);
v___x_2885_ = v___x_2881_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_scheme_2875_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_authority_2876_);
lean_ctor_set(v_reuseFailAlloc_2886_, 2, v___x_2883_);
lean_ctor_set(v_reuseFailAlloc_2886_, 3, v_query_2878_);
lean_ctor_set(v_reuseFailAlloc_2886_, 4, v_fragment_2879_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___redArg(lean_object* v_x_2888_){
_start:
{
lean_object* v_scheme_2889_; lean_object* v_host_2890_; uint16_t v_port_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; uint8_t v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v_ctr_2912_; lean_object* v_a_2913_; 
v_scheme_2889_ = lean_ctor_get(v_x_2888_, 0);
lean_inc_ref(v_scheme_2889_);
v_host_2890_ = lean_ctor_get(v_x_2888_, 1);
lean_inc_ref(v_host_2890_);
v_port_2891_ = lean_ctor_get_uint16(v_x_2888_, sizeof(void*)*2);
lean_dec_ref(v_x_2888_);
v___x_2892_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2893_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2894_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2895_ = l_String_quote(v_scheme_2889_);
v___x_2896_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
v___x_2897_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2894_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
v___x_2898_ = 0;
v___x_2899_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2899_, 0, v___x_2897_);
lean_ctor_set_uint8(v___x_2899_, sizeof(void*)*1, v___x_2898_);
v___x_2900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2893_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
v___x_2901_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2900_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
v___x_2903_ = lean_box(1);
v___x_2904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2902_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_2906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
lean_ctor_set(v___x_2907_, 1, v___x_2892_);
v___x_2908_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2909_ = lean_unsigned_to_nat(0u);
v___x_2910_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_2890_))
{
case 0:
{
lean_object* v_name_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2952_; 
v_name_2943_ = lean_ctor_get(v_host_2890_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_host_2890_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2945_ = v_host_2890_;
v_isShared_2946_ = v_isSharedCheck_2952_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_name_2943_);
lean_dec(v_host_2890_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2952_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2947_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_2948_ = l_String_quote(v_name_2943_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set_tag(v___x_2945_, 3);
lean_ctor_set(v___x_2945_, 0, v___x_2948_);
v___x_2950_ = v___x_2945_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
v_ctr_2912_ = v___x_2947_;
v_a_2913_ = v___x_2950_;
goto v___jp_2911_;
}
}
}
case 1:
{
lean_object* v_ipv4_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2962_; 
v_ipv4_2953_ = lean_ctor_get(v_host_2890_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_host_2890_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2955_ = v_host_2890_;
v_isShared_2956_ = v_isSharedCheck_2962_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_ipv4_2953_);
lean_dec(v_host_2890_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2962_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2960_; 
v___x_2957_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_2958_ = lean_uv_ntop_v4(v_ipv4_2953_);
lean_dec_ref(v_ipv4_2953_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set_tag(v___x_2955_, 3);
lean_ctor_set(v___x_2955_, 0, v___x_2958_);
v___x_2960_ = v___x_2955_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
v_ctr_2912_ = v___x_2957_;
v_a_2913_ = v___x_2960_;
goto v___jp_2911_;
}
}
}
default: 
{
lean_object* v_ipv6_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2972_; 
v_ipv6_2963_ = lean_ctor_get(v_host_2890_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v_host_2890_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2965_ = v_host_2890_;
v_isShared_2966_ = v_isSharedCheck_2972_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_ipv6_2963_);
lean_dec(v_host_2890_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2972_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2970_; 
v___x_2967_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_2968_ = lean_uv_ntop_v6(v_ipv6_2963_);
lean_dec_ref(v_ipv6_2963_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set_tag(v___x_2965_, 3);
lean_ctor_set(v___x_2965_, 0, v___x_2968_);
v___x_2970_ = v___x_2965_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2968_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
v_ctr_2912_ = v___x_2967_;
v_a_2913_ = v___x_2970_;
goto v___jp_2911_;
}
}
}
}
v___jp_2911_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2914_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_2915_ = lean_string_append(v___x_2914_, v_ctr_2912_);
v___x_2916_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
v___x_2917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
lean_ctor_set(v___x_2917_, 1, v___x_2903_);
v___x_2918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
lean_ctor_set(v___x_2918_, 1, v_a_2913_);
v___x_2919_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2910_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*1, v___x_2898_);
v___x_2921_ = l_Repr_addAppParen(v___x_2920_, v___x_2909_);
v___x_2922_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2908_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
v___x_2923_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
lean_ctor_set_uint8(v___x_2923_, sizeof(void*)*1, v___x_2898_);
v___x_2924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2907_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
lean_ctor_set(v___x_2925_, 1, v___x_2901_);
v___x_2926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
lean_ctor_set(v___x_2926_, 1, v___x_2903_);
v___x_2927_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_2928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2926_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
v___x_2929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
lean_ctor_set(v___x_2929_, 1, v___x_2892_);
v___x_2930_ = lean_uint16_to_nat(v_port_2891_);
v___x_2931_ = l_Nat_reprFast(v___x_2930_);
v___x_2932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
v___x_2933_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2908_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
v___x_2934_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*1, v___x_2898_);
v___x_2935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2929_);
lean_ctor_set(v___x_2935_, 1, v___x_2934_);
v___x_2936_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2937_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v___x_2935_);
v___x_2939_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2938_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2936_);
lean_ctor_set(v___x_2941_, 1, v___x_2940_);
v___x_2942_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set_uint8(v___x_2942_, sizeof(void*)*1, v___x_2898_);
return v___x_2942_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr(lean_object* v_x_2973_, lean_object* v_prec_2974_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Std_Http_URI_instReprOrigin_repr___redArg(v_x_2973_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___boxed(lean_object* v_x_2976_, lean_object* v_prec_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Std_Http_URI_instReprOrigin_repr(v_x_2976_, v_prec_2977_);
lean_dec(v_prec_2977_);
return v_res_2978_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqOrigin_beq(lean_object* v_x_2981_, lean_object* v_x_2982_){
_start:
{
lean_object* v_scheme_2983_; lean_object* v_host_2984_; uint16_t v_port_2985_; lean_object* v_scheme_2986_; lean_object* v_host_2987_; uint16_t v_port_2988_; uint8_t v___x_2989_; 
v_scheme_2983_ = lean_ctor_get(v_x_2981_, 0);
v_host_2984_ = lean_ctor_get(v_x_2981_, 1);
v_port_2985_ = lean_ctor_get_uint16(v_x_2981_, sizeof(void*)*2);
v_scheme_2986_ = lean_ctor_get(v_x_2982_, 0);
v_host_2987_ = lean_ctor_get(v_x_2982_, 1);
v_port_2988_ = lean_ctor_get_uint16(v_x_2982_, sizeof(void*)*2);
v___x_2989_ = lean_string_dec_eq(v_scheme_2983_, v_scheme_2986_);
if (v___x_2989_ == 0)
{
return v___x_2989_;
}
else
{
uint8_t v___x_2990_; 
v___x_2990_ = l_Std_Http_URI_instBEqHost_beq(v_host_2984_, v_host_2987_);
if (v___x_2990_ == 0)
{
return v___x_2990_;
}
else
{
uint8_t v___x_2991_; 
v___x_2991_ = lean_uint16_dec_eq(v_port_2985_, v_port_2988_);
return v___x_2991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqOrigin_beq___boxed(lean_object* v_x_2992_, lean_object* v_x_2993_){
_start:
{
uint8_t v_res_2994_; lean_object* v_r_2995_; 
v_res_2994_ = l_Std_Http_URI_instBEqOrigin_beq(v_x_2992_, v_x_2993_);
lean_dec_ref(v_x_2993_);
lean_dec_ref(v_x_2992_);
v_r_2995_ = lean_box(v_res_2994_);
return v_r_2995_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Origin_hostHeader(lean_object* v_o_2998_){
_start:
{
lean_object* v_scheme_2999_; lean_object* v_host_3000_; uint16_t v_port_3001_; lean_object* v___y_3003_; uint16_t v_defaultPort_3009_; uint8_t v___x_3010_; 
v_scheme_2999_ = lean_ctor_get(v_o_2998_, 0);
lean_inc_ref(v_scheme_2999_);
v_host_3000_ = lean_ctor_get(v_o_2998_, 1);
lean_inc_ref(v_host_3000_);
v_port_3001_ = lean_ctor_get_uint16(v_o_2998_, sizeof(void*)*2);
lean_dec_ref(v_o_2998_);
v_defaultPort_3009_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_2999_);
lean_dec_ref(v_scheme_2999_);
v___x_3010_ = lean_uint16_dec_eq(v_port_3001_, v_defaultPort_3009_);
if (v___x_3010_ == 0)
{
switch(lean_obj_tag(v_host_3000_))
{
case 0:
{
lean_object* v_name_3011_; 
v_name_3011_ = lean_ctor_get(v_host_3000_, 0);
lean_inc_ref(v_name_3011_);
lean_dec_ref_known(v_host_3000_, 1);
v___y_3003_ = v_name_3011_;
goto v___jp_3002_;
}
case 1:
{
lean_object* v_ipv4_3012_; lean_object* v___x_3013_; 
v_ipv4_3012_ = lean_ctor_get(v_host_3000_, 0);
lean_inc_ref(v_ipv4_3012_);
lean_dec_ref_known(v_host_3000_, 1);
v___x_3013_ = lean_uv_ntop_v4(v_ipv4_3012_);
lean_dec_ref(v_ipv4_3012_);
v___y_3003_ = v___x_3013_;
goto v___jp_3002_;
}
default: 
{
lean_object* v_ipv6_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v_ipv6_3014_ = lean_ctor_get(v_host_3000_, 0);
lean_inc_ref(v_ipv6_3014_);
lean_dec_ref_known(v_host_3000_, 1);
v___x_3015_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3016_ = lean_uv_ntop_v6(v_ipv6_3014_);
lean_dec_ref(v_ipv6_3014_);
v___x_3017_ = lean_string_append(v___x_3015_, v___x_3016_);
lean_dec_ref(v___x_3016_);
v___x_3018_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3019_ = lean_string_append(v___x_3017_, v___x_3018_);
v___y_3003_ = v___x_3019_;
goto v___jp_3002_;
}
}
}
else
{
switch(lean_obj_tag(v_host_3000_))
{
case 0:
{
lean_object* v_name_3020_; 
v_name_3020_ = lean_ctor_get(v_host_3000_, 0);
lean_inc_ref(v_name_3020_);
lean_dec_ref_known(v_host_3000_, 1);
return v_name_3020_;
}
case 1:
{
lean_object* v_ipv4_3021_; lean_object* v___x_3022_; 
v_ipv4_3021_ = lean_ctor_get(v_host_3000_, 0);
lean_inc_ref(v_ipv4_3021_);
lean_dec_ref_known(v_host_3000_, 1);
v___x_3022_ = lean_uv_ntop_v4(v_ipv4_3021_);
lean_dec_ref(v_ipv4_3021_);
return v___x_3022_;
}
default: 
{
lean_object* v_ipv6_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v_ipv6_3023_ = lean_ctor_get(v_host_3000_, 0);
lean_inc_ref(v_ipv6_3023_);
lean_dec_ref_known(v_host_3000_, 1);
v___x_3024_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3025_ = lean_uv_ntop_v6(v_ipv6_3023_);
lean_dec_ref(v_ipv6_3023_);
v___x_3026_ = lean_string_append(v___x_3024_, v___x_3025_);
lean_dec_ref(v___x_3025_);
v___x_3027_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3028_ = lean_string_append(v___x_3026_, v___x_3027_);
return v___x_3028_;
}
}
}
v___jp_3002_:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3004_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3005_ = lean_string_append(v___y_3003_, v___x_3004_);
v___x_3006_ = lean_uint16_to_nat(v_port_3001_);
v___x_3007_ = l_Nat_reprFast(v___x_3006_);
v___x_3008_ = lean_string_append(v___x_3005_, v___x_3007_);
lean_dec_ref(v___x_3007_);
return v___x_3008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___redArg(lean_object* v_x_3035_){
_start:
{
lean_object* v_authority_3036_; lean_object* v_path_3037_; lean_object* v_query_3038_; lean_object* v_fragment_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; uint8_t v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v_authority_3036_ = lean_ctor_get(v_x_3035_, 0);
lean_inc(v_authority_3036_);
v_path_3037_ = lean_ctor_get(v_x_3035_, 1);
lean_inc_ref(v_path_3037_);
v_query_3038_ = lean_ctor_get(v_x_3035_, 2);
lean_inc(v_query_3038_);
v_fragment_3039_ = lean_ctor_get(v_x_3035_, 3);
lean_inc(v_fragment_3039_);
lean_dec_ref(v_x_3035_);
v___x_3040_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_3041_ = ((lean_object*)(l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__1));
v___x_3042_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_3043_ = lean_unsigned_to_nat(0u);
v___x_3044_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_3036_, v___x_3043_);
v___x_3045_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3042_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = 0;
v___x_3047_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3047_, 0, v___x_3045_);
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*1, v___x_3046_);
v___x_3048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3041_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_3050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3048_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
v___x_3051_ = lean_box(1);
v___x_3052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3050_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_3054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3052_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v___x_3040_);
v___x_3056_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_3057_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3037_);
v___x_3058_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3056_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v___x_3059_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
lean_ctor_set_uint8(v___x_3059_, sizeof(void*)*1, v___x_3046_);
v___x_3060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3055_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
v___x_3061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3060_);
lean_ctor_set(v___x_3061_, 1, v___x_3049_);
v___x_3062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
lean_ctor_set(v___x_3062_, 1, v___x_3051_);
v___x_3063_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_3064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3062_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
v___x_3065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
lean_ctor_set(v___x_3065_, 1, v___x_3040_);
v___x_3066_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_3067_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3038_, v___x_3043_);
v___x_3068_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3066_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*1, v___x_3046_);
v___x_3070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3065_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
lean_ctor_set(v___x_3071_, 1, v___x_3049_);
v___x_3072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v___x_3051_);
v___x_3073_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_3074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3072_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
v___x_3075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set(v___x_3075_, 1, v___x_3040_);
v___x_3076_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_3077_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_3039_, v___x_3043_);
v___x_3078_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3076_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
v___x_3079_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
lean_ctor_set_uint8(v___x_3079_, sizeof(void*)*1, v___x_3046_);
v___x_3080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3075_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_3082_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_3083_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
lean_ctor_set(v___x_3083_, 1, v___x_3080_);
v___x_3084_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_3085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3083_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
v___x_3086_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3081_);
lean_ctor_set(v___x_3086_, 1, v___x_3085_);
v___x_3087_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
lean_ctor_set_uint8(v___x_3087_, sizeof(void*)*1, v___x_3046_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr(lean_object* v_x_3088_, lean_object* v_prec_3089_){
_start:
{
lean_object* v___x_3090_; 
v___x_3090_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_x_3088_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___boxed(lean_object* v_x_3091_, lean_object* v_prec_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Std_Http_URI_instReprRelativeRef_repr(v_x_3091_, v_prec_3092_);
lean_dec(v_prec_3092_);
return v_res_3093_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqRelativeRef_beq(lean_object* v_x_3101_, lean_object* v_x_3102_){
_start:
{
lean_object* v_authority_3103_; lean_object* v_path_3104_; lean_object* v_query_3105_; lean_object* v_fragment_3106_; lean_object* v_authority_3107_; lean_object* v_path_3108_; lean_object* v_query_3109_; lean_object* v_fragment_3110_; uint8_t v___x_3111_; 
v_authority_3103_ = lean_ctor_get(v_x_3101_, 0);
v_path_3104_ = lean_ctor_get(v_x_3101_, 1);
v_query_3105_ = lean_ctor_get(v_x_3101_, 2);
v_fragment_3106_ = lean_ctor_get(v_x_3101_, 3);
v_authority_3107_ = lean_ctor_get(v_x_3102_, 0);
v_path_3108_ = lean_ctor_get(v_x_3102_, 1);
v_query_3109_ = lean_ctor_get(v_x_3102_, 2);
v_fragment_3110_ = lean_ctor_get(v_x_3102_, 3);
v___x_3111_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_3103_, v_authority_3107_);
if (v___x_3111_ == 0)
{
return v___x_3111_;
}
else
{
uint8_t v___x_3112_; 
v___x_3112_ = l_Std_Http_URI_instBEqPath_beq(v_path_3104_, v_path_3108_);
if (v___x_3112_ == 0)
{
return v___x_3112_;
}
else
{
uint8_t v___x_3113_; 
v___x_3113_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_3105_, v_query_3109_);
if (v___x_3113_ == 0)
{
return v___x_3113_;
}
else
{
uint8_t v___x_3114_; 
v___x_3114_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_3106_, v_fragment_3110_);
return v___x_3114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqRelativeRef_beq___boxed(lean_object* v_x_3115_, lean_object* v_x_3116_){
_start:
{
uint8_t v_res_3117_; lean_object* v_r_3118_; 
v_res_3117_ = l_Std_Http_URI_instBEqRelativeRef_beq(v_x_3115_, v_x_3116_);
lean_dec_ref(v_x_3116_);
lean_dec_ref(v_x_3115_);
v_r_3118_ = lean_box(v_res_3117_);
return v_r_3118_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringRelativeRef___lam__1(lean_object* v___f_3121_, lean_object* v_ref_3122_){
_start:
{
lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v_authority_3131_; lean_object* v_path_3132_; lean_object* v_query_3133_; lean_object* v_fragment_3134_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3146_; 
v_authority_3131_ = lean_ctor_get(v_ref_3122_, 0);
lean_inc(v_authority_3131_);
v_path_3132_ = lean_ctor_get(v_ref_3122_, 1);
lean_inc_ref(v_path_3132_);
v_query_3133_ = lean_ctor_get(v_ref_3122_, 2);
lean_inc(v_query_3133_);
v_fragment_3134_ = lean_ctor_get(v_ref_3122_, 3);
lean_inc(v_fragment_3134_);
lean_dec_ref(v_ref_3122_);
if (lean_obj_tag(v_authority_3131_) == 0)
{
lean_object* v___x_3157_; 
v___x_3157_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3146_ = v___x_3157_;
goto v___jp_3145_;
}
else
{
lean_object* v_val_3158_; lean_object* v_userInfo_3159_; lean_object* v_host_3160_; lean_object* v_port_3161_; lean_object* v___x_3162_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3181_; 
v_val_3158_ = lean_ctor_get(v_authority_3131_, 0);
lean_inc(v_val_3158_);
lean_dec_ref_known(v_authority_3131_, 1);
v_userInfo_3159_ = lean_ctor_get(v_val_3158_, 0);
lean_inc(v_userInfo_3159_);
v_host_3160_ = lean_ctor_get(v_val_3158_, 1);
lean_inc_ref(v_host_3160_);
v_port_3161_ = lean_ctor_get(v_val_3158_, 2);
lean_inc(v_port_3161_);
lean_dec(v_val_3158_);
v___x_3162_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3159_) == 0)
{
lean_object* v___x_3191_; 
v___x_3191_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3181_ = v___x_3191_;
goto v___jp_3180_;
}
else
{
lean_object* v_val_3192_; lean_object* v_password_3193_; 
v_val_3192_ = lean_ctor_get(v_userInfo_3159_, 0);
lean_inc(v_val_3192_);
lean_dec_ref_known(v_userInfo_3159_, 1);
v_password_3193_ = lean_ctor_get(v_val_3192_, 1);
if (lean_obj_tag(v_password_3193_) == 0)
{
lean_object* v_username_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v_username_3194_ = lean_ctor_get(v_val_3192_, 0);
lean_inc_ref(v_username_3194_);
lean_dec(v_val_3192_);
v___x_3195_ = lean_string_from_utf8_unchecked(v_username_3194_);
v___x_3196_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3197_ = lean_string_append(v___x_3195_, v___x_3196_);
v___y_3181_ = v___x_3197_;
goto v___jp_3180_;
}
else
{
lean_object* v_username_3198_; lean_object* v_val_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
lean_inc_ref(v_password_3193_);
v_username_3198_ = lean_ctor_get(v_val_3192_, 0);
lean_inc_ref(v_username_3198_);
lean_dec(v_val_3192_);
v_val_3199_ = lean_ctor_get(v_password_3193_, 0);
lean_inc(v_val_3199_);
lean_dec_ref_known(v_password_3193_, 1);
v___x_3200_ = lean_string_from_utf8_unchecked(v_username_3198_);
v___x_3201_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3202_ = lean_string_append(v___x_3200_, v___x_3201_);
v___x_3203_ = lean_string_from_utf8_unchecked(v_val_3199_);
v___x_3204_ = lean_string_append(v___x_3202_, v___x_3203_);
lean_dec_ref(v___x_3203_);
v___x_3205_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3206_ = lean_string_append(v___x_3204_, v___x_3205_);
v___y_3181_ = v___x_3206_;
goto v___jp_3180_;
}
}
v___jp_3163_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_string_append(v___y_3164_, v___y_3165_);
lean_dec_ref(v___y_3165_);
v___x_3168_ = lean_string_append(v___x_3167_, v___y_3166_);
lean_dec_ref(v___y_3166_);
v___x_3169_ = lean_string_append(v___x_3162_, v___x_3168_);
lean_dec_ref(v___x_3168_);
v___y_3146_ = v___x_3169_;
goto v___jp_3145_;
}
v___jp_3170_:
{
switch(lean_obj_tag(v_port_3161_))
{
case 0:
{
lean_object* v___x_3173_; 
v___x_3173_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3164_ = v___y_3171_;
v___y_3165_ = v___y_3172_;
v___y_3166_ = v___x_3173_;
goto v___jp_3163_;
}
case 1:
{
lean_object* v___x_3174_; 
v___x_3174_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3164_ = v___y_3171_;
v___y_3165_ = v___y_3172_;
v___y_3166_ = v___x_3174_;
goto v___jp_3163_;
}
default: 
{
uint16_t v_port_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v_port_3175_ = lean_ctor_get_uint16(v_port_3161_, 0);
lean_dec_ref_known(v_port_3161_, 0);
v___x_3176_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3177_ = lean_uint16_to_nat(v_port_3175_);
v___x_3178_ = l_Nat_reprFast(v___x_3177_);
v___x_3179_ = lean_string_append(v___x_3176_, v___x_3178_);
lean_dec_ref(v___x_3178_);
v___y_3164_ = v___y_3171_;
v___y_3165_ = v___y_3172_;
v___y_3166_ = v___x_3179_;
goto v___jp_3163_;
}
}
}
v___jp_3180_:
{
switch(lean_obj_tag(v_host_3160_))
{
case 0:
{
lean_object* v_name_3182_; 
v_name_3182_ = lean_ctor_get(v_host_3160_, 0);
lean_inc_ref(v_name_3182_);
lean_dec_ref_known(v_host_3160_, 1);
v___y_3171_ = v___y_3181_;
v___y_3172_ = v_name_3182_;
goto v___jp_3170_;
}
case 1:
{
lean_object* v_ipv4_3183_; lean_object* v___x_3184_; 
v_ipv4_3183_ = lean_ctor_get(v_host_3160_, 0);
lean_inc_ref(v_ipv4_3183_);
lean_dec_ref_known(v_host_3160_, 1);
v___x_3184_ = lean_uv_ntop_v4(v_ipv4_3183_);
lean_dec_ref(v_ipv4_3183_);
v___y_3171_ = v___y_3181_;
v___y_3172_ = v___x_3184_;
goto v___jp_3170_;
}
default: 
{
lean_object* v_ipv6_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v_ipv6_3185_ = lean_ctor_get(v_host_3160_, 0);
lean_inc_ref(v_ipv6_3185_);
lean_dec_ref_known(v_host_3160_, 1);
v___x_3186_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3187_ = lean_uv_ntop_v6(v_ipv6_3185_);
lean_dec_ref(v_ipv6_3185_);
v___x_3188_ = lean_string_append(v___x_3186_, v___x_3187_);
lean_dec_ref(v___x_3187_);
v___x_3189_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3190_ = lean_string_append(v___x_3188_, v___x_3189_);
v___y_3171_ = v___y_3181_;
v___y_3172_ = v___x_3190_;
goto v___jp_3170_;
}
}
}
}
v___jp_3123_:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = lean_string_append(v___y_3125_, v___y_3126_);
lean_dec_ref(v___y_3126_);
v___x_3129_ = lean_string_append(v___x_3128_, v___y_3124_);
lean_dec_ref(v___y_3124_);
v___x_3130_ = lean_string_append(v___x_3129_, v___y_3127_);
lean_dec_ref(v___y_3127_);
return v___x_3130_;
}
v___jp_3135_:
{
lean_object* v_queryPart_3138_; 
v_queryPart_3138_ = l_Std_Http_URI_Query_formatOption(v_query_3133_);
if (lean_obj_tag(v_fragment_3134_) == 0)
{
lean_object* v___x_3139_; 
v___x_3139_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3124_ = v_queryPart_3138_;
v___y_3125_ = v___y_3136_;
v___y_3126_ = v___y_3137_;
v___y_3127_ = v___x_3139_;
goto v___jp_3123_;
}
else
{
lean_object* v_val_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v_val_3140_ = lean_ctor_get(v_fragment_3134_, 0);
lean_inc(v_val_3140_);
lean_dec_ref_known(v_fragment_3134_, 1);
v___x_3141_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3142_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3140_);
lean_dec(v_val_3140_);
v___x_3143_ = lean_string_from_utf8_unchecked(v___x_3142_);
v___x_3144_ = lean_string_append(v___x_3141_, v___x_3143_);
lean_dec_ref(v___x_3143_);
v___y_3124_ = v_queryPart_3138_;
v___y_3125_ = v___y_3136_;
v___y_3126_ = v___y_3137_;
v___y_3127_ = v___x_3144_;
goto v___jp_3123_;
}
}
v___jp_3145_:
{
lean_object* v_segments_3147_; uint8_t v_absolute_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; size_t v_sz_3151_; size_t v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v_result_3155_; 
v_segments_3147_ = lean_ctor_get(v_path_3132_, 0);
lean_inc_ref(v_segments_3147_);
v_absolute_3148_ = lean_ctor_get_uint8(v_path_3132_, sizeof(void*)*1);
lean_dec_ref(v_path_3132_);
v___x_3149_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3150_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3151_ = lean_array_size(v_segments_3147_);
v___x_3152_ = ((size_t)0ULL);
v___x_3153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3150_, v___f_3121_, v_sz_3151_, v___x_3152_, v_segments_3147_);
v___x_3154_ = lean_array_to_list(v___x_3153_);
v_result_3155_ = l_String_intercalate(v___x_3149_, v___x_3154_);
if (v_absolute_3148_ == 0)
{
v___y_3136_ = v___y_3146_;
v___y_3137_ = v_result_3155_;
goto v___jp_3135_;
}
else
{
lean_object* v___x_3156_; 
v___x_3156_ = lean_string_append(v___x_3149_, v_result_3155_);
lean_dec_ref(v_result_3155_);
v___y_3136_ = v___y_3146_;
v___y_3137_ = v___x_3156_;
goto v___jp_3135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___impl(lean_object* v_x_3210_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = lean_obj_tag_nat(v_x_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___impl___boxed(lean_object* v_x_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Std_Http_URIReference_ctorIdx___impl(v_x_3212_);
lean_dec_ref(v_x_3212_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___redArg(lean_object* v_t_3214_, lean_object* v_k_3215_){
_start:
{
lean_object* v_uri_3216_; lean_object* v___x_3217_; 
v_uri_3216_ = lean_ctor_get(v_t_3214_, 0);
lean_inc_ref(v_uri_3216_);
lean_dec_ref(v_t_3214_);
v___x_3217_ = lean_apply_1(v_k_3215_, v_uri_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim(lean_object* v_motive_3218_, lean_object* v_ctorIdx_3219_, lean_object* v_t_3220_, lean_object* v_h_3221_, lean_object* v_k_3222_){
_start:
{
lean_object* v___x_3223_; 
v___x_3223_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3220_, v_k_3222_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___boxed(lean_object* v_motive_3224_, lean_object* v_ctorIdx_3225_, lean_object* v_t_3226_, lean_object* v_h_3227_, lean_object* v_k_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Std_Http_URIReference_ctorElim(v_motive_3224_, v_ctorIdx_3225_, v_t_3226_, v_h_3227_, v_k_3228_);
lean_dec(v_ctorIdx_3225_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim___redArg(lean_object* v_t_3230_, lean_object* v_absolute_3231_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3230_, v_absolute_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim(lean_object* v_motive_3233_, lean_object* v_t_3234_, lean_object* v_h_3235_, lean_object* v_absolute_3236_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3234_, v_absolute_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim___redArg(lean_object* v_t_3238_, lean_object* v_relative_3239_){
_start:
{
lean_object* v___x_3240_; 
v___x_3240_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3238_, v_relative_3239_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim(lean_object* v_motive_3241_, lean_object* v_t_3242_, lean_object* v_h_3243_, lean_object* v_relative_3244_){
_start:
{
lean_object* v___x_3245_; 
v___x_3245_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3242_, v_relative_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr(lean_object* v_x_3258_, lean_object* v_prec_3259_){
_start:
{
if (lean_obj_tag(v_x_3258_) == 0)
{
lean_object* v_uri_3260_; lean_object* v___y_3262_; lean_object* v___x_3270_; uint8_t v___x_3271_; 
v_uri_3260_ = lean_ctor_get(v_x_3258_, 0);
lean_inc_ref(v_uri_3260_);
lean_dec_ref_known(v_x_3258_, 1);
v___x_3270_ = lean_unsigned_to_nat(1024u);
v___x_3271_ = lean_nat_dec_le(v___x_3270_, v_prec_3259_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; 
v___x_3272_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3262_ = v___x_3272_;
goto v___jp_3261_;
}
else
{
lean_object* v___x_3273_; 
v___x_3273_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3262_ = v___x_3273_;
goto v___jp_3261_;
}
v___jp_3261_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; uint8_t v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3263_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__2));
v___x_3264_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3260_);
v___x_3265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
lean_inc(v___y_3262_);
v___x_3266_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___y_3262_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
v___x_3267_ = 0;
v___x_3268_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3268_, 0, v___x_3266_);
lean_ctor_set_uint8(v___x_3268_, sizeof(void*)*1, v___x_3267_);
v___x_3269_ = l_Repr_addAppParen(v___x_3268_, v_prec_3259_);
return v___x_3269_;
}
}
else
{
lean_object* v_ref_3274_; lean_object* v___y_3276_; lean_object* v___x_3284_; uint8_t v___x_3285_; 
v_ref_3274_ = lean_ctor_get(v_x_3258_, 0);
lean_inc_ref(v_ref_3274_);
lean_dec_ref_known(v_x_3258_, 1);
v___x_3284_ = lean_unsigned_to_nat(1024u);
v___x_3285_ = lean_nat_dec_le(v___x_3284_, v_prec_3259_);
if (v___x_3285_ == 0)
{
lean_object* v___x_3286_; 
v___x_3286_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3276_ = v___x_3286_;
goto v___jp_3275_;
}
else
{
lean_object* v___x_3287_; 
v___x_3287_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3276_ = v___x_3287_;
goto v___jp_3275_;
}
v___jp_3275_:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; uint8_t v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3277_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__5));
v___x_3278_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_ref_3274_);
v___x_3279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3277_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
lean_inc(v___y_3276_);
v___x_3280_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___y_3276_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
v___x_3281_ = 0;
v___x_3282_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set_uint8(v___x_3282_, sizeof(void*)*1, v___x_3281_);
v___x_3283_ = l_Repr_addAppParen(v___x_3282_, v_prec_3259_);
return v___x_3283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr___boxed(lean_object* v_x_3288_, lean_object* v_prec_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Std_Http_instReprURIReference_repr(v_x_3288_, v_prec_3289_);
lean_dec(v_prec_3289_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURIReference___lam__2(lean_object* v___f_3297_, lean_object* v___f_3298_, lean_object* v_x_3299_){
_start:
{
lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; 
if (lean_obj_tag(v_x_3299_) == 0)
{
lean_object* v_uri_3308_; lean_object* v_scheme_3309_; lean_object* v_authority_3310_; lean_object* v_path_3311_; lean_object* v_query_3312_; lean_object* v_fragment_3313_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3336_; 
lean_dec_ref(v___f_3298_);
v_uri_3308_ = lean_ctor_get(v_x_3299_, 0);
lean_inc_ref(v_uri_3308_);
lean_dec_ref_known(v_x_3299_, 1);
v_scheme_3309_ = lean_ctor_get(v_uri_3308_, 0);
lean_inc_ref(v_scheme_3309_);
v_authority_3310_ = lean_ctor_get(v_uri_3308_, 1);
lean_inc(v_authority_3310_);
v_path_3311_ = lean_ctor_get(v_uri_3308_, 2);
lean_inc_ref(v_path_3311_);
v_query_3312_ = lean_ctor_get(v_uri_3308_, 3);
lean_inc(v_query_3312_);
v_fragment_3313_ = lean_ctor_get(v_uri_3308_, 4);
lean_inc(v_fragment_3313_);
lean_dec_ref(v_uri_3308_);
if (lean_obj_tag(v_authority_3310_) == 0)
{
lean_object* v___x_3347_; 
v___x_3347_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3336_ = v___x_3347_;
goto v___jp_3335_;
}
else
{
lean_object* v_val_3348_; lean_object* v_userInfo_3349_; lean_object* v_host_3350_; lean_object* v_port_3351_; lean_object* v___x_3352_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3371_; 
v_val_3348_ = lean_ctor_get(v_authority_3310_, 0);
lean_inc(v_val_3348_);
lean_dec_ref_known(v_authority_3310_, 1);
v_userInfo_3349_ = lean_ctor_get(v_val_3348_, 0);
lean_inc(v_userInfo_3349_);
v_host_3350_ = lean_ctor_get(v_val_3348_, 1);
lean_inc_ref(v_host_3350_);
v_port_3351_ = lean_ctor_get(v_val_3348_, 2);
lean_inc(v_port_3351_);
lean_dec(v_val_3348_);
v___x_3352_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3349_) == 0)
{
lean_object* v___x_3381_; 
v___x_3381_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3371_ = v___x_3381_;
goto v___jp_3370_;
}
else
{
lean_object* v_val_3382_; lean_object* v_password_3383_; 
v_val_3382_ = lean_ctor_get(v_userInfo_3349_, 0);
lean_inc(v_val_3382_);
lean_dec_ref_known(v_userInfo_3349_, 1);
v_password_3383_ = lean_ctor_get(v_val_3382_, 1);
if (lean_obj_tag(v_password_3383_) == 0)
{
lean_object* v_username_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v_username_3384_ = lean_ctor_get(v_val_3382_, 0);
lean_inc_ref(v_username_3384_);
lean_dec(v_val_3382_);
v___x_3385_ = lean_string_from_utf8_unchecked(v_username_3384_);
v___x_3386_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3387_ = lean_string_append(v___x_3385_, v___x_3386_);
v___y_3371_ = v___x_3387_;
goto v___jp_3370_;
}
else
{
lean_object* v_username_3388_; lean_object* v_val_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
lean_inc_ref(v_password_3383_);
v_username_3388_ = lean_ctor_get(v_val_3382_, 0);
lean_inc_ref(v_username_3388_);
lean_dec(v_val_3382_);
v_val_3389_ = lean_ctor_get(v_password_3383_, 0);
lean_inc(v_val_3389_);
lean_dec_ref_known(v_password_3383_, 1);
v___x_3390_ = lean_string_from_utf8_unchecked(v_username_3388_);
v___x_3391_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3392_ = lean_string_append(v___x_3390_, v___x_3391_);
v___x_3393_ = lean_string_from_utf8_unchecked(v_val_3389_);
v___x_3394_ = lean_string_append(v___x_3392_, v___x_3393_);
lean_dec_ref(v___x_3393_);
v___x_3395_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3396_ = lean_string_append(v___x_3394_, v___x_3395_);
v___y_3371_ = v___x_3396_;
goto v___jp_3370_;
}
}
v___jp_3353_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3357_ = lean_string_append(v___y_3354_, v___y_3355_);
lean_dec_ref(v___y_3355_);
v___x_3358_ = lean_string_append(v___x_3357_, v___y_3356_);
lean_dec_ref(v___y_3356_);
v___x_3359_ = lean_string_append(v___x_3352_, v___x_3358_);
lean_dec_ref(v___x_3358_);
v___y_3336_ = v___x_3359_;
goto v___jp_3335_;
}
v___jp_3360_:
{
switch(lean_obj_tag(v_port_3351_))
{
case 0:
{
lean_object* v___x_3363_; 
v___x_3363_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3354_ = v___y_3361_;
v___y_3355_ = v___y_3362_;
v___y_3356_ = v___x_3363_;
goto v___jp_3353_;
}
case 1:
{
lean_object* v___x_3364_; 
v___x_3364_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3354_ = v___y_3361_;
v___y_3355_ = v___y_3362_;
v___y_3356_ = v___x_3364_;
goto v___jp_3353_;
}
default: 
{
uint16_t v_port_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v_port_3365_ = lean_ctor_get_uint16(v_port_3351_, 0);
lean_dec_ref_known(v_port_3351_, 0);
v___x_3366_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3367_ = lean_uint16_to_nat(v_port_3365_);
v___x_3368_ = l_Nat_reprFast(v___x_3367_);
v___x_3369_ = lean_string_append(v___x_3366_, v___x_3368_);
lean_dec_ref(v___x_3368_);
v___y_3354_ = v___y_3361_;
v___y_3355_ = v___y_3362_;
v___y_3356_ = v___x_3369_;
goto v___jp_3353_;
}
}
}
v___jp_3370_:
{
switch(lean_obj_tag(v_host_3350_))
{
case 0:
{
lean_object* v_name_3372_; 
v_name_3372_ = lean_ctor_get(v_host_3350_, 0);
lean_inc_ref(v_name_3372_);
lean_dec_ref_known(v_host_3350_, 1);
v___y_3361_ = v___y_3371_;
v___y_3362_ = v_name_3372_;
goto v___jp_3360_;
}
case 1:
{
lean_object* v_ipv4_3373_; lean_object* v___x_3374_; 
v_ipv4_3373_ = lean_ctor_get(v_host_3350_, 0);
lean_inc_ref(v_ipv4_3373_);
lean_dec_ref_known(v_host_3350_, 1);
v___x_3374_ = lean_uv_ntop_v4(v_ipv4_3373_);
lean_dec_ref(v_ipv4_3373_);
v___y_3361_ = v___y_3371_;
v___y_3362_ = v___x_3374_;
goto v___jp_3360_;
}
default: 
{
lean_object* v_ipv6_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v_ipv6_3375_ = lean_ctor_get(v_host_3350_, 0);
lean_inc_ref(v_ipv6_3375_);
lean_dec_ref_known(v_host_3350_, 1);
v___x_3376_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3377_ = lean_uv_ntop_v6(v_ipv6_3375_);
lean_dec_ref(v_ipv6_3375_);
v___x_3378_ = lean_string_append(v___x_3376_, v___x_3377_);
lean_dec_ref(v___x_3377_);
v___x_3379_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3380_ = lean_string_append(v___x_3378_, v___x_3379_);
v___y_3361_ = v___y_3371_;
v___y_3362_ = v___x_3380_;
goto v___jp_3360_;
}
}
}
}
v___jp_3314_:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3319_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3320_ = lean_string_append(v_scheme_3309_, v___x_3319_);
v___x_3321_ = lean_string_append(v___x_3320_, v___y_3315_);
lean_dec_ref(v___y_3315_);
v___x_3322_ = lean_string_append(v___x_3321_, v___y_3317_);
lean_dec_ref(v___y_3317_);
v___x_3323_ = lean_string_append(v___x_3322_, v___y_3316_);
lean_dec_ref(v___y_3316_);
v___x_3324_ = lean_string_append(v___x_3323_, v___y_3318_);
lean_dec_ref(v___y_3318_);
return v___x_3324_;
}
v___jp_3325_:
{
lean_object* v_queryPart_3328_; 
v_queryPart_3328_ = l_Std_Http_URI_Query_formatOption(v_query_3312_);
if (lean_obj_tag(v_fragment_3313_) == 0)
{
lean_object* v___x_3329_; 
v___x_3329_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3315_ = v___y_3326_;
v___y_3316_ = v_queryPart_3328_;
v___y_3317_ = v___y_3327_;
v___y_3318_ = v___x_3329_;
goto v___jp_3314_;
}
else
{
lean_object* v_val_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v_val_3330_ = lean_ctor_get(v_fragment_3313_, 0);
lean_inc(v_val_3330_);
lean_dec_ref_known(v_fragment_3313_, 1);
v___x_3331_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3332_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3330_);
lean_dec(v_val_3330_);
v___x_3333_ = lean_string_from_utf8_unchecked(v___x_3332_);
v___x_3334_ = lean_string_append(v___x_3331_, v___x_3333_);
lean_dec_ref(v___x_3333_);
v___y_3315_ = v___y_3326_;
v___y_3316_ = v_queryPart_3328_;
v___y_3317_ = v___y_3327_;
v___y_3318_ = v___x_3334_;
goto v___jp_3314_;
}
}
v___jp_3335_:
{
lean_object* v_segments_3337_; uint8_t v_absolute_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; size_t v_sz_3341_; size_t v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v_result_3345_; 
v_segments_3337_ = lean_ctor_get(v_path_3311_, 0);
lean_inc_ref(v_segments_3337_);
v_absolute_3338_ = lean_ctor_get_uint8(v_path_3311_, sizeof(void*)*1);
lean_dec_ref(v_path_3311_);
v___x_3339_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3340_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3341_ = lean_array_size(v_segments_3337_);
v___x_3342_ = ((size_t)0ULL);
v___x_3343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3340_, v___f_3297_, v_sz_3341_, v___x_3342_, v_segments_3337_);
v___x_3344_ = lean_array_to_list(v___x_3343_);
v_result_3345_ = l_String_intercalate(v___x_3339_, v___x_3344_);
if (v_absolute_3338_ == 0)
{
v___y_3326_ = v___y_3336_;
v___y_3327_ = v_result_3345_;
goto v___jp_3325_;
}
else
{
lean_object* v___x_3346_; 
v___x_3346_ = lean_string_append(v___x_3339_, v_result_3345_);
lean_dec_ref(v_result_3345_);
v___y_3326_ = v___y_3336_;
v___y_3327_ = v___x_3346_;
goto v___jp_3325_;
}
}
}
else
{
lean_object* v_ref_3397_; lean_object* v_authority_3398_; lean_object* v_path_3399_; lean_object* v_query_3400_; lean_object* v_fragment_3401_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3413_; 
lean_dec_ref(v___f_3297_);
v_ref_3397_ = lean_ctor_get(v_x_3299_, 0);
lean_inc_ref(v_ref_3397_);
lean_dec_ref_known(v_x_3299_, 1);
v_authority_3398_ = lean_ctor_get(v_ref_3397_, 0);
lean_inc(v_authority_3398_);
v_path_3399_ = lean_ctor_get(v_ref_3397_, 1);
lean_inc_ref(v_path_3399_);
v_query_3400_ = lean_ctor_get(v_ref_3397_, 2);
lean_inc(v_query_3400_);
v_fragment_3401_ = lean_ctor_get(v_ref_3397_, 3);
lean_inc(v_fragment_3401_);
lean_dec_ref(v_ref_3397_);
if (lean_obj_tag(v_authority_3398_) == 0)
{
lean_object* v___x_3424_; 
v___x_3424_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3413_ = v___x_3424_;
goto v___jp_3412_;
}
else
{
lean_object* v_val_3425_; lean_object* v_userInfo_3426_; lean_object* v_host_3427_; lean_object* v_port_3428_; lean_object* v___x_3429_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3448_; 
v_val_3425_ = lean_ctor_get(v_authority_3398_, 0);
lean_inc(v_val_3425_);
lean_dec_ref_known(v_authority_3398_, 1);
v_userInfo_3426_ = lean_ctor_get(v_val_3425_, 0);
lean_inc(v_userInfo_3426_);
v_host_3427_ = lean_ctor_get(v_val_3425_, 1);
lean_inc_ref(v_host_3427_);
v_port_3428_ = lean_ctor_get(v_val_3425_, 2);
lean_inc(v_port_3428_);
lean_dec(v_val_3425_);
v___x_3429_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3426_) == 0)
{
lean_object* v___x_3458_; 
v___x_3458_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3448_ = v___x_3458_;
goto v___jp_3447_;
}
else
{
lean_object* v_val_3459_; lean_object* v_password_3460_; 
v_val_3459_ = lean_ctor_get(v_userInfo_3426_, 0);
lean_inc(v_val_3459_);
lean_dec_ref_known(v_userInfo_3426_, 1);
v_password_3460_ = lean_ctor_get(v_val_3459_, 1);
if (lean_obj_tag(v_password_3460_) == 0)
{
lean_object* v_username_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v_username_3461_ = lean_ctor_get(v_val_3459_, 0);
lean_inc_ref(v_username_3461_);
lean_dec(v_val_3459_);
v___x_3462_ = lean_string_from_utf8_unchecked(v_username_3461_);
v___x_3463_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3464_ = lean_string_append(v___x_3462_, v___x_3463_);
v___y_3448_ = v___x_3464_;
goto v___jp_3447_;
}
else
{
lean_object* v_username_3465_; lean_object* v_val_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
lean_inc_ref(v_password_3460_);
v_username_3465_ = lean_ctor_get(v_val_3459_, 0);
lean_inc_ref(v_username_3465_);
lean_dec(v_val_3459_);
v_val_3466_ = lean_ctor_get(v_password_3460_, 0);
lean_inc(v_val_3466_);
lean_dec_ref_known(v_password_3460_, 1);
v___x_3467_ = lean_string_from_utf8_unchecked(v_username_3465_);
v___x_3468_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3469_ = lean_string_append(v___x_3467_, v___x_3468_);
v___x_3470_ = lean_string_from_utf8_unchecked(v_val_3466_);
v___x_3471_ = lean_string_append(v___x_3469_, v___x_3470_);
lean_dec_ref(v___x_3470_);
v___x_3472_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3473_ = lean_string_append(v___x_3471_, v___x_3472_);
v___y_3448_ = v___x_3473_;
goto v___jp_3447_;
}
}
v___jp_3430_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3434_ = lean_string_append(v___y_3431_, v___y_3432_);
lean_dec_ref(v___y_3432_);
v___x_3435_ = lean_string_append(v___x_3434_, v___y_3433_);
lean_dec_ref(v___y_3433_);
v___x_3436_ = lean_string_append(v___x_3429_, v___x_3435_);
lean_dec_ref(v___x_3435_);
v___y_3413_ = v___x_3436_;
goto v___jp_3412_;
}
v___jp_3437_:
{
switch(lean_obj_tag(v_port_3428_))
{
case 0:
{
lean_object* v___x_3440_; 
v___x_3440_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3431_ = v___y_3438_;
v___y_3432_ = v___y_3439_;
v___y_3433_ = v___x_3440_;
goto v___jp_3430_;
}
case 1:
{
lean_object* v___x_3441_; 
v___x_3441_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3431_ = v___y_3438_;
v___y_3432_ = v___y_3439_;
v___y_3433_ = v___x_3441_;
goto v___jp_3430_;
}
default: 
{
uint16_t v_port_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v_port_3442_ = lean_ctor_get_uint16(v_port_3428_, 0);
lean_dec_ref_known(v_port_3428_, 0);
v___x_3443_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3444_ = lean_uint16_to_nat(v_port_3442_);
v___x_3445_ = l_Nat_reprFast(v___x_3444_);
v___x_3446_ = lean_string_append(v___x_3443_, v___x_3445_);
lean_dec_ref(v___x_3445_);
v___y_3431_ = v___y_3438_;
v___y_3432_ = v___y_3439_;
v___y_3433_ = v___x_3446_;
goto v___jp_3430_;
}
}
}
v___jp_3447_:
{
switch(lean_obj_tag(v_host_3427_))
{
case 0:
{
lean_object* v_name_3449_; 
v_name_3449_ = lean_ctor_get(v_host_3427_, 0);
lean_inc_ref(v_name_3449_);
lean_dec_ref_known(v_host_3427_, 1);
v___y_3438_ = v___y_3448_;
v___y_3439_ = v_name_3449_;
goto v___jp_3437_;
}
case 1:
{
lean_object* v_ipv4_3450_; lean_object* v___x_3451_; 
v_ipv4_3450_ = lean_ctor_get(v_host_3427_, 0);
lean_inc_ref(v_ipv4_3450_);
lean_dec_ref_known(v_host_3427_, 1);
v___x_3451_ = lean_uv_ntop_v4(v_ipv4_3450_);
lean_dec_ref(v_ipv4_3450_);
v___y_3438_ = v___y_3448_;
v___y_3439_ = v___x_3451_;
goto v___jp_3437_;
}
default: 
{
lean_object* v_ipv6_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v_ipv6_3452_ = lean_ctor_get(v_host_3427_, 0);
lean_inc_ref(v_ipv6_3452_);
lean_dec_ref_known(v_host_3427_, 1);
v___x_3453_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3454_ = lean_uv_ntop_v6(v_ipv6_3452_);
lean_dec_ref(v_ipv6_3452_);
v___x_3455_ = lean_string_append(v___x_3453_, v___x_3454_);
lean_dec_ref(v___x_3454_);
v___x_3456_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3457_ = lean_string_append(v___x_3455_, v___x_3456_);
v___y_3438_ = v___y_3448_;
v___y_3439_ = v___x_3457_;
goto v___jp_3437_;
}
}
}
}
v___jp_3402_:
{
lean_object* v_queryPart_3405_; 
v_queryPart_3405_ = l_Std_Http_URI_Query_formatOption(v_query_3400_);
if (lean_obj_tag(v_fragment_3401_) == 0)
{
lean_object* v___x_3406_; 
v___x_3406_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3301_ = v_queryPart_3405_;
v___y_3302_ = v___y_3403_;
v___y_3303_ = v___y_3404_;
v___y_3304_ = v___x_3406_;
goto v___jp_3300_;
}
else
{
lean_object* v_val_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v_val_3407_ = lean_ctor_get(v_fragment_3401_, 0);
lean_inc(v_val_3407_);
lean_dec_ref_known(v_fragment_3401_, 1);
v___x_3408_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3409_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3407_);
lean_dec(v_val_3407_);
v___x_3410_ = lean_string_from_utf8_unchecked(v___x_3409_);
v___x_3411_ = lean_string_append(v___x_3408_, v___x_3410_);
lean_dec_ref(v___x_3410_);
v___y_3301_ = v_queryPart_3405_;
v___y_3302_ = v___y_3403_;
v___y_3303_ = v___y_3404_;
v___y_3304_ = v___x_3411_;
goto v___jp_3300_;
}
}
v___jp_3412_:
{
lean_object* v_segments_3414_; uint8_t v_absolute_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; size_t v_sz_3418_; size_t v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v_result_3422_; 
v_segments_3414_ = lean_ctor_get(v_path_3399_, 0);
lean_inc_ref(v_segments_3414_);
v_absolute_3415_ = lean_ctor_get_uint8(v_path_3399_, sizeof(void*)*1);
lean_dec_ref(v_path_3399_);
v___x_3416_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3417_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3418_ = lean_array_size(v_segments_3414_);
v___x_3419_ = ((size_t)0ULL);
v___x_3420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3417_, v___f_3298_, v_sz_3418_, v___x_3419_, v_segments_3414_);
v___x_3421_ = lean_array_to_list(v___x_3420_);
v_result_3422_ = l_String_intercalate(v___x_3416_, v___x_3421_);
if (v_absolute_3415_ == 0)
{
v___y_3403_ = v___y_3413_;
v___y_3404_ = v_result_3422_;
goto v___jp_3402_;
}
else
{
lean_object* v___x_3423_; 
v___x_3423_ = lean_string_append(v___x_3416_, v_result_3422_);
lean_dec_ref(v_result_3422_);
v___y_3403_ = v___y_3413_;
v___y_3404_ = v___x_3423_;
goto v___jp_3402_;
}
}
}
v___jp_3300_:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = lean_string_append(v___y_3302_, v___y_3303_);
lean_dec_ref(v___y_3303_);
v___x_3306_ = lean_string_append(v___x_3305_, v___y_3301_);
lean_dec_ref(v___y_3301_);
v___x_3307_ = lean_string_append(v___x_3306_, v___y_3304_);
lean_dec_ref(v___y_3304_);
return v___x_3307_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___impl(lean_object* v_x_3477_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = lean_obj_tag_nat(v_x_3477_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___impl___boxed(lean_object* v_x_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Std_Http_RequestTarget_ctorIdx___impl(v_x_3479_);
lean_dec(v_x_3479_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___redArg(lean_object* v_t_3481_, lean_object* v_k_3482_){
_start:
{
switch(lean_obj_tag(v_t_3481_))
{
case 0:
{
lean_object* v_path_3483_; lean_object* v_query_3484_; lean_object* v___x_3485_; 
v_path_3483_ = lean_ctor_get(v_t_3481_, 0);
lean_inc_ref(v_path_3483_);
v_query_3484_ = lean_ctor_get(v_t_3481_, 1);
lean_inc(v_query_3484_);
lean_dec_ref_known(v_t_3481_, 2);
v___x_3485_ = lean_apply_2(v_k_3482_, v_path_3483_, v_query_3484_);
return v___x_3485_;
}
case 3:
{
return v_k_3482_;
}
default: 
{
lean_object* v_uri_3486_; lean_object* v___x_3487_; 
v_uri_3486_ = lean_ctor_get(v_t_3481_, 0);
lean_inc_ref(v_uri_3486_);
lean_dec(v_t_3481_);
v___x_3487_ = lean_apply_1(v_k_3482_, v_uri_3486_);
return v___x_3487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim(lean_object* v_motive_3488_, lean_object* v_ctorIdx_3489_, lean_object* v_t_3490_, lean_object* v_h_3491_, lean_object* v_k_3492_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3490_, v_k_3492_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___boxed(lean_object* v_motive_3494_, lean_object* v_ctorIdx_3495_, lean_object* v_t_3496_, lean_object* v_h_3497_, lean_object* v_k_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l_Std_Http_RequestTarget_ctorElim(v_motive_3494_, v_ctorIdx_3495_, v_t_3496_, v_h_3497_, v_k_3498_);
lean_dec(v_ctorIdx_3495_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim___redArg(lean_object* v_t_3500_, lean_object* v_originForm_3501_){
_start:
{
lean_object* v___x_3502_; 
v___x_3502_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3500_, v_originForm_3501_);
return v___x_3502_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim(lean_object* v_motive_3503_, lean_object* v_t_3504_, lean_object* v_h_3505_, lean_object* v_originForm_3506_){
_start:
{
lean_object* v___x_3507_; 
v___x_3507_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3504_, v_originForm_3506_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim___redArg(lean_object* v_t_3508_, lean_object* v_absoluteForm_3509_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3508_, v_absoluteForm_3509_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim(lean_object* v_motive_3511_, lean_object* v_t_3512_, lean_object* v_h_3513_, lean_object* v_absoluteForm_3514_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3512_, v_absoluteForm_3514_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim___redArg(lean_object* v_t_3516_, lean_object* v_authorityForm_3517_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3516_, v_authorityForm_3517_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim(lean_object* v_motive_3519_, lean_object* v_t_3520_, lean_object* v_h_3521_, lean_object* v_authorityForm_3522_){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3520_, v_authorityForm_3522_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim___redArg(lean_object* v_t_3524_, lean_object* v_asteriskForm_3525_){
_start:
{
lean_object* v___x_3526_; 
v___x_3526_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3524_, v_asteriskForm_3525_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim(lean_object* v_motive_3527_, lean_object* v_t_3528_, lean_object* v_h_3529_, lean_object* v_asteriskForm_3530_){
_start:
{
lean_object* v___x_3531_; 
v___x_3531_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3528_, v_asteriskForm_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object* v_x_3558_, lean_object* v_prec_3559_){
_start:
{
lean_object* v___y_3561_; 
switch(lean_obj_tag(v_x_3558_))
{
case 0:
{
lean_object* v_path_3567_; lean_object* v_query_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3592_; 
v_path_3567_ = lean_ctor_get(v_x_3558_, 0);
v_query_3568_ = lean_ctor_get(v_x_3558_, 1);
v_isSharedCheck_3592_ = !lean_is_exclusive(v_x_3558_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3570_ = v_x_3558_;
v_isShared_3571_ = v_isSharedCheck_3592_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_query_3568_);
lean_inc(v_path_3567_);
lean_dec(v_x_3558_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3592_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___y_3573_; lean_object* v___x_3588_; uint8_t v___x_3589_; 
v___x_3588_ = lean_unsigned_to_nat(1024u);
v___x_3589_ = lean_nat_dec_le(v___x_3588_, v_prec_3559_);
if (v___x_3589_ == 0)
{
lean_object* v___x_3590_; 
v___x_3590_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3573_ = v___x_3590_;
goto v___jp_3572_;
}
else
{
lean_object* v___x_3591_; 
v___x_3591_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3573_ = v___x_3591_;
goto v___jp_3572_;
}
v___jp_3572_:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3574_ = lean_box(1);
v___x_3575_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__4));
v___x_3576_ = lean_unsigned_to_nat(1024u);
v___x_3577_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3567_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set_tag(v___x_3570_, 5);
lean_ctor_set(v___x_3570_, 1, v___x_3577_);
lean_ctor_set(v___x_3570_, 0, v___x_3575_);
v___x_3579_ = v___x_3570_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3575_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; uint8_t v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
lean_ctor_set(v___x_3580_, 1, v___x_3574_);
v___x_3581_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3568_, v___x_3576_);
v___x_3582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3580_);
lean_ctor_set(v___x_3582_, 1, v___x_3581_);
lean_inc(v___y_3573_);
v___x_3583_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___y_3573_);
lean_ctor_set(v___x_3583_, 1, v___x_3582_);
v___x_3584_ = 0;
v___x_3585_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3585_, 0, v___x_3583_);
lean_ctor_set_uint8(v___x_3585_, sizeof(void*)*1, v___x_3584_);
v___x_3586_ = l_Repr_addAppParen(v___x_3585_, v_prec_3559_);
return v___x_3586_;
}
}
}
}
case 1:
{
lean_object* v_uri_3593_; lean_object* v___y_3595_; lean_object* v___x_3603_; uint8_t v___x_3604_; 
v_uri_3593_ = lean_ctor_get(v_x_3558_, 0);
lean_inc_ref(v_uri_3593_);
lean_dec_ref_known(v_x_3558_, 1);
v___x_3603_ = lean_unsigned_to_nat(1024u);
v___x_3604_ = lean_nat_dec_le(v___x_3603_, v_prec_3559_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; 
v___x_3605_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3595_ = v___x_3605_;
goto v___jp_3594_;
}
else
{
lean_object* v___x_3606_; 
v___x_3606_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3595_ = v___x_3606_;
goto v___jp_3594_;
}
v___jp_3594_:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; uint8_t v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3596_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__7));
v___x_3597_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3593_);
v___x_3598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3596_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
lean_inc(v___y_3595_);
v___x_3599_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___y_3595_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
v___x_3600_ = 0;
v___x_3601_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3601_, 0, v___x_3599_);
lean_ctor_set_uint8(v___x_3601_, sizeof(void*)*1, v___x_3600_);
v___x_3602_ = l_Repr_addAppParen(v___x_3601_, v_prec_3559_);
return v___x_3602_;
}
}
case 2:
{
lean_object* v_authority_3607_; lean_object* v___y_3609_; lean_object* v___x_3617_; uint8_t v___x_3618_; 
v_authority_3607_ = lean_ctor_get(v_x_3558_, 0);
lean_inc_ref(v_authority_3607_);
lean_dec_ref_known(v_x_3558_, 1);
v___x_3617_ = lean_unsigned_to_nat(1024u);
v___x_3618_ = lean_nat_dec_le(v___x_3617_, v_prec_3559_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; 
v___x_3619_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3609_ = v___x_3619_;
goto v___jp_3608_;
}
else
{
lean_object* v___x_3620_; 
v___x_3620_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3609_ = v___x_3620_;
goto v___jp_3608_;
}
v___jp_3608_:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; uint8_t v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3610_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__10));
v___x_3611_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_authority_3607_);
v___x_3612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3610_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
lean_inc(v___y_3609_);
v___x_3613_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___y_3609_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v___x_3614_ = 0;
v___x_3615_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3615_, 0, v___x_3613_);
lean_ctor_set_uint8(v___x_3615_, sizeof(void*)*1, v___x_3614_);
v___x_3616_ = l_Repr_addAppParen(v___x_3615_, v_prec_3559_);
return v___x_3616_;
}
}
default: 
{
lean_object* v___x_3621_; uint8_t v___x_3622_; 
v___x_3621_ = lean_unsigned_to_nat(1024u);
v___x_3622_ = lean_nat_dec_le(v___x_3621_, v_prec_3559_);
if (v___x_3622_ == 0)
{
lean_object* v___x_3623_; 
v___x_3623_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3561_ = v___x_3623_;
goto v___jp_3560_;
}
else
{
lean_object* v___x_3624_; 
v___x_3624_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3561_ = v___x_3624_;
goto v___jp_3560_;
}
}
}
v___jp_3560_:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; uint8_t v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3562_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__1));
lean_inc(v___y_3561_);
v___x_3563_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___y_3561_);
lean_ctor_set(v___x_3563_, 1, v___x_3562_);
v___x_3564_ = 0;
v___x_3565_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3565_, 0, v___x_3563_);
lean_ctor_set_uint8(v___x_3565_, sizeof(void*)*1, v___x_3564_);
v___x_3566_ = l_Repr_addAppParen(v___x_3565_, v_prec_3559_);
return v___x_3566_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr___boxed(lean_object* v_x_3625_, lean_object* v_prec_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Std_Http_instReprRequestTarget_repr(v_x_3625_, v_prec_3626_);
lean_dec(v_prec_3626_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path(lean_object* v_x_3635_){
_start:
{
switch(lean_obj_tag(v_x_3635_))
{
case 0:
{
lean_object* v_path_3636_; 
v_path_3636_ = lean_ctor_get(v_x_3635_, 0);
lean_inc_ref(v_path_3636_);
return v_path_3636_;
}
case 1:
{
lean_object* v_uri_3637_; lean_object* v_path_3638_; 
v_uri_3637_ = lean_ctor_get(v_x_3635_, 0);
v_path_3638_ = lean_ctor_get(v_uri_3637_, 2);
lean_inc_ref(v_path_3638_);
return v_path_3638_;
}
default: 
{
lean_object* v___x_3639_; 
v___x_3639_ = ((lean_object*)(l_Std_Http_RequestTarget_path___closed__1));
return v___x_3639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path___boxed(lean_object* v_x_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_Std_Http_RequestTarget_path(v_x_3640_);
lean_dec(v_x_3640_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query(lean_object* v_x_3642_){
_start:
{
switch(lean_obj_tag(v_x_3642_))
{
case 0:
{
lean_object* v_query_3643_; 
v_query_3643_ = lean_ctor_get(v_x_3642_, 1);
if (lean_obj_tag(v_query_3643_) == 0)
{
lean_object* v___x_3644_; 
v___x_3644_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3644_;
}
else
{
lean_object* v_val_3645_; 
v_val_3645_ = lean_ctor_get(v_query_3643_, 0);
lean_inc(v_val_3645_);
return v_val_3645_;
}
}
case 1:
{
lean_object* v_uri_3646_; lean_object* v_query_3647_; 
v_uri_3646_ = lean_ctor_get(v_x_3642_, 0);
v_query_3647_ = lean_ctor_get(v_uri_3646_, 3);
if (lean_obj_tag(v_query_3647_) == 0)
{
lean_object* v___x_3648_; 
v___x_3648_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3648_;
}
else
{
lean_object* v_val_3649_; 
v_val_3649_ = lean_ctor_get(v_query_3647_, 0);
lean_inc(v_val_3649_);
return v_val_3649_;
}
}
default: 
{
lean_object* v___x_3650_; 
v___x_3650_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query___boxed(lean_object* v_x_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Std_Http_RequestTarget_query(v_x_3651_);
lean_dec(v_x_3651_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authority_x3f(lean_object* v_x_3653_){
_start:
{
switch(lean_obj_tag(v_x_3653_))
{
case 2:
{
lean_object* v_authority_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
v_authority_3654_ = lean_ctor_get(v_x_3653_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v_x_3653_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v_x_3653_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_authority_3654_);
lean_dec(v_x_3653_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
lean_ctor_set_tag(v___x_3656_, 1);
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_authority_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
case 1:
{
lean_object* v_uri_3662_; lean_object* v_authority_3663_; 
v_uri_3662_ = lean_ctor_get(v_x_3653_, 0);
lean_inc_ref(v_uri_3662_);
lean_dec_ref_known(v_x_3653_, 1);
v_authority_3663_ = lean_ctor_get(v_uri_3662_, 1);
lean_inc(v_authority_3663_);
lean_dec_ref(v_uri_3662_);
return v_authority_3663_;
}
default: 
{
lean_object* v___x_3664_; 
lean_dec(v_x_3653_);
v___x_3664_ = lean_box(0);
return v___x_3664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__2(lean_object* v___f_3666_, lean_object* v___f_3667_, lean_object* v_x_3668_){
_start:
{
lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; 
switch(lean_obj_tag(v_x_3668_))
{
case 0:
{
lean_object* v_path_3675_; lean_object* v_query_3676_; lean_object* v___y_3678_; lean_object* v_segments_3681_; uint8_t v_absolute_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; size_t v_sz_3685_; size_t v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v_result_3689_; 
lean_dec_ref(v___f_3667_);
v_path_3675_ = lean_ctor_get(v_x_3668_, 0);
lean_inc_ref(v_path_3675_);
v_query_3676_ = lean_ctor_get(v_x_3668_, 1);
lean_inc(v_query_3676_);
lean_dec_ref_known(v_x_3668_, 2);
v_segments_3681_ = lean_ctor_get(v_path_3675_, 0);
lean_inc_ref(v_segments_3681_);
v_absolute_3682_ = lean_ctor_get_uint8(v_path_3675_, sizeof(void*)*1);
lean_dec_ref(v_path_3675_);
v___x_3683_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3684_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3685_ = lean_array_size(v_segments_3681_);
v___x_3686_ = ((size_t)0ULL);
v___x_3687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3684_, v___f_3666_, v_sz_3685_, v___x_3686_, v_segments_3681_);
v___x_3688_ = lean_array_to_list(v___x_3687_);
v_result_3689_ = l_String_intercalate(v___x_3683_, v___x_3688_);
if (v_absolute_3682_ == 0)
{
v___y_3678_ = v_result_3689_;
goto v___jp_3677_;
}
else
{
lean_object* v___x_3690_; 
v___x_3690_ = lean_string_append(v___x_3683_, v_result_3689_);
lean_dec_ref(v_result_3689_);
v___y_3678_ = v___x_3690_;
goto v___jp_3677_;
}
v___jp_3677_:
{
lean_object* v_queryStr_3679_; lean_object* v___x_3680_; 
v_queryStr_3679_ = l_Std_Http_URI_Query_formatOption(v_query_3676_);
v___x_3680_ = lean_string_append(v___y_3678_, v_queryStr_3679_);
lean_dec_ref(v_queryStr_3679_);
return v___x_3680_;
}
}
case 1:
{
lean_object* v_uri_3691_; lean_object* v_scheme_3692_; lean_object* v_authority_3693_; lean_object* v_path_3694_; lean_object* v_query_3695_; lean_object* v_fragment_3696_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3719_; 
lean_dec_ref(v___f_3666_);
v_uri_3691_ = lean_ctor_get(v_x_3668_, 0);
lean_inc_ref(v_uri_3691_);
lean_dec_ref_known(v_x_3668_, 1);
v_scheme_3692_ = lean_ctor_get(v_uri_3691_, 0);
lean_inc_ref(v_scheme_3692_);
v_authority_3693_ = lean_ctor_get(v_uri_3691_, 1);
lean_inc(v_authority_3693_);
v_path_3694_ = lean_ctor_get(v_uri_3691_, 2);
lean_inc_ref(v_path_3694_);
v_query_3695_ = lean_ctor_get(v_uri_3691_, 3);
lean_inc(v_query_3695_);
v_fragment_3696_ = lean_ctor_get(v_uri_3691_, 4);
lean_inc(v_fragment_3696_);
lean_dec_ref(v_uri_3691_);
if (lean_obj_tag(v_authority_3693_) == 0)
{
lean_object* v___x_3730_; 
v___x_3730_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3719_ = v___x_3730_;
goto v___jp_3718_;
}
else
{
lean_object* v_val_3731_; lean_object* v_userInfo_3732_; lean_object* v_host_3733_; lean_object* v_port_3734_; lean_object* v___x_3735_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3754_; 
v_val_3731_ = lean_ctor_get(v_authority_3693_, 0);
lean_inc(v_val_3731_);
lean_dec_ref_known(v_authority_3693_, 1);
v_userInfo_3732_ = lean_ctor_get(v_val_3731_, 0);
lean_inc(v_userInfo_3732_);
v_host_3733_ = lean_ctor_get(v_val_3731_, 1);
lean_inc_ref(v_host_3733_);
v_port_3734_ = lean_ctor_get(v_val_3731_, 2);
lean_inc(v_port_3734_);
lean_dec(v_val_3731_);
v___x_3735_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3732_) == 0)
{
lean_object* v___x_3764_; 
v___x_3764_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3754_ = v___x_3764_;
goto v___jp_3753_;
}
else
{
lean_object* v_val_3765_; lean_object* v_password_3766_; 
v_val_3765_ = lean_ctor_get(v_userInfo_3732_, 0);
lean_inc(v_val_3765_);
lean_dec_ref_known(v_userInfo_3732_, 1);
v_password_3766_ = lean_ctor_get(v_val_3765_, 1);
if (lean_obj_tag(v_password_3766_) == 0)
{
lean_object* v_username_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v_username_3767_ = lean_ctor_get(v_val_3765_, 0);
lean_inc_ref(v_username_3767_);
lean_dec(v_val_3765_);
v___x_3768_ = lean_string_from_utf8_unchecked(v_username_3767_);
v___x_3769_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3770_ = lean_string_append(v___x_3768_, v___x_3769_);
v___y_3754_ = v___x_3770_;
goto v___jp_3753_;
}
else
{
lean_object* v_username_3771_; lean_object* v_val_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
lean_inc_ref(v_password_3766_);
v_username_3771_ = lean_ctor_get(v_val_3765_, 0);
lean_inc_ref(v_username_3771_);
lean_dec(v_val_3765_);
v_val_3772_ = lean_ctor_get(v_password_3766_, 0);
lean_inc(v_val_3772_);
lean_dec_ref_known(v_password_3766_, 1);
v___x_3773_ = lean_string_from_utf8_unchecked(v_username_3771_);
v___x_3774_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3775_ = lean_string_append(v___x_3773_, v___x_3774_);
v___x_3776_ = lean_string_from_utf8_unchecked(v_val_3772_);
v___x_3777_ = lean_string_append(v___x_3775_, v___x_3776_);
lean_dec_ref(v___x_3776_);
v___x_3778_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3779_ = lean_string_append(v___x_3777_, v___x_3778_);
v___y_3754_ = v___x_3779_;
goto v___jp_3753_;
}
}
v___jp_3736_:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3740_ = lean_string_append(v___y_3737_, v___y_3738_);
lean_dec_ref(v___y_3738_);
v___x_3741_ = lean_string_append(v___x_3740_, v___y_3739_);
lean_dec_ref(v___y_3739_);
v___x_3742_ = lean_string_append(v___x_3735_, v___x_3741_);
lean_dec_ref(v___x_3741_);
v___y_3719_ = v___x_3742_;
goto v___jp_3718_;
}
v___jp_3743_:
{
switch(lean_obj_tag(v_port_3734_))
{
case 0:
{
lean_object* v___x_3746_; 
v___x_3746_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3737_ = v___y_3744_;
v___y_3738_ = v___y_3745_;
v___y_3739_ = v___x_3746_;
goto v___jp_3736_;
}
case 1:
{
lean_object* v___x_3747_; 
v___x_3747_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3737_ = v___y_3744_;
v___y_3738_ = v___y_3745_;
v___y_3739_ = v___x_3747_;
goto v___jp_3736_;
}
default: 
{
uint16_t v_port_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v_port_3748_ = lean_ctor_get_uint16(v_port_3734_, 0);
lean_dec_ref_known(v_port_3734_, 0);
v___x_3749_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3750_ = lean_uint16_to_nat(v_port_3748_);
v___x_3751_ = l_Nat_reprFast(v___x_3750_);
v___x_3752_ = lean_string_append(v___x_3749_, v___x_3751_);
lean_dec_ref(v___x_3751_);
v___y_3737_ = v___y_3744_;
v___y_3738_ = v___y_3745_;
v___y_3739_ = v___x_3752_;
goto v___jp_3736_;
}
}
}
v___jp_3753_:
{
switch(lean_obj_tag(v_host_3733_))
{
case 0:
{
lean_object* v_name_3755_; 
v_name_3755_ = lean_ctor_get(v_host_3733_, 0);
lean_inc_ref(v_name_3755_);
lean_dec_ref_known(v_host_3733_, 1);
v___y_3744_ = v___y_3754_;
v___y_3745_ = v_name_3755_;
goto v___jp_3743_;
}
case 1:
{
lean_object* v_ipv4_3756_; lean_object* v___x_3757_; 
v_ipv4_3756_ = lean_ctor_get(v_host_3733_, 0);
lean_inc_ref(v_ipv4_3756_);
lean_dec_ref_known(v_host_3733_, 1);
v___x_3757_ = lean_uv_ntop_v4(v_ipv4_3756_);
lean_dec_ref(v_ipv4_3756_);
v___y_3744_ = v___y_3754_;
v___y_3745_ = v___x_3757_;
goto v___jp_3743_;
}
default: 
{
lean_object* v_ipv6_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v_ipv6_3758_ = lean_ctor_get(v_host_3733_, 0);
lean_inc_ref(v_ipv6_3758_);
lean_dec_ref_known(v_host_3733_, 1);
v___x_3759_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3760_ = lean_uv_ntop_v6(v_ipv6_3758_);
lean_dec_ref(v_ipv6_3758_);
v___x_3761_ = lean_string_append(v___x_3759_, v___x_3760_);
lean_dec_ref(v___x_3760_);
v___x_3762_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3763_ = lean_string_append(v___x_3761_, v___x_3762_);
v___y_3744_ = v___y_3754_;
v___y_3745_ = v___x_3763_;
goto v___jp_3743_;
}
}
}
}
v___jp_3697_:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3702_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3703_ = lean_string_append(v_scheme_3692_, v___x_3702_);
v___x_3704_ = lean_string_append(v___x_3703_, v___y_3698_);
lean_dec_ref(v___y_3698_);
v___x_3705_ = lean_string_append(v___x_3704_, v___y_3699_);
lean_dec_ref(v___y_3699_);
v___x_3706_ = lean_string_append(v___x_3705_, v___y_3700_);
lean_dec_ref(v___y_3700_);
v___x_3707_ = lean_string_append(v___x_3706_, v___y_3701_);
lean_dec_ref(v___y_3701_);
return v___x_3707_;
}
v___jp_3708_:
{
lean_object* v_queryPart_3711_; 
v_queryPart_3711_ = l_Std_Http_URI_Query_formatOption(v_query_3695_);
if (lean_obj_tag(v_fragment_3696_) == 0)
{
lean_object* v___x_3712_; 
v___x_3712_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3698_ = v___y_3709_;
v___y_3699_ = v___y_3710_;
v___y_3700_ = v_queryPart_3711_;
v___y_3701_ = v___x_3712_;
goto v___jp_3697_;
}
else
{
lean_object* v_val_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v_val_3713_ = lean_ctor_get(v_fragment_3696_, 0);
lean_inc(v_val_3713_);
lean_dec_ref_known(v_fragment_3696_, 1);
v___x_3714_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3715_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3713_);
lean_dec(v_val_3713_);
v___x_3716_ = lean_string_from_utf8_unchecked(v___x_3715_);
v___x_3717_ = lean_string_append(v___x_3714_, v___x_3716_);
lean_dec_ref(v___x_3716_);
v___y_3698_ = v___y_3709_;
v___y_3699_ = v___y_3710_;
v___y_3700_ = v_queryPart_3711_;
v___y_3701_ = v___x_3717_;
goto v___jp_3697_;
}
}
v___jp_3718_:
{
lean_object* v_segments_3720_; uint8_t v_absolute_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; size_t v_sz_3724_; size_t v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v_result_3728_; 
v_segments_3720_ = lean_ctor_get(v_path_3694_, 0);
lean_inc_ref(v_segments_3720_);
v_absolute_3721_ = lean_ctor_get_uint8(v_path_3694_, sizeof(void*)*1);
lean_dec_ref(v_path_3694_);
v___x_3722_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3723_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3724_ = lean_array_size(v_segments_3720_);
v___x_3725_ = ((size_t)0ULL);
v___x_3726_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3723_, v___f_3667_, v_sz_3724_, v___x_3725_, v_segments_3720_);
v___x_3727_ = lean_array_to_list(v___x_3726_);
v_result_3728_ = l_String_intercalate(v___x_3722_, v___x_3727_);
if (v_absolute_3721_ == 0)
{
v___y_3709_ = v___y_3719_;
v___y_3710_ = v_result_3728_;
goto v___jp_3708_;
}
else
{
lean_object* v___x_3729_; 
v___x_3729_ = lean_string_append(v___x_3722_, v_result_3728_);
lean_dec_ref(v_result_3728_);
v___y_3709_ = v___y_3719_;
v___y_3710_ = v___x_3729_;
goto v___jp_3708_;
}
}
}
case 2:
{
lean_object* v_authority_3780_; lean_object* v_userInfo_3781_; lean_object* v_host_3782_; lean_object* v_port_3783_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3795_; 
lean_dec_ref(v___f_3667_);
lean_dec_ref(v___f_3666_);
v_authority_3780_ = lean_ctor_get(v_x_3668_, 0);
lean_inc_ref(v_authority_3780_);
lean_dec_ref_known(v_x_3668_, 1);
v_userInfo_3781_ = lean_ctor_get(v_authority_3780_, 0);
lean_inc(v_userInfo_3781_);
v_host_3782_ = lean_ctor_get(v_authority_3780_, 1);
lean_inc_ref(v_host_3782_);
v_port_3783_ = lean_ctor_get(v_authority_3780_, 2);
lean_inc(v_port_3783_);
lean_dec_ref(v_authority_3780_);
if (lean_obj_tag(v_userInfo_3781_) == 0)
{
lean_object* v___x_3805_; 
v___x_3805_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3795_ = v___x_3805_;
goto v___jp_3794_;
}
else
{
lean_object* v_val_3806_; lean_object* v_password_3807_; 
v_val_3806_ = lean_ctor_get(v_userInfo_3781_, 0);
lean_inc(v_val_3806_);
lean_dec_ref_known(v_userInfo_3781_, 1);
v_password_3807_ = lean_ctor_get(v_val_3806_, 1);
if (lean_obj_tag(v_password_3807_) == 0)
{
lean_object* v_username_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; 
v_username_3808_ = lean_ctor_get(v_val_3806_, 0);
lean_inc_ref(v_username_3808_);
lean_dec(v_val_3806_);
v___x_3809_ = lean_string_from_utf8_unchecked(v_username_3808_);
v___x_3810_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3811_ = lean_string_append(v___x_3809_, v___x_3810_);
v___y_3795_ = v___x_3811_;
goto v___jp_3794_;
}
else
{
lean_object* v_username_3812_; lean_object* v_val_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
lean_inc_ref(v_password_3807_);
v_username_3812_ = lean_ctor_get(v_val_3806_, 0);
lean_inc_ref(v_username_3812_);
lean_dec(v_val_3806_);
v_val_3813_ = lean_ctor_get(v_password_3807_, 0);
lean_inc(v_val_3813_);
lean_dec_ref_known(v_password_3807_, 1);
v___x_3814_ = lean_string_from_utf8_unchecked(v_username_3812_);
v___x_3815_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3816_ = lean_string_append(v___x_3814_, v___x_3815_);
v___x_3817_ = lean_string_from_utf8_unchecked(v_val_3813_);
v___x_3818_ = lean_string_append(v___x_3816_, v___x_3817_);
lean_dec_ref(v___x_3817_);
v___x_3819_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3820_ = lean_string_append(v___x_3818_, v___x_3819_);
v___y_3795_ = v___x_3820_;
goto v___jp_3794_;
}
}
v___jp_3784_:
{
switch(lean_obj_tag(v_port_3783_))
{
case 0:
{
lean_object* v___x_3787_; 
v___x_3787_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3670_ = v___y_3786_;
v___y_3671_ = v___y_3785_;
v___y_3672_ = v___x_3787_;
goto v___jp_3669_;
}
case 1:
{
lean_object* v___x_3788_; 
v___x_3788_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3670_ = v___y_3786_;
v___y_3671_ = v___y_3785_;
v___y_3672_ = v___x_3788_;
goto v___jp_3669_;
}
default: 
{
uint16_t v_port_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v_port_3789_ = lean_ctor_get_uint16(v_port_3783_, 0);
lean_dec_ref_known(v_port_3783_, 0);
v___x_3790_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3791_ = lean_uint16_to_nat(v_port_3789_);
v___x_3792_ = l_Nat_reprFast(v___x_3791_);
v___x_3793_ = lean_string_append(v___x_3790_, v___x_3792_);
lean_dec_ref(v___x_3792_);
v___y_3670_ = v___y_3786_;
v___y_3671_ = v___y_3785_;
v___y_3672_ = v___x_3793_;
goto v___jp_3669_;
}
}
}
v___jp_3794_:
{
switch(lean_obj_tag(v_host_3782_))
{
case 0:
{
lean_object* v_name_3796_; 
v_name_3796_ = lean_ctor_get(v_host_3782_, 0);
lean_inc_ref(v_name_3796_);
lean_dec_ref_known(v_host_3782_, 1);
v___y_3785_ = v___y_3795_;
v___y_3786_ = v_name_3796_;
goto v___jp_3784_;
}
case 1:
{
lean_object* v_ipv4_3797_; lean_object* v___x_3798_; 
v_ipv4_3797_ = lean_ctor_get(v_host_3782_, 0);
lean_inc_ref(v_ipv4_3797_);
lean_dec_ref_known(v_host_3782_, 1);
v___x_3798_ = lean_uv_ntop_v4(v_ipv4_3797_);
lean_dec_ref(v_ipv4_3797_);
v___y_3785_ = v___y_3795_;
v___y_3786_ = v___x_3798_;
goto v___jp_3784_;
}
default: 
{
lean_object* v_ipv6_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v_ipv6_3799_ = lean_ctor_get(v_host_3782_, 0);
lean_inc_ref(v_ipv6_3799_);
lean_dec_ref_known(v_host_3782_, 1);
v___x_3800_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3801_ = lean_uv_ntop_v6(v_ipv6_3799_);
lean_dec_ref(v_ipv6_3799_);
v___x_3802_ = lean_string_append(v___x_3800_, v___x_3801_);
lean_dec_ref(v___x_3801_);
v___x_3803_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3804_ = lean_string_append(v___x_3802_, v___x_3803_);
v___y_3785_ = v___y_3795_;
v___y_3786_ = v___x_3804_;
goto v___jp_3784_;
}
}
}
}
default: 
{
lean_object* v___x_3821_; 
lean_dec_ref(v___f_3667_);
lean_dec_ref(v___f_3666_);
v___x_3821_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__2___closed__0));
return v___x_3821_;
}
}
v___jp_3669_:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = lean_string_append(v___y_3671_, v___y_3670_);
lean_dec_ref(v___y_3670_);
v___x_3674_ = lean_string_append(v___x_3673_, v___y_3672_);
lean_dec_ref(v___y_3672_);
return v___x_3674_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__2(lean_object* v___f_3825_, lean_object* v___f_3826_, lean_object* v_buffer_3827_, lean_object* v_target_3828_){
_start:
{
lean_object* v___y_3830_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; 
switch(lean_obj_tag(v_target_3828_))
{
case 0:
{
lean_object* v_path_3850_; lean_object* v_query_3851_; lean_object* v___y_3853_; lean_object* v_segments_3856_; uint8_t v_absolute_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; size_t v_sz_3860_; size_t v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v_result_3864_; 
lean_dec_ref(v___f_3826_);
v_path_3850_ = lean_ctor_get(v_target_3828_, 0);
lean_inc_ref(v_path_3850_);
v_query_3851_ = lean_ctor_get(v_target_3828_, 1);
lean_inc(v_query_3851_);
lean_dec_ref_known(v_target_3828_, 2);
v_segments_3856_ = lean_ctor_get(v_path_3850_, 0);
lean_inc_ref(v_segments_3856_);
v_absolute_3857_ = lean_ctor_get_uint8(v_path_3850_, sizeof(void*)*1);
lean_dec_ref(v_path_3850_);
v___x_3858_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3859_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3860_ = lean_array_size(v_segments_3856_);
v___x_3861_ = ((size_t)0ULL);
v___x_3862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3859_, v___f_3825_, v_sz_3860_, v___x_3861_, v_segments_3856_);
v___x_3863_ = lean_array_to_list(v___x_3862_);
v_result_3864_ = l_String_intercalate(v___x_3858_, v___x_3863_);
if (v_absolute_3857_ == 0)
{
v___y_3853_ = v_result_3864_;
goto v___jp_3852_;
}
else
{
lean_object* v___x_3865_; 
v___x_3865_ = lean_string_append(v___x_3858_, v_result_3864_);
lean_dec_ref(v_result_3864_);
v___y_3853_ = v___x_3865_;
goto v___jp_3852_;
}
v___jp_3852_:
{
lean_object* v_queryStr_3854_; lean_object* v___x_3855_; 
v_queryStr_3854_ = l_Std_Http_URI_Query_formatOption(v_query_3851_);
v___x_3855_ = lean_string_append(v___y_3853_, v_queryStr_3854_);
lean_dec_ref(v_queryStr_3854_);
v___y_3830_ = v___x_3855_;
goto v___jp_3829_;
}
}
case 1:
{
lean_object* v_uri_3866_; lean_object* v_scheme_3867_; lean_object* v_authority_3868_; lean_object* v_path_3869_; lean_object* v_query_3870_; lean_object* v_fragment_3871_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3894_; 
lean_dec_ref(v___f_3825_);
v_uri_3866_ = lean_ctor_get(v_target_3828_, 0);
lean_inc_ref(v_uri_3866_);
lean_dec_ref_known(v_target_3828_, 1);
v_scheme_3867_ = lean_ctor_get(v_uri_3866_, 0);
lean_inc_ref(v_scheme_3867_);
v_authority_3868_ = lean_ctor_get(v_uri_3866_, 1);
lean_inc(v_authority_3868_);
v_path_3869_ = lean_ctor_get(v_uri_3866_, 2);
lean_inc_ref(v_path_3869_);
v_query_3870_ = lean_ctor_get(v_uri_3866_, 3);
lean_inc(v_query_3870_);
v_fragment_3871_ = lean_ctor_get(v_uri_3866_, 4);
lean_inc(v_fragment_3871_);
lean_dec_ref(v_uri_3866_);
if (lean_obj_tag(v_authority_3868_) == 0)
{
lean_object* v___x_3905_; 
v___x_3905_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3894_ = v___x_3905_;
goto v___jp_3893_;
}
else
{
lean_object* v_val_3906_; lean_object* v_userInfo_3907_; lean_object* v_host_3908_; lean_object* v_port_3909_; lean_object* v___x_3910_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3929_; 
v_val_3906_ = lean_ctor_get(v_authority_3868_, 0);
lean_inc(v_val_3906_);
lean_dec_ref_known(v_authority_3868_, 1);
v_userInfo_3907_ = lean_ctor_get(v_val_3906_, 0);
lean_inc(v_userInfo_3907_);
v_host_3908_ = lean_ctor_get(v_val_3906_, 1);
lean_inc_ref(v_host_3908_);
v_port_3909_ = lean_ctor_get(v_val_3906_, 2);
lean_inc(v_port_3909_);
lean_dec(v_val_3906_);
v___x_3910_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3907_) == 0)
{
lean_object* v___x_3939_; 
v___x_3939_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3929_ = v___x_3939_;
goto v___jp_3928_;
}
else
{
lean_object* v_val_3940_; lean_object* v_password_3941_; 
v_val_3940_ = lean_ctor_get(v_userInfo_3907_, 0);
lean_inc(v_val_3940_);
lean_dec_ref_known(v_userInfo_3907_, 1);
v_password_3941_ = lean_ctor_get(v_val_3940_, 1);
if (lean_obj_tag(v_password_3941_) == 0)
{
lean_object* v_username_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v_username_3942_ = lean_ctor_get(v_val_3940_, 0);
lean_inc_ref(v_username_3942_);
lean_dec(v_val_3940_);
v___x_3943_ = lean_string_from_utf8_unchecked(v_username_3942_);
v___x_3944_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3945_ = lean_string_append(v___x_3943_, v___x_3944_);
v___y_3929_ = v___x_3945_;
goto v___jp_3928_;
}
else
{
lean_object* v_username_3946_; lean_object* v_val_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
lean_inc_ref(v_password_3941_);
v_username_3946_ = lean_ctor_get(v_val_3940_, 0);
lean_inc_ref(v_username_3946_);
lean_dec(v_val_3940_);
v_val_3947_ = lean_ctor_get(v_password_3941_, 0);
lean_inc(v_val_3947_);
lean_dec_ref_known(v_password_3941_, 1);
v___x_3948_ = lean_string_from_utf8_unchecked(v_username_3946_);
v___x_3949_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3950_ = lean_string_append(v___x_3948_, v___x_3949_);
v___x_3951_ = lean_string_from_utf8_unchecked(v_val_3947_);
v___x_3952_ = lean_string_append(v___x_3950_, v___x_3951_);
lean_dec_ref(v___x_3951_);
v___x_3953_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3954_ = lean_string_append(v___x_3952_, v___x_3953_);
v___y_3929_ = v___x_3954_;
goto v___jp_3928_;
}
}
v___jp_3911_:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3915_ = lean_string_append(v___y_3913_, v___y_3912_);
lean_dec_ref(v___y_3912_);
v___x_3916_ = lean_string_append(v___x_3915_, v___y_3914_);
lean_dec_ref(v___y_3914_);
v___x_3917_ = lean_string_append(v___x_3910_, v___x_3916_);
lean_dec_ref(v___x_3916_);
v___y_3894_ = v___x_3917_;
goto v___jp_3893_;
}
v___jp_3918_:
{
switch(lean_obj_tag(v_port_3909_))
{
case 0:
{
lean_object* v___x_3921_; 
v___x_3921_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3912_ = v___y_3920_;
v___y_3913_ = v___y_3919_;
v___y_3914_ = v___x_3921_;
goto v___jp_3911_;
}
case 1:
{
lean_object* v___x_3922_; 
v___x_3922_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3912_ = v___y_3920_;
v___y_3913_ = v___y_3919_;
v___y_3914_ = v___x_3922_;
goto v___jp_3911_;
}
default: 
{
uint16_t v_port_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v_port_3923_ = lean_ctor_get_uint16(v_port_3909_, 0);
lean_dec_ref_known(v_port_3909_, 0);
v___x_3924_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3925_ = lean_uint16_to_nat(v_port_3923_);
v___x_3926_ = l_Nat_reprFast(v___x_3925_);
v___x_3927_ = lean_string_append(v___x_3924_, v___x_3926_);
lean_dec_ref(v___x_3926_);
v___y_3912_ = v___y_3920_;
v___y_3913_ = v___y_3919_;
v___y_3914_ = v___x_3927_;
goto v___jp_3911_;
}
}
}
v___jp_3928_:
{
switch(lean_obj_tag(v_host_3908_))
{
case 0:
{
lean_object* v_name_3930_; 
v_name_3930_ = lean_ctor_get(v_host_3908_, 0);
lean_inc_ref(v_name_3930_);
lean_dec_ref_known(v_host_3908_, 1);
v___y_3919_ = v___y_3929_;
v___y_3920_ = v_name_3930_;
goto v___jp_3918_;
}
case 1:
{
lean_object* v_ipv4_3931_; lean_object* v___x_3932_; 
v_ipv4_3931_ = lean_ctor_get(v_host_3908_, 0);
lean_inc_ref(v_ipv4_3931_);
lean_dec_ref_known(v_host_3908_, 1);
v___x_3932_ = lean_uv_ntop_v4(v_ipv4_3931_);
lean_dec_ref(v_ipv4_3931_);
v___y_3919_ = v___y_3929_;
v___y_3920_ = v___x_3932_;
goto v___jp_3918_;
}
default: 
{
lean_object* v_ipv6_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v_ipv6_3933_ = lean_ctor_get(v_host_3908_, 0);
lean_inc_ref(v_ipv6_3933_);
lean_dec_ref_known(v_host_3908_, 1);
v___x_3934_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3935_ = lean_uv_ntop_v6(v_ipv6_3933_);
lean_dec_ref(v_ipv6_3933_);
v___x_3936_ = lean_string_append(v___x_3934_, v___x_3935_);
lean_dec_ref(v___x_3935_);
v___x_3937_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3938_ = lean_string_append(v___x_3936_, v___x_3937_);
v___y_3919_ = v___y_3929_;
v___y_3920_ = v___x_3938_;
goto v___jp_3918_;
}
}
}
}
v___jp_3872_:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3877_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3878_ = lean_string_append(v_scheme_3867_, v___x_3877_);
v___x_3879_ = lean_string_append(v___x_3878_, v___y_3874_);
lean_dec_ref(v___y_3874_);
v___x_3880_ = lean_string_append(v___x_3879_, v___y_3875_);
lean_dec_ref(v___y_3875_);
v___x_3881_ = lean_string_append(v___x_3880_, v___y_3873_);
lean_dec_ref(v___y_3873_);
v___x_3882_ = lean_string_append(v___x_3881_, v___y_3876_);
lean_dec_ref(v___y_3876_);
v___y_3830_ = v___x_3882_;
goto v___jp_3829_;
}
v___jp_3883_:
{
lean_object* v_queryPart_3886_; 
v_queryPart_3886_ = l_Std_Http_URI_Query_formatOption(v_query_3870_);
if (lean_obj_tag(v_fragment_3871_) == 0)
{
lean_object* v___x_3887_; 
v___x_3887_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3873_ = v_queryPart_3886_;
v___y_3874_ = v___y_3884_;
v___y_3875_ = v___y_3885_;
v___y_3876_ = v___x_3887_;
goto v___jp_3872_;
}
else
{
lean_object* v_val_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v_val_3888_ = lean_ctor_get(v_fragment_3871_, 0);
lean_inc(v_val_3888_);
lean_dec_ref_known(v_fragment_3871_, 1);
v___x_3889_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3890_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3888_);
lean_dec(v_val_3888_);
v___x_3891_ = lean_string_from_utf8_unchecked(v___x_3890_);
v___x_3892_ = lean_string_append(v___x_3889_, v___x_3891_);
lean_dec_ref(v___x_3891_);
v___y_3873_ = v_queryPart_3886_;
v___y_3874_ = v___y_3884_;
v___y_3875_ = v___y_3885_;
v___y_3876_ = v___x_3892_;
goto v___jp_3872_;
}
}
v___jp_3893_:
{
lean_object* v_segments_3895_; uint8_t v_absolute_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; size_t v_sz_3899_; size_t v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v_result_3903_; 
v_segments_3895_ = lean_ctor_get(v_path_3869_, 0);
lean_inc_ref(v_segments_3895_);
v_absolute_3896_ = lean_ctor_get_uint8(v_path_3869_, sizeof(void*)*1);
lean_dec_ref(v_path_3869_);
v___x_3897_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3898_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3899_ = lean_array_size(v_segments_3895_);
v___x_3900_ = ((size_t)0ULL);
v___x_3901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3898_, v___f_3826_, v_sz_3899_, v___x_3900_, v_segments_3895_);
v___x_3902_ = lean_array_to_list(v___x_3901_);
v_result_3903_ = l_String_intercalate(v___x_3897_, v___x_3902_);
if (v_absolute_3896_ == 0)
{
v___y_3884_ = v___y_3894_;
v___y_3885_ = v_result_3903_;
goto v___jp_3883_;
}
else
{
lean_object* v___x_3904_; 
v___x_3904_ = lean_string_append(v___x_3897_, v_result_3903_);
lean_dec_ref(v_result_3903_);
v___y_3884_ = v___y_3894_;
v___y_3885_ = v___x_3904_;
goto v___jp_3883_;
}
}
}
case 2:
{
lean_object* v_authority_3955_; lean_object* v_userInfo_3956_; lean_object* v_host_3957_; lean_object* v_port_3958_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3970_; 
lean_dec_ref(v___f_3826_);
lean_dec_ref(v___f_3825_);
v_authority_3955_ = lean_ctor_get(v_target_3828_, 0);
lean_inc_ref(v_authority_3955_);
lean_dec_ref_known(v_target_3828_, 1);
v_userInfo_3956_ = lean_ctor_get(v_authority_3955_, 0);
lean_inc(v_userInfo_3956_);
v_host_3957_ = lean_ctor_get(v_authority_3955_, 1);
lean_inc_ref(v_host_3957_);
v_port_3958_ = lean_ctor_get(v_authority_3955_, 2);
lean_inc(v_port_3958_);
lean_dec_ref(v_authority_3955_);
if (lean_obj_tag(v_userInfo_3956_) == 0)
{
lean_object* v___x_3980_; 
v___x_3980_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3970_ = v___x_3980_;
goto v___jp_3969_;
}
else
{
lean_object* v_val_3981_; lean_object* v_password_3982_; 
v_val_3981_ = lean_ctor_get(v_userInfo_3956_, 0);
lean_inc(v_val_3981_);
lean_dec_ref_known(v_userInfo_3956_, 1);
v_password_3982_ = lean_ctor_get(v_val_3981_, 1);
if (lean_obj_tag(v_password_3982_) == 0)
{
lean_object* v_username_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v_username_3983_ = lean_ctor_get(v_val_3981_, 0);
lean_inc_ref(v_username_3983_);
lean_dec(v_val_3981_);
v___x_3984_ = lean_string_from_utf8_unchecked(v_username_3983_);
v___x_3985_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3986_ = lean_string_append(v___x_3984_, v___x_3985_);
v___y_3970_ = v___x_3986_;
goto v___jp_3969_;
}
else
{
lean_object* v_username_3987_; lean_object* v_val_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
lean_inc_ref(v_password_3982_);
v_username_3987_ = lean_ctor_get(v_val_3981_, 0);
lean_inc_ref(v_username_3987_);
lean_dec(v_val_3981_);
v_val_3988_ = lean_ctor_get(v_password_3982_, 0);
lean_inc(v_val_3988_);
lean_dec_ref_known(v_password_3982_, 1);
v___x_3989_ = lean_string_from_utf8_unchecked(v_username_3987_);
v___x_3990_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3991_ = lean_string_append(v___x_3989_, v___x_3990_);
v___x_3992_ = lean_string_from_utf8_unchecked(v_val_3988_);
v___x_3993_ = lean_string_append(v___x_3991_, v___x_3992_);
lean_dec_ref(v___x_3992_);
v___x_3994_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3995_ = lean_string_append(v___x_3993_, v___x_3994_);
v___y_3970_ = v___x_3995_;
goto v___jp_3969_;
}
}
v___jp_3959_:
{
switch(lean_obj_tag(v_port_3958_))
{
case 0:
{
lean_object* v___x_3962_; 
v___x_3962_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3845_ = v___y_3961_;
v___y_3846_ = v___y_3960_;
v___y_3847_ = v___x_3962_;
goto v___jp_3844_;
}
case 1:
{
lean_object* v___x_3963_; 
v___x_3963_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3845_ = v___y_3961_;
v___y_3846_ = v___y_3960_;
v___y_3847_ = v___x_3963_;
goto v___jp_3844_;
}
default: 
{
uint16_t v_port_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v_port_3964_ = lean_ctor_get_uint16(v_port_3958_, 0);
lean_dec_ref_known(v_port_3958_, 0);
v___x_3965_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3966_ = lean_uint16_to_nat(v_port_3964_);
v___x_3967_ = l_Nat_reprFast(v___x_3966_);
v___x_3968_ = lean_string_append(v___x_3965_, v___x_3967_);
lean_dec_ref(v___x_3967_);
v___y_3845_ = v___y_3961_;
v___y_3846_ = v___y_3960_;
v___y_3847_ = v___x_3968_;
goto v___jp_3844_;
}
}
}
v___jp_3969_:
{
switch(lean_obj_tag(v_host_3957_))
{
case 0:
{
lean_object* v_name_3971_; 
v_name_3971_ = lean_ctor_get(v_host_3957_, 0);
lean_inc_ref(v_name_3971_);
lean_dec_ref_known(v_host_3957_, 1);
v___y_3960_ = v___y_3970_;
v___y_3961_ = v_name_3971_;
goto v___jp_3959_;
}
case 1:
{
lean_object* v_ipv4_3972_; lean_object* v___x_3973_; 
v_ipv4_3972_ = lean_ctor_get(v_host_3957_, 0);
lean_inc_ref(v_ipv4_3972_);
lean_dec_ref_known(v_host_3957_, 1);
v___x_3973_ = lean_uv_ntop_v4(v_ipv4_3972_);
lean_dec_ref(v_ipv4_3972_);
v___y_3960_ = v___y_3970_;
v___y_3961_ = v___x_3973_;
goto v___jp_3959_;
}
default: 
{
lean_object* v_ipv6_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v_ipv6_3974_ = lean_ctor_get(v_host_3957_, 0);
lean_inc_ref(v_ipv6_3974_);
lean_dec_ref_known(v_host_3957_, 1);
v___x_3975_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3976_ = lean_uv_ntop_v6(v_ipv6_3974_);
lean_dec_ref(v_ipv6_3974_);
v___x_3977_ = lean_string_append(v___x_3975_, v___x_3976_);
lean_dec_ref(v___x_3976_);
v___x_3978_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3979_ = lean_string_append(v___x_3977_, v___x_3978_);
v___y_3960_ = v___y_3970_;
v___y_3961_ = v___x_3979_;
goto v___jp_3959_;
}
}
}
}
default: 
{
lean_object* v___x_3996_; 
lean_dec_ref(v___f_3826_);
lean_dec_ref(v___f_3825_);
v___x_3996_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__2___closed__0));
v___y_3830_ = v___x_3996_;
goto v___jp_3829_;
}
}
v___jp_3829_:
{
lean_object* v_data_3831_; lean_object* v_size_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3843_; 
v_data_3831_ = lean_ctor_get(v_buffer_3827_, 0);
v_size_3832_ = lean_ctor_get(v_buffer_3827_, 1);
v_isSharedCheck_3843_ = !lean_is_exclusive(v_buffer_3827_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3834_ = v_buffer_3827_;
v_isShared_3835_ = v_isSharedCheck_3843_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_size_3832_);
lean_inc(v_data_3831_);
lean_dec(v_buffer_3827_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3843_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3841_; 
v___x_3836_ = lean_string_to_utf8(v___y_3830_);
lean_dec_ref(v___y_3830_);
lean_inc_ref(v___x_3836_);
v___x_3837_ = lean_array_push(v_data_3831_, v___x_3836_);
v___x_3838_ = lean_byte_array_size(v___x_3836_);
lean_dec_ref(v___x_3836_);
v___x_3839_ = lean_nat_add(v_size_3832_, v___x_3838_);
lean_dec(v_size_3832_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 1, v___x_3839_);
lean_ctor_set(v___x_3834_, 0, v___x_3837_);
v___x_3841_ = v___x_3834_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3837_);
lean_ctor_set(v_reuseFailAlloc_3842_, 1, v___x_3839_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
v___jp_3844_:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3848_ = lean_string_append(v___y_3846_, v___y_3845_);
lean_dec_ref(v___y_3845_);
v___x_3849_ = lean_string_append(v___x_3848_, v___y_3847_);
lean_dec_ref(v___y_3847_);
v___y_3830_ = v___x_3849_;
goto v___jp_3829_;
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
