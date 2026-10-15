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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
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
lean_object* v___x_80_; lean_object* v_lower_81_; uint8_t v___y_83_; uint8_t v___x_86_; 
v___x_80_ = lean_unsigned_to_nat(0u);
v_lower_81_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_79_, v___x_80_);
lean_inc_ref(v_lower_81_);
v___x_86_ = l_Std_Http_Internal_instDecidableIsLowerCase(v_lower_81_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; 
lean_dec_ref(v_lower_81_);
v___x_87_ = lean_box(0);
return v___x_87_;
}
else
{
lean_object* v___x_88_; uint8_t v___x_89_; 
lean_inc_ref(v_lower_81_);
v___x_88_ = l_String_toListImpl(v_lower_81_);
v___x_89_ = l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(v___x_88_);
if (v___x_89_ == 0)
{
lean_dec(v___x_88_);
v___y_83_ = v___x_89_;
goto v___jp_82_;
}
else
{
lean_object* v___x_90_; 
v___x_90_ = l_List_head_x3f___redArg(v___x_88_);
lean_dec(v___x_88_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v___x_91_; 
lean_dec_ref(v_lower_81_);
v___x_91_ = lean_box(0);
return v___x_91_;
}
else
{
lean_object* v_val_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_113_; 
v_val_92_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_113_ == 0)
{
v___x_94_ = v___x_90_;
v_isShared_95_ = v_isSharedCheck_113_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_val_92_);
lean_dec(v___x_90_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_113_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
uint32_t v___x_104_; uint32_t v___x_105_; uint8_t v___x_106_; 
v___x_104_ = 65;
v___x_105_ = lean_unbox_uint32(v_val_92_);
v___x_106_ = lean_uint32_dec_le(v___x_104_, v___x_105_);
if (v___x_106_ == 0)
{
lean_del_object(v___x_94_);
goto v___jp_96_;
}
else
{
uint32_t v___x_107_; uint32_t v___x_108_; uint8_t v___x_109_; 
v___x_107_ = 90;
v___x_108_ = lean_unbox_uint32(v_val_92_);
v___x_109_ = lean_uint32_dec_le(v___x_108_, v___x_107_);
if (v___x_109_ == 0)
{
lean_del_object(v___x_94_);
goto v___jp_96_;
}
else
{
lean_object* v___x_111_; 
lean_dec(v_val_92_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v_lower_81_);
v___x_111_ = v___x_94_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_lower_81_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
v___jp_96_:
{
uint32_t v___x_97_; uint32_t v___x_98_; uint8_t v___x_99_; 
v___x_97_ = 97;
v___x_98_ = lean_unbox_uint32(v_val_92_);
v___x_99_ = lean_uint32_dec_le(v___x_97_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec(v_val_92_);
lean_dec_ref(v_lower_81_);
v___x_100_ = lean_box(0);
return v___x_100_;
}
else
{
uint32_t v___x_101_; uint32_t v___x_102_; uint8_t v___x_103_; 
v___x_101_ = 122;
v___x_102_ = lean_unbox_uint32(v_val_92_);
lean_dec(v_val_92_);
v___x_103_ = lean_uint32_dec_le(v___x_102_, v___x_101_);
v___y_83_ = v___x_103_;
goto v___jp_82_;
}
}
}
}
}
}
v___jp_82_:
{
if (v___y_83_ == 0)
{
lean_object* v___x_84_; 
lean_dec_ref(v_lower_81_);
v___x_84_ = lean_box(0);
return v___x_84_;
}
else
{
lean_object* v___x_85_; 
v___x_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_85_, 0, v_lower_81_);
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(lean_object* v_msg_114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l_Std_Http_URI_instInhabitedScheme___closed__0));
v___x_116_ = lean_panic_fn_borrowed(v___x_115_, v_msg_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x21(lean_object* v_s_120_){
_start:
{
lean_object* v___x_121_; 
lean_inc_ref(v_s_120_);
v___x_121_ = l_Std_Http_URI_Scheme_ofString_x3f(v_s_120_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_122_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_123_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__1));
v___x_124_ = lean_unsigned_to_nat(84u);
v___x_125_ = lean_unsigned_to_nat(12u);
v___x_126_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_127_ = l_String_quote(v_s_120_);
v___x_128_ = lean_string_append(v___x_126_, v___x_127_);
lean_dec_ref(v___x_127_);
v___x_129_ = l_mkPanicMessageWithDecl(v___x_122_, v___x_123_, v___x_124_, v___x_125_, v___x_128_);
lean_dec_ref(v___x_128_);
v___x_130_ = l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(v___x_129_);
return v___x_130_;
}
else
{
lean_object* v_val_131_; 
lean_dec_ref(v_s_120_);
v_val_131_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_val_131_);
lean_dec_ref_known(v___x_121_, 1);
return v_val_131_;
}
}
}
LEAN_EXPORT uint16_t l_Std_Http_URI_Scheme_defaultPort(lean_object* v_scheme_133_){
_start:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___x_135_ = lean_string_dec_eq(v_scheme_133_, v___x_134_);
if (v___x_135_ == 0)
{
uint16_t v___x_136_; 
v___x_136_ = 80;
return v___x_136_;
}
else
{
uint16_t v___x_137_; 
v___x_137_ = 443;
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_defaultPort___boxed(lean_object* v_scheme_138_){
_start:
{
uint16_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_138_);
lean_dec_ref(v_scheme_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofPort(uint16_t v_port_141_){
_start:
{
uint16_t v___x_142_; uint8_t v___x_143_; 
v___x_142_ = 443;
v___x_143_ = lean_uint16_dec_eq(v_port_141_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = ((lean_object*)(l_Std_Http_URI_instInhabitedScheme___closed__0));
return v___x_144_;
}
else
{
lean_object* v___x_145_; 
v___x_145_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofPort___boxed(lean_object* v_port_146_){
_start:
{
uint16_t v_port_boxed_147_; lean_object* v_res_148_; 
v_port_boxed_147_ = lean_unbox(v_port_146_);
v_res_148_ = l_Std_Http_URI_Scheme_ofPort(v_port_boxed_147_);
return v_res_148_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__0(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_box(0);
v___x_150_ = l_ByteArray_empty;
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v___x_149_);
return v___x_151_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_obj_once(&l_Std_Http_URI_instInhabitedUserInfo_default___closed__0, &l_Std_Http_URI_instInhabitedUserInfo_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__0);
return v___x_152_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo(void){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Std_Http_URI_instInhabitedUserInfo_default;
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
if (lean_obj_tag(v_x_160_) == 0)
{
lean_object* v___x_162_; 
v___x_162_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_162_;
}
else
{
lean_object* v_val_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_175_; 
v_val_163_ = lean_ctor_get(v_x_160_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v_x_160_);
if (v_isSharedCheck_175_ == 0)
{
v___x_165_ = v_x_160_;
v_isShared_166_ = v_isSharedCheck_175_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_val_163_);
lean_dec(v_x_160_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_175_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_167_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_168_ = lean_string_from_utf8_unchecked(v_val_163_);
v___x_169_ = l_String_quote(v___x_168_);
if (v_isShared_166_ == 0)
{
lean_ctor_set_tag(v___x_165_, 3);
lean_ctor_set(v___x_165_, 0, v___x_169_);
v___x_171_ = v___x_165_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_174_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_167_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = l_Repr_addAppParen(v___x_172_, v_x_161_);
return v___x_173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___boxed(lean_object* v_x_176_, lean_object* v_x_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_x_176_, v_x_177_);
lean_dec(v_x_177_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_URI_instReprUserInfo_repr_spec__1(lean_object* v_a_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_nat_to_int(v_a_179_);
return v___x_180_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_unsigned_to_nat(12u);
v___x_195_ = lean_nat_to_int(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0));
v___x_204_ = lean_string_length(v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13);
v___x_206_ = lean_nat_to_int(v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg(lean_object* v_x_211_){
_start:
{
lean_object* v_username_212_; lean_object* v_password_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_248_; 
v_username_212_ = lean_ctor_get(v_x_211_, 0);
v_password_213_ = lean_ctor_get(v_x_211_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_211_);
if (v_isSharedCheck_248_ == 0)
{
v___x_215_ = v_x_211_;
v_isShared_216_ = v_isSharedCheck_248_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_password_213_);
lean_inc(v_username_212_);
lean_dec(v_x_211_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_248_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_217_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_218_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__6));
v___x_219_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_220_ = lean_string_from_utf8_unchecked(v_username_212_);
v___x_221_ = l_String_quote(v___x_220_);
v___x_222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
if (v_isShared_216_ == 0)
{
lean_ctor_set_tag(v___x_215_, 4);
lean_ctor_set(v___x_215_, 1, v___x_222_);
lean_ctor_set(v___x_215_, 0, v___x_219_);
v___x_224_ = v___x_215_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v___x_222_);
v___x_224_ = v_reuseFailAlloc_247_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_225_ = 0;
v___x_226_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*1, v___x_225_);
v___x_227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_218_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = lean_box(1);
v___x_231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__11));
v___x_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___x_217_);
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_password_213_, v___x_235_);
v___x_237_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_219_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set_uint8(v___x_238_, sizeof(void*)*1, v___x_225_);
v___x_239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_234_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_241_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___x_239_);
v___x_243_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_240_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*1, v___x_225_);
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr(lean_object* v_x_249_, lean_object* v_prec_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_x_249_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___boxed(lean_object* v_x_252_, lean_object* v_prec_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Std_Http_URI_instReprUserInfo_repr(v_x_252_, v_prec_253_);
lean_dec(v_prec_253_);
return v_res_254_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
if (lean_obj_tag(v_x_257_) == 0)
{
if (lean_obj_tag(v_x_258_) == 0)
{
uint8_t v___x_259_; 
v___x_259_ = 1;
return v___x_259_;
}
else
{
uint8_t v___x_260_; 
v___x_260_ = 0;
return v___x_260_;
}
}
else
{
if (lean_obj_tag(v_x_258_) == 0)
{
uint8_t v___x_261_; 
v___x_261_ = 0;
return v___x_261_;
}
else
{
lean_object* v_val_262_; lean_object* v_val_263_; uint8_t v___x_264_; 
v_val_262_ = lean_ctor_get(v_x_257_, 0);
v_val_263_ = lean_ctor_get(v_x_258_, 0);
v___x_264_ = lean_sarray_dec_eq(v_val_262_, v_val_263_);
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0___boxed(lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
uint8_t v_res_267_; lean_object* v_r_268_; 
v_res_267_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_x_265_, v_x_266_);
lean_dec(v_x_266_);
lean_dec(v_x_265_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqUserInfo_beq(lean_object* v_x_269_, lean_object* v_x_270_){
_start:
{
lean_object* v_username_271_; lean_object* v_password_272_; lean_object* v_username_273_; lean_object* v_password_274_; uint8_t v___x_275_; 
v_username_271_ = lean_ctor_get(v_x_269_, 0);
v_password_272_ = lean_ctor_get(v_x_269_, 1);
v_username_273_ = lean_ctor_get(v_x_270_, 0);
v_password_274_ = lean_ctor_get(v_x_270_, 1);
v___x_275_ = lean_sarray_dec_eq(v_username_271_, v_username_273_);
if (v___x_275_ == 0)
{
return v___x_275_;
}
else
{
uint8_t v___x_276_; 
v___x_276_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_password_272_, v_password_274_);
return v___x_276_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqUserInfo_beq___boxed(lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Std_Http_URI_instBEqUserInfo_beq(v_x_277_, v_x_278_);
lean_dec_ref(v_x_278_);
lean_dec_ref(v_x_277_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings(lean_object* v_username_283_, lean_object* v_password_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_283_);
if (lean_obj_tag(v_password_284_) == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_box(0);
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
return v___x_287_;
}
else
{
lean_object* v_val_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_297_; 
v_val_288_ = lean_ctor_get(v_password_284_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v_password_284_);
if (v_isSharedCheck_297_ == 0)
{
v___x_290_ = v_password_284_;
v_isShared_291_ = v_isSharedCheck_297_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_val_288_);
lean_dec(v_password_284_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_297_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_288_);
lean_dec(v_val_288_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_292_);
v___x_294_ = v___x_290_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_296_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; 
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_285_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
return v___x_295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings___boxed(lean_object* v_username_298_, lean_object* v_password_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_Http_URI_UserInfo_ofStrings(v_username_298_, v_password_299_);
lean_dec_ref(v_username_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f(lean_object* v_ui_301_){
_start:
{
lean_object* v_username_302_; lean_object* v___x_303_; 
v_username_302_ = lean_ctor_get(v_ui_301_, 0);
v___x_303_ = l_Std_Http_URI_EncodedUserInfo_decode(v_username_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f___boxed(lean_object* v_ui_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Std_Http_URI_UserInfo_username_x3f(v_ui_304_);
lean_dec_ref(v_ui_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f(lean_object* v_ui_306_){
_start:
{
lean_object* v_password_307_; 
v_password_307_ = lean_ctor_get(v_ui_306_, 1);
if (lean_obj_tag(v_password_307_) == 0)
{
lean_object* v___x_308_; 
v___x_308_ = lean_box(0);
return v___x_308_;
}
else
{
lean_object* v_val_309_; lean_object* v___x_310_; 
v_val_309_ = lean_ctor_get(v_password_307_, 0);
v___x_310_ = l_Std_Http_URI_EncodedUserInfo_decode(v_val_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f___boxed(lean_object* v_ui_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_Http_URI_UserInfo_password_x3f(v_ui_311_);
lean_dec_ref(v_ui_311_);
return v_res_312_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(lean_object* v_x_313_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
uint8_t v___x_314_; 
v___x_314_ = 1;
return v___x_314_;
}
else
{
lean_object* v_head_315_; lean_object* v_tail_316_; uint32_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v_head_315_ = lean_ctor_get(v_x_313_, 0);
v_tail_316_ = lean_ctor_get(v_x_313_, 1);
v___x_338_ = lean_unbox_uint32(v_head_315_);
v___x_339_ = lean_uint32_to_nat(v___x_338_);
v___x_340_ = lean_unsigned_to_nat(128u);
v___x_341_ = lean_nat_dec_lt(v___x_339_, v___x_340_);
lean_dec(v___x_339_);
if (v___x_341_ == 0)
{
goto v___jp_317_;
}
else
{
uint32_t v___x_342_; uint32_t v___x_343_; uint8_t v___x_344_; 
v___x_342_ = 48;
v___x_343_ = lean_unbox_uint32(v_head_315_);
v___x_344_ = lean_uint32_dec_le(v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
goto v___jp_330_;
}
else
{
uint32_t v___x_345_; uint32_t v___x_346_; uint8_t v___x_347_; 
v___x_345_ = 57;
v___x_346_ = lean_unbox_uint32(v_head_315_);
v___x_347_ = lean_uint32_dec_le(v___x_346_, v___x_345_);
if (v___x_347_ == 0)
{
goto v___jp_330_;
}
else
{
v_x_313_ = v_tail_316_;
goto _start;
}
}
}
v___jp_317_:
{
uint32_t v___x_318_; uint32_t v___x_319_; uint8_t v___x_320_; 
v___x_318_ = 45;
v___x_319_ = lean_unbox_uint32(v_head_315_);
v___x_320_ = lean_uint32_dec_eq(v___x_319_, v___x_318_);
if (v___x_320_ == 0)
{
return v___x_320_;
}
else
{
v_x_313_ = v_tail_316_;
goto _start;
}
}
v___jp_322_:
{
uint32_t v___x_323_; uint32_t v___x_324_; uint8_t v___x_325_; 
v___x_323_ = 97;
v___x_324_ = lean_unbox_uint32(v_head_315_);
v___x_325_ = lean_uint32_dec_le(v___x_323_, v___x_324_);
if (v___x_325_ == 0)
{
goto v___jp_317_;
}
else
{
uint32_t v___x_326_; uint32_t v___x_327_; uint8_t v___x_328_; 
v___x_326_ = 122;
v___x_327_ = lean_unbox_uint32(v_head_315_);
v___x_328_ = lean_uint32_dec_le(v___x_327_, v___x_326_);
if (v___x_328_ == 0)
{
goto v___jp_317_;
}
else
{
v_x_313_ = v_tail_316_;
goto _start;
}
}
}
v___jp_330_:
{
uint32_t v___x_331_; uint32_t v___x_332_; uint8_t v___x_333_; 
v___x_331_ = 65;
v___x_332_ = lean_unbox_uint32(v_head_315_);
v___x_333_ = lean_uint32_dec_le(v___x_331_, v___x_332_);
if (v___x_333_ == 0)
{
goto v___jp_322_;
}
else
{
uint32_t v___x_334_; uint32_t v___x_335_; uint8_t v___x_336_; 
v___x_334_ = 90;
v___x_335_ = lean_unbox_uint32(v_head_315_);
v___x_336_ = lean_uint32_dec_le(v___x_335_, v___x_334_);
if (v___x_336_ == 0)
{
goto v___jp_322_;
}
else
{
v_x_313_ = v_tail_316_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0___boxed(lean_object* v_x_349_){
_start:
{
uint8_t v_res_350_; lean_object* v_r_351_; 
v_res_350_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v_x_349_);
lean_dec(v_x_349_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object* v_s_352_){
_start:
{
uint32_t v___y_354_; uint32_t v___y_360_; lean_object* v_chars_365_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v_chars_365_ = l_String_toListImpl(v_s_352_);
v___x_382_ = l_List_lengthTR___redArg(v_chars_365_);
v___x_383_ = lean_unsigned_to_nat(63u);
v___x_384_ = lean_nat_dec_le(v___x_382_, v___x_383_);
lean_dec(v___x_382_);
if (v___x_384_ == 0)
{
lean_dec(v_chars_365_);
return v___x_384_;
}
else
{
uint8_t v___x_385_; 
v___x_385_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v_chars_365_);
if (v___x_385_ == 0)
{
lean_dec(v_chars_365_);
return v___x_385_;
}
else
{
lean_object* v___x_386_; 
v___x_386_ = l_List_head_x3f___redArg(v_chars_365_);
if (lean_obj_tag(v___x_386_) == 0)
{
uint8_t v___x_387_; 
lean_dec(v_chars_365_);
v___x_387_ = 0;
return v___x_387_;
}
else
{
lean_object* v_val_388_; uint32_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v_val_388_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_val_388_);
lean_dec_ref_known(v___x_386_, 1);
v___x_403_ = lean_unbox_uint32(v_val_388_);
v___x_404_ = lean_uint32_to_nat(v___x_403_);
v___x_405_ = lean_unsigned_to_nat(128u);
v___x_406_ = lean_nat_dec_lt(v___x_404_, v___x_405_);
lean_dec(v___x_404_);
if (v___x_406_ == 0)
{
lean_dec(v_val_388_);
lean_dec(v_chars_365_);
return v___x_406_;
}
else
{
uint32_t v___x_407_; uint32_t v___x_408_; uint8_t v___x_409_; 
v___x_407_ = 48;
v___x_408_ = lean_unbox_uint32(v_val_388_);
v___x_409_ = lean_uint32_dec_le(v___x_407_, v___x_408_);
if (v___x_409_ == 0)
{
goto v___jp_396_;
}
else
{
uint32_t v___x_410_; uint32_t v___x_411_; uint8_t v___x_412_; 
v___x_410_ = 57;
v___x_411_ = lean_unbox_uint32(v_val_388_);
v___x_412_ = lean_uint32_dec_le(v___x_411_, v___x_410_);
if (v___x_412_ == 0)
{
goto v___jp_396_;
}
else
{
lean_dec(v_val_388_);
goto v___jp_366_;
}
}
}
v___jp_389_:
{
uint32_t v___x_390_; uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_390_ = 97;
v___x_391_ = lean_unbox_uint32(v_val_388_);
v___x_392_ = lean_uint32_dec_le(v___x_390_, v___x_391_);
if (v___x_392_ == 0)
{
lean_dec(v_val_388_);
lean_dec(v_chars_365_);
return v___x_392_;
}
else
{
uint32_t v___x_393_; uint32_t v___x_394_; uint8_t v___x_395_; 
v___x_393_ = 122;
v___x_394_ = lean_unbox_uint32(v_val_388_);
lean_dec(v_val_388_);
v___x_395_ = lean_uint32_dec_le(v___x_394_, v___x_393_);
if (v___x_395_ == 0)
{
lean_dec(v_chars_365_);
return v___x_395_;
}
else
{
goto v___jp_366_;
}
}
}
v___jp_396_:
{
uint32_t v___x_397_; uint32_t v___x_398_; uint8_t v___x_399_; 
v___x_397_ = 65;
v___x_398_ = lean_unbox_uint32(v_val_388_);
v___x_399_ = lean_uint32_dec_le(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
goto v___jp_389_;
}
else
{
uint32_t v___x_400_; uint32_t v___x_401_; uint8_t v___x_402_; 
v___x_400_ = 90;
v___x_401_ = lean_unbox_uint32(v_val_388_);
v___x_402_ = lean_uint32_dec_le(v___x_401_, v___x_400_);
if (v___x_402_ == 0)
{
goto v___jp_389_;
}
else
{
lean_dec(v_val_388_);
goto v___jp_366_;
}
}
}
}
}
}
v___jp_353_:
{
uint32_t v___x_355_; uint8_t v___x_356_; 
v___x_355_ = 97;
v___x_356_ = lean_uint32_dec_le(v___x_355_, v___y_354_);
if (v___x_356_ == 0)
{
return v___x_356_;
}
else
{
uint32_t v___x_357_; uint8_t v___x_358_; 
v___x_357_ = 122;
v___x_358_ = lean_uint32_dec_le(v___y_354_, v___x_357_);
return v___x_358_;
}
}
v___jp_359_:
{
uint32_t v___x_361_; uint8_t v___x_362_; 
v___x_361_ = 65;
v___x_362_ = lean_uint32_dec_le(v___x_361_, v___y_360_);
if (v___x_362_ == 0)
{
v___y_354_ = v___y_360_;
goto v___jp_353_;
}
else
{
uint32_t v___x_363_; uint8_t v___x_364_; 
v___x_363_ = 90;
v___x_364_ = lean_uint32_dec_le(v___y_360_, v___x_363_);
if (v___x_364_ == 0)
{
v___y_354_ = v___y_360_;
goto v___jp_353_;
}
else
{
return v___x_364_;
}
}
}
v___jp_366_:
{
lean_object* v___x_367_; 
v___x_367_ = l_List_getLast_x3f___redArg(v_chars_365_);
lean_dec(v_chars_365_);
if (lean_obj_tag(v___x_367_) == 0)
{
uint8_t v___x_368_; 
v___x_368_ = 0;
return v___x_368_;
}
else
{
lean_object* v_val_369_; uint32_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v_val_369_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_val_369_);
lean_dec_ref_known(v___x_367_, 1);
v___x_370_ = lean_unbox_uint32(v_val_369_);
v___x_371_ = lean_uint32_to_nat(v___x_370_);
v___x_372_ = lean_unsigned_to_nat(128u);
v___x_373_ = lean_nat_dec_lt(v___x_371_, v___x_372_);
lean_dec(v___x_371_);
if (v___x_373_ == 0)
{
lean_dec(v_val_369_);
return v___x_373_;
}
else
{
uint32_t v___x_374_; uint32_t v___x_375_; uint8_t v___x_376_; 
v___x_374_ = 48;
v___x_375_ = lean_unbox_uint32(v_val_369_);
v___x_376_ = lean_uint32_dec_le(v___x_374_, v___x_375_);
if (v___x_376_ == 0)
{
uint32_t v___x_377_; 
v___x_377_ = lean_unbox_uint32(v_val_369_);
lean_dec(v_val_369_);
v___y_360_ = v___x_377_;
goto v___jp_359_;
}
else
{
uint32_t v___x_378_; uint32_t v___x_379_; uint8_t v___x_380_; 
v___x_378_ = 57;
v___x_379_ = lean_unbox_uint32(v_val_369_);
v___x_380_ = lean_uint32_dec_le(v___x_379_, v___x_378_);
if (v___x_380_ == 0)
{
uint32_t v___x_381_; 
v___x_381_ = lean_unbox_uint32(v_val_369_);
lean_dec(v_val_369_);
v___y_360_ = v___x_381_;
goto v___jp_359_;
}
else
{
lean_dec(v_val_369_);
return v___x_380_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidDomainLabel___boxed(lean_object* v_s_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_Std_Http_URI_isValidDomainLabel(v_s_413_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg(){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___closed__0));
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___boxed(lean_object* v___dummy_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg();
return v_res_421_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg();
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(lean_object* v_s_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___boxed(lean_object* v_s_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(v_s_425_);
lean_dec_ref(v_s_425_);
return v_res_426_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(uint8_t v___x_427_, lean_object* v_lower_428_, lean_object* v___x_429_, lean_object* v___x_430_, lean_object* v_a_431_, uint8_t v_b_432_){
_start:
{
uint8_t v___y_434_; lean_object* v_it_435_; lean_object* v_startInclusive_436_; lean_object* v_endExclusive_437_; uint8_t v___y_442_; 
if (v___x_427_ == 0)
{
uint8_t v___x_468_; 
v___x_468_ = 1;
v___y_442_ = v___x_468_;
goto v___jp_441_;
}
else
{
uint8_t v___x_469_; 
v___x_469_ = 0;
v___y_442_ = v___x_469_;
goto v___jp_441_;
}
v___jp_433_:
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_string_utf8_extract_fast(v_lower_428_, v_startInclusive_436_, v_endExclusive_437_);
lean_dec(v_endExclusive_437_);
lean_dec(v_startInclusive_436_);
v___x_439_ = l_Std_Http_URI_isValidDomainLabel(v___x_438_);
if (v___x_439_ == 0)
{
lean_dec(v_it_435_);
lean_dec(v___x_430_);
return v___x_439_;
}
else
{
v_a_431_ = v_it_435_;
v_b_432_ = v___y_434_;
goto _start;
}
}
v___jp_441_:
{
if (lean_obj_tag(v_a_431_) == 0)
{
lean_object* v_currPos_443_; lean_object* v_searcher_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_467_; 
v_currPos_443_ = lean_ctor_get(v_a_431_, 0);
v_searcher_444_ = lean_ctor_get(v_a_431_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_a_431_);
if (v_isSharedCheck_467_ == 0)
{
v___x_446_ = v_a_431_;
v_isShared_447_ = v_isSharedCheck_467_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_searcher_444_);
lean_inc(v_currPos_443_);
lean_dec(v_a_431_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_467_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
uint8_t v_decide_448_; 
v_decide_448_ = lean_nat_dec_eq(v_searcher_444_, v___x_430_);
if (v_decide_448_ == 0)
{
uint32_t v___x_449_; uint32_t v___x_450_; uint8_t v___x_451_; 
v___x_449_ = 46;
v___x_450_ = lean_string_utf8_get_fast(v_lower_428_, v_searcher_444_);
v___x_451_ = lean_uint32_dec_eq(v___x_450_, v___x_449_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_452_ = lean_string_utf8_next_fast(v_lower_428_, v_searcher_444_);
lean_dec(v_searcher_444_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v___x_452_);
v___x_454_ = v___x_446_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_currPos_443_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_452_);
v___x_454_ = v_reuseFailAlloc_456_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
v_a_431_ = v___x_454_;
goto _start;
}
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v_slice_460_; lean_object* v_nextIt_462_; 
v___x_457_ = lean_string_utf8_next_fast(v_lower_428_, v_searcher_444_);
v___x_458_ = lean_nat_sub(v___x_457_, v_searcher_444_);
v___x_459_ = lean_nat_add(v_searcher_444_, v___x_458_);
lean_dec(v___x_458_);
v_slice_460_ = l_String_Slice_subslice_x21(v___x_429_, v_currPos_443_, v_searcher_444_);
lean_inc(v___x_459_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v___x_459_);
lean_ctor_set(v___x_446_, 0, v___x_459_);
v_nextIt_462_ = v___x_446_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_459_);
v_nextIt_462_ = v_reuseFailAlloc_465_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v_startInclusive_463_; lean_object* v_endExclusive_464_; 
v_startInclusive_463_ = lean_ctor_get(v_slice_460_, 0);
lean_inc(v_startInclusive_463_);
v_endExclusive_464_ = lean_ctor_get(v_slice_460_, 1);
lean_inc(v_endExclusive_464_);
lean_dec_ref(v_slice_460_);
v___y_434_ = v___y_442_;
v_it_435_ = v_nextIt_462_;
v_startInclusive_436_ = v_startInclusive_463_;
v_endExclusive_437_ = v_endExclusive_464_;
goto v___jp_433_;
}
}
}
else
{
lean_object* v___x_466_; 
lean_del_object(v___x_446_);
lean_dec(v_searcher_444_);
v___x_466_ = lean_box(1);
lean_inc(v___x_430_);
v___y_434_ = v___y_442_;
v_it_435_ = v___x_466_;
v_startInclusive_436_ = v_currPos_443_;
v_endExclusive_437_ = v___x_430_;
goto v___jp_433_;
}
}
}
else
{
lean_dec(v___x_430_);
return v_b_432_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg___boxed(lean_object* v___x_470_, lean_object* v_lower_471_, lean_object* v___x_472_, lean_object* v___x_473_, lean_object* v_a_474_, lean_object* v_b_475_){
_start:
{
uint8_t v___x_3750__boxed_476_; uint8_t v_b_boxed_477_; uint8_t v_res_478_; lean_object* v_r_479_; 
v___x_3750__boxed_476_ = lean_unbox(v___x_470_);
v_b_boxed_477_ = lean_unbox(v_b_475_);
v_res_478_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_3750__boxed_476_, v_lower_471_, v___x_472_, v___x_473_, v_a_474_, v_b_boxed_477_);
lean_dec_ref(v___x_472_);
lean_dec_ref(v_lower_471_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(lean_object* v___x_480_, lean_object* v_lower_481_, lean_object* v___x_482_, lean_object* v_a_483_, uint8_t v_b_484_){
_start:
{
if (lean_obj_tag(v_a_483_) == 0)
{
lean_object* v_currPos_485_; lean_object* v_searcher_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_501_; 
v_currPos_485_ = lean_ctor_get(v_a_483_, 0);
v_searcher_486_ = lean_ctor_get(v_a_483_, 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v_a_483_);
if (v_isSharedCheck_501_ == 0)
{
v___x_488_ = v_a_483_;
v_isShared_489_ = v_isSharedCheck_501_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_searcher_486_);
lean_inc(v_currPos_485_);
lean_dec(v_a_483_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_501_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; uint8_t v___x_491_; uint8_t v_decide_492_; 
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = lean_nat_dec_eq(v___x_480_, v___x_490_);
v_decide_492_ = lean_nat_dec_eq(v_searcher_486_, v___x_482_);
if (v_decide_492_ == 0)
{
uint32_t v___x_493_; uint32_t v___x_494_; uint8_t v___x_495_; 
v___x_493_ = 46;
v___x_494_ = lean_string_utf8_get_fast(v_lower_481_, v_searcher_486_);
v___x_495_ = lean_uint32_dec_eq(v___x_494_, v___x_493_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_496_ = lean_string_utf8_next_fast(v_lower_481_, v_searcher_486_);
lean_dec(v_searcher_486_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_496_);
v___x_498_ = v___x_488_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_currPos_485_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v___x_496_);
v___x_498_ = v_reuseFailAlloc_500_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
v_a_483_ = v___x_498_;
goto _start;
}
}
else
{
lean_del_object(v___x_488_);
lean_dec(v_searcher_486_);
lean_dec(v_currPos_485_);
return v___x_491_;
}
}
else
{
lean_del_object(v___x_488_);
lean_dec(v_searcher_486_);
lean_dec(v_currPos_485_);
return v___x_491_;
}
}
}
else
{
return v_b_484_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg___boxed(lean_object* v___x_502_, lean_object* v_lower_503_, lean_object* v___x_504_, lean_object* v_a_505_, lean_object* v_b_506_){
_start:
{
uint8_t v_b_boxed_507_; uint8_t v_res_508_; lean_object* v_r_509_; 
v_b_boxed_507_ = lean_unbox(v_b_506_);
v_res_508_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_502_, v_lower_503_, v___x_504_, v_a_505_, v_b_boxed_507_);
lean_dec(v___x_504_);
lean_dec_ref(v_lower_503_);
lean_dec(v___x_502_);
v_r_509_ = lean_box(v_res_508_);
return v_r_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_DomainName_ofString_x3f(lean_object* v_s_510_){
_start:
{
lean_object* v___x_511_; lean_object* v_lower_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_511_ = lean_unsigned_to_nat(0u);
v_lower_512_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_510_, v___x_511_);
v___x_513_ = lean_string_utf8_byte_size(v_lower_512_);
v___x_514_ = lean_nat_dec_eq(v___x_513_, v___x_511_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; uint8_t v___x_518_; uint8_t v___y_520_; 
lean_inc_ref(v_lower_512_);
v___x_515_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_515_, 0, v_lower_512_);
lean_ctor_set(v___x_515_, 1, v___x_511_);
lean_ctor_set(v___x_515_, 2, v___x_513_);
v___x_516_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0);
v___x_517_ = 1;
v___x_518_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_513_, v_lower_512_, v___x_513_, v___x_516_, v___x_517_);
if (v___x_518_ == 0)
{
v___y_520_ = v___x_517_;
goto v___jp_519_;
}
else
{
if (v___x_514_ == 0)
{
lean_object* v___x_528_; 
lean_dec_ref_known(v___x_515_, 3);
lean_dec_ref(v_lower_512_);
v___x_528_ = lean_box(0);
return v___x_528_;
}
else
{
v___y_520_ = v___x_514_;
goto v___jp_519_;
}
}
v___jp_519_:
{
uint8_t v___x_521_; 
v___x_521_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_518_, v_lower_512_, v___x_515_, v___x_513_, v___x_516_, v___y_520_);
lean_dec_ref_known(v___x_515_, 3);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
lean_dec_ref(v_lower_512_);
v___x_522_ = lean_box(0);
return v___x_522_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_523_ = lean_string_length(v_lower_512_);
v___x_524_ = lean_unsigned_to_nat(255u);
v___x_525_ = lean_nat_dec_le(v___x_523_, v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; 
lean_dec_ref(v_lower_512_);
v___x_526_ = lean_box(0);
return v___x_526_;
}
else
{
lean_object* v___x_527_; 
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v_lower_512_);
return v___x_527_;
}
}
}
}
else
{
lean_object* v___x_529_; 
lean_dec_ref(v_lower_512_);
v___x_529_ = lean_box(0);
return v___x_529_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(lean_object* v___x_530_, lean_object* v_lower_531_, lean_object* v___x_532_, lean_object* v___x_533_, lean_object* v_inst_534_, lean_object* v_R_535_, lean_object* v_a_536_, uint8_t v_b_537_, lean_object* v_c_538_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_530_, v_lower_531_, v___x_533_, v_a_536_, v_b_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___boxed(lean_object* v___x_540_, lean_object* v_lower_541_, lean_object* v___x_542_, lean_object* v___x_543_, lean_object* v_inst_544_, lean_object* v_R_545_, lean_object* v_a_546_, lean_object* v_b_547_, lean_object* v_c_548_){
_start:
{
uint8_t v_b_boxed_549_; uint8_t v_res_550_; lean_object* v_r_551_; 
v_b_boxed_549_ = lean_unbox(v_b_547_);
v_res_550_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(v___x_540_, v_lower_541_, v___x_542_, v___x_543_, v_inst_544_, v_R_545_, v_a_546_, v_b_boxed_549_, v_c_548_);
lean_dec(v___x_543_);
lean_dec_ref(v___x_542_);
lean_dec_ref(v_lower_541_);
lean_dec(v___x_540_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(uint8_t v___x_552_, lean_object* v_lower_553_, lean_object* v___x_554_, lean_object* v___x_555_, lean_object* v_inst_556_, lean_object* v_R_557_, lean_object* v_a_558_, uint8_t v_b_559_, lean_object* v_c_560_){
_start:
{
uint8_t v___x_561_; 
v___x_561_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_552_, v_lower_553_, v___x_554_, v___x_555_, v_a_558_, v_b_559_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___boxed(lean_object* v___x_562_, lean_object* v_lower_563_, lean_object* v___x_564_, lean_object* v___x_565_, lean_object* v_inst_566_, lean_object* v_R_567_, lean_object* v_a_568_, lean_object* v_b_569_, lean_object* v_c_570_){
_start:
{
uint8_t v___x_3912__boxed_571_; uint8_t v_b_boxed_572_; uint8_t v_res_573_; lean_object* v_r_574_; 
v___x_3912__boxed_571_ = lean_unbox(v___x_562_);
v_b_boxed_572_ = lean_unbox(v_b_569_);
v_res_573_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(v___x_3912__boxed_571_, v_lower_563_, v___x_564_, v___x_565_, v_inst_566_, v_R_567_, v_a_568_, v_b_boxed_572_, v_c_570_);
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
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqHost_beq(lean_object* v_x_623_, lean_object* v_x_624_){
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
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqHost_beq___boxed(lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
uint8_t v_res_639_; lean_object* v_r_640_; 
v_res_639_ = l_Std_Http_URI_instBEqHost_beq(v_x_637_, v_x_638_);
lean_dec_ref(v_x_638_);
lean_dec_ref(v_x_637_);
v_r_640_ = lean_box(v_res_639_);
return v_r_640_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__4(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_unsigned_to_nat(2u);
v___x_648_ = lean_nat_to_int(v___x_647_);
return v___x_648_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__5(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_to_int(v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0(lean_object* v_x_651_, lean_object* v_prec_652_){
_start:
{
lean_object* v___y_654_; lean_object* v_ctr_655_; lean_object* v_a_656_; lean_object* v___y_668_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = lean_unsigned_to_nat(1024u);
v___x_700_ = lean_nat_dec_le(v___x_699_, v_prec_652_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
v___x_701_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_668_ = v___x_701_;
goto v___jp_667_;
}
else
{
lean_object* v___x_702_; 
v___x_702_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_668_ = v___x_702_;
goto v___jp_667_;
}
v___jp_653_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_657_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_658_ = lean_string_append(v___x_657_, v_ctr_655_);
v___x_659_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
v___x_660_ = lean_box(1);
v___x_661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v_a_656_);
lean_inc(v___y_654_);
v___x_663_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_663_, 0, v___y_654_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = 0;
v___x_665_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*1, v___x_664_);
v___x_666_ = l_Repr_addAppParen(v___x_665_, v_prec_652_);
return v___x_666_;
}
v___jp_667_:
{
switch(lean_obj_tag(v_x_651_))
{
case 0:
{
lean_object* v_name_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_678_; 
v_name_669_ = lean_ctor_get(v_x_651_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v_x_651_);
if (v_isSharedCheck_678_ == 0)
{
v___x_671_ = v_x_651_;
v_isShared_672_ = v_isSharedCheck_678_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_name_669_);
lean_dec(v_x_651_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_678_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_673_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_674_ = l_String_quote(v_name_669_);
if (v_isShared_672_ == 0)
{
lean_ctor_set_tag(v___x_671_, 3);
lean_ctor_set(v___x_671_, 0, v___x_674_);
v___x_676_ = v___x_671_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
v___y_654_ = v___y_668_;
v_ctr_655_ = v___x_673_;
v_a_656_ = v___x_676_;
goto v___jp_653_;
}
}
}
case 1:
{
lean_object* v_ipv4_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_688_; 
v_ipv4_679_ = lean_ctor_get(v_x_651_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v_x_651_);
if (v_isSharedCheck_688_ == 0)
{
v___x_681_ = v_x_651_;
v_isShared_682_ = v_isSharedCheck_688_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_ipv4_679_);
lean_dec(v_x_651_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_688_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_683_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_684_ = lean_uv_ntop_v4(v_ipv4_679_);
lean_dec_ref(v_ipv4_679_);
if (v_isShared_682_ == 0)
{
lean_ctor_set_tag(v___x_681_, 3);
lean_ctor_set(v___x_681_, 0, v___x_684_);
v___x_686_ = v___x_681_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
v___y_654_ = v___y_668_;
v_ctr_655_ = v___x_683_;
v_a_656_ = v___x_686_;
goto v___jp_653_;
}
}
}
default: 
{
lean_object* v_ipv6_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_698_; 
v_ipv6_689_ = lean_ctor_get(v_x_651_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v_x_651_);
if (v_isSharedCheck_698_ == 0)
{
v___x_691_ = v_x_651_;
v_isShared_692_ = v_isSharedCheck_698_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_ipv6_689_);
lean_dec(v_x_651_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_698_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_693_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_694_ = lean_uv_ntop_v6(v_ipv6_689_);
lean_dec_ref(v_ipv6_689_);
if (v_isShared_692_ == 0)
{
lean_ctor_set_tag(v___x_691_, 3);
lean_ctor_set(v___x_691_, 0, v___x_694_);
v___x_696_ = v___x_691_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
v___y_654_ = v___y_668_;
v_ctr_655_ = v___x_693_;
v_a_656_ = v___x_696_;
goto v___jp_653_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0___boxed(lean_object* v_x_703_, lean_object* v_prec_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Std_Http_URI_instReprHost___lam__0(v_x_703_, v_prec_704_);
lean_dec(v_prec_704_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0(lean_object* v_x_710_){
_start:
{
switch(lean_obj_tag(v_x_710_))
{
case 0:
{
lean_object* v_name_711_; 
v_name_711_ = lean_ctor_get(v_x_710_, 0);
lean_inc_ref(v_name_711_);
return v_name_711_;
}
case 1:
{
lean_object* v_ipv4_712_; lean_object* v___x_713_; 
v_ipv4_712_ = lean_ctor_get(v_x_710_, 0);
v___x_713_ = lean_uv_ntop_v4(v_ipv4_712_);
return v___x_713_;
}
default: 
{
lean_object* v_ipv6_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_ipv6_714_ = lean_ctor_get(v_x_710_, 0);
v___x_715_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_716_ = lean_uv_ntop_v6(v_ipv6_714_);
v___x_717_ = lean_string_append(v___x_715_, v___x_716_);
lean_dec_ref(v___x_716_);
v___x_718_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_719_ = lean_string_append(v___x_717_, v___x_718_);
return v___x_719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0___boxed(lean_object* v_x_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Std_Http_URI_instToStringHost___lam__0(v_x_720_);
lean_dec_ref(v_x_720_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___impl(lean_object* v_x_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = lean_obj_tag_nat(v_x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___impl___boxed(lean_object* v_x_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Std_Http_URI_Port_ctorIdx___impl(v_x_726_);
lean_dec(v_x_726_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg(lean_object* v_t_728_, lean_object* v_k_729_){
_start:
{
if (lean_obj_tag(v_t_728_) == 2)
{
uint16_t v_port_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_port_730_ = lean_ctor_get_uint16(v_t_728_, 0);
v___x_731_ = lean_box(v_port_730_);
v___x_732_ = lean_apply_1(v_k_729_, v___x_731_);
return v___x_732_;
}
else
{
return v_k_729_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg___boxed(lean_object* v_t_733_, lean_object* v_k_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_733_, v_k_734_);
lean_dec(v_t_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim(lean_object* v_motive_736_, lean_object* v_ctorIdx_737_, lean_object* v_t_738_, lean_object* v_h_739_, lean_object* v_k_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_738_, v_k_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___boxed(lean_object* v_motive_742_, lean_object* v_ctorIdx_743_, lean_object* v_t_744_, lean_object* v_h_745_, lean_object* v_k_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Std_Http_URI_Port_ctorElim(v_motive_742_, v_ctorIdx_743_, v_t_744_, v_h_745_, v_k_746_);
lean_dec(v_t_744_);
lean_dec(v_ctorIdx_743_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg(lean_object* v_t_748_, lean_object* v_omitted_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_748_, v_omitted_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg___boxed(lean_object* v_t_751_, lean_object* v_omitted_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Std_Http_URI_Port_omitted_elim___redArg(v_t_751_, v_omitted_752_);
lean_dec(v_t_751_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim(lean_object* v_motive_754_, lean_object* v_t_755_, lean_object* v_h_756_, lean_object* v_omitted_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_755_, v_omitted_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___boxed(lean_object* v_motive_759_, lean_object* v_t_760_, lean_object* v_h_761_, lean_object* v_omitted_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_Http_URI_Port_omitted_elim(v_motive_759_, v_t_760_, v_h_761_, v_omitted_762_);
lean_dec(v_t_760_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg(lean_object* v_t_764_, lean_object* v_empty_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_764_, v_empty_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg___boxed(lean_object* v_t_767_, lean_object* v_empty_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Std_Http_URI_Port_empty_elim___redArg(v_t_767_, v_empty_768_);
lean_dec(v_t_767_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim(lean_object* v_motive_770_, lean_object* v_t_771_, lean_object* v_h_772_, lean_object* v_empty_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_771_, v_empty_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___boxed(lean_object* v_motive_775_, lean_object* v_t_776_, lean_object* v_h_777_, lean_object* v_empty_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Std_Http_URI_Port_empty_elim(v_motive_775_, v_t_776_, v_h_777_, v_empty_778_);
lean_dec(v_t_776_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg(lean_object* v_t_780_, lean_object* v_value_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_780_, v_value_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg___boxed(lean_object* v_t_783_, lean_object* v_value_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_Http_URI_Port_value_elim___redArg(v_t_783_, v_value_784_);
lean_dec(v_t_783_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim(lean_object* v_motive_786_, lean_object* v_t_787_, lean_object* v_h_788_, lean_object* v_value_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_787_, v_value_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___boxed(lean_object* v_motive_791_, lean_object* v_t_792_, lean_object* v_h_793_, lean_object* v_value_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Std_Http_URI_Port_value_elim(v_motive_791_, v_t_792_, v_h_793_, v_value_794_);
lean_dec(v_t_792_);
return v_res_795_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort_default(void){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = lean_box(0);
return v___x_796_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort(void){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = lean_box(0);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr(lean_object* v_x_810_, lean_object* v_prec_811_){
_start:
{
lean_object* v___y_813_; lean_object* v___y_820_; 
switch(lean_obj_tag(v_x_810_))
{
case 0:
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = lean_unsigned_to_nat(1024u);
v___x_827_ = lean_nat_dec_le(v___x_826_, v_prec_811_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
v___x_828_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_820_ = v___x_828_;
goto v___jp_819_;
}
else
{
lean_object* v___x_829_; 
v___x_829_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_820_ = v___x_829_;
goto v___jp_819_;
}
}
case 1:
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = lean_unsigned_to_nat(1024u);
v___x_831_ = lean_nat_dec_le(v___x_830_, v_prec_811_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
v___x_832_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_813_ = v___x_832_;
goto v___jp_812_;
}
else
{
lean_object* v___x_833_; 
v___x_833_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_813_ = v___x_833_;
goto v___jp_812_;
}
}
default: 
{
uint16_t v_port_834_; lean_object* v___y_836_; lean_object* v___x_846_; uint8_t v___x_847_; 
v_port_834_ = lean_ctor_get_uint16(v_x_810_, 0);
v___x_846_ = lean_unsigned_to_nat(1024u);
v___x_847_ = lean_nat_dec_le(v___x_846_, v_prec_811_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
v___x_848_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_836_ = v___x_848_;
goto v___jp_835_;
}
else
{
lean_object* v___x_849_; 
v___x_849_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_836_ = v___x_849_;
goto v___jp_835_;
}
v___jp_835_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_837_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__6));
v___x_838_ = lean_uint16_to_nat(v_port_834_);
v___x_839_ = l_Nat_reprFast(v___x_838_);
v___x_840_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
v___x_841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_837_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
lean_inc(v___y_836_);
v___x_842_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_842_, 0, v___y_836_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = 0;
v___x_844_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_844_, 0, v___x_842_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*1, v___x_843_);
v___x_845_ = l_Repr_addAppParen(v___x_844_, v_prec_811_);
return v___x_845_;
}
}
}
v___jp_812_:
{
lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_814_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__1));
lean_inc(v___y_813_);
v___x_815_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_815_, 0, v___y_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = 0;
v___x_817_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set_uint8(v___x_817_, sizeof(void*)*1, v___x_816_);
v___x_818_ = l_Repr_addAppParen(v___x_817_, v_prec_811_);
return v___x_818_;
}
v___jp_819_:
{
lean_object* v___x_821_; lean_object* v___x_822_; uint8_t v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_821_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__3));
lean_inc(v___y_820_);
v___x_822_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_822_, 0, v___y_820_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = 0;
v___x_824_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set_uint8(v___x_824_, sizeof(void*)*1, v___x_823_);
v___x_825_ = l_Repr_addAppParen(v___x_824_, v_prec_811_);
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr___boxed(lean_object* v_x_850_, lean_object* v_prec_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_Http_URI_instReprPort_repr(v_x_850_, v_prec_851_);
lean_dec(v_prec_851_);
lean_dec(v_x_850_);
return v_res_852_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort_decEq(lean_object* v_x_855_, lean_object* v_x_856_){
_start:
{
switch(lean_obj_tag(v_x_855_))
{
case 0:
{
if (lean_obj_tag(v_x_856_) == 0)
{
uint8_t v___x_857_; 
v___x_857_ = 1;
return v___x_857_;
}
else
{
uint8_t v___x_858_; 
v___x_858_ = 0;
return v___x_858_;
}
}
case 1:
{
if (lean_obj_tag(v_x_856_) == 1)
{
uint8_t v___x_859_; 
v___x_859_ = 1;
return v___x_859_;
}
else
{
uint8_t v___x_860_; 
v___x_860_ = 0;
return v___x_860_;
}
}
default: 
{
if (lean_obj_tag(v_x_856_) == 2)
{
uint16_t v_port_861_; uint16_t v_port_862_; uint8_t v___x_863_; 
v_port_861_ = lean_ctor_get_uint16(v_x_855_, 0);
v_port_862_ = lean_ctor_get_uint16(v_x_856_, 0);
v___x_863_ = lean_uint16_dec_eq(v_port_861_, v_port_862_);
return v___x_863_;
}
else
{
uint8_t v___x_864_; 
v___x_864_ = 0;
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort_decEq___boxed(lean_object* v_x_865_, lean_object* v_x_866_){
_start:
{
uint8_t v_res_867_; lean_object* v_r_868_; 
v_res_867_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_865_, v_x_866_);
lean_dec(v_x_866_);
lean_dec(v_x_865_);
v_r_868_ = lean_box(v_res_867_);
return v_r_868_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort(lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
uint8_t v___x_871_; 
v___x_871_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_869_, v_x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort___boxed(lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
uint8_t v_res_874_; lean_object* v_r_875_; 
v_res_874_ = l_Std_Http_URI_instDecidableEqPort(v_x_872_, v_x_873_);
lean_dec(v_x_873_);
lean_dec(v_x_872_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_876_ = lean_box(0);
v___x_877_ = l_Std_Http_URI_instInhabitedHost_default;
v___x_878_ = lean_box(0);
v___x_879_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set(v___x_879_, 1, v___x_877_);
lean_ctor_set(v___x_879_, 2, v___x_876_);
return v___x_879_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default(void){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = lean_obj_once(&l_Std_Http_URI_instInhabitedAuthority_default___closed__0, &l_Std_Http_URI_instInhabitedAuthority_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0);
return v___x_880_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority(void){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Std_Http_URI_instInhabitedAuthority_default;
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
if (lean_obj_tag(v_x_882_) == 0)
{
lean_object* v___x_884_; 
v___x_884_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_884_;
}
else
{
lean_object* v_val_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_val_885_ = lean_ctor_get(v_x_882_, 0);
lean_inc(v_val_885_);
lean_dec_ref_known(v_x_882_, 1);
v___x_886_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_887_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_val_885_);
v___x_888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = l_Repr_addAppParen(v___x_888_, v_x_883_);
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0___boxed(lean_object* v_x_890_, lean_object* v_x_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_x_890_, v_x_891_);
lean_dec(v_x_891_);
return v_res_892_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_unsigned_to_nat(8u);
v___x_906_ = lean_nat_to_int(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg(lean_object* v_x_910_){
_start:
{
lean_object* v_userInfo_911_; lean_object* v_host_912_; lean_object* v_port_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_ctr_933_; lean_object* v_a_934_; 
v_userInfo_911_ = lean_ctor_get(v_x_910_, 0);
lean_inc(v_userInfo_911_);
v_host_912_ = lean_ctor_get(v_x_910_, 1);
lean_inc_ref(v_host_912_);
v_port_913_ = lean_ctor_get(v_x_910_, 2);
lean_inc(v_port_913_);
lean_dec_ref(v_x_910_);
v___x_914_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_915_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3));
v___x_916_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_userInfo_911_, v___x_917_);
v___x_919_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_916_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = 0;
v___x_921_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set_uint8(v___x_921_, sizeof(void*)*1, v___x_920_);
v___x_922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_915_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = lean_box(1);
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_914_);
v___x_930_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_931_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_912_))
{
case 0:
{
lean_object* v_name_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_971_; 
v_name_962_ = lean_ctor_get(v_host_912_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v_host_912_);
if (v_isSharedCheck_971_ == 0)
{
v___x_964_ = v_host_912_;
v_isShared_965_ = v_isSharedCheck_971_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_name_962_);
lean_dec(v_host_912_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_971_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_966_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_967_ = l_String_quote(v_name_962_);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 3);
lean_ctor_set(v___x_964_, 0, v___x_967_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
v_ctr_933_ = v___x_966_;
v_a_934_ = v___x_969_;
goto v___jp_932_;
}
}
}
case 1:
{
lean_object* v_ipv4_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_981_; 
v_ipv4_972_ = lean_ctor_get(v_host_912_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v_host_912_);
if (v_isSharedCheck_981_ == 0)
{
v___x_974_ = v_host_912_;
v_isShared_975_ = v_isSharedCheck_981_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_ipv4_972_);
lean_dec(v_host_912_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_981_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_976_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_977_ = lean_uv_ntop_v4(v_ipv4_972_);
lean_dec_ref(v_ipv4_972_);
if (v_isShared_975_ == 0)
{
lean_ctor_set_tag(v___x_974_, 3);
lean_ctor_set(v___x_974_, 0, v___x_977_);
v___x_979_ = v___x_974_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
v_ctr_933_ = v___x_976_;
v_a_934_ = v___x_979_;
goto v___jp_932_;
}
}
}
default: 
{
lean_object* v_ipv6_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_991_; 
v_ipv6_982_ = lean_ctor_get(v_host_912_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v_host_912_);
if (v_isSharedCheck_991_ == 0)
{
v___x_984_ = v_host_912_;
v_isShared_985_ = v_isSharedCheck_991_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_ipv6_982_);
lean_dec(v_host_912_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_991_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_986_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_987_ = lean_uv_ntop_v6(v_ipv6_982_);
lean_dec_ref(v_ipv6_982_);
if (v_isShared_985_ == 0)
{
lean_ctor_set_tag(v___x_984_, 3);
lean_ctor_set(v___x_984_, 0, v___x_987_);
v___x_989_ = v___x_984_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
v_ctr_933_ = v___x_986_;
v_a_934_ = v___x_989_;
goto v___jp_932_;
}
}
}
}
v___jp_932_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_935_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_936_ = lean_string_append(v___x_935_, v_ctr_933_);
v___x_937_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_925_);
v___x_939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v_a_934_);
v___x_940_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_931_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*1, v___x_920_);
v___x_942_ = l_Repr_addAppParen(v___x_941_, v___x_917_);
v___x_943_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_930_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set_uint8(v___x_944_, sizeof(void*)*1, v___x_920_);
v___x_945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_929_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_923_);
v___x_947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v___x_925_);
v___x_948_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___x_914_);
v___x_951_ = l_Std_Http_URI_instReprPort_repr(v_port_913_, v___x_917_);
lean_dec(v_port_913_);
v___x_952_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_930_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set_uint8(v___x_953_, sizeof(void*)*1, v___x_920_);
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_950_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_956_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v___x_954_);
v___x_958_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_955_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*1, v___x_920_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr(lean_object* v_x_992_, lean_object* v_prec_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_x_992_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___boxed(lean_object* v_x_995_, lean_object* v_prec_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Std_Http_URI_instReprAuthority_repr(v_x_995_, v_prec_996_);
lean_dec(v_prec_996_);
return v_res_997_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(lean_object* v_x_1000_, lean_object* v_x_1001_){
_start:
{
if (lean_obj_tag(v_x_1000_) == 0)
{
if (lean_obj_tag(v_x_1001_) == 0)
{
uint8_t v___x_1002_; 
v___x_1002_ = 1;
return v___x_1002_;
}
else
{
uint8_t v___x_1003_; 
v___x_1003_ = 0;
return v___x_1003_;
}
}
else
{
if (lean_obj_tag(v_x_1001_) == 0)
{
uint8_t v___x_1004_; 
v___x_1004_ = 0;
return v___x_1004_;
}
else
{
lean_object* v_val_1005_; lean_object* v_val_1006_; uint8_t v___x_1007_; 
v_val_1005_ = lean_ctor_get(v_x_1000_, 0);
v_val_1006_ = lean_ctor_get(v_x_1001_, 0);
v___x_1007_ = l_Std_Http_URI_instBEqUserInfo_beq(v_val_1005_, v_val_1006_);
return v___x_1007_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0___boxed(lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
uint8_t v_res_1010_; lean_object* v_r_1011_; 
v_res_1010_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_x_1008_, v_x_1009_);
lean_dec(v_x_1009_);
lean_dec(v_x_1008_);
v_r_1011_ = lean_box(v_res_1010_);
return v_r_1011_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqAuthority_beq(lean_object* v_x_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v_userInfo_1014_; lean_object* v_host_1015_; lean_object* v_port_1016_; lean_object* v_userInfo_1017_; lean_object* v_host_1018_; lean_object* v_port_1019_; uint8_t v___x_1020_; 
v_userInfo_1014_ = lean_ctor_get(v_x_1012_, 0);
v_host_1015_ = lean_ctor_get(v_x_1012_, 1);
v_port_1016_ = lean_ctor_get(v_x_1012_, 2);
v_userInfo_1017_ = lean_ctor_get(v_x_1013_, 0);
v_host_1018_ = lean_ctor_get(v_x_1013_, 1);
v_port_1019_ = lean_ctor_get(v_x_1013_, 2);
v___x_1020_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_userInfo_1014_, v_userInfo_1017_);
if (v___x_1020_ == 0)
{
return v___x_1020_;
}
else
{
uint8_t v___x_1021_; 
v___x_1021_ = l_Std_Http_URI_instBEqHost_beq(v_host_1015_, v_host_1018_);
if (v___x_1021_ == 0)
{
return v___x_1021_;
}
else
{
uint8_t v___x_1022_; 
v___x_1022_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1016_, v_port_1019_);
return v___x_1022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqAuthority_beq___boxed(lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
uint8_t v_res_1025_; lean_object* v_r_1026_; 
v_res_1025_ = l_Std_Http_URI_instBEqAuthority_beq(v_x_1023_, v_x_1024_);
lean_dec_ref(v_x_1024_);
lean_dec_ref(v_x_1023_);
v_r_1026_ = lean_box(v_res_1025_);
return v_r_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringAuthority___lam__0(lean_object* v_auth_1032_){
_start:
{
lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v_userInfo_1039_; lean_object* v_host_1040_; lean_object* v_port_1041_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1053_; 
v_userInfo_1039_ = lean_ctor_get(v_auth_1032_, 0);
lean_inc(v_userInfo_1039_);
v_host_1040_ = lean_ctor_get(v_auth_1032_, 1);
lean_inc_ref(v_host_1040_);
v_port_1041_ = lean_ctor_get(v_auth_1032_, 2);
lean_inc(v_port_1041_);
lean_dec_ref(v_auth_1032_);
if (lean_obj_tag(v_userInfo_1039_) == 0)
{
lean_object* v___x_1063_; 
v___x_1063_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1053_ = v___x_1063_;
goto v___jp_1052_;
}
else
{
lean_object* v_val_1064_; lean_object* v_password_1065_; 
v_val_1064_ = lean_ctor_get(v_userInfo_1039_, 0);
lean_inc(v_val_1064_);
lean_dec_ref_known(v_userInfo_1039_, 1);
v_password_1065_ = lean_ctor_get(v_val_1064_, 1);
if (lean_obj_tag(v_password_1065_) == 0)
{
lean_object* v_username_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_username_1066_ = lean_ctor_get(v_val_1064_, 0);
lean_inc_ref(v_username_1066_);
lean_dec(v_val_1064_);
v___x_1067_ = lean_string_from_utf8_unchecked(v_username_1066_);
v___x_1068_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1069_ = lean_string_append(v___x_1067_, v___x_1068_);
v___y_1053_ = v___x_1069_;
goto v___jp_1052_;
}
else
{
lean_object* v_username_1070_; lean_object* v_val_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_inc_ref(v_password_1065_);
v_username_1070_ = lean_ctor_get(v_val_1064_, 0);
lean_inc_ref(v_username_1070_);
lean_dec(v_val_1064_);
v_val_1071_ = lean_ctor_get(v_password_1065_, 0);
lean_inc(v_val_1071_);
lean_dec_ref_known(v_password_1065_, 1);
v___x_1072_ = lean_string_from_utf8_unchecked(v_username_1070_);
v___x_1073_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1074_ = lean_string_append(v___x_1072_, v___x_1073_);
v___x_1075_ = lean_string_from_utf8_unchecked(v_val_1071_);
v___x_1076_ = lean_string_append(v___x_1074_, v___x_1075_);
lean_dec_ref(v___x_1075_);
v___x_1077_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1078_ = lean_string_append(v___x_1076_, v___x_1077_);
v___y_1053_ = v___x_1078_;
goto v___jp_1052_;
}
}
v___jp_1033_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_string_append(v___y_1034_, v___y_1035_);
lean_dec_ref(v___y_1035_);
v___x_1038_ = lean_string_append(v___x_1037_, v___y_1036_);
lean_dec_ref(v___y_1036_);
return v___x_1038_;
}
v___jp_1042_:
{
switch(lean_obj_tag(v_port_1041_))
{
case 0:
{
lean_object* v___x_1045_; 
v___x_1045_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1034_ = v___y_1043_;
v___y_1035_ = v___y_1044_;
v___y_1036_ = v___x_1045_;
goto v___jp_1033_;
}
case 1:
{
lean_object* v___x_1046_; 
v___x_1046_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_1034_ = v___y_1043_;
v___y_1035_ = v___y_1044_;
v___y_1036_ = v___x_1046_;
goto v___jp_1033_;
}
default: 
{
uint16_t v_port_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_port_1047_ = lean_ctor_get_uint16(v_port_1041_, 0);
lean_dec_ref_known(v_port_1041_, 0);
v___x_1048_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1049_ = lean_uint16_to_nat(v_port_1047_);
v___x_1050_ = l_Nat_reprFast(v___x_1049_);
v___x_1051_ = lean_string_append(v___x_1048_, v___x_1050_);
lean_dec_ref(v___x_1050_);
v___y_1034_ = v___y_1043_;
v___y_1035_ = v___y_1044_;
v___y_1036_ = v___x_1051_;
goto v___jp_1033_;
}
}
}
v___jp_1052_:
{
switch(lean_obj_tag(v_host_1040_))
{
case 0:
{
lean_object* v_name_1054_; 
v_name_1054_ = lean_ctor_get(v_host_1040_, 0);
lean_inc_ref(v_name_1054_);
lean_dec_ref_known(v_host_1040_, 1);
v___y_1043_ = v___y_1053_;
v___y_1044_ = v_name_1054_;
goto v___jp_1042_;
}
case 1:
{
lean_object* v_ipv4_1055_; lean_object* v___x_1056_; 
v_ipv4_1055_ = lean_ctor_get(v_host_1040_, 0);
lean_inc_ref(v_ipv4_1055_);
lean_dec_ref_known(v_host_1040_, 1);
v___x_1056_ = lean_uv_ntop_v4(v_ipv4_1055_);
lean_dec_ref(v_ipv4_1055_);
v___y_1043_ = v___y_1053_;
v___y_1044_ = v___x_1056_;
goto v___jp_1042_;
}
default: 
{
lean_object* v_ipv6_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_ipv6_1057_ = lean_ctor_get(v_host_1040_, 0);
lean_inc_ref(v_ipv6_1057_);
lean_dec_ref_known(v_host_1040_, 1);
v___x_1058_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_1059_ = lean_uv_ntop_v6(v_ipv6_1057_);
lean_dec_ref(v_ipv6_1057_);
v___x_1060_ = lean_string_append(v___x_1058_, v___x_1059_);
lean_dec_ref(v___x_1059_);
v___x_1061_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_1062_ = lean_string_append(v___x_1060_, v___x_1061_);
v___y_1043_ = v___y_1053_;
v___y_1044_ = v___x_1062_;
goto v___jp_1042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_){
_start:
{
if (lean_obj_tag(v_x_1090_) == 0)
{
lean_dec(v_x_1088_);
return v_x_1089_;
}
else
{
lean_object* v_head_1091_; lean_object* v_tail_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1104_; 
v_head_1091_ = lean_ctor_get(v_x_1090_, 0);
v_tail_1092_ = lean_ctor_get(v_x_1090_, 1);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_x_1090_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1094_ = v_x_1090_;
v_isShared_1095_ = v_isSharedCheck_1104_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_tail_1092_);
lean_inc(v_head_1091_);
lean_dec(v_x_1090_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1104_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
lean_inc(v_x_1088_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set_tag(v___x_1094_, 5);
lean_ctor_set(v___x_1094_, 1, v_x_1088_);
lean_ctor_set(v___x_1094_, 0, v_x_1089_);
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_x_1089_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_x_1088_);
v___x_1097_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1098_ = lean_string_from_utf8_unchecked(v_head_1091_);
v___x_1099_ = l_String_quote(v___x_1098_);
v___x_1100_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
v___x_1101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1097_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v_x_1089_ = v___x_1101_;
v_x_1090_ = v_tail_1092_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
if (lean_obj_tag(v_x_1107_) == 0)
{
lean_dec(v_x_1105_);
return v_x_1106_;
}
else
{
lean_object* v_head_1108_; lean_object* v_tail_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1121_; 
v_head_1108_ = lean_ctor_get(v_x_1107_, 0);
v_tail_1109_ = lean_ctor_get(v_x_1107_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_x_1107_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1111_ = v_x_1107_;
v_isShared_1112_ = v_isSharedCheck_1121_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_tail_1109_);
lean_inc(v_head_1108_);
lean_dec(v_x_1107_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1121_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
lean_inc(v_x_1105_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set_tag(v___x_1111_, 5);
lean_ctor_set(v___x_1111_, 1, v_x_1105_);
lean_ctor_set(v___x_1111_, 0, v_x_1106_);
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_x_1106_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_x_1105_);
v___x_1114_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1115_ = lean_string_from_utf8_unchecked(v_head_1108_);
v___x_1116_ = l_String_quote(v___x_1115_);
v___x_1117_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
v___x_1118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1114_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(v_x_1105_, v___x_1118_, v_tail_1109_);
return v___x_1119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = lean_string_from_utf8_unchecked(v___y_1122_);
v___x_1124_ = l_String_quote(v___x_1123_);
v___x_1125_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(lean_object* v_x_1126_, lean_object* v_x_1127_){
_start:
{
if (lean_obj_tag(v_x_1126_) == 0)
{
lean_object* v___x_1128_; 
lean_dec(v_x_1127_);
v___x_1128_ = lean_box(0);
return v___x_1128_;
}
else
{
lean_object* v_tail_1129_; 
v_tail_1129_ = lean_ctor_get(v_x_1126_, 1);
if (lean_obj_tag(v_tail_1129_) == 0)
{
lean_object* v_head_1130_; lean_object* v___x_1131_; 
lean_dec(v_x_1127_);
v_head_1130_ = lean_ctor_get(v_x_1126_, 0);
lean_inc(v_head_1130_);
lean_dec_ref_known(v_x_1126_, 2);
v___x_1131_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1130_);
return v___x_1131_;
}
else
{
lean_object* v_head_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_inc(v_tail_1129_);
v_head_1132_ = lean_ctor_get(v_x_1126_, 0);
lean_inc(v_head_1132_);
lean_dec_ref_known(v_x_1126_, 2);
v___x_1133_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1132_);
v___x_1134_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(v_x_1127_, v___x_1133_, v_tail_1129_);
return v___x_1134_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0));
v___x_1140_ = lean_string_length(v___x_1139_);
return v___x_1140_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2);
v___x_1142_ = lean_nat_to_int(v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(lean_object* v_xs_1150_){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1151_ = lean_array_get_size(v_xs_1150_);
v___x_1152_ = lean_unsigned_to_nat(0u);
v___x_1153_ = lean_nat_dec_eq(v___x_1151_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1154_ = lean_array_to_list(v_xs_1150_);
v___x_1155_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1156_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(v___x_1154_, v___x_1155_);
v___x_1157_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1158_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v___x_1156_);
v___x_1160_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1157_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = l_Std_Format_fill(v___x_1162_);
return v___x_1163_;
}
else
{
lean_object* v___x_1164_; 
lean_dec_ref(v_xs_1150_);
v___x_1164_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___redArg(lean_object* v_x_1177_){
_start:
{
lean_object* v_segments_1178_; uint8_t v_absolute_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1211_; 
v_segments_1178_ = lean_ctor_get(v_x_1177_, 0);
v_absolute_1179_ = lean_ctor_get_uint8(v_x_1177_, sizeof(void*)*1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_x_1177_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1181_ = v_x_1177_;
v_isShared_1182_ = v_isSharedCheck_1211_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_segments_1178_);
lean_dec(v_x_1177_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1211_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; lean_object* v___x_1190_; 
v___x_1183_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1184_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__3));
v___x_1185_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_1186_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(v_segments_1178_);
v___x_1187_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = 0;
if (v_isShared_1182_ == 0)
{
lean_ctor_set_tag(v___x_1181_, 6);
lean_ctor_set(v___x_1181_, 0, v___x_1187_);
v___x_1190_ = v___x_1181_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1187_);
v___x_1190_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_ctor_set_uint8(v___x_1190_, sizeof(void*)*1, v___x_1188_);
v___x_1191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1184_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_box(1);
v___x_1195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__5));
v___x_1197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1195_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v___x_1183_);
v___x_1199_ = l_Bool_repr___redArg(v_absolute_1179_);
v___x_1200_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1185_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
lean_ctor_set_uint8(v___x_1201_, sizeof(void*)*1, v___x_1188_);
v___x_1202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1198_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1204_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
lean_ctor_set(v___x_1205_, 1, v___x_1202_);
v___x_1206_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1205_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1203_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set_uint8(v___x_1209_, sizeof(void*)*1, v___x_1188_);
return v___x_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr(lean_object* v_x_1212_, lean_object* v_prec_1213_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Std_Http_URI_instReprPath_repr___redArg(v_x_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___boxed(lean_object* v_x_1215_, lean_object* v_prec_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Std_Http_URI_instReprPath_repr(v_x_1215_, v_prec_1216_);
lean_dec(v_prec_1216_);
return v_res_1217_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(lean_object* v_xs_1220_, lean_object* v_ys_1221_, lean_object* v_x_1222_){
_start:
{
lean_object* v_zero_1223_; uint8_t v_isZero_1224_; 
v_zero_1223_ = lean_unsigned_to_nat(0u);
v_isZero_1224_ = lean_nat_dec_eq(v_x_1222_, v_zero_1223_);
if (v_isZero_1224_ == 1)
{
lean_dec(v_x_1222_);
return v_isZero_1224_;
}
else
{
lean_object* v_one_1225_; lean_object* v_n_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v_one_1225_ = lean_unsigned_to_nat(1u);
v_n_1226_ = lean_nat_sub(v_x_1222_, v_one_1225_);
lean_dec(v_x_1222_);
v___x_1227_ = lean_array_fget_borrowed(v_xs_1220_, v_n_1226_);
v___x_1228_ = lean_array_fget_borrowed(v_ys_1221_, v_n_1226_);
v___x_1229_ = lean_sarray_dec_eq(v___x_1227_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_dec(v_n_1226_);
return v___x_1229_;
}
else
{
v_x_1222_ = v_n_1226_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg___boxed(lean_object* v_xs_1231_, lean_object* v_ys_1232_, lean_object* v_x_1233_){
_start:
{
uint8_t v_res_1234_; lean_object* v_r_1235_; 
v_res_1234_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1231_, v_ys_1232_, v_x_1233_);
lean_dec_ref(v_ys_1232_);
lean_dec_ref(v_xs_1231_);
v_r_1235_ = lean_box(v_res_1234_);
return v_r_1235_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqPath_beq(lean_object* v_x_1236_, lean_object* v_x_1237_){
_start:
{
lean_object* v_segments_1238_; uint8_t v_absolute_1239_; lean_object* v_segments_1240_; uint8_t v_absolute_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_segments_1238_ = lean_ctor_get(v_x_1236_, 0);
v_absolute_1239_ = lean_ctor_get_uint8(v_x_1236_, sizeof(void*)*1);
v_segments_1240_ = lean_ctor_get(v_x_1237_, 0);
v_absolute_1241_ = lean_ctor_get_uint8(v_x_1237_, sizeof(void*)*1);
v___x_1242_ = lean_array_get_size(v_segments_1238_);
v___x_1243_ = lean_array_get_size(v_segments_1240_);
v___x_1244_ = lean_nat_dec_eq(v___x_1242_, v___x_1243_);
if (v___x_1244_ == 0)
{
return v___x_1244_;
}
else
{
uint8_t v___x_1245_; 
v___x_1245_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_segments_1238_, v_segments_1240_, v___x_1242_);
if (v___x_1245_ == 0)
{
return v___x_1245_;
}
else
{
if (v_absolute_1241_ == 0)
{
if (v_absolute_1239_ == 0)
{
return v___x_1245_;
}
else
{
return v_absolute_1241_;
}
}
else
{
return v_absolute_1239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqPath_beq___boxed(lean_object* v_x_1246_, lean_object* v_x_1247_){
_start:
{
uint8_t v_res_1248_; lean_object* v_r_1249_; 
v_res_1248_ = l_Std_Http_URI_instBEqPath_beq(v_x_1246_, v_x_1247_);
lean_dec_ref(v_x_1247_);
lean_dec_ref(v_x_1246_);
v_r_1249_ = lean_box(v_res_1248_);
return v_r_1249_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(lean_object* v_xs_1250_, lean_object* v_ys_1251_, lean_object* v_hsz_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
uint8_t v___x_1255_; 
v___x_1255_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1250_, v_ys_1251_, v_x_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___boxed(lean_object* v_xs_1256_, lean_object* v_ys_1257_, lean_object* v_hsz_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_){
_start:
{
uint8_t v_res_1261_; lean_object* v_r_1262_; 
v_res_1261_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(v_xs_1256_, v_ys_1257_, v_hsz_1258_, v_x_1259_, v_x_1260_);
lean_dec_ref(v_ys_1257_);
lean_dec_ref(v_xs_1256_);
v_r_1262_ = lean_box(v_res_1261_);
return v_r_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__0(lean_object* v_x_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_string_from_utf8_unchecked(v_x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__1(lean_object* v___f_1287_, lean_object* v_path_1288_){
_start:
{
lean_object* v_segments_1289_; uint8_t v_absolute_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; size_t v_sz_1293_; size_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v_result_1297_; 
v_segments_1289_ = lean_ctor_get(v_path_1288_, 0);
lean_inc_ref(v_segments_1289_);
v_absolute_1290_ = lean_ctor_get_uint8(v_path_1288_, sizeof(void*)*1);
lean_dec_ref(v_path_1288_);
v___x_1291_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_1292_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_1293_ = lean_array_size(v_segments_1289_);
v___x_1294_ = ((size_t)0ULL);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1292_, v___f_1287_, v_sz_1293_, v___x_1294_, v_segments_1289_);
v___x_1296_ = lean_array_to_list(v___x_1295_);
v_result_1297_ = l_String_intercalate(v___x_1291_, v___x_1296_);
if (v_absolute_1290_ == 0)
{
return v_result_1297_;
}
else
{
lean_object* v___x_1298_; 
v___x_1298_ = lean_string_append(v___x_1291_, v_result_1297_);
lean_dec_ref(v_result_1297_);
return v___x_1298_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Path_isEmpty(lean_object* v_p_1303_){
_start:
{
lean_object* v_segments_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_segments_1304_ = lean_ctor_get(v_p_1303_, 0);
v___x_1305_ = lean_array_get_size(v_segments_1304_);
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = lean_nat_dec_eq(v___x_1305_, v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_isEmpty___boxed(lean_object* v_p_1308_){
_start:
{
uint8_t v_res_1309_; lean_object* v_r_1310_; 
v_res_1309_ = l_Std_Http_URI_Path_isEmpty(v_p_1308_);
lean_dec_ref(v_p_1308_);
v_r_1310_ = lean_box(v_res_1309_);
return v_r_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parent(lean_object* v_p_1311_){
_start:
{
lean_object* v_segments_1312_; uint8_t v_absolute_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_segments_1312_ = lean_ctor_get(v_p_1311_, 0);
v_absolute_1313_ = lean_ctor_get_uint8(v_p_1311_, sizeof(void*)*1);
v___x_1314_ = lean_array_get_size(v_segments_1312_);
v___x_1315_ = lean_unsigned_to_nat(0u);
v___x_1316_ = lean_nat_dec_eq(v___x_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
lean_inc_ref(v_segments_1312_);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_p_1311_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v_p_1311_, 0);
lean_dec(v_unused_1325_);
v___x_1318_ = v_p_1311_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_dec(v_p_1311_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_array_pop(v_segments_1312_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*1, v_absolute_1313_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
return v_p_1311_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join(lean_object* v_p1_1326_, lean_object* v_p2_1327_){
_start:
{
uint8_t v_absolute_1328_; 
v_absolute_1328_ = lean_ctor_get_uint8(v_p2_1327_, sizeof(void*)*1);
if (v_absolute_1328_ == 0)
{
lean_object* v_segments_1329_; lean_object* v_segments_1330_; uint8_t v_absolute_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1339_; 
v_segments_1329_ = lean_ctor_get(v_p2_1327_, 0);
v_segments_1330_ = lean_ctor_get(v_p1_1326_, 0);
v_absolute_1331_ = lean_ctor_get_uint8(v_p1_1326_, sizeof(void*)*1);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_p1_1326_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1333_ = v_p1_1326_;
v_isShared_1334_ = v_isSharedCheck_1339_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_segments_1330_);
lean_dec(v_p1_1326_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1339_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = l_Array_append___redArg(v_segments_1330_, v_segments_1329_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1335_);
v___x_1337_ = v___x_1333_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
lean_ctor_set_uint8(v_reuseFailAlloc_1338_, sizeof(void*)*1, v_absolute_1331_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
else
{
lean_dec_ref(v_p1_1326_);
lean_inc_ref(v_p2_1327_);
return v_p2_1327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join___boxed(lean_object* v_p1_1340_, lean_object* v_p2_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Std_Http_URI_Path_join(v_p1_1340_, v_p2_1341_);
lean_dec_ref(v_p2_1341_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append(lean_object* v_p_1343_, lean_object* v_segment_1344_){
_start:
{
lean_object* v_segments_1345_; uint8_t v_absolute_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1355_; 
v_segments_1345_ = lean_ctor_get(v_p_1343_, 0);
v_absolute_1346_ = lean_ctor_get_uint8(v_p_1343_, sizeof(void*)*1);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_p_1343_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1348_ = v_p_1343_;
v_isShared_1349_ = v_isSharedCheck_1355_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_segments_1345_);
lean_dec(v_p_1343_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1355_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1350_ = l_Std_Http_URI_EncodedSegment_encode(v_segment_1344_);
v___x_1351_ = lean_array_push(v_segments_1345_, v___x_1350_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1351_);
v___x_1353_ = v___x_1348_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*1, v_absolute_1346_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append___boxed(lean_object* v_p_1356_, lean_object* v_segment_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Std_Http_URI_Path_append(v_p_1356_, v_segment_1357_);
lean_dec_ref(v_segment_1357_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_appendEncoded(lean_object* v_p_1359_, lean_object* v_segment_1360_){
_start:
{
lean_object* v_segments_1361_; uint8_t v_absolute_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1370_; 
v_segments_1361_ = lean_ctor_get(v_p_1359_, 0);
v_absolute_1362_ = lean_ctor_get_uint8(v_p_1359_, sizeof(void*)*1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_p_1359_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1364_ = v_p_1359_;
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_segments_1361_);
lean_dec(v_p_1359_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = lean_array_push(v_segments_1361_, v_segment_1360_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1366_);
v___x_1368_ = v___x_1364_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*1, v_absolute_1362_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(lean_object* v_input_1373_, lean_object* v_output_1374_){
_start:
{
if (lean_obj_tag(v_input_1373_) == 0)
{
lean_object* v___x_1375_; 
v___x_1375_ = l_List_reverse___redArg(v_output_1374_);
return v___x_1375_;
}
else
{
lean_object* v_head_1376_; lean_object* v_tail_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1394_; 
v_head_1376_ = lean_ctor_get(v_input_1373_, 0);
v_tail_1377_ = lean_ctor_get(v_input_1373_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_input_1373_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1379_ = v_input_1373_;
v_isShared_1380_ = v_isSharedCheck_1394_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_tail_1377_);
lean_inc(v_head_1376_);
lean_dec(v_input_1373_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1394_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
lean_inc(v_head_1376_);
v___x_1381_ = lean_string_from_utf8_unchecked(v_head_1376_);
v___x_1382_ = ((lean_object*)(l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0));
v___x_1383_ = lean_string_dec_eq(v___x_1381_, v___x_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1384_ = ((lean_object*)(l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1));
v___x_1385_ = lean_string_dec_eq(v___x_1381_, v___x_1384_);
lean_dec_ref(v___x_1381_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1387_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 1, v_output_1374_);
v___x_1387_ = v___x_1379_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_head_1376_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_output_1374_);
v___x_1387_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
v_input_1373_ = v_tail_1377_;
v_output_1374_ = v___x_1387_;
goto _start;
}
}
else
{
lean_del_object(v___x_1379_);
lean_dec(v_head_1376_);
if (lean_obj_tag(v_output_1374_) == 0)
{
v_input_1373_ = v_tail_1377_;
goto _start;
}
else
{
lean_object* v_tail_1391_; 
v_tail_1391_ = lean_ctor_get(v_output_1374_, 1);
lean_inc(v_tail_1391_);
lean_dec_ref_known(v_output_1374_, 2);
v_input_1373_ = v_tail_1377_;
v_output_1374_ = v_tail_1391_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_1381_);
lean_del_object(v___x_1379_);
lean_dec(v_head_1376_);
v_input_1373_ = v_tail_1377_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_normalize(lean_object* v_p_1395_){
_start:
{
lean_object* v_segments_1396_; uint8_t v_absolute_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1408_; 
v_segments_1396_ = lean_ctor_get(v_p_1395_, 0);
v_absolute_1397_ = lean_ctor_get_uint8(v_p_1395_, sizeof(void*)*1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_p_1395_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1399_ = v_p_1395_;
v_isShared_1400_ = v_isSharedCheck_1408_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_segments_1396_);
lean_dec(v_p_1395_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1408_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1401_ = lean_array_to_list(v_segments_1396_);
v___x_1402_ = lean_box(0);
v___x_1403_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(v___x_1401_, v___x_1402_);
v___x_1404_ = lean_array_mk(v___x_1403_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1404_);
v___x_1406_ = v___x_1399_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
lean_ctor_set_uint8(v_reuseFailAlloc_1407_, sizeof(void*)*1, v_absolute_1397_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(size_t v_sz_1409_, size_t v_i_1410_, lean_object* v_bs_1411_){
_start:
{
uint8_t v___x_1412_; 
v___x_1412_ = lean_usize_dec_lt(v_i_1410_, v_sz_1409_);
if (v___x_1412_ == 0)
{
return v_bs_1411_;
}
else
{
lean_object* v_v_1413_; lean_object* v___x_1414_; lean_object* v_bs_x27_1415_; lean_object* v___y_1417_; lean_object* v___x_1422_; 
v_v_1413_ = lean_array_uget(v_bs_1411_, v_i_1410_);
v___x_1414_ = lean_unsigned_to_nat(0u);
v_bs_x27_1415_ = lean_array_uset(v_bs_1411_, v_i_1410_, v___x_1414_);
v___x_1422_ = l_Std_Http_URI_EncodedSegment_decode(v_v_1413_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_string_from_utf8_unchecked(v_v_1413_);
v___y_1417_ = v___x_1423_;
goto v___jp_1416_;
}
else
{
lean_object* v_val_1424_; 
lean_dec(v_v_1413_);
v_val_1424_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_val_1424_);
lean_dec_ref_known(v___x_1422_, 1);
v___y_1417_ = v_val_1424_;
goto v___jp_1416_;
}
v___jp_1416_:
{
size_t v___x_1418_; size_t v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = ((size_t)1ULL);
v___x_1419_ = lean_usize_add(v_i_1410_, v___x_1418_);
v___x_1420_ = lean_array_uset(v_bs_x27_1415_, v_i_1410_, v___y_1417_);
v_i_1410_ = v___x_1419_;
v_bs_1411_ = v___x_1420_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0___boxed(lean_object* v_sz_1425_, lean_object* v_i_1426_, lean_object* v_bs_1427_){
_start:
{
size_t v_sz_boxed_1428_; size_t v_i_boxed_1429_; lean_object* v_res_1430_; 
v_sz_boxed_1428_ = lean_unbox_usize(v_sz_1425_);
lean_dec(v_sz_1425_);
v_i_boxed_1429_ = lean_unbox_usize(v_i_1426_);
lean_dec(v_i_1426_);
v_res_1430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_boxed_1428_, v_i_boxed_1429_, v_bs_1427_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_toDecodedSegments(lean_object* v_p_1431_){
_start:
{
lean_object* v_segments_1432_; size_t v_sz_1433_; size_t v___x_1434_; lean_object* v___x_1435_; 
v_segments_1432_ = lean_ctor_get(v_p_1431_, 0);
lean_inc_ref(v_segments_1432_);
lean_dec_ref(v_p_1431_);
v_sz_1433_ = lean_array_size(v_segments_1432_);
v___x_1434_ = ((size_t)0ULL);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_1433_, v___x_1434_, v_segments_1432_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___redArg(lean_object* v_xs_1444_){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1446_ = l_Array_repr___redArg(v___x_1445_, v_xs_1444_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1(lean_object* v_xs_1447_, lean_object* v_x_1448_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1450_ = l_Array_repr___redArg(v___x_1449_, v_xs_1447_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___boxed(lean_object* v_xs_1451_, lean_object* v_x_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Std_Http_URI_instReprQuery___aux__1(v_xs_1451_, v_x_1452_);
lean_dec(v_x_1452_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_1454_, lean_object* v_x_1455_, lean_object* v_x_1456_){
_start:
{
if (lean_obj_tag(v_x_1456_) == 0)
{
lean_dec(v_x_1454_);
return v_x_1455_;
}
else
{
lean_object* v_head_1457_; lean_object* v_tail_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1467_; 
v_head_1457_ = lean_ctor_get(v_x_1456_, 0);
v_tail_1458_ = lean_ctor_get(v_x_1456_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_x_1456_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1460_ = v_x_1456_;
v_isShared_1461_ = v_isSharedCheck_1467_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_tail_1458_);
lean_inc(v_head_1457_);
lean_dec(v_x_1456_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1467_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
lean_inc(v_x_1454_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set_tag(v___x_1460_, 5);
lean_ctor_set(v___x_1460_, 1, v_x_1454_);
lean_ctor_set(v___x_1460_, 0, v_x_1455_);
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_x_1455_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_x_1454_);
v___x_1463_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
lean_ctor_set(v___x_1464_, 1, v_head_1457_);
v_x_1455_ = v___x_1464_;
v_x_1456_ = v_tail_1458_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(lean_object* v_x_1468_, lean_object* v_x_1469_){
_start:
{
if (lean_obj_tag(v_x_1468_) == 0)
{
lean_object* v___x_1470_; 
lean_dec(v_x_1469_);
v___x_1470_ = lean_box(0);
return v___x_1470_;
}
else
{
lean_object* v_tail_1471_; 
v_tail_1471_ = lean_ctor_get(v_x_1468_, 1);
if (lean_obj_tag(v_tail_1471_) == 0)
{
lean_object* v_head_1472_; 
lean_dec(v_x_1469_);
v_head_1472_ = lean_ctor_get(v_x_1468_, 0);
lean_inc(v_head_1472_);
lean_dec_ref_known(v_x_1468_, 2);
return v_head_1472_;
}
else
{
lean_object* v_head_1473_; lean_object* v___x_1474_; 
lean_inc(v_tail_1471_);
v_head_1473_ = lean_ctor_get(v_x_1468_, 0);
lean_inc(v_head_1473_);
lean_dec_ref_known(v_x_1468_, 2);
v___x_1474_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(v_x_1469_, v_head_1473_, v_tail_1471_);
return v___x_1474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(lean_object* v_x_1475_, lean_object* v_x_1476_){
_start:
{
if (lean_obj_tag(v_x_1475_) == 0)
{
lean_object* v___x_1477_; 
v___x_1477_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1477_;
}
else
{
lean_object* v_val_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1490_; 
v_val_1478_ = lean_ctor_get(v_x_1475_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_x_1475_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1480_ = v_x_1475_;
v_isShared_1481_ = v_isSharedCheck_1490_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_val_1478_);
lean_dec(v_x_1475_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1490_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1482_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1483_ = lean_string_from_utf8_unchecked(v_val_1478_);
v___x_1484_ = l_String_quote(v___x_1483_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set_tag(v___x_1480_, 3);
lean_ctor_set(v___x_1480_, 0, v___x_1484_);
v___x_1486_ = v___x_1480_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1482_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = l_Repr_addAppParen(v___x_1487_, v_x_1476_);
return v___x_1488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1491_, lean_object* v_x_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_x_1491_, v_x_1492_);
lean_dec(v_x_1492_);
return v_res_1493_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0));
v___x_1497_ = lean_string_length(v___x_1496_);
return v___x_1497_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2);
v___x_1499_ = lean_nat_to_int(v___x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(lean_object* v_x_1504_){
_start:
{
lean_object* v_fst_1505_; lean_object* v_snd_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1531_; 
v_fst_1505_ = lean_ctor_get(v_x_1504_, 0);
v_snd_1506_ = lean_ctor_get(v_x_1504_, 1);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_x_1504_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1508_ = v_x_1504_;
v_isShared_1509_ = v_isSharedCheck_1531_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_snd_1506_);
lean_inc(v_fst_1505_);
lean_dec(v_x_1504_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1531_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1510_ = lean_string_from_utf8_unchecked(v_fst_1505_);
v___x_1511_ = l_String_quote(v___x_1510_);
v___x_1512_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
v___x_1513_ = lean_box(0);
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 1);
lean_ctor_set(v___x_1508_, 1, v___x_1513_);
lean_ctor_set(v___x_1508_, 0, v___x_1512_);
v___x_1515_ = v___x_1508_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; 
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_snd_1506_, v___x_1516_);
v___x_1518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
lean_ctor_set(v___x_1518_, 1, v___x_1515_);
v___x_1519_ = l_List_reverse___redArg(v___x_1518_);
v___x_1520_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1521_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(v___x_1519_, v___x_1520_);
v___x_1522_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3);
v___x_1523_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4));
v___x_1524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
lean_ctor_set(v___x_1524_, 1, v___x_1521_);
v___x_1525_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5));
v___x_1526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1522_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = 0;
v___x_1529_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set_uint8(v___x_1529_, sizeof(void*)*1, v___x_1528_);
return v___x_1529_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(lean_object* v_x_1532_, lean_object* v_x_1533_, lean_object* v_x_1534_){
_start:
{
if (lean_obj_tag(v_x_1534_) == 0)
{
lean_dec(v_x_1532_);
return v_x_1533_;
}
else
{
lean_object* v_head_1535_; lean_object* v_tail_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1546_; 
v_head_1535_ = lean_ctor_get(v_x_1534_, 0);
v_tail_1536_ = lean_ctor_get(v_x_1534_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_x_1534_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1538_ = v_x_1534_;
v_isShared_1539_ = v_isSharedCheck_1546_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_tail_1536_);
lean_inc(v_head_1535_);
lean_dec(v_x_1534_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1546_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
lean_inc(v_x_1532_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set_tag(v___x_1538_, 5);
lean_ctor_set(v___x_1538_, 1, v_x_1532_);
lean_ctor_set(v___x_1538_, 0, v_x_1533_);
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_x_1533_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_x_1532_);
v___x_1541_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1535_);
v___x_1543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v_x_1533_ = v___x_1543_;
v_x_1534_ = v_tail_1536_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(lean_object* v_x_1547_, lean_object* v_x_1548_, lean_object* v_x_1549_){
_start:
{
if (lean_obj_tag(v_x_1549_) == 0)
{
lean_dec(v_x_1547_);
return v_x_1548_;
}
else
{
lean_object* v_head_1550_; lean_object* v_tail_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1561_; 
v_head_1550_ = lean_ctor_get(v_x_1549_, 0);
v_tail_1551_ = lean_ctor_get(v_x_1549_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_x_1549_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1553_ = v_x_1549_;
v_isShared_1554_ = v_isSharedCheck_1561_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_tail_1551_);
lean_inc(v_head_1550_);
lean_dec(v_x_1549_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1561_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
lean_inc(v_x_1547_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set_tag(v___x_1553_, 5);
lean_ctor_set(v___x_1553_, 1, v_x_1547_);
lean_ctor_set(v___x_1553_, 0, v_x_1548_);
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_x_1548_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_x_1547_);
v___x_1556_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1550_);
v___x_1558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(v_x_1547_, v___x_1558_, v_tail_1551_);
return v___x_1559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(lean_object* v_x_1562_, lean_object* v_x_1563_){
_start:
{
if (lean_obj_tag(v_x_1562_) == 0)
{
lean_object* v___x_1564_; 
lean_dec(v_x_1563_);
v___x_1564_ = lean_box(0);
return v___x_1564_;
}
else
{
lean_object* v_tail_1565_; 
v_tail_1565_ = lean_ctor_get(v_x_1562_, 1);
if (lean_obj_tag(v_tail_1565_) == 0)
{
lean_object* v_head_1566_; lean_object* v___x_1567_; 
lean_dec(v_x_1563_);
v_head_1566_ = lean_ctor_get(v_x_1562_, 0);
lean_inc(v_head_1566_);
lean_dec_ref_known(v_x_1562_, 2);
v___x_1567_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1566_);
return v___x_1567_;
}
else
{
lean_object* v_head_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
lean_inc(v_tail_1565_);
v_head_1568_ = lean_ctor_get(v_x_1562_, 0);
lean_inc(v_head_1568_);
lean_dec_ref_known(v_x_1562_, 2);
v___x_1569_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1568_);
v___x_1570_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(v_x_1563_, v___x_1569_, v_tail_1565_);
return v___x_1570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(lean_object* v_xs_1571_){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1572_ = lean_array_get_size(v_xs_1571_);
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = lean_nat_dec_eq(v___x_1572_, v___x_1573_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1575_ = lean_array_to_list(v_xs_1571_);
v___x_1576_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1577_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(v___x_1575_, v___x_1576_);
v___x_1578_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1579_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
lean_ctor_set(v___x_1580_, 1, v___x_1577_);
v___x_1581_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1578_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = l_Std_Format_fill(v___x_1583_);
return v___x_1584_;
}
else
{
lean_object* v___x_1585_; 
lean_dec_ref(v_xs_1571_);
v___x_1585_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1585_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0(lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v___y_1586_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0___boxed(lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Std_Http_URI_instReprQuery___lam__0(v___y_1589_, v___y_1590_);
lean_dec(v___y_1590_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(lean_object* v_x_1594_, lean_object* v_x_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_x_1594_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___boxed(lean_object* v_x_1597_, lean_object* v_x_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(v_x_1597_, v_x_1598_);
lean_dec(v_x_1598_);
return v_res_1599_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1___lam__0(lean_object* v___f_1604_, lean_object* v_x_1605_, lean_object* v_x_1606_){
_start:
{
lean_object* v_fst_1607_; lean_object* v_snd_1608_; lean_object* v_fst_1609_; lean_object* v_snd_1610_; uint8_t v___x_1611_; 
v_fst_1607_ = lean_ctor_get(v_x_1605_, 0);
lean_inc(v_fst_1607_);
v_snd_1608_ = lean_ctor_get(v_x_1605_, 1);
lean_inc(v_snd_1608_);
lean_dec_ref(v_x_1605_);
v_fst_1609_ = lean_ctor_get(v_x_1606_, 0);
lean_inc(v_fst_1609_);
v_snd_1610_ = lean_ctor_get(v_x_1606_, 1);
lean_inc(v_snd_1610_);
lean_dec_ref(v_x_1606_);
v___x_1611_ = lean_sarray_dec_eq(v_fst_1607_, v_fst_1609_);
lean_dec(v_fst_1609_);
lean_dec(v_fst_1607_);
if (v___x_1611_ == 0)
{
lean_dec(v_snd_1610_);
lean_dec(v_snd_1608_);
lean_dec_ref(v___f_1604_);
return v___x_1611_;
}
else
{
uint8_t v___x_1612_; 
v___x_1612_ = l_instBEqOption_beq___redArg(v___f_1604_, v_snd_1608_, v_snd_1610_);
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___lam__0___boxed(lean_object* v___f_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_){
_start:
{
uint8_t v_res_1616_; lean_object* v_r_1617_; 
v_res_1616_ = l_Std_Http_URI_instBEqQuery___aux__1___lam__0(v___f_1613_, v_x_1614_, v_x_1615_);
v_r_1617_ = lean_box(v_res_1616_);
return v_r_1617_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1(lean_object* v_xs_1621_, lean_object* v_ys_1622_){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1623_ = lean_array_get_size(v_xs_1621_);
v___x_1624_ = lean_array_get_size(v_ys_1622_);
v___x_1625_ = lean_nat_dec_eq(v___x_1623_, v___x_1624_);
if (v___x_1625_ == 0)
{
return v___x_1625_;
}
else
{
lean_object* v___f_1626_; uint8_t v___x_1627_; 
v___f_1626_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__1));
v___x_1627_ = l_Array_isEqvAux___redArg(v_xs_1621_, v_ys_1622_, v___f_1626_, v___x_1623_);
return v___x_1627_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___boxed(lean_object* v_xs_1628_, lean_object* v_ys_1629_){
_start:
{
uint8_t v_res_1630_; lean_object* v_r_1631_; 
v_res_1630_ = l_Std_Http_URI_instBEqQuery___aux__1(v_xs_1628_, v_ys_1629_);
lean_dec_ref(v_ys_1629_);
lean_dec_ref(v_xs_1628_);
v_r_1631_ = lean_box(v_res_1630_);
return v_r_1631_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(lean_object* v_x_1632_, lean_object* v_x_1633_){
_start:
{
if (lean_obj_tag(v_x_1632_) == 0)
{
if (lean_obj_tag(v_x_1633_) == 0)
{
uint8_t v___x_1634_; 
v___x_1634_ = 1;
return v___x_1634_;
}
else
{
uint8_t v___x_1635_; 
v___x_1635_ = 0;
return v___x_1635_;
}
}
else
{
if (lean_obj_tag(v_x_1633_) == 0)
{
uint8_t v___x_1636_; 
v___x_1636_ = 0;
return v___x_1636_;
}
else
{
lean_object* v_val_1637_; lean_object* v_val_1638_; uint8_t v___x_1639_; 
v_val_1637_ = lean_ctor_get(v_x_1632_, 0);
v_val_1638_ = lean_ctor_get(v_x_1633_, 0);
v___x_1639_ = lean_sarray_dec_eq(v_val_1637_, v_val_1638_);
return v___x_1639_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0___boxed(lean_object* v_x_1640_, lean_object* v_x_1641_){
_start:
{
uint8_t v_res_1642_; lean_object* v_r_1643_; 
v_res_1642_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_x_1640_, v_x_1641_);
lean_dec(v_x_1641_);
lean_dec(v_x_1640_);
v_r_1643_ = lean_box(v_res_1642_);
return v_r_1643_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(lean_object* v_xs_1644_, lean_object* v_ys_1645_, lean_object* v_x_1646_){
_start:
{
lean_object* v_zero_1647_; uint8_t v_isZero_1648_; 
v_zero_1647_ = lean_unsigned_to_nat(0u);
v_isZero_1648_ = lean_nat_dec_eq(v_x_1646_, v_zero_1647_);
if (v_isZero_1648_ == 1)
{
lean_dec(v_x_1646_);
return v_isZero_1648_;
}
else
{
lean_object* v_one_1649_; lean_object* v_n_1650_; lean_object* v___x_1651_; lean_object* v_fst_1652_; lean_object* v_snd_1653_; lean_object* v___x_1654_; lean_object* v_fst_1655_; lean_object* v_snd_1656_; uint8_t v___x_1657_; 
v_one_1649_ = lean_unsigned_to_nat(1u);
v_n_1650_ = lean_nat_sub(v_x_1646_, v_one_1649_);
lean_dec(v_x_1646_);
v___x_1651_ = lean_array_fget_borrowed(v_xs_1644_, v_n_1650_);
v_fst_1652_ = lean_ctor_get(v___x_1651_, 0);
v_snd_1653_ = lean_ctor_get(v___x_1651_, 1);
v___x_1654_ = lean_array_fget_borrowed(v_ys_1645_, v_n_1650_);
v_fst_1655_ = lean_ctor_get(v___x_1654_, 0);
v_snd_1656_ = lean_ctor_get(v___x_1654_, 1);
v___x_1657_ = lean_sarray_dec_eq(v_fst_1652_, v_fst_1655_);
if (v___x_1657_ == 0)
{
lean_dec(v_n_1650_);
return v___x_1657_;
}
else
{
uint8_t v___x_1658_; 
v___x_1658_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_snd_1653_, v_snd_1656_);
if (v___x_1658_ == 0)
{
lean_dec(v_n_1650_);
return v___x_1658_;
}
else
{
v_x_1646_ = v_n_1650_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg___boxed(lean_object* v_xs_1660_, lean_object* v_ys_1661_, lean_object* v_x_1662_){
_start:
{
uint8_t v_res_1663_; lean_object* v_r_1664_; 
v_res_1663_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1660_, v_ys_1661_, v_x_1662_);
lean_dec_ref(v_ys_1661_);
lean_dec_ref(v_xs_1660_);
v_r_1664_ = lean_box(v_res_1663_);
return v_r_1664_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___lam__0(lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1667_ = lean_array_get_size(v___y_1665_);
v___x_1668_ = lean_array_get_size(v___y_1666_);
v___x_1669_ = lean_nat_dec_eq(v___x_1667_, v___x_1668_);
if (v___x_1669_ == 0)
{
return v___x_1669_;
}
else
{
uint8_t v___x_1670_; 
v___x_1670_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v___y_1665_, v___y_1666_, v___x_1667_);
return v___x_1670_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___lam__0___boxed(lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
uint8_t v_res_1673_; lean_object* v_r_1674_; 
v_res_1673_ = l_Std_Http_URI_instBEqQuery___lam__0(v___y_1671_, v___y_1672_);
lean_dec_ref(v___y_1672_);
lean_dec_ref(v___y_1671_);
v_r_1674_ = lean_box(v_res_1673_);
return v_r_1674_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(lean_object* v_xs_1677_, lean_object* v_ys_1678_, lean_object* v_hsz_1679_, lean_object* v_x_1680_, lean_object* v_x_1681_){
_start:
{
uint8_t v___x_1682_; 
v___x_1682_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1677_, v_ys_1678_, v_x_1680_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___boxed(lean_object* v_xs_1683_, lean_object* v_ys_1684_, lean_object* v_hsz_1685_, lean_object* v_x_1686_, lean_object* v_x_1687_){
_start:
{
uint8_t v_res_1688_; lean_object* v_r_1689_; 
v_res_1688_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(v_xs_1683_, v_ys_1684_, v_hsz_1685_, v_x_1686_, v_x_1687_);
lean_dec_ref(v_ys_1684_);
lean_dec_ref(v_xs_1683_);
v_r_1689_ = lean_box(v_res_1688_);
return v_r_1689_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(lean_object* v_as_1690_){
_start:
{
lean_object* v___f_1691_; lean_object* v___x_1692_; 
v___f_1691_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__0));
v___x_1692_ = l_List_eraseDupsBy___redArg(v___f_1691_, v_as_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(size_t v_sz_1693_, size_t v_i_1694_, lean_object* v_bs_1695_){
_start:
{
uint8_t v___x_1696_; 
v___x_1696_ = lean_usize_dec_lt(v_i_1694_, v_sz_1693_);
if (v___x_1696_ == 0)
{
return v_bs_1695_;
}
else
{
lean_object* v_v_1697_; lean_object* v_fst_1698_; lean_object* v___x_1699_; lean_object* v_bs_x27_1700_; size_t v___x_1701_; size_t v___x_1702_; lean_object* v___x_1703_; 
v_v_1697_ = lean_array_uget_borrowed(v_bs_1695_, v_i_1694_);
v_fst_1698_ = lean_ctor_get(v_v_1697_, 0);
lean_inc(v_fst_1698_);
v___x_1699_ = lean_unsigned_to_nat(0u);
v_bs_x27_1700_ = lean_array_uset(v_bs_1695_, v_i_1694_, v___x_1699_);
v___x_1701_ = ((size_t)1ULL);
v___x_1702_ = lean_usize_add(v_i_1694_, v___x_1701_);
v___x_1703_ = lean_array_uset(v_bs_x27_1700_, v_i_1694_, v_fst_1698_);
v_i_1694_ = v___x_1702_;
v_bs_1695_ = v___x_1703_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0___boxed(lean_object* v_sz_1705_, lean_object* v_i_1706_, lean_object* v_bs_1707_){
_start:
{
size_t v_sz_boxed_1708_; size_t v_i_boxed_1709_; lean_object* v_res_1710_; 
v_sz_boxed_1708_ = lean_unbox_usize(v_sz_1705_);
lean_dec(v_sz_1705_);
v_i_boxed_1709_ = lean_unbox_usize(v_i_1706_);
lean_dec(v_i_1706_);
v_res_1710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_boxed_1708_, v_i_boxed_1709_, v_bs_1707_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names(lean_object* v_query_1711_){
_start:
{
size_t v_sz_1712_; size_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v_sz_1712_ = lean_array_size(v_query_1711_);
v___x_1713_ = ((size_t)0ULL);
v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_1712_, v___x_1713_, v_query_1711_);
v___x_1715_ = lean_array_to_list(v___x_1714_);
v___x_1716_ = l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(v___x_1715_);
v___x_1717_ = lean_array_mk(v___x_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(size_t v_sz_1718_, size_t v_i_1719_, lean_object* v_bs_1720_){
_start:
{
uint8_t v___x_1721_; 
v___x_1721_ = lean_usize_dec_lt(v_i_1719_, v_sz_1718_);
if (v___x_1721_ == 0)
{
return v_bs_1720_;
}
else
{
lean_object* v_v_1722_; lean_object* v_snd_1723_; lean_object* v___x_1724_; lean_object* v_bs_x27_1725_; size_t v___x_1726_; size_t v___x_1727_; lean_object* v___x_1728_; 
v_v_1722_ = lean_array_uget_borrowed(v_bs_1720_, v_i_1719_);
v_snd_1723_ = lean_ctor_get(v_v_1722_, 1);
lean_inc(v_snd_1723_);
v___x_1724_ = lean_unsigned_to_nat(0u);
v_bs_x27_1725_ = lean_array_uset(v_bs_1720_, v_i_1719_, v___x_1724_);
v___x_1726_ = ((size_t)1ULL);
v___x_1727_ = lean_usize_add(v_i_1719_, v___x_1726_);
v___x_1728_ = lean_array_uset(v_bs_x27_1725_, v_i_1719_, v_snd_1723_);
v_i_1719_ = v___x_1727_;
v_bs_1720_ = v___x_1728_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0___boxed(lean_object* v_sz_1730_, lean_object* v_i_1731_, lean_object* v_bs_1732_){
_start:
{
size_t v_sz_boxed_1733_; size_t v_i_boxed_1734_; lean_object* v_res_1735_; 
v_sz_boxed_1733_ = lean_unbox_usize(v_sz_1730_);
lean_dec(v_sz_1730_);
v_i_boxed_1734_ = lean_unbox_usize(v_i_1731_);
lean_dec(v_i_1731_);
v_res_1735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_boxed_1733_, v_i_boxed_1734_, v_bs_1732_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_values(lean_object* v_query_1736_){
_start:
{
size_t v_sz_1737_; size_t v___x_1738_; lean_object* v___x_1739_; 
v_sz_1737_ = lean_array_size(v_query_1736_);
v___x_1738_ = ((size_t)0ULL);
v___x_1739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_1737_, v___x_1738_, v_query_1736_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray(lean_object* v_query_1740_){
_start:
{
lean_inc_ref(v_query_1740_);
return v_query_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray___boxed(lean_object* v_query_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Std_Http_URI_Query_toArray(v_query_1741_);
lean_dec_ref(v_query_1741_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object* v_key_1744_, lean_object* v_value_1745_){
_start:
{
if (lean_obj_tag(v_value_1745_) == 0)
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_string_from_utf8_unchecked(v_key_1744_);
return v___x_1746_;
}
else
{
lean_object* v_val_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v_val_1747_ = lean_ctor_get(v_value_1745_, 0);
lean_inc(v_val_1747_);
lean_dec_ref_known(v_value_1745_, 1);
v___x_1748_ = lean_string_from_utf8_unchecked(v_key_1744_);
v___x_1749_ = ((lean_object*)(l_Std_Http_URI_Query_formatQueryParam___closed__0));
v___x_1750_ = lean_string_append(v___x_1748_, v___x_1749_);
v___x_1751_ = lean_string_from_utf8_unchecked(v_val_1747_);
v___x_1752_ = lean_string_append(v___x_1750_, v___x_1751_);
lean_dec_ref(v___x_1751_);
return v___x_1752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(lean_object* v_key_1756_, lean_object* v_as_1757_, size_t v_sz_1758_, size_t v_i_1759_, lean_object* v_b_1760_){
_start:
{
uint8_t v___x_1761_; 
v___x_1761_ = lean_usize_dec_lt(v_i_1759_, v_sz_1758_);
if (v___x_1761_ == 0)
{
lean_inc_ref(v_b_1760_);
return v_b_1760_;
}
else
{
lean_object* v_a_1762_; lean_object* v_fst_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v_a_1762_ = lean_array_uget_borrowed(v_as_1757_, v_i_1759_);
v_fst_1763_ = lean_ctor_get(v_a_1762_, 0);
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_sarray_dec_eq(v_fst_1763_, v_key_1756_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; size_t v___x_1767_; size_t v___x_1768_; 
v___x_1766_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v___x_1767_ = ((size_t)1ULL);
v___x_1768_ = lean_usize_add(v_i_1759_, v___x_1767_);
v_i_1759_ = v___x_1768_;
v_b_1760_ = v___x_1766_;
goto _start;
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_inc(v_a_1762_);
v___x_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_a_1762_);
v___x_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v___x_1764_);
return v___x_1772_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___boxed(lean_object* v_key_1773_, lean_object* v_as_1774_, lean_object* v_sz_1775_, lean_object* v_i_1776_, lean_object* v_b_1777_){
_start:
{
size_t v_sz_boxed_1778_; size_t v_i_boxed_1779_; lean_object* v_res_1780_; 
v_sz_boxed_1778_ = lean_unbox_usize(v_sz_1775_);
lean_dec(v_sz_1775_);
v_i_boxed_1779_ = lean_unbox_usize(v_i_1776_);
lean_dec(v_i_1776_);
v_res_1780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1773_, v_as_1774_, v_sz_boxed_1778_, v_i_boxed_1779_, v_b_1777_);
lean_dec_ref(v_b_1777_);
lean_dec_ref(v_as_1774_);
lean_dec_ref(v_key_1773_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f(lean_object* v_query_1781_, lean_object* v_key_1782_){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; size_t v_sz_1785_; size_t v___x_1786_; lean_object* v___x_1787_; lean_object* v_fst_1788_; 
v___x_1783_ = lean_box(0);
v___x_1784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v_sz_1785_ = lean_array_size(v_query_1781_);
v___x_1786_ = ((size_t)0ULL);
v___x_1787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1782_, v_query_1781_, v_sz_1785_, v___x_1786_, v___x_1784_);
v_fst_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_fst_1788_);
lean_dec_ref(v___x_1787_);
if (lean_obj_tag(v_fst_1788_) == 0)
{
return v___x_1783_;
}
else
{
lean_object* v_val_1789_; 
v_val_1789_ = lean_ctor_get(v_fst_1788_, 0);
lean_inc(v_val_1789_);
lean_dec_ref_known(v_fst_1788_, 1);
if (lean_obj_tag(v_val_1789_) == 0)
{
return v___x_1783_;
}
else
{
lean_object* v_val_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1798_; 
v_val_1790_ = lean_ctor_get(v_val_1789_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_val_1789_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1792_ = v_val_1789_;
v_isShared_1793_ = v_isSharedCheck_1798_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_val_1790_);
lean_dec(v_val_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1798_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v_snd_1794_; lean_object* v___x_1796_; 
v_snd_1794_ = lean_ctor_get(v_val_1790_, 1);
lean_inc(v_snd_1794_);
lean_dec(v_val_1790_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v_snd_1794_);
v___x_1796_ = v___x_1792_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_snd_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f___boxed(lean_object* v_query_1799_, lean_object* v_key_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1799_, v_key_1800_);
lean_dec_ref(v_key_1800_);
lean_dec_ref(v_query_1799_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f(lean_object* v_query_1802_, lean_object* v_key_1803_){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1803_);
v___x_1805_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1802_, v___x_1804_);
lean_dec_ref(v___x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f___boxed(lean_object* v_query_1806_, lean_object* v_key_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Std_Http_URI_Query_find_x3f(v_query_1806_, v_key_1807_);
lean_dec_ref(v_key_1807_);
lean_dec_ref(v_query_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(lean_object* v_key_1809_, lean_object* v_as_1810_, size_t v_i_1811_, size_t v_stop_1812_, lean_object* v_b_1813_){
_start:
{
lean_object* v___y_1815_; uint8_t v___x_1819_; 
v___x_1819_ = lean_usize_dec_eq(v_i_1811_, v_stop_1812_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1820_; lean_object* v_fst_1821_; lean_object* v_snd_1822_; uint8_t v___x_1823_; 
v___x_1820_ = lean_array_uget_borrowed(v_as_1810_, v_i_1811_);
v_fst_1821_ = lean_ctor_get(v___x_1820_, 0);
v_snd_1822_ = lean_ctor_get(v___x_1820_, 1);
v___x_1823_ = lean_sarray_dec_eq(v_fst_1821_, v_key_1809_);
if (v___x_1823_ == 0)
{
v___y_1815_ = v_b_1813_;
goto v___jp_1814_;
}
else
{
lean_object* v___x_1824_; 
lean_inc(v_snd_1822_);
v___x_1824_ = lean_array_push(v_b_1813_, v_snd_1822_);
v___y_1815_ = v___x_1824_;
goto v___jp_1814_;
}
}
else
{
return v_b_1813_;
}
v___jp_1814_:
{
size_t v___x_1816_; size_t v___x_1817_; 
v___x_1816_ = ((size_t)1ULL);
v___x_1817_ = lean_usize_add(v_i_1811_, v___x_1816_);
v_i_1811_ = v___x_1817_;
v_b_1813_ = v___y_1815_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0___boxed(lean_object* v_key_1825_, lean_object* v_as_1826_, lean_object* v_i_1827_, lean_object* v_stop_1828_, lean_object* v_b_1829_){
_start:
{
size_t v_i_boxed_1830_; size_t v_stop_boxed_1831_; lean_object* v_res_1832_; 
v_i_boxed_1830_ = lean_unbox_usize(v_i_1827_);
lean_dec(v_i_1827_);
v_stop_boxed_1831_ = lean_unbox_usize(v_stop_1828_);
lean_dec(v_stop_1828_);
v_res_1832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1825_, v_as_1826_, v_i_boxed_1830_, v_stop_boxed_1831_, v_b_1829_);
lean_dec_ref(v_as_1826_);
lean_dec_ref(v_key_1825_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(lean_object* v_key_1835_, lean_object* v_as_1836_, lean_object* v_start_1837_, lean_object* v_stop_1838_){
_start:
{
lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_1840_ = lean_nat_dec_lt(v_start_1837_, v_stop_1838_);
if (v___x_1840_ == 0)
{
return v___x_1839_;
}
else
{
lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1841_ = lean_array_get_size(v_as_1836_);
v___x_1842_ = lean_nat_dec_le(v_stop_1838_, v___x_1841_);
if (v___x_1842_ == 0)
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_nat_dec_lt(v_start_1837_, v___x_1841_);
if (v___x_1843_ == 0)
{
return v___x_1839_;
}
else
{
size_t v___x_1844_; size_t v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_usize_of_nat(v_start_1837_);
v___x_1845_ = lean_usize_of_nat(v___x_1841_);
v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1835_, v_as_1836_, v___x_1844_, v___x_1845_, v___x_1839_);
return v___x_1846_;
}
}
else
{
size_t v___x_1847_; size_t v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_usize_of_nat(v_start_1837_);
v___x_1848_ = lean_usize_of_nat(v_stop_1838_);
v___x_1849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1835_, v_as_1836_, v___x_1847_, v___x_1848_, v___x_1839_);
return v___x_1849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___boxed(lean_object* v_key_1850_, lean_object* v_as_1851_, lean_object* v_start_1852_, lean_object* v_stop_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1850_, v_as_1851_, v_start_1852_, v_stop_1853_);
lean_dec(v_stop_1853_);
lean_dec(v_start_1852_);
lean_dec_ref(v_as_1851_);
lean_dec_ref(v_key_1850_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded(lean_object* v_query_1855_, lean_object* v_key_1856_){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = lean_unsigned_to_nat(0u);
v___x_1858_ = lean_array_get_size(v_query_1855_);
v___x_1859_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1856_, v_query_1855_, v___x_1857_, v___x_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded___boxed(lean_object* v_query_1860_, lean_object* v_key_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1860_, v_key_1861_);
lean_dec_ref(v_key_1861_);
lean_dec_ref(v_query_1860_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll(lean_object* v_query_1863_, lean_object* v_key_1864_){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1864_);
v___x_1866_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1863_, v___x_1865_);
lean_dec_ref(v___x_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll___boxed(lean_object* v_query_1867_, lean_object* v_key_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Std_Http_URI_Query_findAll(v_query_1867_, v_key_1868_);
lean_dec_ref(v_key_1868_);
lean_dec_ref(v_query_1867_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert(lean_object* v_query_1870_, lean_object* v_key_1871_, lean_object* v_value_1872_){
_start:
{
lean_object* v_encodedKey_1873_; lean_object* v_encodedValue_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_encodedKey_1873_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1871_);
v_encodedValue_1874_ = l_Std_Http_URI_EncodedQueryParam_encode(v_value_1872_);
v___x_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1875_, 0, v_encodedValue_1874_);
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v_encodedKey_1873_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = lean_array_push(v_query_1870_, v___x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert___boxed(lean_object* v_query_1878_, lean_object* v_key_1879_, lean_object* v_value_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Std_Http_URI_Query_insert(v_query_1878_, v_key_1879_, v_value_1880_);
lean_dec_ref(v_value_1880_);
lean_dec_ref(v_key_1879_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object* v_query_1882_, lean_object* v_key_1883_, lean_object* v_value_1884_){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v_key_1883_);
lean_ctor_set(v___x_1885_, 1, v_value_1884_);
v___x_1886_ = lean_array_push(v_query_1882_, v___x_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_ofList(lean_object* v_pairs_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_array_mk(v_pairs_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(lean_object* v_key_1892_, lean_object* v_as_1893_, size_t v_i_1894_, size_t v_stop_1895_){
_start:
{
uint8_t v___x_1896_; 
v___x_1896_ = lean_usize_dec_eq(v_i_1894_, v_stop_1895_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; lean_object* v_fst_1898_; uint8_t v___x_1899_; 
v___x_1897_ = lean_array_uget_borrowed(v_as_1893_, v_i_1894_);
v_fst_1898_ = lean_ctor_get(v___x_1897_, 0);
v___x_1899_ = lean_sarray_dec_eq(v_fst_1898_, v_key_1892_);
if (v___x_1899_ == 0)
{
size_t v___x_1900_; size_t v___x_1901_; 
v___x_1900_ = ((size_t)1ULL);
v___x_1901_ = lean_usize_add(v_i_1894_, v___x_1900_);
v_i_1894_ = v___x_1901_;
goto _start;
}
else
{
return v___x_1899_;
}
}
else
{
uint8_t v___x_1903_; 
v___x_1903_ = 0;
return v___x_1903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(lean_object* v_key_1904_, lean_object* v_as_1905_, lean_object* v_i_1906_, lean_object* v_stop_1907_){
_start:
{
size_t v_i_boxed_1908_; size_t v_stop_boxed_1909_; uint8_t v_res_1910_; lean_object* v_r_1911_; 
v_i_boxed_1908_ = lean_unbox_usize(v_i_1906_);
lean_dec(v_i_1906_);
v_stop_boxed_1909_ = lean_unbox_usize(v_stop_1907_);
lean_dec(v_stop_1907_);
v_res_1910_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1904_, v_as_1905_, v_i_boxed_1908_, v_stop_boxed_1909_);
lean_dec_ref(v_as_1905_);
lean_dec_ref(v_key_1904_);
v_r_1911_ = lean_box(v_res_1910_);
return v_r_1911_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_containsEncoded(lean_object* v_query_1912_, lean_object* v_key_1913_){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; 
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = lean_array_get_size(v_query_1912_);
v___x_1916_ = lean_nat_dec_lt(v___x_1914_, v___x_1915_);
if (v___x_1916_ == 0)
{
return v___x_1916_;
}
else
{
if (v___x_1916_ == 0)
{
return v___x_1916_;
}
else
{
size_t v___x_1917_; size_t v___x_1918_; uint8_t v___x_1919_; 
v___x_1917_ = ((size_t)0ULL);
v___x_1918_ = lean_usize_of_nat(v___x_1915_);
v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1913_, v_query_1912_, v___x_1917_, v___x_1918_);
return v___x_1919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_containsEncoded___boxed(lean_object* v_query_1920_, lean_object* v_key_1921_){
_start:
{
uint8_t v_res_1922_; lean_object* v_r_1923_; 
v_res_1922_ = l_Std_Http_URI_Query_containsEncoded(v_query_1920_, v_key_1921_);
lean_dec_ref(v_key_1921_);
lean_dec_ref(v_query_1920_);
v_r_1923_ = lean_box(v_res_1922_);
return v_r_1923_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_contains(lean_object* v_query_1924_, lean_object* v_key_1925_){
_start:
{
lean_object* v___x_1926_; uint8_t v___x_1927_; 
v___x_1926_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1925_);
v___x_1927_ = l_Std_Http_URI_Query_containsEncoded(v_query_1924_, v___x_1926_);
lean_dec_ref(v___x_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_contains___boxed(lean_object* v_query_1928_, lean_object* v_key_1929_){
_start:
{
uint8_t v_res_1930_; lean_object* v_r_1931_; 
v_res_1930_ = l_Std_Http_URI_Query_contains(v_query_1928_, v_key_1929_);
lean_dec_ref(v_key_1929_);
lean_dec_ref(v_query_1928_);
v_r_1931_ = lean_box(v_res_1930_);
return v_r_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(lean_object* v_key_1932_, lean_object* v_as_1933_, size_t v_i_1934_, size_t v_stop_1935_, lean_object* v_b_1936_){
_start:
{
lean_object* v___y_1938_; uint8_t v___x_1942_; 
v___x_1942_ = lean_usize_dec_eq(v_i_1934_, v_stop_1935_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v_fst_1946_; uint8_t v___x_1947_; 
v___x_1943_ = lean_array_uget_borrowed(v_as_1933_, v_i_1934_);
v_fst_1946_ = lean_ctor_get(v___x_1943_, 0);
v___x_1947_ = lean_sarray_dec_eq(v_fst_1946_, v_key_1932_);
if (v___x_1947_ == 0)
{
goto v___jp_1944_;
}
else
{
if (v___x_1942_ == 0)
{
v___y_1938_ = v_b_1936_;
goto v___jp_1937_;
}
else
{
goto v___jp_1944_;
}
}
v___jp_1944_:
{
lean_object* v___x_1945_; 
lean_inc(v___x_1943_);
v___x_1945_ = lean_array_push(v_b_1936_, v___x_1943_);
v___y_1938_ = v___x_1945_;
goto v___jp_1937_;
}
}
else
{
return v_b_1936_;
}
v___jp_1937_:
{
size_t v___x_1939_; size_t v___x_1940_; 
v___x_1939_ = ((size_t)1ULL);
v___x_1940_ = lean_usize_add(v_i_1934_, v___x_1939_);
v_i_1934_ = v___x_1940_;
v_b_1936_ = v___y_1938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(lean_object* v_key_1948_, lean_object* v_as_1949_, lean_object* v_i_1950_, lean_object* v_stop_1951_, lean_object* v_b_1952_){
_start:
{
size_t v_i_boxed_1953_; size_t v_stop_boxed_1954_; lean_object* v_res_1955_; 
v_i_boxed_1953_ = lean_unbox_usize(v_i_1950_);
lean_dec(v_i_1950_);
v_stop_boxed_1954_ = lean_unbox_usize(v_stop_1951_);
lean_dec(v_stop_1951_);
v_res_1955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1948_, v_as_1949_, v_i_boxed_1953_, v_stop_boxed_1954_, v_b_1952_);
lean_dec_ref(v_as_1949_);
lean_dec_ref(v_key_1948_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded(lean_object* v_query_1956_, lean_object* v_key_1957_){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v___x_1958_ = lean_unsigned_to_nat(0u);
v___x_1959_ = lean_array_get_size(v_query_1956_);
v___x_1960_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_1961_ = lean_nat_dec_lt(v___x_1958_, v___x_1959_);
if (v___x_1961_ == 0)
{
return v___x_1960_;
}
else
{
uint8_t v___x_1962_; 
v___x_1962_ = lean_nat_dec_le(v___x_1959_, v___x_1959_);
if (v___x_1962_ == 0)
{
if (v___x_1961_ == 0)
{
return v___x_1960_;
}
else
{
size_t v___x_1963_; size_t v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = ((size_t)0ULL);
v___x_1964_ = lean_usize_of_nat(v___x_1959_);
v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1957_, v_query_1956_, v___x_1963_, v___x_1964_, v___x_1960_);
return v___x_1965_;
}
}
else
{
size_t v___x_1966_; size_t v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = ((size_t)0ULL);
v___x_1967_ = lean_usize_of_nat(v___x_1959_);
v___x_1968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1957_, v_query_1956_, v___x_1966_, v___x_1967_, v___x_1960_);
return v___x_1968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded___boxed(lean_object* v_query_1969_, lean_object* v_key_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Std_Http_URI_Query_eraseEncoded(v_query_1969_, v_key_1970_);
lean_dec_ref(v_key_1970_);
lean_dec_ref(v_query_1969_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase(lean_object* v_query_1972_, lean_object* v_key_1973_){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1973_);
v___x_1975_ = l_Std_Http_URI_Query_eraseEncoded(v_query_1972_, v___x_1974_);
lean_dec_ref(v___x_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase___boxed(lean_object* v_query_1976_, lean_object* v_key_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Std_Http_URI_Query_erase(v_query_1976_, v_key_1977_);
lean_dec_ref(v_key_1977_);
lean_dec_ref(v_query_1976_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get(lean_object* v_query_1981_, lean_object* v_key_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Std_Http_URI_Query_find_x3f(v_query_1981_, v_key_1982_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v___x_1984_; 
v___x_1984_ = lean_box(0);
return v___x_1984_;
}
else
{
lean_object* v_val_1985_; 
v_val_1985_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_val_1985_);
lean_dec_ref_known(v___x_1983_, 1);
if (lean_obj_tag(v_val_1985_) == 0)
{
lean_object* v___x_1986_; 
v___x_1986_ = ((lean_object*)(l_Std_Http_URI_Query_get___closed__0));
return v___x_1986_;
}
else
{
lean_object* v_val_1987_; lean_object* v___x_1988_; 
v_val_1987_ = lean_ctor_get(v_val_1985_, 0);
lean_inc(v_val_1987_);
lean_dec_ref_known(v_val_1985_, 1);
v___x_1988_ = l_Std_Http_URI_EncodedQueryParam_decode(v_val_1987_);
lean_dec(v_val_1987_);
return v___x_1988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get___boxed(lean_object* v_query_1989_, lean_object* v_key_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Std_Http_URI_Query_get(v_query_1989_, v_key_1990_);
lean_dec_ref(v_key_1990_);
lean_dec_ref(v_query_1989_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD(lean_object* v_query_1992_, lean_object* v_key_1993_, lean_object* v_default_1994_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Std_Http_URI_Query_get(v_query_1992_, v_key_1993_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_inc_ref(v_default_1994_);
return v_default_1994_;
}
else
{
lean_object* v_val_1996_; 
v_val_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_val_1996_);
lean_dec_ref_known(v___x_1995_, 1);
return v_val_1996_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD___boxed(lean_object* v_query_1997_, lean_object* v_key_1998_, lean_object* v_default_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Std_Http_URI_Query_getD(v_query_1997_, v_key_1998_, v_default_1999_);
lean_dec_ref(v_default_1999_);
lean_dec_ref(v_key_1998_);
lean_dec_ref(v_query_1997_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set(lean_object* v_query_2001_, lean_object* v_key_2002_, lean_object* v_value_2003_){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = l_Std_Http_URI_Query_erase(v_query_2001_, v_key_2002_);
v___x_2005_ = l_Std_Http_URI_Query_insert(v___x_2004_, v_key_2002_, v_value_2003_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set___boxed(lean_object* v_query_2006_, lean_object* v_key_2007_, lean_object* v_value_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Std_Http_URI_Query_set(v_query_2006_, v_key_2007_, v_value_2008_);
lean_dec_ref(v_value_2008_);
lean_dec_ref(v_key_2007_);
lean_dec_ref(v_query_2006_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(size_t v_sz_2010_, size_t v_i_2011_, lean_object* v_bs_2012_){
_start:
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_usize_dec_lt(v_i_2011_, v_sz_2010_);
if (v___x_2013_ == 0)
{
return v_bs_2012_;
}
else
{
lean_object* v_v_2014_; lean_object* v_fst_2015_; lean_object* v_snd_2016_; lean_object* v___x_2017_; lean_object* v_bs_x27_2018_; lean_object* v___x_2019_; size_t v___x_2020_; size_t v___x_2021_; lean_object* v___x_2022_; 
v_v_2014_ = lean_array_uget_borrowed(v_bs_2012_, v_i_2011_);
v_fst_2015_ = lean_ctor_get(v_v_2014_, 0);
lean_inc(v_fst_2015_);
v_snd_2016_ = lean_ctor_get(v_v_2014_, 1);
lean_inc(v_snd_2016_);
v___x_2017_ = lean_unsigned_to_nat(0u);
v_bs_x27_2018_ = lean_array_uset(v_bs_2012_, v_i_2011_, v___x_2017_);
v___x_2019_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2015_, v_snd_2016_);
v___x_2020_ = ((size_t)1ULL);
v___x_2021_ = lean_usize_add(v_i_2011_, v___x_2020_);
v___x_2022_ = lean_array_uset(v_bs_x27_2018_, v_i_2011_, v___x_2019_);
v_i_2011_ = v___x_2021_;
v_bs_2012_ = v___x_2022_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0___boxed(lean_object* v_sz_2024_, lean_object* v_i_2025_, lean_object* v_bs_2026_){
_start:
{
size_t v_sz_boxed_2027_; size_t v_i_boxed_2028_; lean_object* v_res_2029_; 
v_sz_boxed_2027_ = lean_unbox_usize(v_sz_2024_);
lean_dec(v_sz_2024_);
v_i_boxed_2028_ = lean_unbox_usize(v_i_2025_);
lean_dec(v_i_2025_);
v_res_2029_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_boxed_2027_, v_i_boxed_2028_, v_bs_2026_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toRawString(lean_object* v_query_2031_){
_start:
{
size_t v_sz_2032_; size_t v___x_2033_; lean_object* v_params_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v_sz_2032_ = lean_array_size(v_query_2031_);
v___x_2033_ = ((size_t)0ULL);
v_params_2034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_2032_, v___x_2033_, v_query_2031_);
v___x_2035_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2036_ = lean_array_to_list(v_params_2034_);
v___x_2037_ = l_String_intercalate(v___x_2035_, v___x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0(lean_object* v_x_2039_){
_start:
{
lean_object* v_fst_2040_; lean_object* v_snd_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_fst_2040_ = lean_ctor_get(v_x_2039_, 0);
v_snd_2041_ = lean_ctor_get(v_x_2039_, 1);
v___x_2042_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
v___x_2043_ = l_Std_Http_URI_Query_insert(v___x_2042_, v_fst_2040_, v_snd_2041_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0___boxed(lean_object* v_x_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Std_Http_URI_Query_instSingletonProdString___lam__0(v_x_2044_);
lean_dec_ref(v_x_2044_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0(lean_object* v_x_2048_, lean_object* v_q_2049_){
_start:
{
lean_object* v_fst_2050_; lean_object* v_snd_2051_; lean_object* v___x_2052_; 
v_fst_2050_ = lean_ctor_get(v_x_2048_, 0);
v_snd_2051_ = lean_ctor_get(v_x_2048_, 1);
v___x_2052_ = l_Std_Http_URI_Query_insert(v_q_2049_, v_fst_2050_, v_snd_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0___boxed(lean_object* v_x_2053_, lean_object* v_q_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Std_Http_URI_Query_instInsertProdString___lam__0(v_x_2053_, v_q_2054_);
lean_dec_ref(v_x_2053_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__0(lean_object* v_x_2058_){
_start:
{
lean_object* v_fst_2059_; lean_object* v_snd_2060_; lean_object* v___x_2061_; 
v_fst_2059_ = lean_ctor_get(v_x_2058_, 0);
lean_inc(v_fst_2059_);
v_snd_2060_ = lean_ctor_get(v_x_2058_, 1);
lean_inc(v_snd_2060_);
lean_dec_ref(v_x_2058_);
v___x_2061_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2059_, v_snd_2060_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__1(lean_object* v___f_2063_, lean_object* v_q_2064_){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2065_ = lean_array_get_size(v_q_2064_);
v___x_2066_ = lean_unsigned_to_nat(0u);
v___x_2067_ = lean_nat_dec_eq(v___x_2065_, v___x_2066_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v_encodedParams_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2068_ = lean_array_to_list(v_q_2064_);
v___x_2069_ = lean_box(0);
v_encodedParams_2070_ = l_List_mapTR_loop___redArg(v___f_2063_, v___x_2068_, v___x_2069_);
v___x_2071_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2072_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2073_ = l_String_intercalate(v___x_2072_, v_encodedParams_2070_);
v___x_2074_ = lean_string_append(v___x_2071_, v___x_2073_);
lean_dec_ref(v___x_2073_);
return v___x_2074_;
}
else
{
lean_object* v___x_2075_; 
lean_dec_ref(v_q_2064_);
lean_dec_ref(v___f_2063_);
v___x_2075_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2075_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
if (lean_obj_tag(v_a_2080_) == 0)
{
lean_object* v___x_2082_; 
v___x_2082_ = l_List_reverse___redArg(v_a_2081_);
return v___x_2082_;
}
else
{
lean_object* v_head_2083_; lean_object* v_tail_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2095_; 
v_head_2083_ = lean_ctor_get(v_a_2080_, 0);
v_tail_2084_ = lean_ctor_get(v_a_2080_, 1);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_a_2080_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2086_ = v_a_2080_;
v_isShared_2087_ = v_isSharedCheck_2095_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_tail_2084_);
lean_inc(v_head_2083_);
lean_dec(v_a_2080_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2095_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v_fst_2088_; lean_object* v_snd_2089_; lean_object* v___x_2090_; lean_object* v___x_2092_; 
v_fst_2088_ = lean_ctor_get(v_head_2083_, 0);
lean_inc(v_fst_2088_);
v_snd_2089_ = lean_ctor_get(v_head_2083_, 1);
lean_inc(v_snd_2089_);
lean_dec(v_head_2083_);
v___x_2090_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2088_, v_snd_2089_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 1, v_a_2081_);
lean_ctor_set(v___x_2086_, 0, v___x_2090_);
v___x_2092_ = v___x_2086_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_a_2081_);
v___x_2092_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
v_a_2080_ = v_tail_2084_;
v_a_2081_ = v___x_2092_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatOption(lean_object* v_x_2096_){
_start:
{
if (lean_obj_tag(v_x_2096_) == 0)
{
lean_object* v___x_2097_; 
v___x_2097_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2097_;
}
else
{
lean_object* v_val_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v_val_2098_ = lean_ctor_get(v_x_2096_, 0);
lean_inc(v_val_2098_);
lean_dec_ref_known(v_x_2096_, 1);
v___x_2099_ = lean_array_get_size(v_val_2098_);
v___x_2100_ = lean_unsigned_to_nat(0u);
v___x_2101_ = lean_nat_dec_eq(v___x_2099_, v___x_2100_);
if (v___x_2101_ == 0)
{
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v_encodedParams_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2102_ = lean_array_to_list(v_val_2098_);
v___x_2103_ = lean_box(0);
v_encodedParams_2104_ = l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(v___x_2102_, v___x_2103_);
v___x_2105_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2106_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2107_ = l_String_intercalate(v___x_2106_, v_encodedParams_2104_);
v___x_2108_ = lean_string_append(v___x_2105_, v___x_2107_);
lean_dec_ref(v___x_2107_);
return v___x_2108_;
}
else
{
lean_object* v___x_2109_; 
lean_dec(v_val_2098_);
v___x_2109_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2109_;
}
}
else
{
lean_object* v___x_2110_; 
lean_dec(v_val_2098_);
v___x_2110_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
return v___x_2110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(lean_object* v_x_2111_, lean_object* v_x_2112_){
_start:
{
if (lean_obj_tag(v_x_2111_) == 0)
{
lean_object* v___x_2113_; 
v___x_2113_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2113_;
}
else
{
lean_object* v_val_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_val_2114_ = lean_ctor_get(v_x_2111_, 0);
lean_inc(v_val_2114_);
lean_dec_ref_known(v_x_2111_, 1);
v___x_2115_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2116_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_val_2114_);
v___x_2117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2115_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = l_Repr_addAppParen(v___x_2117_, v_x_2112_);
return v___x_2118_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(lean_object* v_x_2119_, lean_object* v_x_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_x_2119_, v_x_2120_);
lean_dec(v_x_2120_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object* v_x_2122_, lean_object* v_x_2123_){
_start:
{
if (lean_obj_tag(v_x_2122_) == 0)
{
lean_object* v___x_2124_; 
v___x_2124_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2124_;
}
else
{
lean_object* v_val_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v_val_2125_ = lean_ctor_get(v_x_2122_, 0);
lean_inc(v_val_2125_);
lean_dec_ref_known(v_x_2122_, 1);
v___x_2126_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2127_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_val_2125_);
v___x_2128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2126_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = l_Repr_addAppParen(v___x_2128_, v_x_2123_);
return v___x_2129_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1___boxed(lean_object* v_x_2130_, lean_object* v_x_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_x_2130_, v_x_2131_);
lean_dec(v_x_2131_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(lean_object* v_x_2133_, lean_object* v_x_2134_){
_start:
{
if (lean_obj_tag(v_x_2133_) == 0)
{
lean_object* v___x_2135_; 
v___x_2135_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2135_;
}
else
{
lean_object* v_val_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2147_; 
v_val_2136_ = lean_ctor_get(v_x_2133_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_x_2133_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2138_ = v_x_2133_;
v_isShared_2139_ = v_isSharedCheck_2147_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_val_2136_);
lean_dec(v_x_2133_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2147_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2140_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2141_ = l_String_quote(v_val_2136_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set_tag(v___x_2138_, 3);
lean_ctor_set(v___x_2138_, 0, v___x_2141_);
v___x_2143_ = v___x_2138_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2140_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = l_Repr_addAppParen(v___x_2144_, v_x_2134_);
return v___x_2145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2___boxed(lean_object* v_x_2148_, lean_object* v_x_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_x_2148_, v_x_2149_);
lean_dec(v_x_2149_);
return v_res_2150_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = lean_unsigned_to_nat(10u);
v___x_2161_ = lean_nat_to_int(v___x_2160_);
return v___x_2161_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_unsigned_to_nat(13u);
v___x_2166_ = lean_nat_to_int(v___x_2165_);
return v___x_2166_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_unsigned_to_nat(9u);
v___x_2174_ = lean_nat_to_int(v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___redArg(lean_object* v_x_2178_){
_start:
{
lean_object* v_scheme_2179_; lean_object* v_authority_2180_; lean_object* v_path_2181_; lean_object* v_query_2182_; lean_object* v_fragment_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v_scheme_2179_ = lean_ctor_get(v_x_2178_, 0);
lean_inc_ref(v_scheme_2179_);
v_authority_2180_ = lean_ctor_get(v_x_2178_, 1);
lean_inc(v_authority_2180_);
v_path_2181_ = lean_ctor_get(v_x_2178_, 2);
lean_inc_ref(v_path_2181_);
v_query_2182_ = lean_ctor_get(v_x_2178_, 3);
lean_inc(v_query_2182_);
v_fragment_2183_ = lean_ctor_get(v_x_2178_, 4);
lean_inc(v_fragment_2183_);
lean_dec_ref(v_x_2178_);
v___x_2184_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2185_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2186_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2187_ = l_String_quote(v_scheme_2179_);
v___x_2188_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
v___x_2189_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2186_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = 0;
v___x_2191_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set_uint8(v___x_2191_, sizeof(void*)*1, v___x_2190_);
v___x_2192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2185_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___x_2193_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2192_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
v___x_2195_ = lean_box(1);
v___x_2196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2194_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
v___x_2197_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__6));
v___x_2198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2196_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
v___x_2199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
lean_ctor_set(v___x_2199_, 1, v___x_2184_);
v___x_2200_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_2180_, v___x_2201_);
v___x_2203_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2200_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*1, v___x_2190_);
v___x_2205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2199_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v___x_2193_);
v___x_2207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
lean_ctor_set(v___x_2207_, 1, v___x_2195_);
v___x_2208_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_2209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2207_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v___x_2184_);
v___x_2211_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2212_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_2181_);
v___x_2213_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2211_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
lean_ctor_set_uint8(v___x_2214_, sizeof(void*)*1, v___x_2190_);
v___x_2215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2210_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v___x_2193_);
v___x_2217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
lean_ctor_set(v___x_2217_, 1, v___x_2195_);
v___x_2218_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_2219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2217_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
lean_ctor_set(v___x_2220_, 1, v___x_2184_);
v___x_2221_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_2222_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_2182_, v___x_2201_);
v___x_2223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2221_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
v___x_2224_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
lean_ctor_set_uint8(v___x_2224_, sizeof(void*)*1, v___x_2190_);
v___x_2225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2220_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
v___x_2226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
lean_ctor_set(v___x_2226_, 1, v___x_2193_);
v___x_2227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set(v___x_2227_, 1, v___x_2195_);
v___x_2228_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_2229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2227_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
v___x_2230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set(v___x_2230_, 1, v___x_2184_);
v___x_2231_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_2232_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_2183_, v___x_2201_);
v___x_2233_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2231_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
v___x_2234_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
lean_ctor_set_uint8(v___x_2234_, sizeof(void*)*1, v___x_2190_);
v___x_2235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2230_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
v___x_2236_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2237_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
lean_ctor_set(v___x_2238_, 1, v___x_2235_);
v___x_2239_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2238_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2236_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*1, v___x_2190_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr(lean_object* v_x_2243_, lean_object* v_prec_2244_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Std_Http_instReprURI_repr___redArg(v_x_2243_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___boxed(lean_object* v_x_2246_, lean_object* v_prec_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Std_Http_instReprURI_repr(v_x_2246_, v_prec_2247_);
lean_dec(v_prec_2247_);
return v_res_2248_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object* v_x_2257_, lean_object* v_x_2258_){
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
lean_object* v_val_2262_; lean_object* v_val_2263_; uint8_t v___x_2264_; 
v_val_2262_ = lean_ctor_get(v_x_2257_, 0);
v_val_2263_ = lean_ctor_get(v_x_2258_, 0);
v___x_2264_ = l_Std_Http_URI_instBEqAuthority_beq(v_val_2262_, v_val_2263_);
return v___x_2264_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object* v_x_2265_, lean_object* v_x_2266_){
_start:
{
uint8_t v_res_2267_; lean_object* v_r_2268_; 
v_res_2267_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_x_2265_, v_x_2266_);
lean_dec(v_x_2266_);
lean_dec(v_x_2265_);
v_r_2268_ = lean_box(v_res_2267_);
return v_r_2268_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object* v_x_2269_, lean_object* v_x_2270_){
_start:
{
if (lean_obj_tag(v_x_2269_) == 0)
{
if (lean_obj_tag(v_x_2270_) == 0)
{
uint8_t v___x_2271_; 
v___x_2271_ = 1;
return v___x_2271_;
}
else
{
uint8_t v___x_2272_; 
v___x_2272_ = 0;
return v___x_2272_;
}
}
else
{
if (lean_obj_tag(v_x_2270_) == 0)
{
uint8_t v___x_2273_; 
v___x_2273_ = 0;
return v___x_2273_;
}
else
{
lean_object* v_val_2274_; lean_object* v_val_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v_val_2274_ = lean_ctor_get(v_x_2269_, 0);
v_val_2275_ = lean_ctor_get(v_x_2270_, 0);
v___x_2276_ = lean_array_get_size(v_val_2274_);
v___x_2277_ = lean_array_get_size(v_val_2275_);
v___x_2278_ = lean_nat_dec_eq(v___x_2276_, v___x_2277_);
if (v___x_2278_ == 0)
{
return v___x_2278_;
}
else
{
uint8_t v___x_2279_; 
v___x_2279_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_val_2274_, v_val_2275_, v___x_2276_);
return v___x_2279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object* v_x_2280_, lean_object* v_x_2281_){
_start:
{
uint8_t v_res_2282_; lean_object* v_r_2283_; 
v_res_2282_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_x_2280_, v_x_2281_);
lean_dec(v_x_2281_);
lean_dec(v_x_2280_);
v_r_2283_ = lean_box(v_res_2282_);
return v_r_2283_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(lean_object* v_x_2284_, lean_object* v_x_2285_){
_start:
{
if (lean_obj_tag(v_x_2284_) == 0)
{
if (lean_obj_tag(v_x_2285_) == 0)
{
uint8_t v___x_2286_; 
v___x_2286_ = 1;
return v___x_2286_;
}
else
{
uint8_t v___x_2287_; 
v___x_2287_ = 0;
return v___x_2287_;
}
}
else
{
if (lean_obj_tag(v_x_2285_) == 0)
{
uint8_t v___x_2288_; 
v___x_2288_ = 0;
return v___x_2288_;
}
else
{
lean_object* v_val_2289_; lean_object* v_val_2290_; uint8_t v___x_2291_; 
v_val_2289_ = lean_ctor_get(v_x_2284_, 0);
v_val_2290_ = lean_ctor_get(v_x_2285_, 0);
v___x_2291_ = lean_string_dec_eq(v_val_2289_, v_val_2290_);
return v___x_2291_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2___boxed(lean_object* v_x_2292_, lean_object* v_x_2293_){
_start:
{
uint8_t v_res_2294_; lean_object* v_r_2295_; 
v_res_2294_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_x_2292_, v_x_2293_);
lean_dec(v_x_2293_);
lean_dec(v_x_2292_);
v_r_2295_ = lean_box(v_res_2294_);
return v_r_2295_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object* v_x_2296_, lean_object* v_x_2297_){
_start:
{
lean_object* v_scheme_2298_; lean_object* v_authority_2299_; lean_object* v_path_2300_; lean_object* v_query_2301_; lean_object* v_fragment_2302_; lean_object* v_scheme_2303_; lean_object* v_authority_2304_; lean_object* v_path_2305_; lean_object* v_query_2306_; lean_object* v_fragment_2307_; uint8_t v___x_2308_; 
v_scheme_2298_ = lean_ctor_get(v_x_2296_, 0);
v_authority_2299_ = lean_ctor_get(v_x_2296_, 1);
v_path_2300_ = lean_ctor_get(v_x_2296_, 2);
v_query_2301_ = lean_ctor_get(v_x_2296_, 3);
v_fragment_2302_ = lean_ctor_get(v_x_2296_, 4);
v_scheme_2303_ = lean_ctor_get(v_x_2297_, 0);
v_authority_2304_ = lean_ctor_get(v_x_2297_, 1);
v_path_2305_ = lean_ctor_get(v_x_2297_, 2);
v_query_2306_ = lean_ctor_get(v_x_2297_, 3);
v_fragment_2307_ = lean_ctor_get(v_x_2297_, 4);
v___x_2308_ = lean_string_dec_eq(v_scheme_2298_, v_scheme_2303_);
if (v___x_2308_ == 0)
{
return v___x_2308_;
}
else
{
uint8_t v___x_2309_; 
v___x_2309_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_2299_, v_authority_2304_);
if (v___x_2309_ == 0)
{
return v___x_2309_;
}
else
{
uint8_t v___x_2310_; 
v___x_2310_ = l_Std_Http_URI_instBEqPath_beq(v_path_2300_, v_path_2305_);
if (v___x_2310_ == 0)
{
return v___x_2310_;
}
else
{
uint8_t v___x_2311_; 
v___x_2311_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_2301_, v_query_2306_);
if (v___x_2311_ == 0)
{
return v___x_2311_;
}
else
{
uint8_t v___x_2312_; 
v___x_2312_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_2302_, v_fragment_2307_);
return v___x_2312_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object* v_x_2313_, lean_object* v_x_2314_){
_start:
{
uint8_t v_res_2315_; lean_object* v_r_2316_; 
v_res_2315_ = l_Std_Http_instBEqURI_beq(v_x_2313_, v_x_2314_);
lean_dec_ref(v_x_2314_);
lean_dec_ref(v_x_2313_);
v_r_2316_ = lean_box(v_res_2315_);
return v_r_2316_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__1(lean_object* v___f_2321_, lean_object* v_uri_2322_){
_start:
{
lean_object* v_scheme_2323_; lean_object* v_authority_2324_; lean_object* v_path_2325_; lean_object* v_query_2326_; lean_object* v_fragment_2327_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2350_; 
v_scheme_2323_ = lean_ctor_get(v_uri_2322_, 0);
lean_inc_ref(v_scheme_2323_);
v_authority_2324_ = lean_ctor_get(v_uri_2322_, 1);
lean_inc(v_authority_2324_);
v_path_2325_ = lean_ctor_get(v_uri_2322_, 2);
lean_inc_ref(v_path_2325_);
v_query_2326_ = lean_ctor_get(v_uri_2322_, 3);
lean_inc(v_query_2326_);
v_fragment_2327_ = lean_ctor_get(v_uri_2322_, 4);
lean_inc(v_fragment_2327_);
lean_dec_ref(v_uri_2322_);
if (lean_obj_tag(v_authority_2324_) == 0)
{
lean_object* v___x_2361_; 
v___x_2361_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2350_ = v___x_2361_;
goto v___jp_2349_;
}
else
{
lean_object* v_val_2362_; lean_object* v_userInfo_2363_; lean_object* v_host_2364_; lean_object* v_port_2365_; lean_object* v___x_2366_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2385_; 
v_val_2362_ = lean_ctor_get(v_authority_2324_, 0);
lean_inc(v_val_2362_);
lean_dec_ref_known(v_authority_2324_, 1);
v_userInfo_2363_ = lean_ctor_get(v_val_2362_, 0);
lean_inc(v_userInfo_2363_);
v_host_2364_ = lean_ctor_get(v_val_2362_, 1);
lean_inc_ref(v_host_2364_);
v_port_2365_ = lean_ctor_get(v_val_2362_, 2);
lean_inc(v_port_2365_);
lean_dec(v_val_2362_);
v___x_2366_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_2363_) == 0)
{
lean_object* v___x_2395_; 
v___x_2395_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2385_ = v___x_2395_;
goto v___jp_2384_;
}
else
{
lean_object* v_val_2396_; lean_object* v_password_2397_; 
v_val_2396_ = lean_ctor_get(v_userInfo_2363_, 0);
lean_inc(v_val_2396_);
lean_dec_ref_known(v_userInfo_2363_, 1);
v_password_2397_ = lean_ctor_get(v_val_2396_, 1);
if (lean_obj_tag(v_password_2397_) == 0)
{
lean_object* v_username_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_username_2398_ = lean_ctor_get(v_val_2396_, 0);
lean_inc_ref(v_username_2398_);
lean_dec(v_val_2396_);
v___x_2399_ = lean_string_from_utf8_unchecked(v_username_2398_);
v___x_2400_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2401_ = lean_string_append(v___x_2399_, v___x_2400_);
v___y_2385_ = v___x_2401_;
goto v___jp_2384_;
}
else
{
lean_object* v_username_2402_; lean_object* v_val_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_inc_ref(v_password_2397_);
v_username_2402_ = lean_ctor_get(v_val_2396_, 0);
lean_inc_ref(v_username_2402_);
lean_dec(v_val_2396_);
v_val_2403_ = lean_ctor_get(v_password_2397_, 0);
lean_inc(v_val_2403_);
lean_dec_ref_known(v_password_2397_, 1);
v___x_2404_ = lean_string_from_utf8_unchecked(v_username_2402_);
v___x_2405_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2406_ = lean_string_append(v___x_2404_, v___x_2405_);
v___x_2407_ = lean_string_from_utf8_unchecked(v_val_2403_);
v___x_2408_ = lean_string_append(v___x_2406_, v___x_2407_);
lean_dec_ref(v___x_2407_);
v___x_2409_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2410_ = lean_string_append(v___x_2408_, v___x_2409_);
v___y_2385_ = v___x_2410_;
goto v___jp_2384_;
}
}
v___jp_2367_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2371_ = lean_string_append(v___y_2369_, v___y_2368_);
lean_dec_ref(v___y_2368_);
v___x_2372_ = lean_string_append(v___x_2371_, v___y_2370_);
lean_dec_ref(v___y_2370_);
v___x_2373_ = lean_string_append(v___x_2366_, v___x_2372_);
lean_dec_ref(v___x_2372_);
v___y_2350_ = v___x_2373_;
goto v___jp_2349_;
}
v___jp_2374_:
{
switch(lean_obj_tag(v_port_2365_))
{
case 0:
{
lean_object* v___x_2377_; 
v___x_2377_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2368_ = v___y_2376_;
v___y_2369_ = v___y_2375_;
v___y_2370_ = v___x_2377_;
goto v___jp_2367_;
}
case 1:
{
lean_object* v___x_2378_; 
v___x_2378_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_2368_ = v___y_2376_;
v___y_2369_ = v___y_2375_;
v___y_2370_ = v___x_2378_;
goto v___jp_2367_;
}
default: 
{
uint16_t v_port_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v_port_2379_ = lean_ctor_get_uint16(v_port_2365_, 0);
lean_dec_ref_known(v_port_2365_, 0);
v___x_2380_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2381_ = lean_uint16_to_nat(v_port_2379_);
v___x_2382_ = l_Nat_reprFast(v___x_2381_);
v___x_2383_ = lean_string_append(v___x_2380_, v___x_2382_);
lean_dec_ref(v___x_2382_);
v___y_2368_ = v___y_2376_;
v___y_2369_ = v___y_2375_;
v___y_2370_ = v___x_2383_;
goto v___jp_2367_;
}
}
}
v___jp_2384_:
{
switch(lean_obj_tag(v_host_2364_))
{
case 0:
{
lean_object* v_name_2386_; 
v_name_2386_ = lean_ctor_get(v_host_2364_, 0);
lean_inc_ref(v_name_2386_);
lean_dec_ref_known(v_host_2364_, 1);
v___y_2375_ = v___y_2385_;
v___y_2376_ = v_name_2386_;
goto v___jp_2374_;
}
case 1:
{
lean_object* v_ipv4_2387_; lean_object* v___x_2388_; 
v_ipv4_2387_ = lean_ctor_get(v_host_2364_, 0);
lean_inc_ref(v_ipv4_2387_);
lean_dec_ref_known(v_host_2364_, 1);
v___x_2388_ = lean_uv_ntop_v4(v_ipv4_2387_);
lean_dec_ref(v_ipv4_2387_);
v___y_2375_ = v___y_2385_;
v___y_2376_ = v___x_2388_;
goto v___jp_2374_;
}
default: 
{
lean_object* v_ipv6_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v_ipv6_2389_ = lean_ctor_get(v_host_2364_, 0);
lean_inc_ref(v_ipv6_2389_);
lean_dec_ref_known(v_host_2364_, 1);
v___x_2390_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_2391_ = lean_uv_ntop_v6(v_ipv6_2389_);
lean_dec_ref(v_ipv6_2389_);
v___x_2392_ = lean_string_append(v___x_2390_, v___x_2391_);
lean_dec_ref(v___x_2391_);
v___x_2393_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_2394_ = lean_string_append(v___x_2392_, v___x_2393_);
v___y_2375_ = v___y_2385_;
v___y_2376_ = v___x_2394_;
goto v___jp_2374_;
}
}
}
}
v___jp_2328_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2333_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2334_ = lean_string_append(v_scheme_2323_, v___x_2333_);
v___x_2335_ = lean_string_append(v___x_2334_, v___y_2331_);
lean_dec_ref(v___y_2331_);
v___x_2336_ = lean_string_append(v___x_2335_, v___y_2329_);
lean_dec_ref(v___y_2329_);
v___x_2337_ = lean_string_append(v___x_2336_, v___y_2330_);
lean_dec_ref(v___y_2330_);
v___x_2338_ = lean_string_append(v___x_2337_, v___y_2332_);
lean_dec_ref(v___y_2332_);
return v___x_2338_;
}
v___jp_2339_:
{
lean_object* v_queryPart_2342_; 
v_queryPart_2342_ = l_Std_Http_URI_Query_formatOption(v_query_2326_);
if (lean_obj_tag(v_fragment_2327_) == 0)
{
lean_object* v___x_2343_; 
v___x_2343_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2329_ = v___y_2341_;
v___y_2330_ = v_queryPart_2342_;
v___y_2331_ = v___y_2340_;
v___y_2332_ = v___x_2343_;
goto v___jp_2328_;
}
else
{
lean_object* v_val_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v_val_2344_ = lean_ctor_get(v_fragment_2327_, 0);
lean_inc(v_val_2344_);
lean_dec_ref_known(v_fragment_2327_, 1);
v___x_2345_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_2346_ = l_Std_Http_URI_EncodedFragment_encode(v_val_2344_);
lean_dec(v_val_2344_);
v___x_2347_ = lean_string_from_utf8_unchecked(v___x_2346_);
v___x_2348_ = lean_string_append(v___x_2345_, v___x_2347_);
lean_dec_ref(v___x_2347_);
v___y_2329_ = v___y_2341_;
v___y_2330_ = v_queryPart_2342_;
v___y_2331_ = v___y_2340_;
v___y_2332_ = v___x_2348_;
goto v___jp_2328_;
}
}
v___jp_2349_:
{
lean_object* v_segments_2351_; uint8_t v_absolute_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; size_t v_sz_2355_; size_t v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v_result_2359_; 
v_segments_2351_ = lean_ctor_get(v_path_2325_, 0);
lean_inc_ref(v_segments_2351_);
v_absolute_2352_ = lean_ctor_get_uint8(v_path_2325_, sizeof(void*)*1);
lean_dec_ref(v_path_2325_);
v___x_2353_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_2354_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_2355_ = lean_array_size(v_segments_2351_);
v___x_2356_ = ((size_t)0ULL);
v___x_2357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2354_, v___f_2321_, v_sz_2355_, v___x_2356_, v_segments_2351_);
v___x_2358_ = lean_array_to_list(v___x_2357_);
v_result_2359_ = l_String_intercalate(v___x_2353_, v___x_2358_);
if (v_absolute_2352_ == 0)
{
v___y_2340_ = v___y_2350_;
v___y_2341_ = v_result_2359_;
goto v___jp_2339_;
}
else
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_string_append(v___x_2353_, v_result_2359_);
lean_dec_ref(v_result_2359_);
v___y_2340_ = v___y_2350_;
v___y_2341_ = v___x_2360_;
goto v___jp_2339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x3f(lean_object* v_b_2423_, lean_object* v_scheme_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Std_Http_URI_Scheme_ofString_x3f(v_scheme_2424_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v___x_2426_; 
lean_dec_ref(v_b_2423_);
v___x_2426_ = lean_box(0);
return v___x_2426_;
}
else
{
lean_object* v_userInfo_2427_; lean_object* v_host_2428_; lean_object* v_port_2429_; lean_object* v_pathSegments_2430_; lean_object* v_query_2431_; lean_object* v_fragment_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2447_; 
v_userInfo_2427_ = lean_ctor_get(v_b_2423_, 1);
v_host_2428_ = lean_ctor_get(v_b_2423_, 2);
v_port_2429_ = lean_ctor_get(v_b_2423_, 3);
v_pathSegments_2430_ = lean_ctor_get(v_b_2423_, 4);
v_query_2431_ = lean_ctor_get(v_b_2423_, 5);
v_fragment_2432_ = lean_ctor_get(v_b_2423_, 6);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_b_2423_);
if (v_isSharedCheck_2447_ == 0)
{
lean_object* v_unused_2448_; 
v_unused_2448_ = lean_ctor_get(v_b_2423_, 0);
lean_dec(v_unused_2448_);
v___x_2434_ = v_b_2423_;
v_isShared_2435_ = v_isSharedCheck_2447_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_fragment_2432_);
lean_inc(v_query_2431_);
lean_inc(v_pathSegments_2430_);
lean_inc(v_port_2429_);
lean_inc(v_host_2428_);
lean_inc(v_userInfo_2427_);
lean_dec(v_b_2423_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2447_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
lean_inc_ref(v___x_2425_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v___x_2425_);
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_userInfo_2427_);
lean_ctor_set(v_reuseFailAlloc_2446_, 2, v_host_2428_);
lean_ctor_set(v_reuseFailAlloc_2446_, 3, v_port_2429_);
lean_ctor_set(v_reuseFailAlloc_2446_, 4, v_pathSegments_2430_);
lean_ctor_set(v_reuseFailAlloc_2446_, 5, v_query_2431_);
lean_ctor_set(v_reuseFailAlloc_2446_, 6, v_fragment_2432_);
v___x_2437_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2444_ == 0)
{
lean_object* v_unused_2445_; 
v_unused_2445_ = lean_ctor_get(v___x_2425_, 0);
lean_dec(v_unused_2445_);
v___x_2439_ = v___x_2425_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_dec(v___x_2425_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2437_);
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(lean_object* v_msg_2449_){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = ((lean_object*)(l_Std_Http_URI_instInhabitedBuilder_default));
v___x_2451_ = lean_panic_fn_borrowed(v___x_2450_, v_msg_2449_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x21(lean_object* v_b_2453_, lean_object* v_scheme_2454_){
_start:
{
lean_object* v___x_2455_; 
lean_inc_ref(v_scheme_2454_);
v___x_2455_ = l_Std_Http_URI_Builder_setScheme_x3f(v_b_2453_, v_scheme_2454_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2456_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2457_ = ((lean_object*)(l_Std_Http_URI_Builder_setScheme_x21___closed__0));
v___x_2458_ = lean_unsigned_to_nat(687u);
v___x_2459_ = lean_unsigned_to_nat(14u);
v___x_2460_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_2461_ = l_String_quote(v_scheme_2454_);
v___x_2462_ = lean_string_append(v___x_2460_, v___x_2461_);
lean_dec_ref(v___x_2461_);
v___x_2463_ = l_mkPanicMessageWithDecl(v___x_2456_, v___x_2457_, v___x_2458_, v___x_2459_, v___x_2462_);
lean_dec_ref(v___x_2462_);
v___x_2464_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2463_);
return v___x_2464_;
}
else
{
lean_object* v_val_2465_; 
lean_dec_ref(v_scheme_2454_);
v_val_2465_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_val_2465_);
lean_dec_ref_known(v___x_2455_, 1);
return v_val_2465_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo(lean_object* v_b_2466_, lean_object* v_username_2467_, lean_object* v_password_2468_){
_start:
{
lean_object* v_scheme_2469_; lean_object* v_host_2470_; lean_object* v_port_2471_; lean_object* v_pathSegments_2472_; lean_object* v_query_2473_; lean_object* v_fragment_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2497_; 
v_scheme_2469_ = lean_ctor_get(v_b_2466_, 0);
v_host_2470_ = lean_ctor_get(v_b_2466_, 2);
v_port_2471_ = lean_ctor_get(v_b_2466_, 3);
v_pathSegments_2472_ = lean_ctor_get(v_b_2466_, 4);
v_query_2473_ = lean_ctor_get(v_b_2466_, 5);
v_fragment_2474_ = lean_ctor_get(v_b_2466_, 6);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_b_2466_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; 
v_unused_2498_ = lean_ctor_get(v_b_2466_, 1);
lean_dec(v_unused_2498_);
v___x_2476_ = v_b_2466_;
v_isShared_2477_ = v_isSharedCheck_2497_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_fragment_2474_);
lean_inc(v_query_2473_);
lean_inc(v_pathSegments_2472_);
lean_inc(v_port_2471_);
lean_inc(v_host_2470_);
lean_inc(v_scheme_2469_);
lean_dec(v_b_2466_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2497_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___y_2479_; lean_object* v___x_2484_; 
v___x_2484_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_2467_);
if (lean_obj_tag(v_password_2468_) == 0)
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = lean_box(0);
v___x_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___y_2479_ = v___x_2486_;
goto v___jp_2478_;
}
else
{
lean_object* v_val_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2496_; 
v_val_2487_ = lean_ctor_get(v_password_2468_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_password_2468_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2489_ = v_password_2468_;
v_isShared_2490_ = v_isSharedCheck_2496_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_val_2487_);
lean_dec(v_password_2468_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2496_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2491_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_2487_);
lean_dec(v_val_2487_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v___x_2491_);
v___x_2493_ = v___x_2489_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; 
v___x_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2484_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
v___y_2479_ = v___x_2494_;
goto v___jp_2478_;
}
}
}
v___jp_2478_:
{
lean_object* v___x_2480_; lean_object* v___x_2482_; 
v___x_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___y_2479_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 1, v___x_2480_);
v___x_2482_ = v___x_2476_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_scheme_2469_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_host_2470_);
lean_ctor_set(v_reuseFailAlloc_2483_, 3, v_port_2471_);
lean_ctor_set(v_reuseFailAlloc_2483_, 4, v_pathSegments_2472_);
lean_ctor_set(v_reuseFailAlloc_2483_, 5, v_query_2473_);
lean_ctor_set(v_reuseFailAlloc_2483_, 6, v_fragment_2474_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo___boxed(lean_object* v_b_2499_, lean_object* v_username_2500_, lean_object* v_password_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Std_Http_URI_Builder_setUserInfo(v_b_2499_, v_username_2500_, v_password_2501_);
lean_dec_ref(v_username_2500_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x3f(lean_object* v_b_2503_, lean_object* v_name_2504_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Std_Http_URI_DomainName_ofString_x3f(v_name_2504_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v___x_2506_; 
lean_dec_ref(v_b_2503_);
v___x_2506_ = lean_box(0);
return v___x_2506_;
}
else
{
lean_object* v_val_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2530_; 
v_val_2507_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2509_ = v___x_2505_;
v_isShared_2510_ = v_isSharedCheck_2530_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_val_2507_);
lean_dec(v___x_2505_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2530_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v_scheme_2511_; lean_object* v_userInfo_2512_; lean_object* v_port_2513_; lean_object* v_pathSegments_2514_; lean_object* v_query_2515_; lean_object* v_fragment_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2528_; 
v_scheme_2511_ = lean_ctor_get(v_b_2503_, 0);
v_userInfo_2512_ = lean_ctor_get(v_b_2503_, 1);
v_port_2513_ = lean_ctor_get(v_b_2503_, 3);
v_pathSegments_2514_ = lean_ctor_get(v_b_2503_, 4);
v_query_2515_ = lean_ctor_get(v_b_2503_, 5);
v_fragment_2516_ = lean_ctor_get(v_b_2503_, 6);
v_isSharedCheck_2528_ = !lean_is_exclusive(v_b_2503_);
if (v_isSharedCheck_2528_ == 0)
{
lean_object* v_unused_2529_; 
v_unused_2529_ = lean_ctor_get(v_b_2503_, 2);
lean_dec(v_unused_2529_);
v___x_2518_ = v_b_2503_;
v_isShared_2519_ = v_isSharedCheck_2528_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_fragment_2516_);
lean_inc(v_query_2515_);
lean_inc(v_pathSegments_2514_);
lean_inc(v_port_2513_);
lean_inc(v_userInfo_2512_);
lean_inc(v_scheme_2511_);
lean_dec(v_b_2503_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2528_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; lean_object* v___x_2522_; 
v___x_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2520_, 0, v_val_2507_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v___x_2520_);
v___x_2522_ = v___x_2509_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2520_);
v___x_2522_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2524_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 2, v___x_2522_);
v___x_2524_ = v___x_2518_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_scheme_2511_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v_userInfo_2512_);
lean_ctor_set(v_reuseFailAlloc_2526_, 2, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2526_, 3, v_port_2513_);
lean_ctor_set(v_reuseFailAlloc_2526_, 4, v_pathSegments_2514_);
lean_ctor_set(v_reuseFailAlloc_2526_, 5, v_query_2515_);
lean_ctor_set(v_reuseFailAlloc_2526_, 6, v_fragment_2516_);
v___x_2524_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2525_; 
v___x_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
return v___x_2525_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x21(lean_object* v_b_2533_, lean_object* v_name_2534_){
_start:
{
lean_object* v___x_2535_; 
lean_inc_ref(v_name_2534_);
v___x_2535_ = l_Std_Http_URI_Builder_setHost_x3f(v_b_2533_, v_name_2534_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2536_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2537_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__0));
v___x_2538_ = lean_unsigned_to_nat(716u);
v___x_2539_ = lean_unsigned_to_nat(14u);
v___x_2540_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__1));
v___x_2541_ = l_String_quote(v_name_2534_);
v___x_2542_ = lean_string_append(v___x_2540_, v___x_2541_);
lean_dec_ref(v___x_2541_);
v___x_2543_ = l_mkPanicMessageWithDecl(v___x_2536_, v___x_2537_, v___x_2538_, v___x_2539_, v___x_2542_);
lean_dec_ref(v___x_2542_);
v___x_2544_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2543_);
return v___x_2544_;
}
else
{
lean_object* v_val_2545_; 
lean_dec_ref(v_name_2534_);
v_val_2545_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_val_2545_);
lean_dec_ref_known(v___x_2535_, 1);
return v_val_2545_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv4(lean_object* v_b_2546_, lean_object* v_addr_2547_){
_start:
{
lean_object* v_scheme_2548_; lean_object* v_userInfo_2549_; lean_object* v_port_2550_; lean_object* v_pathSegments_2551_; lean_object* v_query_2552_; lean_object* v_fragment_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2562_; 
v_scheme_2548_ = lean_ctor_get(v_b_2546_, 0);
v_userInfo_2549_ = lean_ctor_get(v_b_2546_, 1);
v_port_2550_ = lean_ctor_get(v_b_2546_, 3);
v_pathSegments_2551_ = lean_ctor_get(v_b_2546_, 4);
v_query_2552_ = lean_ctor_get(v_b_2546_, 5);
v_fragment_2553_ = lean_ctor_get(v_b_2546_, 6);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_b_2546_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v_b_2546_, 2);
lean_dec(v_unused_2563_);
v___x_2555_ = v_b_2546_;
v_isShared_2556_ = v_isSharedCheck_2562_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_fragment_2553_);
lean_inc(v_query_2552_);
lean_inc(v_pathSegments_2551_);
lean_inc(v_port_2550_);
lean_inc(v_userInfo_2549_);
lean_inc(v_scheme_2548_);
lean_dec(v_b_2546_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2562_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2560_; 
v___x_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2557_, 0, v_addr_2547_);
v___x_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 2, v___x_2558_);
v___x_2560_ = v___x_2555_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_scheme_2548_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_userInfo_2549_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2561_, 3, v_port_2550_);
lean_ctor_set(v_reuseFailAlloc_2561_, 4, v_pathSegments_2551_);
lean_ctor_set(v_reuseFailAlloc_2561_, 5, v_query_2552_);
lean_ctor_set(v_reuseFailAlloc_2561_, 6, v_fragment_2553_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv6(lean_object* v_b_2564_, lean_object* v_addr_2565_){
_start:
{
lean_object* v_scheme_2566_; lean_object* v_userInfo_2567_; lean_object* v_port_2568_; lean_object* v_pathSegments_2569_; lean_object* v_query_2570_; lean_object* v_fragment_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2580_; 
v_scheme_2566_ = lean_ctor_get(v_b_2564_, 0);
v_userInfo_2567_ = lean_ctor_get(v_b_2564_, 1);
v_port_2568_ = lean_ctor_get(v_b_2564_, 3);
v_pathSegments_2569_ = lean_ctor_get(v_b_2564_, 4);
v_query_2570_ = lean_ctor_get(v_b_2564_, 5);
v_fragment_2571_ = lean_ctor_get(v_b_2564_, 6);
v_isSharedCheck_2580_ = !lean_is_exclusive(v_b_2564_);
if (v_isSharedCheck_2580_ == 0)
{
lean_object* v_unused_2581_; 
v_unused_2581_ = lean_ctor_get(v_b_2564_, 2);
lean_dec(v_unused_2581_);
v___x_2573_ = v_b_2564_;
v_isShared_2574_ = v_isSharedCheck_2580_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_fragment_2571_);
lean_inc(v_query_2570_);
lean_inc(v_pathSegments_2569_);
lean_inc(v_port_2568_);
lean_inc(v_userInfo_2567_);
lean_inc(v_scheme_2566_);
lean_dec(v_b_2564_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2580_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2575_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2575_, 0, v_addr_2565_);
v___x_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 2, v___x_2576_);
v___x_2578_ = v___x_2573_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_scheme_2566_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_userInfo_2567_);
lean_ctor_set(v_reuseFailAlloc_2579_, 2, v___x_2576_);
lean_ctor_set(v_reuseFailAlloc_2579_, 3, v_port_2568_);
lean_ctor_set(v_reuseFailAlloc_2579_, 4, v_pathSegments_2569_);
lean_ctor_set(v_reuseFailAlloc_2579_, 5, v_query_2570_);
lean_ctor_set(v_reuseFailAlloc_2579_, 6, v_fragment_2571_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort(lean_object* v_b_2582_, uint16_t v_port_2583_){
_start:
{
lean_object* v_scheme_2584_; lean_object* v_userInfo_2585_; lean_object* v_host_2586_; lean_object* v_pathSegments_2587_; lean_object* v_query_2588_; lean_object* v_fragment_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2597_; 
v_scheme_2584_ = lean_ctor_get(v_b_2582_, 0);
v_userInfo_2585_ = lean_ctor_get(v_b_2582_, 1);
v_host_2586_ = lean_ctor_get(v_b_2582_, 2);
v_pathSegments_2587_ = lean_ctor_get(v_b_2582_, 4);
v_query_2588_ = lean_ctor_get(v_b_2582_, 5);
v_fragment_2589_ = lean_ctor_get(v_b_2582_, 6);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_b_2582_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; 
v_unused_2598_ = lean_ctor_get(v_b_2582_, 3);
lean_dec(v_unused_2598_);
v___x_2591_ = v_b_2582_;
v_isShared_2592_ = v_isSharedCheck_2597_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_fragment_2589_);
lean_inc(v_query_2588_);
lean_inc(v_pathSegments_2587_);
lean_inc(v_host_2586_);
lean_inc(v_userInfo_2585_);
lean_inc(v_scheme_2584_);
lean_dec(v_b_2582_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2597_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
v___x_2593_ = lean_alloc_ctor(2, 0, 2);
lean_ctor_set_uint16(v___x_2593_, 0, v_port_2583_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 3, v___x_2593_);
v___x_2595_ = v___x_2591_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_scheme_2584_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_userInfo_2585_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_host_2586_);
lean_ctor_set(v_reuseFailAlloc_2596_, 3, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2596_, 4, v_pathSegments_2587_);
lean_ctor_set(v_reuseFailAlloc_2596_, 5, v_query_2588_);
lean_ctor_set(v_reuseFailAlloc_2596_, 6, v_fragment_2589_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort___boxed(lean_object* v_b_2599_, lean_object* v_port_2600_){
_start:
{
uint16_t v_port_boxed_2601_; lean_object* v_res_2602_; 
v_port_boxed_2601_ = lean_unbox(v_port_2600_);
v_res_2602_ = l_Std_Http_URI_Builder_setPort(v_b_2599_, v_port_boxed_2601_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPath(lean_object* v_b_2603_, lean_object* v_segments_2604_){
_start:
{
lean_object* v_scheme_2605_; lean_object* v_userInfo_2606_; lean_object* v_host_2607_; lean_object* v_port_2608_; lean_object* v_query_2609_; lean_object* v_fragment_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
v_scheme_2605_ = lean_ctor_get(v_b_2603_, 0);
v_userInfo_2606_ = lean_ctor_get(v_b_2603_, 1);
v_host_2607_ = lean_ctor_get(v_b_2603_, 2);
v_port_2608_ = lean_ctor_get(v_b_2603_, 3);
v_query_2609_ = lean_ctor_get(v_b_2603_, 5);
v_fragment_2610_ = lean_ctor_get(v_b_2603_, 6);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_b_2603_);
if (v_isSharedCheck_2617_ == 0)
{
lean_object* v_unused_2618_; 
v_unused_2618_ = lean_ctor_get(v_b_2603_, 4);
lean_dec(v_unused_2618_);
v___x_2612_ = v_b_2603_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_fragment_2610_);
lean_inc(v_query_2609_);
lean_inc(v_port_2608_);
lean_inc(v_host_2607_);
lean_inc(v_userInfo_2606_);
lean_inc(v_scheme_2605_);
lean_dec(v_b_2603_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 4, v_segments_2604_);
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_scheme_2605_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_userInfo_2606_);
lean_ctor_set(v_reuseFailAlloc_2616_, 2, v_host_2607_);
lean_ctor_set(v_reuseFailAlloc_2616_, 3, v_port_2608_);
lean_ctor_set(v_reuseFailAlloc_2616_, 4, v_segments_2604_);
lean_ctor_set(v_reuseFailAlloc_2616_, 5, v_query_2609_);
lean_ctor_set(v_reuseFailAlloc_2616_, 6, v_fragment_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_appendPathSegment(lean_object* v_b_2619_, lean_object* v_segment_2620_){
_start:
{
lean_object* v_scheme_2621_; lean_object* v_userInfo_2622_; lean_object* v_host_2623_; lean_object* v_port_2624_; lean_object* v_pathSegments_2625_; lean_object* v_query_2626_; lean_object* v_fragment_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2635_; 
v_scheme_2621_ = lean_ctor_get(v_b_2619_, 0);
v_userInfo_2622_ = lean_ctor_get(v_b_2619_, 1);
v_host_2623_ = lean_ctor_get(v_b_2619_, 2);
v_port_2624_ = lean_ctor_get(v_b_2619_, 3);
v_pathSegments_2625_ = lean_ctor_get(v_b_2619_, 4);
v_query_2626_ = lean_ctor_get(v_b_2619_, 5);
v_fragment_2627_ = lean_ctor_get(v_b_2619_, 6);
v_isSharedCheck_2635_ = !lean_is_exclusive(v_b_2619_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2629_ = v_b_2619_;
v_isShared_2630_ = v_isSharedCheck_2635_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_fragment_2627_);
lean_inc(v_query_2626_);
lean_inc(v_pathSegments_2625_);
lean_inc(v_port_2624_);
lean_inc(v_host_2623_);
lean_inc(v_userInfo_2622_);
lean_inc(v_scheme_2621_);
lean_dec(v_b_2619_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2635_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2631_ = lean_array_push(v_pathSegments_2625_, v_segment_2620_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 4, v___x_2631_);
v___x_2633_ = v___x_2629_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_scheme_2621_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v_userInfo_2622_);
lean_ctor_set(v_reuseFailAlloc_2634_, 2, v_host_2623_);
lean_ctor_set(v_reuseFailAlloc_2634_, 3, v_port_2624_);
lean_ctor_set(v_reuseFailAlloc_2634_, 4, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2634_, 5, v_query_2626_);
lean_ctor_set(v_reuseFailAlloc_2634_, 6, v_fragment_2627_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryParam(lean_object* v_b_2636_, lean_object* v_key_2637_, lean_object* v_value_2638_){
_start:
{
lean_object* v_scheme_2639_; lean_object* v_userInfo_2640_; lean_object* v_host_2641_; lean_object* v_port_2642_; lean_object* v_pathSegments_2643_; lean_object* v_query_2644_; lean_object* v_fragment_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2655_; 
v_scheme_2639_ = lean_ctor_get(v_b_2636_, 0);
v_userInfo_2640_ = lean_ctor_get(v_b_2636_, 1);
v_host_2641_ = lean_ctor_get(v_b_2636_, 2);
v_port_2642_ = lean_ctor_get(v_b_2636_, 3);
v_pathSegments_2643_ = lean_ctor_get(v_b_2636_, 4);
v_query_2644_ = lean_ctor_get(v_b_2636_, 5);
v_fragment_2645_ = lean_ctor_get(v_b_2636_, 6);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_b_2636_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2647_ = v_b_2636_;
v_isShared_2648_ = v_isSharedCheck_2655_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_fragment_2645_);
lean_inc(v_query_2644_);
lean_inc(v_pathSegments_2643_);
lean_inc(v_port_2642_);
lean_inc(v_host_2641_);
lean_inc(v_userInfo_2640_);
lean_inc(v_scheme_2639_);
lean_dec(v_b_2636_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2655_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2649_, 0, v_value_2638_);
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v_key_2637_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
v___x_2651_ = lean_array_push(v_query_2644_, v___x_2650_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 5, v___x_2651_);
v___x_2653_ = v___x_2647_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_scheme_2639_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_userInfo_2640_);
lean_ctor_set(v_reuseFailAlloc_2654_, 2, v_host_2641_);
lean_ctor_set(v_reuseFailAlloc_2654_, 3, v_port_2642_);
lean_ctor_set(v_reuseFailAlloc_2654_, 4, v_pathSegments_2643_);
lean_ctor_set(v_reuseFailAlloc_2654_, 5, v___x_2651_);
lean_ctor_set(v_reuseFailAlloc_2654_, 6, v_fragment_2645_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryFlag(lean_object* v_b_2656_, lean_object* v_key_2657_){
_start:
{
lean_object* v_scheme_2658_; lean_object* v_userInfo_2659_; lean_object* v_host_2660_; lean_object* v_port_2661_; lean_object* v_pathSegments_2662_; lean_object* v_query_2663_; lean_object* v_fragment_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2674_; 
v_scheme_2658_ = lean_ctor_get(v_b_2656_, 0);
v_userInfo_2659_ = lean_ctor_get(v_b_2656_, 1);
v_host_2660_ = lean_ctor_get(v_b_2656_, 2);
v_port_2661_ = lean_ctor_get(v_b_2656_, 3);
v_pathSegments_2662_ = lean_ctor_get(v_b_2656_, 4);
v_query_2663_ = lean_ctor_get(v_b_2656_, 5);
v_fragment_2664_ = lean_ctor_get(v_b_2656_, 6);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_b_2656_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2666_ = v_b_2656_;
v_isShared_2667_ = v_isSharedCheck_2674_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_fragment_2664_);
lean_inc(v_query_2663_);
lean_inc(v_pathSegments_2662_);
lean_inc(v_port_2661_);
lean_inc(v_host_2660_);
lean_inc(v_userInfo_2659_);
lean_inc(v_scheme_2658_);
lean_dec(v_b_2656_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2674_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2668_ = lean_box(0);
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v_key_2657_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = lean_array_push(v_query_2663_, v___x_2669_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 5, v___x_2670_);
v___x_2672_ = v___x_2666_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_scheme_2658_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_userInfo_2659_);
lean_ctor_set(v_reuseFailAlloc_2673_, 2, v_host_2660_);
lean_ctor_set(v_reuseFailAlloc_2673_, 3, v_port_2661_);
lean_ctor_set(v_reuseFailAlloc_2673_, 4, v_pathSegments_2662_);
lean_ctor_set(v_reuseFailAlloc_2673_, 5, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2673_, 6, v_fragment_2664_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setQuery(lean_object* v_b_2675_, lean_object* v_query_2676_){
_start:
{
lean_object* v_scheme_2677_; lean_object* v_userInfo_2678_; lean_object* v_host_2679_; lean_object* v_port_2680_; lean_object* v_pathSegments_2681_; lean_object* v_fragment_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
v_scheme_2677_ = lean_ctor_get(v_b_2675_, 0);
v_userInfo_2678_ = lean_ctor_get(v_b_2675_, 1);
v_host_2679_ = lean_ctor_get(v_b_2675_, 2);
v_port_2680_ = lean_ctor_get(v_b_2675_, 3);
v_pathSegments_2681_ = lean_ctor_get(v_b_2675_, 4);
v_fragment_2682_ = lean_ctor_get(v_b_2675_, 6);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_b_2675_);
if (v_isSharedCheck_2689_ == 0)
{
lean_object* v_unused_2690_; 
v_unused_2690_ = lean_ctor_get(v_b_2675_, 5);
lean_dec(v_unused_2690_);
v___x_2684_ = v_b_2675_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_fragment_2682_);
lean_inc(v_pathSegments_2681_);
lean_inc(v_port_2680_);
lean_inc(v_host_2679_);
lean_inc(v_userInfo_2678_);
lean_inc(v_scheme_2677_);
lean_dec(v_b_2675_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
lean_ctor_set(v___x_2684_, 5, v_query_2676_);
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_scheme_2677_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_userInfo_2678_);
lean_ctor_set(v_reuseFailAlloc_2688_, 2, v_host_2679_);
lean_ctor_set(v_reuseFailAlloc_2688_, 3, v_port_2680_);
lean_ctor_set(v_reuseFailAlloc_2688_, 4, v_pathSegments_2681_);
lean_ctor_set(v_reuseFailAlloc_2688_, 5, v_query_2676_);
lean_ctor_set(v_reuseFailAlloc_2688_, 6, v_fragment_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setFragment(lean_object* v_b_2691_, lean_object* v_fragment_2692_){
_start:
{
lean_object* v_scheme_2693_; lean_object* v_userInfo_2694_; lean_object* v_host_2695_; lean_object* v_port_2696_; lean_object* v_pathSegments_2697_; lean_object* v_query_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2706_; 
v_scheme_2693_ = lean_ctor_get(v_b_2691_, 0);
v_userInfo_2694_ = lean_ctor_get(v_b_2691_, 1);
v_host_2695_ = lean_ctor_get(v_b_2691_, 2);
v_port_2696_ = lean_ctor_get(v_b_2691_, 3);
v_pathSegments_2697_ = lean_ctor_get(v_b_2691_, 4);
v_query_2698_ = lean_ctor_get(v_b_2691_, 5);
v_isSharedCheck_2706_ = !lean_is_exclusive(v_b_2691_);
if (v_isSharedCheck_2706_ == 0)
{
lean_object* v_unused_2707_; 
v_unused_2707_ = lean_ctor_get(v_b_2691_, 6);
lean_dec(v_unused_2707_);
v___x_2700_ = v_b_2691_;
v_isShared_2701_ = v_isSharedCheck_2706_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_query_2698_);
lean_inc(v_pathSegments_2697_);
lean_inc(v_port_2696_);
lean_inc(v_host_2695_);
lean_inc(v_userInfo_2694_);
lean_inc(v_scheme_2693_);
lean_dec(v_b_2691_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2706_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2702_, 0, v_fragment_2692_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 6, v___x_2702_);
v___x_2704_ = v___x_2700_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_scheme_2693_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v_userInfo_2694_);
lean_ctor_set(v_reuseFailAlloc_2705_, 2, v_host_2695_);
lean_ctor_set(v_reuseFailAlloc_2705_, 3, v_port_2696_);
lean_ctor_set(v_reuseFailAlloc_2705_, 4, v_pathSegments_2697_);
lean_ctor_set(v_reuseFailAlloc_2705_, 5, v_query_2698_);
lean_ctor_set(v_reuseFailAlloc_2705_, 6, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(size_t v_sz_2708_, size_t v_i_2709_, lean_object* v_bs_2710_){
_start:
{
uint8_t v___x_2711_; 
v___x_2711_ = lean_usize_dec_lt(v_i_2709_, v_sz_2708_);
if (v___x_2711_ == 0)
{
return v_bs_2710_;
}
else
{
lean_object* v_v_2712_; lean_object* v___x_2713_; lean_object* v_bs_x27_2714_; lean_object* v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; lean_object* v___x_2718_; 
v_v_2712_ = lean_array_uget(v_bs_2710_, v_i_2709_);
v___x_2713_ = lean_unsigned_to_nat(0u);
v_bs_x27_2714_ = lean_array_uset(v_bs_2710_, v_i_2709_, v___x_2713_);
v___x_2715_ = l_Std_Http_URI_EncodedSegment_encode(v_v_2712_);
lean_dec(v_v_2712_);
v___x_2716_ = ((size_t)1ULL);
v___x_2717_ = lean_usize_add(v_i_2709_, v___x_2716_);
v___x_2718_ = lean_array_uset(v_bs_x27_2714_, v_i_2709_, v___x_2715_);
v_i_2709_ = v___x_2717_;
v_bs_2710_ = v___x_2718_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0___boxed(lean_object* v_sz_2720_, lean_object* v_i_2721_, lean_object* v_bs_2722_){
_start:
{
size_t v_sz_boxed_2723_; size_t v_i_boxed_2724_; lean_object* v_res_2725_; 
v_sz_boxed_2723_ = lean_unbox_usize(v_sz_2720_);
lean_dec(v_sz_2720_);
v_i_boxed_2724_ = lean_unbox_usize(v_i_2721_);
lean_dec(v_i_2721_);
v_res_2725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_boxed_2723_, v_i_boxed_2724_, v_bs_2722_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(size_t v_sz_2726_, size_t v_i_2727_, lean_object* v_bs_2728_){
_start:
{
uint8_t v___x_2729_; 
v___x_2729_ = lean_usize_dec_lt(v_i_2727_, v_sz_2726_);
if (v___x_2729_ == 0)
{
return v_bs_2728_;
}
else
{
lean_object* v_v_2730_; lean_object* v_fst_2731_; lean_object* v_snd_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2761_; 
v_v_2730_ = lean_array_uget(v_bs_2728_, v_i_2727_);
v_fst_2731_ = lean_ctor_get(v_v_2730_, 0);
v_snd_2732_ = lean_ctor_get(v_v_2730_, 1);
v_isSharedCheck_2761_ = !lean_is_exclusive(v_v_2730_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2734_ = v_v_2730_;
v_isShared_2735_ = v_isSharedCheck_2761_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_snd_2732_);
lean_inc(v_fst_2731_);
lean_dec(v_v_2730_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2761_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; lean_object* v_bs_x27_2737_; lean_object* v___y_2739_; lean_object* v___x_2744_; 
v___x_2736_ = lean_unsigned_to_nat(0u);
v_bs_x27_2737_ = lean_array_uset(v_bs_2728_, v_i_2727_, v___x_2736_);
v___x_2744_ = l_Std_Http_URI_EncodedQueryParam_encode(v_fst_2731_);
lean_dec(v_fst_2731_);
if (lean_obj_tag(v_snd_2732_) == 0)
{
lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2745_ = lean_box(0);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v___x_2745_);
lean_ctor_set(v___x_2734_, 0, v___x_2744_);
v___x_2747_ = v___x_2734_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v___x_2745_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
v___y_2739_ = v___x_2747_;
goto v___jp_2738_;
}
}
else
{
lean_object* v_val_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2760_; 
v_val_2749_ = lean_ctor_get(v_snd_2732_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_snd_2732_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2751_ = v_snd_2732_;
v_isShared_2752_ = v_isSharedCheck_2760_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_val_2749_);
lean_dec(v_snd_2732_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2760_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2753_; lean_object* v___x_2755_; 
v___x_2753_ = l_Std_Http_URI_EncodedQueryParam_encode(v_val_2749_);
lean_dec(v_val_2749_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 0, v___x_2753_);
v___x_2755_ = v___x_2751_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2757_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v___x_2755_);
lean_ctor_set(v___x_2734_, 0, v___x_2744_);
v___x_2757_ = v___x_2734_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
v___y_2739_ = v___x_2757_;
goto v___jp_2738_;
}
}
}
}
v___jp_2738_:
{
size_t v___x_2740_; size_t v___x_2741_; lean_object* v___x_2742_; 
v___x_2740_ = ((size_t)1ULL);
v___x_2741_ = lean_usize_add(v_i_2727_, v___x_2740_);
v___x_2742_ = lean_array_uset(v_bs_x27_2737_, v_i_2727_, v___y_2739_);
v_i_2727_ = v___x_2741_;
v_bs_2728_ = v___x_2742_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1___boxed(lean_object* v_sz_2762_, lean_object* v_i_2763_, lean_object* v_bs_2764_){
_start:
{
size_t v_sz_boxed_2765_; size_t v_i_boxed_2766_; lean_object* v_res_2767_; 
v_sz_boxed_2765_ = lean_unbox_usize(v_sz_2762_);
lean_dec(v_sz_2762_);
v_i_boxed_2766_ = lean_unbox_usize(v_i_2763_);
lean_dec(v_i_2763_);
v_res_2767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_boxed_2765_, v_i_boxed_2766_, v_bs_2764_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_build(lean_object* v_b_2768_){
_start:
{
lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; uint8_t v___y_2774_; lean_object* v___y_2775_; lean_object* v_scheme_2791_; lean_object* v_userInfo_2792_; lean_object* v_host_2793_; lean_object* v_port_2794_; lean_object* v_pathSegments_2795_; lean_object* v_query_2796_; lean_object* v_fragment_2797_; lean_object* v___y_2799_; 
v_scheme_2791_ = lean_ctor_get(v_b_2768_, 0);
lean_inc(v_scheme_2791_);
v_userInfo_2792_ = lean_ctor_get(v_b_2768_, 1);
lean_inc(v_userInfo_2792_);
v_host_2793_ = lean_ctor_get(v_b_2768_, 2);
lean_inc(v_host_2793_);
v_port_2794_ = lean_ctor_get(v_b_2768_, 3);
lean_inc(v_port_2794_);
v_pathSegments_2795_ = lean_ctor_get(v_b_2768_, 4);
lean_inc_ref(v_pathSegments_2795_);
v_query_2796_ = lean_ctor_get(v_b_2768_, 5);
lean_inc_ref(v_query_2796_);
v_fragment_2797_ = lean_ctor_get(v_b_2768_, 6);
lean_inc(v_fragment_2797_);
lean_dec_ref(v_b_2768_);
if (lean_obj_tag(v_scheme_2791_) == 0)
{
lean_object* v___x_2812_; 
v___x_2812_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___y_2799_ = v___x_2812_;
goto v___jp_2798_;
}
else
{
lean_object* v_val_2813_; 
v_val_2813_ = lean_ctor_get(v_scheme_2791_, 0);
lean_inc(v_val_2813_);
lean_dec_ref_known(v_scheme_2791_, 1);
v___y_2799_ = v_val_2813_;
goto v___jp_2798_;
}
v___jp_2769_:
{
size_t v_sz_2776_; size_t v___x_2777_; lean_object* v___x_2778_; lean_object* v_path_2779_; size_t v_sz_2780_; lean_object* v_query_2781_; lean_object* v___x_2782_; lean_object* v_query_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; uint8_t v___x_2786_; 
v_sz_2776_ = lean_array_size(v___y_2771_);
v___x_2777_ = ((size_t)0ULL);
v___x_2778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_2776_, v___x_2777_, v___y_2771_);
v_path_2779_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_path_2779_, 0, v___x_2778_);
lean_ctor_set_uint8(v_path_2779_, sizeof(void*)*1, v___y_2774_);
v_sz_2780_ = lean_array_size(v___y_2772_);
v_query_2781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_2780_, v___x_2777_, v___y_2772_);
v___x_2782_ = lean_array_to_list(v_query_2781_);
v_query_2783_ = lean_array_mk(v___x_2782_);
v___x_2784_ = lean_array_get_size(v_query_2783_);
v___x_2785_ = lean_unsigned_to_nat(0u);
v___x_2786_ = lean_nat_dec_eq(v___x_2784_, v___x_2785_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2787_, 0, v_query_2783_);
v___x_2788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2788_, 0, v___y_2770_);
lean_ctor_set(v___x_2788_, 1, v___y_2775_);
lean_ctor_set(v___x_2788_, 2, v_path_2779_);
lean_ctor_set(v___x_2788_, 3, v___x_2787_);
lean_ctor_set(v___x_2788_, 4, v___y_2773_);
return v___x_2788_;
}
else
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
lean_dec_ref(v_query_2783_);
v___x_2789_ = lean_box(0);
v___x_2790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2790_, 0, v___y_2770_);
lean_ctor_set(v___x_2790_, 1, v___y_2775_);
lean_ctor_set(v___x_2790_, 2, v_path_2779_);
lean_ctor_set(v___x_2790_, 3, v___x_2789_);
lean_ctor_set(v___x_2790_, 4, v___y_2773_);
return v___x_2790_;
}
}
v___jp_2798_:
{
if (lean_obj_tag(v_host_2793_) == 0)
{
uint8_t v___x_2800_; lean_object* v___x_2801_; 
lean_dec(v_port_2794_);
lean_dec(v_userInfo_2792_);
v___x_2800_ = 1;
v___x_2801_ = lean_box(0);
v___y_2770_ = v___y_2799_;
v___y_2771_ = v_pathSegments_2795_;
v___y_2772_ = v_query_2796_;
v___y_2773_ = v_fragment_2797_;
v___y_2774_ = v___x_2800_;
v___y_2775_ = v___x_2801_;
goto v___jp_2769_;
}
else
{
lean_object* v_val_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2811_; 
v_val_2802_ = lean_ctor_get(v_host_2793_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v_host_2793_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2804_ = v_host_2793_;
v_isShared_2805_ = v_isSharedCheck_2811_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_val_2802_);
lean_dec(v_host_2793_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2811_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
uint8_t v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2809_; 
v___x_2806_ = 1;
v___x_2807_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2807_, 0, v_userInfo_2792_);
lean_ctor_set(v___x_2807_, 1, v_val_2802_);
lean_ctor_set(v___x_2807_, 2, v_port_2794_);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2807_);
v___x_2809_ = v___x_2804_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2807_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
v___y_2770_ = v___y_2799_;
v___y_2771_ = v_pathSegments_2795_;
v___y_2772_ = v_query_2796_;
v___y_2773_ = v_fragment_2797_;
v___y_2774_ = v___x_2806_;
v___y_2775_ = v___x_2809_;
goto v___jp_2769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withScheme_x21(lean_object* v_uri_2814_, lean_object* v_scheme_2815_){
_start:
{
lean_object* v_authority_2816_; lean_object* v_path_2817_; lean_object* v_query_2818_; lean_object* v_fragment_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2827_; 
v_authority_2816_ = lean_ctor_get(v_uri_2814_, 1);
v_path_2817_ = lean_ctor_get(v_uri_2814_, 2);
v_query_2818_ = lean_ctor_get(v_uri_2814_, 3);
v_fragment_2819_ = lean_ctor_get(v_uri_2814_, 4);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_uri_2814_);
if (v_isSharedCheck_2827_ == 0)
{
lean_object* v_unused_2828_; 
v_unused_2828_ = lean_ctor_get(v_uri_2814_, 0);
lean_dec(v_unused_2828_);
v___x_2821_ = v_uri_2814_;
v_isShared_2822_ = v_isSharedCheck_2827_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_fragment_2819_);
lean_inc(v_query_2818_);
lean_inc(v_path_2817_);
lean_inc(v_authority_2816_);
lean_dec(v_uri_2814_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2827_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; lean_object* v___x_2825_; 
v___x_2823_ = l_Std_Http_URI_Scheme_ofString_x21(v_scheme_2815_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v___x_2823_);
v___x_2825_ = v___x_2821_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_authority_2816_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_path_2817_);
lean_ctor_set(v_reuseFailAlloc_2826_, 3, v_query_2818_);
lean_ctor_set(v_reuseFailAlloc_2826_, 4, v_fragment_2819_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withAuthority(lean_object* v_uri_2829_, lean_object* v_authority_2830_){
_start:
{
lean_object* v_scheme_2831_; lean_object* v_path_2832_; lean_object* v_query_2833_; lean_object* v_fragment_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
v_scheme_2831_ = lean_ctor_get(v_uri_2829_, 0);
v_path_2832_ = lean_ctor_get(v_uri_2829_, 2);
v_query_2833_ = lean_ctor_get(v_uri_2829_, 3);
v_fragment_2834_ = lean_ctor_get(v_uri_2829_, 4);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_uri_2829_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; 
v_unused_2842_ = lean_ctor_get(v_uri_2829_, 1);
lean_dec(v_unused_2842_);
v___x_2836_ = v_uri_2829_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_fragment_2834_);
lean_inc(v_query_2833_);
lean_inc(v_path_2832_);
lean_inc(v_scheme_2831_);
lean_dec(v_uri_2829_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 1, v_authority_2830_);
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_scheme_2831_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_authority_2830_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_path_2832_);
lean_ctor_set(v_reuseFailAlloc_2840_, 3, v_query_2833_);
lean_ctor_set(v_reuseFailAlloc_2840_, 4, v_fragment_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withPath(lean_object* v_uri_2843_, lean_object* v_path_2844_){
_start:
{
lean_object* v_scheme_2845_; lean_object* v_authority_2846_; lean_object* v_query_2847_; lean_object* v_fragment_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
v_scheme_2845_ = lean_ctor_get(v_uri_2843_, 0);
v_authority_2846_ = lean_ctor_get(v_uri_2843_, 1);
v_query_2847_ = lean_ctor_get(v_uri_2843_, 3);
v_fragment_2848_ = lean_ctor_get(v_uri_2843_, 4);
v_isSharedCheck_2855_ = !lean_is_exclusive(v_uri_2843_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v_uri_2843_, 2);
lean_dec(v_unused_2856_);
v___x_2850_ = v_uri_2843_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_fragment_2848_);
lean_inc(v_query_2847_);
lean_inc(v_authority_2846_);
lean_inc(v_scheme_2845_);
lean_dec(v_uri_2843_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 2, v_path_2844_);
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_scheme_2845_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_authority_2846_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_path_2844_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_query_2847_);
lean_ctor_set(v_reuseFailAlloc_2854_, 4, v_fragment_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withQuery(lean_object* v_uri_2857_, lean_object* v_query_2858_){
_start:
{
lean_object* v_scheme_2859_; lean_object* v_authority_2860_; lean_object* v_path_2861_; lean_object* v_fragment_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2870_; 
v_scheme_2859_ = lean_ctor_get(v_uri_2857_, 0);
v_authority_2860_ = lean_ctor_get(v_uri_2857_, 1);
v_path_2861_ = lean_ctor_get(v_uri_2857_, 2);
v_fragment_2862_ = lean_ctor_get(v_uri_2857_, 4);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_uri_2857_);
if (v_isSharedCheck_2870_ == 0)
{
lean_object* v_unused_2871_; 
v_unused_2871_ = lean_ctor_get(v_uri_2857_, 3);
lean_dec(v_unused_2871_);
v___x_2864_ = v_uri_2857_;
v_isShared_2865_ = v_isSharedCheck_2870_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_fragment_2862_);
lean_inc(v_path_2861_);
lean_inc(v_authority_2860_);
lean_inc(v_scheme_2859_);
lean_dec(v_uri_2857_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2870_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2866_; lean_object* v___x_2868_; 
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v_query_2858_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 3, v___x_2866_);
v___x_2868_ = v___x_2864_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_scheme_2859_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_authority_2860_);
lean_ctor_set(v_reuseFailAlloc_2869_, 2, v_path_2861_);
lean_ctor_set(v_reuseFailAlloc_2869_, 3, v___x_2866_);
lean_ctor_set(v_reuseFailAlloc_2869_, 4, v_fragment_2862_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withFragment(lean_object* v_uri_2872_, lean_object* v_fragment_2873_){
_start:
{
lean_object* v_scheme_2874_; lean_object* v_authority_2875_; lean_object* v_path_2876_; lean_object* v_query_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
v_scheme_2874_ = lean_ctor_get(v_uri_2872_, 0);
v_authority_2875_ = lean_ctor_get(v_uri_2872_, 1);
v_path_2876_ = lean_ctor_get(v_uri_2872_, 2);
v_query_2877_ = lean_ctor_get(v_uri_2872_, 3);
v_isSharedCheck_2884_ = !lean_is_exclusive(v_uri_2872_);
if (v_isSharedCheck_2884_ == 0)
{
lean_object* v_unused_2885_; 
v_unused_2885_ = lean_ctor_get(v_uri_2872_, 4);
lean_dec(v_unused_2885_);
v___x_2879_ = v_uri_2872_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_query_2877_);
lean_inc(v_path_2876_);
lean_inc(v_authority_2875_);
lean_inc(v_scheme_2874_);
lean_dec(v_uri_2872_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 4, v_fragment_2873_);
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_scheme_2874_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v_authority_2875_);
lean_ctor_set(v_reuseFailAlloc_2883_, 2, v_path_2876_);
lean_ctor_set(v_reuseFailAlloc_2883_, 3, v_query_2877_);
lean_ctor_set(v_reuseFailAlloc_2883_, 4, v_fragment_2873_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_normalize(lean_object* v_uri_2886_){
_start:
{
lean_object* v_scheme_2887_; lean_object* v_authority_2888_; lean_object* v_path_2889_; lean_object* v_query_2890_; lean_object* v_fragment_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2899_; 
v_scheme_2887_ = lean_ctor_get(v_uri_2886_, 0);
v_authority_2888_ = lean_ctor_get(v_uri_2886_, 1);
v_path_2889_ = lean_ctor_get(v_uri_2886_, 2);
v_query_2890_ = lean_ctor_get(v_uri_2886_, 3);
v_fragment_2891_ = lean_ctor_get(v_uri_2886_, 4);
v_isSharedCheck_2899_ = !lean_is_exclusive(v_uri_2886_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2893_ = v_uri_2886_;
v_isShared_2894_ = v_isSharedCheck_2899_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_fragment_2891_);
lean_inc(v_query_2890_);
lean_inc(v_path_2889_);
lean_inc(v_authority_2888_);
lean_inc(v_scheme_2887_);
lean_dec(v_uri_2886_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2899_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2895_ = l_Std_Http_URI_Path_normalize(v_path_2889_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 2, v___x_2895_);
v___x_2897_ = v___x_2893_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_scheme_2887_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v_authority_2888_);
lean_ctor_set(v_reuseFailAlloc_2898_, 2, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_2898_, 3, v_query_2890_);
lean_ctor_set(v_reuseFailAlloc_2898_, 4, v_fragment_2891_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___redArg(lean_object* v_x_2900_){
_start:
{
lean_object* v_scheme_2901_; lean_object* v_host_2902_; uint16_t v_port_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v_ctr_2924_; lean_object* v_a_2925_; 
v_scheme_2901_ = lean_ctor_get(v_x_2900_, 0);
lean_inc_ref(v_scheme_2901_);
v_host_2902_ = lean_ctor_get(v_x_2900_, 1);
lean_inc_ref(v_host_2902_);
v_port_2903_ = lean_ctor_get_uint16(v_x_2900_, sizeof(void*)*2);
lean_dec_ref(v_x_2900_);
v___x_2904_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2905_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2906_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2907_ = l_String_quote(v_scheme_2901_);
v___x_2908_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
v___x_2909_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2906_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = 0;
v___x_2911_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2911_, 0, v___x_2909_);
lean_ctor_set_uint8(v___x_2911_, sizeof(void*)*1, v___x_2910_);
v___x_2912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2905_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2912_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
v___x_2915_ = lean_box(1);
v___x_2916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2914_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
v___x_2917_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_2918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2916_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
lean_ctor_set(v___x_2919_, 1, v___x_2904_);
v___x_2920_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2921_ = lean_unsigned_to_nat(0u);
v___x_2922_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_2902_))
{
case 0:
{
lean_object* v_name_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2964_; 
v_name_2955_ = lean_ctor_get(v_host_2902_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v_host_2902_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2957_ = v_host_2902_;
v_isShared_2958_ = v_isSharedCheck_2964_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_name_2955_);
lean_dec(v_host_2902_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2964_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2962_; 
v___x_2959_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_2960_ = l_String_quote(v_name_2955_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set_tag(v___x_2957_, 3);
lean_ctor_set(v___x_2957_, 0, v___x_2960_);
v___x_2962_ = v___x_2957_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2960_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
v_ctr_2924_ = v___x_2959_;
v_a_2925_ = v___x_2962_;
goto v___jp_2923_;
}
}
}
case 1:
{
lean_object* v_ipv4_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2974_; 
v_ipv4_2965_ = lean_ctor_get(v_host_2902_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v_host_2902_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2967_ = v_host_2902_;
v_isShared_2968_ = v_isSharedCheck_2974_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_ipv4_2965_);
lean_dec(v_host_2902_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2974_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2969_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_2970_ = lean_uv_ntop_v4(v_ipv4_2965_);
lean_dec_ref(v_ipv4_2965_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set_tag(v___x_2967_, 3);
lean_ctor_set(v___x_2967_, 0, v___x_2970_);
v___x_2972_ = v___x_2967_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
v_ctr_2924_ = v___x_2969_;
v_a_2925_ = v___x_2972_;
goto v___jp_2923_;
}
}
}
default: 
{
lean_object* v_ipv6_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2984_; 
v_ipv6_2975_ = lean_ctor_get(v_host_2902_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_host_2902_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2977_ = v_host_2902_;
v_isShared_2978_ = v_isSharedCheck_2984_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_ipv6_2975_);
lean_dec(v_host_2902_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2984_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2982_; 
v___x_2979_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_2980_ = lean_uv_ntop_v6(v_ipv6_2975_);
lean_dec_ref(v_ipv6_2975_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set_tag(v___x_2977_, 3);
lean_ctor_set(v___x_2977_, 0, v___x_2980_);
v___x_2982_ = v___x_2977_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
v_ctr_2924_ = v___x_2979_;
v_a_2925_ = v___x_2982_;
goto v___jp_2923_;
}
}
}
}
v___jp_2923_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2926_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_2927_ = lean_string_append(v___x_2926_, v_ctr_2924_);
v___x_2928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
v___x_2929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
lean_ctor_set(v___x_2929_, 1, v___x_2915_);
v___x_2930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
lean_ctor_set(v___x_2930_, 1, v_a_2925_);
v___x_2931_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2922_);
lean_ctor_set(v___x_2931_, 1, v___x_2930_);
v___x_2932_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*1, v___x_2910_);
v___x_2933_ = l_Repr_addAppParen(v___x_2932_, v___x_2921_);
v___x_2934_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2920_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
v___x_2935_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
lean_ctor_set_uint8(v___x_2935_, sizeof(void*)*1, v___x_2910_);
v___x_2936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2919_);
lean_ctor_set(v___x_2936_, 1, v___x_2935_);
v___x_2937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
lean_ctor_set(v___x_2937_, 1, v___x_2913_);
v___x_2938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v___x_2915_);
v___x_2939_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_2940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2938_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
lean_ctor_set(v___x_2941_, 1, v___x_2904_);
v___x_2942_ = lean_uint16_to_nat(v_port_2903_);
v___x_2943_ = l_Nat_reprFast(v___x_2942_);
v___x_2944_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
v___x_2945_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2920_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___x_2946_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
lean_ctor_set_uint8(v___x_2946_, sizeof(void*)*1, v___x_2910_);
v___x_2947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2941_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
v___x_2948_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2949_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
lean_ctor_set(v___x_2950_, 1, v___x_2947_);
v___x_2951_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2950_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
v___x_2953_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2948_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
lean_ctor_set_uint8(v___x_2954_, sizeof(void*)*1, v___x_2910_);
return v___x_2954_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr(lean_object* v_x_2985_, lean_object* v_prec_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_Std_Http_URI_instReprOrigin_repr___redArg(v_x_2985_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___boxed(lean_object* v_x_2988_, lean_object* v_prec_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Std_Http_URI_instReprOrigin_repr(v_x_2988_, v_prec_2989_);
lean_dec(v_prec_2989_);
return v_res_2990_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqOrigin_beq(lean_object* v_x_2993_, lean_object* v_x_2994_){
_start:
{
lean_object* v_scheme_2995_; lean_object* v_host_2996_; uint16_t v_port_2997_; lean_object* v_scheme_2998_; lean_object* v_host_2999_; uint16_t v_port_3000_; uint8_t v___x_3001_; 
v_scheme_2995_ = lean_ctor_get(v_x_2993_, 0);
v_host_2996_ = lean_ctor_get(v_x_2993_, 1);
v_port_2997_ = lean_ctor_get_uint16(v_x_2993_, sizeof(void*)*2);
v_scheme_2998_ = lean_ctor_get(v_x_2994_, 0);
v_host_2999_ = lean_ctor_get(v_x_2994_, 1);
v_port_3000_ = lean_ctor_get_uint16(v_x_2994_, sizeof(void*)*2);
v___x_3001_ = lean_string_dec_eq(v_scheme_2995_, v_scheme_2998_);
if (v___x_3001_ == 0)
{
return v___x_3001_;
}
else
{
uint8_t v___x_3002_; 
v___x_3002_ = l_Std_Http_URI_instBEqHost_beq(v_host_2996_, v_host_2999_);
if (v___x_3002_ == 0)
{
return v___x_3002_;
}
else
{
uint8_t v___x_3003_; 
v___x_3003_ = lean_uint16_dec_eq(v_port_2997_, v_port_3000_);
return v___x_3003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqOrigin_beq___boxed(lean_object* v_x_3004_, lean_object* v_x_3005_){
_start:
{
uint8_t v_res_3006_; lean_object* v_r_3007_; 
v_res_3006_ = l_Std_Http_URI_instBEqOrigin_beq(v_x_3004_, v_x_3005_);
lean_dec_ref(v_x_3005_);
lean_dec_ref(v_x_3004_);
v_r_3007_ = lean_box(v_res_3006_);
return v_r_3007_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Origin_hostHeader(lean_object* v_o_3010_){
_start:
{
lean_object* v_scheme_3011_; lean_object* v_host_3012_; uint16_t v_port_3013_; lean_object* v___y_3015_; uint16_t v_defaultPort_3021_; uint8_t v___x_3022_; 
v_scheme_3011_ = lean_ctor_get(v_o_3010_, 0);
lean_inc_ref(v_scheme_3011_);
v_host_3012_ = lean_ctor_get(v_o_3010_, 1);
lean_inc_ref(v_host_3012_);
v_port_3013_ = lean_ctor_get_uint16(v_o_3010_, sizeof(void*)*2);
lean_dec_ref(v_o_3010_);
v_defaultPort_3021_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_3011_);
lean_dec_ref(v_scheme_3011_);
v___x_3022_ = lean_uint16_dec_eq(v_port_3013_, v_defaultPort_3021_);
if (v___x_3022_ == 0)
{
switch(lean_obj_tag(v_host_3012_))
{
case 0:
{
lean_object* v_name_3023_; 
v_name_3023_ = lean_ctor_get(v_host_3012_, 0);
lean_inc_ref(v_name_3023_);
lean_dec_ref_known(v_host_3012_, 1);
v___y_3015_ = v_name_3023_;
goto v___jp_3014_;
}
case 1:
{
lean_object* v_ipv4_3024_; lean_object* v___x_3025_; 
v_ipv4_3024_ = lean_ctor_get(v_host_3012_, 0);
lean_inc_ref(v_ipv4_3024_);
lean_dec_ref_known(v_host_3012_, 1);
v___x_3025_ = lean_uv_ntop_v4(v_ipv4_3024_);
lean_dec_ref(v_ipv4_3024_);
v___y_3015_ = v___x_3025_;
goto v___jp_3014_;
}
default: 
{
lean_object* v_ipv6_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v_ipv6_3026_ = lean_ctor_get(v_host_3012_, 0);
lean_inc_ref(v_ipv6_3026_);
lean_dec_ref_known(v_host_3012_, 1);
v___x_3027_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3028_ = lean_uv_ntop_v6(v_ipv6_3026_);
lean_dec_ref(v_ipv6_3026_);
v___x_3029_ = lean_string_append(v___x_3027_, v___x_3028_);
lean_dec_ref(v___x_3028_);
v___x_3030_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3031_ = lean_string_append(v___x_3029_, v___x_3030_);
v___y_3015_ = v___x_3031_;
goto v___jp_3014_;
}
}
}
else
{
switch(lean_obj_tag(v_host_3012_))
{
case 0:
{
lean_object* v_name_3032_; 
v_name_3032_ = lean_ctor_get(v_host_3012_, 0);
lean_inc_ref(v_name_3032_);
lean_dec_ref_known(v_host_3012_, 1);
return v_name_3032_;
}
case 1:
{
lean_object* v_ipv4_3033_; lean_object* v___x_3034_; 
v_ipv4_3033_ = lean_ctor_get(v_host_3012_, 0);
lean_inc_ref(v_ipv4_3033_);
lean_dec_ref_known(v_host_3012_, 1);
v___x_3034_ = lean_uv_ntop_v4(v_ipv4_3033_);
lean_dec_ref(v_ipv4_3033_);
return v___x_3034_;
}
default: 
{
lean_object* v_ipv6_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v_ipv6_3035_ = lean_ctor_get(v_host_3012_, 0);
lean_inc_ref(v_ipv6_3035_);
lean_dec_ref_known(v_host_3012_, 1);
v___x_3036_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3037_ = lean_uv_ntop_v6(v_ipv6_3035_);
lean_dec_ref(v_ipv6_3035_);
v___x_3038_ = lean_string_append(v___x_3036_, v___x_3037_);
lean_dec_ref(v___x_3037_);
v___x_3039_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3040_ = lean_string_append(v___x_3038_, v___x_3039_);
return v___x_3040_;
}
}
}
v___jp_3014_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3016_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3017_ = lean_string_append(v___y_3015_, v___x_3016_);
v___x_3018_ = lean_uint16_to_nat(v_port_3013_);
v___x_3019_ = l_Nat_reprFast(v___x_3018_);
v___x_3020_ = lean_string_append(v___x_3017_, v___x_3019_);
lean_dec_ref(v___x_3019_);
return v___x_3020_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___redArg(lean_object* v_x_3047_){
_start:
{
lean_object* v_authority_3048_; lean_object* v_path_3049_; lean_object* v_query_3050_; lean_object* v_fragment_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v_authority_3048_ = lean_ctor_get(v_x_3047_, 0);
lean_inc(v_authority_3048_);
v_path_3049_ = lean_ctor_get(v_x_3047_, 1);
lean_inc_ref(v_path_3049_);
v_query_3050_ = lean_ctor_get(v_x_3047_, 2);
lean_inc(v_query_3050_);
v_fragment_3051_ = lean_ctor_get(v_x_3047_, 3);
lean_inc(v_fragment_3051_);
lean_dec_ref(v_x_3047_);
v___x_3052_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_3053_ = ((lean_object*)(l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__1));
v___x_3054_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_3055_ = lean_unsigned_to_nat(0u);
v___x_3056_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_3048_, v___x_3055_);
v___x_3057_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3054_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
v___x_3058_ = 0;
v___x_3059_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3059_, 0, v___x_3057_);
lean_ctor_set_uint8(v___x_3059_, sizeof(void*)*1, v___x_3058_);
v___x_3060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3053_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
v___x_3061_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_3062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3060_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = lean_box(1);
v___x_3064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3062_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
v___x_3065_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_3066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3064_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
lean_ctor_set(v___x_3067_, 1, v___x_3052_);
v___x_3068_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_3069_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3049_);
v___x_3070_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3068_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*1, v___x_3058_);
v___x_3072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3067_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v___x_3073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v___x_3061_);
v___x_3074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
lean_ctor_set(v___x_3074_, 1, v___x_3063_);
v___x_3075_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_3076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3074_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v___x_3077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3076_);
lean_ctor_set(v___x_3077_, 1, v___x_3052_);
v___x_3078_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_3079_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3050_, v___x_3055_);
v___x_3080_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3078_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
lean_ctor_set_uint8(v___x_3081_, sizeof(void*)*1, v___x_3058_);
v___x_3082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3077_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___x_3083_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
lean_ctor_set(v___x_3083_, 1, v___x_3061_);
v___x_3084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
lean_ctor_set(v___x_3084_, 1, v___x_3063_);
v___x_3085_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_3086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3084_);
lean_ctor_set(v___x_3086_, 1, v___x_3085_);
v___x_3087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
lean_ctor_set(v___x_3087_, 1, v___x_3052_);
v___x_3088_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_3089_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_3051_, v___x_3055_);
v___x_3090_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3088_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
v___x_3091_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
lean_ctor_set_uint8(v___x_3091_, sizeof(void*)*1, v___x_3058_);
v___x_3092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3087_);
lean_ctor_set(v___x_3092_, 1, v___x_3091_);
v___x_3093_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_3094_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_3095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
lean_ctor_set(v___x_3095_, 1, v___x_3092_);
v___x_3096_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_3097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3095_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
v___x_3098_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3093_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
lean_ctor_set_uint8(v___x_3099_, sizeof(void*)*1, v___x_3058_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr(lean_object* v_x_3100_, lean_object* v_prec_3101_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_x_3100_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___boxed(lean_object* v_x_3103_, lean_object* v_prec_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Std_Http_URI_instReprRelativeRef_repr(v_x_3103_, v_prec_3104_);
lean_dec(v_prec_3104_);
return v_res_3105_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqRelativeRef_beq(lean_object* v_x_3113_, lean_object* v_x_3114_){
_start:
{
lean_object* v_authority_3115_; lean_object* v_path_3116_; lean_object* v_query_3117_; lean_object* v_fragment_3118_; lean_object* v_authority_3119_; lean_object* v_path_3120_; lean_object* v_query_3121_; lean_object* v_fragment_3122_; uint8_t v___x_3123_; 
v_authority_3115_ = lean_ctor_get(v_x_3113_, 0);
v_path_3116_ = lean_ctor_get(v_x_3113_, 1);
v_query_3117_ = lean_ctor_get(v_x_3113_, 2);
v_fragment_3118_ = lean_ctor_get(v_x_3113_, 3);
v_authority_3119_ = lean_ctor_get(v_x_3114_, 0);
v_path_3120_ = lean_ctor_get(v_x_3114_, 1);
v_query_3121_ = lean_ctor_get(v_x_3114_, 2);
v_fragment_3122_ = lean_ctor_get(v_x_3114_, 3);
v___x_3123_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_3115_, v_authority_3119_);
if (v___x_3123_ == 0)
{
return v___x_3123_;
}
else
{
uint8_t v___x_3124_; 
v___x_3124_ = l_Std_Http_URI_instBEqPath_beq(v_path_3116_, v_path_3120_);
if (v___x_3124_ == 0)
{
return v___x_3124_;
}
else
{
uint8_t v___x_3125_; 
v___x_3125_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_3117_, v_query_3121_);
if (v___x_3125_ == 0)
{
return v___x_3125_;
}
else
{
uint8_t v___x_3126_; 
v___x_3126_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_3118_, v_fragment_3122_);
return v___x_3126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqRelativeRef_beq___boxed(lean_object* v_x_3127_, lean_object* v_x_3128_){
_start:
{
uint8_t v_res_3129_; lean_object* v_r_3130_; 
v_res_3129_ = l_Std_Http_URI_instBEqRelativeRef_beq(v_x_3127_, v_x_3128_);
lean_dec_ref(v_x_3128_);
lean_dec_ref(v_x_3127_);
v_r_3130_ = lean_box(v_res_3129_);
return v_r_3130_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringRelativeRef___lam__1(lean_object* v___f_3133_, lean_object* v_ref_3134_){
_start:
{
lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v_authority_3143_; lean_object* v_path_3144_; lean_object* v_query_3145_; lean_object* v_fragment_3146_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3158_; 
v_authority_3143_ = lean_ctor_get(v_ref_3134_, 0);
lean_inc(v_authority_3143_);
v_path_3144_ = lean_ctor_get(v_ref_3134_, 1);
lean_inc_ref(v_path_3144_);
v_query_3145_ = lean_ctor_get(v_ref_3134_, 2);
lean_inc(v_query_3145_);
v_fragment_3146_ = lean_ctor_get(v_ref_3134_, 3);
lean_inc(v_fragment_3146_);
lean_dec_ref(v_ref_3134_);
if (lean_obj_tag(v_authority_3143_) == 0)
{
lean_object* v___x_3169_; 
v___x_3169_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3158_ = v___x_3169_;
goto v___jp_3157_;
}
else
{
lean_object* v_val_3170_; lean_object* v_userInfo_3171_; lean_object* v_host_3172_; lean_object* v_port_3173_; lean_object* v___x_3174_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3193_; 
v_val_3170_ = lean_ctor_get(v_authority_3143_, 0);
lean_inc(v_val_3170_);
lean_dec_ref_known(v_authority_3143_, 1);
v_userInfo_3171_ = lean_ctor_get(v_val_3170_, 0);
lean_inc(v_userInfo_3171_);
v_host_3172_ = lean_ctor_get(v_val_3170_, 1);
lean_inc_ref(v_host_3172_);
v_port_3173_ = lean_ctor_get(v_val_3170_, 2);
lean_inc(v_port_3173_);
lean_dec(v_val_3170_);
v___x_3174_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3171_) == 0)
{
lean_object* v___x_3203_; 
v___x_3203_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3193_ = v___x_3203_;
goto v___jp_3192_;
}
else
{
lean_object* v_val_3204_; lean_object* v_password_3205_; 
v_val_3204_ = lean_ctor_get(v_userInfo_3171_, 0);
lean_inc(v_val_3204_);
lean_dec_ref_known(v_userInfo_3171_, 1);
v_password_3205_ = lean_ctor_get(v_val_3204_, 1);
if (lean_obj_tag(v_password_3205_) == 0)
{
lean_object* v_username_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v_username_3206_ = lean_ctor_get(v_val_3204_, 0);
lean_inc_ref(v_username_3206_);
lean_dec(v_val_3204_);
v___x_3207_ = lean_string_from_utf8_unchecked(v_username_3206_);
v___x_3208_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3209_ = lean_string_append(v___x_3207_, v___x_3208_);
v___y_3193_ = v___x_3209_;
goto v___jp_3192_;
}
else
{
lean_object* v_username_3210_; lean_object* v_val_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
lean_inc_ref(v_password_3205_);
v_username_3210_ = lean_ctor_get(v_val_3204_, 0);
lean_inc_ref(v_username_3210_);
lean_dec(v_val_3204_);
v_val_3211_ = lean_ctor_get(v_password_3205_, 0);
lean_inc(v_val_3211_);
lean_dec_ref_known(v_password_3205_, 1);
v___x_3212_ = lean_string_from_utf8_unchecked(v_username_3210_);
v___x_3213_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3214_ = lean_string_append(v___x_3212_, v___x_3213_);
v___x_3215_ = lean_string_from_utf8_unchecked(v_val_3211_);
v___x_3216_ = lean_string_append(v___x_3214_, v___x_3215_);
lean_dec_ref(v___x_3215_);
v___x_3217_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3218_ = lean_string_append(v___x_3216_, v___x_3217_);
v___y_3193_ = v___x_3218_;
goto v___jp_3192_;
}
}
v___jp_3175_:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3179_ = lean_string_append(v___y_3176_, v___y_3177_);
lean_dec_ref(v___y_3177_);
v___x_3180_ = lean_string_append(v___x_3179_, v___y_3178_);
lean_dec_ref(v___y_3178_);
v___x_3181_ = lean_string_append(v___x_3174_, v___x_3180_);
lean_dec_ref(v___x_3180_);
v___y_3158_ = v___x_3181_;
goto v___jp_3157_;
}
v___jp_3182_:
{
switch(lean_obj_tag(v_port_3173_))
{
case 0:
{
lean_object* v___x_3185_; 
v___x_3185_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3176_ = v___y_3183_;
v___y_3177_ = v___y_3184_;
v___y_3178_ = v___x_3185_;
goto v___jp_3175_;
}
case 1:
{
lean_object* v___x_3186_; 
v___x_3186_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3176_ = v___y_3183_;
v___y_3177_ = v___y_3184_;
v___y_3178_ = v___x_3186_;
goto v___jp_3175_;
}
default: 
{
uint16_t v_port_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v_port_3187_ = lean_ctor_get_uint16(v_port_3173_, 0);
lean_dec_ref_known(v_port_3173_, 0);
v___x_3188_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3189_ = lean_uint16_to_nat(v_port_3187_);
v___x_3190_ = l_Nat_reprFast(v___x_3189_);
v___x_3191_ = lean_string_append(v___x_3188_, v___x_3190_);
lean_dec_ref(v___x_3190_);
v___y_3176_ = v___y_3183_;
v___y_3177_ = v___y_3184_;
v___y_3178_ = v___x_3191_;
goto v___jp_3175_;
}
}
}
v___jp_3192_:
{
switch(lean_obj_tag(v_host_3172_))
{
case 0:
{
lean_object* v_name_3194_; 
v_name_3194_ = lean_ctor_get(v_host_3172_, 0);
lean_inc_ref(v_name_3194_);
lean_dec_ref_known(v_host_3172_, 1);
v___y_3183_ = v___y_3193_;
v___y_3184_ = v_name_3194_;
goto v___jp_3182_;
}
case 1:
{
lean_object* v_ipv4_3195_; lean_object* v___x_3196_; 
v_ipv4_3195_ = lean_ctor_get(v_host_3172_, 0);
lean_inc_ref(v_ipv4_3195_);
lean_dec_ref_known(v_host_3172_, 1);
v___x_3196_ = lean_uv_ntop_v4(v_ipv4_3195_);
lean_dec_ref(v_ipv4_3195_);
v___y_3183_ = v___y_3193_;
v___y_3184_ = v___x_3196_;
goto v___jp_3182_;
}
default: 
{
lean_object* v_ipv6_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v_ipv6_3197_ = lean_ctor_get(v_host_3172_, 0);
lean_inc_ref(v_ipv6_3197_);
lean_dec_ref_known(v_host_3172_, 1);
v___x_3198_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3199_ = lean_uv_ntop_v6(v_ipv6_3197_);
lean_dec_ref(v_ipv6_3197_);
v___x_3200_ = lean_string_append(v___x_3198_, v___x_3199_);
lean_dec_ref(v___x_3199_);
v___x_3201_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3202_ = lean_string_append(v___x_3200_, v___x_3201_);
v___y_3183_ = v___y_3193_;
v___y_3184_ = v___x_3202_;
goto v___jp_3182_;
}
}
}
}
v___jp_3135_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = lean_string_append(v___y_3137_, v___y_3138_);
lean_dec_ref(v___y_3138_);
v___x_3141_ = lean_string_append(v___x_3140_, v___y_3136_);
lean_dec_ref(v___y_3136_);
v___x_3142_ = lean_string_append(v___x_3141_, v___y_3139_);
lean_dec_ref(v___y_3139_);
return v___x_3142_;
}
v___jp_3147_:
{
lean_object* v_queryPart_3150_; 
v_queryPart_3150_ = l_Std_Http_URI_Query_formatOption(v_query_3145_);
if (lean_obj_tag(v_fragment_3146_) == 0)
{
lean_object* v___x_3151_; 
v___x_3151_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3136_ = v_queryPart_3150_;
v___y_3137_ = v___y_3148_;
v___y_3138_ = v___y_3149_;
v___y_3139_ = v___x_3151_;
goto v___jp_3135_;
}
else
{
lean_object* v_val_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v_val_3152_ = lean_ctor_get(v_fragment_3146_, 0);
lean_inc(v_val_3152_);
lean_dec_ref_known(v_fragment_3146_, 1);
v___x_3153_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3154_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3152_);
lean_dec(v_val_3152_);
v___x_3155_ = lean_string_from_utf8_unchecked(v___x_3154_);
v___x_3156_ = lean_string_append(v___x_3153_, v___x_3155_);
lean_dec_ref(v___x_3155_);
v___y_3136_ = v_queryPart_3150_;
v___y_3137_ = v___y_3148_;
v___y_3138_ = v___y_3149_;
v___y_3139_ = v___x_3156_;
goto v___jp_3135_;
}
}
v___jp_3157_:
{
lean_object* v_segments_3159_; uint8_t v_absolute_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; size_t v_sz_3163_; size_t v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v_result_3167_; 
v_segments_3159_ = lean_ctor_get(v_path_3144_, 0);
lean_inc_ref(v_segments_3159_);
v_absolute_3160_ = lean_ctor_get_uint8(v_path_3144_, sizeof(void*)*1);
lean_dec_ref(v_path_3144_);
v___x_3161_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3162_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3163_ = lean_array_size(v_segments_3159_);
v___x_3164_ = ((size_t)0ULL);
v___x_3165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3162_, v___f_3133_, v_sz_3163_, v___x_3164_, v_segments_3159_);
v___x_3166_ = lean_array_to_list(v___x_3165_);
v_result_3167_ = l_String_intercalate(v___x_3161_, v___x_3166_);
if (v_absolute_3160_ == 0)
{
v___y_3148_ = v___y_3158_;
v___y_3149_ = v_result_3167_;
goto v___jp_3147_;
}
else
{
lean_object* v___x_3168_; 
v___x_3168_ = lean_string_append(v___x_3161_, v_result_3167_);
lean_dec_ref(v_result_3167_);
v___y_3148_ = v___y_3158_;
v___y_3149_ = v___x_3168_;
goto v___jp_3147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___impl(lean_object* v_x_3222_){
_start:
{
lean_object* v___x_3223_; 
v___x_3223_ = lean_obj_tag_nat(v_x_3222_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___impl___boxed(lean_object* v_x_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Std_Http_URIReference_ctorIdx___impl(v_x_3224_);
lean_dec_ref(v_x_3224_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___redArg(lean_object* v_t_3226_, lean_object* v_k_3227_){
_start:
{
lean_object* v_uri_3228_; lean_object* v___x_3229_; 
v_uri_3228_ = lean_ctor_get(v_t_3226_, 0);
lean_inc_ref(v_uri_3228_);
lean_dec_ref(v_t_3226_);
v___x_3229_ = lean_apply_1(v_k_3227_, v_uri_3228_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim(lean_object* v_motive_3230_, lean_object* v_ctorIdx_3231_, lean_object* v_t_3232_, lean_object* v_h_3233_, lean_object* v_k_3234_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3232_, v_k_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___boxed(lean_object* v_motive_3236_, lean_object* v_ctorIdx_3237_, lean_object* v_t_3238_, lean_object* v_h_3239_, lean_object* v_k_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Std_Http_URIReference_ctorElim(v_motive_3236_, v_ctorIdx_3237_, v_t_3238_, v_h_3239_, v_k_3240_);
lean_dec(v_ctorIdx_3237_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim___redArg(lean_object* v_t_3242_, lean_object* v_absolute_3243_){
_start:
{
lean_object* v___x_3244_; 
v___x_3244_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3242_, v_absolute_3243_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim(lean_object* v_motive_3245_, lean_object* v_t_3246_, lean_object* v_h_3247_, lean_object* v_absolute_3248_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3246_, v_absolute_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim___redArg(lean_object* v_t_3250_, lean_object* v_relative_3251_){
_start:
{
lean_object* v___x_3252_; 
v___x_3252_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3250_, v_relative_3251_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim(lean_object* v_motive_3253_, lean_object* v_t_3254_, lean_object* v_h_3255_, lean_object* v_relative_3256_){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3254_, v_relative_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr(lean_object* v_x_3270_, lean_object* v_prec_3271_){
_start:
{
if (lean_obj_tag(v_x_3270_) == 0)
{
lean_object* v_uri_3272_; lean_object* v___y_3274_; lean_object* v___x_3282_; uint8_t v___x_3283_; 
v_uri_3272_ = lean_ctor_get(v_x_3270_, 0);
lean_inc_ref(v_uri_3272_);
lean_dec_ref_known(v_x_3270_, 1);
v___x_3282_ = lean_unsigned_to_nat(1024u);
v___x_3283_ = lean_nat_dec_le(v___x_3282_, v_prec_3271_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; 
v___x_3284_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3274_ = v___x_3284_;
goto v___jp_3273_;
}
else
{
lean_object* v___x_3285_; 
v___x_3285_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3274_ = v___x_3285_;
goto v___jp_3273_;
}
v___jp_3273_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; uint8_t v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3275_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__2));
v___x_3276_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3272_);
v___x_3277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3275_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
lean_inc(v___y_3274_);
v___x_3278_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___y_3274_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
v___x_3279_ = 0;
v___x_3280_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3280_, 0, v___x_3278_);
lean_ctor_set_uint8(v___x_3280_, sizeof(void*)*1, v___x_3279_);
v___x_3281_ = l_Repr_addAppParen(v___x_3280_, v_prec_3271_);
return v___x_3281_;
}
}
else
{
lean_object* v_ref_3286_; lean_object* v___y_3288_; lean_object* v___x_3296_; uint8_t v___x_3297_; 
v_ref_3286_ = lean_ctor_get(v_x_3270_, 0);
lean_inc_ref(v_ref_3286_);
lean_dec_ref_known(v_x_3270_, 1);
v___x_3296_ = lean_unsigned_to_nat(1024u);
v___x_3297_ = lean_nat_dec_le(v___x_3296_, v_prec_3271_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; 
v___x_3298_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3288_ = v___x_3298_;
goto v___jp_3287_;
}
else
{
lean_object* v___x_3299_; 
v___x_3299_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3288_ = v___x_3299_;
goto v___jp_3287_;
}
v___jp_3287_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3289_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__5));
v___x_3290_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_ref_3286_);
v___x_3291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3289_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
lean_inc(v___y_3288_);
v___x_3292_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___y_3288_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = 0;
v___x_3294_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3294_, 0, v___x_3292_);
lean_ctor_set_uint8(v___x_3294_, sizeof(void*)*1, v___x_3293_);
v___x_3295_ = l_Repr_addAppParen(v___x_3294_, v_prec_3271_);
return v___x_3295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr___boxed(lean_object* v_x_3300_, lean_object* v_prec_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Std_Http_instReprURIReference_repr(v_x_3300_, v_prec_3301_);
lean_dec(v_prec_3301_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURIReference___lam__2(lean_object* v___f_3309_, lean_object* v___f_3310_, lean_object* v_x_3311_){
_start:
{
lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; 
if (lean_obj_tag(v_x_3311_) == 0)
{
lean_object* v_uri_3320_; lean_object* v_scheme_3321_; lean_object* v_authority_3322_; lean_object* v_path_3323_; lean_object* v_query_3324_; lean_object* v_fragment_3325_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3348_; 
lean_dec_ref(v___f_3310_);
v_uri_3320_ = lean_ctor_get(v_x_3311_, 0);
lean_inc_ref(v_uri_3320_);
lean_dec_ref_known(v_x_3311_, 1);
v_scheme_3321_ = lean_ctor_get(v_uri_3320_, 0);
lean_inc_ref(v_scheme_3321_);
v_authority_3322_ = lean_ctor_get(v_uri_3320_, 1);
lean_inc(v_authority_3322_);
v_path_3323_ = lean_ctor_get(v_uri_3320_, 2);
lean_inc_ref(v_path_3323_);
v_query_3324_ = lean_ctor_get(v_uri_3320_, 3);
lean_inc(v_query_3324_);
v_fragment_3325_ = lean_ctor_get(v_uri_3320_, 4);
lean_inc(v_fragment_3325_);
lean_dec_ref(v_uri_3320_);
if (lean_obj_tag(v_authority_3322_) == 0)
{
lean_object* v___x_3359_; 
v___x_3359_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3348_ = v___x_3359_;
goto v___jp_3347_;
}
else
{
lean_object* v_val_3360_; lean_object* v_userInfo_3361_; lean_object* v_host_3362_; lean_object* v_port_3363_; lean_object* v___x_3364_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3383_; 
v_val_3360_ = lean_ctor_get(v_authority_3322_, 0);
lean_inc(v_val_3360_);
lean_dec_ref_known(v_authority_3322_, 1);
v_userInfo_3361_ = lean_ctor_get(v_val_3360_, 0);
lean_inc(v_userInfo_3361_);
v_host_3362_ = lean_ctor_get(v_val_3360_, 1);
lean_inc_ref(v_host_3362_);
v_port_3363_ = lean_ctor_get(v_val_3360_, 2);
lean_inc(v_port_3363_);
lean_dec(v_val_3360_);
v___x_3364_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3361_) == 0)
{
lean_object* v___x_3393_; 
v___x_3393_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3383_ = v___x_3393_;
goto v___jp_3382_;
}
else
{
lean_object* v_val_3394_; lean_object* v_password_3395_; 
v_val_3394_ = lean_ctor_get(v_userInfo_3361_, 0);
lean_inc(v_val_3394_);
lean_dec_ref_known(v_userInfo_3361_, 1);
v_password_3395_ = lean_ctor_get(v_val_3394_, 1);
if (lean_obj_tag(v_password_3395_) == 0)
{
lean_object* v_username_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v_username_3396_ = lean_ctor_get(v_val_3394_, 0);
lean_inc_ref(v_username_3396_);
lean_dec(v_val_3394_);
v___x_3397_ = lean_string_from_utf8_unchecked(v_username_3396_);
v___x_3398_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3399_ = lean_string_append(v___x_3397_, v___x_3398_);
v___y_3383_ = v___x_3399_;
goto v___jp_3382_;
}
else
{
lean_object* v_username_3400_; lean_object* v_val_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
lean_inc_ref(v_password_3395_);
v_username_3400_ = lean_ctor_get(v_val_3394_, 0);
lean_inc_ref(v_username_3400_);
lean_dec(v_val_3394_);
v_val_3401_ = lean_ctor_get(v_password_3395_, 0);
lean_inc(v_val_3401_);
lean_dec_ref_known(v_password_3395_, 1);
v___x_3402_ = lean_string_from_utf8_unchecked(v_username_3400_);
v___x_3403_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3404_ = lean_string_append(v___x_3402_, v___x_3403_);
v___x_3405_ = lean_string_from_utf8_unchecked(v_val_3401_);
v___x_3406_ = lean_string_append(v___x_3404_, v___x_3405_);
lean_dec_ref(v___x_3405_);
v___x_3407_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3408_ = lean_string_append(v___x_3406_, v___x_3407_);
v___y_3383_ = v___x_3408_;
goto v___jp_3382_;
}
}
v___jp_3365_:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3369_ = lean_string_append(v___y_3366_, v___y_3367_);
lean_dec_ref(v___y_3367_);
v___x_3370_ = lean_string_append(v___x_3369_, v___y_3368_);
lean_dec_ref(v___y_3368_);
v___x_3371_ = lean_string_append(v___x_3364_, v___x_3370_);
lean_dec_ref(v___x_3370_);
v___y_3348_ = v___x_3371_;
goto v___jp_3347_;
}
v___jp_3372_:
{
switch(lean_obj_tag(v_port_3363_))
{
case 0:
{
lean_object* v___x_3375_; 
v___x_3375_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3366_ = v___y_3373_;
v___y_3367_ = v___y_3374_;
v___y_3368_ = v___x_3375_;
goto v___jp_3365_;
}
case 1:
{
lean_object* v___x_3376_; 
v___x_3376_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3366_ = v___y_3373_;
v___y_3367_ = v___y_3374_;
v___y_3368_ = v___x_3376_;
goto v___jp_3365_;
}
default: 
{
uint16_t v_port_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v_port_3377_ = lean_ctor_get_uint16(v_port_3363_, 0);
lean_dec_ref_known(v_port_3363_, 0);
v___x_3378_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3379_ = lean_uint16_to_nat(v_port_3377_);
v___x_3380_ = l_Nat_reprFast(v___x_3379_);
v___x_3381_ = lean_string_append(v___x_3378_, v___x_3380_);
lean_dec_ref(v___x_3380_);
v___y_3366_ = v___y_3373_;
v___y_3367_ = v___y_3374_;
v___y_3368_ = v___x_3381_;
goto v___jp_3365_;
}
}
}
v___jp_3382_:
{
switch(lean_obj_tag(v_host_3362_))
{
case 0:
{
lean_object* v_name_3384_; 
v_name_3384_ = lean_ctor_get(v_host_3362_, 0);
lean_inc_ref(v_name_3384_);
lean_dec_ref_known(v_host_3362_, 1);
v___y_3373_ = v___y_3383_;
v___y_3374_ = v_name_3384_;
goto v___jp_3372_;
}
case 1:
{
lean_object* v_ipv4_3385_; lean_object* v___x_3386_; 
v_ipv4_3385_ = lean_ctor_get(v_host_3362_, 0);
lean_inc_ref(v_ipv4_3385_);
lean_dec_ref_known(v_host_3362_, 1);
v___x_3386_ = lean_uv_ntop_v4(v_ipv4_3385_);
lean_dec_ref(v_ipv4_3385_);
v___y_3373_ = v___y_3383_;
v___y_3374_ = v___x_3386_;
goto v___jp_3372_;
}
default: 
{
lean_object* v_ipv6_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v_ipv6_3387_ = lean_ctor_get(v_host_3362_, 0);
lean_inc_ref(v_ipv6_3387_);
lean_dec_ref_known(v_host_3362_, 1);
v___x_3388_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3389_ = lean_uv_ntop_v6(v_ipv6_3387_);
lean_dec_ref(v_ipv6_3387_);
v___x_3390_ = lean_string_append(v___x_3388_, v___x_3389_);
lean_dec_ref(v___x_3389_);
v___x_3391_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3392_ = lean_string_append(v___x_3390_, v___x_3391_);
v___y_3373_ = v___y_3383_;
v___y_3374_ = v___x_3392_;
goto v___jp_3372_;
}
}
}
}
v___jp_3326_:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3331_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3332_ = lean_string_append(v_scheme_3321_, v___x_3331_);
v___x_3333_ = lean_string_append(v___x_3332_, v___y_3327_);
lean_dec_ref(v___y_3327_);
v___x_3334_ = lean_string_append(v___x_3333_, v___y_3329_);
lean_dec_ref(v___y_3329_);
v___x_3335_ = lean_string_append(v___x_3334_, v___y_3328_);
lean_dec_ref(v___y_3328_);
v___x_3336_ = lean_string_append(v___x_3335_, v___y_3330_);
lean_dec_ref(v___y_3330_);
return v___x_3336_;
}
v___jp_3337_:
{
lean_object* v_queryPart_3340_; 
v_queryPart_3340_ = l_Std_Http_URI_Query_formatOption(v_query_3324_);
if (lean_obj_tag(v_fragment_3325_) == 0)
{
lean_object* v___x_3341_; 
v___x_3341_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3327_ = v___y_3338_;
v___y_3328_ = v_queryPart_3340_;
v___y_3329_ = v___y_3339_;
v___y_3330_ = v___x_3341_;
goto v___jp_3326_;
}
else
{
lean_object* v_val_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v_val_3342_ = lean_ctor_get(v_fragment_3325_, 0);
lean_inc(v_val_3342_);
lean_dec_ref_known(v_fragment_3325_, 1);
v___x_3343_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3344_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3342_);
lean_dec(v_val_3342_);
v___x_3345_ = lean_string_from_utf8_unchecked(v___x_3344_);
v___x_3346_ = lean_string_append(v___x_3343_, v___x_3345_);
lean_dec_ref(v___x_3345_);
v___y_3327_ = v___y_3338_;
v___y_3328_ = v_queryPart_3340_;
v___y_3329_ = v___y_3339_;
v___y_3330_ = v___x_3346_;
goto v___jp_3326_;
}
}
v___jp_3347_:
{
lean_object* v_segments_3349_; uint8_t v_absolute_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; size_t v_sz_3353_; size_t v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v_result_3357_; 
v_segments_3349_ = lean_ctor_get(v_path_3323_, 0);
lean_inc_ref(v_segments_3349_);
v_absolute_3350_ = lean_ctor_get_uint8(v_path_3323_, sizeof(void*)*1);
lean_dec_ref(v_path_3323_);
v___x_3351_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3352_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3353_ = lean_array_size(v_segments_3349_);
v___x_3354_ = ((size_t)0ULL);
v___x_3355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3352_, v___f_3309_, v_sz_3353_, v___x_3354_, v_segments_3349_);
v___x_3356_ = lean_array_to_list(v___x_3355_);
v_result_3357_ = l_String_intercalate(v___x_3351_, v___x_3356_);
if (v_absolute_3350_ == 0)
{
v___y_3338_ = v___y_3348_;
v___y_3339_ = v_result_3357_;
goto v___jp_3337_;
}
else
{
lean_object* v___x_3358_; 
v___x_3358_ = lean_string_append(v___x_3351_, v_result_3357_);
lean_dec_ref(v_result_3357_);
v___y_3338_ = v___y_3348_;
v___y_3339_ = v___x_3358_;
goto v___jp_3337_;
}
}
}
else
{
lean_object* v_ref_3409_; lean_object* v_authority_3410_; lean_object* v_path_3411_; lean_object* v_query_3412_; lean_object* v_fragment_3413_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3425_; 
lean_dec_ref(v___f_3309_);
v_ref_3409_ = lean_ctor_get(v_x_3311_, 0);
lean_inc_ref(v_ref_3409_);
lean_dec_ref_known(v_x_3311_, 1);
v_authority_3410_ = lean_ctor_get(v_ref_3409_, 0);
lean_inc(v_authority_3410_);
v_path_3411_ = lean_ctor_get(v_ref_3409_, 1);
lean_inc_ref(v_path_3411_);
v_query_3412_ = lean_ctor_get(v_ref_3409_, 2);
lean_inc(v_query_3412_);
v_fragment_3413_ = lean_ctor_get(v_ref_3409_, 3);
lean_inc(v_fragment_3413_);
lean_dec_ref(v_ref_3409_);
if (lean_obj_tag(v_authority_3410_) == 0)
{
lean_object* v___x_3436_; 
v___x_3436_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3425_ = v___x_3436_;
goto v___jp_3424_;
}
else
{
lean_object* v_val_3437_; lean_object* v_userInfo_3438_; lean_object* v_host_3439_; lean_object* v_port_3440_; lean_object* v___x_3441_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3460_; 
v_val_3437_ = lean_ctor_get(v_authority_3410_, 0);
lean_inc(v_val_3437_);
lean_dec_ref_known(v_authority_3410_, 1);
v_userInfo_3438_ = lean_ctor_get(v_val_3437_, 0);
lean_inc(v_userInfo_3438_);
v_host_3439_ = lean_ctor_get(v_val_3437_, 1);
lean_inc_ref(v_host_3439_);
v_port_3440_ = lean_ctor_get(v_val_3437_, 2);
lean_inc(v_port_3440_);
lean_dec(v_val_3437_);
v___x_3441_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3438_) == 0)
{
lean_object* v___x_3470_; 
v___x_3470_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3460_ = v___x_3470_;
goto v___jp_3459_;
}
else
{
lean_object* v_val_3471_; lean_object* v_password_3472_; 
v_val_3471_ = lean_ctor_get(v_userInfo_3438_, 0);
lean_inc(v_val_3471_);
lean_dec_ref_known(v_userInfo_3438_, 1);
v_password_3472_ = lean_ctor_get(v_val_3471_, 1);
if (lean_obj_tag(v_password_3472_) == 0)
{
lean_object* v_username_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v_username_3473_ = lean_ctor_get(v_val_3471_, 0);
lean_inc_ref(v_username_3473_);
lean_dec(v_val_3471_);
v___x_3474_ = lean_string_from_utf8_unchecked(v_username_3473_);
v___x_3475_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3476_ = lean_string_append(v___x_3474_, v___x_3475_);
v___y_3460_ = v___x_3476_;
goto v___jp_3459_;
}
else
{
lean_object* v_username_3477_; lean_object* v_val_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
lean_inc_ref(v_password_3472_);
v_username_3477_ = lean_ctor_get(v_val_3471_, 0);
lean_inc_ref(v_username_3477_);
lean_dec(v_val_3471_);
v_val_3478_ = lean_ctor_get(v_password_3472_, 0);
lean_inc(v_val_3478_);
lean_dec_ref_known(v_password_3472_, 1);
v___x_3479_ = lean_string_from_utf8_unchecked(v_username_3477_);
v___x_3480_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3481_ = lean_string_append(v___x_3479_, v___x_3480_);
v___x_3482_ = lean_string_from_utf8_unchecked(v_val_3478_);
v___x_3483_ = lean_string_append(v___x_3481_, v___x_3482_);
lean_dec_ref(v___x_3482_);
v___x_3484_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3485_ = lean_string_append(v___x_3483_, v___x_3484_);
v___y_3460_ = v___x_3485_;
goto v___jp_3459_;
}
}
v___jp_3442_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = lean_string_append(v___y_3443_, v___y_3444_);
lean_dec_ref(v___y_3444_);
v___x_3447_ = lean_string_append(v___x_3446_, v___y_3445_);
lean_dec_ref(v___y_3445_);
v___x_3448_ = lean_string_append(v___x_3441_, v___x_3447_);
lean_dec_ref(v___x_3447_);
v___y_3425_ = v___x_3448_;
goto v___jp_3424_;
}
v___jp_3449_:
{
switch(lean_obj_tag(v_port_3440_))
{
case 0:
{
lean_object* v___x_3452_; 
v___x_3452_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3443_ = v___y_3450_;
v___y_3444_ = v___y_3451_;
v___y_3445_ = v___x_3452_;
goto v___jp_3442_;
}
case 1:
{
lean_object* v___x_3453_; 
v___x_3453_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3443_ = v___y_3450_;
v___y_3444_ = v___y_3451_;
v___y_3445_ = v___x_3453_;
goto v___jp_3442_;
}
default: 
{
uint16_t v_port_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v_port_3454_ = lean_ctor_get_uint16(v_port_3440_, 0);
lean_dec_ref_known(v_port_3440_, 0);
v___x_3455_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3456_ = lean_uint16_to_nat(v_port_3454_);
v___x_3457_ = l_Nat_reprFast(v___x_3456_);
v___x_3458_ = lean_string_append(v___x_3455_, v___x_3457_);
lean_dec_ref(v___x_3457_);
v___y_3443_ = v___y_3450_;
v___y_3444_ = v___y_3451_;
v___y_3445_ = v___x_3458_;
goto v___jp_3442_;
}
}
}
v___jp_3459_:
{
switch(lean_obj_tag(v_host_3439_))
{
case 0:
{
lean_object* v_name_3461_; 
v_name_3461_ = lean_ctor_get(v_host_3439_, 0);
lean_inc_ref(v_name_3461_);
lean_dec_ref_known(v_host_3439_, 1);
v___y_3450_ = v___y_3460_;
v___y_3451_ = v_name_3461_;
goto v___jp_3449_;
}
case 1:
{
lean_object* v_ipv4_3462_; lean_object* v___x_3463_; 
v_ipv4_3462_ = lean_ctor_get(v_host_3439_, 0);
lean_inc_ref(v_ipv4_3462_);
lean_dec_ref_known(v_host_3439_, 1);
v___x_3463_ = lean_uv_ntop_v4(v_ipv4_3462_);
lean_dec_ref(v_ipv4_3462_);
v___y_3450_ = v___y_3460_;
v___y_3451_ = v___x_3463_;
goto v___jp_3449_;
}
default: 
{
lean_object* v_ipv6_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v_ipv6_3464_ = lean_ctor_get(v_host_3439_, 0);
lean_inc_ref(v_ipv6_3464_);
lean_dec_ref_known(v_host_3439_, 1);
v___x_3465_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3466_ = lean_uv_ntop_v6(v_ipv6_3464_);
lean_dec_ref(v_ipv6_3464_);
v___x_3467_ = lean_string_append(v___x_3465_, v___x_3466_);
lean_dec_ref(v___x_3466_);
v___x_3468_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3469_ = lean_string_append(v___x_3467_, v___x_3468_);
v___y_3450_ = v___y_3460_;
v___y_3451_ = v___x_3469_;
goto v___jp_3449_;
}
}
}
}
v___jp_3414_:
{
lean_object* v_queryPart_3417_; 
v_queryPart_3417_ = l_Std_Http_URI_Query_formatOption(v_query_3412_);
if (lean_obj_tag(v_fragment_3413_) == 0)
{
lean_object* v___x_3418_; 
v___x_3418_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3313_ = v_queryPart_3417_;
v___y_3314_ = v___y_3415_;
v___y_3315_ = v___y_3416_;
v___y_3316_ = v___x_3418_;
goto v___jp_3312_;
}
else
{
lean_object* v_val_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v_val_3419_ = lean_ctor_get(v_fragment_3413_, 0);
lean_inc(v_val_3419_);
lean_dec_ref_known(v_fragment_3413_, 1);
v___x_3420_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3421_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3419_);
lean_dec(v_val_3419_);
v___x_3422_ = lean_string_from_utf8_unchecked(v___x_3421_);
v___x_3423_ = lean_string_append(v___x_3420_, v___x_3422_);
lean_dec_ref(v___x_3422_);
v___y_3313_ = v_queryPart_3417_;
v___y_3314_ = v___y_3415_;
v___y_3315_ = v___y_3416_;
v___y_3316_ = v___x_3423_;
goto v___jp_3312_;
}
}
v___jp_3424_:
{
lean_object* v_segments_3426_; uint8_t v_absolute_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; size_t v_sz_3430_; size_t v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v_result_3434_; 
v_segments_3426_ = lean_ctor_get(v_path_3411_, 0);
lean_inc_ref(v_segments_3426_);
v_absolute_3427_ = lean_ctor_get_uint8(v_path_3411_, sizeof(void*)*1);
lean_dec_ref(v_path_3411_);
v___x_3428_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3429_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3430_ = lean_array_size(v_segments_3426_);
v___x_3431_ = ((size_t)0ULL);
v___x_3432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3429_, v___f_3310_, v_sz_3430_, v___x_3431_, v_segments_3426_);
v___x_3433_ = lean_array_to_list(v___x_3432_);
v_result_3434_ = l_String_intercalate(v___x_3428_, v___x_3433_);
if (v_absolute_3427_ == 0)
{
v___y_3415_ = v___y_3425_;
v___y_3416_ = v_result_3434_;
goto v___jp_3414_;
}
else
{
lean_object* v___x_3435_; 
v___x_3435_ = lean_string_append(v___x_3428_, v_result_3434_);
lean_dec_ref(v_result_3434_);
v___y_3415_ = v___y_3425_;
v___y_3416_ = v___x_3435_;
goto v___jp_3414_;
}
}
}
v___jp_3312_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = lean_string_append(v___y_3314_, v___y_3315_);
lean_dec_ref(v___y_3315_);
v___x_3318_ = lean_string_append(v___x_3317_, v___y_3313_);
lean_dec_ref(v___y_3313_);
v___x_3319_ = lean_string_append(v___x_3318_, v___y_3316_);
lean_dec_ref(v___y_3316_);
return v___x_3319_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___impl(lean_object* v_x_3489_){
_start:
{
lean_object* v___x_3490_; 
v___x_3490_ = lean_obj_tag_nat(v_x_3489_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___impl___boxed(lean_object* v_x_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Std_Http_RequestTarget_ctorIdx___impl(v_x_3491_);
lean_dec(v_x_3491_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___redArg(lean_object* v_t_3493_, lean_object* v_k_3494_){
_start:
{
switch(lean_obj_tag(v_t_3493_))
{
case 0:
{
lean_object* v_path_3495_; lean_object* v_query_3496_; lean_object* v___x_3497_; 
v_path_3495_ = lean_ctor_get(v_t_3493_, 0);
lean_inc_ref(v_path_3495_);
v_query_3496_ = lean_ctor_get(v_t_3493_, 1);
lean_inc(v_query_3496_);
lean_dec_ref_known(v_t_3493_, 2);
v___x_3497_ = lean_apply_2(v_k_3494_, v_path_3495_, v_query_3496_);
return v___x_3497_;
}
case 3:
{
return v_k_3494_;
}
default: 
{
lean_object* v_uri_3498_; lean_object* v___x_3499_; 
v_uri_3498_ = lean_ctor_get(v_t_3493_, 0);
lean_inc_ref(v_uri_3498_);
lean_dec(v_t_3493_);
v___x_3499_ = lean_apply_1(v_k_3494_, v_uri_3498_);
return v___x_3499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim(lean_object* v_motive_3500_, lean_object* v_ctorIdx_3501_, lean_object* v_t_3502_, lean_object* v_h_3503_, lean_object* v_k_3504_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3502_, v_k_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___boxed(lean_object* v_motive_3506_, lean_object* v_ctorIdx_3507_, lean_object* v_t_3508_, lean_object* v_h_3509_, lean_object* v_k_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Std_Http_RequestTarget_ctorElim(v_motive_3506_, v_ctorIdx_3507_, v_t_3508_, v_h_3509_, v_k_3510_);
lean_dec(v_ctorIdx_3507_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim___redArg(lean_object* v_t_3512_, lean_object* v_originForm_3513_){
_start:
{
lean_object* v___x_3514_; 
v___x_3514_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3512_, v_originForm_3513_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim(lean_object* v_motive_3515_, lean_object* v_t_3516_, lean_object* v_h_3517_, lean_object* v_originForm_3518_){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3516_, v_originForm_3518_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim___redArg(lean_object* v_t_3520_, lean_object* v_absoluteForm_3521_){
_start:
{
lean_object* v___x_3522_; 
v___x_3522_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3520_, v_absoluteForm_3521_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim(lean_object* v_motive_3523_, lean_object* v_t_3524_, lean_object* v_h_3525_, lean_object* v_absoluteForm_3526_){
_start:
{
lean_object* v___x_3527_; 
v___x_3527_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3524_, v_absoluteForm_3526_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim___redArg(lean_object* v_t_3528_, lean_object* v_authorityForm_3529_){
_start:
{
lean_object* v___x_3530_; 
v___x_3530_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3528_, v_authorityForm_3529_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim(lean_object* v_motive_3531_, lean_object* v_t_3532_, lean_object* v_h_3533_, lean_object* v_authorityForm_3534_){
_start:
{
lean_object* v___x_3535_; 
v___x_3535_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3532_, v_authorityForm_3534_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim___redArg(lean_object* v_t_3536_, lean_object* v_asteriskForm_3537_){
_start:
{
lean_object* v___x_3538_; 
v___x_3538_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3536_, v_asteriskForm_3537_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim(lean_object* v_motive_3539_, lean_object* v_t_3540_, lean_object* v_h_3541_, lean_object* v_asteriskForm_3542_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3540_, v_asteriskForm_3542_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object* v_x_3570_, lean_object* v_prec_3571_){
_start:
{
lean_object* v___y_3573_; 
switch(lean_obj_tag(v_x_3570_))
{
case 0:
{
lean_object* v_path_3579_; lean_object* v_query_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3604_; 
v_path_3579_ = lean_ctor_get(v_x_3570_, 0);
v_query_3580_ = lean_ctor_get(v_x_3570_, 1);
v_isSharedCheck_3604_ = !lean_is_exclusive(v_x_3570_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3582_ = v_x_3570_;
v_isShared_3583_ = v_isSharedCheck_3604_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_query_3580_);
lean_inc(v_path_3579_);
lean_dec(v_x_3570_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3604_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___y_3585_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3600_ = lean_unsigned_to_nat(1024u);
v___x_3601_ = lean_nat_dec_le(v___x_3600_, v_prec_3571_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; 
v___x_3602_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3585_ = v___x_3602_;
goto v___jp_3584_;
}
else
{
lean_object* v___x_3603_; 
v___x_3603_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3585_ = v___x_3603_;
goto v___jp_3584_;
}
v___jp_3584_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3591_; 
v___x_3586_ = lean_box(1);
v___x_3587_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__4));
v___x_3588_ = lean_unsigned_to_nat(1024u);
v___x_3589_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3579_);
if (v_isShared_3583_ == 0)
{
lean_ctor_set_tag(v___x_3582_, 5);
lean_ctor_set(v___x_3582_, 1, v___x_3589_);
lean_ctor_set(v___x_3582_, 0, v___x_3587_);
v___x_3591_ = v___x_3582_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3587_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v___x_3589_);
v___x_3591_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
lean_ctor_set(v___x_3592_, 1, v___x_3586_);
v___x_3593_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3580_, v___x_3588_);
v___x_3594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3592_);
lean_ctor_set(v___x_3594_, 1, v___x_3593_);
lean_inc(v___y_3585_);
v___x_3595_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___y_3585_);
lean_ctor_set(v___x_3595_, 1, v___x_3594_);
v___x_3596_ = 0;
v___x_3597_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3597_, 0, v___x_3595_);
lean_ctor_set_uint8(v___x_3597_, sizeof(void*)*1, v___x_3596_);
v___x_3598_ = l_Repr_addAppParen(v___x_3597_, v_prec_3571_);
return v___x_3598_;
}
}
}
}
case 1:
{
lean_object* v_uri_3605_; lean_object* v___y_3607_; lean_object* v___x_3615_; uint8_t v___x_3616_; 
v_uri_3605_ = lean_ctor_get(v_x_3570_, 0);
lean_inc_ref(v_uri_3605_);
lean_dec_ref_known(v_x_3570_, 1);
v___x_3615_ = lean_unsigned_to_nat(1024u);
v___x_3616_ = lean_nat_dec_le(v___x_3615_, v_prec_3571_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; 
v___x_3617_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3607_ = v___x_3617_;
goto v___jp_3606_;
}
else
{
lean_object* v___x_3618_; 
v___x_3618_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3607_ = v___x_3618_;
goto v___jp_3606_;
}
v___jp_3606_:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3608_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__7));
v___x_3609_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3605_);
v___x_3610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3608_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
lean_inc(v___y_3607_);
v___x_3611_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___y_3607_);
lean_ctor_set(v___x_3611_, 1, v___x_3610_);
v___x_3612_ = 0;
v___x_3613_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3613_, 0, v___x_3611_);
lean_ctor_set_uint8(v___x_3613_, sizeof(void*)*1, v___x_3612_);
v___x_3614_ = l_Repr_addAppParen(v___x_3613_, v_prec_3571_);
return v___x_3614_;
}
}
case 2:
{
lean_object* v_authority_3619_; lean_object* v___y_3621_; lean_object* v___x_3629_; uint8_t v___x_3630_; 
v_authority_3619_ = lean_ctor_get(v_x_3570_, 0);
lean_inc_ref(v_authority_3619_);
lean_dec_ref_known(v_x_3570_, 1);
v___x_3629_ = lean_unsigned_to_nat(1024u);
v___x_3630_ = lean_nat_dec_le(v___x_3629_, v_prec_3571_);
if (v___x_3630_ == 0)
{
lean_object* v___x_3631_; 
v___x_3631_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3621_ = v___x_3631_;
goto v___jp_3620_;
}
else
{
lean_object* v___x_3632_; 
v___x_3632_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3621_ = v___x_3632_;
goto v___jp_3620_;
}
v___jp_3620_:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; uint8_t v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3622_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__10));
v___x_3623_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_authority_3619_);
v___x_3624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3622_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
lean_inc(v___y_3621_);
v___x_3625_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___y_3621_);
lean_ctor_set(v___x_3625_, 1, v___x_3624_);
v___x_3626_ = 0;
v___x_3627_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3627_, 0, v___x_3625_);
lean_ctor_set_uint8(v___x_3627_, sizeof(void*)*1, v___x_3626_);
v___x_3628_ = l_Repr_addAppParen(v___x_3627_, v_prec_3571_);
return v___x_3628_;
}
}
default: 
{
lean_object* v___x_3633_; uint8_t v___x_3634_; 
v___x_3633_ = lean_unsigned_to_nat(1024u);
v___x_3634_ = lean_nat_dec_le(v___x_3633_, v_prec_3571_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; 
v___x_3635_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3573_ = v___x_3635_;
goto v___jp_3572_;
}
else
{
lean_object* v___x_3636_; 
v___x_3636_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3573_ = v___x_3636_;
goto v___jp_3572_;
}
}
}
v___jp_3572_:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3574_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__1));
lean_inc(v___y_3573_);
v___x_3575_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___y_3573_);
lean_ctor_set(v___x_3575_, 1, v___x_3574_);
v___x_3576_ = 0;
v___x_3577_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3577_, 0, v___x_3575_);
lean_ctor_set_uint8(v___x_3577_, sizeof(void*)*1, v___x_3576_);
v___x_3578_ = l_Repr_addAppParen(v___x_3577_, v_prec_3571_);
return v___x_3578_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr___boxed(lean_object* v_x_3637_, lean_object* v_prec_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_Std_Http_instReprRequestTarget_repr(v_x_3637_, v_prec_3638_);
lean_dec(v_prec_3638_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path(lean_object* v_x_3647_){
_start:
{
switch(lean_obj_tag(v_x_3647_))
{
case 0:
{
lean_object* v_path_3648_; 
v_path_3648_ = lean_ctor_get(v_x_3647_, 0);
lean_inc_ref(v_path_3648_);
return v_path_3648_;
}
case 1:
{
lean_object* v_uri_3649_; lean_object* v_path_3650_; 
v_uri_3649_ = lean_ctor_get(v_x_3647_, 0);
v_path_3650_ = lean_ctor_get(v_uri_3649_, 2);
lean_inc_ref(v_path_3650_);
return v_path_3650_;
}
default: 
{
lean_object* v___x_3651_; 
v___x_3651_ = ((lean_object*)(l_Std_Http_RequestTarget_path___closed__1));
return v___x_3651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path___boxed(lean_object* v_x_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l_Std_Http_RequestTarget_path(v_x_3652_);
lean_dec(v_x_3652_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query(lean_object* v_x_3654_){
_start:
{
switch(lean_obj_tag(v_x_3654_))
{
case 0:
{
lean_object* v_query_3655_; 
v_query_3655_ = lean_ctor_get(v_x_3654_, 1);
if (lean_obj_tag(v_query_3655_) == 0)
{
lean_object* v___x_3656_; 
v___x_3656_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3656_;
}
else
{
lean_object* v_val_3657_; 
v_val_3657_ = lean_ctor_get(v_query_3655_, 0);
lean_inc(v_val_3657_);
return v_val_3657_;
}
}
case 1:
{
lean_object* v_uri_3658_; lean_object* v_query_3659_; 
v_uri_3658_ = lean_ctor_get(v_x_3654_, 0);
v_query_3659_ = lean_ctor_get(v_uri_3658_, 3);
if (lean_obj_tag(v_query_3659_) == 0)
{
lean_object* v___x_3660_; 
v___x_3660_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3660_;
}
else
{
lean_object* v_val_3661_; 
v_val_3661_ = lean_ctor_get(v_query_3659_, 0);
lean_inc(v_val_3661_);
return v_val_3661_;
}
}
default: 
{
lean_object* v___x_3662_; 
v___x_3662_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query___boxed(lean_object* v_x_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l_Std_Http_RequestTarget_query(v_x_3663_);
lean_dec(v_x_3663_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authority_x3f(lean_object* v_x_3665_){
_start:
{
switch(lean_obj_tag(v_x_3665_))
{
case 2:
{
lean_object* v_authority_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
v_authority_3666_ = lean_ctor_get(v_x_3665_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v_x_3665_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v_x_3665_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_authority_3666_);
lean_dec(v_x_3665_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set_tag(v___x_3668_, 1);
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_authority_3666_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
case 1:
{
lean_object* v_uri_3674_; lean_object* v_authority_3675_; 
v_uri_3674_ = lean_ctor_get(v_x_3665_, 0);
lean_inc_ref(v_uri_3674_);
lean_dec_ref_known(v_x_3665_, 1);
v_authority_3675_ = lean_ctor_get(v_uri_3674_, 1);
lean_inc(v_authority_3675_);
lean_dec_ref(v_uri_3674_);
return v_authority_3675_;
}
default: 
{
lean_object* v___x_3676_; 
lean_dec(v_x_3665_);
v___x_3676_ = lean_box(0);
return v___x_3676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__2(lean_object* v___f_3678_, lean_object* v___f_3679_, lean_object* v_x_3680_){
_start:
{
lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; 
switch(lean_obj_tag(v_x_3680_))
{
case 0:
{
lean_object* v_path_3687_; lean_object* v_query_3688_; lean_object* v___y_3690_; lean_object* v_segments_3693_; uint8_t v_absolute_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; size_t v_sz_3697_; size_t v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v_result_3701_; 
lean_dec_ref(v___f_3679_);
v_path_3687_ = lean_ctor_get(v_x_3680_, 0);
lean_inc_ref(v_path_3687_);
v_query_3688_ = lean_ctor_get(v_x_3680_, 1);
lean_inc(v_query_3688_);
lean_dec_ref_known(v_x_3680_, 2);
v_segments_3693_ = lean_ctor_get(v_path_3687_, 0);
lean_inc_ref(v_segments_3693_);
v_absolute_3694_ = lean_ctor_get_uint8(v_path_3687_, sizeof(void*)*1);
lean_dec_ref(v_path_3687_);
v___x_3695_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3696_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3697_ = lean_array_size(v_segments_3693_);
v___x_3698_ = ((size_t)0ULL);
v___x_3699_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3696_, v___f_3678_, v_sz_3697_, v___x_3698_, v_segments_3693_);
v___x_3700_ = lean_array_to_list(v___x_3699_);
v_result_3701_ = l_String_intercalate(v___x_3695_, v___x_3700_);
if (v_absolute_3694_ == 0)
{
v___y_3690_ = v_result_3701_;
goto v___jp_3689_;
}
else
{
lean_object* v___x_3702_; 
v___x_3702_ = lean_string_append(v___x_3695_, v_result_3701_);
lean_dec_ref(v_result_3701_);
v___y_3690_ = v___x_3702_;
goto v___jp_3689_;
}
v___jp_3689_:
{
lean_object* v_queryStr_3691_; lean_object* v___x_3692_; 
v_queryStr_3691_ = l_Std_Http_URI_Query_formatOption(v_query_3688_);
v___x_3692_ = lean_string_append(v___y_3690_, v_queryStr_3691_);
lean_dec_ref(v_queryStr_3691_);
return v___x_3692_;
}
}
case 1:
{
lean_object* v_uri_3703_; lean_object* v_scheme_3704_; lean_object* v_authority_3705_; lean_object* v_path_3706_; lean_object* v_query_3707_; lean_object* v_fragment_3708_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3731_; 
lean_dec_ref(v___f_3678_);
v_uri_3703_ = lean_ctor_get(v_x_3680_, 0);
lean_inc_ref(v_uri_3703_);
lean_dec_ref_known(v_x_3680_, 1);
v_scheme_3704_ = lean_ctor_get(v_uri_3703_, 0);
lean_inc_ref(v_scheme_3704_);
v_authority_3705_ = lean_ctor_get(v_uri_3703_, 1);
lean_inc(v_authority_3705_);
v_path_3706_ = lean_ctor_get(v_uri_3703_, 2);
lean_inc_ref(v_path_3706_);
v_query_3707_ = lean_ctor_get(v_uri_3703_, 3);
lean_inc(v_query_3707_);
v_fragment_3708_ = lean_ctor_get(v_uri_3703_, 4);
lean_inc(v_fragment_3708_);
lean_dec_ref(v_uri_3703_);
if (lean_obj_tag(v_authority_3705_) == 0)
{
lean_object* v___x_3742_; 
v___x_3742_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3731_ = v___x_3742_;
goto v___jp_3730_;
}
else
{
lean_object* v_val_3743_; lean_object* v_userInfo_3744_; lean_object* v_host_3745_; lean_object* v_port_3746_; lean_object* v___x_3747_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3766_; 
v_val_3743_ = lean_ctor_get(v_authority_3705_, 0);
lean_inc(v_val_3743_);
lean_dec_ref_known(v_authority_3705_, 1);
v_userInfo_3744_ = lean_ctor_get(v_val_3743_, 0);
lean_inc(v_userInfo_3744_);
v_host_3745_ = lean_ctor_get(v_val_3743_, 1);
lean_inc_ref(v_host_3745_);
v_port_3746_ = lean_ctor_get(v_val_3743_, 2);
lean_inc(v_port_3746_);
lean_dec(v_val_3743_);
v___x_3747_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3744_) == 0)
{
lean_object* v___x_3776_; 
v___x_3776_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3766_ = v___x_3776_;
goto v___jp_3765_;
}
else
{
lean_object* v_val_3777_; lean_object* v_password_3778_; 
v_val_3777_ = lean_ctor_get(v_userInfo_3744_, 0);
lean_inc(v_val_3777_);
lean_dec_ref_known(v_userInfo_3744_, 1);
v_password_3778_ = lean_ctor_get(v_val_3777_, 1);
if (lean_obj_tag(v_password_3778_) == 0)
{
lean_object* v_username_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
v_username_3779_ = lean_ctor_get(v_val_3777_, 0);
lean_inc_ref(v_username_3779_);
lean_dec(v_val_3777_);
v___x_3780_ = lean_string_from_utf8_unchecked(v_username_3779_);
v___x_3781_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3782_ = lean_string_append(v___x_3780_, v___x_3781_);
v___y_3766_ = v___x_3782_;
goto v___jp_3765_;
}
else
{
lean_object* v_username_3783_; lean_object* v_val_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
lean_inc_ref(v_password_3778_);
v_username_3783_ = lean_ctor_get(v_val_3777_, 0);
lean_inc_ref(v_username_3783_);
lean_dec(v_val_3777_);
v_val_3784_ = lean_ctor_get(v_password_3778_, 0);
lean_inc(v_val_3784_);
lean_dec_ref_known(v_password_3778_, 1);
v___x_3785_ = lean_string_from_utf8_unchecked(v_username_3783_);
v___x_3786_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3787_ = lean_string_append(v___x_3785_, v___x_3786_);
v___x_3788_ = lean_string_from_utf8_unchecked(v_val_3784_);
v___x_3789_ = lean_string_append(v___x_3787_, v___x_3788_);
lean_dec_ref(v___x_3788_);
v___x_3790_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3791_ = lean_string_append(v___x_3789_, v___x_3790_);
v___y_3766_ = v___x_3791_;
goto v___jp_3765_;
}
}
v___jp_3748_:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3752_ = lean_string_append(v___y_3749_, v___y_3750_);
lean_dec_ref(v___y_3750_);
v___x_3753_ = lean_string_append(v___x_3752_, v___y_3751_);
lean_dec_ref(v___y_3751_);
v___x_3754_ = lean_string_append(v___x_3747_, v___x_3753_);
lean_dec_ref(v___x_3753_);
v___y_3731_ = v___x_3754_;
goto v___jp_3730_;
}
v___jp_3755_:
{
switch(lean_obj_tag(v_port_3746_))
{
case 0:
{
lean_object* v___x_3758_; 
v___x_3758_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3749_ = v___y_3756_;
v___y_3750_ = v___y_3757_;
v___y_3751_ = v___x_3758_;
goto v___jp_3748_;
}
case 1:
{
lean_object* v___x_3759_; 
v___x_3759_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3749_ = v___y_3756_;
v___y_3750_ = v___y_3757_;
v___y_3751_ = v___x_3759_;
goto v___jp_3748_;
}
default: 
{
uint16_t v_port_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v_port_3760_ = lean_ctor_get_uint16(v_port_3746_, 0);
lean_dec_ref_known(v_port_3746_, 0);
v___x_3761_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3762_ = lean_uint16_to_nat(v_port_3760_);
v___x_3763_ = l_Nat_reprFast(v___x_3762_);
v___x_3764_ = lean_string_append(v___x_3761_, v___x_3763_);
lean_dec_ref(v___x_3763_);
v___y_3749_ = v___y_3756_;
v___y_3750_ = v___y_3757_;
v___y_3751_ = v___x_3764_;
goto v___jp_3748_;
}
}
}
v___jp_3765_:
{
switch(lean_obj_tag(v_host_3745_))
{
case 0:
{
lean_object* v_name_3767_; 
v_name_3767_ = lean_ctor_get(v_host_3745_, 0);
lean_inc_ref(v_name_3767_);
lean_dec_ref_known(v_host_3745_, 1);
v___y_3756_ = v___y_3766_;
v___y_3757_ = v_name_3767_;
goto v___jp_3755_;
}
case 1:
{
lean_object* v_ipv4_3768_; lean_object* v___x_3769_; 
v_ipv4_3768_ = lean_ctor_get(v_host_3745_, 0);
lean_inc_ref(v_ipv4_3768_);
lean_dec_ref_known(v_host_3745_, 1);
v___x_3769_ = lean_uv_ntop_v4(v_ipv4_3768_);
lean_dec_ref(v_ipv4_3768_);
v___y_3756_ = v___y_3766_;
v___y_3757_ = v___x_3769_;
goto v___jp_3755_;
}
default: 
{
lean_object* v_ipv6_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v_ipv6_3770_ = lean_ctor_get(v_host_3745_, 0);
lean_inc_ref(v_ipv6_3770_);
lean_dec_ref_known(v_host_3745_, 1);
v___x_3771_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3772_ = lean_uv_ntop_v6(v_ipv6_3770_);
lean_dec_ref(v_ipv6_3770_);
v___x_3773_ = lean_string_append(v___x_3771_, v___x_3772_);
lean_dec_ref(v___x_3772_);
v___x_3774_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3775_ = lean_string_append(v___x_3773_, v___x_3774_);
v___y_3756_ = v___y_3766_;
v___y_3757_ = v___x_3775_;
goto v___jp_3755_;
}
}
}
}
v___jp_3709_:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3714_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3715_ = lean_string_append(v_scheme_3704_, v___x_3714_);
v___x_3716_ = lean_string_append(v___x_3715_, v___y_3710_);
lean_dec_ref(v___y_3710_);
v___x_3717_ = lean_string_append(v___x_3716_, v___y_3711_);
lean_dec_ref(v___y_3711_);
v___x_3718_ = lean_string_append(v___x_3717_, v___y_3712_);
lean_dec_ref(v___y_3712_);
v___x_3719_ = lean_string_append(v___x_3718_, v___y_3713_);
lean_dec_ref(v___y_3713_);
return v___x_3719_;
}
v___jp_3720_:
{
lean_object* v_queryPart_3723_; 
v_queryPart_3723_ = l_Std_Http_URI_Query_formatOption(v_query_3707_);
if (lean_obj_tag(v_fragment_3708_) == 0)
{
lean_object* v___x_3724_; 
v___x_3724_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3710_ = v___y_3721_;
v___y_3711_ = v___y_3722_;
v___y_3712_ = v_queryPart_3723_;
v___y_3713_ = v___x_3724_;
goto v___jp_3709_;
}
else
{
lean_object* v_val_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v_val_3725_ = lean_ctor_get(v_fragment_3708_, 0);
lean_inc(v_val_3725_);
lean_dec_ref_known(v_fragment_3708_, 1);
v___x_3726_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3727_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3725_);
lean_dec(v_val_3725_);
v___x_3728_ = lean_string_from_utf8_unchecked(v___x_3727_);
v___x_3729_ = lean_string_append(v___x_3726_, v___x_3728_);
lean_dec_ref(v___x_3728_);
v___y_3710_ = v___y_3721_;
v___y_3711_ = v___y_3722_;
v___y_3712_ = v_queryPart_3723_;
v___y_3713_ = v___x_3729_;
goto v___jp_3709_;
}
}
v___jp_3730_:
{
lean_object* v_segments_3732_; uint8_t v_absolute_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; size_t v_sz_3736_; size_t v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v_result_3740_; 
v_segments_3732_ = lean_ctor_get(v_path_3706_, 0);
lean_inc_ref(v_segments_3732_);
v_absolute_3733_ = lean_ctor_get_uint8(v_path_3706_, sizeof(void*)*1);
lean_dec_ref(v_path_3706_);
v___x_3734_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3735_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3736_ = lean_array_size(v_segments_3732_);
v___x_3737_ = ((size_t)0ULL);
v___x_3738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3735_, v___f_3679_, v_sz_3736_, v___x_3737_, v_segments_3732_);
v___x_3739_ = lean_array_to_list(v___x_3738_);
v_result_3740_ = l_String_intercalate(v___x_3734_, v___x_3739_);
if (v_absolute_3733_ == 0)
{
v___y_3721_ = v___y_3731_;
v___y_3722_ = v_result_3740_;
goto v___jp_3720_;
}
else
{
lean_object* v___x_3741_; 
v___x_3741_ = lean_string_append(v___x_3734_, v_result_3740_);
lean_dec_ref(v_result_3740_);
v___y_3721_ = v___y_3731_;
v___y_3722_ = v___x_3741_;
goto v___jp_3720_;
}
}
}
case 2:
{
lean_object* v_authority_3792_; lean_object* v_userInfo_3793_; lean_object* v_host_3794_; lean_object* v_port_3795_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3807_; 
lean_dec_ref(v___f_3679_);
lean_dec_ref(v___f_3678_);
v_authority_3792_ = lean_ctor_get(v_x_3680_, 0);
lean_inc_ref(v_authority_3792_);
lean_dec_ref_known(v_x_3680_, 1);
v_userInfo_3793_ = lean_ctor_get(v_authority_3792_, 0);
lean_inc(v_userInfo_3793_);
v_host_3794_ = lean_ctor_get(v_authority_3792_, 1);
lean_inc_ref(v_host_3794_);
v_port_3795_ = lean_ctor_get(v_authority_3792_, 2);
lean_inc(v_port_3795_);
lean_dec_ref(v_authority_3792_);
if (lean_obj_tag(v_userInfo_3793_) == 0)
{
lean_object* v___x_3817_; 
v___x_3817_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3807_ = v___x_3817_;
goto v___jp_3806_;
}
else
{
lean_object* v_val_3818_; lean_object* v_password_3819_; 
v_val_3818_ = lean_ctor_get(v_userInfo_3793_, 0);
lean_inc(v_val_3818_);
lean_dec_ref_known(v_userInfo_3793_, 1);
v_password_3819_ = lean_ctor_get(v_val_3818_, 1);
if (lean_obj_tag(v_password_3819_) == 0)
{
lean_object* v_username_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v_username_3820_ = lean_ctor_get(v_val_3818_, 0);
lean_inc_ref(v_username_3820_);
lean_dec(v_val_3818_);
v___x_3821_ = lean_string_from_utf8_unchecked(v_username_3820_);
v___x_3822_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3823_ = lean_string_append(v___x_3821_, v___x_3822_);
v___y_3807_ = v___x_3823_;
goto v___jp_3806_;
}
else
{
lean_object* v_username_3824_; lean_object* v_val_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
lean_inc_ref(v_password_3819_);
v_username_3824_ = lean_ctor_get(v_val_3818_, 0);
lean_inc_ref(v_username_3824_);
lean_dec(v_val_3818_);
v_val_3825_ = lean_ctor_get(v_password_3819_, 0);
lean_inc(v_val_3825_);
lean_dec_ref_known(v_password_3819_, 1);
v___x_3826_ = lean_string_from_utf8_unchecked(v_username_3824_);
v___x_3827_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3828_ = lean_string_append(v___x_3826_, v___x_3827_);
v___x_3829_ = lean_string_from_utf8_unchecked(v_val_3825_);
v___x_3830_ = lean_string_append(v___x_3828_, v___x_3829_);
lean_dec_ref(v___x_3829_);
v___x_3831_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3832_ = lean_string_append(v___x_3830_, v___x_3831_);
v___y_3807_ = v___x_3832_;
goto v___jp_3806_;
}
}
v___jp_3796_:
{
switch(lean_obj_tag(v_port_3795_))
{
case 0:
{
lean_object* v___x_3799_; 
v___x_3799_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3682_ = v___y_3798_;
v___y_3683_ = v___y_3797_;
v___y_3684_ = v___x_3799_;
goto v___jp_3681_;
}
case 1:
{
lean_object* v___x_3800_; 
v___x_3800_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3682_ = v___y_3798_;
v___y_3683_ = v___y_3797_;
v___y_3684_ = v___x_3800_;
goto v___jp_3681_;
}
default: 
{
uint16_t v_port_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
v_port_3801_ = lean_ctor_get_uint16(v_port_3795_, 0);
lean_dec_ref_known(v_port_3795_, 0);
v___x_3802_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3803_ = lean_uint16_to_nat(v_port_3801_);
v___x_3804_ = l_Nat_reprFast(v___x_3803_);
v___x_3805_ = lean_string_append(v___x_3802_, v___x_3804_);
lean_dec_ref(v___x_3804_);
v___y_3682_ = v___y_3798_;
v___y_3683_ = v___y_3797_;
v___y_3684_ = v___x_3805_;
goto v___jp_3681_;
}
}
}
v___jp_3806_:
{
switch(lean_obj_tag(v_host_3794_))
{
case 0:
{
lean_object* v_name_3808_; 
v_name_3808_ = lean_ctor_get(v_host_3794_, 0);
lean_inc_ref(v_name_3808_);
lean_dec_ref_known(v_host_3794_, 1);
v___y_3797_ = v___y_3807_;
v___y_3798_ = v_name_3808_;
goto v___jp_3796_;
}
case 1:
{
lean_object* v_ipv4_3809_; lean_object* v___x_3810_; 
v_ipv4_3809_ = lean_ctor_get(v_host_3794_, 0);
lean_inc_ref(v_ipv4_3809_);
lean_dec_ref_known(v_host_3794_, 1);
v___x_3810_ = lean_uv_ntop_v4(v_ipv4_3809_);
lean_dec_ref(v_ipv4_3809_);
v___y_3797_ = v___y_3807_;
v___y_3798_ = v___x_3810_;
goto v___jp_3796_;
}
default: 
{
lean_object* v_ipv6_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v_ipv6_3811_ = lean_ctor_get(v_host_3794_, 0);
lean_inc_ref(v_ipv6_3811_);
lean_dec_ref_known(v_host_3794_, 1);
v___x_3812_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3813_ = lean_uv_ntop_v6(v_ipv6_3811_);
lean_dec_ref(v_ipv6_3811_);
v___x_3814_ = lean_string_append(v___x_3812_, v___x_3813_);
lean_dec_ref(v___x_3813_);
v___x_3815_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3816_ = lean_string_append(v___x_3814_, v___x_3815_);
v___y_3797_ = v___y_3807_;
v___y_3798_ = v___x_3816_;
goto v___jp_3796_;
}
}
}
}
default: 
{
lean_object* v___x_3833_; 
lean_dec_ref(v___f_3679_);
lean_dec_ref(v___f_3678_);
v___x_3833_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__2___closed__0));
return v___x_3833_;
}
}
v___jp_3681_:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3685_ = lean_string_append(v___y_3683_, v___y_3682_);
lean_dec_ref(v___y_3682_);
v___x_3686_ = lean_string_append(v___x_3685_, v___y_3684_);
lean_dec_ref(v___y_3684_);
return v___x_3686_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__2(lean_object* v___f_3837_, lean_object* v___f_3838_, lean_object* v_buffer_3839_, lean_object* v_target_3840_){
_start:
{
lean_object* v___y_3842_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; 
switch(lean_obj_tag(v_target_3840_))
{
case 0:
{
lean_object* v_path_3862_; lean_object* v_query_3863_; lean_object* v___y_3865_; lean_object* v_segments_3868_; uint8_t v_absolute_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; size_t v_sz_3872_; size_t v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v_result_3876_; 
lean_dec_ref(v___f_3838_);
v_path_3862_ = lean_ctor_get(v_target_3840_, 0);
lean_inc_ref(v_path_3862_);
v_query_3863_ = lean_ctor_get(v_target_3840_, 1);
lean_inc(v_query_3863_);
lean_dec_ref_known(v_target_3840_, 2);
v_segments_3868_ = lean_ctor_get(v_path_3862_, 0);
lean_inc_ref(v_segments_3868_);
v_absolute_3869_ = lean_ctor_get_uint8(v_path_3862_, sizeof(void*)*1);
lean_dec_ref(v_path_3862_);
v___x_3870_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3871_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3872_ = lean_array_size(v_segments_3868_);
v___x_3873_ = ((size_t)0ULL);
v___x_3874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3871_, v___f_3837_, v_sz_3872_, v___x_3873_, v_segments_3868_);
v___x_3875_ = lean_array_to_list(v___x_3874_);
v_result_3876_ = l_String_intercalate(v___x_3870_, v___x_3875_);
if (v_absolute_3869_ == 0)
{
v___y_3865_ = v_result_3876_;
goto v___jp_3864_;
}
else
{
lean_object* v___x_3877_; 
v___x_3877_ = lean_string_append(v___x_3870_, v_result_3876_);
lean_dec_ref(v_result_3876_);
v___y_3865_ = v___x_3877_;
goto v___jp_3864_;
}
v___jp_3864_:
{
lean_object* v_queryStr_3866_; lean_object* v___x_3867_; 
v_queryStr_3866_ = l_Std_Http_URI_Query_formatOption(v_query_3863_);
v___x_3867_ = lean_string_append(v___y_3865_, v_queryStr_3866_);
lean_dec_ref(v_queryStr_3866_);
v___y_3842_ = v___x_3867_;
goto v___jp_3841_;
}
}
case 1:
{
lean_object* v_uri_3878_; lean_object* v_scheme_3879_; lean_object* v_authority_3880_; lean_object* v_path_3881_; lean_object* v_query_3882_; lean_object* v_fragment_3883_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3906_; 
lean_dec_ref(v___f_3837_);
v_uri_3878_ = lean_ctor_get(v_target_3840_, 0);
lean_inc_ref(v_uri_3878_);
lean_dec_ref_known(v_target_3840_, 1);
v_scheme_3879_ = lean_ctor_get(v_uri_3878_, 0);
lean_inc_ref(v_scheme_3879_);
v_authority_3880_ = lean_ctor_get(v_uri_3878_, 1);
lean_inc(v_authority_3880_);
v_path_3881_ = lean_ctor_get(v_uri_3878_, 2);
lean_inc_ref(v_path_3881_);
v_query_3882_ = lean_ctor_get(v_uri_3878_, 3);
lean_inc(v_query_3882_);
v_fragment_3883_ = lean_ctor_get(v_uri_3878_, 4);
lean_inc(v_fragment_3883_);
lean_dec_ref(v_uri_3878_);
if (lean_obj_tag(v_authority_3880_) == 0)
{
lean_object* v___x_3917_; 
v___x_3917_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3906_ = v___x_3917_;
goto v___jp_3905_;
}
else
{
lean_object* v_val_3918_; lean_object* v_userInfo_3919_; lean_object* v_host_3920_; lean_object* v_port_3921_; lean_object* v___x_3922_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3941_; 
v_val_3918_ = lean_ctor_get(v_authority_3880_, 0);
lean_inc(v_val_3918_);
lean_dec_ref_known(v_authority_3880_, 1);
v_userInfo_3919_ = lean_ctor_get(v_val_3918_, 0);
lean_inc(v_userInfo_3919_);
v_host_3920_ = lean_ctor_get(v_val_3918_, 1);
lean_inc_ref(v_host_3920_);
v_port_3921_ = lean_ctor_get(v_val_3918_, 2);
lean_inc(v_port_3921_);
lean_dec(v_val_3918_);
v___x_3922_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3919_) == 0)
{
lean_object* v___x_3951_; 
v___x_3951_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3941_ = v___x_3951_;
goto v___jp_3940_;
}
else
{
lean_object* v_val_3952_; lean_object* v_password_3953_; 
v_val_3952_ = lean_ctor_get(v_userInfo_3919_, 0);
lean_inc(v_val_3952_);
lean_dec_ref_known(v_userInfo_3919_, 1);
v_password_3953_ = lean_ctor_get(v_val_3952_, 1);
if (lean_obj_tag(v_password_3953_) == 0)
{
lean_object* v_username_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v_username_3954_ = lean_ctor_get(v_val_3952_, 0);
lean_inc_ref(v_username_3954_);
lean_dec(v_val_3952_);
v___x_3955_ = lean_string_from_utf8_unchecked(v_username_3954_);
v___x_3956_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3957_ = lean_string_append(v___x_3955_, v___x_3956_);
v___y_3941_ = v___x_3957_;
goto v___jp_3940_;
}
else
{
lean_object* v_username_3958_; lean_object* v_val_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
lean_inc_ref(v_password_3953_);
v_username_3958_ = lean_ctor_get(v_val_3952_, 0);
lean_inc_ref(v_username_3958_);
lean_dec(v_val_3952_);
v_val_3959_ = lean_ctor_get(v_password_3953_, 0);
lean_inc(v_val_3959_);
lean_dec_ref_known(v_password_3953_, 1);
v___x_3960_ = lean_string_from_utf8_unchecked(v_username_3958_);
v___x_3961_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3962_ = lean_string_append(v___x_3960_, v___x_3961_);
v___x_3963_ = lean_string_from_utf8_unchecked(v_val_3959_);
v___x_3964_ = lean_string_append(v___x_3962_, v___x_3963_);
lean_dec_ref(v___x_3963_);
v___x_3965_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3966_ = lean_string_append(v___x_3964_, v___x_3965_);
v___y_3941_ = v___x_3966_;
goto v___jp_3940_;
}
}
v___jp_3923_:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3927_ = lean_string_append(v___y_3925_, v___y_3924_);
lean_dec_ref(v___y_3924_);
v___x_3928_ = lean_string_append(v___x_3927_, v___y_3926_);
lean_dec_ref(v___y_3926_);
v___x_3929_ = lean_string_append(v___x_3922_, v___x_3928_);
lean_dec_ref(v___x_3928_);
v___y_3906_ = v___x_3929_;
goto v___jp_3905_;
}
v___jp_3930_:
{
switch(lean_obj_tag(v_port_3921_))
{
case 0:
{
lean_object* v___x_3933_; 
v___x_3933_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3924_ = v___y_3932_;
v___y_3925_ = v___y_3931_;
v___y_3926_ = v___x_3933_;
goto v___jp_3923_;
}
case 1:
{
lean_object* v___x_3934_; 
v___x_3934_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3924_ = v___y_3932_;
v___y_3925_ = v___y_3931_;
v___y_3926_ = v___x_3934_;
goto v___jp_3923_;
}
default: 
{
uint16_t v_port_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v_port_3935_ = lean_ctor_get_uint16(v_port_3921_, 0);
lean_dec_ref_known(v_port_3921_, 0);
v___x_3936_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3937_ = lean_uint16_to_nat(v_port_3935_);
v___x_3938_ = l_Nat_reprFast(v___x_3937_);
v___x_3939_ = lean_string_append(v___x_3936_, v___x_3938_);
lean_dec_ref(v___x_3938_);
v___y_3924_ = v___y_3932_;
v___y_3925_ = v___y_3931_;
v___y_3926_ = v___x_3939_;
goto v___jp_3923_;
}
}
}
v___jp_3940_:
{
switch(lean_obj_tag(v_host_3920_))
{
case 0:
{
lean_object* v_name_3942_; 
v_name_3942_ = lean_ctor_get(v_host_3920_, 0);
lean_inc_ref(v_name_3942_);
lean_dec_ref_known(v_host_3920_, 1);
v___y_3931_ = v___y_3941_;
v___y_3932_ = v_name_3942_;
goto v___jp_3930_;
}
case 1:
{
lean_object* v_ipv4_3943_; lean_object* v___x_3944_; 
v_ipv4_3943_ = lean_ctor_get(v_host_3920_, 0);
lean_inc_ref(v_ipv4_3943_);
lean_dec_ref_known(v_host_3920_, 1);
v___x_3944_ = lean_uv_ntop_v4(v_ipv4_3943_);
lean_dec_ref(v_ipv4_3943_);
v___y_3931_ = v___y_3941_;
v___y_3932_ = v___x_3944_;
goto v___jp_3930_;
}
default: 
{
lean_object* v_ipv6_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v_ipv6_3945_ = lean_ctor_get(v_host_3920_, 0);
lean_inc_ref(v_ipv6_3945_);
lean_dec_ref_known(v_host_3920_, 1);
v___x_3946_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3947_ = lean_uv_ntop_v6(v_ipv6_3945_);
lean_dec_ref(v_ipv6_3945_);
v___x_3948_ = lean_string_append(v___x_3946_, v___x_3947_);
lean_dec_ref(v___x_3947_);
v___x_3949_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3950_ = lean_string_append(v___x_3948_, v___x_3949_);
v___y_3931_ = v___y_3941_;
v___y_3932_ = v___x_3950_;
goto v___jp_3930_;
}
}
}
}
v___jp_3884_:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3889_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3890_ = lean_string_append(v_scheme_3879_, v___x_3889_);
v___x_3891_ = lean_string_append(v___x_3890_, v___y_3886_);
lean_dec_ref(v___y_3886_);
v___x_3892_ = lean_string_append(v___x_3891_, v___y_3887_);
lean_dec_ref(v___y_3887_);
v___x_3893_ = lean_string_append(v___x_3892_, v___y_3885_);
lean_dec_ref(v___y_3885_);
v___x_3894_ = lean_string_append(v___x_3893_, v___y_3888_);
lean_dec_ref(v___y_3888_);
v___y_3842_ = v___x_3894_;
goto v___jp_3841_;
}
v___jp_3895_:
{
lean_object* v_queryPart_3898_; 
v_queryPart_3898_ = l_Std_Http_URI_Query_formatOption(v_query_3882_);
if (lean_obj_tag(v_fragment_3883_) == 0)
{
lean_object* v___x_3899_; 
v___x_3899_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3885_ = v_queryPart_3898_;
v___y_3886_ = v___y_3896_;
v___y_3887_ = v___y_3897_;
v___y_3888_ = v___x_3899_;
goto v___jp_3884_;
}
else
{
lean_object* v_val_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v_val_3900_ = lean_ctor_get(v_fragment_3883_, 0);
lean_inc(v_val_3900_);
lean_dec_ref_known(v_fragment_3883_, 1);
v___x_3901_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3902_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3900_);
lean_dec(v_val_3900_);
v___x_3903_ = lean_string_from_utf8_unchecked(v___x_3902_);
v___x_3904_ = lean_string_append(v___x_3901_, v___x_3903_);
lean_dec_ref(v___x_3903_);
v___y_3885_ = v_queryPart_3898_;
v___y_3886_ = v___y_3896_;
v___y_3887_ = v___y_3897_;
v___y_3888_ = v___x_3904_;
goto v___jp_3884_;
}
}
v___jp_3905_:
{
lean_object* v_segments_3907_; uint8_t v_absolute_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; size_t v_sz_3911_; size_t v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v_result_3915_; 
v_segments_3907_ = lean_ctor_get(v_path_3881_, 0);
lean_inc_ref(v_segments_3907_);
v_absolute_3908_ = lean_ctor_get_uint8(v_path_3881_, sizeof(void*)*1);
lean_dec_ref(v_path_3881_);
v___x_3909_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3910_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3911_ = lean_array_size(v_segments_3907_);
v___x_3912_ = ((size_t)0ULL);
v___x_3913_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3910_, v___f_3838_, v_sz_3911_, v___x_3912_, v_segments_3907_);
v___x_3914_ = lean_array_to_list(v___x_3913_);
v_result_3915_ = l_String_intercalate(v___x_3909_, v___x_3914_);
if (v_absolute_3908_ == 0)
{
v___y_3896_ = v___y_3906_;
v___y_3897_ = v_result_3915_;
goto v___jp_3895_;
}
else
{
lean_object* v___x_3916_; 
v___x_3916_ = lean_string_append(v___x_3909_, v_result_3915_);
lean_dec_ref(v_result_3915_);
v___y_3896_ = v___y_3906_;
v___y_3897_ = v___x_3916_;
goto v___jp_3895_;
}
}
}
case 2:
{
lean_object* v_authority_3967_; lean_object* v_userInfo_3968_; lean_object* v_host_3969_; lean_object* v_port_3970_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3982_; 
lean_dec_ref(v___f_3838_);
lean_dec_ref(v___f_3837_);
v_authority_3967_ = lean_ctor_get(v_target_3840_, 0);
lean_inc_ref(v_authority_3967_);
lean_dec_ref_known(v_target_3840_, 1);
v_userInfo_3968_ = lean_ctor_get(v_authority_3967_, 0);
lean_inc(v_userInfo_3968_);
v_host_3969_ = lean_ctor_get(v_authority_3967_, 1);
lean_inc_ref(v_host_3969_);
v_port_3970_ = lean_ctor_get(v_authority_3967_, 2);
lean_inc(v_port_3970_);
lean_dec_ref(v_authority_3967_);
if (lean_obj_tag(v_userInfo_3968_) == 0)
{
lean_object* v___x_3992_; 
v___x_3992_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3982_ = v___x_3992_;
goto v___jp_3981_;
}
else
{
lean_object* v_val_3993_; lean_object* v_password_3994_; 
v_val_3993_ = lean_ctor_get(v_userInfo_3968_, 0);
lean_inc(v_val_3993_);
lean_dec_ref_known(v_userInfo_3968_, 1);
v_password_3994_ = lean_ctor_get(v_val_3993_, 1);
if (lean_obj_tag(v_password_3994_) == 0)
{
lean_object* v_username_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v_username_3995_ = lean_ctor_get(v_val_3993_, 0);
lean_inc_ref(v_username_3995_);
lean_dec(v_val_3993_);
v___x_3996_ = lean_string_from_utf8_unchecked(v_username_3995_);
v___x_3997_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3998_ = lean_string_append(v___x_3996_, v___x_3997_);
v___y_3982_ = v___x_3998_;
goto v___jp_3981_;
}
else
{
lean_object* v_username_3999_; lean_object* v_val_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
lean_inc_ref(v_password_3994_);
v_username_3999_ = lean_ctor_get(v_val_3993_, 0);
lean_inc_ref(v_username_3999_);
lean_dec(v_val_3993_);
v_val_4000_ = lean_ctor_get(v_password_3994_, 0);
lean_inc(v_val_4000_);
lean_dec_ref_known(v_password_3994_, 1);
v___x_4001_ = lean_string_from_utf8_unchecked(v_username_3999_);
v___x_4002_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4003_ = lean_string_append(v___x_4001_, v___x_4002_);
v___x_4004_ = lean_string_from_utf8_unchecked(v_val_4000_);
v___x_4005_ = lean_string_append(v___x_4003_, v___x_4004_);
lean_dec_ref(v___x_4004_);
v___x_4006_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4007_ = lean_string_append(v___x_4005_, v___x_4006_);
v___y_3982_ = v___x_4007_;
goto v___jp_3981_;
}
}
v___jp_3971_:
{
switch(lean_obj_tag(v_port_3970_))
{
case 0:
{
lean_object* v___x_3974_; 
v___x_3974_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3857_ = v___y_3973_;
v___y_3858_ = v___y_3972_;
v___y_3859_ = v___x_3974_;
goto v___jp_3856_;
}
case 1:
{
lean_object* v___x_3975_; 
v___x_3975_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3857_ = v___y_3973_;
v___y_3858_ = v___y_3972_;
v___y_3859_ = v___x_3975_;
goto v___jp_3856_;
}
default: 
{
uint16_t v_port_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v_port_3976_ = lean_ctor_get_uint16(v_port_3970_, 0);
lean_dec_ref_known(v_port_3970_, 0);
v___x_3977_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3978_ = lean_uint16_to_nat(v_port_3976_);
v___x_3979_ = l_Nat_reprFast(v___x_3978_);
v___x_3980_ = lean_string_append(v___x_3977_, v___x_3979_);
lean_dec_ref(v___x_3979_);
v___y_3857_ = v___y_3973_;
v___y_3858_ = v___y_3972_;
v___y_3859_ = v___x_3980_;
goto v___jp_3856_;
}
}
}
v___jp_3981_:
{
switch(lean_obj_tag(v_host_3969_))
{
case 0:
{
lean_object* v_name_3983_; 
v_name_3983_ = lean_ctor_get(v_host_3969_, 0);
lean_inc_ref(v_name_3983_);
lean_dec_ref_known(v_host_3969_, 1);
v___y_3972_ = v___y_3982_;
v___y_3973_ = v_name_3983_;
goto v___jp_3971_;
}
case 1:
{
lean_object* v_ipv4_3984_; lean_object* v___x_3985_; 
v_ipv4_3984_ = lean_ctor_get(v_host_3969_, 0);
lean_inc_ref(v_ipv4_3984_);
lean_dec_ref_known(v_host_3969_, 1);
v___x_3985_ = lean_uv_ntop_v4(v_ipv4_3984_);
lean_dec_ref(v_ipv4_3984_);
v___y_3972_ = v___y_3982_;
v___y_3973_ = v___x_3985_;
goto v___jp_3971_;
}
default: 
{
lean_object* v_ipv6_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v_ipv6_3986_ = lean_ctor_get(v_host_3969_, 0);
lean_inc_ref(v_ipv6_3986_);
lean_dec_ref_known(v_host_3969_, 1);
v___x_3987_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3988_ = lean_uv_ntop_v6(v_ipv6_3986_);
lean_dec_ref(v_ipv6_3986_);
v___x_3989_ = lean_string_append(v___x_3987_, v___x_3988_);
lean_dec_ref(v___x_3988_);
v___x_3990_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3991_ = lean_string_append(v___x_3989_, v___x_3990_);
v___y_3972_ = v___y_3982_;
v___y_3973_ = v___x_3991_;
goto v___jp_3971_;
}
}
}
}
default: 
{
lean_object* v___x_4008_; 
lean_dec_ref(v___f_3838_);
lean_dec_ref(v___f_3837_);
v___x_4008_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__2___closed__0));
v___y_3842_ = v___x_4008_;
goto v___jp_3841_;
}
}
v___jp_3841_:
{
lean_object* v_data_3843_; lean_object* v_size_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3855_; 
v_data_3843_ = lean_ctor_get(v_buffer_3839_, 0);
v_size_3844_ = lean_ctor_get(v_buffer_3839_, 1);
v_isSharedCheck_3855_ = !lean_is_exclusive(v_buffer_3839_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3846_ = v_buffer_3839_;
v_isShared_3847_ = v_isSharedCheck_3855_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_size_3844_);
lean_inc(v_data_3843_);
lean_dec(v_buffer_3839_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3855_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3853_; 
v___x_3848_ = lean_string_to_utf8(v___y_3842_);
lean_dec_ref(v___y_3842_);
lean_inc_ref(v___x_3848_);
v___x_3849_ = lean_array_push(v_data_3843_, v___x_3848_);
v___x_3850_ = lean_byte_array_size(v___x_3848_);
lean_dec_ref(v___x_3848_);
v___x_3851_ = lean_nat_add(v_size_3844_, v___x_3850_);
lean_dec(v_size_3844_);
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 1, v___x_3851_);
lean_ctor_set(v___x_3846_, 0, v___x_3849_);
v___x_3853_ = v___x_3846_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3849_);
lean_ctor_set(v_reuseFailAlloc_3854_, 1, v___x_3851_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
v___jp_3856_:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3860_ = lean_string_append(v___y_3858_, v___y_3857_);
lean_dec_ref(v___y_3857_);
v___x_3861_ = lean_string_append(v___x_3860_, v___y_3859_);
lean_dec_ref(v___y_3859_);
v___y_3842_ = v___x_3861_;
goto v___jp_3841_;
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
