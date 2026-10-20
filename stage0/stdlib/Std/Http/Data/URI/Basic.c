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
lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object*);
lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object*);
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
v___x_123_ = lean_unsigned_to_nat(84u);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings(lean_object* v_username_282_, lean_object* v_password_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_282_);
if (lean_obj_tag(v_password_283_) == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_box(0);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
return v___x_286_;
}
else
{
lean_object* v_val_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_296_; 
v_val_287_ = lean_ctor_get(v_password_283_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v_password_283_);
if (v_isSharedCheck_296_ == 0)
{
v___x_289_ = v_password_283_;
v_isShared_290_ = v_isSharedCheck_296_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_val_287_);
lean_dec(v_password_283_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_296_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_291_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_287_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_291_);
v___x_293_ = v___x_289_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_295_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_294_; 
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_284_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
return v___x_294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f(lean_object* v_ui_297_){
_start:
{
lean_object* v_username_298_; lean_object* v___x_299_; 
v_username_298_ = lean_ctor_get(v_ui_297_, 0);
v___x_299_ = l_Std_Http_URI_EncodedUserInfo_decode(v_username_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f___boxed(lean_object* v_ui_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Std_Http_URI_UserInfo_username_x3f(v_ui_300_);
lean_dec_ref(v_ui_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f(lean_object* v_ui_302_){
_start:
{
lean_object* v_password_303_; 
v_password_303_ = lean_ctor_get(v_ui_302_, 1);
if (lean_obj_tag(v_password_303_) == 0)
{
lean_object* v___x_304_; 
v___x_304_ = lean_box(0);
return v___x_304_;
}
else
{
lean_object* v_val_305_; lean_object* v___x_306_; 
v_val_305_ = lean_ctor_get(v_password_303_, 0);
v___x_306_ = l_Std_Http_URI_EncodedUserInfo_decode(v_val_305_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f___boxed(lean_object* v_ui_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Std_Http_URI_UserInfo_password_x3f(v_ui_307_);
lean_dec_ref(v_ui_307_);
return v_res_308_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(lean_object* v_x_309_){
_start:
{
if (lean_obj_tag(v_x_309_) == 0)
{
uint8_t v___x_310_; 
v___x_310_ = 1;
return v___x_310_;
}
else
{
lean_object* v_head_311_; lean_object* v_tail_312_; uint32_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v_head_311_ = lean_ctor_get(v_x_309_, 0);
v_tail_312_ = lean_ctor_get(v_x_309_, 1);
v___x_334_ = lean_unbox_uint32(v_head_311_);
v___x_335_ = lean_uint32_to_nat(v___x_334_);
v___x_336_ = lean_unsigned_to_nat(128u);
v___x_337_ = lean_nat_dec_lt(v___x_335_, v___x_336_);
lean_dec(v___x_335_);
if (v___x_337_ == 0)
{
goto v___jp_313_;
}
else
{
uint32_t v___x_338_; uint32_t v___x_339_; uint8_t v___x_340_; 
v___x_338_ = 48;
v___x_339_ = lean_unbox_uint32(v_head_311_);
v___x_340_ = lean_uint32_dec_le(v___x_338_, v___x_339_);
if (v___x_340_ == 0)
{
goto v___jp_326_;
}
else
{
uint32_t v___x_341_; uint32_t v___x_342_; uint8_t v___x_343_; 
v___x_341_ = 57;
v___x_342_ = lean_unbox_uint32(v_head_311_);
v___x_343_ = lean_uint32_dec_le(v___x_342_, v___x_341_);
if (v___x_343_ == 0)
{
goto v___jp_326_;
}
else
{
v_x_309_ = v_tail_312_;
goto _start;
}
}
}
v___jp_313_:
{
uint32_t v___x_314_; uint32_t v___x_315_; uint8_t v___x_316_; 
v___x_314_ = 45;
v___x_315_ = lean_unbox_uint32(v_head_311_);
v___x_316_ = lean_uint32_dec_eq(v___x_315_, v___x_314_);
if (v___x_316_ == 0)
{
return v___x_316_;
}
else
{
v_x_309_ = v_tail_312_;
goto _start;
}
}
v___jp_318_:
{
uint32_t v___x_319_; uint32_t v___x_320_; uint8_t v___x_321_; 
v___x_319_ = 97;
v___x_320_ = lean_unbox_uint32(v_head_311_);
v___x_321_ = lean_uint32_dec_le(v___x_319_, v___x_320_);
if (v___x_321_ == 0)
{
goto v___jp_313_;
}
else
{
uint32_t v___x_322_; uint32_t v___x_323_; uint8_t v___x_324_; 
v___x_322_ = 122;
v___x_323_ = lean_unbox_uint32(v_head_311_);
v___x_324_ = lean_uint32_dec_le(v___x_323_, v___x_322_);
if (v___x_324_ == 0)
{
goto v___jp_313_;
}
else
{
v_x_309_ = v_tail_312_;
goto _start;
}
}
}
v___jp_326_:
{
uint32_t v___x_327_; uint32_t v___x_328_; uint8_t v___x_329_; 
v___x_327_ = 65;
v___x_328_ = lean_unbox_uint32(v_head_311_);
v___x_329_ = lean_uint32_dec_le(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
goto v___jp_318_;
}
else
{
uint32_t v___x_330_; uint32_t v___x_331_; uint8_t v___x_332_; 
v___x_330_ = 90;
v___x_331_ = lean_unbox_uint32(v_head_311_);
v___x_332_ = lean_uint32_dec_le(v___x_331_, v___x_330_);
if (v___x_332_ == 0)
{
goto v___jp_318_;
}
else
{
v_x_309_ = v_tail_312_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0___boxed(lean_object* v_x_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v_x_345_);
lean_dec(v_x_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object* v_s_348_){
_start:
{
uint32_t v___y_350_; uint32_t v___y_356_; lean_object* v_chars_361_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v_chars_361_ = l_String_toListImpl(v_s_348_);
v___x_378_ = l_List_lengthTR___redArg(v_chars_361_);
v___x_379_ = lean_unsigned_to_nat(63u);
v___x_380_ = lean_nat_dec_le(v___x_378_, v___x_379_);
lean_dec(v___x_378_);
if (v___x_380_ == 0)
{
lean_dec(v_chars_361_);
return v___x_380_;
}
else
{
uint8_t v___x_381_; 
v___x_381_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v_chars_361_);
if (v___x_381_ == 0)
{
lean_dec(v_chars_361_);
return v___x_381_;
}
else
{
lean_object* v___x_382_; 
v___x_382_ = l_List_head_x3f___redArg(v_chars_361_);
if (lean_obj_tag(v___x_382_) == 0)
{
uint8_t v___x_383_; 
lean_dec(v_chars_361_);
v___x_383_ = 0;
return v___x_383_;
}
else
{
lean_object* v_val_384_; uint32_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_val_384_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_val_384_);
lean_dec_ref_known(v___x_382_, 1);
v___x_399_ = lean_unbox_uint32(v_val_384_);
v___x_400_ = lean_uint32_to_nat(v___x_399_);
v___x_401_ = lean_unsigned_to_nat(128u);
v___x_402_ = lean_nat_dec_lt(v___x_400_, v___x_401_);
lean_dec(v___x_400_);
if (v___x_402_ == 0)
{
lean_dec(v_val_384_);
lean_dec(v_chars_361_);
return v___x_402_;
}
else
{
uint32_t v___x_403_; uint32_t v___x_404_; uint8_t v___x_405_; 
v___x_403_ = 48;
v___x_404_ = lean_unbox_uint32(v_val_384_);
v___x_405_ = lean_uint32_dec_le(v___x_403_, v___x_404_);
if (v___x_405_ == 0)
{
goto v___jp_392_;
}
else
{
uint32_t v___x_406_; uint32_t v___x_407_; uint8_t v___x_408_; 
v___x_406_ = 57;
v___x_407_ = lean_unbox_uint32(v_val_384_);
v___x_408_ = lean_uint32_dec_le(v___x_407_, v___x_406_);
if (v___x_408_ == 0)
{
goto v___jp_392_;
}
else
{
lean_dec(v_val_384_);
goto v___jp_362_;
}
}
}
v___jp_385_:
{
uint32_t v___x_386_; uint32_t v___x_387_; uint8_t v___x_388_; 
v___x_386_ = 97;
v___x_387_ = lean_unbox_uint32(v_val_384_);
v___x_388_ = lean_uint32_dec_le(v___x_386_, v___x_387_);
if (v___x_388_ == 0)
{
lean_dec(v_val_384_);
lean_dec(v_chars_361_);
return v___x_388_;
}
else
{
uint32_t v___x_389_; uint32_t v___x_390_; uint8_t v___x_391_; 
v___x_389_ = 122;
v___x_390_ = lean_unbox_uint32(v_val_384_);
lean_dec(v_val_384_);
v___x_391_ = lean_uint32_dec_le(v___x_390_, v___x_389_);
if (v___x_391_ == 0)
{
lean_dec(v_chars_361_);
return v___x_391_;
}
else
{
goto v___jp_362_;
}
}
}
v___jp_392_:
{
uint32_t v___x_393_; uint32_t v___x_394_; uint8_t v___x_395_; 
v___x_393_ = 65;
v___x_394_ = lean_unbox_uint32(v_val_384_);
v___x_395_ = lean_uint32_dec_le(v___x_393_, v___x_394_);
if (v___x_395_ == 0)
{
goto v___jp_385_;
}
else
{
uint32_t v___x_396_; uint32_t v___x_397_; uint8_t v___x_398_; 
v___x_396_ = 90;
v___x_397_ = lean_unbox_uint32(v_val_384_);
v___x_398_ = lean_uint32_dec_le(v___x_397_, v___x_396_);
if (v___x_398_ == 0)
{
goto v___jp_385_;
}
else
{
lean_dec(v_val_384_);
goto v___jp_362_;
}
}
}
}
}
}
v___jp_349_:
{
uint32_t v___x_351_; uint8_t v___x_352_; 
v___x_351_ = 97;
v___x_352_ = lean_uint32_dec_le(v___x_351_, v___y_350_);
if (v___x_352_ == 0)
{
return v___x_352_;
}
else
{
uint32_t v___x_353_; uint8_t v___x_354_; 
v___x_353_ = 122;
v___x_354_ = lean_uint32_dec_le(v___y_350_, v___x_353_);
return v___x_354_;
}
}
v___jp_355_:
{
uint32_t v___x_357_; uint8_t v___x_358_; 
v___x_357_ = 65;
v___x_358_ = lean_uint32_dec_le(v___x_357_, v___y_356_);
if (v___x_358_ == 0)
{
v___y_350_ = v___y_356_;
goto v___jp_349_;
}
else
{
uint32_t v___x_359_; uint8_t v___x_360_; 
v___x_359_ = 90;
v___x_360_ = lean_uint32_dec_le(v___y_356_, v___x_359_);
if (v___x_360_ == 0)
{
v___y_350_ = v___y_356_;
goto v___jp_349_;
}
else
{
return v___x_360_;
}
}
}
v___jp_362_:
{
lean_object* v___x_363_; 
v___x_363_ = l_List_getLast_x3f___redArg(v_chars_361_);
lean_dec(v_chars_361_);
if (lean_obj_tag(v___x_363_) == 0)
{
uint8_t v___x_364_; 
v___x_364_ = 0;
return v___x_364_;
}
else
{
lean_object* v_val_365_; uint32_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v_val_365_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_val_365_);
lean_dec_ref_known(v___x_363_, 1);
v___x_366_ = lean_unbox_uint32(v_val_365_);
v___x_367_ = lean_uint32_to_nat(v___x_366_);
v___x_368_ = lean_unsigned_to_nat(128u);
v___x_369_ = lean_nat_dec_lt(v___x_367_, v___x_368_);
lean_dec(v___x_367_);
if (v___x_369_ == 0)
{
lean_dec(v_val_365_);
return v___x_369_;
}
else
{
uint32_t v___x_370_; uint32_t v___x_371_; uint8_t v___x_372_; 
v___x_370_ = 48;
v___x_371_ = lean_unbox_uint32(v_val_365_);
v___x_372_ = lean_uint32_dec_le(v___x_370_, v___x_371_);
if (v___x_372_ == 0)
{
uint32_t v___x_373_; 
v___x_373_ = lean_unbox_uint32(v_val_365_);
lean_dec(v_val_365_);
v___y_356_ = v___x_373_;
goto v___jp_355_;
}
else
{
uint32_t v___x_374_; uint32_t v___x_375_; uint8_t v___x_376_; 
v___x_374_ = 57;
v___x_375_ = lean_unbox_uint32(v_val_365_);
v___x_376_ = lean_uint32_dec_le(v___x_375_, v___x_374_);
if (v___x_376_ == 0)
{
uint32_t v___x_377_; 
v___x_377_ = lean_unbox_uint32(v_val_365_);
lean_dec(v_val_365_);
v___y_356_ = v___x_377_;
goto v___jp_355_;
}
else
{
lean_dec(v_val_365_);
return v___x_376_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidDomainLabel___boxed(lean_object* v_s_409_){
_start:
{
uint8_t v_res_410_; lean_object* v_r_411_; 
v_res_410_ = l_Std_Http_URI_isValidDomainLabel(v_s_409_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg(){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___redArg___closed__0));
return v___x_415_;
}
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
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(uint8_t v___x_423_, lean_object* v_lower_424_, lean_object* v___x_425_, lean_object* v___x_426_, lean_object* v_a_427_, uint8_t v_b_428_){
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg___boxed(lean_object* v___x_466_, lean_object* v_lower_467_, lean_object* v___x_468_, lean_object* v___x_469_, lean_object* v_a_470_, lean_object* v_b_471_){
_start:
{
uint8_t v___x_3760__boxed_472_; uint8_t v_b_boxed_473_; uint8_t v_res_474_; lean_object* v_r_475_; 
v___x_3760__boxed_472_ = lean_unbox(v___x_466_);
v_b_boxed_473_ = lean_unbox(v_b_471_);
v_res_474_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_3760__boxed_472_, v_lower_467_, v___x_468_, v___x_469_, v_a_470_, v_b_boxed_473_);
lean_dec_ref(v___x_468_);
lean_dec_ref(v_lower_467_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(lean_object* v___x_476_, lean_object* v_lower_477_, lean_object* v___x_478_, lean_object* v_a_479_, uint8_t v_b_480_){
_start:
{
if (lean_obj_tag(v_a_479_) == 0)
{
lean_object* v_currPos_481_; lean_object* v_searcher_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_497_; 
v_currPos_481_ = lean_ctor_get(v_a_479_, 0);
v_searcher_482_ = lean_ctor_get(v_a_479_, 1);
v_isSharedCheck_497_ = !lean_is_exclusive(v_a_479_);
if (v_isSharedCheck_497_ == 0)
{
v___x_484_ = v_a_479_;
v_isShared_485_ = v_isSharedCheck_497_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_searcher_482_);
lean_inc(v_currPos_481_);
lean_dec(v_a_479_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_497_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; uint8_t v___x_487_; uint8_t v_decide_488_; 
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = lean_nat_dec_eq(v___x_476_, v___x_486_);
v_decide_488_ = lean_nat_dec_eq(v_searcher_482_, v___x_478_);
if (v_decide_488_ == 0)
{
uint32_t v___x_489_; uint32_t v___x_490_; uint8_t v___x_491_; 
v___x_489_ = 46;
v___x_490_ = lean_string_utf8_get_fast(v_lower_477_, v_searcher_482_);
v___x_491_ = lean_uint32_dec_eq(v___x_490_, v___x_489_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_492_ = lean_string_utf8_next_fast(v_lower_477_, v_searcher_482_);
lean_dec(v_searcher_482_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 1, v___x_492_);
v___x_494_ = v___x_484_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_currPos_481_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v___x_492_);
v___x_494_ = v_reuseFailAlloc_496_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
v_a_479_ = v___x_494_;
goto _start;
}
}
else
{
lean_del_object(v___x_484_);
lean_dec(v_searcher_482_);
lean_dec(v_currPos_481_);
return v___x_487_;
}
}
else
{
lean_del_object(v___x_484_);
lean_dec(v_searcher_482_);
lean_dec(v_currPos_481_);
return v___x_487_;
}
}
}
else
{
return v_b_480_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg___boxed(lean_object* v___x_498_, lean_object* v_lower_499_, lean_object* v___x_500_, lean_object* v_a_501_, lean_object* v_b_502_){
_start:
{
uint8_t v_b_boxed_503_; uint8_t v_res_504_; lean_object* v_r_505_; 
v_b_boxed_503_ = lean_unbox(v_b_502_);
v_res_504_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_498_, v_lower_499_, v___x_500_, v_a_501_, v_b_boxed_503_);
lean_dec(v___x_500_);
lean_dec_ref(v_lower_499_);
lean_dec(v___x_498_);
v_r_505_ = lean_box(v_res_504_);
return v_r_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_DomainName_ofString_x3f(lean_object* v_s_506_){
_start:
{
lean_object* v___x_507_; lean_object* v_lower_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v_lower_508_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_506_, v___x_507_);
v___x_509_ = lean_string_utf8_byte_size(v_lower_508_);
v___x_510_ = lean_nat_dec_eq(v___x_509_, v___x_507_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; uint8_t v___x_514_; 
lean_inc_ref(v_lower_508_);
v___x_511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_511_, 0, v_lower_508_);
lean_ctor_set(v___x_511_, 1, v___x_507_);
lean_ctor_set(v___x_511_, 2, v___x_509_);
v___x_512_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0);
v___x_513_ = 1;
v___x_514_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_509_, v_lower_508_, v___x_509_, v___x_512_, v___x_513_);
if (v___x_514_ == 0)
{
uint8_t v___x_515_; 
v___x_515_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_514_, v_lower_508_, v___x_511_, v___x_509_, v___x_512_, v___x_513_);
lean_dec_ref_known(v___x_511_, 3);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
lean_dec_ref(v_lower_508_);
v___x_516_ = lean_box(0);
return v___x_516_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_517_ = lean_string_length(v_lower_508_);
v___x_518_ = lean_unsigned_to_nat(255u);
v___x_519_ = lean_nat_dec_le(v___x_517_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
lean_dec_ref(v_lower_508_);
v___x_520_ = lean_box(0);
return v___x_520_;
}
else
{
lean_object* v___x_521_; 
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v_lower_508_);
return v___x_521_;
}
}
}
else
{
lean_object* v___x_522_; 
lean_dec_ref_known(v___x_511_, 3);
lean_dec_ref(v_lower_508_);
v___x_522_ = lean_box(0);
return v___x_522_;
}
}
else
{
lean_object* v___x_523_; 
lean_dec_ref(v_lower_508_);
v___x_523_ = lean_box(0);
return v___x_523_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(lean_object* v___x_524_, lean_object* v_lower_525_, lean_object* v___x_526_, lean_object* v___x_527_, lean_object* v_inst_528_, lean_object* v_R_529_, lean_object* v_a_530_, uint8_t v_b_531_, lean_object* v_c_532_){
_start:
{
uint8_t v___x_533_; 
v___x_533_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_524_, v_lower_525_, v___x_527_, v_a_530_, v_b_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___boxed(lean_object* v___x_534_, lean_object* v_lower_535_, lean_object* v___x_536_, lean_object* v___x_537_, lean_object* v_inst_538_, lean_object* v_R_539_, lean_object* v_a_540_, lean_object* v_b_541_, lean_object* v_c_542_){
_start:
{
uint8_t v_b_boxed_543_; uint8_t v_res_544_; lean_object* v_r_545_; 
v_b_boxed_543_ = lean_unbox(v_b_541_);
v_res_544_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(v___x_534_, v_lower_535_, v___x_536_, v___x_537_, v_inst_538_, v_R_539_, v_a_540_, v_b_boxed_543_, v_c_542_);
lean_dec(v___x_537_);
lean_dec_ref(v___x_536_);
lean_dec_ref(v_lower_535_);
lean_dec(v___x_534_);
v_r_545_ = lean_box(v_res_544_);
return v_r_545_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(uint8_t v___x_546_, lean_object* v_lower_547_, lean_object* v___x_548_, lean_object* v___x_549_, lean_object* v_inst_550_, lean_object* v_R_551_, lean_object* v_a_552_, uint8_t v_b_553_, lean_object* v_c_554_){
_start:
{
uint8_t v___x_555_; 
v___x_555_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_546_, v_lower_547_, v___x_548_, v___x_549_, v_a_552_, v_b_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___boxed(lean_object* v___x_556_, lean_object* v_lower_557_, lean_object* v___x_558_, lean_object* v___x_559_, lean_object* v_inst_560_, lean_object* v_R_561_, lean_object* v_a_562_, lean_object* v_b_563_, lean_object* v_c_564_){
_start:
{
uint8_t v___x_3918__boxed_565_; uint8_t v_b_boxed_566_; uint8_t v_res_567_; lean_object* v_r_568_; 
v___x_3918__boxed_565_ = lean_unbox(v___x_556_);
v_b_boxed_566_ = lean_unbox(v_b_563_);
v_res_567_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(v___x_3918__boxed_565_, v_lower_557_, v___x_558_, v___x_559_, v_inst_560_, v_R_561_, v_a_562_, v_b_boxed_566_, v_c_564_);
lean_dec_ref(v___x_558_);
lean_dec_ref(v_lower_557_);
v_r_568_ = lean_box(v_res_567_);
return v_r_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx___impl(lean_object* v_x_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = lean_obj_tag_nat(v_x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx___impl___boxed(lean_object* v_x_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_Http_URI_Host_ctorIdx___impl(v_x_571_);
lean_dec_ref(v_x_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___redArg(lean_object* v_t_573_, lean_object* v_k_574_){
_start:
{
lean_object* v_name_575_; lean_object* v___x_576_; 
v_name_575_ = lean_ctor_get(v_t_573_, 0);
lean_inc_ref(v_name_575_);
lean_dec_ref(v_t_573_);
v___x_576_ = lean_apply_1(v_k_574_, v_name_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim(lean_object* v_motive_577_, lean_object* v_ctorIdx_578_, lean_object* v_t_579_, lean_object* v_h_580_, lean_object* v_k_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_579_, v_k_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___boxed(lean_object* v_motive_583_, lean_object* v_ctorIdx_584_, lean_object* v_t_585_, lean_object* v_h_586_, lean_object* v_k_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Std_Http_URI_Host_ctorElim(v_motive_583_, v_ctorIdx_584_, v_t_585_, v_h_586_, v_k_587_);
lean_dec(v_ctorIdx_584_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim___redArg(lean_object* v_t_589_, lean_object* v_name_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_589_, v_name_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim(lean_object* v_motive_592_, lean_object* v_t_593_, lean_object* v_h_594_, lean_object* v_name_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_593_, v_name_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim___redArg(lean_object* v_t_597_, lean_object* v_ipv4_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_597_, v_ipv4_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim(lean_object* v_motive_600_, lean_object* v_t_601_, lean_object* v_h_602_, lean_object* v_ipv4_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_601_, v_ipv4_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim___redArg(lean_object* v_t_605_, lean_object* v_ipv6_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_605_, v_ipv6_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim(lean_object* v_motive_608_, lean_object* v_t_609_, lean_object* v_h_610_, lean_object* v_ipv6_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_609_, v_ipv6_611_);
return v___x_612_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default___closed__0(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default(void){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_obj_once(&l_Std_Http_URI_instInhabitedHost_default___closed__0, &l_Std_Http_URI_instInhabitedHost_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedHost_default___closed__0);
return v___x_615_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost(void){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Std_Http_URI_instInhabitedHost_default;
return v___x_616_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqHost_beq(lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
switch(lean_obj_tag(v_x_617_))
{
case 0:
{
if (lean_obj_tag(v_x_618_) == 0)
{
lean_object* v_name_619_; lean_object* v_name_620_; uint8_t v___x_621_; 
v_name_619_ = lean_ctor_get(v_x_617_, 0);
v_name_620_ = lean_ctor_get(v_x_618_, 0);
v___x_621_ = lean_string_dec_eq(v_name_619_, v_name_620_);
return v___x_621_;
}
else
{
uint8_t v___x_622_; 
v___x_622_ = 0;
return v___x_622_;
}
}
case 1:
{
if (lean_obj_tag(v_x_618_) == 1)
{
lean_object* v_ipv4_623_; lean_object* v_ipv4_624_; uint8_t v___x_625_; 
v_ipv4_623_ = lean_ctor_get(v_x_617_, 0);
v_ipv4_624_ = lean_ctor_get(v_x_618_, 0);
v___x_625_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_ipv4_623_, v_ipv4_624_);
return v___x_625_;
}
else
{
uint8_t v___x_626_; 
v___x_626_ = 0;
return v___x_626_;
}
}
default: 
{
if (lean_obj_tag(v_x_618_) == 2)
{
lean_object* v_ipv6_627_; lean_object* v_ipv6_628_; uint8_t v___x_629_; 
v_ipv6_627_ = lean_ctor_get(v_x_617_, 0);
v_ipv6_628_ = lean_ctor_get(v_x_618_, 0);
v___x_629_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_ipv6_627_, v_ipv6_628_);
return v___x_629_;
}
else
{
uint8_t v___x_630_; 
v___x_630_ = 0;
return v___x_630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqHost_beq___boxed(lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
uint8_t v_res_633_; lean_object* v_r_634_; 
v_res_633_ = l_Std_Http_URI_instBEqHost_beq(v_x_631_, v_x_632_);
lean_dec_ref(v_x_632_);
lean_dec_ref(v_x_631_);
v_r_634_ = lean_box(v_res_633_);
return v_r_634_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__4(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_unsigned_to_nat(2u);
v___x_642_ = lean_nat_to_int(v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__5(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_nat_to_int(v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0(lean_object* v_x_645_, lean_object* v_prec_646_){
_start:
{
lean_object* v___y_648_; lean_object* v_ctr_649_; lean_object* v_a_650_; lean_object* v___y_662_; lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_unsigned_to_nat(1024u);
v___x_694_ = lean_nat_dec_le(v___x_693_, v_prec_646_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
v___x_695_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_662_ = v___x_695_;
goto v___jp_661_;
}
else
{
lean_object* v___x_696_; 
v___x_696_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_662_ = v___x_696_;
goto v___jp_661_;
}
v___jp_647_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_651_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_652_ = lean_string_append(v___x_651_, v_ctr_649_);
v___x_653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
v___x_654_ = lean_box(1);
v___x_655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set(v___x_656_, 1, v_a_650_);
lean_inc(v___y_648_);
v___x_657_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_657_, 0, v___y_648_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = 0;
v___x_659_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*1, v___x_658_);
v___x_660_ = l_Repr_addAppParen(v___x_659_, v_prec_646_);
return v___x_660_;
}
v___jp_661_:
{
switch(lean_obj_tag(v_x_645_))
{
case 0:
{
lean_object* v_name_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_672_; 
v_name_663_ = lean_ctor_get(v_x_645_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v_x_645_);
if (v_isSharedCheck_672_ == 0)
{
v___x_665_ = v_x_645_;
v_isShared_666_ = v_isSharedCheck_672_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_name_663_);
lean_dec(v_x_645_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_672_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_667_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_668_ = l_String_quote(v_name_663_);
if (v_isShared_666_ == 0)
{
lean_ctor_set_tag(v___x_665_, 3);
lean_ctor_set(v___x_665_, 0, v___x_668_);
v___x_670_ = v___x_665_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
v___y_648_ = v___y_662_;
v_ctr_649_ = v___x_667_;
v_a_650_ = v___x_670_;
goto v___jp_647_;
}
}
}
case 1:
{
lean_object* v_ipv4_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_682_; 
v_ipv4_673_ = lean_ctor_get(v_x_645_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v_x_645_);
if (v_isSharedCheck_682_ == 0)
{
v___x_675_ = v_x_645_;
v_isShared_676_ = v_isSharedCheck_682_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_ipv4_673_);
lean_dec(v_x_645_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_682_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_677_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_678_ = lean_uv_ntop_v4(v_ipv4_673_);
lean_dec_ref(v_ipv4_673_);
if (v_isShared_676_ == 0)
{
lean_ctor_set_tag(v___x_675_, 3);
lean_ctor_set(v___x_675_, 0, v___x_678_);
v___x_680_ = v___x_675_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
v___y_648_ = v___y_662_;
v_ctr_649_ = v___x_677_;
v_a_650_ = v___x_680_;
goto v___jp_647_;
}
}
}
default: 
{
lean_object* v_ipv6_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_692_; 
v_ipv6_683_ = lean_ctor_get(v_x_645_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v_x_645_);
if (v_isSharedCheck_692_ == 0)
{
v___x_685_ = v_x_645_;
v_isShared_686_ = v_isSharedCheck_692_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_ipv6_683_);
lean_dec(v_x_645_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_692_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_687_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_688_ = lean_uv_ntop_v6(v_ipv6_683_);
lean_dec_ref(v_ipv6_683_);
if (v_isShared_686_ == 0)
{
lean_ctor_set_tag(v___x_685_, 3);
lean_ctor_set(v___x_685_, 0, v___x_688_);
v___x_690_ = v___x_685_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
v___y_648_ = v___y_662_;
v_ctr_649_ = v___x_687_;
v_a_650_ = v___x_690_;
goto v___jp_647_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0___boxed(lean_object* v_x_697_, lean_object* v_prec_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std_Http_URI_instReprHost___lam__0(v_x_697_, v_prec_698_);
lean_dec(v_prec_698_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0(lean_object* v_x_704_){
_start:
{
switch(lean_obj_tag(v_x_704_))
{
case 0:
{
lean_object* v_name_705_; 
v_name_705_ = lean_ctor_get(v_x_704_, 0);
lean_inc_ref(v_name_705_);
return v_name_705_;
}
case 1:
{
lean_object* v_ipv4_706_; lean_object* v___x_707_; 
v_ipv4_706_ = lean_ctor_get(v_x_704_, 0);
v___x_707_ = lean_uv_ntop_v4(v_ipv4_706_);
return v___x_707_;
}
default: 
{
lean_object* v_ipv6_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_ipv6_708_ = lean_ctor_get(v_x_704_, 0);
v___x_709_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_710_ = lean_uv_ntop_v6(v_ipv6_708_);
v___x_711_ = lean_string_append(v___x_709_, v___x_710_);
lean_dec_ref(v___x_710_);
v___x_712_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_713_ = lean_string_append(v___x_711_, v___x_712_);
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0___boxed(lean_object* v_x_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Std_Http_URI_instToStringHost___lam__0(v_x_714_);
lean_dec_ref(v_x_714_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___impl(lean_object* v_x_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = lean_obj_tag_nat(v_x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___impl___boxed(lean_object* v_x_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Std_Http_URI_Port_ctorIdx___impl(v_x_720_);
lean_dec(v_x_720_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg(lean_object* v_t_722_, lean_object* v_k_723_){
_start:
{
if (lean_obj_tag(v_t_722_) == 2)
{
uint16_t v_port_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_port_724_ = lean_ctor_get_uint16(v_t_722_, 0);
v___x_725_ = lean_box(v_port_724_);
v___x_726_ = lean_apply_1(v_k_723_, v___x_725_);
return v___x_726_;
}
else
{
return v_k_723_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg___boxed(lean_object* v_t_727_, lean_object* v_k_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_727_, v_k_728_);
lean_dec(v_t_727_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim(lean_object* v_motive_730_, lean_object* v_ctorIdx_731_, lean_object* v_t_732_, lean_object* v_h_733_, lean_object* v_k_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_732_, v_k_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___boxed(lean_object* v_motive_736_, lean_object* v_ctorIdx_737_, lean_object* v_t_738_, lean_object* v_h_739_, lean_object* v_k_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Std_Http_URI_Port_ctorElim(v_motive_736_, v_ctorIdx_737_, v_t_738_, v_h_739_, v_k_740_);
lean_dec(v_t_738_);
lean_dec(v_ctorIdx_737_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg(lean_object* v_t_742_, lean_object* v_omitted_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_742_, v_omitted_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg___boxed(lean_object* v_t_745_, lean_object* v_omitted_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Std_Http_URI_Port_omitted_elim___redArg(v_t_745_, v_omitted_746_);
lean_dec(v_t_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim(lean_object* v_motive_748_, lean_object* v_t_749_, lean_object* v_h_750_, lean_object* v_omitted_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_749_, v_omitted_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___boxed(lean_object* v_motive_753_, lean_object* v_t_754_, lean_object* v_h_755_, lean_object* v_omitted_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Std_Http_URI_Port_omitted_elim(v_motive_753_, v_t_754_, v_h_755_, v_omitted_756_);
lean_dec(v_t_754_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg(lean_object* v_t_758_, lean_object* v_empty_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_758_, v_empty_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg___boxed(lean_object* v_t_761_, lean_object* v_empty_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_Http_URI_Port_empty_elim___redArg(v_t_761_, v_empty_762_);
lean_dec(v_t_761_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim(lean_object* v_motive_764_, lean_object* v_t_765_, lean_object* v_h_766_, lean_object* v_empty_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_765_, v_empty_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___boxed(lean_object* v_motive_769_, lean_object* v_t_770_, lean_object* v_h_771_, lean_object* v_empty_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Std_Http_URI_Port_empty_elim(v_motive_769_, v_t_770_, v_h_771_, v_empty_772_);
lean_dec(v_t_770_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg(lean_object* v_t_774_, lean_object* v_value_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_774_, v_value_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg___boxed(lean_object* v_t_777_, lean_object* v_value_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Std_Http_URI_Port_value_elim___redArg(v_t_777_, v_value_778_);
lean_dec(v_t_777_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim(lean_object* v_motive_780_, lean_object* v_t_781_, lean_object* v_h_782_, lean_object* v_value_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_781_, v_value_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___boxed(lean_object* v_motive_785_, lean_object* v_t_786_, lean_object* v_h_787_, lean_object* v_value_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_Http_URI_Port_value_elim(v_motive_785_, v_t_786_, v_h_787_, v_value_788_);
lean_dec(v_t_786_);
return v_res_789_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort_default(void){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = lean_box(0);
return v___x_790_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort(void){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = lean_box(0);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr(lean_object* v_x_804_, lean_object* v_prec_805_){
_start:
{
lean_object* v___y_807_; lean_object* v___y_814_; 
switch(lean_obj_tag(v_x_804_))
{
case 0:
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = lean_unsigned_to_nat(1024u);
v___x_821_ = lean_nat_dec_le(v___x_820_, v_prec_805_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; 
v___x_822_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_814_ = v___x_822_;
goto v___jp_813_;
}
else
{
lean_object* v___x_823_; 
v___x_823_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_814_ = v___x_823_;
goto v___jp_813_;
}
}
case 1:
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = lean_unsigned_to_nat(1024u);
v___x_825_ = lean_nat_dec_le(v___x_824_, v_prec_805_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; 
v___x_826_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_807_ = v___x_826_;
goto v___jp_806_;
}
else
{
lean_object* v___x_827_; 
v___x_827_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_807_ = v___x_827_;
goto v___jp_806_;
}
}
default: 
{
uint16_t v_port_828_; lean_object* v___y_830_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_port_828_ = lean_ctor_get_uint16(v_x_804_, 0);
v___x_840_ = lean_unsigned_to_nat(1024u);
v___x_841_ = lean_nat_dec_le(v___x_840_, v_prec_805_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; 
v___x_842_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_830_ = v___x_842_;
goto v___jp_829_;
}
else
{
lean_object* v___x_843_; 
v___x_843_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_830_ = v___x_843_;
goto v___jp_829_;
}
v___jp_829_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_831_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__6));
v___x_832_ = lean_uint16_to_nat(v_port_828_);
v___x_833_ = l_Nat_reprFast(v___x_832_);
v___x_834_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
v___x_835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_831_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
lean_inc(v___y_830_);
v___x_836_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_836_, 0, v___y_830_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = 0;
v___x_838_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*1, v___x_837_);
v___x_839_ = l_Repr_addAppParen(v___x_838_, v_prec_805_);
return v___x_839_;
}
}
}
v___jp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_808_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__1));
lean_inc(v___y_807_);
v___x_809_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_809_, 0, v___y_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = 0;
v___x_811_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*1, v___x_810_);
v___x_812_ = l_Repr_addAppParen(v___x_811_, v_prec_805_);
return v___x_812_;
}
v___jp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_815_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__3));
lean_inc(v___y_814_);
v___x_816_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_816_, 0, v___y_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = 0;
v___x_818_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*1, v___x_817_);
v___x_819_ = l_Repr_addAppParen(v___x_818_, v_prec_805_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr___boxed(lean_object* v_x_844_, lean_object* v_prec_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Std_Http_URI_instReprPort_repr(v_x_844_, v_prec_845_);
lean_dec(v_prec_845_);
lean_dec(v_x_844_);
return v_res_846_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort_decEq(lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
switch(lean_obj_tag(v_x_849_))
{
case 0:
{
if (lean_obj_tag(v_x_850_) == 0)
{
uint8_t v___x_851_; 
v___x_851_ = 1;
return v___x_851_;
}
else
{
uint8_t v___x_852_; 
v___x_852_ = 0;
return v___x_852_;
}
}
case 1:
{
if (lean_obj_tag(v_x_850_) == 1)
{
uint8_t v___x_853_; 
v___x_853_ = 1;
return v___x_853_;
}
else
{
uint8_t v___x_854_; 
v___x_854_ = 0;
return v___x_854_;
}
}
default: 
{
if (lean_obj_tag(v_x_850_) == 2)
{
uint16_t v_port_855_; uint16_t v_port_856_; uint8_t v___x_857_; 
v_port_855_ = lean_ctor_get_uint16(v_x_849_, 0);
v_port_856_ = lean_ctor_get_uint16(v_x_850_, 0);
v___x_857_ = lean_uint16_dec_eq(v_port_855_, v_port_856_);
return v___x_857_;
}
else
{
uint8_t v___x_858_; 
v___x_858_ = 0;
return v___x_858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort_decEq___boxed(lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
uint8_t v_res_861_; lean_object* v_r_862_; 
v_res_861_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_859_, v_x_860_);
lean_dec(v_x_860_);
lean_dec(v_x_859_);
v_r_862_ = lean_box(v_res_861_);
return v_r_862_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort(lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
uint8_t v___x_865_; 
v___x_865_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_863_, v_x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort___boxed(lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
uint8_t v_res_868_; lean_object* v_r_869_; 
v_res_868_ = l_Std_Http_URI_instDecidableEqPort(v_x_866_, v_x_867_);
lean_dec(v_x_867_);
lean_dec(v_x_866_);
v_r_869_ = lean_box(v_res_868_);
return v_r_869_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_870_ = lean_box(0);
v___x_871_ = l_Std_Http_URI_instInhabitedHost_default;
v___x_872_ = lean_box(0);
v___x_873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v___x_871_);
lean_ctor_set(v___x_873_, 2, v___x_870_);
return v___x_873_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default(void){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = lean_obj_once(&l_Std_Http_URI_instInhabitedAuthority_default___closed__0, &l_Std_Http_URI_instInhabitedAuthority_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0);
return v___x_874_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority(void){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Std_Http_URI_instInhabitedAuthority_default;
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
if (lean_obj_tag(v_x_876_) == 0)
{
lean_object* v___x_878_; 
v___x_878_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_878_;
}
else
{
lean_object* v_val_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_val_879_ = lean_ctor_get(v_x_876_, 0);
lean_inc(v_val_879_);
lean_dec_ref_known(v_x_876_, 1);
v___x_880_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_881_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_val_879_);
v___x_882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = l_Repr_addAppParen(v___x_882_, v_x_877_);
return v___x_883_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0___boxed(lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_x_884_, v_x_885_);
lean_dec(v_x_885_);
return v_res_886_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_unsigned_to_nat(8u);
v___x_900_ = lean_nat_to_int(v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg(lean_object* v_x_904_){
_start:
{
lean_object* v_userInfo_905_; lean_object* v_host_906_; lean_object* v_port_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v_ctr_927_; lean_object* v_a_928_; 
v_userInfo_905_ = lean_ctor_get(v_x_904_, 0);
lean_inc(v_userInfo_905_);
v_host_906_ = lean_ctor_get(v_x_904_, 1);
lean_inc_ref(v_host_906_);
v_port_907_ = lean_ctor_get(v_x_904_, 2);
lean_inc(v_port_907_);
lean_dec_ref(v_x_904_);
v___x_908_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_909_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3));
v___x_910_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_userInfo_905_, v___x_911_);
v___x_913_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_910_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = 0;
v___x_915_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*1, v___x_914_);
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_909_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_box(1);
v___x_920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_920_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___x_908_);
v___x_924_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_925_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_906_))
{
case 0:
{
lean_object* v_name_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_965_; 
v_name_956_ = lean_ctor_get(v_host_906_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v_host_906_);
if (v_isSharedCheck_965_ == 0)
{
v___x_958_ = v_host_906_;
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_name_956_);
lean_dec(v_host_906_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_960_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_961_ = l_String_quote(v_name_956_);
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 3);
lean_ctor_set(v___x_958_, 0, v___x_961_);
v___x_963_ = v___x_958_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
v_ctr_927_ = v___x_960_;
v_a_928_ = v___x_963_;
goto v___jp_926_;
}
}
}
case 1:
{
lean_object* v_ipv4_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_975_; 
v_ipv4_966_ = lean_ctor_get(v_host_906_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v_host_906_);
if (v_isSharedCheck_975_ == 0)
{
v___x_968_ = v_host_906_;
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_ipv4_966_);
lean_dec(v_host_906_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_970_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_971_ = lean_uv_ntop_v4(v_ipv4_966_);
lean_dec_ref(v_ipv4_966_);
if (v_isShared_969_ == 0)
{
lean_ctor_set_tag(v___x_968_, 3);
lean_ctor_set(v___x_968_, 0, v___x_971_);
v___x_973_ = v___x_968_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
v_ctr_927_ = v___x_970_;
v_a_928_ = v___x_973_;
goto v___jp_926_;
}
}
}
default: 
{
lean_object* v_ipv6_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_985_; 
v_ipv6_976_ = lean_ctor_get(v_host_906_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v_host_906_);
if (v_isSharedCheck_985_ == 0)
{
v___x_978_ = v_host_906_;
v_isShared_979_ = v_isSharedCheck_985_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_ipv6_976_);
lean_dec(v_host_906_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_985_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_980_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_981_ = lean_uv_ntop_v6(v_ipv6_976_);
lean_dec_ref(v_ipv6_976_);
if (v_isShared_979_ == 0)
{
lean_ctor_set_tag(v___x_978_, 3);
lean_ctor_set(v___x_978_, 0, v___x_981_);
v___x_983_ = v___x_978_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
v_ctr_927_ = v___x_980_;
v_a_928_ = v___x_983_;
goto v___jp_926_;
}
}
}
}
v___jp_926_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_929_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_930_ = lean_string_append(v___x_929_, v_ctr_927_);
v___x_931_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
v___x_932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v___x_919_);
v___x_933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v_a_928_);
v___x_934_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_925_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*1, v___x_914_);
v___x_936_ = l_Repr_addAppParen(v___x_935_, v___x_911_);
v___x_937_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_924_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set_uint8(v___x_938_, sizeof(void*)*1, v___x_914_);
v___x_939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_923_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v___x_917_);
v___x_941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_919_);
v___x_942_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___x_908_);
v___x_945_ = l_Std_Http_URI_instReprPort_repr(v_port_907_, v___x_911_);
lean_dec(v_port_907_);
v___x_946_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_924_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*1, v___x_914_);
v___x_948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_944_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_950_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___x_948_);
v___x_952_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_949_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set_uint8(v___x_955_, sizeof(void*)*1, v___x_914_);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr(lean_object* v_x_986_, lean_object* v_prec_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_x_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___boxed(lean_object* v_x_989_, lean_object* v_prec_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Std_Http_URI_instReprAuthority_repr(v_x_989_, v_prec_990_);
lean_dec(v_prec_990_);
return v_res_991_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(lean_object* v_x_994_, lean_object* v_x_995_){
_start:
{
if (lean_obj_tag(v_x_994_) == 0)
{
if (lean_obj_tag(v_x_995_) == 0)
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
else
{
if (lean_obj_tag(v_x_995_) == 0)
{
uint8_t v___x_998_; 
v___x_998_ = 0;
return v___x_998_;
}
else
{
lean_object* v_val_999_; lean_object* v_val_1000_; uint8_t v___x_1001_; 
v_val_999_ = lean_ctor_get(v_x_994_, 0);
v_val_1000_ = lean_ctor_get(v_x_995_, 0);
v___x_1001_ = l_Std_Http_URI_instBEqUserInfo_beq(v_val_999_, v_val_1000_);
return v___x_1001_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0___boxed(lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
uint8_t v_res_1004_; lean_object* v_r_1005_; 
v_res_1004_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_x_1002_, v_x_1003_);
lean_dec(v_x_1003_);
lean_dec(v_x_1002_);
v_r_1005_ = lean_box(v_res_1004_);
return v_r_1005_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqAuthority_beq(lean_object* v_x_1006_, lean_object* v_x_1007_){
_start:
{
lean_object* v_userInfo_1008_; lean_object* v_host_1009_; lean_object* v_port_1010_; lean_object* v_userInfo_1011_; lean_object* v_host_1012_; lean_object* v_port_1013_; uint8_t v___x_1014_; 
v_userInfo_1008_ = lean_ctor_get(v_x_1006_, 0);
v_host_1009_ = lean_ctor_get(v_x_1006_, 1);
v_port_1010_ = lean_ctor_get(v_x_1006_, 2);
v_userInfo_1011_ = lean_ctor_get(v_x_1007_, 0);
v_host_1012_ = lean_ctor_get(v_x_1007_, 1);
v_port_1013_ = lean_ctor_get(v_x_1007_, 2);
v___x_1014_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_userInfo_1008_, v_userInfo_1011_);
if (v___x_1014_ == 0)
{
return v___x_1014_;
}
else
{
uint8_t v___x_1015_; 
v___x_1015_ = l_Std_Http_URI_instBEqHost_beq(v_host_1009_, v_host_1012_);
if (v___x_1015_ == 0)
{
return v___x_1015_;
}
else
{
uint8_t v___x_1016_; 
v___x_1016_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1010_, v_port_1013_);
return v___x_1016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqAuthority_beq___boxed(lean_object* v_x_1017_, lean_object* v_x_1018_){
_start:
{
uint8_t v_res_1019_; lean_object* v_r_1020_; 
v_res_1019_ = l_Std_Http_URI_instBEqAuthority_beq(v_x_1017_, v_x_1018_);
lean_dec_ref(v_x_1018_);
lean_dec_ref(v_x_1017_);
v_r_1020_ = lean_box(v_res_1019_);
return v_r_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringAuthority___lam__0(lean_object* v_auth_1026_){
_start:
{
lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v_userInfo_1033_; lean_object* v_host_1034_; lean_object* v_port_1035_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1047_; 
v_userInfo_1033_ = lean_ctor_get(v_auth_1026_, 0);
lean_inc(v_userInfo_1033_);
v_host_1034_ = lean_ctor_get(v_auth_1026_, 1);
lean_inc_ref(v_host_1034_);
v_port_1035_ = lean_ctor_get(v_auth_1026_, 2);
lean_inc(v_port_1035_);
lean_dec_ref(v_auth_1026_);
if (lean_obj_tag(v_userInfo_1033_) == 0)
{
lean_object* v___x_1057_; 
v___x_1057_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1047_ = v___x_1057_;
goto v___jp_1046_;
}
else
{
lean_object* v_val_1058_; lean_object* v_password_1059_; 
v_val_1058_ = lean_ctor_get(v_userInfo_1033_, 0);
lean_inc(v_val_1058_);
lean_dec_ref_known(v_userInfo_1033_, 1);
v_password_1059_ = lean_ctor_get(v_val_1058_, 1);
if (lean_obj_tag(v_password_1059_) == 0)
{
lean_object* v_username_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_username_1060_ = lean_ctor_get(v_val_1058_, 0);
lean_inc_ref(v_username_1060_);
lean_dec(v_val_1058_);
v___x_1061_ = lean_string_from_utf8_unchecked(v_username_1060_);
v___x_1062_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1063_ = lean_string_append(v___x_1061_, v___x_1062_);
v___y_1047_ = v___x_1063_;
goto v___jp_1046_;
}
else
{
lean_object* v_username_1064_; lean_object* v_val_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_inc_ref(v_password_1059_);
v_username_1064_ = lean_ctor_get(v_val_1058_, 0);
lean_inc_ref(v_username_1064_);
lean_dec(v_val_1058_);
v_val_1065_ = lean_ctor_get(v_password_1059_, 0);
lean_inc(v_val_1065_);
lean_dec_ref_known(v_password_1059_, 1);
v___x_1066_ = lean_string_from_utf8_unchecked(v_username_1064_);
v___x_1067_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1068_ = lean_string_append(v___x_1066_, v___x_1067_);
v___x_1069_ = lean_string_from_utf8_unchecked(v_val_1065_);
v___x_1070_ = lean_string_append(v___x_1068_, v___x_1069_);
lean_dec_ref(v___x_1069_);
v___x_1071_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1072_ = lean_string_append(v___x_1070_, v___x_1071_);
v___y_1047_ = v___x_1072_;
goto v___jp_1046_;
}
}
v___jp_1027_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_string_append(v___y_1029_, v___y_1028_);
lean_dec_ref(v___y_1028_);
v___x_1032_ = lean_string_append(v___x_1031_, v___y_1030_);
lean_dec_ref(v___y_1030_);
return v___x_1032_;
}
v___jp_1036_:
{
switch(lean_obj_tag(v_port_1035_))
{
case 0:
{
lean_object* v___x_1039_; 
v___x_1039_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1028_ = v___y_1038_;
v___y_1029_ = v___y_1037_;
v___y_1030_ = v___x_1039_;
goto v___jp_1027_;
}
case 1:
{
lean_object* v___x_1040_; 
v___x_1040_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_1028_ = v___y_1038_;
v___y_1029_ = v___y_1037_;
v___y_1030_ = v___x_1040_;
goto v___jp_1027_;
}
default: 
{
uint16_t v_port_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v_port_1041_ = lean_ctor_get_uint16(v_port_1035_, 0);
lean_dec_ref_known(v_port_1035_, 0);
v___x_1042_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1043_ = lean_uint16_to_nat(v_port_1041_);
v___x_1044_ = l_Nat_reprFast(v___x_1043_);
v___x_1045_ = lean_string_append(v___x_1042_, v___x_1044_);
lean_dec_ref(v___x_1044_);
v___y_1028_ = v___y_1038_;
v___y_1029_ = v___y_1037_;
v___y_1030_ = v___x_1045_;
goto v___jp_1027_;
}
}
}
v___jp_1046_:
{
switch(lean_obj_tag(v_host_1034_))
{
case 0:
{
lean_object* v_name_1048_; 
v_name_1048_ = lean_ctor_get(v_host_1034_, 0);
lean_inc_ref(v_name_1048_);
lean_dec_ref_known(v_host_1034_, 1);
v___y_1037_ = v___y_1047_;
v___y_1038_ = v_name_1048_;
goto v___jp_1036_;
}
case 1:
{
lean_object* v_ipv4_1049_; lean_object* v___x_1050_; 
v_ipv4_1049_ = lean_ctor_get(v_host_1034_, 0);
lean_inc_ref(v_ipv4_1049_);
lean_dec_ref_known(v_host_1034_, 1);
v___x_1050_ = lean_uv_ntop_v4(v_ipv4_1049_);
lean_dec_ref(v_ipv4_1049_);
v___y_1037_ = v___y_1047_;
v___y_1038_ = v___x_1050_;
goto v___jp_1036_;
}
default: 
{
lean_object* v_ipv6_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_ipv6_1051_ = lean_ctor_get(v_host_1034_, 0);
lean_inc_ref(v_ipv6_1051_);
lean_dec_ref_known(v_host_1034_, 1);
v___x_1052_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_1053_ = lean_uv_ntop_v6(v_ipv6_1051_);
lean_dec_ref(v_ipv6_1051_);
v___x_1054_ = lean_string_append(v___x_1052_, v___x_1053_);
lean_dec_ref(v___x_1053_);
v___x_1055_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_1056_ = lean_string_append(v___x_1054_, v___x_1055_);
v___y_1037_ = v___y_1047_;
v___y_1038_ = v___x_1056_;
goto v___jp_1036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
if (lean_obj_tag(v_x_1084_) == 0)
{
lean_dec(v_x_1082_);
return v_x_1083_;
}
else
{
lean_object* v_head_1085_; lean_object* v_tail_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1098_; 
v_head_1085_ = lean_ctor_get(v_x_1084_, 0);
v_tail_1086_ = lean_ctor_get(v_x_1084_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_x_1084_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1088_ = v_x_1084_;
v_isShared_1089_ = v_isSharedCheck_1098_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_tail_1086_);
lean_inc(v_head_1085_);
lean_dec(v_x_1084_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1098_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
lean_inc(v_x_1082_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 5);
lean_ctor_set(v___x_1088_, 1, v_x_1082_);
lean_ctor_set(v___x_1088_, 0, v_x_1083_);
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_x_1083_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_x_1082_);
v___x_1091_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1092_ = lean_string_from_utf8_unchecked(v_head_1085_);
v___x_1093_ = l_String_quote(v___x_1092_);
v___x_1094_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
v___x_1095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1091_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v_x_1083_ = v___x_1095_;
v_x_1084_ = v_tail_1086_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(lean_object* v_x_1099_, lean_object* v_x_1100_, lean_object* v_x_1101_){
_start:
{
if (lean_obj_tag(v_x_1101_) == 0)
{
lean_dec(v_x_1099_);
return v_x_1100_;
}
else
{
lean_object* v_head_1102_; lean_object* v_tail_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1115_; 
v_head_1102_ = lean_ctor_get(v_x_1101_, 0);
v_tail_1103_ = lean_ctor_get(v_x_1101_, 1);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_x_1101_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1105_ = v_x_1101_;
v_isShared_1106_ = v_isSharedCheck_1115_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_tail_1103_);
lean_inc(v_head_1102_);
lean_dec(v_x_1101_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1115_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
lean_inc(v_x_1099_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set_tag(v___x_1105_, 5);
lean_ctor_set(v___x_1105_, 1, v_x_1099_);
lean_ctor_set(v___x_1105_, 0, v_x_1100_);
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_x_1100_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_x_1099_);
v___x_1108_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1109_ = lean_string_from_utf8_unchecked(v_head_1102_);
v___x_1110_ = l_String_quote(v___x_1109_);
v___x_1111_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
v___x_1112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1108_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(v_x_1099_, v___x_1112_, v_tail_1103_);
return v___x_1113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(lean_object* v___y_1116_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = lean_string_from_utf8_unchecked(v___y_1116_);
v___x_1118_ = l_String_quote(v___x_1117_);
v___x_1119_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(lean_object* v_x_1120_, lean_object* v_x_1121_){
_start:
{
if (lean_obj_tag(v_x_1120_) == 0)
{
lean_object* v___x_1122_; 
lean_dec(v_x_1121_);
v___x_1122_ = lean_box(0);
return v___x_1122_;
}
else
{
lean_object* v_tail_1123_; 
v_tail_1123_ = lean_ctor_get(v_x_1120_, 1);
if (lean_obj_tag(v_tail_1123_) == 0)
{
lean_object* v_head_1124_; lean_object* v___x_1125_; 
lean_dec(v_x_1121_);
v_head_1124_ = lean_ctor_get(v_x_1120_, 0);
lean_inc(v_head_1124_);
lean_dec_ref_known(v_x_1120_, 2);
v___x_1125_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1124_);
return v___x_1125_;
}
else
{
lean_object* v_head_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_inc(v_tail_1123_);
v_head_1126_ = lean_ctor_get(v_x_1120_, 0);
lean_inc(v_head_1126_);
lean_dec_ref_known(v_x_1120_, 2);
v___x_1127_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1126_);
v___x_1128_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(v_x_1121_, v___x_1127_, v_tail_1123_);
return v___x_1128_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0));
v___x_1134_ = lean_string_length(v___x_1133_);
return v___x_1134_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2);
v___x_1136_ = lean_nat_to_int(v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(lean_object* v_xs_1144_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = lean_array_get_size(v_xs_1144_);
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = lean_nat_dec_eq(v___x_1145_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1148_ = lean_array_to_list(v_xs_1144_);
v___x_1149_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1150_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(v___x_1148_, v___x_1149_);
v___x_1151_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1152_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v___x_1150_);
v___x_1154_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1151_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l_Std_Format_fill(v___x_1156_);
return v___x_1157_;
}
else
{
lean_object* v___x_1158_; 
lean_dec_ref(v_xs_1144_);
v___x_1158_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___redArg(lean_object* v_x_1171_){
_start:
{
lean_object* v_segments_1172_; uint8_t v_absolute_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1205_; 
v_segments_1172_ = lean_ctor_get(v_x_1171_, 0);
v_absolute_1173_ = lean_ctor_get_uint8(v_x_1171_, sizeof(void*)*1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1175_ = v_x_1171_;
v_isShared_1176_ = v_isSharedCheck_1205_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_segments_1172_);
lean_dec(v_x_1171_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1205_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; lean_object* v___x_1184_; 
v___x_1177_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1178_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__3));
v___x_1179_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_1180_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(v_segments_1172_);
v___x_1181_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = 0;
if (v_isShared_1176_ == 0)
{
lean_ctor_set_tag(v___x_1175_, 6);
lean_ctor_set(v___x_1175_, 0, v___x_1181_);
v___x_1184_ = v___x_1175_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1181_);
v___x_1184_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*1, v___x_1182_);
v___x_1185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1178_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = lean_box(1);
v___x_1189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__5));
v___x_1191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v___x_1177_);
v___x_1193_ = l_Bool_repr___redArg(v_absolute_1173_);
v___x_1194_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1179_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set_uint8(v___x_1195_, sizeof(void*)*1, v___x_1182_);
v___x_1196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1192_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1198_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v___x_1196_);
v___x_1200_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1197_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
lean_ctor_set_uint8(v___x_1203_, sizeof(void*)*1, v___x_1182_);
return v___x_1203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr(lean_object* v_x_1206_, lean_object* v_prec_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Std_Http_URI_instReprPath_repr___redArg(v_x_1206_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___boxed(lean_object* v_x_1209_, lean_object* v_prec_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Std_Http_URI_instReprPath_repr(v_x_1209_, v_prec_1210_);
lean_dec(v_prec_1210_);
return v_res_1211_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(lean_object* v_xs_1214_, lean_object* v_ys_1215_, lean_object* v_x_1216_){
_start:
{
lean_object* v_zero_1217_; uint8_t v_isZero_1218_; 
v_zero_1217_ = lean_unsigned_to_nat(0u);
v_isZero_1218_ = lean_nat_dec_eq(v_x_1216_, v_zero_1217_);
if (v_isZero_1218_ == 1)
{
lean_dec(v_x_1216_);
return v_isZero_1218_;
}
else
{
lean_object* v_one_1219_; lean_object* v_n_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v_one_1219_ = lean_unsigned_to_nat(1u);
v_n_1220_ = lean_nat_sub(v_x_1216_, v_one_1219_);
lean_dec(v_x_1216_);
v___x_1221_ = lean_array_fget_borrowed(v_xs_1214_, v_n_1220_);
v___x_1222_ = lean_array_fget_borrowed(v_ys_1215_, v_n_1220_);
v___x_1223_ = lean_sarray_dec_eq(v___x_1221_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_dec(v_n_1220_);
return v___x_1223_;
}
else
{
v_x_1216_ = v_n_1220_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg___boxed(lean_object* v_xs_1225_, lean_object* v_ys_1226_, lean_object* v_x_1227_){
_start:
{
uint8_t v_res_1228_; lean_object* v_r_1229_; 
v_res_1228_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1225_, v_ys_1226_, v_x_1227_);
lean_dec_ref(v_ys_1226_);
lean_dec_ref(v_xs_1225_);
v_r_1229_ = lean_box(v_res_1228_);
return v_r_1229_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqPath_beq(lean_object* v_x_1230_, lean_object* v_x_1231_){
_start:
{
lean_object* v_segments_1232_; uint8_t v_absolute_1233_; lean_object* v_segments_1234_; uint8_t v_absolute_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v_segments_1232_ = lean_ctor_get(v_x_1230_, 0);
v_absolute_1233_ = lean_ctor_get_uint8(v_x_1230_, sizeof(void*)*1);
v_segments_1234_ = lean_ctor_get(v_x_1231_, 0);
v_absolute_1235_ = lean_ctor_get_uint8(v_x_1231_, sizeof(void*)*1);
v___x_1236_ = lean_array_get_size(v_segments_1232_);
v___x_1237_ = lean_array_get_size(v_segments_1234_);
v___x_1238_ = lean_nat_dec_eq(v___x_1236_, v___x_1237_);
if (v___x_1238_ == 0)
{
return v___x_1238_;
}
else
{
uint8_t v___x_1239_; 
v___x_1239_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_segments_1232_, v_segments_1234_, v___x_1236_);
if (v___x_1239_ == 0)
{
return v___x_1239_;
}
else
{
if (v_absolute_1235_ == 0)
{
if (v_absolute_1233_ == 0)
{
return v___x_1239_;
}
else
{
return v_absolute_1235_;
}
}
else
{
return v_absolute_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqPath_beq___boxed(lean_object* v_x_1240_, lean_object* v_x_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l_Std_Http_URI_instBEqPath_beq(v_x_1240_, v_x_1241_);
lean_dec_ref(v_x_1241_);
lean_dec_ref(v_x_1240_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(lean_object* v_xs_1244_, lean_object* v_ys_1245_, lean_object* v_hsz_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
uint8_t v___x_1249_; 
v___x_1249_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1244_, v_ys_1245_, v_x_1247_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___boxed(lean_object* v_xs_1250_, lean_object* v_ys_1251_, lean_object* v_hsz_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
uint8_t v_res_1255_; lean_object* v_r_1256_; 
v_res_1255_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(v_xs_1250_, v_ys_1251_, v_hsz_1252_, v_x_1253_, v_x_1254_);
lean_dec_ref(v_ys_1251_);
lean_dec_ref(v_xs_1250_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__0(lean_object* v_x_1259_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_string_from_utf8_unchecked(v_x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__1(lean_object* v___f_1281_, lean_object* v_path_1282_){
_start:
{
lean_object* v_segments_1283_; uint8_t v_absolute_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; size_t v_sz_1287_; size_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v_result_1291_; 
v_segments_1283_ = lean_ctor_get(v_path_1282_, 0);
lean_inc_ref(v_segments_1283_);
v_absolute_1284_ = lean_ctor_get_uint8(v_path_1282_, sizeof(void*)*1);
lean_dec_ref(v_path_1282_);
v___x_1285_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_1286_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_1287_ = lean_array_size(v_segments_1283_);
v___x_1288_ = ((size_t)0ULL);
v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1286_, v___f_1281_, v_sz_1287_, v___x_1288_, v_segments_1283_);
v___x_1290_ = lean_array_to_list(v___x_1289_);
v_result_1291_ = l_String_intercalate(v___x_1285_, v___x_1290_);
if (v_absolute_1284_ == 0)
{
return v_result_1291_;
}
else
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_string_append(v___x_1285_, v_result_1291_);
lean_dec_ref(v_result_1291_);
return v___x_1292_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Path_isEmpty(lean_object* v_p_1297_){
_start:
{
lean_object* v_segments_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_segments_1298_ = lean_ctor_get(v_p_1297_, 0);
v___x_1299_ = lean_array_get_size(v_segments_1298_);
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = lean_nat_dec_eq(v___x_1299_, v___x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_isEmpty___boxed(lean_object* v_p_1302_){
_start:
{
uint8_t v_res_1303_; lean_object* v_r_1304_; 
v_res_1303_ = l_Std_Http_URI_Path_isEmpty(v_p_1302_);
lean_dec_ref(v_p_1302_);
v_r_1304_ = lean_box(v_res_1303_);
return v_r_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parent(lean_object* v_p_1305_){
_start:
{
lean_object* v_segments_1306_; uint8_t v_absolute_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v_segments_1306_ = lean_ctor_get(v_p_1305_, 0);
v_absolute_1307_ = lean_ctor_get_uint8(v_p_1305_, sizeof(void*)*1);
v___x_1308_ = lean_array_get_size(v_segments_1306_);
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = lean_nat_dec_eq(v___x_1308_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1318_; 
lean_inc_ref(v_segments_1306_);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_p_1305_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; 
v_unused_1319_ = lean_ctor_get(v_p_1305_, 0);
lean_dec(v_unused_1319_);
v___x_1312_ = v_p_1305_;
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
else
{
lean_dec(v_p_1305_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = lean_array_pop(v_segments_1306_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1314_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, sizeof(void*)*1, v_absolute_1307_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
else
{
return v_p_1305_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join(lean_object* v_p1_1320_, lean_object* v_p2_1321_){
_start:
{
uint8_t v_absolute_1322_; 
v_absolute_1322_ = lean_ctor_get_uint8(v_p2_1321_, sizeof(void*)*1);
if (v_absolute_1322_ == 0)
{
lean_object* v_segments_1323_; lean_object* v_segments_1324_; uint8_t v_absolute_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1333_; 
v_segments_1323_ = lean_ctor_get(v_p2_1321_, 0);
v_segments_1324_ = lean_ctor_get(v_p1_1320_, 0);
v_absolute_1325_ = lean_ctor_get_uint8(v_p1_1320_, sizeof(void*)*1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_p1_1320_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1327_ = v_p1_1320_;
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_segments_1324_);
lean_dec(v_p1_1320_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = l_Array_append___redArg(v_segments_1324_, v_segments_1323_);
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
lean_ctor_set_uint8(v_reuseFailAlloc_1332_, sizeof(void*)*1, v_absolute_1325_);
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
lean_dec_ref(v_p1_1320_);
lean_inc_ref(v_p2_1321_);
return v_p2_1321_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join___boxed(lean_object* v_p1_1334_, lean_object* v_p2_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Std_Http_URI_Path_join(v_p1_1334_, v_p2_1335_);
lean_dec_ref(v_p2_1335_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append(lean_object* v_p_1337_, lean_object* v_segment_1338_){
_start:
{
lean_object* v_segments_1339_; uint8_t v_absolute_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1349_; 
v_segments_1339_ = lean_ctor_get(v_p_1337_, 0);
v_absolute_1340_ = lean_ctor_get_uint8(v_p_1337_, sizeof(void*)*1);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_p_1337_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1342_ = v_p_1337_;
v_isShared_1343_ = v_isSharedCheck_1349_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_segments_1339_);
lean_dec(v_p_1337_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1349_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1344_ = l_Std_Http_URI_EncodedSegment_encode(v_segment_1338_);
v___x_1345_ = lean_array_push(v_segments_1339_, v___x_1344_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1345_);
v___x_1347_ = v___x_1342_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
lean_ctor_set_uint8(v_reuseFailAlloc_1348_, sizeof(void*)*1, v_absolute_1340_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_appendEncoded(lean_object* v_p_1350_, lean_object* v_segment_1351_){
_start:
{
lean_object* v_segments_1352_; uint8_t v_absolute_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1361_; 
v_segments_1352_ = lean_ctor_get(v_p_1350_, 0);
v_absolute_1353_ = lean_ctor_get_uint8(v_p_1350_, sizeof(void*)*1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_p_1350_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1355_ = v_p_1350_;
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_segments_1352_);
lean_dec(v_p_1350_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_array_push(v_segments_1352_, v_segment_1351_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1357_);
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*1, v_absolute_1353_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(lean_object* v_input_1364_, lean_object* v_output_1365_){
_start:
{
if (lean_obj_tag(v_input_1364_) == 0)
{
lean_object* v___x_1366_; 
v___x_1366_ = l_List_reverse___redArg(v_output_1365_);
return v___x_1366_;
}
else
{
lean_object* v_head_1367_; lean_object* v_tail_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1385_; 
v_head_1367_ = lean_ctor_get(v_input_1364_, 0);
v_tail_1368_ = lean_ctor_get(v_input_1364_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_input_1364_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1370_ = v_input_1364_;
v_isShared_1371_ = v_isSharedCheck_1385_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_tail_1368_);
lean_inc(v_head_1367_);
lean_dec(v_input_1364_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1385_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
lean_inc(v_head_1367_);
v___x_1372_ = lean_string_from_utf8_unchecked(v_head_1367_);
v___x_1373_ = ((lean_object*)(l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0));
v___x_1374_ = lean_string_dec_eq(v___x_1372_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = ((lean_object*)(l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1));
v___x_1376_ = lean_string_dec_eq(v___x_1372_, v___x_1375_);
lean_dec_ref(v___x_1372_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1378_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v_output_1365_);
v___x_1378_ = v___x_1370_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_head_1367_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_output_1365_);
v___x_1378_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
v_input_1364_ = v_tail_1368_;
v_output_1365_ = v___x_1378_;
goto _start;
}
}
else
{
lean_del_object(v___x_1370_);
lean_dec(v_head_1367_);
if (lean_obj_tag(v_output_1365_) == 0)
{
v_input_1364_ = v_tail_1368_;
goto _start;
}
else
{
lean_object* v_tail_1382_; 
v_tail_1382_ = lean_ctor_get(v_output_1365_, 1);
lean_inc(v_tail_1382_);
lean_dec_ref_known(v_output_1365_, 2);
v_input_1364_ = v_tail_1368_;
v_output_1365_ = v_tail_1382_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_1372_);
lean_del_object(v___x_1370_);
lean_dec(v_head_1367_);
v_input_1364_ = v_tail_1368_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_normalize(lean_object* v_p_1386_){
_start:
{
lean_object* v_segments_1387_; uint8_t v_absolute_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1399_; 
v_segments_1387_ = lean_ctor_get(v_p_1386_, 0);
v_absolute_1388_ = lean_ctor_get_uint8(v_p_1386_, sizeof(void*)*1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_p_1386_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1390_ = v_p_1386_;
v_isShared_1391_ = v_isSharedCheck_1399_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_segments_1387_);
lean_dec(v_p_1386_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1399_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1392_ = lean_array_to_list(v_segments_1387_);
v___x_1393_ = lean_box(0);
v___x_1394_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(v___x_1392_, v___x_1393_);
v___x_1395_ = lean_array_mk(v___x_1394_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1395_);
v___x_1397_ = v___x_1390_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
lean_ctor_set_uint8(v_reuseFailAlloc_1398_, sizeof(void*)*1, v_absolute_1388_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(size_t v_sz_1400_, size_t v_i_1401_, lean_object* v_bs_1402_){
_start:
{
uint8_t v___x_1403_; 
v___x_1403_ = lean_usize_dec_lt(v_i_1401_, v_sz_1400_);
if (v___x_1403_ == 0)
{
return v_bs_1402_;
}
else
{
lean_object* v_v_1404_; lean_object* v___x_1405_; lean_object* v_bs_x27_1406_; lean_object* v___y_1408_; lean_object* v___x_1413_; 
v_v_1404_ = lean_array_uget(v_bs_1402_, v_i_1401_);
v___x_1405_ = lean_unsigned_to_nat(0u);
v_bs_x27_1406_ = lean_array_uset(v_bs_1402_, v_i_1401_, v___x_1405_);
v___x_1413_ = l_Std_Http_URI_EncodedSegment_decode(v_v_1404_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_string_from_utf8_unchecked(v_v_1404_);
v___y_1408_ = v___x_1414_;
goto v___jp_1407_;
}
else
{
lean_object* v_val_1415_; 
lean_dec(v_v_1404_);
v_val_1415_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_val_1415_);
lean_dec_ref_known(v___x_1413_, 1);
v___y_1408_ = v_val_1415_;
goto v___jp_1407_;
}
v___jp_1407_:
{
size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = ((size_t)1ULL);
v___x_1410_ = lean_usize_add(v_i_1401_, v___x_1409_);
v___x_1411_ = lean_array_uset(v_bs_x27_1406_, v_i_1401_, v___y_1408_);
v_i_1401_ = v___x_1410_;
v_bs_1402_ = v___x_1411_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0___boxed(lean_object* v_sz_1416_, lean_object* v_i_1417_, lean_object* v_bs_1418_){
_start:
{
size_t v_sz_boxed_1419_; size_t v_i_boxed_1420_; lean_object* v_res_1421_; 
v_sz_boxed_1419_ = lean_unbox_usize(v_sz_1416_);
lean_dec(v_sz_1416_);
v_i_boxed_1420_ = lean_unbox_usize(v_i_1417_);
lean_dec(v_i_1417_);
v_res_1421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_boxed_1419_, v_i_boxed_1420_, v_bs_1418_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_toDecodedSegments(lean_object* v_p_1422_){
_start:
{
lean_object* v_segments_1423_; size_t v_sz_1424_; size_t v___x_1425_; lean_object* v___x_1426_; 
v_segments_1423_ = lean_ctor_get(v_p_1422_, 0);
lean_inc_ref(v_segments_1423_);
lean_dec_ref(v_p_1422_);
v_sz_1424_ = lean_array_size(v_segments_1423_);
v___x_1425_ = ((size_t)0ULL);
v___x_1426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_1424_, v___x_1425_, v_segments_1423_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___redArg(lean_object* v_xs_1435_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1437_ = l_Array_repr___redArg(v___x_1436_, v_xs_1435_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1(lean_object* v_xs_1438_, lean_object* v_x_1439_){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1441_ = l_Array_repr___redArg(v___x_1440_, v_xs_1438_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___boxed(lean_object* v_xs_1442_, lean_object* v_x_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Std_Http_URI_instReprQuery___aux__1(v_xs_1442_, v_x_1443_);
lean_dec(v_x_1443_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_){
_start:
{
if (lean_obj_tag(v_x_1447_) == 0)
{
lean_dec(v_x_1445_);
return v_x_1446_;
}
else
{
lean_object* v_head_1448_; lean_object* v_tail_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1458_; 
v_head_1448_ = lean_ctor_get(v_x_1447_, 0);
v_tail_1449_ = lean_ctor_get(v_x_1447_, 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_x_1447_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1451_ = v_x_1447_;
v_isShared_1452_ = v_isSharedCheck_1458_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_tail_1449_);
lean_inc(v_head_1448_);
lean_dec(v_x_1447_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1458_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
lean_inc(v_x_1445_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set_tag(v___x_1451_, 5);
lean_ctor_set(v___x_1451_, 1, v_x_1445_);
lean_ctor_set(v___x_1451_, 0, v_x_1446_);
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_x_1446_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_x_1445_);
v___x_1454_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
lean_ctor_set(v___x_1455_, 1, v_head_1448_);
v_x_1446_ = v___x_1455_;
v_x_1447_ = v_tail_1449_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(lean_object* v_x_1459_, lean_object* v_x_1460_){
_start:
{
if (lean_obj_tag(v_x_1459_) == 0)
{
lean_object* v___x_1461_; 
lean_dec(v_x_1460_);
v___x_1461_ = lean_box(0);
return v___x_1461_;
}
else
{
lean_object* v_tail_1462_; 
v_tail_1462_ = lean_ctor_get(v_x_1459_, 1);
if (lean_obj_tag(v_tail_1462_) == 0)
{
lean_object* v_head_1463_; 
lean_dec(v_x_1460_);
v_head_1463_ = lean_ctor_get(v_x_1459_, 0);
lean_inc(v_head_1463_);
lean_dec_ref_known(v_x_1459_, 2);
return v_head_1463_;
}
else
{
lean_object* v_head_1464_; lean_object* v___x_1465_; 
lean_inc(v_tail_1462_);
v_head_1464_ = lean_ctor_get(v_x_1459_, 0);
lean_inc(v_head_1464_);
lean_dec_ref_known(v_x_1459_, 2);
v___x_1465_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(v_x_1460_, v_head_1464_, v_tail_1462_);
return v___x_1465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(lean_object* v_x_1466_, lean_object* v_x_1467_){
_start:
{
if (lean_obj_tag(v_x_1466_) == 0)
{
lean_object* v___x_1468_; 
v___x_1468_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1468_;
}
else
{
lean_object* v_val_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1481_; 
v_val_1469_ = lean_ctor_get(v_x_1466_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_x_1466_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1471_ = v_x_1466_;
v_isShared_1472_ = v_isSharedCheck_1481_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_val_1469_);
lean_dec(v_x_1466_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1481_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1473_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1474_ = lean_string_from_utf8_unchecked(v_val_1469_);
v___x_1475_ = l_String_quote(v___x_1474_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set_tag(v___x_1471_, 3);
lean_ctor_set(v___x_1471_, 0, v___x_1475_);
v___x_1477_ = v___x_1471_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1473_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = l_Repr_addAppParen(v___x_1478_, v_x_1467_);
return v___x_1479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1482_, lean_object* v_x_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_x_1482_, v_x_1483_);
lean_dec(v_x_1483_);
return v_res_1484_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0));
v___x_1488_ = lean_string_length(v___x_1487_);
return v___x_1488_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2);
v___x_1490_ = lean_nat_to_int(v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(lean_object* v_x_1495_){
_start:
{
lean_object* v_fst_1496_; lean_object* v_snd_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1522_; 
v_fst_1496_ = lean_ctor_get(v_x_1495_, 0);
v_snd_1497_ = lean_ctor_get(v_x_1495_, 1);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_x_1495_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1499_ = v_x_1495_;
v_isShared_1500_ = v_isSharedCheck_1522_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_snd_1497_);
lean_inc(v_fst_1496_);
lean_dec(v_x_1495_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1522_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1501_ = lean_string_from_utf8_unchecked(v_fst_1496_);
v___x_1502_ = l_String_quote(v___x_1501_);
v___x_1503_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
v___x_1504_ = lean_box(0);
if (v_isShared_1500_ == 0)
{
lean_ctor_set_tag(v___x_1499_, 1);
lean_ctor_set(v___x_1499_, 1, v___x_1504_);
lean_ctor_set(v___x_1499_, 0, v___x_1503_);
v___x_1506_ = v___x_1499_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; lean_object* v___x_1520_; 
v___x_1507_ = lean_unsigned_to_nat(0u);
v___x_1508_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_snd_1497_, v___x_1507_);
v___x_1509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set(v___x_1509_, 1, v___x_1506_);
v___x_1510_ = l_List_reverse___redArg(v___x_1509_);
v___x_1511_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1512_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(v___x_1510_, v___x_1511_);
v___x_1513_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3);
v___x_1514_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4));
v___x_1515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
lean_ctor_set(v___x_1515_, 1, v___x_1512_);
v___x_1516_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5));
v___x_1517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1515_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
v___x_1518_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1513_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v___x_1519_ = 0;
v___x_1520_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1520_, 0, v___x_1518_);
lean_ctor_set_uint8(v___x_1520_, sizeof(void*)*1, v___x_1519_);
return v___x_1520_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(lean_object* v_x_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_){
_start:
{
if (lean_obj_tag(v_x_1525_) == 0)
{
lean_dec(v_x_1523_);
return v_x_1524_;
}
else
{
lean_object* v_head_1526_; lean_object* v_tail_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1537_; 
v_head_1526_ = lean_ctor_get(v_x_1525_, 0);
v_tail_1527_ = lean_ctor_get(v_x_1525_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_x_1525_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1529_ = v_x_1525_;
v_isShared_1530_ = v_isSharedCheck_1537_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_tail_1527_);
lean_inc(v_head_1526_);
lean_dec(v_x_1525_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1537_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
lean_inc(v_x_1523_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set_tag(v___x_1529_, 5);
lean_ctor_set(v___x_1529_, 1, v_x_1523_);
lean_ctor_set(v___x_1529_, 0, v_x_1524_);
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_x_1524_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_x_1523_);
v___x_1532_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1526_);
v___x_1534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1532_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v_x_1524_ = v___x_1534_;
v_x_1525_ = v_tail_1527_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(lean_object* v_x_1538_, lean_object* v_x_1539_, lean_object* v_x_1540_){
_start:
{
if (lean_obj_tag(v_x_1540_) == 0)
{
lean_dec(v_x_1538_);
return v_x_1539_;
}
else
{
lean_object* v_head_1541_; lean_object* v_tail_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1552_; 
v_head_1541_ = lean_ctor_get(v_x_1540_, 0);
v_tail_1542_ = lean_ctor_get(v_x_1540_, 1);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_x_1540_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1544_ = v_x_1540_;
v_isShared_1545_ = v_isSharedCheck_1552_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_tail_1542_);
lean_inc(v_head_1541_);
lean_dec(v_x_1540_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1552_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
lean_inc(v_x_1538_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set_tag(v___x_1544_, 5);
lean_ctor_set(v___x_1544_, 1, v_x_1538_);
lean_ctor_set(v___x_1544_, 0, v_x_1539_);
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_x_1539_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_x_1538_);
v___x_1547_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1541_);
v___x_1549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(v_x_1538_, v___x_1549_, v_tail_1542_);
return v___x_1550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(lean_object* v_x_1553_, lean_object* v_x_1554_){
_start:
{
if (lean_obj_tag(v_x_1553_) == 0)
{
lean_object* v___x_1555_; 
lean_dec(v_x_1554_);
v___x_1555_ = lean_box(0);
return v___x_1555_;
}
else
{
lean_object* v_tail_1556_; 
v_tail_1556_ = lean_ctor_get(v_x_1553_, 1);
if (lean_obj_tag(v_tail_1556_) == 0)
{
lean_object* v_head_1557_; lean_object* v___x_1558_; 
lean_dec(v_x_1554_);
v_head_1557_ = lean_ctor_get(v_x_1553_, 0);
lean_inc(v_head_1557_);
lean_dec_ref_known(v_x_1553_, 2);
v___x_1558_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1557_);
return v___x_1558_;
}
else
{
lean_object* v_head_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_inc(v_tail_1556_);
v_head_1559_ = lean_ctor_get(v_x_1553_, 0);
lean_inc(v_head_1559_);
lean_dec_ref_known(v_x_1553_, 2);
v___x_1560_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1559_);
v___x_1561_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(v_x_1554_, v___x_1560_, v_tail_1556_);
return v___x_1561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(lean_object* v_xs_1562_){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1563_ = lean_array_get_size(v_xs_1562_);
v___x_1564_ = lean_unsigned_to_nat(0u);
v___x_1565_ = lean_nat_dec_eq(v___x_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1566_ = lean_array_to_list(v_xs_1562_);
v___x_1567_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1568_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(v___x_1566_, v___x_1567_);
v___x_1569_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1570_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v___x_1568_);
v___x_1572_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1569_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = l_Std_Format_fill(v___x_1574_);
return v___x_1575_;
}
else
{
lean_object* v___x_1576_; 
lean_dec_ref(v_xs_1562_);
v___x_1576_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1576_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0(lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v___y_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0___boxed(lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Std_Http_URI_instReprQuery___lam__0(v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(lean_object* v_x_1585_, lean_object* v_x_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_x_1585_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___boxed(lean_object* v_x_1588_, lean_object* v_x_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(v_x_1588_, v_x_1589_);
lean_dec(v_x_1589_);
return v_res_1590_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1___lam__0(lean_object* v___f_1595_, lean_object* v_x_1596_, lean_object* v_x_1597_){
_start:
{
lean_object* v_fst_1598_; lean_object* v_snd_1599_; lean_object* v_fst_1600_; lean_object* v_snd_1601_; uint8_t v___x_1602_; 
v_fst_1598_ = lean_ctor_get(v_x_1596_, 0);
lean_inc(v_fst_1598_);
v_snd_1599_ = lean_ctor_get(v_x_1596_, 1);
lean_inc(v_snd_1599_);
lean_dec_ref(v_x_1596_);
v_fst_1600_ = lean_ctor_get(v_x_1597_, 0);
lean_inc(v_fst_1600_);
v_snd_1601_ = lean_ctor_get(v_x_1597_, 1);
lean_inc(v_snd_1601_);
lean_dec_ref(v_x_1597_);
v___x_1602_ = lean_sarray_dec_eq(v_fst_1598_, v_fst_1600_);
lean_dec(v_fst_1600_);
lean_dec(v_fst_1598_);
if (v___x_1602_ == 0)
{
lean_dec(v_snd_1601_);
lean_dec(v_snd_1599_);
lean_dec_ref(v___f_1595_);
return v___x_1602_;
}
else
{
uint8_t v___x_1603_; 
v___x_1603_ = l_instBEqOption_beq___redArg(v___f_1595_, v_snd_1599_, v_snd_1601_);
return v___x_1603_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___lam__0___boxed(lean_object* v___f_1604_, lean_object* v_x_1605_, lean_object* v_x_1606_){
_start:
{
uint8_t v_res_1607_; lean_object* v_r_1608_; 
v_res_1607_ = l_Std_Http_URI_instBEqQuery___aux__1___lam__0(v___f_1604_, v_x_1605_, v_x_1606_);
v_r_1608_ = lean_box(v_res_1607_);
return v_r_1608_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1(lean_object* v_xs_1612_, lean_object* v_ys_1613_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1614_ = lean_array_get_size(v_xs_1612_);
v___x_1615_ = lean_array_get_size(v_ys_1613_);
v___x_1616_ = lean_nat_dec_eq(v___x_1614_, v___x_1615_);
if (v___x_1616_ == 0)
{
return v___x_1616_;
}
else
{
lean_object* v___f_1617_; uint8_t v___x_1618_; 
v___f_1617_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__1));
v___x_1618_ = l_Array_isEqvAux___redArg(v_xs_1612_, v_ys_1613_, v___f_1617_, v___x_1614_);
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___boxed(lean_object* v_xs_1619_, lean_object* v_ys_1620_){
_start:
{
uint8_t v_res_1621_; lean_object* v_r_1622_; 
v_res_1621_ = l_Std_Http_URI_instBEqQuery___aux__1(v_xs_1619_, v_ys_1620_);
lean_dec_ref(v_ys_1620_);
lean_dec_ref(v_xs_1619_);
v_r_1622_ = lean_box(v_res_1621_);
return v_r_1622_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(lean_object* v_x_1623_, lean_object* v_x_1624_){
_start:
{
if (lean_obj_tag(v_x_1623_) == 0)
{
if (lean_obj_tag(v_x_1624_) == 0)
{
uint8_t v___x_1625_; 
v___x_1625_ = 1;
return v___x_1625_;
}
else
{
uint8_t v___x_1626_; 
v___x_1626_ = 0;
return v___x_1626_;
}
}
else
{
if (lean_obj_tag(v_x_1624_) == 0)
{
uint8_t v___x_1627_; 
v___x_1627_ = 0;
return v___x_1627_;
}
else
{
lean_object* v_val_1628_; lean_object* v_val_1629_; uint8_t v___x_1630_; 
v_val_1628_ = lean_ctor_get(v_x_1623_, 0);
v_val_1629_ = lean_ctor_get(v_x_1624_, 0);
v___x_1630_ = lean_sarray_dec_eq(v_val_1628_, v_val_1629_);
return v___x_1630_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0___boxed(lean_object* v_x_1631_, lean_object* v_x_1632_){
_start:
{
uint8_t v_res_1633_; lean_object* v_r_1634_; 
v_res_1633_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_x_1631_, v_x_1632_);
lean_dec(v_x_1632_);
lean_dec(v_x_1631_);
v_r_1634_ = lean_box(v_res_1633_);
return v_r_1634_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(lean_object* v_xs_1635_, lean_object* v_ys_1636_, lean_object* v_x_1637_){
_start:
{
lean_object* v_zero_1638_; uint8_t v_isZero_1639_; 
v_zero_1638_ = lean_unsigned_to_nat(0u);
v_isZero_1639_ = lean_nat_dec_eq(v_x_1637_, v_zero_1638_);
if (v_isZero_1639_ == 1)
{
lean_dec(v_x_1637_);
return v_isZero_1639_;
}
else
{
lean_object* v_one_1640_; lean_object* v_n_1641_; lean_object* v___x_1642_; lean_object* v_fst_1643_; lean_object* v_snd_1644_; lean_object* v___x_1645_; lean_object* v_fst_1646_; lean_object* v_snd_1647_; uint8_t v___x_1648_; 
v_one_1640_ = lean_unsigned_to_nat(1u);
v_n_1641_ = lean_nat_sub(v_x_1637_, v_one_1640_);
lean_dec(v_x_1637_);
v___x_1642_ = lean_array_fget_borrowed(v_xs_1635_, v_n_1641_);
v_fst_1643_ = lean_ctor_get(v___x_1642_, 0);
v_snd_1644_ = lean_ctor_get(v___x_1642_, 1);
v___x_1645_ = lean_array_fget_borrowed(v_ys_1636_, v_n_1641_);
v_fst_1646_ = lean_ctor_get(v___x_1645_, 0);
v_snd_1647_ = lean_ctor_get(v___x_1645_, 1);
v___x_1648_ = lean_sarray_dec_eq(v_fst_1643_, v_fst_1646_);
if (v___x_1648_ == 0)
{
lean_dec(v_n_1641_);
return v___x_1648_;
}
else
{
uint8_t v___x_1649_; 
v___x_1649_ = l_instBEqOption_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_snd_1644_, v_snd_1647_);
if (v___x_1649_ == 0)
{
lean_dec(v_n_1641_);
return v___x_1649_;
}
else
{
v_x_1637_ = v_n_1641_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg___boxed(lean_object* v_xs_1651_, lean_object* v_ys_1652_, lean_object* v_x_1653_){
_start:
{
uint8_t v_res_1654_; lean_object* v_r_1655_; 
v_res_1654_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1651_, v_ys_1652_, v_x_1653_);
lean_dec_ref(v_ys_1652_);
lean_dec_ref(v_xs_1651_);
v_r_1655_ = lean_box(v_res_1654_);
return v_r_1655_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___lam__0(lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
v___x_1658_ = lean_array_get_size(v___y_1656_);
v___x_1659_ = lean_array_get_size(v___y_1657_);
v___x_1660_ = lean_nat_dec_eq(v___x_1658_, v___x_1659_);
if (v___x_1660_ == 0)
{
return v___x_1660_;
}
else
{
uint8_t v___x_1661_; 
v___x_1661_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v___y_1656_, v___y_1657_, v___x_1658_);
return v___x_1661_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___lam__0___boxed(lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
uint8_t v_res_1664_; lean_object* v_r_1665_; 
v_res_1664_ = l_Std_Http_URI_instBEqQuery___lam__0(v___y_1662_, v___y_1663_);
lean_dec_ref(v___y_1663_);
lean_dec_ref(v___y_1662_);
v_r_1665_ = lean_box(v_res_1664_);
return v_r_1665_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(lean_object* v_xs_1668_, lean_object* v_ys_1669_, lean_object* v_hsz_1670_, lean_object* v_x_1671_, lean_object* v_x_1672_){
_start:
{
uint8_t v___x_1673_; 
v___x_1673_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1668_, v_ys_1669_, v_x_1671_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___boxed(lean_object* v_xs_1674_, lean_object* v_ys_1675_, lean_object* v_hsz_1676_, lean_object* v_x_1677_, lean_object* v_x_1678_){
_start:
{
uint8_t v_res_1679_; lean_object* v_r_1680_; 
v_res_1679_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(v_xs_1674_, v_ys_1675_, v_hsz_1676_, v_x_1677_, v_x_1678_);
lean_dec_ref(v_ys_1675_);
lean_dec_ref(v_xs_1674_);
v_r_1680_ = lean_box(v_res_1679_);
return v_r_1680_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(lean_object* v_as_1681_){
_start:
{
lean_object* v___f_1682_; lean_object* v___x_1683_; 
v___f_1682_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__0));
v___x_1683_ = l_List_eraseDupsBy___redArg(v___f_1682_, v_as_1681_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(size_t v_sz_1684_, size_t v_i_1685_, lean_object* v_bs_1686_){
_start:
{
uint8_t v___x_1687_; 
v___x_1687_ = lean_usize_dec_lt(v_i_1685_, v_sz_1684_);
if (v___x_1687_ == 0)
{
return v_bs_1686_;
}
else
{
lean_object* v_v_1688_; lean_object* v_fst_1689_; lean_object* v___x_1690_; lean_object* v_bs_x27_1691_; size_t v___x_1692_; size_t v___x_1693_; lean_object* v___x_1694_; 
v_v_1688_ = lean_array_uget_borrowed(v_bs_1686_, v_i_1685_);
v_fst_1689_ = lean_ctor_get(v_v_1688_, 0);
lean_inc(v_fst_1689_);
v___x_1690_ = lean_unsigned_to_nat(0u);
v_bs_x27_1691_ = lean_array_uset(v_bs_1686_, v_i_1685_, v___x_1690_);
v___x_1692_ = ((size_t)1ULL);
v___x_1693_ = lean_usize_add(v_i_1685_, v___x_1692_);
v___x_1694_ = lean_array_uset(v_bs_x27_1691_, v_i_1685_, v_fst_1689_);
v_i_1685_ = v___x_1693_;
v_bs_1686_ = v___x_1694_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0___boxed(lean_object* v_sz_1696_, lean_object* v_i_1697_, lean_object* v_bs_1698_){
_start:
{
size_t v_sz_boxed_1699_; size_t v_i_boxed_1700_; lean_object* v_res_1701_; 
v_sz_boxed_1699_ = lean_unbox_usize(v_sz_1696_);
lean_dec(v_sz_1696_);
v_i_boxed_1700_ = lean_unbox_usize(v_i_1697_);
lean_dec(v_i_1697_);
v_res_1701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_boxed_1699_, v_i_boxed_1700_, v_bs_1698_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names(lean_object* v_query_1702_){
_start:
{
size_t v_sz_1703_; size_t v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_sz_1703_ = lean_array_size(v_query_1702_);
v___x_1704_ = ((size_t)0ULL);
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_1703_, v___x_1704_, v_query_1702_);
v___x_1706_ = lean_array_to_list(v___x_1705_);
v___x_1707_ = l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(v___x_1706_);
v___x_1708_ = lean_array_mk(v___x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(size_t v_sz_1709_, size_t v_i_1710_, lean_object* v_bs_1711_){
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
lean_object* v_v_1713_; lean_object* v_snd_1714_; lean_object* v___x_1715_; lean_object* v_bs_x27_1716_; size_t v___x_1717_; size_t v___x_1718_; lean_object* v___x_1719_; 
v_v_1713_ = lean_array_uget_borrowed(v_bs_1711_, v_i_1710_);
v_snd_1714_ = lean_ctor_get(v_v_1713_, 1);
lean_inc(v_snd_1714_);
v___x_1715_ = lean_unsigned_to_nat(0u);
v_bs_x27_1716_ = lean_array_uset(v_bs_1711_, v_i_1710_, v___x_1715_);
v___x_1717_ = ((size_t)1ULL);
v___x_1718_ = lean_usize_add(v_i_1710_, v___x_1717_);
v___x_1719_ = lean_array_uset(v_bs_x27_1716_, v_i_1710_, v_snd_1714_);
v_i_1710_ = v___x_1718_;
v_bs_1711_ = v___x_1719_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0___boxed(lean_object* v_sz_1721_, lean_object* v_i_1722_, lean_object* v_bs_1723_){
_start:
{
size_t v_sz_boxed_1724_; size_t v_i_boxed_1725_; lean_object* v_res_1726_; 
v_sz_boxed_1724_ = lean_unbox_usize(v_sz_1721_);
lean_dec(v_sz_1721_);
v_i_boxed_1725_ = lean_unbox_usize(v_i_1722_);
lean_dec(v_i_1722_);
v_res_1726_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_boxed_1724_, v_i_boxed_1725_, v_bs_1723_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_values(lean_object* v_query_1727_){
_start:
{
size_t v_sz_1728_; size_t v___x_1729_; lean_object* v___x_1730_; 
v_sz_1728_ = lean_array_size(v_query_1727_);
v___x_1729_ = ((size_t)0ULL);
v___x_1730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_1728_, v___x_1729_, v_query_1727_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray(lean_object* v_query_1731_){
_start:
{
lean_inc_ref(v_query_1731_);
return v_query_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray___boxed(lean_object* v_query_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Std_Http_URI_Query_toArray(v_query_1732_);
lean_dec_ref(v_query_1732_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object* v_key_1735_, lean_object* v_value_1736_){
_start:
{
if (lean_obj_tag(v_value_1736_) == 0)
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_string_from_utf8_unchecked(v_key_1735_);
return v___x_1737_;
}
else
{
lean_object* v_val_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_val_1738_ = lean_ctor_get(v_value_1736_, 0);
lean_inc(v_val_1738_);
lean_dec_ref_known(v_value_1736_, 1);
v___x_1739_ = lean_string_from_utf8_unchecked(v_key_1735_);
v___x_1740_ = ((lean_object*)(l_Std_Http_URI_Query_formatQueryParam___closed__0));
v___x_1741_ = lean_string_append(v___x_1739_, v___x_1740_);
v___x_1742_ = lean_string_from_utf8_unchecked(v_val_1738_);
v___x_1743_ = lean_string_append(v___x_1741_, v___x_1742_);
lean_dec_ref(v___x_1742_);
return v___x_1743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(lean_object* v_key_1747_, lean_object* v_as_1748_, size_t v_sz_1749_, size_t v_i_1750_, lean_object* v_b_1751_){
_start:
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_usize_dec_lt(v_i_1750_, v_sz_1749_);
if (v___x_1752_ == 0)
{
lean_inc_ref(v_b_1751_);
return v_b_1751_;
}
else
{
lean_object* v_a_1753_; lean_object* v_fst_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v_a_1753_ = lean_array_uget_borrowed(v_as_1748_, v_i_1750_);
v_fst_1754_ = lean_ctor_get(v_a_1753_, 0);
v___x_1755_ = lean_box(0);
v___x_1756_ = lean_sarray_dec_eq(v_fst_1754_, v_key_1747_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; size_t v___x_1758_; size_t v___x_1759_; 
v___x_1757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v___x_1758_ = ((size_t)1ULL);
v___x_1759_ = lean_usize_add(v_i_1750_, v___x_1758_);
v_i_1750_ = v___x_1759_;
v_b_1751_ = v___x_1757_;
goto _start;
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_inc(v_a_1753_);
v___x_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_a_1753_);
v___x_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v___x_1755_);
return v___x_1763_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___boxed(lean_object* v_key_1764_, lean_object* v_as_1765_, lean_object* v_sz_1766_, lean_object* v_i_1767_, lean_object* v_b_1768_){
_start:
{
size_t v_sz_boxed_1769_; size_t v_i_boxed_1770_; lean_object* v_res_1771_; 
v_sz_boxed_1769_ = lean_unbox_usize(v_sz_1766_);
lean_dec(v_sz_1766_);
v_i_boxed_1770_ = lean_unbox_usize(v_i_1767_);
lean_dec(v_i_1767_);
v_res_1771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1764_, v_as_1765_, v_sz_boxed_1769_, v_i_boxed_1770_, v_b_1768_);
lean_dec_ref(v_b_1768_);
lean_dec_ref(v_as_1765_);
lean_dec_ref(v_key_1764_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f(lean_object* v_query_1772_, lean_object* v_key_1773_){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; size_t v_sz_1776_; size_t v___x_1777_; lean_object* v___x_1778_; lean_object* v_fst_1779_; 
v___x_1774_ = lean_box(0);
v___x_1775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v_sz_1776_ = lean_array_size(v_query_1772_);
v___x_1777_ = ((size_t)0ULL);
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1773_, v_query_1772_, v_sz_1776_, v___x_1777_, v___x_1775_);
v_fst_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_fst_1779_);
lean_dec_ref(v___x_1778_);
if (lean_obj_tag(v_fst_1779_) == 0)
{
return v___x_1774_;
}
else
{
lean_object* v_val_1780_; 
v_val_1780_ = lean_ctor_get(v_fst_1779_, 0);
lean_inc(v_val_1780_);
lean_dec_ref_known(v_fst_1779_, 1);
if (lean_obj_tag(v_val_1780_) == 0)
{
return v___x_1774_;
}
else
{
lean_object* v_val_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1789_; 
v_val_1781_ = lean_ctor_get(v_val_1780_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_val_1780_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1783_ = v_val_1780_;
v_isShared_1784_ = v_isSharedCheck_1789_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_val_1781_);
lean_dec(v_val_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1789_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v_snd_1785_; lean_object* v___x_1787_; 
v_snd_1785_ = lean_ctor_get(v_val_1781_, 1);
lean_inc(v_snd_1785_);
lean_dec(v_val_1781_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v_snd_1785_);
v___x_1787_ = v___x_1783_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_snd_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f___boxed(lean_object* v_query_1790_, lean_object* v_key_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1790_, v_key_1791_);
lean_dec_ref(v_key_1791_);
lean_dec_ref(v_query_1790_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f(lean_object* v_query_1793_, lean_object* v_key_1794_){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1794_);
v___x_1796_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1793_, v___x_1795_);
lean_dec_ref(v___x_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f___boxed(lean_object* v_query_1797_, lean_object* v_key_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Std_Http_URI_Query_find_x3f(v_query_1797_, v_key_1798_);
lean_dec_ref(v_query_1797_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(lean_object* v_key_1800_, lean_object* v_as_1801_, size_t v_i_1802_, size_t v_stop_1803_, lean_object* v_b_1804_){
_start:
{
lean_object* v___y_1806_; uint8_t v___x_1810_; 
v___x_1810_ = lean_usize_dec_eq(v_i_1802_, v_stop_1803_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; lean_object* v_fst_1812_; lean_object* v_snd_1813_; uint8_t v___x_1814_; 
v___x_1811_ = lean_array_uget_borrowed(v_as_1801_, v_i_1802_);
v_fst_1812_ = lean_ctor_get(v___x_1811_, 0);
v_snd_1813_ = lean_ctor_get(v___x_1811_, 1);
v___x_1814_ = lean_sarray_dec_eq(v_fst_1812_, v_key_1800_);
if (v___x_1814_ == 0)
{
v___y_1806_ = v_b_1804_;
goto v___jp_1805_;
}
else
{
lean_object* v___x_1815_; 
lean_inc(v_snd_1813_);
v___x_1815_ = lean_array_push(v_b_1804_, v_snd_1813_);
v___y_1806_ = v___x_1815_;
goto v___jp_1805_;
}
}
else
{
return v_b_1804_;
}
v___jp_1805_:
{
size_t v___x_1807_; size_t v___x_1808_; 
v___x_1807_ = ((size_t)1ULL);
v___x_1808_ = lean_usize_add(v_i_1802_, v___x_1807_);
v_i_1802_ = v___x_1808_;
v_b_1804_ = v___y_1806_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0___boxed(lean_object* v_key_1816_, lean_object* v_as_1817_, lean_object* v_i_1818_, lean_object* v_stop_1819_, lean_object* v_b_1820_){
_start:
{
size_t v_i_boxed_1821_; size_t v_stop_boxed_1822_; lean_object* v_res_1823_; 
v_i_boxed_1821_ = lean_unbox_usize(v_i_1818_);
lean_dec(v_i_1818_);
v_stop_boxed_1822_ = lean_unbox_usize(v_stop_1819_);
lean_dec(v_stop_1819_);
v_res_1823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1816_, v_as_1817_, v_i_boxed_1821_, v_stop_boxed_1822_, v_b_1820_);
lean_dec_ref(v_as_1817_);
lean_dec_ref(v_key_1816_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(lean_object* v_key_1826_, lean_object* v_as_1827_, lean_object* v_start_1828_, lean_object* v_stop_1829_){
_start:
{
lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_1831_ = lean_nat_dec_lt(v_start_1828_, v_stop_1829_);
if (v___x_1831_ == 0)
{
return v___x_1830_;
}
else
{
lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1832_ = lean_array_get_size(v_as_1827_);
v___x_1833_ = lean_nat_dec_le(v_stop_1829_, v___x_1832_);
if (v___x_1833_ == 0)
{
uint8_t v___x_1834_; 
v___x_1834_ = lean_nat_dec_lt(v_start_1828_, v___x_1832_);
if (v___x_1834_ == 0)
{
return v___x_1830_;
}
else
{
size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = lean_usize_of_nat(v_start_1828_);
v___x_1836_ = lean_usize_of_nat(v___x_1832_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1826_, v_as_1827_, v___x_1835_, v___x_1836_, v___x_1830_);
return v___x_1837_;
}
}
else
{
size_t v___x_1838_; size_t v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = lean_usize_of_nat(v_start_1828_);
v___x_1839_ = lean_usize_of_nat(v_stop_1829_);
v___x_1840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1826_, v_as_1827_, v___x_1838_, v___x_1839_, v___x_1830_);
return v___x_1840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___boxed(lean_object* v_key_1841_, lean_object* v_as_1842_, lean_object* v_start_1843_, lean_object* v_stop_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1841_, v_as_1842_, v_start_1843_, v_stop_1844_);
lean_dec(v_stop_1844_);
lean_dec(v_start_1843_);
lean_dec_ref(v_as_1842_);
lean_dec_ref(v_key_1841_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded(lean_object* v_query_1846_, lean_object* v_key_1847_){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = lean_array_get_size(v_query_1846_);
v___x_1850_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1847_, v_query_1846_, v___x_1848_, v___x_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded___boxed(lean_object* v_query_1851_, lean_object* v_key_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1851_, v_key_1852_);
lean_dec_ref(v_key_1852_);
lean_dec_ref(v_query_1851_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll(lean_object* v_query_1854_, lean_object* v_key_1855_){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1855_);
v___x_1857_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1854_, v___x_1856_);
lean_dec_ref(v___x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll___boxed(lean_object* v_query_1858_, lean_object* v_key_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Std_Http_URI_Query_findAll(v_query_1858_, v_key_1859_);
lean_dec_ref(v_query_1858_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert(lean_object* v_query_1861_, lean_object* v_key_1862_, lean_object* v_value_1863_){
_start:
{
lean_object* v_encodedKey_1864_; lean_object* v_encodedValue_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v_encodedKey_1864_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1862_);
v_encodedValue_1865_ = l_Std_Http_URI_EncodedQueryParam_encode(v_value_1863_);
v___x_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1866_, 0, v_encodedValue_1865_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v_encodedKey_1864_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_array_push(v_query_1861_, v___x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object* v_query_1869_, lean_object* v_key_1870_, lean_object* v_value_1871_){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v_key_1870_);
lean_ctor_set(v___x_1872_, 1, v_value_1871_);
v___x_1873_ = lean_array_push(v_query_1869_, v___x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_ofList(lean_object* v_pairs_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_array_mk(v_pairs_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(lean_object* v_key_1879_, lean_object* v_as_1880_, size_t v_i_1881_, size_t v_stop_1882_){
_start:
{
uint8_t v___x_1883_; 
v___x_1883_ = lean_usize_dec_eq(v_i_1881_, v_stop_1882_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v_fst_1885_; uint8_t v___x_1886_; 
v___x_1884_ = lean_array_uget_borrowed(v_as_1880_, v_i_1881_);
v_fst_1885_ = lean_ctor_get(v___x_1884_, 0);
v___x_1886_ = lean_sarray_dec_eq(v_fst_1885_, v_key_1879_);
if (v___x_1886_ == 0)
{
size_t v___x_1887_; size_t v___x_1888_; 
v___x_1887_ = ((size_t)1ULL);
v___x_1888_ = lean_usize_add(v_i_1881_, v___x_1887_);
v_i_1881_ = v___x_1888_;
goto _start;
}
else
{
return v___x_1886_;
}
}
else
{
uint8_t v___x_1890_; 
v___x_1890_ = 0;
return v___x_1890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(lean_object* v_key_1891_, lean_object* v_as_1892_, lean_object* v_i_1893_, lean_object* v_stop_1894_){
_start:
{
size_t v_i_boxed_1895_; size_t v_stop_boxed_1896_; uint8_t v_res_1897_; lean_object* v_r_1898_; 
v_i_boxed_1895_ = lean_unbox_usize(v_i_1893_);
lean_dec(v_i_1893_);
v_stop_boxed_1896_ = lean_unbox_usize(v_stop_1894_);
lean_dec(v_stop_1894_);
v_res_1897_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1891_, v_as_1892_, v_i_boxed_1895_, v_stop_boxed_1896_);
lean_dec_ref(v_as_1892_);
lean_dec_ref(v_key_1891_);
v_r_1898_ = lean_box(v_res_1897_);
return v_r_1898_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_containsEncoded(lean_object* v_query_1899_, lean_object* v_key_1900_){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v___x_1901_ = lean_unsigned_to_nat(0u);
v___x_1902_ = lean_array_get_size(v_query_1899_);
v___x_1903_ = lean_nat_dec_lt(v___x_1901_, v___x_1902_);
if (v___x_1903_ == 0)
{
return v___x_1903_;
}
else
{
if (v___x_1903_ == 0)
{
return v___x_1903_;
}
else
{
size_t v___x_1904_; size_t v___x_1905_; uint8_t v___x_1906_; 
v___x_1904_ = ((size_t)0ULL);
v___x_1905_ = lean_usize_of_nat(v___x_1902_);
v___x_1906_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1900_, v_query_1899_, v___x_1904_, v___x_1905_);
return v___x_1906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_containsEncoded___boxed(lean_object* v_query_1907_, lean_object* v_key_1908_){
_start:
{
uint8_t v_res_1909_; lean_object* v_r_1910_; 
v_res_1909_ = l_Std_Http_URI_Query_containsEncoded(v_query_1907_, v_key_1908_);
lean_dec_ref(v_key_1908_);
lean_dec_ref(v_query_1907_);
v_r_1910_ = lean_box(v_res_1909_);
return v_r_1910_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_contains(lean_object* v_query_1911_, lean_object* v_key_1912_){
_start:
{
lean_object* v___x_1913_; uint8_t v___x_1914_; 
v___x_1913_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1912_);
v___x_1914_ = l_Std_Http_URI_Query_containsEncoded(v_query_1911_, v___x_1913_);
lean_dec_ref(v___x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_contains___boxed(lean_object* v_query_1915_, lean_object* v_key_1916_){
_start:
{
uint8_t v_res_1917_; lean_object* v_r_1918_; 
v_res_1917_ = l_Std_Http_URI_Query_contains(v_query_1915_, v_key_1916_);
lean_dec_ref(v_query_1915_);
v_r_1918_ = lean_box(v_res_1917_);
return v_r_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(lean_object* v_key_1919_, lean_object* v_as_1920_, size_t v_i_1921_, size_t v_stop_1922_, lean_object* v_b_1923_){
_start:
{
lean_object* v___y_1925_; uint8_t v___x_1929_; 
v___x_1929_ = lean_usize_dec_eq(v_i_1921_, v_stop_1922_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; lean_object* v_fst_1931_; uint8_t v___x_1932_; 
v___x_1930_ = lean_array_uget_borrowed(v_as_1920_, v_i_1921_);
v_fst_1931_ = lean_ctor_get(v___x_1930_, 0);
v___x_1932_ = lean_sarray_dec_eq(v_fst_1931_, v_key_1919_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; 
lean_inc(v___x_1930_);
v___x_1933_ = lean_array_push(v_b_1923_, v___x_1930_);
v___y_1925_ = v___x_1933_;
goto v___jp_1924_;
}
else
{
v___y_1925_ = v_b_1923_;
goto v___jp_1924_;
}
}
else
{
return v_b_1923_;
}
v___jp_1924_:
{
size_t v___x_1926_; size_t v___x_1927_; 
v___x_1926_ = ((size_t)1ULL);
v___x_1927_ = lean_usize_add(v_i_1921_, v___x_1926_);
v_i_1921_ = v___x_1927_;
v_b_1923_ = v___y_1925_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(lean_object* v_key_1934_, lean_object* v_as_1935_, lean_object* v_i_1936_, lean_object* v_stop_1937_, lean_object* v_b_1938_){
_start:
{
size_t v_i_boxed_1939_; size_t v_stop_boxed_1940_; lean_object* v_res_1941_; 
v_i_boxed_1939_ = lean_unbox_usize(v_i_1936_);
lean_dec(v_i_1936_);
v_stop_boxed_1940_ = lean_unbox_usize(v_stop_1937_);
lean_dec(v_stop_1937_);
v_res_1941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1934_, v_as_1935_, v_i_boxed_1939_, v_stop_boxed_1940_, v_b_1938_);
lean_dec_ref(v_as_1935_);
lean_dec_ref(v_key_1934_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded(lean_object* v_query_1942_, lean_object* v_key_1943_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; 
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = lean_array_get_size(v_query_1942_);
v___x_1946_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_1947_ = lean_nat_dec_lt(v___x_1944_, v___x_1945_);
if (v___x_1947_ == 0)
{
return v___x_1946_;
}
else
{
size_t v___x_1948_; size_t v___x_1949_; lean_object* v___x_1950_; 
v___x_1948_ = ((size_t)0ULL);
v___x_1949_ = lean_usize_of_nat(v___x_1945_);
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1943_, v_query_1942_, v___x_1948_, v___x_1949_, v___x_1946_);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded___boxed(lean_object* v_query_1951_, lean_object* v_key_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Std_Http_URI_Query_eraseEncoded(v_query_1951_, v_key_1952_);
lean_dec_ref(v_key_1952_);
lean_dec_ref(v_query_1951_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase(lean_object* v_query_1954_, lean_object* v_key_1955_){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1955_);
v___x_1957_ = l_Std_Http_URI_Query_eraseEncoded(v_query_1954_, v___x_1956_);
lean_dec_ref(v___x_1956_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase___boxed(lean_object* v_query_1958_, lean_object* v_key_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Std_Http_URI_Query_erase(v_query_1958_, v_key_1959_);
lean_dec_ref(v_query_1958_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get(lean_object* v_query_1963_, lean_object* v_key_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Std_Http_URI_Query_find_x3f(v_query_1963_, v_key_1964_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v___x_1966_; 
v___x_1966_ = lean_box(0);
return v___x_1966_;
}
else
{
lean_object* v_val_1967_; 
v_val_1967_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_val_1967_);
lean_dec_ref_known(v___x_1965_, 1);
if (lean_obj_tag(v_val_1967_) == 0)
{
lean_object* v___x_1968_; 
v___x_1968_ = ((lean_object*)(l_Std_Http_URI_Query_get___closed__0));
return v___x_1968_;
}
else
{
lean_object* v_val_1969_; lean_object* v___x_1970_; 
v_val_1969_ = lean_ctor_get(v_val_1967_, 0);
lean_inc(v_val_1969_);
lean_dec_ref_known(v_val_1967_, 1);
v___x_1970_ = l_Std_Http_URI_EncodedQueryParam_decode(v_val_1969_);
lean_dec(v_val_1969_);
return v___x_1970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get___boxed(lean_object* v_query_1971_, lean_object* v_key_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Std_Http_URI_Query_get(v_query_1971_, v_key_1972_);
lean_dec_ref(v_query_1971_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD(lean_object* v_query_1974_, lean_object* v_key_1975_, lean_object* v_default_1976_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Std_Http_URI_Query_get(v_query_1974_, v_key_1975_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_inc_ref(v_default_1976_);
return v_default_1976_;
}
else
{
lean_object* v_val_1978_; 
v_val_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_val_1978_);
lean_dec_ref_known(v___x_1977_, 1);
return v_val_1978_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD___boxed(lean_object* v_query_1979_, lean_object* v_key_1980_, lean_object* v_default_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Std_Http_URI_Query_getD(v_query_1979_, v_key_1980_, v_default_1981_);
lean_dec_ref(v_default_1981_);
lean_dec_ref(v_query_1979_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set(lean_object* v_query_1983_, lean_object* v_key_1984_, lean_object* v_value_1985_){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
lean_inc_ref(v_key_1984_);
v___x_1986_ = l_Std_Http_URI_Query_erase(v_query_1983_, v_key_1984_);
v___x_1987_ = l_Std_Http_URI_Query_insert(v___x_1986_, v_key_1984_, v_value_1985_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set___boxed(lean_object* v_query_1988_, lean_object* v_key_1989_, lean_object* v_value_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Std_Http_URI_Query_set(v_query_1988_, v_key_1989_, v_value_1990_);
lean_dec_ref(v_query_1988_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(size_t v_sz_1992_, size_t v_i_1993_, lean_object* v_bs_1994_){
_start:
{
uint8_t v___x_1995_; 
v___x_1995_ = lean_usize_dec_lt(v_i_1993_, v_sz_1992_);
if (v___x_1995_ == 0)
{
return v_bs_1994_;
}
else
{
lean_object* v_v_1996_; lean_object* v_fst_1997_; lean_object* v_snd_1998_; lean_object* v___x_1999_; lean_object* v_bs_x27_2000_; lean_object* v___x_2001_; size_t v___x_2002_; size_t v___x_2003_; lean_object* v___x_2004_; 
v_v_1996_ = lean_array_uget_borrowed(v_bs_1994_, v_i_1993_);
v_fst_1997_ = lean_ctor_get(v_v_1996_, 0);
lean_inc(v_fst_1997_);
v_snd_1998_ = lean_ctor_get(v_v_1996_, 1);
lean_inc(v_snd_1998_);
v___x_1999_ = lean_unsigned_to_nat(0u);
v_bs_x27_2000_ = lean_array_uset(v_bs_1994_, v_i_1993_, v___x_1999_);
v___x_2001_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_1997_, v_snd_1998_);
v___x_2002_ = ((size_t)1ULL);
v___x_2003_ = lean_usize_add(v_i_1993_, v___x_2002_);
v___x_2004_ = lean_array_uset(v_bs_x27_2000_, v_i_1993_, v___x_2001_);
v_i_1993_ = v___x_2003_;
v_bs_1994_ = v___x_2004_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0___boxed(lean_object* v_sz_2006_, lean_object* v_i_2007_, lean_object* v_bs_2008_){
_start:
{
size_t v_sz_boxed_2009_; size_t v_i_boxed_2010_; lean_object* v_res_2011_; 
v_sz_boxed_2009_ = lean_unbox_usize(v_sz_2006_);
lean_dec(v_sz_2006_);
v_i_boxed_2010_ = lean_unbox_usize(v_i_2007_);
lean_dec(v_i_2007_);
v_res_2011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_boxed_2009_, v_i_boxed_2010_, v_bs_2008_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toRawString(lean_object* v_query_2013_){
_start:
{
size_t v_sz_2014_; size_t v___x_2015_; lean_object* v_params_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v_sz_2014_ = lean_array_size(v_query_2013_);
v___x_2015_ = ((size_t)0ULL);
v_params_2016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_2014_, v___x_2015_, v_query_2013_);
v___x_2017_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2018_ = lean_array_to_list(v_params_2016_);
v___x_2019_ = l_String_intercalate(v___x_2017_, v___x_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0(lean_object* v_x_2021_){
_start:
{
lean_object* v_fst_2022_; lean_object* v_snd_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v_fst_2022_ = lean_ctor_get(v_x_2021_, 0);
lean_inc(v_fst_2022_);
v_snd_2023_ = lean_ctor_get(v_x_2021_, 1);
lean_inc(v_snd_2023_);
lean_dec_ref(v_x_2021_);
v___x_2024_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
v___x_2025_ = l_Std_Http_URI_Query_insert(v___x_2024_, v_fst_2022_, v_snd_2023_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0(lean_object* v_x_2028_, lean_object* v_q_2029_){
_start:
{
lean_object* v_fst_2030_; lean_object* v_snd_2031_; lean_object* v___x_2032_; 
v_fst_2030_ = lean_ctor_get(v_x_2028_, 0);
lean_inc(v_fst_2030_);
v_snd_2031_ = lean_ctor_get(v_x_2028_, 1);
lean_inc(v_snd_2031_);
lean_dec_ref(v_x_2028_);
v___x_2032_ = l_Std_Http_URI_Query_insert(v_q_2029_, v_fst_2030_, v_snd_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__0(lean_object* v_x_2035_){
_start:
{
lean_object* v_fst_2036_; lean_object* v_snd_2037_; lean_object* v___x_2038_; 
v_fst_2036_ = lean_ctor_get(v_x_2035_, 0);
lean_inc(v_fst_2036_);
v_snd_2037_ = lean_ctor_get(v_x_2035_, 1);
lean_inc(v_snd_2037_);
lean_dec_ref(v_x_2035_);
v___x_2038_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2036_, v_snd_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__1(lean_object* v___f_2040_, lean_object* v_q_2041_){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2042_ = lean_array_get_size(v_q_2041_);
v___x_2043_ = lean_unsigned_to_nat(0u);
v___x_2044_ = lean_nat_dec_eq(v___x_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v_encodedParams_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2045_ = lean_array_to_list(v_q_2041_);
v___x_2046_ = lean_box(0);
v_encodedParams_2047_ = l_List_mapTR_loop___redArg(v___f_2040_, v___x_2045_, v___x_2046_);
v___x_2048_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2049_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2050_ = l_String_intercalate(v___x_2049_, v_encodedParams_2047_);
v___x_2051_ = lean_string_append(v___x_2048_, v___x_2050_);
lean_dec_ref(v___x_2050_);
return v___x_2051_;
}
else
{
lean_object* v___x_2052_; 
lean_dec_ref(v_q_2041_);
lean_dec_ref(v___f_2040_);
v___x_2052_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2052_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
if (lean_obj_tag(v_a_2057_) == 0)
{
lean_object* v___x_2059_; 
v___x_2059_ = l_List_reverse___redArg(v_a_2058_);
return v___x_2059_;
}
else
{
lean_object* v_head_2060_; lean_object* v_tail_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2072_; 
v_head_2060_ = lean_ctor_get(v_a_2057_, 0);
v_tail_2061_ = lean_ctor_get(v_a_2057_, 1);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_a_2057_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2063_ = v_a_2057_;
v_isShared_2064_ = v_isSharedCheck_2072_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_tail_2061_);
lean_inc(v_head_2060_);
lean_dec(v_a_2057_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2072_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v_fst_2065_; lean_object* v_snd_2066_; lean_object* v___x_2067_; lean_object* v___x_2069_; 
v_fst_2065_ = lean_ctor_get(v_head_2060_, 0);
lean_inc(v_fst_2065_);
v_snd_2066_ = lean_ctor_get(v_head_2060_, 1);
lean_inc(v_snd_2066_);
lean_dec(v_head_2060_);
v___x_2067_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2065_, v_snd_2066_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 1, v_a_2058_);
lean_ctor_set(v___x_2063_, 0, v___x_2067_);
v___x_2069_ = v___x_2063_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_a_2058_);
v___x_2069_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
v_a_2057_ = v_tail_2061_;
v_a_2058_ = v___x_2069_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatOption(lean_object* v_x_2073_){
_start:
{
if (lean_obj_tag(v_x_2073_) == 0)
{
lean_object* v___x_2074_; 
v___x_2074_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2074_;
}
else
{
lean_object* v_val_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v_val_2075_ = lean_ctor_get(v_x_2073_, 0);
lean_inc(v_val_2075_);
lean_dec_ref_known(v_x_2073_, 1);
v___x_2076_ = lean_array_get_size(v_val_2075_);
v___x_2077_ = lean_unsigned_to_nat(0u);
v___x_2078_ = lean_nat_dec_eq(v___x_2076_, v___x_2077_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v_encodedParams_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2079_ = lean_array_to_list(v_val_2075_);
v___x_2080_ = lean_box(0);
v_encodedParams_2081_ = l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(v___x_2079_, v___x_2080_);
v___x_2082_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2083_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2084_ = l_String_intercalate(v___x_2083_, v_encodedParams_2081_);
v___x_2085_ = lean_string_append(v___x_2082_, v___x_2084_);
lean_dec_ref(v___x_2084_);
return v___x_2085_;
}
else
{
lean_object* v___x_2086_; 
lean_dec(v_val_2075_);
v___x_2086_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
return v___x_2086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(lean_object* v_x_2087_, lean_object* v_x_2088_){
_start:
{
if (lean_obj_tag(v_x_2087_) == 0)
{
lean_object* v___x_2089_; 
v___x_2089_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2089_;
}
else
{
lean_object* v_val_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_val_2090_ = lean_ctor_get(v_x_2087_, 0);
lean_inc(v_val_2090_);
lean_dec_ref_known(v_x_2087_, 1);
v___x_2091_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2092_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_val_2090_);
v___x_2093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2091_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
v___x_2094_ = l_Repr_addAppParen(v___x_2093_, v_x_2088_);
return v___x_2094_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(lean_object* v_x_2095_, lean_object* v_x_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_x_2095_, v_x_2096_);
lean_dec(v_x_2096_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object* v_x_2098_, lean_object* v_x_2099_){
_start:
{
if (lean_obj_tag(v_x_2098_) == 0)
{
lean_object* v___x_2100_; 
v___x_2100_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2100_;
}
else
{
lean_object* v_val_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v_val_2101_ = lean_ctor_get(v_x_2098_, 0);
lean_inc(v_val_2101_);
lean_dec_ref_known(v_x_2098_, 1);
v___x_2102_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2103_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_val_2101_);
v___x_2104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2102_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = l_Repr_addAppParen(v___x_2104_, v_x_2099_);
return v___x_2105_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1___boxed(lean_object* v_x_2106_, lean_object* v_x_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_x_2106_, v_x_2107_);
lean_dec(v_x_2107_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(lean_object* v_x_2109_, lean_object* v_x_2110_){
_start:
{
if (lean_obj_tag(v_x_2109_) == 0)
{
lean_object* v___x_2111_; 
v___x_2111_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2111_;
}
else
{
lean_object* v_val_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2123_; 
v_val_2112_ = lean_ctor_get(v_x_2109_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_x_2109_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2114_ = v_x_2109_;
v_isShared_2115_ = v_isSharedCheck_2123_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_val_2112_);
lean_dec(v_x_2109_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2123_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2116_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2117_ = l_String_quote(v_val_2112_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set_tag(v___x_2114_, 3);
lean_ctor_set(v___x_2114_, 0, v___x_2117_);
v___x_2119_ = v___x_2114_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2116_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = l_Repr_addAppParen(v___x_2120_, v_x_2110_);
return v___x_2121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2___boxed(lean_object* v_x_2124_, lean_object* v_x_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_x_2124_, v_x_2125_);
lean_dec(v_x_2125_);
return v_res_2126_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = lean_unsigned_to_nat(10u);
v___x_2137_ = lean_nat_to_int(v___x_2136_);
return v___x_2137_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_unsigned_to_nat(13u);
v___x_2142_ = lean_nat_to_int(v___x_2141_);
return v___x_2142_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = lean_unsigned_to_nat(9u);
v___x_2150_ = lean_nat_to_int(v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___redArg(lean_object* v_x_2154_){
_start:
{
lean_object* v_scheme_2155_; lean_object* v_authority_2156_; lean_object* v_path_2157_; lean_object* v_query_2158_; lean_object* v_fragment_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v_scheme_2155_ = lean_ctor_get(v_x_2154_, 0);
lean_inc_ref(v_scheme_2155_);
v_authority_2156_ = lean_ctor_get(v_x_2154_, 1);
lean_inc(v_authority_2156_);
v_path_2157_ = lean_ctor_get(v_x_2154_, 2);
lean_inc_ref(v_path_2157_);
v_query_2158_ = lean_ctor_get(v_x_2154_, 3);
lean_inc(v_query_2158_);
v_fragment_2159_ = lean_ctor_get(v_x_2154_, 4);
lean_inc(v_fragment_2159_);
lean_dec_ref(v_x_2154_);
v___x_2160_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2161_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2162_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2163_ = l_String_quote(v_scheme_2155_);
v___x_2164_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
v___x_2165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2162_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = 0;
v___x_2167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2167_, 0, v___x_2165_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*1, v___x_2166_);
v___x_2168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2161_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2168_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = lean_box(1);
v___x_2172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2170_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__6));
v___x_2174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2172_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
v___x_2175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
lean_ctor_set(v___x_2175_, 1, v___x_2160_);
v___x_2176_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_2177_ = lean_unsigned_to_nat(0u);
v___x_2178_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_2156_, v___x_2177_);
v___x_2179_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2176_);
lean_ctor_set(v___x_2179_, 1, v___x_2178_);
v___x_2180_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
lean_ctor_set_uint8(v___x_2180_, sizeof(void*)*1, v___x_2166_);
v___x_2181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2175_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
v___x_2182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v___x_2169_);
v___x_2183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
lean_ctor_set(v___x_2183_, 1, v___x_2171_);
v___x_2184_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_2185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2183_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
lean_ctor_set(v___x_2186_, 1, v___x_2160_);
v___x_2187_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2188_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_2157_);
v___x_2189_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2187_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set_uint8(v___x_2190_, sizeof(void*)*1, v___x_2166_);
v___x_2191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2186_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
lean_ctor_set(v___x_2192_, 1, v___x_2169_);
v___x_2193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
lean_ctor_set(v___x_2193_, 1, v___x_2171_);
v___x_2194_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_2195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2193_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set(v___x_2196_, 1, v___x_2160_);
v___x_2197_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_2198_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_2158_, v___x_2177_);
v___x_2199_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
lean_ctor_set_uint8(v___x_2200_, sizeof(void*)*1, v___x_2166_);
v___x_2201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2196_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v___x_2169_);
v___x_2203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
lean_ctor_set(v___x_2203_, 1, v___x_2171_);
v___x_2204_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_2205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2203_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v___x_2160_);
v___x_2207_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_2208_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_2159_, v___x_2177_);
v___x_2209_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2207_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set_uint8(v___x_2210_, sizeof(void*)*1, v___x_2166_);
v___x_2211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2206_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2213_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
lean_ctor_set(v___x_2214_, 1, v___x_2211_);
v___x_2215_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2214_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2212_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
v___x_2218_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set_uint8(v___x_2218_, sizeof(void*)*1, v___x_2166_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr(lean_object* v_x_2219_, lean_object* v_prec_2220_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Std_Http_instReprURI_repr___redArg(v_x_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___boxed(lean_object* v_x_2222_, lean_object* v_prec_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Std_Http_instReprURI_repr(v_x_2222_, v_prec_2223_);
lean_dec(v_prec_2223_);
return v_res_2224_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
if (lean_obj_tag(v_x_2233_) == 0)
{
if (lean_obj_tag(v_x_2234_) == 0)
{
uint8_t v___x_2235_; 
v___x_2235_ = 1;
return v___x_2235_;
}
else
{
uint8_t v___x_2236_; 
v___x_2236_ = 0;
return v___x_2236_;
}
}
else
{
if (lean_obj_tag(v_x_2234_) == 0)
{
uint8_t v___x_2237_; 
v___x_2237_ = 0;
return v___x_2237_;
}
else
{
lean_object* v_val_2238_; lean_object* v_val_2239_; uint8_t v___x_2240_; 
v_val_2238_ = lean_ctor_get(v_x_2233_, 0);
v_val_2239_ = lean_ctor_get(v_x_2234_, 0);
v___x_2240_ = l_Std_Http_URI_instBEqAuthority_beq(v_val_2238_, v_val_2239_);
return v___x_2240_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object* v_x_2241_, lean_object* v_x_2242_){
_start:
{
uint8_t v_res_2243_; lean_object* v_r_2244_; 
v_res_2243_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_x_2241_, v_x_2242_);
lean_dec(v_x_2242_);
lean_dec(v_x_2241_);
v_r_2244_ = lean_box(v_res_2243_);
return v_r_2244_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object* v_x_2245_, lean_object* v_x_2246_){
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
lean_object* v_val_2250_; lean_object* v_val_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; 
v_val_2250_ = lean_ctor_get(v_x_2245_, 0);
v_val_2251_ = lean_ctor_get(v_x_2246_, 0);
v___x_2252_ = lean_array_get_size(v_val_2250_);
v___x_2253_ = lean_array_get_size(v_val_2251_);
v___x_2254_ = lean_nat_dec_eq(v___x_2252_, v___x_2253_);
if (v___x_2254_ == 0)
{
return v___x_2254_;
}
else
{
uint8_t v___x_2255_; 
v___x_2255_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_val_2250_, v_val_2251_, v___x_2252_);
return v___x_2255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object* v_x_2256_, lean_object* v_x_2257_){
_start:
{
uint8_t v_res_2258_; lean_object* v_r_2259_; 
v_res_2258_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_x_2256_, v_x_2257_);
lean_dec(v_x_2257_);
lean_dec(v_x_2256_);
v_r_2259_ = lean_box(v_res_2258_);
return v_r_2259_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(lean_object* v_x_2260_, lean_object* v_x_2261_){
_start:
{
if (lean_obj_tag(v_x_2260_) == 0)
{
if (lean_obj_tag(v_x_2261_) == 0)
{
uint8_t v___x_2262_; 
v___x_2262_ = 1;
return v___x_2262_;
}
else
{
uint8_t v___x_2263_; 
v___x_2263_ = 0;
return v___x_2263_;
}
}
else
{
if (lean_obj_tag(v_x_2261_) == 0)
{
uint8_t v___x_2264_; 
v___x_2264_ = 0;
return v___x_2264_;
}
else
{
lean_object* v_val_2265_; lean_object* v_val_2266_; uint8_t v___x_2267_; 
v_val_2265_ = lean_ctor_get(v_x_2260_, 0);
v_val_2266_ = lean_ctor_get(v_x_2261_, 0);
v___x_2267_ = lean_string_dec_eq(v_val_2265_, v_val_2266_);
return v___x_2267_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2___boxed(lean_object* v_x_2268_, lean_object* v_x_2269_){
_start:
{
uint8_t v_res_2270_; lean_object* v_r_2271_; 
v_res_2270_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_x_2268_, v_x_2269_);
lean_dec(v_x_2269_);
lean_dec(v_x_2268_);
v_r_2271_ = lean_box(v_res_2270_);
return v_r_2271_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object* v_x_2272_, lean_object* v_x_2273_){
_start:
{
lean_object* v_scheme_2274_; lean_object* v_authority_2275_; lean_object* v_path_2276_; lean_object* v_query_2277_; lean_object* v_fragment_2278_; lean_object* v_scheme_2279_; lean_object* v_authority_2280_; lean_object* v_path_2281_; lean_object* v_query_2282_; lean_object* v_fragment_2283_; uint8_t v___x_2284_; 
v_scheme_2274_ = lean_ctor_get(v_x_2272_, 0);
v_authority_2275_ = lean_ctor_get(v_x_2272_, 1);
v_path_2276_ = lean_ctor_get(v_x_2272_, 2);
v_query_2277_ = lean_ctor_get(v_x_2272_, 3);
v_fragment_2278_ = lean_ctor_get(v_x_2272_, 4);
v_scheme_2279_ = lean_ctor_get(v_x_2273_, 0);
v_authority_2280_ = lean_ctor_get(v_x_2273_, 1);
v_path_2281_ = lean_ctor_get(v_x_2273_, 2);
v_query_2282_ = lean_ctor_get(v_x_2273_, 3);
v_fragment_2283_ = lean_ctor_get(v_x_2273_, 4);
v___x_2284_ = lean_string_dec_eq(v_scheme_2274_, v_scheme_2279_);
if (v___x_2284_ == 0)
{
return v___x_2284_;
}
else
{
uint8_t v___x_2285_; 
v___x_2285_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_2275_, v_authority_2280_);
if (v___x_2285_ == 0)
{
return v___x_2285_;
}
else
{
uint8_t v___x_2286_; 
v___x_2286_ = l_Std_Http_URI_instBEqPath_beq(v_path_2276_, v_path_2281_);
if (v___x_2286_ == 0)
{
return v___x_2286_;
}
else
{
uint8_t v___x_2287_; 
v___x_2287_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_2277_, v_query_2282_);
if (v___x_2287_ == 0)
{
return v___x_2287_;
}
else
{
uint8_t v___x_2288_; 
v___x_2288_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_2278_, v_fragment_2283_);
return v___x_2288_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object* v_x_2289_, lean_object* v_x_2290_){
_start:
{
uint8_t v_res_2291_; lean_object* v_r_2292_; 
v_res_2291_ = l_Std_Http_instBEqURI_beq(v_x_2289_, v_x_2290_);
lean_dec_ref(v_x_2290_);
lean_dec_ref(v_x_2289_);
v_r_2292_ = lean_box(v_res_2291_);
return v_r_2292_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__1(lean_object* v___f_2297_, lean_object* v_uri_2298_){
_start:
{
lean_object* v_scheme_2299_; lean_object* v_authority_2300_; lean_object* v_path_2301_; lean_object* v_query_2302_; lean_object* v_fragment_2303_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2326_; 
v_scheme_2299_ = lean_ctor_get(v_uri_2298_, 0);
lean_inc_ref(v_scheme_2299_);
v_authority_2300_ = lean_ctor_get(v_uri_2298_, 1);
lean_inc(v_authority_2300_);
v_path_2301_ = lean_ctor_get(v_uri_2298_, 2);
lean_inc_ref(v_path_2301_);
v_query_2302_ = lean_ctor_get(v_uri_2298_, 3);
lean_inc(v_query_2302_);
v_fragment_2303_ = lean_ctor_get(v_uri_2298_, 4);
lean_inc(v_fragment_2303_);
lean_dec_ref(v_uri_2298_);
if (lean_obj_tag(v_authority_2300_) == 0)
{
lean_object* v___x_2337_; 
v___x_2337_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2326_ = v___x_2337_;
goto v___jp_2325_;
}
else
{
lean_object* v_val_2338_; lean_object* v_userInfo_2339_; lean_object* v_host_2340_; lean_object* v_port_2341_; lean_object* v___x_2342_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2361_; 
v_val_2338_ = lean_ctor_get(v_authority_2300_, 0);
lean_inc(v_val_2338_);
lean_dec_ref_known(v_authority_2300_, 1);
v_userInfo_2339_ = lean_ctor_get(v_val_2338_, 0);
lean_inc(v_userInfo_2339_);
v_host_2340_ = lean_ctor_get(v_val_2338_, 1);
lean_inc_ref(v_host_2340_);
v_port_2341_ = lean_ctor_get(v_val_2338_, 2);
lean_inc(v_port_2341_);
lean_dec(v_val_2338_);
v___x_2342_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_2339_) == 0)
{
lean_object* v___x_2371_; 
v___x_2371_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2361_ = v___x_2371_;
goto v___jp_2360_;
}
else
{
lean_object* v_val_2372_; lean_object* v_password_2373_; 
v_val_2372_ = lean_ctor_get(v_userInfo_2339_, 0);
lean_inc(v_val_2372_);
lean_dec_ref_known(v_userInfo_2339_, 1);
v_password_2373_ = lean_ctor_get(v_val_2372_, 1);
if (lean_obj_tag(v_password_2373_) == 0)
{
lean_object* v_username_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v_username_2374_ = lean_ctor_get(v_val_2372_, 0);
lean_inc_ref(v_username_2374_);
lean_dec(v_val_2372_);
v___x_2375_ = lean_string_from_utf8_unchecked(v_username_2374_);
v___x_2376_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2377_ = lean_string_append(v___x_2375_, v___x_2376_);
v___y_2361_ = v___x_2377_;
goto v___jp_2360_;
}
else
{
lean_object* v_username_2378_; lean_object* v_val_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_inc_ref(v_password_2373_);
v_username_2378_ = lean_ctor_get(v_val_2372_, 0);
lean_inc_ref(v_username_2378_);
lean_dec(v_val_2372_);
v_val_2379_ = lean_ctor_get(v_password_2373_, 0);
lean_inc(v_val_2379_);
lean_dec_ref_known(v_password_2373_, 1);
v___x_2380_ = lean_string_from_utf8_unchecked(v_username_2378_);
v___x_2381_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2382_ = lean_string_append(v___x_2380_, v___x_2381_);
v___x_2383_ = lean_string_from_utf8_unchecked(v_val_2379_);
v___x_2384_ = lean_string_append(v___x_2382_, v___x_2383_);
lean_dec_ref(v___x_2383_);
v___x_2385_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2386_ = lean_string_append(v___x_2384_, v___x_2385_);
v___y_2361_ = v___x_2386_;
goto v___jp_2360_;
}
}
v___jp_2343_:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2347_ = lean_string_append(v___y_2345_, v___y_2344_);
lean_dec_ref(v___y_2344_);
v___x_2348_ = lean_string_append(v___x_2347_, v___y_2346_);
lean_dec_ref(v___y_2346_);
v___x_2349_ = lean_string_append(v___x_2342_, v___x_2348_);
lean_dec_ref(v___x_2348_);
v___y_2326_ = v___x_2349_;
goto v___jp_2325_;
}
v___jp_2350_:
{
switch(lean_obj_tag(v_port_2341_))
{
case 0:
{
lean_object* v___x_2353_; 
v___x_2353_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2344_ = v___y_2352_;
v___y_2345_ = v___y_2351_;
v___y_2346_ = v___x_2353_;
goto v___jp_2343_;
}
case 1:
{
lean_object* v___x_2354_; 
v___x_2354_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_2344_ = v___y_2352_;
v___y_2345_ = v___y_2351_;
v___y_2346_ = v___x_2354_;
goto v___jp_2343_;
}
default: 
{
uint16_t v_port_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v_port_2355_ = lean_ctor_get_uint16(v_port_2341_, 0);
lean_dec_ref_known(v_port_2341_, 0);
v___x_2356_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2357_ = lean_uint16_to_nat(v_port_2355_);
v___x_2358_ = l_Nat_reprFast(v___x_2357_);
v___x_2359_ = lean_string_append(v___x_2356_, v___x_2358_);
lean_dec_ref(v___x_2358_);
v___y_2344_ = v___y_2352_;
v___y_2345_ = v___y_2351_;
v___y_2346_ = v___x_2359_;
goto v___jp_2343_;
}
}
}
v___jp_2360_:
{
switch(lean_obj_tag(v_host_2340_))
{
case 0:
{
lean_object* v_name_2362_; 
v_name_2362_ = lean_ctor_get(v_host_2340_, 0);
lean_inc_ref(v_name_2362_);
lean_dec_ref_known(v_host_2340_, 1);
v___y_2351_ = v___y_2361_;
v___y_2352_ = v_name_2362_;
goto v___jp_2350_;
}
case 1:
{
lean_object* v_ipv4_2363_; lean_object* v___x_2364_; 
v_ipv4_2363_ = lean_ctor_get(v_host_2340_, 0);
lean_inc_ref(v_ipv4_2363_);
lean_dec_ref_known(v_host_2340_, 1);
v___x_2364_ = lean_uv_ntop_v4(v_ipv4_2363_);
lean_dec_ref(v_ipv4_2363_);
v___y_2351_ = v___y_2361_;
v___y_2352_ = v___x_2364_;
goto v___jp_2350_;
}
default: 
{
lean_object* v_ipv6_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_ipv6_2365_ = lean_ctor_get(v_host_2340_, 0);
lean_inc_ref(v_ipv6_2365_);
lean_dec_ref_known(v_host_2340_, 1);
v___x_2366_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_2367_ = lean_uv_ntop_v6(v_ipv6_2365_);
lean_dec_ref(v_ipv6_2365_);
v___x_2368_ = lean_string_append(v___x_2366_, v___x_2367_);
lean_dec_ref(v___x_2367_);
v___x_2369_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_2370_ = lean_string_append(v___x_2368_, v___x_2369_);
v___y_2351_ = v___y_2361_;
v___y_2352_ = v___x_2370_;
goto v___jp_2350_;
}
}
}
}
v___jp_2304_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2309_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2310_ = lean_string_append(v_scheme_2299_, v___x_2309_);
v___x_2311_ = lean_string_append(v___x_2310_, v___y_2307_);
lean_dec_ref(v___y_2307_);
v___x_2312_ = lean_string_append(v___x_2311_, v___y_2306_);
lean_dec_ref(v___y_2306_);
v___x_2313_ = lean_string_append(v___x_2312_, v___y_2305_);
lean_dec_ref(v___y_2305_);
v___x_2314_ = lean_string_append(v___x_2313_, v___y_2308_);
lean_dec_ref(v___y_2308_);
return v___x_2314_;
}
v___jp_2315_:
{
lean_object* v_queryPart_2318_; 
v_queryPart_2318_ = l_Std_Http_URI_Query_formatOption(v_query_2302_);
if (lean_obj_tag(v_fragment_2303_) == 0)
{
lean_object* v___x_2319_; 
v___x_2319_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2305_ = v_queryPart_2318_;
v___y_2306_ = v___y_2317_;
v___y_2307_ = v___y_2316_;
v___y_2308_ = v___x_2319_;
goto v___jp_2304_;
}
else
{
lean_object* v_val_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_val_2320_ = lean_ctor_get(v_fragment_2303_, 0);
lean_inc(v_val_2320_);
lean_dec_ref_known(v_fragment_2303_, 1);
v___x_2321_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_2322_ = l_Std_Http_URI_EncodedFragment_encode(v_val_2320_);
v___x_2323_ = lean_string_from_utf8_unchecked(v___x_2322_);
v___x_2324_ = lean_string_append(v___x_2321_, v___x_2323_);
lean_dec_ref(v___x_2323_);
v___y_2305_ = v_queryPart_2318_;
v___y_2306_ = v___y_2317_;
v___y_2307_ = v___y_2316_;
v___y_2308_ = v___x_2324_;
goto v___jp_2304_;
}
}
v___jp_2325_:
{
lean_object* v_segments_2327_; uint8_t v_absolute_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; size_t v_sz_2331_; size_t v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v_result_2335_; 
v_segments_2327_ = lean_ctor_get(v_path_2301_, 0);
lean_inc_ref(v_segments_2327_);
v_absolute_2328_ = lean_ctor_get_uint8(v_path_2301_, sizeof(void*)*1);
lean_dec_ref(v_path_2301_);
v___x_2329_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_2330_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_2331_ = lean_array_size(v_segments_2327_);
v___x_2332_ = ((size_t)0ULL);
v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2330_, v___f_2297_, v_sz_2331_, v___x_2332_, v_segments_2327_);
v___x_2334_ = lean_array_to_list(v___x_2333_);
v_result_2335_ = l_String_intercalate(v___x_2329_, v___x_2334_);
if (v_absolute_2328_ == 0)
{
v___y_2316_ = v___y_2326_;
v___y_2317_ = v_result_2335_;
goto v___jp_2315_;
}
else
{
lean_object* v___x_2336_; 
v___x_2336_ = lean_string_append(v___x_2329_, v_result_2335_);
lean_dec_ref(v_result_2335_);
v___y_2316_ = v___y_2326_;
v___y_2317_ = v___x_2336_;
goto v___jp_2315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x3f(lean_object* v_b_2399_, lean_object* v_scheme_2400_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Std_Http_URI_Scheme_ofString_x3f(v_scheme_2400_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v___x_2402_; 
lean_dec_ref(v_b_2399_);
v___x_2402_ = lean_box(0);
return v___x_2402_;
}
else
{
lean_object* v_userInfo_2403_; lean_object* v_host_2404_; lean_object* v_port_2405_; lean_object* v_pathSegments_2406_; lean_object* v_query_2407_; lean_object* v_fragment_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2423_; 
v_userInfo_2403_ = lean_ctor_get(v_b_2399_, 1);
v_host_2404_ = lean_ctor_get(v_b_2399_, 2);
v_port_2405_ = lean_ctor_get(v_b_2399_, 3);
v_pathSegments_2406_ = lean_ctor_get(v_b_2399_, 4);
v_query_2407_ = lean_ctor_get(v_b_2399_, 5);
v_fragment_2408_ = lean_ctor_get(v_b_2399_, 6);
v_isSharedCheck_2423_ = !lean_is_exclusive(v_b_2399_);
if (v_isSharedCheck_2423_ == 0)
{
lean_object* v_unused_2424_; 
v_unused_2424_ = lean_ctor_get(v_b_2399_, 0);
lean_dec(v_unused_2424_);
v___x_2410_ = v_b_2399_;
v_isShared_2411_ = v_isSharedCheck_2423_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_fragment_2408_);
lean_inc(v_query_2407_);
lean_inc(v_pathSegments_2406_);
lean_inc(v_port_2405_);
lean_inc(v_host_2404_);
lean_inc(v_userInfo_2403_);
lean_dec(v_b_2399_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2423_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
lean_inc_ref(v___x_2401_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2401_);
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_userInfo_2403_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v_host_2404_);
lean_ctor_set(v_reuseFailAlloc_2422_, 3, v_port_2405_);
lean_ctor_set(v_reuseFailAlloc_2422_, 4, v_pathSegments_2406_);
lean_ctor_set(v_reuseFailAlloc_2422_, 5, v_query_2407_);
lean_ctor_set(v_reuseFailAlloc_2422_, 6, v_fragment_2408_);
v___x_2413_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; 
v_unused_2421_ = lean_ctor_get(v___x_2401_, 0);
lean_dec(v_unused_2421_);
v___x_2415_ = v___x_2401_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_dec(v___x_2401_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 0, v___x_2413_);
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(lean_object* v_msg_2425_){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = ((lean_object*)(l_Std_Http_URI_instInhabitedBuilder_default));
v___x_2427_ = lean_panic_fn_borrowed(v___x_2426_, v_msg_2425_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x21(lean_object* v_b_2429_, lean_object* v_scheme_2430_){
_start:
{
lean_object* v___x_2431_; 
lean_inc_ref(v_scheme_2430_);
v___x_2431_ = l_Std_Http_URI_Builder_setScheme_x3f(v_b_2429_, v_scheme_2430_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2432_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2433_ = ((lean_object*)(l_Std_Http_URI_Builder_setScheme_x21___closed__0));
v___x_2434_ = lean_unsigned_to_nat(687u);
v___x_2435_ = lean_unsigned_to_nat(14u);
v___x_2436_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_2437_ = l_String_quote(v_scheme_2430_);
v___x_2438_ = lean_string_append(v___x_2436_, v___x_2437_);
lean_dec_ref(v___x_2437_);
v___x_2439_ = l_mkPanicMessageWithDecl(v___x_2432_, v___x_2433_, v___x_2434_, v___x_2435_, v___x_2438_);
lean_dec_ref(v___x_2438_);
v___x_2440_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2439_);
return v___x_2440_;
}
else
{
lean_object* v_val_2441_; 
lean_dec_ref(v_scheme_2430_);
v_val_2441_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_val_2441_);
lean_dec_ref_known(v___x_2431_, 1);
return v_val_2441_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo(lean_object* v_b_2442_, lean_object* v_username_2443_, lean_object* v_password_2444_){
_start:
{
lean_object* v_scheme_2445_; lean_object* v_host_2446_; lean_object* v_port_2447_; lean_object* v_pathSegments_2448_; lean_object* v_query_2449_; lean_object* v_fragment_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2473_; 
v_scheme_2445_ = lean_ctor_get(v_b_2442_, 0);
v_host_2446_ = lean_ctor_get(v_b_2442_, 2);
v_port_2447_ = lean_ctor_get(v_b_2442_, 3);
v_pathSegments_2448_ = lean_ctor_get(v_b_2442_, 4);
v_query_2449_ = lean_ctor_get(v_b_2442_, 5);
v_fragment_2450_ = lean_ctor_get(v_b_2442_, 6);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_b_2442_);
if (v_isSharedCheck_2473_ == 0)
{
lean_object* v_unused_2474_; 
v_unused_2474_ = lean_ctor_get(v_b_2442_, 1);
lean_dec(v_unused_2474_);
v___x_2452_ = v_b_2442_;
v_isShared_2453_ = v_isSharedCheck_2473_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_fragment_2450_);
lean_inc(v_query_2449_);
lean_inc(v_pathSegments_2448_);
lean_inc(v_port_2447_);
lean_inc(v_host_2446_);
lean_inc(v_scheme_2445_);
lean_dec(v_b_2442_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2473_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___y_2455_; lean_object* v___x_2460_; 
v___x_2460_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_2443_);
if (lean_obj_tag(v_password_2444_) == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = lean_box(0);
v___x_2462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___y_2455_ = v___x_2462_;
goto v___jp_2454_;
}
else
{
lean_object* v_val_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2472_; 
v_val_2463_ = lean_ctor_get(v_password_2444_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v_password_2444_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2465_ = v_password_2444_;
v_isShared_2466_ = v_isSharedCheck_2472_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_val_2463_);
lean_dec(v_password_2444_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2472_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2467_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_2463_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v___x_2467_);
v___x_2469_ = v___x_2465_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2470_; 
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2460_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___y_2455_ = v___x_2470_;
goto v___jp_2454_;
}
}
}
v___jp_2454_:
{
lean_object* v___x_2456_; lean_object* v___x_2458_; 
v___x_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___y_2455_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 1, v___x_2456_);
v___x_2458_ = v___x_2452_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_scheme_2445_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v___x_2456_);
lean_ctor_set(v_reuseFailAlloc_2459_, 2, v_host_2446_);
lean_ctor_set(v_reuseFailAlloc_2459_, 3, v_port_2447_);
lean_ctor_set(v_reuseFailAlloc_2459_, 4, v_pathSegments_2448_);
lean_ctor_set(v_reuseFailAlloc_2459_, 5, v_query_2449_);
lean_ctor_set(v_reuseFailAlloc_2459_, 6, v_fragment_2450_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x3f(lean_object* v_b_2475_, lean_object* v_name_2476_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Std_Http_URI_DomainName_ofString_x3f(v_name_2476_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v___x_2478_; 
lean_dec_ref(v_b_2475_);
v___x_2478_ = lean_box(0);
return v___x_2478_;
}
else
{
lean_object* v_val_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2502_; 
v_val_2479_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2481_ = v___x_2477_;
v_isShared_2482_ = v_isSharedCheck_2502_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_val_2479_);
lean_dec(v___x_2477_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2502_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v_scheme_2483_; lean_object* v_userInfo_2484_; lean_object* v_port_2485_; lean_object* v_pathSegments_2486_; lean_object* v_query_2487_; lean_object* v_fragment_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2500_; 
v_scheme_2483_ = lean_ctor_get(v_b_2475_, 0);
v_userInfo_2484_ = lean_ctor_get(v_b_2475_, 1);
v_port_2485_ = lean_ctor_get(v_b_2475_, 3);
v_pathSegments_2486_ = lean_ctor_get(v_b_2475_, 4);
v_query_2487_ = lean_ctor_get(v_b_2475_, 5);
v_fragment_2488_ = lean_ctor_get(v_b_2475_, 6);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_b_2475_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; 
v_unused_2501_ = lean_ctor_get(v_b_2475_, 2);
lean_dec(v_unused_2501_);
v___x_2490_ = v_b_2475_;
v_isShared_2491_ = v_isSharedCheck_2500_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_fragment_2488_);
lean_inc(v_query_2487_);
lean_inc(v_pathSegments_2486_);
lean_inc(v_port_2485_);
lean_inc(v_userInfo_2484_);
lean_inc(v_scheme_2483_);
lean_dec(v_b_2475_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2500_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2492_; lean_object* v___x_2494_; 
v___x_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2492_, 0, v_val_2479_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2492_);
v___x_2494_ = v___x_2481_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
lean_object* v___x_2496_; 
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 2, v___x_2494_);
v___x_2496_ = v___x_2490_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_scheme_2483_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_userInfo_2484_);
lean_ctor_set(v_reuseFailAlloc_2498_, 2, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2498_, 3, v_port_2485_);
lean_ctor_set(v_reuseFailAlloc_2498_, 4, v_pathSegments_2486_);
lean_ctor_set(v_reuseFailAlloc_2498_, 5, v_query_2487_);
lean_ctor_set(v_reuseFailAlloc_2498_, 6, v_fragment_2488_);
v___x_2496_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; 
v___x_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
return v___x_2497_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x21(lean_object* v_b_2505_, lean_object* v_name_2506_){
_start:
{
lean_object* v___x_2507_; 
lean_inc_ref(v_name_2506_);
v___x_2507_ = l_Std_Http_URI_Builder_setHost_x3f(v_b_2505_, v_name_2506_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2508_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2509_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__0));
v___x_2510_ = lean_unsigned_to_nat(716u);
v___x_2511_ = lean_unsigned_to_nat(14u);
v___x_2512_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__1));
v___x_2513_ = l_String_quote(v_name_2506_);
v___x_2514_ = lean_string_append(v___x_2512_, v___x_2513_);
lean_dec_ref(v___x_2513_);
v___x_2515_ = l_mkPanicMessageWithDecl(v___x_2508_, v___x_2509_, v___x_2510_, v___x_2511_, v___x_2514_);
lean_dec_ref(v___x_2514_);
v___x_2516_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2515_);
return v___x_2516_;
}
else
{
lean_object* v_val_2517_; 
lean_dec_ref(v_name_2506_);
v_val_2517_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_val_2517_);
lean_dec_ref_known(v___x_2507_, 1);
return v_val_2517_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv4(lean_object* v_b_2518_, lean_object* v_addr_2519_){
_start:
{
lean_object* v_scheme_2520_; lean_object* v_userInfo_2521_; lean_object* v_port_2522_; lean_object* v_pathSegments_2523_; lean_object* v_query_2524_; lean_object* v_fragment_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2534_; 
v_scheme_2520_ = lean_ctor_get(v_b_2518_, 0);
v_userInfo_2521_ = lean_ctor_get(v_b_2518_, 1);
v_port_2522_ = lean_ctor_get(v_b_2518_, 3);
v_pathSegments_2523_ = lean_ctor_get(v_b_2518_, 4);
v_query_2524_ = lean_ctor_get(v_b_2518_, 5);
v_fragment_2525_ = lean_ctor_get(v_b_2518_, 6);
v_isSharedCheck_2534_ = !lean_is_exclusive(v_b_2518_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; 
v_unused_2535_ = lean_ctor_get(v_b_2518_, 2);
lean_dec(v_unused_2535_);
v___x_2527_ = v_b_2518_;
v_isShared_2528_ = v_isSharedCheck_2534_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_fragment_2525_);
lean_inc(v_query_2524_);
lean_inc(v_pathSegments_2523_);
lean_inc(v_port_2522_);
lean_inc(v_userInfo_2521_);
lean_inc(v_scheme_2520_);
lean_dec(v_b_2518_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2534_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2529_, 0, v_addr_2519_);
v___x_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 2, v___x_2530_);
v___x_2532_ = v___x_2527_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_scheme_2520_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_userInfo_2521_);
lean_ctor_set(v_reuseFailAlloc_2533_, 2, v___x_2530_);
lean_ctor_set(v_reuseFailAlloc_2533_, 3, v_port_2522_);
lean_ctor_set(v_reuseFailAlloc_2533_, 4, v_pathSegments_2523_);
lean_ctor_set(v_reuseFailAlloc_2533_, 5, v_query_2524_);
lean_ctor_set(v_reuseFailAlloc_2533_, 6, v_fragment_2525_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv6(lean_object* v_b_2536_, lean_object* v_addr_2537_){
_start:
{
lean_object* v_scheme_2538_; lean_object* v_userInfo_2539_; lean_object* v_port_2540_; lean_object* v_pathSegments_2541_; lean_object* v_query_2542_; lean_object* v_fragment_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2552_; 
v_scheme_2538_ = lean_ctor_get(v_b_2536_, 0);
v_userInfo_2539_ = lean_ctor_get(v_b_2536_, 1);
v_port_2540_ = lean_ctor_get(v_b_2536_, 3);
v_pathSegments_2541_ = lean_ctor_get(v_b_2536_, 4);
v_query_2542_ = lean_ctor_get(v_b_2536_, 5);
v_fragment_2543_ = lean_ctor_get(v_b_2536_, 6);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_b_2536_);
if (v_isSharedCheck_2552_ == 0)
{
lean_object* v_unused_2553_; 
v_unused_2553_ = lean_ctor_get(v_b_2536_, 2);
lean_dec(v_unused_2553_);
v___x_2545_ = v_b_2536_;
v_isShared_2546_ = v_isSharedCheck_2552_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_fragment_2543_);
lean_inc(v_query_2542_);
lean_inc(v_pathSegments_2541_);
lean_inc(v_port_2540_);
lean_inc(v_userInfo_2539_);
lean_inc(v_scheme_2538_);
lean_dec(v_b_2536_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2552_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2550_; 
v___x_2547_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2547_, 0, v_addr_2537_);
v___x_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 2, v___x_2548_);
v___x_2550_ = v___x_2545_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_scheme_2538_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v_userInfo_2539_);
lean_ctor_set(v_reuseFailAlloc_2551_, 2, v___x_2548_);
lean_ctor_set(v_reuseFailAlloc_2551_, 3, v_port_2540_);
lean_ctor_set(v_reuseFailAlloc_2551_, 4, v_pathSegments_2541_);
lean_ctor_set(v_reuseFailAlloc_2551_, 5, v_query_2542_);
lean_ctor_set(v_reuseFailAlloc_2551_, 6, v_fragment_2543_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort(lean_object* v_b_2554_, uint16_t v_port_2555_){
_start:
{
lean_object* v_scheme_2556_; lean_object* v_userInfo_2557_; lean_object* v_host_2558_; lean_object* v_pathSegments_2559_; lean_object* v_query_2560_; lean_object* v_fragment_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2569_; 
v_scheme_2556_ = lean_ctor_get(v_b_2554_, 0);
v_userInfo_2557_ = lean_ctor_get(v_b_2554_, 1);
v_host_2558_ = lean_ctor_get(v_b_2554_, 2);
v_pathSegments_2559_ = lean_ctor_get(v_b_2554_, 4);
v_query_2560_ = lean_ctor_get(v_b_2554_, 5);
v_fragment_2561_ = lean_ctor_get(v_b_2554_, 6);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_b_2554_);
if (v_isSharedCheck_2569_ == 0)
{
lean_object* v_unused_2570_; 
v_unused_2570_ = lean_ctor_get(v_b_2554_, 3);
lean_dec(v_unused_2570_);
v___x_2563_ = v_b_2554_;
v_isShared_2564_ = v_isSharedCheck_2569_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_fragment_2561_);
lean_inc(v_query_2560_);
lean_inc(v_pathSegments_2559_);
lean_inc(v_host_2558_);
lean_inc(v_userInfo_2557_);
lean_inc(v_scheme_2556_);
lean_dec(v_b_2554_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2569_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2565_ = lean_alloc_ctor(2, 0, 2);
lean_ctor_set_uint16(v___x_2565_, 0, v_port_2555_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 3, v___x_2565_);
v___x_2567_ = v___x_2563_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_scheme_2556_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_userInfo_2557_);
lean_ctor_set(v_reuseFailAlloc_2568_, 2, v_host_2558_);
lean_ctor_set(v_reuseFailAlloc_2568_, 3, v___x_2565_);
lean_ctor_set(v_reuseFailAlloc_2568_, 4, v_pathSegments_2559_);
lean_ctor_set(v_reuseFailAlloc_2568_, 5, v_query_2560_);
lean_ctor_set(v_reuseFailAlloc_2568_, 6, v_fragment_2561_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort___boxed(lean_object* v_b_2571_, lean_object* v_port_2572_){
_start:
{
uint16_t v_port_boxed_2573_; lean_object* v_res_2574_; 
v_port_boxed_2573_ = lean_unbox(v_port_2572_);
v_res_2574_ = l_Std_Http_URI_Builder_setPort(v_b_2571_, v_port_boxed_2573_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPath(lean_object* v_b_2575_, lean_object* v_segments_2576_){
_start:
{
lean_object* v_scheme_2577_; lean_object* v_userInfo_2578_; lean_object* v_host_2579_; lean_object* v_port_2580_; lean_object* v_query_2581_; lean_object* v_fragment_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
v_scheme_2577_ = lean_ctor_get(v_b_2575_, 0);
v_userInfo_2578_ = lean_ctor_get(v_b_2575_, 1);
v_host_2579_ = lean_ctor_get(v_b_2575_, 2);
v_port_2580_ = lean_ctor_get(v_b_2575_, 3);
v_query_2581_ = lean_ctor_get(v_b_2575_, 5);
v_fragment_2582_ = lean_ctor_get(v_b_2575_, 6);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_b_2575_);
if (v_isSharedCheck_2589_ == 0)
{
lean_object* v_unused_2590_; 
v_unused_2590_ = lean_ctor_get(v_b_2575_, 4);
lean_dec(v_unused_2590_);
v___x_2584_ = v_b_2575_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_fragment_2582_);
lean_inc(v_query_2581_);
lean_inc(v_port_2580_);
lean_inc(v_host_2579_);
lean_inc(v_userInfo_2578_);
lean_inc(v_scheme_2577_);
lean_dec(v_b_2575_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 4, v_segments_2576_);
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_scheme_2577_);
lean_ctor_set(v_reuseFailAlloc_2588_, 1, v_userInfo_2578_);
lean_ctor_set(v_reuseFailAlloc_2588_, 2, v_host_2579_);
lean_ctor_set(v_reuseFailAlloc_2588_, 3, v_port_2580_);
lean_ctor_set(v_reuseFailAlloc_2588_, 4, v_segments_2576_);
lean_ctor_set(v_reuseFailAlloc_2588_, 5, v_query_2581_);
lean_ctor_set(v_reuseFailAlloc_2588_, 6, v_fragment_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_appendPathSegment(lean_object* v_b_2591_, lean_object* v_segment_2592_){
_start:
{
lean_object* v_scheme_2593_; lean_object* v_userInfo_2594_; lean_object* v_host_2595_; lean_object* v_port_2596_; lean_object* v_pathSegments_2597_; lean_object* v_query_2598_; lean_object* v_fragment_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2607_; 
v_scheme_2593_ = lean_ctor_get(v_b_2591_, 0);
v_userInfo_2594_ = lean_ctor_get(v_b_2591_, 1);
v_host_2595_ = lean_ctor_get(v_b_2591_, 2);
v_port_2596_ = lean_ctor_get(v_b_2591_, 3);
v_pathSegments_2597_ = lean_ctor_get(v_b_2591_, 4);
v_query_2598_ = lean_ctor_get(v_b_2591_, 5);
v_fragment_2599_ = lean_ctor_get(v_b_2591_, 6);
v_isSharedCheck_2607_ = !lean_is_exclusive(v_b_2591_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2601_ = v_b_2591_;
v_isShared_2602_ = v_isSharedCheck_2607_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_fragment_2599_);
lean_inc(v_query_2598_);
lean_inc(v_pathSegments_2597_);
lean_inc(v_port_2596_);
lean_inc(v_host_2595_);
lean_inc(v_userInfo_2594_);
lean_inc(v_scheme_2593_);
lean_dec(v_b_2591_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2607_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2603_; lean_object* v___x_2605_; 
v___x_2603_ = lean_array_push(v_pathSegments_2597_, v_segment_2592_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 4, v___x_2603_);
v___x_2605_ = v___x_2601_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_scheme_2593_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_userInfo_2594_);
lean_ctor_set(v_reuseFailAlloc_2606_, 2, v_host_2595_);
lean_ctor_set(v_reuseFailAlloc_2606_, 3, v_port_2596_);
lean_ctor_set(v_reuseFailAlloc_2606_, 4, v___x_2603_);
lean_ctor_set(v_reuseFailAlloc_2606_, 5, v_query_2598_);
lean_ctor_set(v_reuseFailAlloc_2606_, 6, v_fragment_2599_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryParam(lean_object* v_b_2608_, lean_object* v_key_2609_, lean_object* v_value_2610_){
_start:
{
lean_object* v_scheme_2611_; lean_object* v_userInfo_2612_; lean_object* v_host_2613_; lean_object* v_port_2614_; lean_object* v_pathSegments_2615_; lean_object* v_query_2616_; lean_object* v_fragment_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2627_; 
v_scheme_2611_ = lean_ctor_get(v_b_2608_, 0);
v_userInfo_2612_ = lean_ctor_get(v_b_2608_, 1);
v_host_2613_ = lean_ctor_get(v_b_2608_, 2);
v_port_2614_ = lean_ctor_get(v_b_2608_, 3);
v_pathSegments_2615_ = lean_ctor_get(v_b_2608_, 4);
v_query_2616_ = lean_ctor_get(v_b_2608_, 5);
v_fragment_2617_ = lean_ctor_get(v_b_2608_, 6);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_b_2608_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2619_ = v_b_2608_;
v_isShared_2620_ = v_isSharedCheck_2627_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_fragment_2617_);
lean_inc(v_query_2616_);
lean_inc(v_pathSegments_2615_);
lean_inc(v_port_2614_);
lean_inc(v_host_2613_);
lean_inc(v_userInfo_2612_);
lean_inc(v_scheme_2611_);
lean_dec(v_b_2608_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2627_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2621_, 0, v_value_2610_);
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v_key_2609_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = lean_array_push(v_query_2616_, v___x_2622_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 5, v___x_2623_);
v___x_2625_ = v___x_2619_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_scheme_2611_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_userInfo_2612_);
lean_ctor_set(v_reuseFailAlloc_2626_, 2, v_host_2613_);
lean_ctor_set(v_reuseFailAlloc_2626_, 3, v_port_2614_);
lean_ctor_set(v_reuseFailAlloc_2626_, 4, v_pathSegments_2615_);
lean_ctor_set(v_reuseFailAlloc_2626_, 5, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2626_, 6, v_fragment_2617_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryFlag(lean_object* v_b_2628_, lean_object* v_key_2629_){
_start:
{
lean_object* v_scheme_2630_; lean_object* v_userInfo_2631_; lean_object* v_host_2632_; lean_object* v_port_2633_; lean_object* v_pathSegments_2634_; lean_object* v_query_2635_; lean_object* v_fragment_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2646_; 
v_scheme_2630_ = lean_ctor_get(v_b_2628_, 0);
v_userInfo_2631_ = lean_ctor_get(v_b_2628_, 1);
v_host_2632_ = lean_ctor_get(v_b_2628_, 2);
v_port_2633_ = lean_ctor_get(v_b_2628_, 3);
v_pathSegments_2634_ = lean_ctor_get(v_b_2628_, 4);
v_query_2635_ = lean_ctor_get(v_b_2628_, 5);
v_fragment_2636_ = lean_ctor_get(v_b_2628_, 6);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_b_2628_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2638_ = v_b_2628_;
v_isShared_2639_ = v_isSharedCheck_2646_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_fragment_2636_);
lean_inc(v_query_2635_);
lean_inc(v_pathSegments_2634_);
lean_inc(v_port_2633_);
lean_inc(v_host_2632_);
lean_inc(v_userInfo_2631_);
lean_inc(v_scheme_2630_);
lean_dec(v_b_2628_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2646_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2640_ = lean_box(0);
v___x_2641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2641_, 0, v_key_2629_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
v___x_2642_ = lean_array_push(v_query_2635_, v___x_2641_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 5, v___x_2642_);
v___x_2644_ = v___x_2638_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_scheme_2630_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v_userInfo_2631_);
lean_ctor_set(v_reuseFailAlloc_2645_, 2, v_host_2632_);
lean_ctor_set(v_reuseFailAlloc_2645_, 3, v_port_2633_);
lean_ctor_set(v_reuseFailAlloc_2645_, 4, v_pathSegments_2634_);
lean_ctor_set(v_reuseFailAlloc_2645_, 5, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2645_, 6, v_fragment_2636_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setQuery(lean_object* v_b_2647_, lean_object* v_query_2648_){
_start:
{
lean_object* v_scheme_2649_; lean_object* v_userInfo_2650_; lean_object* v_host_2651_; lean_object* v_port_2652_; lean_object* v_pathSegments_2653_; lean_object* v_fragment_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
v_scheme_2649_ = lean_ctor_get(v_b_2647_, 0);
v_userInfo_2650_ = lean_ctor_get(v_b_2647_, 1);
v_host_2651_ = lean_ctor_get(v_b_2647_, 2);
v_port_2652_ = lean_ctor_get(v_b_2647_, 3);
v_pathSegments_2653_ = lean_ctor_get(v_b_2647_, 4);
v_fragment_2654_ = lean_ctor_get(v_b_2647_, 6);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_b_2647_);
if (v_isSharedCheck_2661_ == 0)
{
lean_object* v_unused_2662_; 
v_unused_2662_ = lean_ctor_get(v_b_2647_, 5);
lean_dec(v_unused_2662_);
v___x_2656_ = v_b_2647_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_fragment_2654_);
lean_inc(v_pathSegments_2653_);
lean_inc(v_port_2652_);
lean_inc(v_host_2651_);
lean_inc(v_userInfo_2650_);
lean_inc(v_scheme_2649_);
lean_dec(v_b_2647_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 5, v_query_2648_);
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_scheme_2649_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v_userInfo_2650_);
lean_ctor_set(v_reuseFailAlloc_2660_, 2, v_host_2651_);
lean_ctor_set(v_reuseFailAlloc_2660_, 3, v_port_2652_);
lean_ctor_set(v_reuseFailAlloc_2660_, 4, v_pathSegments_2653_);
lean_ctor_set(v_reuseFailAlloc_2660_, 5, v_query_2648_);
lean_ctor_set(v_reuseFailAlloc_2660_, 6, v_fragment_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setFragment(lean_object* v_b_2663_, lean_object* v_fragment_2664_){
_start:
{
lean_object* v_scheme_2665_; lean_object* v_userInfo_2666_; lean_object* v_host_2667_; lean_object* v_port_2668_; lean_object* v_pathSegments_2669_; lean_object* v_query_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2678_; 
v_scheme_2665_ = lean_ctor_get(v_b_2663_, 0);
v_userInfo_2666_ = lean_ctor_get(v_b_2663_, 1);
v_host_2667_ = lean_ctor_get(v_b_2663_, 2);
v_port_2668_ = lean_ctor_get(v_b_2663_, 3);
v_pathSegments_2669_ = lean_ctor_get(v_b_2663_, 4);
v_query_2670_ = lean_ctor_get(v_b_2663_, 5);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_b_2663_);
if (v_isSharedCheck_2678_ == 0)
{
lean_object* v_unused_2679_; 
v_unused_2679_ = lean_ctor_get(v_b_2663_, 6);
lean_dec(v_unused_2679_);
v___x_2672_ = v_b_2663_;
v_isShared_2673_ = v_isSharedCheck_2678_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_query_2670_);
lean_inc(v_pathSegments_2669_);
lean_inc(v_port_2668_);
lean_inc(v_host_2667_);
lean_inc(v_userInfo_2666_);
lean_inc(v_scheme_2665_);
lean_dec(v_b_2663_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2678_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2674_, 0, v_fragment_2664_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 6, v___x_2674_);
v___x_2676_ = v___x_2672_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_scheme_2665_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_userInfo_2666_);
lean_ctor_set(v_reuseFailAlloc_2677_, 2, v_host_2667_);
lean_ctor_set(v_reuseFailAlloc_2677_, 3, v_port_2668_);
lean_ctor_set(v_reuseFailAlloc_2677_, 4, v_pathSegments_2669_);
lean_ctor_set(v_reuseFailAlloc_2677_, 5, v_query_2670_);
lean_ctor_set(v_reuseFailAlloc_2677_, 6, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(size_t v_sz_2680_, size_t v_i_2681_, lean_object* v_bs_2682_){
_start:
{
uint8_t v___x_2683_; 
v___x_2683_ = lean_usize_dec_lt(v_i_2681_, v_sz_2680_);
if (v___x_2683_ == 0)
{
return v_bs_2682_;
}
else
{
lean_object* v_v_2684_; lean_object* v___x_2685_; lean_object* v_bs_x27_2686_; lean_object* v___x_2687_; size_t v___x_2688_; size_t v___x_2689_; lean_object* v___x_2690_; 
v_v_2684_ = lean_array_uget(v_bs_2682_, v_i_2681_);
v___x_2685_ = lean_unsigned_to_nat(0u);
v_bs_x27_2686_ = lean_array_uset(v_bs_2682_, v_i_2681_, v___x_2685_);
v___x_2687_ = l_Std_Http_URI_EncodedSegment_encode(v_v_2684_);
v___x_2688_ = ((size_t)1ULL);
v___x_2689_ = lean_usize_add(v_i_2681_, v___x_2688_);
v___x_2690_ = lean_array_uset(v_bs_x27_2686_, v_i_2681_, v___x_2687_);
v_i_2681_ = v___x_2689_;
v_bs_2682_ = v___x_2690_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0___boxed(lean_object* v_sz_2692_, lean_object* v_i_2693_, lean_object* v_bs_2694_){
_start:
{
size_t v_sz_boxed_2695_; size_t v_i_boxed_2696_; lean_object* v_res_2697_; 
v_sz_boxed_2695_ = lean_unbox_usize(v_sz_2692_);
lean_dec(v_sz_2692_);
v_i_boxed_2696_ = lean_unbox_usize(v_i_2693_);
lean_dec(v_i_2693_);
v_res_2697_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_boxed_2695_, v_i_boxed_2696_, v_bs_2694_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(size_t v_sz_2698_, size_t v_i_2699_, lean_object* v_bs_2700_){
_start:
{
uint8_t v___x_2701_; 
v___x_2701_ = lean_usize_dec_lt(v_i_2699_, v_sz_2698_);
if (v___x_2701_ == 0)
{
return v_bs_2700_;
}
else
{
lean_object* v_v_2702_; lean_object* v_fst_2703_; lean_object* v_snd_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2733_; 
v_v_2702_ = lean_array_uget(v_bs_2700_, v_i_2699_);
v_fst_2703_ = lean_ctor_get(v_v_2702_, 0);
v_snd_2704_ = lean_ctor_get(v_v_2702_, 1);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_v_2702_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2706_ = v_v_2702_;
v_isShared_2707_ = v_isSharedCheck_2733_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_snd_2704_);
lean_inc(v_fst_2703_);
lean_dec(v_v_2702_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2733_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2708_; lean_object* v_bs_x27_2709_; lean_object* v___y_2711_; lean_object* v___x_2716_; 
v___x_2708_ = lean_unsigned_to_nat(0u);
v_bs_x27_2709_ = lean_array_uset(v_bs_2700_, v_i_2699_, v___x_2708_);
v___x_2716_ = l_Std_Http_URI_EncodedQueryParam_encode(v_fst_2703_);
if (lean_obj_tag(v_snd_2704_) == 0)
{
lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2717_ = lean_box(0);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 1, v___x_2717_);
lean_ctor_set(v___x_2706_, 0, v___x_2716_);
v___x_2719_ = v___x_2706_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2716_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
v___y_2711_ = v___x_2719_;
goto v___jp_2710_;
}
}
else
{
lean_object* v_val_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2732_; 
v_val_2721_ = lean_ctor_get(v_snd_2704_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v_snd_2704_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2723_ = v_snd_2704_;
v_isShared_2724_ = v_isSharedCheck_2732_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_val_2721_);
lean_dec(v_snd_2704_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2732_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
v___x_2725_ = l_Std_Http_URI_EncodedQueryParam_encode(v_val_2721_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2725_);
v___x_2727_ = v___x_2723_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
lean_object* v___x_2729_; 
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 1, v___x_2727_);
lean_ctor_set(v___x_2706_, 0, v___x_2716_);
v___x_2729_ = v___x_2706_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2716_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
v___y_2711_ = v___x_2729_;
goto v___jp_2710_;
}
}
}
}
v___jp_2710_:
{
size_t v___x_2712_; size_t v___x_2713_; lean_object* v___x_2714_; 
v___x_2712_ = ((size_t)1ULL);
v___x_2713_ = lean_usize_add(v_i_2699_, v___x_2712_);
v___x_2714_ = lean_array_uset(v_bs_x27_2709_, v_i_2699_, v___y_2711_);
v_i_2699_ = v___x_2713_;
v_bs_2700_ = v___x_2714_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1___boxed(lean_object* v_sz_2734_, lean_object* v_i_2735_, lean_object* v_bs_2736_){
_start:
{
size_t v_sz_boxed_2737_; size_t v_i_boxed_2738_; lean_object* v_res_2739_; 
v_sz_boxed_2737_ = lean_unbox_usize(v_sz_2734_);
lean_dec(v_sz_2734_);
v_i_boxed_2738_ = lean_unbox_usize(v_i_2735_);
lean_dec(v_i_2735_);
v_res_2739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_boxed_2737_, v_i_boxed_2738_, v_bs_2736_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_build(lean_object* v_b_2740_){
_start:
{
lean_object* v___y_2742_; lean_object* v___y_2743_; uint8_t v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v_scheme_2763_; lean_object* v_userInfo_2764_; lean_object* v_host_2765_; lean_object* v_port_2766_; lean_object* v_pathSegments_2767_; lean_object* v_query_2768_; lean_object* v_fragment_2769_; lean_object* v___y_2771_; 
v_scheme_2763_ = lean_ctor_get(v_b_2740_, 0);
lean_inc(v_scheme_2763_);
v_userInfo_2764_ = lean_ctor_get(v_b_2740_, 1);
lean_inc(v_userInfo_2764_);
v_host_2765_ = lean_ctor_get(v_b_2740_, 2);
lean_inc(v_host_2765_);
v_port_2766_ = lean_ctor_get(v_b_2740_, 3);
lean_inc(v_port_2766_);
v_pathSegments_2767_ = lean_ctor_get(v_b_2740_, 4);
lean_inc_ref(v_pathSegments_2767_);
v_query_2768_ = lean_ctor_get(v_b_2740_, 5);
lean_inc_ref(v_query_2768_);
v_fragment_2769_ = lean_ctor_get(v_b_2740_, 6);
lean_inc(v_fragment_2769_);
lean_dec_ref(v_b_2740_);
if (lean_obj_tag(v_scheme_2763_) == 0)
{
lean_object* v___x_2784_; 
v___x_2784_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___y_2771_ = v___x_2784_;
goto v___jp_2770_;
}
else
{
lean_object* v_val_2785_; 
v_val_2785_ = lean_ctor_get(v_scheme_2763_, 0);
lean_inc(v_val_2785_);
lean_dec_ref_known(v_scheme_2763_, 1);
v___y_2771_ = v_val_2785_;
goto v___jp_2770_;
}
v___jp_2741_:
{
size_t v_sz_2748_; size_t v___x_2749_; lean_object* v___x_2750_; lean_object* v_path_2751_; size_t v_sz_2752_; lean_object* v_query_2753_; lean_object* v___x_2754_; lean_object* v_query_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; 
v_sz_2748_ = lean_array_size(v___y_2743_);
v___x_2749_ = ((size_t)0ULL);
v___x_2750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_2748_, v___x_2749_, v___y_2743_);
v_path_2751_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_path_2751_, 0, v___x_2750_);
lean_ctor_set_uint8(v_path_2751_, sizeof(void*)*1, v___y_2744_);
v_sz_2752_ = lean_array_size(v___y_2742_);
v_query_2753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_2752_, v___x_2749_, v___y_2742_);
v___x_2754_ = lean_array_to_list(v_query_2753_);
v_query_2755_ = lean_array_mk(v___x_2754_);
v___x_2756_ = lean_array_get_size(v_query_2755_);
v___x_2757_ = lean_unsigned_to_nat(0u);
v___x_2758_ = lean_nat_dec_eq(v___x_2756_, v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2759_, 0, v_query_2755_);
v___x_2760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2760_, 0, v___y_2745_);
lean_ctor_set(v___x_2760_, 1, v___y_2747_);
lean_ctor_set(v___x_2760_, 2, v_path_2751_);
lean_ctor_set(v___x_2760_, 3, v___x_2759_);
lean_ctor_set(v___x_2760_, 4, v___y_2746_);
return v___x_2760_;
}
else
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_dec_ref(v_query_2755_);
v___x_2761_ = lean_box(0);
v___x_2762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2762_, 0, v___y_2745_);
lean_ctor_set(v___x_2762_, 1, v___y_2747_);
lean_ctor_set(v___x_2762_, 2, v_path_2751_);
lean_ctor_set(v___x_2762_, 3, v___x_2761_);
lean_ctor_set(v___x_2762_, 4, v___y_2746_);
return v___x_2762_;
}
}
v___jp_2770_:
{
if (lean_obj_tag(v_host_2765_) == 0)
{
uint8_t v___x_2772_; lean_object* v___x_2773_; 
lean_dec(v_port_2766_);
lean_dec(v_userInfo_2764_);
v___x_2772_ = 1;
v___x_2773_ = lean_box(0);
v___y_2742_ = v_query_2768_;
v___y_2743_ = v_pathSegments_2767_;
v___y_2744_ = v___x_2772_;
v___y_2745_ = v___y_2771_;
v___y_2746_ = v_fragment_2769_;
v___y_2747_ = v___x_2773_;
goto v___jp_2741_;
}
else
{
lean_object* v_val_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2783_; 
v_val_2774_ = lean_ctor_get(v_host_2765_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_host_2765_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2776_ = v_host_2765_;
v_isShared_2777_ = v_isSharedCheck_2783_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_val_2774_);
lean_dec(v_host_2765_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2783_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
uint8_t v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2778_ = 1;
v___x_2779_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2779_, 0, v_userInfo_2764_);
lean_ctor_set(v___x_2779_, 1, v_val_2774_);
lean_ctor_set(v___x_2779_, 2, v_port_2766_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v___x_2779_);
v___x_2781_ = v___x_2776_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
v___y_2742_ = v_query_2768_;
v___y_2743_ = v_pathSegments_2767_;
v___y_2744_ = v___x_2778_;
v___y_2745_ = v___y_2771_;
v___y_2746_ = v_fragment_2769_;
v___y_2747_ = v___x_2781_;
goto v___jp_2741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withScheme_x21(lean_object* v_uri_2786_, lean_object* v_scheme_2787_){
_start:
{
lean_object* v_authority_2788_; lean_object* v_path_2789_; lean_object* v_query_2790_; lean_object* v_fragment_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2799_; 
v_authority_2788_ = lean_ctor_get(v_uri_2786_, 1);
v_path_2789_ = lean_ctor_get(v_uri_2786_, 2);
v_query_2790_ = lean_ctor_get(v_uri_2786_, 3);
v_fragment_2791_ = lean_ctor_get(v_uri_2786_, 4);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_uri_2786_);
if (v_isSharedCheck_2799_ == 0)
{
lean_object* v_unused_2800_; 
v_unused_2800_ = lean_ctor_get(v_uri_2786_, 0);
lean_dec(v_unused_2800_);
v___x_2793_ = v_uri_2786_;
v_isShared_2794_ = v_isSharedCheck_2799_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_fragment_2791_);
lean_inc(v_query_2790_);
lean_inc(v_path_2789_);
lean_inc(v_authority_2788_);
lean_dec(v_uri_2786_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2799_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2795_; lean_object* v___x_2797_; 
v___x_2795_ = l_Std_Http_URI_Scheme_ofString_x21(v_scheme_2787_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___x_2795_);
v___x_2797_ = v___x_2793_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2795_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_authority_2788_);
lean_ctor_set(v_reuseFailAlloc_2798_, 2, v_path_2789_);
lean_ctor_set(v_reuseFailAlloc_2798_, 3, v_query_2790_);
lean_ctor_set(v_reuseFailAlloc_2798_, 4, v_fragment_2791_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withAuthority(lean_object* v_uri_2801_, lean_object* v_authority_2802_){
_start:
{
lean_object* v_scheme_2803_; lean_object* v_path_2804_; lean_object* v_query_2805_; lean_object* v_fragment_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
v_scheme_2803_ = lean_ctor_get(v_uri_2801_, 0);
v_path_2804_ = lean_ctor_get(v_uri_2801_, 2);
v_query_2805_ = lean_ctor_get(v_uri_2801_, 3);
v_fragment_2806_ = lean_ctor_get(v_uri_2801_, 4);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_uri_2801_);
if (v_isSharedCheck_2813_ == 0)
{
lean_object* v_unused_2814_; 
v_unused_2814_ = lean_ctor_get(v_uri_2801_, 1);
lean_dec(v_unused_2814_);
v___x_2808_ = v_uri_2801_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_fragment_2806_);
lean_inc(v_query_2805_);
lean_inc(v_path_2804_);
lean_inc(v_scheme_2803_);
lean_dec(v_uri_2801_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 1, v_authority_2802_);
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_scheme_2803_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_authority_2802_);
lean_ctor_set(v_reuseFailAlloc_2812_, 2, v_path_2804_);
lean_ctor_set(v_reuseFailAlloc_2812_, 3, v_query_2805_);
lean_ctor_set(v_reuseFailAlloc_2812_, 4, v_fragment_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withPath(lean_object* v_uri_2815_, lean_object* v_path_2816_){
_start:
{
lean_object* v_scheme_2817_; lean_object* v_authority_2818_; lean_object* v_query_2819_; lean_object* v_fragment_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
v_scheme_2817_ = lean_ctor_get(v_uri_2815_, 0);
v_authority_2818_ = lean_ctor_get(v_uri_2815_, 1);
v_query_2819_ = lean_ctor_get(v_uri_2815_, 3);
v_fragment_2820_ = lean_ctor_get(v_uri_2815_, 4);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_uri_2815_);
if (v_isSharedCheck_2827_ == 0)
{
lean_object* v_unused_2828_; 
v_unused_2828_ = lean_ctor_get(v_uri_2815_, 2);
lean_dec(v_unused_2828_);
v___x_2822_ = v_uri_2815_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_fragment_2820_);
lean_inc(v_query_2819_);
lean_inc(v_authority_2818_);
lean_inc(v_scheme_2817_);
lean_dec(v_uri_2815_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 2, v_path_2816_);
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_scheme_2817_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_authority_2818_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_path_2816_);
lean_ctor_set(v_reuseFailAlloc_2826_, 3, v_query_2819_);
lean_ctor_set(v_reuseFailAlloc_2826_, 4, v_fragment_2820_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_withQuery(lean_object* v_uri_2829_, lean_object* v_query_2830_){
_start:
{
lean_object* v_scheme_2831_; lean_object* v_authority_2832_; lean_object* v_path_2833_; lean_object* v_fragment_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2842_; 
v_scheme_2831_ = lean_ctor_get(v_uri_2829_, 0);
v_authority_2832_ = lean_ctor_get(v_uri_2829_, 1);
v_path_2833_ = lean_ctor_get(v_uri_2829_, 2);
v_fragment_2834_ = lean_ctor_get(v_uri_2829_, 4);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_uri_2829_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; 
v_unused_2843_ = lean_ctor_get(v_uri_2829_, 3);
lean_dec(v_unused_2843_);
v___x_2836_ = v_uri_2829_;
v_isShared_2837_ = v_isSharedCheck_2842_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_fragment_2834_);
lean_inc(v_path_2833_);
lean_inc(v_authority_2832_);
lean_inc(v_scheme_2831_);
lean_dec(v_uri_2829_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2842_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2838_; lean_object* v___x_2840_; 
v___x_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2838_, 0, v_query_2830_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 3, v___x_2838_);
v___x_2840_ = v___x_2836_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_scheme_2831_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_authority_2832_);
lean_ctor_set(v_reuseFailAlloc_2841_, 2, v_path_2833_);
lean_ctor_set(v_reuseFailAlloc_2841_, 3, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2841_, 4, v_fragment_2834_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withFragment(lean_object* v_uri_2844_, lean_object* v_fragment_2845_){
_start:
{
lean_object* v_scheme_2846_; lean_object* v_authority_2847_; lean_object* v_path_2848_; lean_object* v_query_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
v_scheme_2846_ = lean_ctor_get(v_uri_2844_, 0);
v_authority_2847_ = lean_ctor_get(v_uri_2844_, 1);
v_path_2848_ = lean_ctor_get(v_uri_2844_, 2);
v_query_2849_ = lean_ctor_get(v_uri_2844_, 3);
v_isSharedCheck_2856_ = !lean_is_exclusive(v_uri_2844_);
if (v_isSharedCheck_2856_ == 0)
{
lean_object* v_unused_2857_; 
v_unused_2857_ = lean_ctor_get(v_uri_2844_, 4);
lean_dec(v_unused_2857_);
v___x_2851_ = v_uri_2844_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_query_2849_);
lean_inc(v_path_2848_);
lean_inc(v_authority_2847_);
lean_inc(v_scheme_2846_);
lean_dec(v_uri_2844_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 4, v_fragment_2845_);
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_scheme_2846_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_authority_2847_);
lean_ctor_set(v_reuseFailAlloc_2855_, 2, v_path_2848_);
lean_ctor_set(v_reuseFailAlloc_2855_, 3, v_query_2849_);
lean_ctor_set(v_reuseFailAlloc_2855_, 4, v_fragment_2845_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_normalize(lean_object* v_uri_2858_){
_start:
{
lean_object* v_scheme_2859_; lean_object* v_authority_2860_; lean_object* v_path_2861_; lean_object* v_query_2862_; lean_object* v_fragment_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2871_; 
v_scheme_2859_ = lean_ctor_get(v_uri_2858_, 0);
v_authority_2860_ = lean_ctor_get(v_uri_2858_, 1);
v_path_2861_ = lean_ctor_get(v_uri_2858_, 2);
v_query_2862_ = lean_ctor_get(v_uri_2858_, 3);
v_fragment_2863_ = lean_ctor_get(v_uri_2858_, 4);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_uri_2858_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2865_ = v_uri_2858_;
v_isShared_2866_ = v_isSharedCheck_2871_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_fragment_2863_);
lean_inc(v_query_2862_);
lean_inc(v_path_2861_);
lean_inc(v_authority_2860_);
lean_inc(v_scheme_2859_);
lean_dec(v_uri_2858_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2871_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2867_ = l_Std_Http_URI_Path_normalize(v_path_2861_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 2, v___x_2867_);
v___x_2869_ = v___x_2865_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_scheme_2859_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_authority_2860_);
lean_ctor_set(v_reuseFailAlloc_2870_, 2, v___x_2867_);
lean_ctor_set(v_reuseFailAlloc_2870_, 3, v_query_2862_);
lean_ctor_set(v_reuseFailAlloc_2870_, 4, v_fragment_2863_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___redArg(lean_object* v_x_2872_){
_start:
{
lean_object* v_scheme_2873_; lean_object* v_host_2874_; uint16_t v_port_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; uint8_t v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v_ctr_2896_; lean_object* v_a_2897_; 
v_scheme_2873_ = lean_ctor_get(v_x_2872_, 0);
lean_inc_ref(v_scheme_2873_);
v_host_2874_ = lean_ctor_get(v_x_2872_, 1);
lean_inc_ref(v_host_2874_);
v_port_2875_ = lean_ctor_get_uint16(v_x_2872_, sizeof(void*)*2);
lean_dec_ref(v_x_2872_);
v___x_2876_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2877_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2878_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2879_ = l_String_quote(v_scheme_2873_);
v___x_2880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
v___x_2881_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2878_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = 0;
v___x_2883_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2883_, 0, v___x_2881_);
lean_ctor_set_uint8(v___x_2883_, sizeof(void*)*1, v___x_2882_);
v___x_2884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2877_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2884_);
lean_ctor_set(v___x_2886_, 1, v___x_2885_);
v___x_2887_ = lean_box(1);
v___x_2888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2886_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
v___x_2889_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_2890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2888_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
v___x_2891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
lean_ctor_set(v___x_2891_, 1, v___x_2876_);
v___x_2892_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2893_ = lean_unsigned_to_nat(0u);
v___x_2894_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_2874_))
{
case 0:
{
lean_object* v_name_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2936_; 
v_name_2927_ = lean_ctor_get(v_host_2874_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v_host_2874_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2929_ = v_host_2874_;
v_isShared_2930_ = v_isSharedCheck_2936_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_name_2927_);
lean_dec(v_host_2874_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2936_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2934_; 
v___x_2931_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_2932_ = l_String_quote(v_name_2927_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set_tag(v___x_2929_, 3);
lean_ctor_set(v___x_2929_, 0, v___x_2932_);
v___x_2934_ = v___x_2929_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
v_ctr_2896_ = v___x_2931_;
v_a_2897_ = v___x_2934_;
goto v___jp_2895_;
}
}
}
case 1:
{
lean_object* v_ipv4_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2946_; 
v_ipv4_2937_ = lean_ctor_get(v_host_2874_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_host_2874_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2939_ = v_host_2874_;
v_isShared_2940_ = v_isSharedCheck_2946_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_ipv4_2937_);
lean_dec(v_host_2874_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2946_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2944_; 
v___x_2941_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_2942_ = lean_uv_ntop_v4(v_ipv4_2937_);
lean_dec_ref(v_ipv4_2937_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set_tag(v___x_2939_, 3);
lean_ctor_set(v___x_2939_, 0, v___x_2942_);
v___x_2944_ = v___x_2939_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2942_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
v_ctr_2896_ = v___x_2941_;
v_a_2897_ = v___x_2944_;
goto v___jp_2895_;
}
}
}
default: 
{
lean_object* v_ipv6_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2956_; 
v_ipv6_2947_ = lean_ctor_get(v_host_2874_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_host_2874_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2949_ = v_host_2874_;
v_isShared_2950_ = v_isSharedCheck_2956_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_ipv6_2947_);
lean_dec(v_host_2874_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2956_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2951_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_2952_ = lean_uv_ntop_v6(v_ipv6_2947_);
lean_dec_ref(v_ipv6_2947_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set_tag(v___x_2949_, 3);
lean_ctor_set(v___x_2949_, 0, v___x_2952_);
v___x_2954_ = v___x_2949_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2952_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
v_ctr_2896_ = v___x_2951_;
v_a_2897_ = v___x_2954_;
goto v___jp_2895_;
}
}
}
}
v___jp_2895_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2898_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_2899_ = lean_string_append(v___x_2898_, v_ctr_2896_);
v___x_2900_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
v___x_2901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
lean_ctor_set(v___x_2901_, 1, v___x_2887_);
v___x_2902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
lean_ctor_set(v___x_2902_, 1, v_a_2897_);
v___x_2903_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2894_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
lean_ctor_set_uint8(v___x_2904_, sizeof(void*)*1, v___x_2882_);
v___x_2905_ = l_Repr_addAppParen(v___x_2904_, v___x_2893_);
v___x_2906_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2892_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*1, v___x_2882_);
v___x_2908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2891_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
lean_ctor_set(v___x_2909_, 1, v___x_2885_);
v___x_2910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
lean_ctor_set(v___x_2910_, 1, v___x_2887_);
v___x_2911_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_2912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2910_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
lean_ctor_set(v___x_2913_, 1, v___x_2876_);
v___x_2914_ = lean_uint16_to_nat(v_port_2875_);
v___x_2915_ = l_Nat_reprFast(v___x_2914_);
v___x_2916_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
v___x_2917_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2892_);
lean_ctor_set(v___x_2917_, 1, v___x_2916_);
v___x_2918_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
lean_ctor_set_uint8(v___x_2918_, sizeof(void*)*1, v___x_2882_);
v___x_2919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2913_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2921_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
lean_ctor_set(v___x_2922_, 1, v___x_2919_);
v___x_2923_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2922_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2920_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
lean_ctor_set_uint8(v___x_2926_, sizeof(void*)*1, v___x_2882_);
return v___x_2926_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr(lean_object* v_x_2957_, lean_object* v_prec_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Std_Http_URI_instReprOrigin_repr___redArg(v_x_2957_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___boxed(lean_object* v_x_2960_, lean_object* v_prec_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Std_Http_URI_instReprOrigin_repr(v_x_2960_, v_prec_2961_);
lean_dec(v_prec_2961_);
return v_res_2962_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqOrigin_beq(lean_object* v_x_2965_, lean_object* v_x_2966_){
_start:
{
lean_object* v_scheme_2967_; lean_object* v_host_2968_; uint16_t v_port_2969_; lean_object* v_scheme_2970_; lean_object* v_host_2971_; uint16_t v_port_2972_; uint8_t v___x_2973_; 
v_scheme_2967_ = lean_ctor_get(v_x_2965_, 0);
v_host_2968_ = lean_ctor_get(v_x_2965_, 1);
v_port_2969_ = lean_ctor_get_uint16(v_x_2965_, sizeof(void*)*2);
v_scheme_2970_ = lean_ctor_get(v_x_2966_, 0);
v_host_2971_ = lean_ctor_get(v_x_2966_, 1);
v_port_2972_ = lean_ctor_get_uint16(v_x_2966_, sizeof(void*)*2);
v___x_2973_ = lean_string_dec_eq(v_scheme_2967_, v_scheme_2970_);
if (v___x_2973_ == 0)
{
return v___x_2973_;
}
else
{
uint8_t v___x_2974_; 
v___x_2974_ = l_Std_Http_URI_instBEqHost_beq(v_host_2968_, v_host_2971_);
if (v___x_2974_ == 0)
{
return v___x_2974_;
}
else
{
uint8_t v___x_2975_; 
v___x_2975_ = lean_uint16_dec_eq(v_port_2969_, v_port_2972_);
return v___x_2975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqOrigin_beq___boxed(lean_object* v_x_2976_, lean_object* v_x_2977_){
_start:
{
uint8_t v_res_2978_; lean_object* v_r_2979_; 
v_res_2978_ = l_Std_Http_URI_instBEqOrigin_beq(v_x_2976_, v_x_2977_);
lean_dec_ref(v_x_2977_);
lean_dec_ref(v_x_2976_);
v_r_2979_ = lean_box(v_res_2978_);
return v_r_2979_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Origin_hostHeader(lean_object* v_o_2982_){
_start:
{
lean_object* v_scheme_2983_; lean_object* v_host_2984_; uint16_t v_port_2985_; lean_object* v___y_2987_; uint16_t v_defaultPort_2993_; uint8_t v___x_2994_; 
v_scheme_2983_ = lean_ctor_get(v_o_2982_, 0);
lean_inc_ref(v_scheme_2983_);
v_host_2984_ = lean_ctor_get(v_o_2982_, 1);
lean_inc_ref(v_host_2984_);
v_port_2985_ = lean_ctor_get_uint16(v_o_2982_, sizeof(void*)*2);
lean_dec_ref(v_o_2982_);
v_defaultPort_2993_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_2983_);
lean_dec_ref(v_scheme_2983_);
v___x_2994_ = lean_uint16_dec_eq(v_port_2985_, v_defaultPort_2993_);
if (v___x_2994_ == 0)
{
switch(lean_obj_tag(v_host_2984_))
{
case 0:
{
lean_object* v_name_2995_; 
v_name_2995_ = lean_ctor_get(v_host_2984_, 0);
lean_inc_ref(v_name_2995_);
lean_dec_ref_known(v_host_2984_, 1);
v___y_2987_ = v_name_2995_;
goto v___jp_2986_;
}
case 1:
{
lean_object* v_ipv4_2996_; lean_object* v___x_2997_; 
v_ipv4_2996_ = lean_ctor_get(v_host_2984_, 0);
lean_inc_ref(v_ipv4_2996_);
lean_dec_ref_known(v_host_2984_, 1);
v___x_2997_ = lean_uv_ntop_v4(v_ipv4_2996_);
lean_dec_ref(v_ipv4_2996_);
v___y_2987_ = v___x_2997_;
goto v___jp_2986_;
}
default: 
{
lean_object* v_ipv6_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v_ipv6_2998_ = lean_ctor_get(v_host_2984_, 0);
lean_inc_ref(v_ipv6_2998_);
lean_dec_ref_known(v_host_2984_, 1);
v___x_2999_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3000_ = lean_uv_ntop_v6(v_ipv6_2998_);
lean_dec_ref(v_ipv6_2998_);
v___x_3001_ = lean_string_append(v___x_2999_, v___x_3000_);
lean_dec_ref(v___x_3000_);
v___x_3002_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3003_ = lean_string_append(v___x_3001_, v___x_3002_);
v___y_2987_ = v___x_3003_;
goto v___jp_2986_;
}
}
}
else
{
switch(lean_obj_tag(v_host_2984_))
{
case 0:
{
lean_object* v_name_3004_; 
v_name_3004_ = lean_ctor_get(v_host_2984_, 0);
lean_inc_ref(v_name_3004_);
lean_dec_ref_known(v_host_2984_, 1);
return v_name_3004_;
}
case 1:
{
lean_object* v_ipv4_3005_; lean_object* v___x_3006_; 
v_ipv4_3005_ = lean_ctor_get(v_host_2984_, 0);
lean_inc_ref(v_ipv4_3005_);
lean_dec_ref_known(v_host_2984_, 1);
v___x_3006_ = lean_uv_ntop_v4(v_ipv4_3005_);
lean_dec_ref(v_ipv4_3005_);
return v___x_3006_;
}
default: 
{
lean_object* v_ipv6_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v_ipv6_3007_ = lean_ctor_get(v_host_2984_, 0);
lean_inc_ref(v_ipv6_3007_);
lean_dec_ref_known(v_host_2984_, 1);
v___x_3008_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3009_ = lean_uv_ntop_v6(v_ipv6_3007_);
lean_dec_ref(v_ipv6_3007_);
v___x_3010_ = lean_string_append(v___x_3008_, v___x_3009_);
lean_dec_ref(v___x_3009_);
v___x_3011_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3012_ = lean_string_append(v___x_3010_, v___x_3011_);
return v___x_3012_;
}
}
}
v___jp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2988_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2989_ = lean_string_append(v___y_2987_, v___x_2988_);
v___x_2990_ = lean_uint16_to_nat(v_port_2985_);
v___x_2991_ = l_Nat_reprFast(v___x_2990_);
v___x_2992_ = lean_string_append(v___x_2989_, v___x_2991_);
lean_dec_ref(v___x_2991_);
return v___x_2992_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___redArg(lean_object* v_x_3019_){
_start:
{
lean_object* v_authority_3020_; lean_object* v_path_3021_; lean_object* v_query_3022_; lean_object* v_fragment_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; uint8_t v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_authority_3020_ = lean_ctor_get(v_x_3019_, 0);
lean_inc(v_authority_3020_);
v_path_3021_ = lean_ctor_get(v_x_3019_, 1);
lean_inc_ref(v_path_3021_);
v_query_3022_ = lean_ctor_get(v_x_3019_, 2);
lean_inc(v_query_3022_);
v_fragment_3023_ = lean_ctor_get(v_x_3019_, 3);
lean_inc(v_fragment_3023_);
lean_dec_ref(v_x_3019_);
v___x_3024_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_3025_ = ((lean_object*)(l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__1));
v___x_3026_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_3027_ = lean_unsigned_to_nat(0u);
v___x_3028_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_3020_, v___x_3027_);
v___x_3029_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3026_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = 0;
v___x_3031_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3031_, 0, v___x_3029_);
lean_ctor_set_uint8(v___x_3031_, sizeof(void*)*1, v___x_3030_);
v___x_3032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3025_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_3034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3032_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v___x_3035_ = lean_box(1);
v___x_3036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_3038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3036_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
v___x_3039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
lean_ctor_set(v___x_3039_, 1, v___x_3024_);
v___x_3040_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_3041_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3021_);
v___x_3042_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3040_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*1, v___x_3030_);
v___x_3044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3039_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
lean_ctor_set(v___x_3045_, 1, v___x_3033_);
v___x_3046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
lean_ctor_set(v___x_3046_, 1, v___x_3035_);
v___x_3047_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_3048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3046_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
lean_ctor_set(v___x_3049_, 1, v___x_3024_);
v___x_3050_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_3051_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3022_, v___x_3027_);
v___x_3052_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3050_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*1, v___x_3030_);
v___x_3054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3049_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v___x_3033_);
v___x_3056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
lean_ctor_set(v___x_3056_, 1, v___x_3035_);
v___x_3057_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_3058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3056_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v___x_3059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
lean_ctor_set(v___x_3059_, 1, v___x_3024_);
v___x_3060_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_3061_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_3023_, v___x_3027_);
v___x_3062_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3060_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
lean_ctor_set_uint8(v___x_3063_, sizeof(void*)*1, v___x_3030_);
v___x_3064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3059_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
v___x_3065_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_3066_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_3067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
lean_ctor_set(v___x_3067_, 1, v___x_3064_);
v___x_3068_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_3069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3067_);
lean_ctor_set(v___x_3069_, 1, v___x_3068_);
v___x_3070_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3065_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*1, v___x_3030_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr(lean_object* v_x_3072_, lean_object* v_prec_3073_){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_x_3072_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___boxed(lean_object* v_x_3075_, lean_object* v_prec_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Std_Http_URI_instReprRelativeRef_repr(v_x_3075_, v_prec_3076_);
lean_dec(v_prec_3076_);
return v_res_3077_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqRelativeRef_beq(lean_object* v_x_3085_, lean_object* v_x_3086_){
_start:
{
lean_object* v_authority_3087_; lean_object* v_path_3088_; lean_object* v_query_3089_; lean_object* v_fragment_3090_; lean_object* v_authority_3091_; lean_object* v_path_3092_; lean_object* v_query_3093_; lean_object* v_fragment_3094_; uint8_t v___x_3095_; 
v_authority_3087_ = lean_ctor_get(v_x_3085_, 0);
v_path_3088_ = lean_ctor_get(v_x_3085_, 1);
v_query_3089_ = lean_ctor_get(v_x_3085_, 2);
v_fragment_3090_ = lean_ctor_get(v_x_3085_, 3);
v_authority_3091_ = lean_ctor_get(v_x_3086_, 0);
v_path_3092_ = lean_ctor_get(v_x_3086_, 1);
v_query_3093_ = lean_ctor_get(v_x_3086_, 2);
v_fragment_3094_ = lean_ctor_get(v_x_3086_, 3);
v___x_3095_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_3087_, v_authority_3091_);
if (v___x_3095_ == 0)
{
return v___x_3095_;
}
else
{
uint8_t v___x_3096_; 
v___x_3096_ = l_Std_Http_URI_instBEqPath_beq(v_path_3088_, v_path_3092_);
if (v___x_3096_ == 0)
{
return v___x_3096_;
}
else
{
uint8_t v___x_3097_; 
v___x_3097_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_3089_, v_query_3093_);
if (v___x_3097_ == 0)
{
return v___x_3097_;
}
else
{
uint8_t v___x_3098_; 
v___x_3098_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_3090_, v_fragment_3094_);
return v___x_3098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqRelativeRef_beq___boxed(lean_object* v_x_3099_, lean_object* v_x_3100_){
_start:
{
uint8_t v_res_3101_; lean_object* v_r_3102_; 
v_res_3101_ = l_Std_Http_URI_instBEqRelativeRef_beq(v_x_3099_, v_x_3100_);
lean_dec_ref(v_x_3100_);
lean_dec_ref(v_x_3099_);
v_r_3102_ = lean_box(v_res_3101_);
return v_r_3102_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringRelativeRef___lam__1(lean_object* v___f_3105_, lean_object* v_ref_3106_){
_start:
{
lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v_authority_3115_; lean_object* v_path_3116_; lean_object* v_query_3117_; lean_object* v_fragment_3118_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3130_; 
v_authority_3115_ = lean_ctor_get(v_ref_3106_, 0);
lean_inc(v_authority_3115_);
v_path_3116_ = lean_ctor_get(v_ref_3106_, 1);
lean_inc_ref(v_path_3116_);
v_query_3117_ = lean_ctor_get(v_ref_3106_, 2);
lean_inc(v_query_3117_);
v_fragment_3118_ = lean_ctor_get(v_ref_3106_, 3);
lean_inc(v_fragment_3118_);
lean_dec_ref(v_ref_3106_);
if (lean_obj_tag(v_authority_3115_) == 0)
{
lean_object* v___x_3141_; 
v___x_3141_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3130_ = v___x_3141_;
goto v___jp_3129_;
}
else
{
lean_object* v_val_3142_; lean_object* v_userInfo_3143_; lean_object* v_host_3144_; lean_object* v_port_3145_; lean_object* v___x_3146_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3165_; 
v_val_3142_ = lean_ctor_get(v_authority_3115_, 0);
lean_inc(v_val_3142_);
lean_dec_ref_known(v_authority_3115_, 1);
v_userInfo_3143_ = lean_ctor_get(v_val_3142_, 0);
lean_inc(v_userInfo_3143_);
v_host_3144_ = lean_ctor_get(v_val_3142_, 1);
lean_inc_ref(v_host_3144_);
v_port_3145_ = lean_ctor_get(v_val_3142_, 2);
lean_inc(v_port_3145_);
lean_dec(v_val_3142_);
v___x_3146_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3143_) == 0)
{
lean_object* v___x_3175_; 
v___x_3175_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3165_ = v___x_3175_;
goto v___jp_3164_;
}
else
{
lean_object* v_val_3176_; lean_object* v_password_3177_; 
v_val_3176_ = lean_ctor_get(v_userInfo_3143_, 0);
lean_inc(v_val_3176_);
lean_dec_ref_known(v_userInfo_3143_, 1);
v_password_3177_ = lean_ctor_get(v_val_3176_, 1);
if (lean_obj_tag(v_password_3177_) == 0)
{
lean_object* v_username_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v_username_3178_ = lean_ctor_get(v_val_3176_, 0);
lean_inc_ref(v_username_3178_);
lean_dec(v_val_3176_);
v___x_3179_ = lean_string_from_utf8_unchecked(v_username_3178_);
v___x_3180_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3181_ = lean_string_append(v___x_3179_, v___x_3180_);
v___y_3165_ = v___x_3181_;
goto v___jp_3164_;
}
else
{
lean_object* v_username_3182_; lean_object* v_val_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
lean_inc_ref(v_password_3177_);
v_username_3182_ = lean_ctor_get(v_val_3176_, 0);
lean_inc_ref(v_username_3182_);
lean_dec(v_val_3176_);
v_val_3183_ = lean_ctor_get(v_password_3177_, 0);
lean_inc(v_val_3183_);
lean_dec_ref_known(v_password_3177_, 1);
v___x_3184_ = lean_string_from_utf8_unchecked(v_username_3182_);
v___x_3185_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3186_ = lean_string_append(v___x_3184_, v___x_3185_);
v___x_3187_ = lean_string_from_utf8_unchecked(v_val_3183_);
v___x_3188_ = lean_string_append(v___x_3186_, v___x_3187_);
lean_dec_ref(v___x_3187_);
v___x_3189_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3190_ = lean_string_append(v___x_3188_, v___x_3189_);
v___y_3165_ = v___x_3190_;
goto v___jp_3164_;
}
}
v___jp_3147_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3151_ = lean_string_append(v___y_3149_, v___y_3148_);
lean_dec_ref(v___y_3148_);
v___x_3152_ = lean_string_append(v___x_3151_, v___y_3150_);
lean_dec_ref(v___y_3150_);
v___x_3153_ = lean_string_append(v___x_3146_, v___x_3152_);
lean_dec_ref(v___x_3152_);
v___y_3130_ = v___x_3153_;
goto v___jp_3129_;
}
v___jp_3154_:
{
switch(lean_obj_tag(v_port_3145_))
{
case 0:
{
lean_object* v___x_3157_; 
v___x_3157_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3148_ = v___y_3156_;
v___y_3149_ = v___y_3155_;
v___y_3150_ = v___x_3157_;
goto v___jp_3147_;
}
case 1:
{
lean_object* v___x_3158_; 
v___x_3158_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3148_ = v___y_3156_;
v___y_3149_ = v___y_3155_;
v___y_3150_ = v___x_3158_;
goto v___jp_3147_;
}
default: 
{
uint16_t v_port_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_port_3159_ = lean_ctor_get_uint16(v_port_3145_, 0);
lean_dec_ref_known(v_port_3145_, 0);
v___x_3160_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3161_ = lean_uint16_to_nat(v_port_3159_);
v___x_3162_ = l_Nat_reprFast(v___x_3161_);
v___x_3163_ = lean_string_append(v___x_3160_, v___x_3162_);
lean_dec_ref(v___x_3162_);
v___y_3148_ = v___y_3156_;
v___y_3149_ = v___y_3155_;
v___y_3150_ = v___x_3163_;
goto v___jp_3147_;
}
}
}
v___jp_3164_:
{
switch(lean_obj_tag(v_host_3144_))
{
case 0:
{
lean_object* v_name_3166_; 
v_name_3166_ = lean_ctor_get(v_host_3144_, 0);
lean_inc_ref(v_name_3166_);
lean_dec_ref_known(v_host_3144_, 1);
v___y_3155_ = v___y_3165_;
v___y_3156_ = v_name_3166_;
goto v___jp_3154_;
}
case 1:
{
lean_object* v_ipv4_3167_; lean_object* v___x_3168_; 
v_ipv4_3167_ = lean_ctor_get(v_host_3144_, 0);
lean_inc_ref(v_ipv4_3167_);
lean_dec_ref_known(v_host_3144_, 1);
v___x_3168_ = lean_uv_ntop_v4(v_ipv4_3167_);
lean_dec_ref(v_ipv4_3167_);
v___y_3155_ = v___y_3165_;
v___y_3156_ = v___x_3168_;
goto v___jp_3154_;
}
default: 
{
lean_object* v_ipv6_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_ipv6_3169_ = lean_ctor_get(v_host_3144_, 0);
lean_inc_ref(v_ipv6_3169_);
lean_dec_ref_known(v_host_3144_, 1);
v___x_3170_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3171_ = lean_uv_ntop_v6(v_ipv6_3169_);
lean_dec_ref(v_ipv6_3169_);
v___x_3172_ = lean_string_append(v___x_3170_, v___x_3171_);
lean_dec_ref(v___x_3171_);
v___x_3173_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3174_ = lean_string_append(v___x_3172_, v___x_3173_);
v___y_3155_ = v___y_3165_;
v___y_3156_ = v___x_3174_;
goto v___jp_3154_;
}
}
}
}
v___jp_3107_:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = lean_string_append(v___y_3108_, v___y_3109_);
lean_dec_ref(v___y_3109_);
v___x_3113_ = lean_string_append(v___x_3112_, v___y_3110_);
lean_dec_ref(v___y_3110_);
v___x_3114_ = lean_string_append(v___x_3113_, v___y_3111_);
lean_dec_ref(v___y_3111_);
return v___x_3114_;
}
v___jp_3119_:
{
lean_object* v_queryPart_3122_; 
v_queryPart_3122_ = l_Std_Http_URI_Query_formatOption(v_query_3117_);
if (lean_obj_tag(v_fragment_3118_) == 0)
{
lean_object* v___x_3123_; 
v___x_3123_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3108_ = v___y_3120_;
v___y_3109_ = v___y_3121_;
v___y_3110_ = v_queryPart_3122_;
v___y_3111_ = v___x_3123_;
goto v___jp_3107_;
}
else
{
lean_object* v_val_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v_val_3124_ = lean_ctor_get(v_fragment_3118_, 0);
lean_inc(v_val_3124_);
lean_dec_ref_known(v_fragment_3118_, 1);
v___x_3125_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3126_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3124_);
v___x_3127_ = lean_string_from_utf8_unchecked(v___x_3126_);
v___x_3128_ = lean_string_append(v___x_3125_, v___x_3127_);
lean_dec_ref(v___x_3127_);
v___y_3108_ = v___y_3120_;
v___y_3109_ = v___y_3121_;
v___y_3110_ = v_queryPart_3122_;
v___y_3111_ = v___x_3128_;
goto v___jp_3107_;
}
}
v___jp_3129_:
{
lean_object* v_segments_3131_; uint8_t v_absolute_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; size_t v_sz_3135_; size_t v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v_result_3139_; 
v_segments_3131_ = lean_ctor_get(v_path_3116_, 0);
lean_inc_ref(v_segments_3131_);
v_absolute_3132_ = lean_ctor_get_uint8(v_path_3116_, sizeof(void*)*1);
lean_dec_ref(v_path_3116_);
v___x_3133_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3134_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3135_ = lean_array_size(v_segments_3131_);
v___x_3136_ = ((size_t)0ULL);
v___x_3137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3134_, v___f_3105_, v_sz_3135_, v___x_3136_, v_segments_3131_);
v___x_3138_ = lean_array_to_list(v___x_3137_);
v_result_3139_ = l_String_intercalate(v___x_3133_, v___x_3138_);
if (v_absolute_3132_ == 0)
{
v___y_3120_ = v___y_3130_;
v___y_3121_ = v_result_3139_;
goto v___jp_3119_;
}
else
{
lean_object* v___x_3140_; 
v___x_3140_ = lean_string_append(v___x_3133_, v_result_3139_);
lean_dec_ref(v_result_3139_);
v___y_3120_ = v___y_3130_;
v___y_3121_ = v___x_3140_;
goto v___jp_3119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___impl(lean_object* v_x_3194_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = lean_obj_tag_nat(v_x_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___impl___boxed(lean_object* v_x_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_Std_Http_URIReference_ctorIdx___impl(v_x_3196_);
lean_dec_ref(v_x_3196_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___redArg(lean_object* v_t_3198_, lean_object* v_k_3199_){
_start:
{
lean_object* v_uri_3200_; lean_object* v___x_3201_; 
v_uri_3200_ = lean_ctor_get(v_t_3198_, 0);
lean_inc_ref(v_uri_3200_);
lean_dec_ref(v_t_3198_);
v___x_3201_ = lean_apply_1(v_k_3199_, v_uri_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim(lean_object* v_motive_3202_, lean_object* v_ctorIdx_3203_, lean_object* v_t_3204_, lean_object* v_h_3205_, lean_object* v_k_3206_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3204_, v_k_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___boxed(lean_object* v_motive_3208_, lean_object* v_ctorIdx_3209_, lean_object* v_t_3210_, lean_object* v_h_3211_, lean_object* v_k_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Std_Http_URIReference_ctorElim(v_motive_3208_, v_ctorIdx_3209_, v_t_3210_, v_h_3211_, v_k_3212_);
lean_dec(v_ctorIdx_3209_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim___redArg(lean_object* v_t_3214_, lean_object* v_absolute_3215_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3214_, v_absolute_3215_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim(lean_object* v_motive_3217_, lean_object* v_t_3218_, lean_object* v_h_3219_, lean_object* v_absolute_3220_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3218_, v_absolute_3220_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim___redArg(lean_object* v_t_3222_, lean_object* v_relative_3223_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3222_, v_relative_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim(lean_object* v_motive_3225_, lean_object* v_t_3226_, lean_object* v_h_3227_, lean_object* v_relative_3228_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3226_, v_relative_3228_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr(lean_object* v_x_3242_, lean_object* v_prec_3243_){
_start:
{
if (lean_obj_tag(v_x_3242_) == 0)
{
lean_object* v_uri_3244_; lean_object* v___y_3246_; lean_object* v___x_3254_; uint8_t v___x_3255_; 
v_uri_3244_ = lean_ctor_get(v_x_3242_, 0);
lean_inc_ref(v_uri_3244_);
lean_dec_ref_known(v_x_3242_, 1);
v___x_3254_ = lean_unsigned_to_nat(1024u);
v___x_3255_ = lean_nat_dec_le(v___x_3254_, v_prec_3243_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; 
v___x_3256_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3246_ = v___x_3256_;
goto v___jp_3245_;
}
else
{
lean_object* v___x_3257_; 
v___x_3257_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3246_ = v___x_3257_;
goto v___jp_3245_;
}
v___jp_3245_:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; uint8_t v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3247_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__2));
v___x_3248_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3244_);
v___x_3249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
lean_inc(v___y_3246_);
v___x_3250_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___y_3246_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___x_3251_ = 0;
v___x_3252_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3252_, 0, v___x_3250_);
lean_ctor_set_uint8(v___x_3252_, sizeof(void*)*1, v___x_3251_);
v___x_3253_ = l_Repr_addAppParen(v___x_3252_, v_prec_3243_);
return v___x_3253_;
}
}
else
{
lean_object* v_ref_3258_; lean_object* v___y_3260_; lean_object* v___x_3268_; uint8_t v___x_3269_; 
v_ref_3258_ = lean_ctor_get(v_x_3242_, 0);
lean_inc_ref(v_ref_3258_);
lean_dec_ref_known(v_x_3242_, 1);
v___x_3268_ = lean_unsigned_to_nat(1024u);
v___x_3269_ = lean_nat_dec_le(v___x_3268_, v_prec_3243_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; 
v___x_3270_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3260_ = v___x_3270_;
goto v___jp_3259_;
}
else
{
lean_object* v___x_3271_; 
v___x_3271_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3260_ = v___x_3271_;
goto v___jp_3259_;
}
v___jp_3259_:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; uint8_t v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3261_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__5));
v___x_3262_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_ref_3258_);
v___x_3263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3261_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
lean_inc(v___y_3260_);
v___x_3264_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___y_3260_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
v___x_3265_ = 0;
v___x_3266_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3266_, 0, v___x_3264_);
lean_ctor_set_uint8(v___x_3266_, sizeof(void*)*1, v___x_3265_);
v___x_3267_ = l_Repr_addAppParen(v___x_3266_, v_prec_3243_);
return v___x_3267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr___boxed(lean_object* v_x_3272_, lean_object* v_prec_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Std_Http_instReprURIReference_repr(v_x_3272_, v_prec_3273_);
lean_dec(v_prec_3273_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURIReference___lam__2(lean_object* v___f_3281_, lean_object* v___f_3282_, lean_object* v_x_3283_){
_start:
{
lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; 
if (lean_obj_tag(v_x_3283_) == 0)
{
lean_object* v_uri_3292_; lean_object* v_scheme_3293_; lean_object* v_authority_3294_; lean_object* v_path_3295_; lean_object* v_query_3296_; lean_object* v_fragment_3297_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3320_; 
lean_dec_ref(v___f_3282_);
v_uri_3292_ = lean_ctor_get(v_x_3283_, 0);
lean_inc_ref(v_uri_3292_);
lean_dec_ref_known(v_x_3283_, 1);
v_scheme_3293_ = lean_ctor_get(v_uri_3292_, 0);
lean_inc_ref(v_scheme_3293_);
v_authority_3294_ = lean_ctor_get(v_uri_3292_, 1);
lean_inc(v_authority_3294_);
v_path_3295_ = lean_ctor_get(v_uri_3292_, 2);
lean_inc_ref(v_path_3295_);
v_query_3296_ = lean_ctor_get(v_uri_3292_, 3);
lean_inc(v_query_3296_);
v_fragment_3297_ = lean_ctor_get(v_uri_3292_, 4);
lean_inc(v_fragment_3297_);
lean_dec_ref(v_uri_3292_);
if (lean_obj_tag(v_authority_3294_) == 0)
{
lean_object* v___x_3331_; 
v___x_3331_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3320_ = v___x_3331_;
goto v___jp_3319_;
}
else
{
lean_object* v_val_3332_; lean_object* v_userInfo_3333_; lean_object* v_host_3334_; lean_object* v_port_3335_; lean_object* v___x_3336_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3355_; 
v_val_3332_ = lean_ctor_get(v_authority_3294_, 0);
lean_inc(v_val_3332_);
lean_dec_ref_known(v_authority_3294_, 1);
v_userInfo_3333_ = lean_ctor_get(v_val_3332_, 0);
lean_inc(v_userInfo_3333_);
v_host_3334_ = lean_ctor_get(v_val_3332_, 1);
lean_inc_ref(v_host_3334_);
v_port_3335_ = lean_ctor_get(v_val_3332_, 2);
lean_inc(v_port_3335_);
lean_dec(v_val_3332_);
v___x_3336_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3333_) == 0)
{
lean_object* v___x_3365_; 
v___x_3365_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3355_ = v___x_3365_;
goto v___jp_3354_;
}
else
{
lean_object* v_val_3366_; lean_object* v_password_3367_; 
v_val_3366_ = lean_ctor_get(v_userInfo_3333_, 0);
lean_inc(v_val_3366_);
lean_dec_ref_known(v_userInfo_3333_, 1);
v_password_3367_ = lean_ctor_get(v_val_3366_, 1);
if (lean_obj_tag(v_password_3367_) == 0)
{
lean_object* v_username_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v_username_3368_ = lean_ctor_get(v_val_3366_, 0);
lean_inc_ref(v_username_3368_);
lean_dec(v_val_3366_);
v___x_3369_ = lean_string_from_utf8_unchecked(v_username_3368_);
v___x_3370_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3371_ = lean_string_append(v___x_3369_, v___x_3370_);
v___y_3355_ = v___x_3371_;
goto v___jp_3354_;
}
else
{
lean_object* v_username_3372_; lean_object* v_val_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
lean_inc_ref(v_password_3367_);
v_username_3372_ = lean_ctor_get(v_val_3366_, 0);
lean_inc_ref(v_username_3372_);
lean_dec(v_val_3366_);
v_val_3373_ = lean_ctor_get(v_password_3367_, 0);
lean_inc(v_val_3373_);
lean_dec_ref_known(v_password_3367_, 1);
v___x_3374_ = lean_string_from_utf8_unchecked(v_username_3372_);
v___x_3375_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3376_ = lean_string_append(v___x_3374_, v___x_3375_);
v___x_3377_ = lean_string_from_utf8_unchecked(v_val_3373_);
v___x_3378_ = lean_string_append(v___x_3376_, v___x_3377_);
lean_dec_ref(v___x_3377_);
v___x_3379_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3380_ = lean_string_append(v___x_3378_, v___x_3379_);
v___y_3355_ = v___x_3380_;
goto v___jp_3354_;
}
}
v___jp_3337_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3341_ = lean_string_append(v___y_3338_, v___y_3339_);
lean_dec_ref(v___y_3339_);
v___x_3342_ = lean_string_append(v___x_3341_, v___y_3340_);
lean_dec_ref(v___y_3340_);
v___x_3343_ = lean_string_append(v___x_3336_, v___x_3342_);
lean_dec_ref(v___x_3342_);
v___y_3320_ = v___x_3343_;
goto v___jp_3319_;
}
v___jp_3344_:
{
switch(lean_obj_tag(v_port_3335_))
{
case 0:
{
lean_object* v___x_3347_; 
v___x_3347_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3338_ = v___y_3345_;
v___y_3339_ = v___y_3346_;
v___y_3340_ = v___x_3347_;
goto v___jp_3337_;
}
case 1:
{
lean_object* v___x_3348_; 
v___x_3348_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3338_ = v___y_3345_;
v___y_3339_ = v___y_3346_;
v___y_3340_ = v___x_3348_;
goto v___jp_3337_;
}
default: 
{
uint16_t v_port_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v_port_3349_ = lean_ctor_get_uint16(v_port_3335_, 0);
lean_dec_ref_known(v_port_3335_, 0);
v___x_3350_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3351_ = lean_uint16_to_nat(v_port_3349_);
v___x_3352_ = l_Nat_reprFast(v___x_3351_);
v___x_3353_ = lean_string_append(v___x_3350_, v___x_3352_);
lean_dec_ref(v___x_3352_);
v___y_3338_ = v___y_3345_;
v___y_3339_ = v___y_3346_;
v___y_3340_ = v___x_3353_;
goto v___jp_3337_;
}
}
}
v___jp_3354_:
{
switch(lean_obj_tag(v_host_3334_))
{
case 0:
{
lean_object* v_name_3356_; 
v_name_3356_ = lean_ctor_get(v_host_3334_, 0);
lean_inc_ref(v_name_3356_);
lean_dec_ref_known(v_host_3334_, 1);
v___y_3345_ = v___y_3355_;
v___y_3346_ = v_name_3356_;
goto v___jp_3344_;
}
case 1:
{
lean_object* v_ipv4_3357_; lean_object* v___x_3358_; 
v_ipv4_3357_ = lean_ctor_get(v_host_3334_, 0);
lean_inc_ref(v_ipv4_3357_);
lean_dec_ref_known(v_host_3334_, 1);
v___x_3358_ = lean_uv_ntop_v4(v_ipv4_3357_);
lean_dec_ref(v_ipv4_3357_);
v___y_3345_ = v___y_3355_;
v___y_3346_ = v___x_3358_;
goto v___jp_3344_;
}
default: 
{
lean_object* v_ipv6_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v_ipv6_3359_ = lean_ctor_get(v_host_3334_, 0);
lean_inc_ref(v_ipv6_3359_);
lean_dec_ref_known(v_host_3334_, 1);
v___x_3360_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3361_ = lean_uv_ntop_v6(v_ipv6_3359_);
lean_dec_ref(v_ipv6_3359_);
v___x_3362_ = lean_string_append(v___x_3360_, v___x_3361_);
lean_dec_ref(v___x_3361_);
v___x_3363_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3364_ = lean_string_append(v___x_3362_, v___x_3363_);
v___y_3345_ = v___y_3355_;
v___y_3346_ = v___x_3364_;
goto v___jp_3344_;
}
}
}
}
v___jp_3298_:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3303_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3304_ = lean_string_append(v_scheme_3293_, v___x_3303_);
v___x_3305_ = lean_string_append(v___x_3304_, v___y_3299_);
lean_dec_ref(v___y_3299_);
v___x_3306_ = lean_string_append(v___x_3305_, v___y_3301_);
lean_dec_ref(v___y_3301_);
v___x_3307_ = lean_string_append(v___x_3306_, v___y_3300_);
lean_dec_ref(v___y_3300_);
v___x_3308_ = lean_string_append(v___x_3307_, v___y_3302_);
lean_dec_ref(v___y_3302_);
return v___x_3308_;
}
v___jp_3309_:
{
lean_object* v_queryPart_3312_; 
v_queryPart_3312_ = l_Std_Http_URI_Query_formatOption(v_query_3296_);
if (lean_obj_tag(v_fragment_3297_) == 0)
{
lean_object* v___x_3313_; 
v___x_3313_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3299_ = v___y_3310_;
v___y_3300_ = v_queryPart_3312_;
v___y_3301_ = v___y_3311_;
v___y_3302_ = v___x_3313_;
goto v___jp_3298_;
}
else
{
lean_object* v_val_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v_val_3314_ = lean_ctor_get(v_fragment_3297_, 0);
lean_inc(v_val_3314_);
lean_dec_ref_known(v_fragment_3297_, 1);
v___x_3315_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3316_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3314_);
v___x_3317_ = lean_string_from_utf8_unchecked(v___x_3316_);
v___x_3318_ = lean_string_append(v___x_3315_, v___x_3317_);
lean_dec_ref(v___x_3317_);
v___y_3299_ = v___y_3310_;
v___y_3300_ = v_queryPart_3312_;
v___y_3301_ = v___y_3311_;
v___y_3302_ = v___x_3318_;
goto v___jp_3298_;
}
}
v___jp_3319_:
{
lean_object* v_segments_3321_; uint8_t v_absolute_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; size_t v_sz_3325_; size_t v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v_result_3329_; 
v_segments_3321_ = lean_ctor_get(v_path_3295_, 0);
lean_inc_ref(v_segments_3321_);
v_absolute_3322_ = lean_ctor_get_uint8(v_path_3295_, sizeof(void*)*1);
lean_dec_ref(v_path_3295_);
v___x_3323_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3324_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3325_ = lean_array_size(v_segments_3321_);
v___x_3326_ = ((size_t)0ULL);
v___x_3327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3324_, v___f_3281_, v_sz_3325_, v___x_3326_, v_segments_3321_);
v___x_3328_ = lean_array_to_list(v___x_3327_);
v_result_3329_ = l_String_intercalate(v___x_3323_, v___x_3328_);
if (v_absolute_3322_ == 0)
{
v___y_3310_ = v___y_3320_;
v___y_3311_ = v_result_3329_;
goto v___jp_3309_;
}
else
{
lean_object* v___x_3330_; 
v___x_3330_ = lean_string_append(v___x_3323_, v_result_3329_);
lean_dec_ref(v_result_3329_);
v___y_3310_ = v___y_3320_;
v___y_3311_ = v___x_3330_;
goto v___jp_3309_;
}
}
}
else
{
lean_object* v_ref_3381_; lean_object* v_authority_3382_; lean_object* v_path_3383_; lean_object* v_query_3384_; lean_object* v_fragment_3385_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3397_; 
lean_dec_ref(v___f_3281_);
v_ref_3381_ = lean_ctor_get(v_x_3283_, 0);
lean_inc_ref(v_ref_3381_);
lean_dec_ref_known(v_x_3283_, 1);
v_authority_3382_ = lean_ctor_get(v_ref_3381_, 0);
lean_inc(v_authority_3382_);
v_path_3383_ = lean_ctor_get(v_ref_3381_, 1);
lean_inc_ref(v_path_3383_);
v_query_3384_ = lean_ctor_get(v_ref_3381_, 2);
lean_inc(v_query_3384_);
v_fragment_3385_ = lean_ctor_get(v_ref_3381_, 3);
lean_inc(v_fragment_3385_);
lean_dec_ref(v_ref_3381_);
if (lean_obj_tag(v_authority_3382_) == 0)
{
lean_object* v___x_3408_; 
v___x_3408_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3397_ = v___x_3408_;
goto v___jp_3396_;
}
else
{
lean_object* v_val_3409_; lean_object* v_userInfo_3410_; lean_object* v_host_3411_; lean_object* v_port_3412_; lean_object* v___x_3413_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3432_; 
v_val_3409_ = lean_ctor_get(v_authority_3382_, 0);
lean_inc(v_val_3409_);
lean_dec_ref_known(v_authority_3382_, 1);
v_userInfo_3410_ = lean_ctor_get(v_val_3409_, 0);
lean_inc(v_userInfo_3410_);
v_host_3411_ = lean_ctor_get(v_val_3409_, 1);
lean_inc_ref(v_host_3411_);
v_port_3412_ = lean_ctor_get(v_val_3409_, 2);
lean_inc(v_port_3412_);
lean_dec(v_val_3409_);
v___x_3413_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3410_) == 0)
{
lean_object* v___x_3442_; 
v___x_3442_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3432_ = v___x_3442_;
goto v___jp_3431_;
}
else
{
lean_object* v_val_3443_; lean_object* v_password_3444_; 
v_val_3443_ = lean_ctor_get(v_userInfo_3410_, 0);
lean_inc(v_val_3443_);
lean_dec_ref_known(v_userInfo_3410_, 1);
v_password_3444_ = lean_ctor_get(v_val_3443_, 1);
if (lean_obj_tag(v_password_3444_) == 0)
{
lean_object* v_username_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v_username_3445_ = lean_ctor_get(v_val_3443_, 0);
lean_inc_ref(v_username_3445_);
lean_dec(v_val_3443_);
v___x_3446_ = lean_string_from_utf8_unchecked(v_username_3445_);
v___x_3447_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3448_ = lean_string_append(v___x_3446_, v___x_3447_);
v___y_3432_ = v___x_3448_;
goto v___jp_3431_;
}
else
{
lean_object* v_username_3449_; lean_object* v_val_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
lean_inc_ref(v_password_3444_);
v_username_3449_ = lean_ctor_get(v_val_3443_, 0);
lean_inc_ref(v_username_3449_);
lean_dec(v_val_3443_);
v_val_3450_ = lean_ctor_get(v_password_3444_, 0);
lean_inc(v_val_3450_);
lean_dec_ref_known(v_password_3444_, 1);
v___x_3451_ = lean_string_from_utf8_unchecked(v_username_3449_);
v___x_3452_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3453_ = lean_string_append(v___x_3451_, v___x_3452_);
v___x_3454_ = lean_string_from_utf8_unchecked(v_val_3450_);
v___x_3455_ = lean_string_append(v___x_3453_, v___x_3454_);
lean_dec_ref(v___x_3454_);
v___x_3456_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3457_ = lean_string_append(v___x_3455_, v___x_3456_);
v___y_3432_ = v___x_3457_;
goto v___jp_3431_;
}
}
v___jp_3414_:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3418_ = lean_string_append(v___y_3416_, v___y_3415_);
lean_dec_ref(v___y_3415_);
v___x_3419_ = lean_string_append(v___x_3418_, v___y_3417_);
lean_dec_ref(v___y_3417_);
v___x_3420_ = lean_string_append(v___x_3413_, v___x_3419_);
lean_dec_ref(v___x_3419_);
v___y_3397_ = v___x_3420_;
goto v___jp_3396_;
}
v___jp_3421_:
{
switch(lean_obj_tag(v_port_3412_))
{
case 0:
{
lean_object* v___x_3424_; 
v___x_3424_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3415_ = v___y_3423_;
v___y_3416_ = v___y_3422_;
v___y_3417_ = v___x_3424_;
goto v___jp_3414_;
}
case 1:
{
lean_object* v___x_3425_; 
v___x_3425_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3415_ = v___y_3423_;
v___y_3416_ = v___y_3422_;
v___y_3417_ = v___x_3425_;
goto v___jp_3414_;
}
default: 
{
uint16_t v_port_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v_port_3426_ = lean_ctor_get_uint16(v_port_3412_, 0);
lean_dec_ref_known(v_port_3412_, 0);
v___x_3427_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3428_ = lean_uint16_to_nat(v_port_3426_);
v___x_3429_ = l_Nat_reprFast(v___x_3428_);
v___x_3430_ = lean_string_append(v___x_3427_, v___x_3429_);
lean_dec_ref(v___x_3429_);
v___y_3415_ = v___y_3423_;
v___y_3416_ = v___y_3422_;
v___y_3417_ = v___x_3430_;
goto v___jp_3414_;
}
}
}
v___jp_3431_:
{
switch(lean_obj_tag(v_host_3411_))
{
case 0:
{
lean_object* v_name_3433_; 
v_name_3433_ = lean_ctor_get(v_host_3411_, 0);
lean_inc_ref(v_name_3433_);
lean_dec_ref_known(v_host_3411_, 1);
v___y_3422_ = v___y_3432_;
v___y_3423_ = v_name_3433_;
goto v___jp_3421_;
}
case 1:
{
lean_object* v_ipv4_3434_; lean_object* v___x_3435_; 
v_ipv4_3434_ = lean_ctor_get(v_host_3411_, 0);
lean_inc_ref(v_ipv4_3434_);
lean_dec_ref_known(v_host_3411_, 1);
v___x_3435_ = lean_uv_ntop_v4(v_ipv4_3434_);
lean_dec_ref(v_ipv4_3434_);
v___y_3422_ = v___y_3432_;
v___y_3423_ = v___x_3435_;
goto v___jp_3421_;
}
default: 
{
lean_object* v_ipv6_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v_ipv6_3436_ = lean_ctor_get(v_host_3411_, 0);
lean_inc_ref(v_ipv6_3436_);
lean_dec_ref_known(v_host_3411_, 1);
v___x_3437_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3438_ = lean_uv_ntop_v6(v_ipv6_3436_);
lean_dec_ref(v_ipv6_3436_);
v___x_3439_ = lean_string_append(v___x_3437_, v___x_3438_);
lean_dec_ref(v___x_3438_);
v___x_3440_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3441_ = lean_string_append(v___x_3439_, v___x_3440_);
v___y_3422_ = v___y_3432_;
v___y_3423_ = v___x_3441_;
goto v___jp_3421_;
}
}
}
}
v___jp_3386_:
{
lean_object* v_queryPart_3389_; 
v_queryPart_3389_ = l_Std_Http_URI_Query_formatOption(v_query_3384_);
if (lean_obj_tag(v_fragment_3385_) == 0)
{
lean_object* v___x_3390_; 
v___x_3390_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3285_ = v_queryPart_3389_;
v___y_3286_ = v___y_3388_;
v___y_3287_ = v___y_3387_;
v___y_3288_ = v___x_3390_;
goto v___jp_3284_;
}
else
{
lean_object* v_val_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v_val_3391_ = lean_ctor_get(v_fragment_3385_, 0);
lean_inc(v_val_3391_);
lean_dec_ref_known(v_fragment_3385_, 1);
v___x_3392_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3393_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3391_);
v___x_3394_ = lean_string_from_utf8_unchecked(v___x_3393_);
v___x_3395_ = lean_string_append(v___x_3392_, v___x_3394_);
lean_dec_ref(v___x_3394_);
v___y_3285_ = v_queryPart_3389_;
v___y_3286_ = v___y_3388_;
v___y_3287_ = v___y_3387_;
v___y_3288_ = v___x_3395_;
goto v___jp_3284_;
}
}
v___jp_3396_:
{
lean_object* v_segments_3398_; uint8_t v_absolute_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; size_t v_sz_3402_; size_t v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v_result_3406_; 
v_segments_3398_ = lean_ctor_get(v_path_3383_, 0);
lean_inc_ref(v_segments_3398_);
v_absolute_3399_ = lean_ctor_get_uint8(v_path_3383_, sizeof(void*)*1);
lean_dec_ref(v_path_3383_);
v___x_3400_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3401_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3402_ = lean_array_size(v_segments_3398_);
v___x_3403_ = ((size_t)0ULL);
v___x_3404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3401_, v___f_3282_, v_sz_3402_, v___x_3403_, v_segments_3398_);
v___x_3405_ = lean_array_to_list(v___x_3404_);
v_result_3406_ = l_String_intercalate(v___x_3400_, v___x_3405_);
if (v_absolute_3399_ == 0)
{
v___y_3387_ = v___y_3397_;
v___y_3388_ = v_result_3406_;
goto v___jp_3386_;
}
else
{
lean_object* v___x_3407_; 
v___x_3407_ = lean_string_append(v___x_3400_, v_result_3406_);
lean_dec_ref(v_result_3406_);
v___y_3387_ = v___y_3397_;
v___y_3388_ = v___x_3407_;
goto v___jp_3386_;
}
}
}
v___jp_3284_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3289_ = lean_string_append(v___y_3287_, v___y_3286_);
lean_dec_ref(v___y_3286_);
v___x_3290_ = lean_string_append(v___x_3289_, v___y_3285_);
lean_dec_ref(v___y_3285_);
v___x_3291_ = lean_string_append(v___x_3290_, v___y_3288_);
lean_dec_ref(v___y_3288_);
return v___x_3291_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___impl(lean_object* v_x_3461_){
_start:
{
lean_object* v___x_3462_; 
v___x_3462_ = lean_obj_tag_nat(v_x_3461_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___impl___boxed(lean_object* v_x_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Std_Http_RequestTarget_ctorIdx___impl(v_x_3463_);
lean_dec(v_x_3463_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___redArg(lean_object* v_t_3465_, lean_object* v_k_3466_){
_start:
{
switch(lean_obj_tag(v_t_3465_))
{
case 0:
{
lean_object* v_path_3467_; lean_object* v_query_3468_; lean_object* v___x_3469_; 
v_path_3467_ = lean_ctor_get(v_t_3465_, 0);
lean_inc_ref(v_path_3467_);
v_query_3468_ = lean_ctor_get(v_t_3465_, 1);
lean_inc(v_query_3468_);
lean_dec_ref_known(v_t_3465_, 2);
v___x_3469_ = lean_apply_2(v_k_3466_, v_path_3467_, v_query_3468_);
return v___x_3469_;
}
case 3:
{
return v_k_3466_;
}
default: 
{
lean_object* v_uri_3470_; lean_object* v___x_3471_; 
v_uri_3470_ = lean_ctor_get(v_t_3465_, 0);
lean_inc_ref(v_uri_3470_);
lean_dec(v_t_3465_);
v___x_3471_ = lean_apply_1(v_k_3466_, v_uri_3470_);
return v___x_3471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim(lean_object* v_motive_3472_, lean_object* v_ctorIdx_3473_, lean_object* v_t_3474_, lean_object* v_h_3475_, lean_object* v_k_3476_){
_start:
{
lean_object* v___x_3477_; 
v___x_3477_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3474_, v_k_3476_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___boxed(lean_object* v_motive_3478_, lean_object* v_ctorIdx_3479_, lean_object* v_t_3480_, lean_object* v_h_3481_, lean_object* v_k_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l_Std_Http_RequestTarget_ctorElim(v_motive_3478_, v_ctorIdx_3479_, v_t_3480_, v_h_3481_, v_k_3482_);
lean_dec(v_ctorIdx_3479_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim___redArg(lean_object* v_t_3484_, lean_object* v_originForm_3485_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3484_, v_originForm_3485_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim(lean_object* v_motive_3487_, lean_object* v_t_3488_, lean_object* v_h_3489_, lean_object* v_originForm_3490_){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3488_, v_originForm_3490_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim___redArg(lean_object* v_t_3492_, lean_object* v_absoluteForm_3493_){
_start:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3492_, v_absoluteForm_3493_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim(lean_object* v_motive_3495_, lean_object* v_t_3496_, lean_object* v_h_3497_, lean_object* v_absoluteForm_3498_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3496_, v_absoluteForm_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim___redArg(lean_object* v_t_3500_, lean_object* v_authorityForm_3501_){
_start:
{
lean_object* v___x_3502_; 
v___x_3502_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3500_, v_authorityForm_3501_);
return v___x_3502_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim(lean_object* v_motive_3503_, lean_object* v_t_3504_, lean_object* v_h_3505_, lean_object* v_authorityForm_3506_){
_start:
{
lean_object* v___x_3507_; 
v___x_3507_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3504_, v_authorityForm_3506_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim___redArg(lean_object* v_t_3508_, lean_object* v_asteriskForm_3509_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3508_, v_asteriskForm_3509_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim(lean_object* v_motive_3511_, lean_object* v_t_3512_, lean_object* v_h_3513_, lean_object* v_asteriskForm_3514_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3512_, v_asteriskForm_3514_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object* v_x_3542_, lean_object* v_prec_3543_){
_start:
{
lean_object* v___y_3545_; 
switch(lean_obj_tag(v_x_3542_))
{
case 0:
{
lean_object* v_path_3551_; lean_object* v_query_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3576_; 
v_path_3551_ = lean_ctor_get(v_x_3542_, 0);
v_query_3552_ = lean_ctor_get(v_x_3542_, 1);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_x_3542_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3554_ = v_x_3542_;
v_isShared_3555_ = v_isSharedCheck_3576_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_query_3552_);
lean_inc(v_path_3551_);
lean_dec(v_x_3542_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3576_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___y_3557_; lean_object* v___x_3572_; uint8_t v___x_3573_; 
v___x_3572_ = lean_unsigned_to_nat(1024u);
v___x_3573_ = lean_nat_dec_le(v___x_3572_, v_prec_3543_);
if (v___x_3573_ == 0)
{
lean_object* v___x_3574_; 
v___x_3574_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3557_ = v___x_3574_;
goto v___jp_3556_;
}
else
{
lean_object* v___x_3575_; 
v___x_3575_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3557_ = v___x_3575_;
goto v___jp_3556_;
}
v___jp_3556_:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3563_; 
v___x_3558_ = lean_box(1);
v___x_3559_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__4));
v___x_3560_ = lean_unsigned_to_nat(1024u);
v___x_3561_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3551_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set_tag(v___x_3554_, 5);
lean_ctor_set(v___x_3554_, 1, v___x_3561_);
lean_ctor_set(v___x_3554_, 0, v___x_3559_);
v___x_3563_ = v___x_3554_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3559_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; uint8_t v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
lean_ctor_set(v___x_3564_, 1, v___x_3558_);
v___x_3565_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3552_, v___x_3560_);
v___x_3566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3564_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
lean_inc(v___y_3557_);
v___x_3567_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3567_, 0, v___y_3557_);
lean_ctor_set(v___x_3567_, 1, v___x_3566_);
v___x_3568_ = 0;
v___x_3569_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3569_, 0, v___x_3567_);
lean_ctor_set_uint8(v___x_3569_, sizeof(void*)*1, v___x_3568_);
v___x_3570_ = l_Repr_addAppParen(v___x_3569_, v_prec_3543_);
return v___x_3570_;
}
}
}
}
case 1:
{
lean_object* v_uri_3577_; lean_object* v___y_3579_; lean_object* v___x_3587_; uint8_t v___x_3588_; 
v_uri_3577_ = lean_ctor_get(v_x_3542_, 0);
lean_inc_ref(v_uri_3577_);
lean_dec_ref_known(v_x_3542_, 1);
v___x_3587_ = lean_unsigned_to_nat(1024u);
v___x_3588_ = lean_nat_dec_le(v___x_3587_, v_prec_3543_);
if (v___x_3588_ == 0)
{
lean_object* v___x_3589_; 
v___x_3589_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3579_ = v___x_3589_;
goto v___jp_3578_;
}
else
{
lean_object* v___x_3590_; 
v___x_3590_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3579_ = v___x_3590_;
goto v___jp_3578_;
}
v___jp_3578_:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; uint8_t v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3580_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__7));
v___x_3581_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3577_);
v___x_3582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3580_);
lean_ctor_set(v___x_3582_, 1, v___x_3581_);
lean_inc(v___y_3579_);
v___x_3583_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___y_3579_);
lean_ctor_set(v___x_3583_, 1, v___x_3582_);
v___x_3584_ = 0;
v___x_3585_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3585_, 0, v___x_3583_);
lean_ctor_set_uint8(v___x_3585_, sizeof(void*)*1, v___x_3584_);
v___x_3586_ = l_Repr_addAppParen(v___x_3585_, v_prec_3543_);
return v___x_3586_;
}
}
case 2:
{
lean_object* v_authority_3591_; lean_object* v___y_3593_; lean_object* v___x_3601_; uint8_t v___x_3602_; 
v_authority_3591_ = lean_ctor_get(v_x_3542_, 0);
lean_inc_ref(v_authority_3591_);
lean_dec_ref_known(v_x_3542_, 1);
v___x_3601_ = lean_unsigned_to_nat(1024u);
v___x_3602_ = lean_nat_dec_le(v___x_3601_, v_prec_3543_);
if (v___x_3602_ == 0)
{
lean_object* v___x_3603_; 
v___x_3603_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3593_ = v___x_3603_;
goto v___jp_3592_;
}
else
{
lean_object* v___x_3604_; 
v___x_3604_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3593_ = v___x_3604_;
goto v___jp_3592_;
}
v___jp_3592_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3594_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__10));
v___x_3595_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_authority_3591_);
v___x_3596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3594_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
lean_inc(v___y_3593_);
v___x_3597_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___y_3593_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = 0;
v___x_3599_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3599_, 0, v___x_3597_);
lean_ctor_set_uint8(v___x_3599_, sizeof(void*)*1, v___x_3598_);
v___x_3600_ = l_Repr_addAppParen(v___x_3599_, v_prec_3543_);
return v___x_3600_;
}
}
default: 
{
lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3605_ = lean_unsigned_to_nat(1024u);
v___x_3606_ = lean_nat_dec_le(v___x_3605_, v_prec_3543_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; 
v___x_3607_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3545_ = v___x_3607_;
goto v___jp_3544_;
}
else
{
lean_object* v___x_3608_; 
v___x_3608_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3545_ = v___x_3608_;
goto v___jp_3544_;
}
}
}
v___jp_3544_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3546_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__1));
lean_inc(v___y_3545_);
v___x_3547_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___y_3545_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
v___x_3548_ = 0;
v___x_3549_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3549_, 0, v___x_3547_);
lean_ctor_set_uint8(v___x_3549_, sizeof(void*)*1, v___x_3548_);
v___x_3550_ = l_Repr_addAppParen(v___x_3549_, v_prec_3543_);
return v___x_3550_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr___boxed(lean_object* v_x_3609_, lean_object* v_prec_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Std_Http_instReprRequestTarget_repr(v_x_3609_, v_prec_3610_);
lean_dec(v_prec_3610_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path(lean_object* v_x_3619_){
_start:
{
switch(lean_obj_tag(v_x_3619_))
{
case 0:
{
lean_object* v_path_3620_; 
v_path_3620_ = lean_ctor_get(v_x_3619_, 0);
lean_inc_ref(v_path_3620_);
return v_path_3620_;
}
case 1:
{
lean_object* v_uri_3621_; lean_object* v_path_3622_; 
v_uri_3621_ = lean_ctor_get(v_x_3619_, 0);
v_path_3622_ = lean_ctor_get(v_uri_3621_, 2);
lean_inc_ref(v_path_3622_);
return v_path_3622_;
}
default: 
{
lean_object* v___x_3623_; 
v___x_3623_ = ((lean_object*)(l_Std_Http_RequestTarget_path___closed__1));
return v___x_3623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path___boxed(lean_object* v_x_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l_Std_Http_RequestTarget_path(v_x_3624_);
lean_dec(v_x_3624_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query(lean_object* v_x_3626_){
_start:
{
switch(lean_obj_tag(v_x_3626_))
{
case 0:
{
lean_object* v_query_3627_; 
v_query_3627_ = lean_ctor_get(v_x_3626_, 1);
if (lean_obj_tag(v_query_3627_) == 0)
{
lean_object* v___x_3628_; 
v___x_3628_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3628_;
}
else
{
lean_object* v_val_3629_; 
v_val_3629_ = lean_ctor_get(v_query_3627_, 0);
lean_inc(v_val_3629_);
return v_val_3629_;
}
}
case 1:
{
lean_object* v_uri_3630_; lean_object* v_query_3631_; 
v_uri_3630_ = lean_ctor_get(v_x_3626_, 0);
v_query_3631_ = lean_ctor_get(v_uri_3630_, 3);
if (lean_obj_tag(v_query_3631_) == 0)
{
lean_object* v___x_3632_; 
v___x_3632_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3632_;
}
else
{
lean_object* v_val_3633_; 
v_val_3633_ = lean_ctor_get(v_query_3631_, 0);
lean_inc(v_val_3633_);
return v_val_3633_;
}
}
default: 
{
lean_object* v___x_3634_; 
v___x_3634_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query___boxed(lean_object* v_x_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_Std_Http_RequestTarget_query(v_x_3635_);
lean_dec(v_x_3635_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authority_x3f(lean_object* v_x_3637_){
_start:
{
switch(lean_obj_tag(v_x_3637_))
{
case 2:
{
lean_object* v_authority_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
v_authority_3638_ = lean_ctor_get(v_x_3637_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_x_3637_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v_x_3637_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_authority_3638_);
lean_dec(v_x_3637_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
lean_ctor_set_tag(v___x_3640_, 1);
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_authority_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
case 1:
{
lean_object* v_uri_3646_; lean_object* v_authority_3647_; 
v_uri_3646_ = lean_ctor_get(v_x_3637_, 0);
lean_inc_ref(v_uri_3646_);
lean_dec_ref_known(v_x_3637_, 1);
v_authority_3647_ = lean_ctor_get(v_uri_3646_, 1);
lean_inc(v_authority_3647_);
lean_dec_ref(v_uri_3646_);
return v_authority_3647_;
}
default: 
{
lean_object* v___x_3648_; 
lean_dec(v_x_3637_);
v___x_3648_ = lean_box(0);
return v___x_3648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__2(lean_object* v___f_3650_, lean_object* v___f_3651_, lean_object* v_x_3652_){
_start:
{
lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; 
switch(lean_obj_tag(v_x_3652_))
{
case 0:
{
lean_object* v_path_3659_; lean_object* v_query_3660_; lean_object* v___y_3662_; lean_object* v_segments_3665_; uint8_t v_absolute_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; size_t v_sz_3669_; size_t v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v_result_3673_; 
lean_dec_ref(v___f_3651_);
v_path_3659_ = lean_ctor_get(v_x_3652_, 0);
lean_inc_ref(v_path_3659_);
v_query_3660_ = lean_ctor_get(v_x_3652_, 1);
lean_inc(v_query_3660_);
lean_dec_ref_known(v_x_3652_, 2);
v_segments_3665_ = lean_ctor_get(v_path_3659_, 0);
lean_inc_ref(v_segments_3665_);
v_absolute_3666_ = lean_ctor_get_uint8(v_path_3659_, sizeof(void*)*1);
lean_dec_ref(v_path_3659_);
v___x_3667_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3668_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3669_ = lean_array_size(v_segments_3665_);
v___x_3670_ = ((size_t)0ULL);
v___x_3671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3668_, v___f_3650_, v_sz_3669_, v___x_3670_, v_segments_3665_);
v___x_3672_ = lean_array_to_list(v___x_3671_);
v_result_3673_ = l_String_intercalate(v___x_3667_, v___x_3672_);
if (v_absolute_3666_ == 0)
{
v___y_3662_ = v_result_3673_;
goto v___jp_3661_;
}
else
{
lean_object* v___x_3674_; 
v___x_3674_ = lean_string_append(v___x_3667_, v_result_3673_);
lean_dec_ref(v_result_3673_);
v___y_3662_ = v___x_3674_;
goto v___jp_3661_;
}
v___jp_3661_:
{
lean_object* v_queryStr_3663_; lean_object* v___x_3664_; 
v_queryStr_3663_ = l_Std_Http_URI_Query_formatOption(v_query_3660_);
v___x_3664_ = lean_string_append(v___y_3662_, v_queryStr_3663_);
lean_dec_ref(v_queryStr_3663_);
return v___x_3664_;
}
}
case 1:
{
lean_object* v_uri_3675_; lean_object* v_scheme_3676_; lean_object* v_authority_3677_; lean_object* v_path_3678_; lean_object* v_query_3679_; lean_object* v_fragment_3680_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3703_; 
lean_dec_ref(v___f_3650_);
v_uri_3675_ = lean_ctor_get(v_x_3652_, 0);
lean_inc_ref(v_uri_3675_);
lean_dec_ref_known(v_x_3652_, 1);
v_scheme_3676_ = lean_ctor_get(v_uri_3675_, 0);
lean_inc_ref(v_scheme_3676_);
v_authority_3677_ = lean_ctor_get(v_uri_3675_, 1);
lean_inc(v_authority_3677_);
v_path_3678_ = lean_ctor_get(v_uri_3675_, 2);
lean_inc_ref(v_path_3678_);
v_query_3679_ = lean_ctor_get(v_uri_3675_, 3);
lean_inc(v_query_3679_);
v_fragment_3680_ = lean_ctor_get(v_uri_3675_, 4);
lean_inc(v_fragment_3680_);
lean_dec_ref(v_uri_3675_);
if (lean_obj_tag(v_authority_3677_) == 0)
{
lean_object* v___x_3714_; 
v___x_3714_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3703_ = v___x_3714_;
goto v___jp_3702_;
}
else
{
lean_object* v_val_3715_; lean_object* v_userInfo_3716_; lean_object* v_host_3717_; lean_object* v_port_3718_; lean_object* v___x_3719_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3738_; 
v_val_3715_ = lean_ctor_get(v_authority_3677_, 0);
lean_inc(v_val_3715_);
lean_dec_ref_known(v_authority_3677_, 1);
v_userInfo_3716_ = lean_ctor_get(v_val_3715_, 0);
lean_inc(v_userInfo_3716_);
v_host_3717_ = lean_ctor_get(v_val_3715_, 1);
lean_inc_ref(v_host_3717_);
v_port_3718_ = lean_ctor_get(v_val_3715_, 2);
lean_inc(v_port_3718_);
lean_dec(v_val_3715_);
v___x_3719_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3716_) == 0)
{
lean_object* v___x_3748_; 
v___x_3748_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3738_ = v___x_3748_;
goto v___jp_3737_;
}
else
{
lean_object* v_val_3749_; lean_object* v_password_3750_; 
v_val_3749_ = lean_ctor_get(v_userInfo_3716_, 0);
lean_inc(v_val_3749_);
lean_dec_ref_known(v_userInfo_3716_, 1);
v_password_3750_ = lean_ctor_get(v_val_3749_, 1);
if (lean_obj_tag(v_password_3750_) == 0)
{
lean_object* v_username_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v_username_3751_ = lean_ctor_get(v_val_3749_, 0);
lean_inc_ref(v_username_3751_);
lean_dec(v_val_3749_);
v___x_3752_ = lean_string_from_utf8_unchecked(v_username_3751_);
v___x_3753_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3754_ = lean_string_append(v___x_3752_, v___x_3753_);
v___y_3738_ = v___x_3754_;
goto v___jp_3737_;
}
else
{
lean_object* v_username_3755_; lean_object* v_val_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
lean_inc_ref(v_password_3750_);
v_username_3755_ = lean_ctor_get(v_val_3749_, 0);
lean_inc_ref(v_username_3755_);
lean_dec(v_val_3749_);
v_val_3756_ = lean_ctor_get(v_password_3750_, 0);
lean_inc(v_val_3756_);
lean_dec_ref_known(v_password_3750_, 1);
v___x_3757_ = lean_string_from_utf8_unchecked(v_username_3755_);
v___x_3758_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3759_ = lean_string_append(v___x_3757_, v___x_3758_);
v___x_3760_ = lean_string_from_utf8_unchecked(v_val_3756_);
v___x_3761_ = lean_string_append(v___x_3759_, v___x_3760_);
lean_dec_ref(v___x_3760_);
v___x_3762_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3763_ = lean_string_append(v___x_3761_, v___x_3762_);
v___y_3738_ = v___x_3763_;
goto v___jp_3737_;
}
}
v___jp_3720_:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3724_ = lean_string_append(v___y_3721_, v___y_3722_);
lean_dec_ref(v___y_3722_);
v___x_3725_ = lean_string_append(v___x_3724_, v___y_3723_);
lean_dec_ref(v___y_3723_);
v___x_3726_ = lean_string_append(v___x_3719_, v___x_3725_);
lean_dec_ref(v___x_3725_);
v___y_3703_ = v___x_3726_;
goto v___jp_3702_;
}
v___jp_3727_:
{
switch(lean_obj_tag(v_port_3718_))
{
case 0:
{
lean_object* v___x_3730_; 
v___x_3730_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3721_ = v___y_3728_;
v___y_3722_ = v___y_3729_;
v___y_3723_ = v___x_3730_;
goto v___jp_3720_;
}
case 1:
{
lean_object* v___x_3731_; 
v___x_3731_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3721_ = v___y_3728_;
v___y_3722_ = v___y_3729_;
v___y_3723_ = v___x_3731_;
goto v___jp_3720_;
}
default: 
{
uint16_t v_port_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v_port_3732_ = lean_ctor_get_uint16(v_port_3718_, 0);
lean_dec_ref_known(v_port_3718_, 0);
v___x_3733_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3734_ = lean_uint16_to_nat(v_port_3732_);
v___x_3735_ = l_Nat_reprFast(v___x_3734_);
v___x_3736_ = lean_string_append(v___x_3733_, v___x_3735_);
lean_dec_ref(v___x_3735_);
v___y_3721_ = v___y_3728_;
v___y_3722_ = v___y_3729_;
v___y_3723_ = v___x_3736_;
goto v___jp_3720_;
}
}
}
v___jp_3737_:
{
switch(lean_obj_tag(v_host_3717_))
{
case 0:
{
lean_object* v_name_3739_; 
v_name_3739_ = lean_ctor_get(v_host_3717_, 0);
lean_inc_ref(v_name_3739_);
lean_dec_ref_known(v_host_3717_, 1);
v___y_3728_ = v___y_3738_;
v___y_3729_ = v_name_3739_;
goto v___jp_3727_;
}
case 1:
{
lean_object* v_ipv4_3740_; lean_object* v___x_3741_; 
v_ipv4_3740_ = lean_ctor_get(v_host_3717_, 0);
lean_inc_ref(v_ipv4_3740_);
lean_dec_ref_known(v_host_3717_, 1);
v___x_3741_ = lean_uv_ntop_v4(v_ipv4_3740_);
lean_dec_ref(v_ipv4_3740_);
v___y_3728_ = v___y_3738_;
v___y_3729_ = v___x_3741_;
goto v___jp_3727_;
}
default: 
{
lean_object* v_ipv6_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
v_ipv6_3742_ = lean_ctor_get(v_host_3717_, 0);
lean_inc_ref(v_ipv6_3742_);
lean_dec_ref_known(v_host_3717_, 1);
v___x_3743_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3744_ = lean_uv_ntop_v6(v_ipv6_3742_);
lean_dec_ref(v_ipv6_3742_);
v___x_3745_ = lean_string_append(v___x_3743_, v___x_3744_);
lean_dec_ref(v___x_3744_);
v___x_3746_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3747_ = lean_string_append(v___x_3745_, v___x_3746_);
v___y_3728_ = v___y_3738_;
v___y_3729_ = v___x_3747_;
goto v___jp_3727_;
}
}
}
}
v___jp_3681_:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3686_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3687_ = lean_string_append(v_scheme_3676_, v___x_3686_);
v___x_3688_ = lean_string_append(v___x_3687_, v___y_3682_);
lean_dec_ref(v___y_3682_);
v___x_3689_ = lean_string_append(v___x_3688_, v___y_3684_);
lean_dec_ref(v___y_3684_);
v___x_3690_ = lean_string_append(v___x_3689_, v___y_3683_);
lean_dec_ref(v___y_3683_);
v___x_3691_ = lean_string_append(v___x_3690_, v___y_3685_);
lean_dec_ref(v___y_3685_);
return v___x_3691_;
}
v___jp_3692_:
{
lean_object* v_queryPart_3695_; 
v_queryPart_3695_ = l_Std_Http_URI_Query_formatOption(v_query_3679_);
if (lean_obj_tag(v_fragment_3680_) == 0)
{
lean_object* v___x_3696_; 
v___x_3696_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3682_ = v___y_3693_;
v___y_3683_ = v_queryPart_3695_;
v___y_3684_ = v___y_3694_;
v___y_3685_ = v___x_3696_;
goto v___jp_3681_;
}
else
{
lean_object* v_val_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v_val_3697_ = lean_ctor_get(v_fragment_3680_, 0);
lean_inc(v_val_3697_);
lean_dec_ref_known(v_fragment_3680_, 1);
v___x_3698_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3699_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3697_);
v___x_3700_ = lean_string_from_utf8_unchecked(v___x_3699_);
v___x_3701_ = lean_string_append(v___x_3698_, v___x_3700_);
lean_dec_ref(v___x_3700_);
v___y_3682_ = v___y_3693_;
v___y_3683_ = v_queryPart_3695_;
v___y_3684_ = v___y_3694_;
v___y_3685_ = v___x_3701_;
goto v___jp_3681_;
}
}
v___jp_3702_:
{
lean_object* v_segments_3704_; uint8_t v_absolute_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; size_t v_sz_3708_; size_t v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v_result_3712_; 
v_segments_3704_ = lean_ctor_get(v_path_3678_, 0);
lean_inc_ref(v_segments_3704_);
v_absolute_3705_ = lean_ctor_get_uint8(v_path_3678_, sizeof(void*)*1);
lean_dec_ref(v_path_3678_);
v___x_3706_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3707_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3708_ = lean_array_size(v_segments_3704_);
v___x_3709_ = ((size_t)0ULL);
v___x_3710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3707_, v___f_3651_, v_sz_3708_, v___x_3709_, v_segments_3704_);
v___x_3711_ = lean_array_to_list(v___x_3710_);
v_result_3712_ = l_String_intercalate(v___x_3706_, v___x_3711_);
if (v_absolute_3705_ == 0)
{
v___y_3693_ = v___y_3703_;
v___y_3694_ = v_result_3712_;
goto v___jp_3692_;
}
else
{
lean_object* v___x_3713_; 
v___x_3713_ = lean_string_append(v___x_3706_, v_result_3712_);
lean_dec_ref(v_result_3712_);
v___y_3693_ = v___y_3703_;
v___y_3694_ = v___x_3713_;
goto v___jp_3692_;
}
}
}
case 2:
{
lean_object* v_authority_3764_; lean_object* v_userInfo_3765_; lean_object* v_host_3766_; lean_object* v_port_3767_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3779_; 
lean_dec_ref(v___f_3651_);
lean_dec_ref(v___f_3650_);
v_authority_3764_ = lean_ctor_get(v_x_3652_, 0);
lean_inc_ref(v_authority_3764_);
lean_dec_ref_known(v_x_3652_, 1);
v_userInfo_3765_ = lean_ctor_get(v_authority_3764_, 0);
lean_inc(v_userInfo_3765_);
v_host_3766_ = lean_ctor_get(v_authority_3764_, 1);
lean_inc_ref(v_host_3766_);
v_port_3767_ = lean_ctor_get(v_authority_3764_, 2);
lean_inc(v_port_3767_);
lean_dec_ref(v_authority_3764_);
if (lean_obj_tag(v_userInfo_3765_) == 0)
{
lean_object* v___x_3789_; 
v___x_3789_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3779_ = v___x_3789_;
goto v___jp_3778_;
}
else
{
lean_object* v_val_3790_; lean_object* v_password_3791_; 
v_val_3790_ = lean_ctor_get(v_userInfo_3765_, 0);
lean_inc(v_val_3790_);
lean_dec_ref_known(v_userInfo_3765_, 1);
v_password_3791_ = lean_ctor_get(v_val_3790_, 1);
if (lean_obj_tag(v_password_3791_) == 0)
{
lean_object* v_username_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
v_username_3792_ = lean_ctor_get(v_val_3790_, 0);
lean_inc_ref(v_username_3792_);
lean_dec(v_val_3790_);
v___x_3793_ = lean_string_from_utf8_unchecked(v_username_3792_);
v___x_3794_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3795_ = lean_string_append(v___x_3793_, v___x_3794_);
v___y_3779_ = v___x_3795_;
goto v___jp_3778_;
}
else
{
lean_object* v_username_3796_; lean_object* v_val_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
lean_inc_ref(v_password_3791_);
v_username_3796_ = lean_ctor_get(v_val_3790_, 0);
lean_inc_ref(v_username_3796_);
lean_dec(v_val_3790_);
v_val_3797_ = lean_ctor_get(v_password_3791_, 0);
lean_inc(v_val_3797_);
lean_dec_ref_known(v_password_3791_, 1);
v___x_3798_ = lean_string_from_utf8_unchecked(v_username_3796_);
v___x_3799_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3800_ = lean_string_append(v___x_3798_, v___x_3799_);
v___x_3801_ = lean_string_from_utf8_unchecked(v_val_3797_);
v___x_3802_ = lean_string_append(v___x_3800_, v___x_3801_);
lean_dec_ref(v___x_3801_);
v___x_3803_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3804_ = lean_string_append(v___x_3802_, v___x_3803_);
v___y_3779_ = v___x_3804_;
goto v___jp_3778_;
}
}
v___jp_3768_:
{
switch(lean_obj_tag(v_port_3767_))
{
case 0:
{
lean_object* v___x_3771_; 
v___x_3771_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3654_ = v___y_3769_;
v___y_3655_ = v___y_3770_;
v___y_3656_ = v___x_3771_;
goto v___jp_3653_;
}
case 1:
{
lean_object* v___x_3772_; 
v___x_3772_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3654_ = v___y_3769_;
v___y_3655_ = v___y_3770_;
v___y_3656_ = v___x_3772_;
goto v___jp_3653_;
}
default: 
{
uint16_t v_port_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v_port_3773_ = lean_ctor_get_uint16(v_port_3767_, 0);
lean_dec_ref_known(v_port_3767_, 0);
v___x_3774_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3775_ = lean_uint16_to_nat(v_port_3773_);
v___x_3776_ = l_Nat_reprFast(v___x_3775_);
v___x_3777_ = lean_string_append(v___x_3774_, v___x_3776_);
lean_dec_ref(v___x_3776_);
v___y_3654_ = v___y_3769_;
v___y_3655_ = v___y_3770_;
v___y_3656_ = v___x_3777_;
goto v___jp_3653_;
}
}
}
v___jp_3778_:
{
switch(lean_obj_tag(v_host_3766_))
{
case 0:
{
lean_object* v_name_3780_; 
v_name_3780_ = lean_ctor_get(v_host_3766_, 0);
lean_inc_ref(v_name_3780_);
lean_dec_ref_known(v_host_3766_, 1);
v___y_3769_ = v___y_3779_;
v___y_3770_ = v_name_3780_;
goto v___jp_3768_;
}
case 1:
{
lean_object* v_ipv4_3781_; lean_object* v___x_3782_; 
v_ipv4_3781_ = lean_ctor_get(v_host_3766_, 0);
lean_inc_ref(v_ipv4_3781_);
lean_dec_ref_known(v_host_3766_, 1);
v___x_3782_ = lean_uv_ntop_v4(v_ipv4_3781_);
lean_dec_ref(v_ipv4_3781_);
v___y_3769_ = v___y_3779_;
v___y_3770_ = v___x_3782_;
goto v___jp_3768_;
}
default: 
{
lean_object* v_ipv6_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v_ipv6_3783_ = lean_ctor_get(v_host_3766_, 0);
lean_inc_ref(v_ipv6_3783_);
lean_dec_ref_known(v_host_3766_, 1);
v___x_3784_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3785_ = lean_uv_ntop_v6(v_ipv6_3783_);
lean_dec_ref(v_ipv6_3783_);
v___x_3786_ = lean_string_append(v___x_3784_, v___x_3785_);
lean_dec_ref(v___x_3785_);
v___x_3787_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3788_ = lean_string_append(v___x_3786_, v___x_3787_);
v___y_3769_ = v___y_3779_;
v___y_3770_ = v___x_3788_;
goto v___jp_3768_;
}
}
}
}
default: 
{
lean_object* v___x_3805_; 
lean_dec_ref(v___f_3651_);
lean_dec_ref(v___f_3650_);
v___x_3805_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__2___closed__0));
return v___x_3805_;
}
}
v___jp_3653_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = lean_string_append(v___y_3654_, v___y_3655_);
lean_dec_ref(v___y_3655_);
v___x_3658_ = lean_string_append(v___x_3657_, v___y_3656_);
lean_dec_ref(v___y_3656_);
return v___x_3658_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__2(lean_object* v___f_3809_, lean_object* v___f_3810_, lean_object* v_buffer_3811_, lean_object* v_target_3812_){
_start:
{
lean_object* v___y_3814_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; 
switch(lean_obj_tag(v_target_3812_))
{
case 0:
{
lean_object* v_path_3834_; lean_object* v_query_3835_; lean_object* v___y_3837_; lean_object* v_segments_3840_; uint8_t v_absolute_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; size_t v_sz_3844_; size_t v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v_result_3848_; 
lean_dec_ref(v___f_3810_);
v_path_3834_ = lean_ctor_get(v_target_3812_, 0);
lean_inc_ref(v_path_3834_);
v_query_3835_ = lean_ctor_get(v_target_3812_, 1);
lean_inc(v_query_3835_);
lean_dec_ref_known(v_target_3812_, 2);
v_segments_3840_ = lean_ctor_get(v_path_3834_, 0);
lean_inc_ref(v_segments_3840_);
v_absolute_3841_ = lean_ctor_get_uint8(v_path_3834_, sizeof(void*)*1);
lean_dec_ref(v_path_3834_);
v___x_3842_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3843_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3844_ = lean_array_size(v_segments_3840_);
v___x_3845_ = ((size_t)0ULL);
v___x_3846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3843_, v___f_3809_, v_sz_3844_, v___x_3845_, v_segments_3840_);
v___x_3847_ = lean_array_to_list(v___x_3846_);
v_result_3848_ = l_String_intercalate(v___x_3842_, v___x_3847_);
if (v_absolute_3841_ == 0)
{
v___y_3837_ = v_result_3848_;
goto v___jp_3836_;
}
else
{
lean_object* v___x_3849_; 
v___x_3849_ = lean_string_append(v___x_3842_, v_result_3848_);
lean_dec_ref(v_result_3848_);
v___y_3837_ = v___x_3849_;
goto v___jp_3836_;
}
v___jp_3836_:
{
lean_object* v_queryStr_3838_; lean_object* v___x_3839_; 
v_queryStr_3838_ = l_Std_Http_URI_Query_formatOption(v_query_3835_);
v___x_3839_ = lean_string_append(v___y_3837_, v_queryStr_3838_);
lean_dec_ref(v_queryStr_3838_);
v___y_3814_ = v___x_3839_;
goto v___jp_3813_;
}
}
case 1:
{
lean_object* v_uri_3850_; lean_object* v_scheme_3851_; lean_object* v_authority_3852_; lean_object* v_path_3853_; lean_object* v_query_3854_; lean_object* v_fragment_3855_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3878_; 
lean_dec_ref(v___f_3809_);
v_uri_3850_ = lean_ctor_get(v_target_3812_, 0);
lean_inc_ref(v_uri_3850_);
lean_dec_ref_known(v_target_3812_, 1);
v_scheme_3851_ = lean_ctor_get(v_uri_3850_, 0);
lean_inc_ref(v_scheme_3851_);
v_authority_3852_ = lean_ctor_get(v_uri_3850_, 1);
lean_inc(v_authority_3852_);
v_path_3853_ = lean_ctor_get(v_uri_3850_, 2);
lean_inc_ref(v_path_3853_);
v_query_3854_ = lean_ctor_get(v_uri_3850_, 3);
lean_inc(v_query_3854_);
v_fragment_3855_ = lean_ctor_get(v_uri_3850_, 4);
lean_inc(v_fragment_3855_);
lean_dec_ref(v_uri_3850_);
if (lean_obj_tag(v_authority_3852_) == 0)
{
lean_object* v___x_3889_; 
v___x_3889_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3878_ = v___x_3889_;
goto v___jp_3877_;
}
else
{
lean_object* v_val_3890_; lean_object* v_userInfo_3891_; lean_object* v_host_3892_; lean_object* v_port_3893_; lean_object* v___x_3894_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3913_; 
v_val_3890_ = lean_ctor_get(v_authority_3852_, 0);
lean_inc(v_val_3890_);
lean_dec_ref_known(v_authority_3852_, 1);
v_userInfo_3891_ = lean_ctor_get(v_val_3890_, 0);
lean_inc(v_userInfo_3891_);
v_host_3892_ = lean_ctor_get(v_val_3890_, 1);
lean_inc_ref(v_host_3892_);
v_port_3893_ = lean_ctor_get(v_val_3890_, 2);
lean_inc(v_port_3893_);
lean_dec(v_val_3890_);
v___x_3894_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3891_) == 0)
{
lean_object* v___x_3923_; 
v___x_3923_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3913_ = v___x_3923_;
goto v___jp_3912_;
}
else
{
lean_object* v_val_3924_; lean_object* v_password_3925_; 
v_val_3924_ = lean_ctor_get(v_userInfo_3891_, 0);
lean_inc(v_val_3924_);
lean_dec_ref_known(v_userInfo_3891_, 1);
v_password_3925_ = lean_ctor_get(v_val_3924_, 1);
if (lean_obj_tag(v_password_3925_) == 0)
{
lean_object* v_username_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v_username_3926_ = lean_ctor_get(v_val_3924_, 0);
lean_inc_ref(v_username_3926_);
lean_dec(v_val_3924_);
v___x_3927_ = lean_string_from_utf8_unchecked(v_username_3926_);
v___x_3928_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3929_ = lean_string_append(v___x_3927_, v___x_3928_);
v___y_3913_ = v___x_3929_;
goto v___jp_3912_;
}
else
{
lean_object* v_username_3930_; lean_object* v_val_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
lean_inc_ref(v_password_3925_);
v_username_3930_ = lean_ctor_get(v_val_3924_, 0);
lean_inc_ref(v_username_3930_);
lean_dec(v_val_3924_);
v_val_3931_ = lean_ctor_get(v_password_3925_, 0);
lean_inc(v_val_3931_);
lean_dec_ref_known(v_password_3925_, 1);
v___x_3932_ = lean_string_from_utf8_unchecked(v_username_3930_);
v___x_3933_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3934_ = lean_string_append(v___x_3932_, v___x_3933_);
v___x_3935_ = lean_string_from_utf8_unchecked(v_val_3931_);
v___x_3936_ = lean_string_append(v___x_3934_, v___x_3935_);
lean_dec_ref(v___x_3935_);
v___x_3937_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3938_ = lean_string_append(v___x_3936_, v___x_3937_);
v___y_3913_ = v___x_3938_;
goto v___jp_3912_;
}
}
v___jp_3895_:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3899_ = lean_string_append(v___y_3896_, v___y_3897_);
lean_dec_ref(v___y_3897_);
v___x_3900_ = lean_string_append(v___x_3899_, v___y_3898_);
lean_dec_ref(v___y_3898_);
v___x_3901_ = lean_string_append(v___x_3894_, v___x_3900_);
lean_dec_ref(v___x_3900_);
v___y_3878_ = v___x_3901_;
goto v___jp_3877_;
}
v___jp_3902_:
{
switch(lean_obj_tag(v_port_3893_))
{
case 0:
{
lean_object* v___x_3905_; 
v___x_3905_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3896_ = v___y_3903_;
v___y_3897_ = v___y_3904_;
v___y_3898_ = v___x_3905_;
goto v___jp_3895_;
}
case 1:
{
lean_object* v___x_3906_; 
v___x_3906_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3896_ = v___y_3903_;
v___y_3897_ = v___y_3904_;
v___y_3898_ = v___x_3906_;
goto v___jp_3895_;
}
default: 
{
uint16_t v_port_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v_port_3907_ = lean_ctor_get_uint16(v_port_3893_, 0);
lean_dec_ref_known(v_port_3893_, 0);
v___x_3908_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3909_ = lean_uint16_to_nat(v_port_3907_);
v___x_3910_ = l_Nat_reprFast(v___x_3909_);
v___x_3911_ = lean_string_append(v___x_3908_, v___x_3910_);
lean_dec_ref(v___x_3910_);
v___y_3896_ = v___y_3903_;
v___y_3897_ = v___y_3904_;
v___y_3898_ = v___x_3911_;
goto v___jp_3895_;
}
}
}
v___jp_3912_:
{
switch(lean_obj_tag(v_host_3892_))
{
case 0:
{
lean_object* v_name_3914_; 
v_name_3914_ = lean_ctor_get(v_host_3892_, 0);
lean_inc_ref(v_name_3914_);
lean_dec_ref_known(v_host_3892_, 1);
v___y_3903_ = v___y_3913_;
v___y_3904_ = v_name_3914_;
goto v___jp_3902_;
}
case 1:
{
lean_object* v_ipv4_3915_; lean_object* v___x_3916_; 
v_ipv4_3915_ = lean_ctor_get(v_host_3892_, 0);
lean_inc_ref(v_ipv4_3915_);
lean_dec_ref_known(v_host_3892_, 1);
v___x_3916_ = lean_uv_ntop_v4(v_ipv4_3915_);
lean_dec_ref(v_ipv4_3915_);
v___y_3903_ = v___y_3913_;
v___y_3904_ = v___x_3916_;
goto v___jp_3902_;
}
default: 
{
lean_object* v_ipv6_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v_ipv6_3917_ = lean_ctor_get(v_host_3892_, 0);
lean_inc_ref(v_ipv6_3917_);
lean_dec_ref_known(v_host_3892_, 1);
v___x_3918_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3919_ = lean_uv_ntop_v6(v_ipv6_3917_);
lean_dec_ref(v_ipv6_3917_);
v___x_3920_ = lean_string_append(v___x_3918_, v___x_3919_);
lean_dec_ref(v___x_3919_);
v___x_3921_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3922_ = lean_string_append(v___x_3920_, v___x_3921_);
v___y_3903_ = v___y_3913_;
v___y_3904_ = v___x_3922_;
goto v___jp_3902_;
}
}
}
}
v___jp_3856_:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3861_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3862_ = lean_string_append(v_scheme_3851_, v___x_3861_);
v___x_3863_ = lean_string_append(v___x_3862_, v___y_3857_);
lean_dec_ref(v___y_3857_);
v___x_3864_ = lean_string_append(v___x_3863_, v___y_3859_);
lean_dec_ref(v___y_3859_);
v___x_3865_ = lean_string_append(v___x_3864_, v___y_3858_);
lean_dec_ref(v___y_3858_);
v___x_3866_ = lean_string_append(v___x_3865_, v___y_3860_);
lean_dec_ref(v___y_3860_);
v___y_3814_ = v___x_3866_;
goto v___jp_3813_;
}
v___jp_3867_:
{
lean_object* v_queryPart_3870_; 
v_queryPart_3870_ = l_Std_Http_URI_Query_formatOption(v_query_3854_);
if (lean_obj_tag(v_fragment_3855_) == 0)
{
lean_object* v___x_3871_; 
v___x_3871_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3857_ = v___y_3868_;
v___y_3858_ = v_queryPart_3870_;
v___y_3859_ = v___y_3869_;
v___y_3860_ = v___x_3871_;
goto v___jp_3856_;
}
else
{
lean_object* v_val_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v_val_3872_ = lean_ctor_get(v_fragment_3855_, 0);
lean_inc(v_val_3872_);
lean_dec_ref_known(v_fragment_3855_, 1);
v___x_3873_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3874_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3872_);
v___x_3875_ = lean_string_from_utf8_unchecked(v___x_3874_);
v___x_3876_ = lean_string_append(v___x_3873_, v___x_3875_);
lean_dec_ref(v___x_3875_);
v___y_3857_ = v___y_3868_;
v___y_3858_ = v_queryPart_3870_;
v___y_3859_ = v___y_3869_;
v___y_3860_ = v___x_3876_;
goto v___jp_3856_;
}
}
v___jp_3877_:
{
lean_object* v_segments_3879_; uint8_t v_absolute_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; size_t v_sz_3883_; size_t v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v_result_3887_; 
v_segments_3879_ = lean_ctor_get(v_path_3853_, 0);
lean_inc_ref(v_segments_3879_);
v_absolute_3880_ = lean_ctor_get_uint8(v_path_3853_, sizeof(void*)*1);
lean_dec_ref(v_path_3853_);
v___x_3881_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3882_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3883_ = lean_array_size(v_segments_3879_);
v___x_3884_ = ((size_t)0ULL);
v___x_3885_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3882_, v___f_3810_, v_sz_3883_, v___x_3884_, v_segments_3879_);
v___x_3886_ = lean_array_to_list(v___x_3885_);
v_result_3887_ = l_String_intercalate(v___x_3881_, v___x_3886_);
if (v_absolute_3880_ == 0)
{
v___y_3868_ = v___y_3878_;
v___y_3869_ = v_result_3887_;
goto v___jp_3867_;
}
else
{
lean_object* v___x_3888_; 
v___x_3888_ = lean_string_append(v___x_3881_, v_result_3887_);
lean_dec_ref(v_result_3887_);
v___y_3868_ = v___y_3878_;
v___y_3869_ = v___x_3888_;
goto v___jp_3867_;
}
}
}
case 2:
{
lean_object* v_authority_3939_; lean_object* v_userInfo_3940_; lean_object* v_host_3941_; lean_object* v_port_3942_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3954_; 
lean_dec_ref(v___f_3810_);
lean_dec_ref(v___f_3809_);
v_authority_3939_ = lean_ctor_get(v_target_3812_, 0);
lean_inc_ref(v_authority_3939_);
lean_dec_ref_known(v_target_3812_, 1);
v_userInfo_3940_ = lean_ctor_get(v_authority_3939_, 0);
lean_inc(v_userInfo_3940_);
v_host_3941_ = lean_ctor_get(v_authority_3939_, 1);
lean_inc_ref(v_host_3941_);
v_port_3942_ = lean_ctor_get(v_authority_3939_, 2);
lean_inc(v_port_3942_);
lean_dec_ref(v_authority_3939_);
if (lean_obj_tag(v_userInfo_3940_) == 0)
{
lean_object* v___x_3964_; 
v___x_3964_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3954_ = v___x_3964_;
goto v___jp_3953_;
}
else
{
lean_object* v_val_3965_; lean_object* v_password_3966_; 
v_val_3965_ = lean_ctor_get(v_userInfo_3940_, 0);
lean_inc(v_val_3965_);
lean_dec_ref_known(v_userInfo_3940_, 1);
v_password_3966_ = lean_ctor_get(v_val_3965_, 1);
if (lean_obj_tag(v_password_3966_) == 0)
{
lean_object* v_username_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v_username_3967_ = lean_ctor_get(v_val_3965_, 0);
lean_inc_ref(v_username_3967_);
lean_dec(v_val_3965_);
v___x_3968_ = lean_string_from_utf8_unchecked(v_username_3967_);
v___x_3969_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3970_ = lean_string_append(v___x_3968_, v___x_3969_);
v___y_3954_ = v___x_3970_;
goto v___jp_3953_;
}
else
{
lean_object* v_username_3971_; lean_object* v_val_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
lean_inc_ref(v_password_3966_);
v_username_3971_ = lean_ctor_get(v_val_3965_, 0);
lean_inc_ref(v_username_3971_);
lean_dec(v_val_3965_);
v_val_3972_ = lean_ctor_get(v_password_3966_, 0);
lean_inc(v_val_3972_);
lean_dec_ref_known(v_password_3966_, 1);
v___x_3973_ = lean_string_from_utf8_unchecked(v_username_3971_);
v___x_3974_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3975_ = lean_string_append(v___x_3973_, v___x_3974_);
v___x_3976_ = lean_string_from_utf8_unchecked(v_val_3972_);
v___x_3977_ = lean_string_append(v___x_3975_, v___x_3976_);
lean_dec_ref(v___x_3976_);
v___x_3978_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3979_ = lean_string_append(v___x_3977_, v___x_3978_);
v___y_3954_ = v___x_3979_;
goto v___jp_3953_;
}
}
v___jp_3943_:
{
switch(lean_obj_tag(v_port_3942_))
{
case 0:
{
lean_object* v___x_3946_; 
v___x_3946_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3829_ = v___y_3944_;
v___y_3830_ = v___y_3945_;
v___y_3831_ = v___x_3946_;
goto v___jp_3828_;
}
case 1:
{
lean_object* v___x_3947_; 
v___x_3947_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3829_ = v___y_3944_;
v___y_3830_ = v___y_3945_;
v___y_3831_ = v___x_3947_;
goto v___jp_3828_;
}
default: 
{
uint16_t v_port_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v_port_3948_ = lean_ctor_get_uint16(v_port_3942_, 0);
lean_dec_ref_known(v_port_3942_, 0);
v___x_3949_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3950_ = lean_uint16_to_nat(v_port_3948_);
v___x_3951_ = l_Nat_reprFast(v___x_3950_);
v___x_3952_ = lean_string_append(v___x_3949_, v___x_3951_);
lean_dec_ref(v___x_3951_);
v___y_3829_ = v___y_3944_;
v___y_3830_ = v___y_3945_;
v___y_3831_ = v___x_3952_;
goto v___jp_3828_;
}
}
}
v___jp_3953_:
{
switch(lean_obj_tag(v_host_3941_))
{
case 0:
{
lean_object* v_name_3955_; 
v_name_3955_ = lean_ctor_get(v_host_3941_, 0);
lean_inc_ref(v_name_3955_);
lean_dec_ref_known(v_host_3941_, 1);
v___y_3944_ = v___y_3954_;
v___y_3945_ = v_name_3955_;
goto v___jp_3943_;
}
case 1:
{
lean_object* v_ipv4_3956_; lean_object* v___x_3957_; 
v_ipv4_3956_ = lean_ctor_get(v_host_3941_, 0);
lean_inc_ref(v_ipv4_3956_);
lean_dec_ref_known(v_host_3941_, 1);
v___x_3957_ = lean_uv_ntop_v4(v_ipv4_3956_);
lean_dec_ref(v_ipv4_3956_);
v___y_3944_ = v___y_3954_;
v___y_3945_ = v___x_3957_;
goto v___jp_3943_;
}
default: 
{
lean_object* v_ipv6_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v_ipv6_3958_ = lean_ctor_get(v_host_3941_, 0);
lean_inc_ref(v_ipv6_3958_);
lean_dec_ref_known(v_host_3941_, 1);
v___x_3959_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3960_ = lean_uv_ntop_v6(v_ipv6_3958_);
lean_dec_ref(v_ipv6_3958_);
v___x_3961_ = lean_string_append(v___x_3959_, v___x_3960_);
lean_dec_ref(v___x_3960_);
v___x_3962_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3963_ = lean_string_append(v___x_3961_, v___x_3962_);
v___y_3944_ = v___y_3954_;
v___y_3945_ = v___x_3963_;
goto v___jp_3943_;
}
}
}
}
default: 
{
lean_object* v___x_3980_; 
lean_dec_ref(v___f_3810_);
lean_dec_ref(v___f_3809_);
v___x_3980_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__2___closed__0));
v___y_3814_ = v___x_3980_;
goto v___jp_3813_;
}
}
v___jp_3813_:
{
lean_object* v_data_3815_; lean_object* v_size_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3827_; 
v_data_3815_ = lean_ctor_get(v_buffer_3811_, 0);
v_size_3816_ = lean_ctor_get(v_buffer_3811_, 1);
v_isSharedCheck_3827_ = !lean_is_exclusive(v_buffer_3811_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3818_ = v_buffer_3811_;
v_isShared_3819_ = v_isSharedCheck_3827_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_size_3816_);
lean_inc(v_data_3815_);
lean_dec(v_buffer_3811_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3827_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3825_; 
v___x_3820_ = lean_string_to_utf8(v___y_3814_);
lean_inc_ref(v___x_3820_);
v___x_3821_ = lean_array_push(v_data_3815_, v___x_3820_);
v___x_3822_ = lean_byte_array_size(v___x_3820_);
lean_dec_ref(v___x_3820_);
v___x_3823_ = lean_nat_add(v_size_3816_, v___x_3822_);
lean_dec(v_size_3816_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 1, v___x_3823_);
lean_ctor_set(v___x_3818_, 0, v___x_3821_);
v___x_3825_ = v___x_3818_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v___x_3823_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
v___jp_3828_:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3832_ = lean_string_append(v___y_3829_, v___y_3830_);
lean_dec_ref(v___y_3830_);
v___x_3833_ = lean_string_append(v___x_3832_, v___y_3831_);
lean_dec_ref(v___y_3831_);
v___y_3814_ = v___x_3833_;
goto v___jp_3813_;
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
