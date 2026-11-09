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
lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_List_getLast_x3f___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs_spec__0(lean_object* v_x_1793_, lean_object* v_x_1794_){
_start:
{
if (lean_obj_tag(v_x_1793_) == 0)
{
if (lean_obj_tag(v_x_1794_) == 0)
{
uint8_t v___x_1795_; 
v___x_1795_ = 1;
return v___x_1795_;
}
else
{
uint8_t v___x_1796_; 
v___x_1796_ = 0;
return v___x_1796_;
}
}
else
{
if (lean_obj_tag(v_x_1794_) == 0)
{
uint8_t v___x_1797_; 
v___x_1797_ = 0;
return v___x_1797_;
}
else
{
lean_object* v_val_1798_; lean_object* v_val_1799_; uint8_t v___x_1800_; 
v_val_1798_ = lean_ctor_get(v_x_1793_, 0);
v_val_1799_ = lean_ctor_get(v_x_1794_, 0);
v___x_1800_ = lean_string_dec_eq(v_val_1798_, v_val_1799_);
return v___x_1800_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs_spec__0___boxed(lean_object* v_x_1801_, lean_object* v_x_1802_){
_start:
{
uint8_t v_res_1803_; lean_object* v_r_1804_; 
v_res_1803_ = l_instBEqOption_beq___at___00__private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs_spec__0(v_x_1801_, v_x_1802_);
lean_dec(v_x_1802_);
lean_dec(v_x_1801_);
v_r_1804_ = lean_box(v_res_1803_);
return v_r_1804_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs(lean_object* v_key_1805_, lean_object* v_name_1806_){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1807_ = l_Std_Http_URI_EncodedQueryParam_decode(v_name_1806_);
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v_key_1805_);
v___x_1809_ = l_instBEqOption_beq___at___00__private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs_spec__0(v___x_1807_, v___x_1808_);
lean_dec_ref_known(v___x_1808_, 1);
lean_dec(v___x_1807_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs___boxed(lean_object* v_key_1810_, lean_object* v_name_1811_){
_start:
{
uint8_t v_res_1812_; lean_object* v_r_1813_; 
v_res_1812_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs(v_key_1810_, v_name_1811_);
lean_dec_ref(v_name_1811_);
v_r_1813_ = lean_box(v_res_1812_);
return v_r_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_find_x3f_spec__0(lean_object* v_key_1814_, lean_object* v_as_1815_, size_t v_sz_1816_, size_t v_i_1817_, lean_object* v_b_1818_){
_start:
{
uint8_t v___x_1819_; 
v___x_1819_ = lean_usize_dec_lt(v_i_1817_, v_sz_1816_);
if (v___x_1819_ == 0)
{
lean_dec_ref(v_key_1814_);
lean_inc_ref(v_b_1818_);
return v_b_1818_;
}
else
{
lean_object* v_a_1820_; lean_object* v_fst_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v_a_1820_ = lean_array_uget_borrowed(v_as_1815_, v_i_1817_);
v_fst_1821_ = lean_ctor_get(v_a_1820_, 0);
v___x_1822_ = lean_box(0);
lean_inc_ref(v_key_1814_);
v___x_1823_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs(v_key_1814_, v_fst_1821_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; size_t v___x_1825_; size_t v___x_1826_; 
v___x_1824_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v___x_1825_ = ((size_t)1ULL);
v___x_1826_ = lean_usize_add(v_i_1817_, v___x_1825_);
v_i_1817_ = v___x_1826_;
v_b_1818_ = v___x_1824_;
goto _start;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec_ref(v_key_1814_);
lean_inc(v_a_1820_);
v___x_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1828_, 0, v_a_1820_);
v___x_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v___x_1822_);
return v___x_1830_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_find_x3f_spec__0___boxed(lean_object* v_key_1831_, lean_object* v_as_1832_, lean_object* v_sz_1833_, lean_object* v_i_1834_, lean_object* v_b_1835_){
_start:
{
size_t v_sz_boxed_1836_; size_t v_i_boxed_1837_; lean_object* v_res_1838_; 
v_sz_boxed_1836_ = lean_unbox_usize(v_sz_1833_);
lean_dec(v_sz_1833_);
v_i_boxed_1837_ = lean_unbox_usize(v_i_1834_);
lean_dec(v_i_1834_);
v_res_1838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_find_x3f_spec__0(v_key_1831_, v_as_1832_, v_sz_boxed_1836_, v_i_boxed_1837_, v_b_1835_);
lean_dec_ref(v_b_1835_);
lean_dec_ref(v_as_1832_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f(lean_object* v_query_1839_, lean_object* v_key_1840_){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; size_t v_sz_1843_; size_t v___x_1844_; lean_object* v___x_1845_; lean_object* v_fst_1846_; 
v___x_1841_ = lean_box(0);
v___x_1842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v_sz_1843_ = lean_array_size(v_query_1839_);
v___x_1844_ = ((size_t)0ULL);
v___x_1845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_find_x3f_spec__0(v_key_1840_, v_query_1839_, v_sz_1843_, v___x_1844_, v___x_1842_);
v_fst_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_fst_1846_);
lean_dec_ref(v___x_1845_);
if (lean_obj_tag(v_fst_1846_) == 0)
{
return v___x_1841_;
}
else
{
lean_object* v_val_1847_; 
v_val_1847_ = lean_ctor_get(v_fst_1846_, 0);
lean_inc(v_val_1847_);
lean_dec_ref_known(v_fst_1846_, 1);
if (lean_obj_tag(v_val_1847_) == 0)
{
return v___x_1841_;
}
else
{
lean_object* v_val_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1856_; 
v_val_1848_ = lean_ctor_get(v_val_1847_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_val_1847_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1850_ = v_val_1847_;
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_val_1848_);
lean_dec(v_val_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v_snd_1852_; lean_object* v___x_1854_; 
v_snd_1852_ = lean_ctor_get(v_val_1848_, 1);
lean_inc(v_snd_1852_);
lean_dec(v_val_1848_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v_snd_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_snd_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f___boxed(lean_object* v_query_1857_, lean_object* v_key_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Std_Http_URI_Query_find_x3f(v_query_1857_, v_key_1858_);
lean_dec_ref(v_query_1857_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(lean_object* v_key_1860_, lean_object* v_as_1861_, size_t v_i_1862_, size_t v_stop_1863_, lean_object* v_b_1864_){
_start:
{
lean_object* v___y_1866_; uint8_t v___x_1870_; 
v___x_1870_ = lean_usize_dec_eq(v_i_1862_, v_stop_1863_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v_fst_1872_; lean_object* v_snd_1873_; uint8_t v___x_1874_; 
v___x_1871_ = lean_array_uget_borrowed(v_as_1861_, v_i_1862_);
v_fst_1872_ = lean_ctor_get(v___x_1871_, 0);
v_snd_1873_ = lean_ctor_get(v___x_1871_, 1);
v___x_1874_ = lean_sarray_dec_eq(v_fst_1872_, v_key_1860_);
if (v___x_1874_ == 0)
{
v___y_1866_ = v_b_1864_;
goto v___jp_1865_;
}
else
{
lean_object* v___x_1875_; 
lean_inc(v_snd_1873_);
v___x_1875_ = lean_array_push(v_b_1864_, v_snd_1873_);
v___y_1866_ = v___x_1875_;
goto v___jp_1865_;
}
}
else
{
return v_b_1864_;
}
v___jp_1865_:
{
size_t v___x_1867_; size_t v___x_1868_; 
v___x_1867_ = ((size_t)1ULL);
v___x_1868_ = lean_usize_add(v_i_1862_, v___x_1867_);
v_i_1862_ = v___x_1868_;
v_b_1864_ = v___y_1866_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0___boxed(lean_object* v_key_1876_, lean_object* v_as_1877_, lean_object* v_i_1878_, lean_object* v_stop_1879_, lean_object* v_b_1880_){
_start:
{
size_t v_i_boxed_1881_; size_t v_stop_boxed_1882_; lean_object* v_res_1883_; 
v_i_boxed_1881_ = lean_unbox_usize(v_i_1878_);
lean_dec(v_i_1878_);
v_stop_boxed_1882_ = lean_unbox_usize(v_stop_1879_);
lean_dec(v_stop_1879_);
v_res_1883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1876_, v_as_1877_, v_i_boxed_1881_, v_stop_boxed_1882_, v_b_1880_);
lean_dec_ref(v_as_1877_);
lean_dec_ref(v_key_1876_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(lean_object* v_key_1886_, lean_object* v_as_1887_, lean_object* v_start_1888_, lean_object* v_stop_1889_){
_start:
{
lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_1891_ = lean_nat_dec_lt(v_start_1888_, v_stop_1889_);
if (v___x_1891_ == 0)
{
return v___x_1890_;
}
else
{
lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1892_ = lean_array_get_size(v_as_1887_);
v___x_1893_ = lean_nat_dec_le(v_stop_1889_, v___x_1892_);
if (v___x_1893_ == 0)
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_nat_dec_lt(v_start_1888_, v___x_1892_);
if (v___x_1894_ == 0)
{
return v___x_1890_;
}
else
{
size_t v___x_1895_; size_t v___x_1896_; lean_object* v___x_1897_; 
v___x_1895_ = lean_usize_of_nat(v_start_1888_);
v___x_1896_ = lean_usize_of_nat(v___x_1892_);
v___x_1897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1886_, v_as_1887_, v___x_1895_, v___x_1896_, v___x_1890_);
return v___x_1897_;
}
}
else
{
size_t v___x_1898_; size_t v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = lean_usize_of_nat(v_start_1888_);
v___x_1899_ = lean_usize_of_nat(v_stop_1889_);
v___x_1900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1886_, v_as_1887_, v___x_1898_, v___x_1899_, v___x_1890_);
return v___x_1900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___boxed(lean_object* v_key_1901_, lean_object* v_as_1902_, lean_object* v_start_1903_, lean_object* v_stop_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1901_, v_as_1902_, v_start_1903_, v_stop_1904_);
lean_dec(v_stop_1904_);
lean_dec(v_start_1903_);
lean_dec_ref(v_as_1902_);
lean_dec_ref(v_key_1901_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded(lean_object* v_query_1906_, lean_object* v_key_1907_){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = lean_unsigned_to_nat(0u);
v___x_1909_ = lean_array_get_size(v_query_1906_);
v___x_1910_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1907_, v_query_1906_, v___x_1908_, v___x_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded___boxed(lean_object* v_query_1911_, lean_object* v_key_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1911_, v_key_1912_);
lean_dec_ref(v_key_1912_);
lean_dec_ref(v_query_1911_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0(lean_object* v_key_1914_, lean_object* v_as_1915_, size_t v_i_1916_, size_t v_stop_1917_, lean_object* v_b_1918_){
_start:
{
lean_object* v___y_1920_; uint8_t v___x_1924_; 
v___x_1924_ = lean_usize_dec_eq(v_i_1916_, v_stop_1917_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v_fst_1926_; lean_object* v_snd_1927_; uint8_t v___x_1928_; 
v___x_1925_ = lean_array_uget_borrowed(v_as_1915_, v_i_1916_);
v_fst_1926_ = lean_ctor_get(v___x_1925_, 0);
v_snd_1927_ = lean_ctor_get(v___x_1925_, 1);
lean_inc_ref(v_key_1914_);
v___x_1928_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs(v_key_1914_, v_fst_1926_);
if (v___x_1928_ == 0)
{
v___y_1920_ = v_b_1918_;
goto v___jp_1919_;
}
else
{
lean_object* v___x_1929_; 
lean_inc(v_snd_1927_);
v___x_1929_ = lean_array_push(v_b_1918_, v_snd_1927_);
v___y_1920_ = v___x_1929_;
goto v___jp_1919_;
}
}
else
{
lean_dec_ref(v_key_1914_);
return v_b_1918_;
}
v___jp_1919_:
{
size_t v___x_1921_; size_t v___x_1922_; 
v___x_1921_ = ((size_t)1ULL);
v___x_1922_ = lean_usize_add(v_i_1916_, v___x_1921_);
v_i_1916_ = v___x_1922_;
v_b_1918_ = v___y_1920_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0___boxed(lean_object* v_key_1930_, lean_object* v_as_1931_, lean_object* v_i_1932_, lean_object* v_stop_1933_, lean_object* v_b_1934_){
_start:
{
size_t v_i_boxed_1935_; size_t v_stop_boxed_1936_; lean_object* v_res_1937_; 
v_i_boxed_1935_ = lean_unbox_usize(v_i_1932_);
lean_dec(v_i_1932_);
v_stop_boxed_1936_ = lean_unbox_usize(v_stop_1933_);
lean_dec(v_stop_1933_);
v_res_1937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0(v_key_1930_, v_as_1931_, v_i_boxed_1935_, v_stop_boxed_1936_, v_b_1934_);
lean_dec_ref(v_as_1931_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0(lean_object* v_key_1938_, lean_object* v_as_1939_, lean_object* v_start_1940_, lean_object* v_stop_1941_){
_start:
{
lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1942_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_1943_ = lean_nat_dec_lt(v_start_1940_, v_stop_1941_);
if (v___x_1943_ == 0)
{
lean_dec_ref(v_key_1938_);
return v___x_1942_;
}
else
{
lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1944_ = lean_array_get_size(v_as_1939_);
v___x_1945_ = lean_nat_dec_le(v_stop_1941_, v___x_1944_);
if (v___x_1945_ == 0)
{
uint8_t v___x_1946_; 
v___x_1946_ = lean_nat_dec_lt(v_start_1940_, v___x_1944_);
if (v___x_1946_ == 0)
{
lean_dec_ref(v_key_1938_);
return v___x_1942_;
}
else
{
size_t v___x_1947_; size_t v___x_1948_; lean_object* v___x_1949_; 
v___x_1947_ = lean_usize_of_nat(v_start_1940_);
v___x_1948_ = lean_usize_of_nat(v___x_1944_);
v___x_1949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0(v_key_1938_, v_as_1939_, v___x_1947_, v___x_1948_, v___x_1942_);
return v___x_1949_;
}
}
else
{
size_t v___x_1950_; size_t v___x_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_usize_of_nat(v_start_1940_);
v___x_1951_ = lean_usize_of_nat(v_stop_1941_);
v___x_1952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0_spec__0(v_key_1938_, v_as_1939_, v___x_1950_, v___x_1951_, v___x_1942_);
return v___x_1952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0___boxed(lean_object* v_key_1953_, lean_object* v_as_1954_, lean_object* v_start_1955_, lean_object* v_stop_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0(v_key_1953_, v_as_1954_, v_start_1955_, v_stop_1956_);
lean_dec(v_stop_1956_);
lean_dec(v_start_1955_);
lean_dec_ref(v_as_1954_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll(lean_object* v_query_1958_, lean_object* v_key_1959_){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1960_ = lean_unsigned_to_nat(0u);
v___x_1961_ = lean_array_get_size(v_query_1958_);
v___x_1962_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAll_spec__0(v_key_1959_, v_query_1958_, v___x_1960_, v___x_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll___boxed(lean_object* v_query_1963_, lean_object* v_key_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Std_Http_URI_Query_findAll(v_query_1963_, v_key_1964_);
lean_dec_ref(v_query_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert(lean_object* v_query_1966_, lean_object* v_key_1967_, lean_object* v_value_1968_){
_start:
{
lean_object* v_encodedKey_1969_; lean_object* v_encodedValue_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v_encodedKey_1969_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1967_);
v_encodedValue_1970_ = l_Std_Http_URI_EncodedQueryParam_encode(v_value_1968_);
v___x_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1971_, 0, v_encodedValue_1970_);
v___x_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1972_, 0, v_encodedKey_1969_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
v___x_1973_ = lean_array_push(v_query_1966_, v___x_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object* v_query_1974_, lean_object* v_key_1975_, lean_object* v_value_1976_){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1977_, 0, v_key_1975_);
lean_ctor_set(v___x_1977_, 1, v_value_1976_);
v___x_1978_ = lean_array_push(v_query_1974_, v___x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_ofList(lean_object* v_pairs_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = lean_array_mk(v_pairs_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(lean_object* v_key_1984_, lean_object* v_as_1985_, size_t v_i_1986_, size_t v_stop_1987_){
_start:
{
uint8_t v___x_1988_; 
v___x_1988_ = lean_usize_dec_eq(v_i_1986_, v_stop_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v_fst_1990_; uint8_t v___x_1991_; 
v___x_1989_ = lean_array_uget_borrowed(v_as_1985_, v_i_1986_);
v_fst_1990_ = lean_ctor_get(v___x_1989_, 0);
v___x_1991_ = lean_sarray_dec_eq(v_fst_1990_, v_key_1984_);
if (v___x_1991_ == 0)
{
size_t v___x_1992_; size_t v___x_1993_; 
v___x_1992_ = ((size_t)1ULL);
v___x_1993_ = lean_usize_add(v_i_1986_, v___x_1992_);
v_i_1986_ = v___x_1993_;
goto _start;
}
else
{
return v___x_1991_;
}
}
else
{
uint8_t v___x_1995_; 
v___x_1995_ = 0;
return v___x_1995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(lean_object* v_key_1996_, lean_object* v_as_1997_, lean_object* v_i_1998_, lean_object* v_stop_1999_){
_start:
{
size_t v_i_boxed_2000_; size_t v_stop_boxed_2001_; uint8_t v_res_2002_; lean_object* v_r_2003_; 
v_i_boxed_2000_ = lean_unbox_usize(v_i_1998_);
lean_dec(v_i_1998_);
v_stop_boxed_2001_ = lean_unbox_usize(v_stop_1999_);
lean_dec(v_stop_1999_);
v_res_2002_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1996_, v_as_1997_, v_i_boxed_2000_, v_stop_boxed_2001_);
lean_dec_ref(v_as_1997_);
lean_dec_ref(v_key_1996_);
v_r_2003_ = lean_box(v_res_2002_);
return v_r_2003_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_containsEncoded(lean_object* v_query_2004_, lean_object* v_key_2005_){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2006_ = lean_unsigned_to_nat(0u);
v___x_2007_ = lean_array_get_size(v_query_2004_);
v___x_2008_ = lean_nat_dec_lt(v___x_2006_, v___x_2007_);
if (v___x_2008_ == 0)
{
return v___x_2008_;
}
else
{
if (v___x_2008_ == 0)
{
return v___x_2008_;
}
else
{
size_t v___x_2009_; size_t v___x_2010_; uint8_t v___x_2011_; 
v___x_2009_ = ((size_t)0ULL);
v___x_2010_ = lean_usize_of_nat(v___x_2007_);
v___x_2011_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_2005_, v_query_2004_, v___x_2009_, v___x_2010_);
return v___x_2011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_containsEncoded___boxed(lean_object* v_query_2012_, lean_object* v_key_2013_){
_start:
{
uint8_t v_res_2014_; lean_object* v_r_2015_; 
v_res_2014_ = l_Std_Http_URI_Query_containsEncoded(v_query_2012_, v_key_2013_);
lean_dec_ref(v_key_2013_);
lean_dec_ref(v_query_2012_);
v_r_2015_ = lean_box(v_res_2014_);
return v_r_2015_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_contains_spec__0(lean_object* v_key_2016_, lean_object* v_as_2017_, size_t v_i_2018_, size_t v_stop_2019_){
_start:
{
uint8_t v___x_2020_; 
v___x_2020_ = lean_usize_dec_eq(v_i_2018_, v_stop_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; lean_object* v_fst_2022_; uint8_t v___x_2023_; 
v___x_2021_ = lean_array_uget_borrowed(v_as_2017_, v_i_2018_);
v_fst_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc_ref(v_key_2016_);
v___x_2023_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs(v_key_2016_, v_fst_2022_);
if (v___x_2023_ == 0)
{
size_t v___x_2024_; size_t v___x_2025_; 
v___x_2024_ = ((size_t)1ULL);
v___x_2025_ = lean_usize_add(v_i_2018_, v___x_2024_);
v_i_2018_ = v___x_2025_;
goto _start;
}
else
{
lean_dec_ref(v_key_2016_);
return v___x_2023_;
}
}
else
{
uint8_t v___x_2027_; 
lean_dec_ref(v_key_2016_);
v___x_2027_ = 0;
return v___x_2027_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_contains_spec__0___boxed(lean_object* v_key_2028_, lean_object* v_as_2029_, lean_object* v_i_2030_, lean_object* v_stop_2031_){
_start:
{
size_t v_i_boxed_2032_; size_t v_stop_boxed_2033_; uint8_t v_res_2034_; lean_object* v_r_2035_; 
v_i_boxed_2032_ = lean_unbox_usize(v_i_2030_);
lean_dec(v_i_2030_);
v_stop_boxed_2033_ = lean_unbox_usize(v_stop_2031_);
lean_dec(v_stop_2031_);
v_res_2034_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_contains_spec__0(v_key_2028_, v_as_2029_, v_i_boxed_2032_, v_stop_boxed_2033_);
lean_dec_ref(v_as_2029_);
v_r_2035_ = lean_box(v_res_2034_);
return v_r_2035_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_contains(lean_object* v_query_2036_, lean_object* v_key_2037_){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2038_ = lean_unsigned_to_nat(0u);
v___x_2039_ = lean_array_get_size(v_query_2036_);
v___x_2040_ = lean_nat_dec_lt(v___x_2038_, v___x_2039_);
if (v___x_2040_ == 0)
{
lean_dec_ref(v_key_2037_);
return v___x_2040_;
}
else
{
if (v___x_2040_ == 0)
{
lean_dec_ref(v_key_2037_);
return v___x_2040_;
}
else
{
size_t v___x_2041_; size_t v___x_2042_; uint8_t v___x_2043_; 
v___x_2041_ = ((size_t)0ULL);
v___x_2042_ = lean_usize_of_nat(v___x_2039_);
v___x_2043_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_contains_spec__0(v_key_2037_, v_query_2036_, v___x_2041_, v___x_2042_);
return v___x_2043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_contains___boxed(lean_object* v_query_2044_, lean_object* v_key_2045_){
_start:
{
uint8_t v_res_2046_; lean_object* v_r_2047_; 
v_res_2046_ = l_Std_Http_URI_Query_contains(v_query_2044_, v_key_2045_);
lean_dec_ref(v_query_2044_);
v_r_2047_ = lean_box(v_res_2046_);
return v_r_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(lean_object* v_key_2048_, lean_object* v_as_2049_, size_t v_i_2050_, size_t v_stop_2051_, lean_object* v_b_2052_){
_start:
{
lean_object* v___y_2054_; uint8_t v___x_2058_; 
v___x_2058_ = lean_usize_dec_eq(v_i_2050_, v_stop_2051_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; lean_object* v_fst_2060_; uint8_t v___x_2061_; 
v___x_2059_ = lean_array_uget_borrowed(v_as_2049_, v_i_2050_);
v_fst_2060_ = lean_ctor_get(v___x_2059_, 0);
v___x_2061_ = lean_sarray_dec_eq(v_fst_2060_, v_key_2048_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; 
lean_inc(v___x_2059_);
v___x_2062_ = lean_array_push(v_b_2052_, v___x_2059_);
v___y_2054_ = v___x_2062_;
goto v___jp_2053_;
}
else
{
v___y_2054_ = v_b_2052_;
goto v___jp_2053_;
}
}
else
{
return v_b_2052_;
}
v___jp_2053_:
{
size_t v___x_2055_; size_t v___x_2056_; 
v___x_2055_ = ((size_t)1ULL);
v___x_2056_ = lean_usize_add(v_i_2050_, v___x_2055_);
v_i_2050_ = v___x_2056_;
v_b_2052_ = v___y_2054_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(lean_object* v_key_2063_, lean_object* v_as_2064_, lean_object* v_i_2065_, lean_object* v_stop_2066_, lean_object* v_b_2067_){
_start:
{
size_t v_i_boxed_2068_; size_t v_stop_boxed_2069_; lean_object* v_res_2070_; 
v_i_boxed_2068_ = lean_unbox_usize(v_i_2065_);
lean_dec(v_i_2065_);
v_stop_boxed_2069_ = lean_unbox_usize(v_stop_2066_);
lean_dec(v_stop_2066_);
v_res_2070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2063_, v_as_2064_, v_i_boxed_2068_, v_stop_boxed_2069_, v_b_2067_);
lean_dec_ref(v_as_2064_);
lean_dec_ref(v_key_2063_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded(lean_object* v_query_2071_, lean_object* v_key_2072_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2073_ = lean_unsigned_to_nat(0u);
v___x_2074_ = lean_array_get_size(v_query_2071_);
v___x_2075_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_2076_ = lean_nat_dec_lt(v___x_2073_, v___x_2074_);
if (v___x_2076_ == 0)
{
return v___x_2075_;
}
else
{
size_t v___x_2077_; size_t v___x_2078_; lean_object* v___x_2079_; 
v___x_2077_ = ((size_t)0ULL);
v___x_2078_ = lean_usize_of_nat(v___x_2074_);
v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2072_, v_query_2071_, v___x_2077_, v___x_2078_, v___x_2075_);
return v___x_2079_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded___boxed(lean_object* v_query_2080_, lean_object* v_key_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Std_Http_URI_Query_eraseEncoded(v_query_2080_, v_key_2081_);
lean_dec_ref(v_key_2081_);
lean_dec_ref(v_query_2080_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_erase_spec__0(lean_object* v_key_2083_, lean_object* v_as_2084_, size_t v_i_2085_, size_t v_stop_2086_, lean_object* v_b_2087_){
_start:
{
lean_object* v___y_2089_; uint8_t v___x_2093_; 
v___x_2093_ = lean_usize_dec_eq(v_i_2085_, v_stop_2086_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v_fst_2095_; uint8_t v___x_2096_; 
v___x_2094_ = lean_array_uget_borrowed(v_as_2084_, v_i_2085_);
v_fst_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc_ref(v_key_2083_);
v___x_2096_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs(v_key_2083_, v_fst_2095_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; 
lean_inc(v___x_2094_);
v___x_2097_ = lean_array_push(v_b_2087_, v___x_2094_);
v___y_2089_ = v___x_2097_;
goto v___jp_2088_;
}
else
{
v___y_2089_ = v_b_2087_;
goto v___jp_2088_;
}
}
else
{
lean_dec_ref(v_key_2083_);
return v_b_2087_;
}
v___jp_2088_:
{
size_t v___x_2090_; size_t v___x_2091_; 
v___x_2090_ = ((size_t)1ULL);
v___x_2091_ = lean_usize_add(v_i_2085_, v___x_2090_);
v_i_2085_ = v___x_2091_;
v_b_2087_ = v___y_2089_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_erase_spec__0___boxed(lean_object* v_key_2098_, lean_object* v_as_2099_, lean_object* v_i_2100_, lean_object* v_stop_2101_, lean_object* v_b_2102_){
_start:
{
size_t v_i_boxed_2103_; size_t v_stop_boxed_2104_; lean_object* v_res_2105_; 
v_i_boxed_2103_ = lean_unbox_usize(v_i_2100_);
lean_dec(v_i_2100_);
v_stop_boxed_2104_ = lean_unbox_usize(v_stop_2101_);
lean_dec(v_stop_2101_);
v_res_2105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_erase_spec__0(v_key_2098_, v_as_2099_, v_i_boxed_2103_, v_stop_boxed_2104_, v_b_2102_);
lean_dec_ref(v_as_2099_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase(lean_object* v_query_2106_, lean_object* v_key_2107_){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2108_ = lean_unsigned_to_nat(0u);
v___x_2109_ = lean_array_get_size(v_query_2106_);
v___x_2110_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_2111_ = lean_nat_dec_lt(v___x_2108_, v___x_2109_);
if (v___x_2111_ == 0)
{
lean_dec_ref(v_key_2107_);
return v___x_2110_;
}
else
{
size_t v___x_2112_; size_t v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = ((size_t)0ULL);
v___x_2113_ = lean_usize_of_nat(v___x_2109_);
v___x_2114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_erase_spec__0(v_key_2107_, v_query_2106_, v___x_2112_, v___x_2113_, v___x_2110_);
return v___x_2114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase___boxed(lean_object* v_query_2115_, lean_object* v_key_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Std_Http_URI_Query_erase(v_query_2115_, v_key_2116_);
lean_dec_ref(v_query_2115_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get(lean_object* v_query_2120_, lean_object* v_key_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Std_Http_URI_Query_find_x3f(v_query_2120_, v_key_2121_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v___x_2123_; 
v___x_2123_ = lean_box(0);
return v___x_2123_;
}
else
{
lean_object* v_val_2124_; 
v_val_2124_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_val_2124_);
lean_dec_ref_known(v___x_2122_, 1);
if (lean_obj_tag(v_val_2124_) == 0)
{
lean_object* v___x_2125_; 
v___x_2125_ = ((lean_object*)(l_Std_Http_URI_Query_get___closed__0));
return v___x_2125_;
}
else
{
lean_object* v_val_2126_; lean_object* v___x_2127_; 
v_val_2126_ = lean_ctor_get(v_val_2124_, 0);
lean_inc(v_val_2126_);
lean_dec_ref_known(v_val_2124_, 1);
v___x_2127_ = l_Std_Http_URI_EncodedQueryParam_decode(v_val_2126_);
lean_dec(v_val_2126_);
return v___x_2127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get___boxed(lean_object* v_query_2128_, lean_object* v_key_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Std_Http_URI_Query_get(v_query_2128_, v_key_2129_);
lean_dec_ref(v_query_2128_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD(lean_object* v_query_2131_, lean_object* v_key_2132_, lean_object* v_default_2133_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Std_Http_URI_Query_get(v_query_2131_, v_key_2132_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_inc_ref(v_default_2133_);
return v_default_2133_;
}
else
{
lean_object* v_val_2135_; 
v_val_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_val_2135_);
lean_dec_ref_known(v___x_2134_, 1);
return v_val_2135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD___boxed(lean_object* v_query_2136_, lean_object* v_key_2137_, lean_object* v_default_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Std_Http_URI_Query_getD(v_query_2136_, v_key_2137_, v_default_2138_);
lean_dec_ref(v_default_2138_);
lean_dec_ref(v_query_2136_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set(lean_object* v_query_2140_, lean_object* v_key_2141_, lean_object* v_value_2142_){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
lean_inc_ref(v_key_2141_);
v___x_2143_ = l_Std_Http_URI_Query_erase(v_query_2140_, v_key_2141_);
v___x_2144_ = l_Std_Http_URI_Query_insert(v___x_2143_, v_key_2141_, v_value_2142_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set___boxed(lean_object* v_query_2145_, lean_object* v_key_2146_, lean_object* v_value_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Std_Http_URI_Query_set(v_query_2145_, v_key_2146_, v_value_2147_);
lean_dec_ref(v_query_2145_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(size_t v_sz_2149_, size_t v_i_2150_, lean_object* v_bs_2151_){
_start:
{
uint8_t v___x_2152_; 
v___x_2152_ = lean_usize_dec_lt(v_i_2150_, v_sz_2149_);
if (v___x_2152_ == 0)
{
return v_bs_2151_;
}
else
{
lean_object* v_v_2153_; lean_object* v_fst_2154_; lean_object* v_snd_2155_; lean_object* v___x_2156_; lean_object* v_bs_x27_2157_; lean_object* v___x_2158_; size_t v___x_2159_; size_t v___x_2160_; lean_object* v___x_2161_; 
v_v_2153_ = lean_array_uget_borrowed(v_bs_2151_, v_i_2150_);
v_fst_2154_ = lean_ctor_get(v_v_2153_, 0);
lean_inc(v_fst_2154_);
v_snd_2155_ = lean_ctor_get(v_v_2153_, 1);
lean_inc(v_snd_2155_);
v___x_2156_ = lean_unsigned_to_nat(0u);
v_bs_x27_2157_ = lean_array_uset(v_bs_2151_, v_i_2150_, v___x_2156_);
v___x_2158_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2154_, v_snd_2155_);
v___x_2159_ = ((size_t)1ULL);
v___x_2160_ = lean_usize_add(v_i_2150_, v___x_2159_);
v___x_2161_ = lean_array_uset(v_bs_x27_2157_, v_i_2150_, v___x_2158_);
v_i_2150_ = v___x_2160_;
v_bs_2151_ = v___x_2161_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0___boxed(lean_object* v_sz_2163_, lean_object* v_i_2164_, lean_object* v_bs_2165_){
_start:
{
size_t v_sz_boxed_2166_; size_t v_i_boxed_2167_; lean_object* v_res_2168_; 
v_sz_boxed_2166_ = lean_unbox_usize(v_sz_2163_);
lean_dec(v_sz_2163_);
v_i_boxed_2167_ = lean_unbox_usize(v_i_2164_);
lean_dec(v_i_2164_);
v_res_2168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_boxed_2166_, v_i_boxed_2167_, v_bs_2165_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toRawString(lean_object* v_query_2170_){
_start:
{
size_t v_sz_2171_; size_t v___x_2172_; lean_object* v_params_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v_sz_2171_ = lean_array_size(v_query_2170_);
v___x_2172_ = ((size_t)0ULL);
v_params_2173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_2171_, v___x_2172_, v_query_2170_);
v___x_2174_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2175_ = lean_array_to_list(v_params_2173_);
v___x_2176_ = l_String_intercalate(v___x_2174_, v___x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0(lean_object* v_x_2178_){
_start:
{
lean_object* v_fst_2179_; lean_object* v_snd_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v_fst_2179_ = lean_ctor_get(v_x_2178_, 0);
lean_inc(v_fst_2179_);
v_snd_2180_ = lean_ctor_get(v_x_2178_, 1);
lean_inc(v_snd_2180_);
lean_dec_ref(v_x_2178_);
v___x_2181_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
v___x_2182_ = l_Std_Http_URI_Query_insert(v___x_2181_, v_fst_2179_, v_snd_2180_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0(lean_object* v_x_2185_, lean_object* v_q_2186_){
_start:
{
lean_object* v_fst_2187_; lean_object* v_snd_2188_; lean_object* v___x_2189_; 
v_fst_2187_ = lean_ctor_get(v_x_2185_, 0);
lean_inc(v_fst_2187_);
v_snd_2188_ = lean_ctor_get(v_x_2185_, 1);
lean_inc(v_snd_2188_);
lean_dec_ref(v_x_2185_);
v___x_2189_ = l_Std_Http_URI_Query_insert(v_q_2186_, v_fst_2187_, v_snd_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__0(lean_object* v_x_2192_){
_start:
{
lean_object* v_fst_2193_; lean_object* v_snd_2194_; lean_object* v___x_2195_; 
v_fst_2193_ = lean_ctor_get(v_x_2192_, 0);
lean_inc(v_fst_2193_);
v_snd_2194_ = lean_ctor_get(v_x_2192_, 1);
lean_inc(v_snd_2194_);
lean_dec_ref(v_x_2192_);
v___x_2195_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2193_, v_snd_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__1(lean_object* v___f_2197_, lean_object* v_q_2198_){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2199_ = lean_array_get_size(v_q_2198_);
v___x_2200_ = lean_unsigned_to_nat(0u);
v___x_2201_ = lean_nat_dec_eq(v___x_2199_, v___x_2200_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v_encodedParams_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2202_ = lean_array_to_list(v_q_2198_);
v___x_2203_ = lean_box(0);
v_encodedParams_2204_ = l_List_mapTR_loop___redArg(v___f_2197_, v___x_2202_, v___x_2203_);
v___x_2205_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2206_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2207_ = l_String_intercalate(v___x_2206_, v_encodedParams_2204_);
v___x_2208_ = lean_string_append(v___x_2205_, v___x_2207_);
lean_dec_ref(v___x_2207_);
return v___x_2208_;
}
else
{
lean_object* v___x_2209_; 
lean_dec_ref(v_q_2198_);
lean_dec_ref(v___f_2197_);
v___x_2209_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
if (lean_obj_tag(v_a_2214_) == 0)
{
lean_object* v___x_2216_; 
v___x_2216_ = l_List_reverse___redArg(v_a_2215_);
return v___x_2216_;
}
else
{
lean_object* v_head_2217_; lean_object* v_tail_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2229_; 
v_head_2217_ = lean_ctor_get(v_a_2214_, 0);
v_tail_2218_ = lean_ctor_get(v_a_2214_, 1);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_a_2214_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2220_ = v_a_2214_;
v_isShared_2221_ = v_isSharedCheck_2229_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_tail_2218_);
lean_inc(v_head_2217_);
lean_dec(v_a_2214_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2229_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v_fst_2222_; lean_object* v_snd_2223_; lean_object* v___x_2224_; lean_object* v___x_2226_; 
v_fst_2222_ = lean_ctor_get(v_head_2217_, 0);
lean_inc(v_fst_2222_);
v_snd_2223_ = lean_ctor_get(v_head_2217_, 1);
lean_inc(v_snd_2223_);
lean_dec(v_head_2217_);
v___x_2224_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2222_, v_snd_2223_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 1, v_a_2215_);
lean_ctor_set(v___x_2220_, 0, v___x_2224_);
v___x_2226_ = v___x_2220_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_a_2215_);
v___x_2226_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
v_a_2214_ = v_tail_2218_;
v_a_2215_ = v___x_2226_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatOption(lean_object* v_x_2230_){
_start:
{
if (lean_obj_tag(v_x_2230_) == 0)
{
lean_object* v___x_2231_; 
v___x_2231_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2231_;
}
else
{
lean_object* v_val_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; 
v_val_2232_ = lean_ctor_get(v_x_2230_, 0);
lean_inc(v_val_2232_);
lean_dec_ref_known(v_x_2230_, 1);
v___x_2233_ = lean_array_get_size(v_val_2232_);
v___x_2234_ = lean_unsigned_to_nat(0u);
v___x_2235_ = lean_nat_dec_eq(v___x_2233_, v___x_2234_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v_encodedParams_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2236_ = lean_array_to_list(v_val_2232_);
v___x_2237_ = lean_box(0);
v_encodedParams_2238_ = l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(v___x_2236_, v___x_2237_);
v___x_2239_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2240_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2241_ = l_String_intercalate(v___x_2240_, v_encodedParams_2238_);
v___x_2242_ = lean_string_append(v___x_2239_, v___x_2241_);
lean_dec_ref(v___x_2241_);
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; 
lean_dec(v_val_2232_);
v___x_2243_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
return v___x_2243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(lean_object* v_x_2244_, lean_object* v_x_2245_){
_start:
{
if (lean_obj_tag(v_x_2244_) == 0)
{
lean_object* v___x_2246_; 
v___x_2246_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2246_;
}
else
{
lean_object* v_val_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v_val_2247_ = lean_ctor_get(v_x_2244_, 0);
lean_inc(v_val_2247_);
lean_dec_ref_known(v_x_2244_, 1);
v___x_2248_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2249_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_val_2247_);
v___x_2250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2248_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = l_Repr_addAppParen(v___x_2250_, v_x_2245_);
return v___x_2251_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(lean_object* v_x_2252_, lean_object* v_x_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_x_2252_, v_x_2253_);
lean_dec(v_x_2253_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object* v_x_2255_, lean_object* v_x_2256_){
_start:
{
if (lean_obj_tag(v_x_2255_) == 0)
{
lean_object* v___x_2257_; 
v___x_2257_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2257_;
}
else
{
lean_object* v_val_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v_val_2258_ = lean_ctor_get(v_x_2255_, 0);
lean_inc(v_val_2258_);
lean_dec_ref_known(v_x_2255_, 1);
v___x_2259_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2260_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_val_2258_);
v___x_2261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2259_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = l_Repr_addAppParen(v___x_2261_, v_x_2256_);
return v___x_2262_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1___boxed(lean_object* v_x_2263_, lean_object* v_x_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_x_2263_, v_x_2264_);
lean_dec(v_x_2264_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(lean_object* v_x_2266_, lean_object* v_x_2267_){
_start:
{
if (lean_obj_tag(v_x_2266_) == 0)
{
lean_object* v___x_2268_; 
v___x_2268_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2268_;
}
else
{
lean_object* v_val_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2280_; 
v_val_2269_ = lean_ctor_get(v_x_2266_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_x_2266_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2271_ = v_x_2266_;
v_isShared_2272_ = v_isSharedCheck_2280_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_val_2269_);
lean_dec(v_x_2266_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2280_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2273_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2274_ = l_String_quote(v_val_2269_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set_tag(v___x_2271_, 3);
lean_ctor_set(v___x_2271_, 0, v___x_2274_);
v___x_2276_ = v___x_2271_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2273_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = l_Repr_addAppParen(v___x_2277_, v_x_2267_);
return v___x_2278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2___boxed(lean_object* v_x_2281_, lean_object* v_x_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_x_2281_, v_x_2282_);
lean_dec(v_x_2282_);
return v_res_2283_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_unsigned_to_nat(10u);
v___x_2294_ = lean_nat_to_int(v___x_2293_);
return v___x_2294_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_unsigned_to_nat(13u);
v___x_2299_ = lean_nat_to_int(v___x_2298_);
return v___x_2299_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_unsigned_to_nat(9u);
v___x_2307_ = lean_nat_to_int(v___x_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___redArg(lean_object* v_x_2311_){
_start:
{
lean_object* v_scheme_2312_; lean_object* v_authority_2313_; lean_object* v_path_2314_; lean_object* v_query_2315_; lean_object* v_fragment_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v_scheme_2312_ = lean_ctor_get(v_x_2311_, 0);
lean_inc_ref(v_scheme_2312_);
v_authority_2313_ = lean_ctor_get(v_x_2311_, 1);
lean_inc(v_authority_2313_);
v_path_2314_ = lean_ctor_get(v_x_2311_, 2);
lean_inc_ref(v_path_2314_);
v_query_2315_ = lean_ctor_get(v_x_2311_, 3);
lean_inc(v_query_2315_);
v_fragment_2316_ = lean_ctor_get(v_x_2311_, 4);
lean_inc(v_fragment_2316_);
lean_dec_ref(v_x_2311_);
v___x_2317_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2318_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2319_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2320_ = l_String_quote(v_scheme_2312_);
v___x_2321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
v___x_2322_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2319_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = 0;
v___x_2324_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2324_, 0, v___x_2322_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*1, v___x_2323_);
v___x_2325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2318_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
v___x_2326_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2327_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2325_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = lean_box(1);
v___x_2329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2327_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
v___x_2330_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__6));
v___x_2331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
lean_ctor_set(v___x_2332_, 1, v___x_2317_);
v___x_2333_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_2334_ = lean_unsigned_to_nat(0u);
v___x_2335_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_2313_, v___x_2334_);
v___x_2336_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2333_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*1, v___x_2323_);
v___x_2338_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2332_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
v___x_2339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
lean_ctor_set(v___x_2339_, 1, v___x_2326_);
v___x_2340_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
lean_ctor_set(v___x_2340_, 1, v___x_2328_);
v___x_2341_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_2342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
lean_ctor_set(v___x_2343_, 1, v___x_2317_);
v___x_2344_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2345_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_2314_);
v___x_2346_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2344_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
v___x_2347_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*1, v___x_2323_);
v___x_2348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2343_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
lean_ctor_set(v___x_2349_, 1, v___x_2326_);
v___x_2350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
lean_ctor_set(v___x_2350_, 1, v___x_2328_);
v___x_2351_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_2352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2350_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v___x_2353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
lean_ctor_set(v___x_2353_, 1, v___x_2317_);
v___x_2354_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_2355_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_2315_, v___x_2334_);
v___x_2356_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
v___x_2357_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
lean_ctor_set_uint8(v___x_2357_, sizeof(void*)*1, v___x_2323_);
v___x_2358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2353_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
lean_ctor_set(v___x_2359_, 1, v___x_2326_);
v___x_2360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
lean_ctor_set(v___x_2360_, 1, v___x_2328_);
v___x_2361_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_2362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2360_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
v___x_2363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
lean_ctor_set(v___x_2363_, 1, v___x_2317_);
v___x_2364_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_2365_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_2316_, v___x_2334_);
v___x_2366_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*1, v___x_2323_);
v___x_2368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2363_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___x_2369_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2370_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
lean_ctor_set(v___x_2371_, 1, v___x_2368_);
v___x_2372_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2369_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
lean_ctor_set_uint8(v___x_2375_, sizeof(void*)*1, v___x_2323_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr(lean_object* v_x_2376_, lean_object* v_prec_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Std_Http_instReprURI_repr___redArg(v_x_2376_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___boxed(lean_object* v_x_2379_, lean_object* v_prec_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Std_Http_instReprURI_repr(v_x_2379_, v_prec_2380_);
lean_dec(v_prec_2380_);
return v_res_2381_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object* v_x_2390_, lean_object* v_x_2391_){
_start:
{
if (lean_obj_tag(v_x_2390_) == 0)
{
if (lean_obj_tag(v_x_2391_) == 0)
{
uint8_t v___x_2392_; 
v___x_2392_ = 1;
return v___x_2392_;
}
else
{
uint8_t v___x_2393_; 
v___x_2393_ = 0;
return v___x_2393_;
}
}
else
{
if (lean_obj_tag(v_x_2391_) == 0)
{
uint8_t v___x_2394_; 
v___x_2394_ = 0;
return v___x_2394_;
}
else
{
lean_object* v_val_2395_; lean_object* v_val_2396_; uint8_t v___x_2397_; 
v_val_2395_ = lean_ctor_get(v_x_2390_, 0);
v_val_2396_ = lean_ctor_get(v_x_2391_, 0);
v___x_2397_ = l_Std_Http_URI_instBEqAuthority_beq(v_val_2395_, v_val_2396_);
return v___x_2397_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object* v_x_2398_, lean_object* v_x_2399_){
_start:
{
uint8_t v_res_2400_; lean_object* v_r_2401_; 
v_res_2400_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_x_2398_, v_x_2399_);
lean_dec(v_x_2399_);
lean_dec(v_x_2398_);
v_r_2401_ = lean_box(v_res_2400_);
return v_r_2401_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object* v_x_2402_, lean_object* v_x_2403_){
_start:
{
if (lean_obj_tag(v_x_2402_) == 0)
{
if (lean_obj_tag(v_x_2403_) == 0)
{
uint8_t v___x_2404_; 
v___x_2404_ = 1;
return v___x_2404_;
}
else
{
uint8_t v___x_2405_; 
v___x_2405_ = 0;
return v___x_2405_;
}
}
else
{
if (lean_obj_tag(v_x_2403_) == 0)
{
uint8_t v___x_2406_; 
v___x_2406_ = 0;
return v___x_2406_;
}
else
{
lean_object* v_val_2407_; lean_object* v_val_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v_val_2407_ = lean_ctor_get(v_x_2402_, 0);
v_val_2408_ = lean_ctor_get(v_x_2403_, 0);
v___x_2409_ = lean_array_get_size(v_val_2407_);
v___x_2410_ = lean_array_get_size(v_val_2408_);
v___x_2411_ = lean_nat_dec_eq(v___x_2409_, v___x_2410_);
if (v___x_2411_ == 0)
{
return v___x_2411_;
}
else
{
uint8_t v___x_2412_; 
v___x_2412_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_val_2407_, v_val_2408_, v___x_2409_);
return v___x_2412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object* v_x_2413_, lean_object* v_x_2414_){
_start:
{
uint8_t v_res_2415_; lean_object* v_r_2416_; 
v_res_2415_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_x_2413_, v_x_2414_);
lean_dec(v_x_2414_);
lean_dec(v_x_2413_);
v_r_2416_ = lean_box(v_res_2415_);
return v_r_2416_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object* v_x_2417_, lean_object* v_x_2418_){
_start:
{
lean_object* v_scheme_2419_; lean_object* v_authority_2420_; lean_object* v_path_2421_; lean_object* v_query_2422_; lean_object* v_fragment_2423_; lean_object* v_scheme_2424_; lean_object* v_authority_2425_; lean_object* v_path_2426_; lean_object* v_query_2427_; lean_object* v_fragment_2428_; uint8_t v___x_2429_; 
v_scheme_2419_ = lean_ctor_get(v_x_2417_, 0);
v_authority_2420_ = lean_ctor_get(v_x_2417_, 1);
v_path_2421_ = lean_ctor_get(v_x_2417_, 2);
v_query_2422_ = lean_ctor_get(v_x_2417_, 3);
v_fragment_2423_ = lean_ctor_get(v_x_2417_, 4);
v_scheme_2424_ = lean_ctor_get(v_x_2418_, 0);
v_authority_2425_ = lean_ctor_get(v_x_2418_, 1);
v_path_2426_ = lean_ctor_get(v_x_2418_, 2);
v_query_2427_ = lean_ctor_get(v_x_2418_, 3);
v_fragment_2428_ = lean_ctor_get(v_x_2418_, 4);
v___x_2429_ = lean_string_dec_eq(v_scheme_2419_, v_scheme_2424_);
if (v___x_2429_ == 0)
{
return v___x_2429_;
}
else
{
uint8_t v___x_2430_; 
v___x_2430_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_2420_, v_authority_2425_);
if (v___x_2430_ == 0)
{
return v___x_2430_;
}
else
{
uint8_t v___x_2431_; 
v___x_2431_ = l_Std_Http_URI_instBEqPath_beq(v_path_2421_, v_path_2426_);
if (v___x_2431_ == 0)
{
return v___x_2431_;
}
else
{
uint8_t v___x_2432_; 
v___x_2432_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_2422_, v_query_2427_);
if (v___x_2432_ == 0)
{
return v___x_2432_;
}
else
{
uint8_t v___x_2433_; 
v___x_2433_ = l_instBEqOption_beq___at___00__private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs_spec__0(v_fragment_2423_, v_fragment_2428_);
return v___x_2433_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object* v_x_2434_, lean_object* v_x_2435_){
_start:
{
uint8_t v_res_2436_; lean_object* v_r_2437_; 
v_res_2436_ = l_Std_Http_instBEqURI_beq(v_x_2434_, v_x_2435_);
lean_dec_ref(v_x_2435_);
lean_dec_ref(v_x_2434_);
v_r_2437_ = lean_box(v_res_2436_);
return v_r_2437_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__1(lean_object* v___f_2442_, lean_object* v_uri_2443_){
_start:
{
lean_object* v_scheme_2444_; lean_object* v_authority_2445_; lean_object* v_path_2446_; lean_object* v_query_2447_; lean_object* v_fragment_2448_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2471_; 
v_scheme_2444_ = lean_ctor_get(v_uri_2443_, 0);
lean_inc_ref(v_scheme_2444_);
v_authority_2445_ = lean_ctor_get(v_uri_2443_, 1);
lean_inc(v_authority_2445_);
v_path_2446_ = lean_ctor_get(v_uri_2443_, 2);
lean_inc_ref(v_path_2446_);
v_query_2447_ = lean_ctor_get(v_uri_2443_, 3);
lean_inc(v_query_2447_);
v_fragment_2448_ = lean_ctor_get(v_uri_2443_, 4);
lean_inc(v_fragment_2448_);
lean_dec_ref(v_uri_2443_);
if (lean_obj_tag(v_authority_2445_) == 0)
{
lean_object* v___x_2482_; 
v___x_2482_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2471_ = v___x_2482_;
goto v___jp_2470_;
}
else
{
lean_object* v_val_2483_; lean_object* v_userInfo_2484_; lean_object* v_host_2485_; lean_object* v_port_2486_; lean_object* v___x_2487_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2506_; 
v_val_2483_ = lean_ctor_get(v_authority_2445_, 0);
lean_inc(v_val_2483_);
lean_dec_ref_known(v_authority_2445_, 1);
v_userInfo_2484_ = lean_ctor_get(v_val_2483_, 0);
lean_inc(v_userInfo_2484_);
v_host_2485_ = lean_ctor_get(v_val_2483_, 1);
lean_inc_ref(v_host_2485_);
v_port_2486_ = lean_ctor_get(v_val_2483_, 2);
lean_inc(v_port_2486_);
lean_dec(v_val_2483_);
v___x_2487_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_2484_) == 0)
{
lean_object* v___x_2516_; 
v___x_2516_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2506_ = v___x_2516_;
goto v___jp_2505_;
}
else
{
lean_object* v_val_2517_; lean_object* v_password_2518_; 
v_val_2517_ = lean_ctor_get(v_userInfo_2484_, 0);
lean_inc(v_val_2517_);
lean_dec_ref_known(v_userInfo_2484_, 1);
v_password_2518_ = lean_ctor_get(v_val_2517_, 1);
if (lean_obj_tag(v_password_2518_) == 0)
{
lean_object* v_username_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v_username_2519_ = lean_ctor_get(v_val_2517_, 0);
lean_inc_ref(v_username_2519_);
lean_dec(v_val_2517_);
v___x_2520_ = lean_string_from_utf8_unchecked(v_username_2519_);
v___x_2521_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2522_ = lean_string_append(v___x_2520_, v___x_2521_);
v___y_2506_ = v___x_2522_;
goto v___jp_2505_;
}
else
{
lean_object* v_username_2523_; lean_object* v_val_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
lean_inc_ref(v_password_2518_);
v_username_2523_ = lean_ctor_get(v_val_2517_, 0);
lean_inc_ref(v_username_2523_);
lean_dec(v_val_2517_);
v_val_2524_ = lean_ctor_get(v_password_2518_, 0);
lean_inc(v_val_2524_);
lean_dec_ref_known(v_password_2518_, 1);
v___x_2525_ = lean_string_from_utf8_unchecked(v_username_2523_);
v___x_2526_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2527_ = lean_string_append(v___x_2525_, v___x_2526_);
v___x_2528_ = lean_string_from_utf8_unchecked(v_val_2524_);
v___x_2529_ = lean_string_append(v___x_2527_, v___x_2528_);
lean_dec_ref(v___x_2528_);
v___x_2530_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2531_ = lean_string_append(v___x_2529_, v___x_2530_);
v___y_2506_ = v___x_2531_;
goto v___jp_2505_;
}
}
v___jp_2488_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2492_ = lean_string_append(v___y_2490_, v___y_2489_);
lean_dec_ref(v___y_2489_);
v___x_2493_ = lean_string_append(v___x_2492_, v___y_2491_);
lean_dec_ref(v___y_2491_);
v___x_2494_ = lean_string_append(v___x_2487_, v___x_2493_);
lean_dec_ref(v___x_2493_);
v___y_2471_ = v___x_2494_;
goto v___jp_2470_;
}
v___jp_2495_:
{
switch(lean_obj_tag(v_port_2486_))
{
case 0:
{
lean_object* v___x_2498_; 
v___x_2498_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2489_ = v___y_2497_;
v___y_2490_ = v___y_2496_;
v___y_2491_ = v___x_2498_;
goto v___jp_2488_;
}
case 1:
{
lean_object* v___x_2499_; 
v___x_2499_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_2489_ = v___y_2497_;
v___y_2490_ = v___y_2496_;
v___y_2491_ = v___x_2499_;
goto v___jp_2488_;
}
default: 
{
uint16_t v_port_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v_port_2500_ = lean_ctor_get_uint16(v_port_2486_, 0);
lean_dec_ref_known(v_port_2486_, 0);
v___x_2501_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2502_ = lean_uint16_to_nat(v_port_2500_);
v___x_2503_ = l_Nat_reprFast(v___x_2502_);
v___x_2504_ = lean_string_append(v___x_2501_, v___x_2503_);
lean_dec_ref(v___x_2503_);
v___y_2489_ = v___y_2497_;
v___y_2490_ = v___y_2496_;
v___y_2491_ = v___x_2504_;
goto v___jp_2488_;
}
}
}
v___jp_2505_:
{
switch(lean_obj_tag(v_host_2485_))
{
case 0:
{
lean_object* v_name_2507_; 
v_name_2507_ = lean_ctor_get(v_host_2485_, 0);
lean_inc_ref(v_name_2507_);
lean_dec_ref_known(v_host_2485_, 1);
v___y_2496_ = v___y_2506_;
v___y_2497_ = v_name_2507_;
goto v___jp_2495_;
}
case 1:
{
lean_object* v_ipv4_2508_; lean_object* v___x_2509_; 
v_ipv4_2508_ = lean_ctor_get(v_host_2485_, 0);
lean_inc_ref(v_ipv4_2508_);
lean_dec_ref_known(v_host_2485_, 1);
v___x_2509_ = lean_uv_ntop_v4(v_ipv4_2508_);
lean_dec_ref(v_ipv4_2508_);
v___y_2496_ = v___y_2506_;
v___y_2497_ = v___x_2509_;
goto v___jp_2495_;
}
default: 
{
lean_object* v_ipv6_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v_ipv6_2510_ = lean_ctor_get(v_host_2485_, 0);
lean_inc_ref(v_ipv6_2510_);
lean_dec_ref_known(v_host_2485_, 1);
v___x_2511_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_2512_ = lean_uv_ntop_v6(v_ipv6_2510_);
lean_dec_ref(v_ipv6_2510_);
v___x_2513_ = lean_string_append(v___x_2511_, v___x_2512_);
lean_dec_ref(v___x_2512_);
v___x_2514_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_2515_ = lean_string_append(v___x_2513_, v___x_2514_);
v___y_2496_ = v___y_2506_;
v___y_2497_ = v___x_2515_;
goto v___jp_2495_;
}
}
}
}
v___jp_2449_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2454_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2455_ = lean_string_append(v_scheme_2444_, v___x_2454_);
v___x_2456_ = lean_string_append(v___x_2455_, v___y_2451_);
lean_dec_ref(v___y_2451_);
v___x_2457_ = lean_string_append(v___x_2456_, v___y_2450_);
lean_dec_ref(v___y_2450_);
v___x_2458_ = lean_string_append(v___x_2457_, v___y_2452_);
lean_dec_ref(v___y_2452_);
v___x_2459_ = lean_string_append(v___x_2458_, v___y_2453_);
lean_dec_ref(v___y_2453_);
return v___x_2459_;
}
v___jp_2460_:
{
lean_object* v_queryPart_2463_; 
v_queryPart_2463_ = l_Std_Http_URI_Query_formatOption(v_query_2447_);
if (lean_obj_tag(v_fragment_2448_) == 0)
{
lean_object* v___x_2464_; 
v___x_2464_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2450_ = v___y_2462_;
v___y_2451_ = v___y_2461_;
v___y_2452_ = v_queryPart_2463_;
v___y_2453_ = v___x_2464_;
goto v___jp_2449_;
}
else
{
lean_object* v_val_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v_val_2465_ = lean_ctor_get(v_fragment_2448_, 0);
lean_inc(v_val_2465_);
lean_dec_ref_known(v_fragment_2448_, 1);
v___x_2466_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_2467_ = l_Std_Http_URI_EncodedFragment_encode(v_val_2465_);
v___x_2468_ = lean_string_from_utf8_unchecked(v___x_2467_);
v___x_2469_ = lean_string_append(v___x_2466_, v___x_2468_);
lean_dec_ref(v___x_2468_);
v___y_2450_ = v___y_2462_;
v___y_2451_ = v___y_2461_;
v___y_2452_ = v_queryPart_2463_;
v___y_2453_ = v___x_2469_;
goto v___jp_2449_;
}
}
v___jp_2470_:
{
lean_object* v_segments_2472_; uint8_t v_absolute_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; size_t v_sz_2476_; size_t v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v_result_2480_; 
v_segments_2472_ = lean_ctor_get(v_path_2446_, 0);
lean_inc_ref(v_segments_2472_);
v_absolute_2473_ = lean_ctor_get_uint8(v_path_2446_, sizeof(void*)*1);
lean_dec_ref(v_path_2446_);
v___x_2474_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_2475_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_2476_ = lean_array_size(v_segments_2472_);
v___x_2477_ = ((size_t)0ULL);
v___x_2478_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2475_, v___f_2442_, v_sz_2476_, v___x_2477_, v_segments_2472_);
v___x_2479_ = lean_array_to_list(v___x_2478_);
v_result_2480_ = l_String_intercalate(v___x_2474_, v___x_2479_);
if (v_absolute_2473_ == 0)
{
v___y_2461_ = v___y_2471_;
v___y_2462_ = v_result_2480_;
goto v___jp_2460_;
}
else
{
lean_object* v___x_2481_; 
v___x_2481_ = lean_string_append(v___x_2474_, v_result_2480_);
lean_dec_ref(v_result_2480_);
v___y_2461_ = v___y_2471_;
v___y_2462_ = v___x_2481_;
goto v___jp_2460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x3f(lean_object* v_b_2544_, lean_object* v_scheme_2545_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Std_Http_URI_Scheme_ofString_x3f(v_scheme_2545_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v___x_2547_; 
lean_dec_ref(v_b_2544_);
v___x_2547_ = lean_box(0);
return v___x_2547_;
}
else
{
lean_object* v_userInfo_2548_; lean_object* v_host_2549_; lean_object* v_port_2550_; lean_object* v_pathSegments_2551_; lean_object* v_query_2552_; lean_object* v_fragment_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2568_; 
v_userInfo_2548_ = lean_ctor_get(v_b_2544_, 1);
v_host_2549_ = lean_ctor_get(v_b_2544_, 2);
v_port_2550_ = lean_ctor_get(v_b_2544_, 3);
v_pathSegments_2551_ = lean_ctor_get(v_b_2544_, 4);
v_query_2552_ = lean_ctor_get(v_b_2544_, 5);
v_fragment_2553_ = lean_ctor_get(v_b_2544_, 6);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_b_2544_);
if (v_isSharedCheck_2568_ == 0)
{
lean_object* v_unused_2569_; 
v_unused_2569_ = lean_ctor_get(v_b_2544_, 0);
lean_dec(v_unused_2569_);
v___x_2555_ = v_b_2544_;
v_isShared_2556_ = v_isSharedCheck_2568_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_fragment_2553_);
lean_inc(v_query_2552_);
lean_inc(v_pathSegments_2551_);
lean_inc(v_port_2550_);
lean_inc(v_host_2549_);
lean_inc(v_userInfo_2548_);
lean_dec(v_b_2544_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2568_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
lean_inc_ref(v___x_2546_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v___x_2546_);
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2546_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_userInfo_2548_);
lean_ctor_set(v_reuseFailAlloc_2567_, 2, v_host_2549_);
lean_ctor_set(v_reuseFailAlloc_2567_, 3, v_port_2550_);
lean_ctor_set(v_reuseFailAlloc_2567_, 4, v_pathSegments_2551_);
lean_ctor_set(v_reuseFailAlloc_2567_, 5, v_query_2552_);
lean_ctor_set(v_reuseFailAlloc_2567_, 6, v_fragment_2553_);
v___x_2558_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v___x_2546_, 0);
lean_dec(v_unused_2566_);
v___x_2560_ = v___x_2546_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_dec(v___x_2546_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v___x_2558_);
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(lean_object* v_msg_2570_){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = ((lean_object*)(l_Std_Http_URI_instInhabitedBuilder_default));
v___x_2572_ = lean_panic_fn_borrowed(v___x_2571_, v_msg_2570_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x21(lean_object* v_b_2574_, lean_object* v_scheme_2575_){
_start:
{
lean_object* v___x_2576_; 
lean_inc_ref(v_scheme_2575_);
v___x_2576_ = l_Std_Http_URI_Builder_setScheme_x3f(v_b_2574_, v_scheme_2575_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2577_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2578_ = ((lean_object*)(l_Std_Http_URI_Builder_setScheme_x21___closed__0));
v___x_2579_ = lean_unsigned_to_nat(694u);
v___x_2580_ = lean_unsigned_to_nat(14u);
v___x_2581_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_2582_ = l_String_quote(v_scheme_2575_);
v___x_2583_ = lean_string_append(v___x_2581_, v___x_2582_);
lean_dec_ref(v___x_2582_);
v___x_2584_ = l_mkPanicMessageWithDecl(v___x_2577_, v___x_2578_, v___x_2579_, v___x_2580_, v___x_2583_);
lean_dec_ref(v___x_2583_);
v___x_2585_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2584_);
return v___x_2585_;
}
else
{
lean_object* v_val_2586_; 
lean_dec_ref(v_scheme_2575_);
v_val_2586_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_val_2586_);
lean_dec_ref_known(v___x_2576_, 1);
return v_val_2586_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo(lean_object* v_b_2587_, lean_object* v_username_2588_, lean_object* v_password_2589_){
_start:
{
lean_object* v_scheme_2590_; lean_object* v_host_2591_; lean_object* v_port_2592_; lean_object* v_pathSegments_2593_; lean_object* v_query_2594_; lean_object* v_fragment_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2618_; 
v_scheme_2590_ = lean_ctor_get(v_b_2587_, 0);
v_host_2591_ = lean_ctor_get(v_b_2587_, 2);
v_port_2592_ = lean_ctor_get(v_b_2587_, 3);
v_pathSegments_2593_ = lean_ctor_get(v_b_2587_, 4);
v_query_2594_ = lean_ctor_get(v_b_2587_, 5);
v_fragment_2595_ = lean_ctor_get(v_b_2587_, 6);
v_isSharedCheck_2618_ = !lean_is_exclusive(v_b_2587_);
if (v_isSharedCheck_2618_ == 0)
{
lean_object* v_unused_2619_; 
v_unused_2619_ = lean_ctor_get(v_b_2587_, 1);
lean_dec(v_unused_2619_);
v___x_2597_ = v_b_2587_;
v_isShared_2598_ = v_isSharedCheck_2618_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_fragment_2595_);
lean_inc(v_query_2594_);
lean_inc(v_pathSegments_2593_);
lean_inc(v_port_2592_);
lean_inc(v_host_2591_);
lean_inc(v_scheme_2590_);
lean_dec(v_b_2587_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2618_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___y_2600_; lean_object* v___x_2605_; 
v___x_2605_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_2588_);
if (lean_obj_tag(v_password_2589_) == 0)
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = lean_box(0);
v___x_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___y_2600_ = v___x_2607_;
goto v___jp_2599_;
}
else
{
lean_object* v_val_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2617_; 
v_val_2608_ = lean_ctor_get(v_password_2589_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_password_2589_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2610_ = v_password_2589_;
v_isShared_2611_ = v_isSharedCheck_2617_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_val_2608_);
lean_dec(v_password_2589_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2617_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2612_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_2608_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2612_);
v___x_2614_ = v___x_2610_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2615_; 
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2605_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___y_2600_ = v___x_2615_;
goto v___jp_2599_;
}
}
}
v___jp_2599_:
{
lean_object* v___x_2601_; lean_object* v___x_2603_; 
v___x_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___y_2600_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 1, v___x_2601_);
v___x_2603_ = v___x_2597_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_scheme_2590_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2601_);
lean_ctor_set(v_reuseFailAlloc_2604_, 2, v_host_2591_);
lean_ctor_set(v_reuseFailAlloc_2604_, 3, v_port_2592_);
lean_ctor_set(v_reuseFailAlloc_2604_, 4, v_pathSegments_2593_);
lean_ctor_set(v_reuseFailAlloc_2604_, 5, v_query_2594_);
lean_ctor_set(v_reuseFailAlloc_2604_, 6, v_fragment_2595_);
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
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x3f(lean_object* v_b_2620_, lean_object* v_name_2621_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l_Std_Http_URI_DomainName_ofString_x3f(v_name_2621_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v___x_2623_; 
lean_dec_ref(v_b_2620_);
v___x_2623_ = lean_box(0);
return v___x_2623_;
}
else
{
lean_object* v_val_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2647_; 
v_val_2624_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2626_ = v___x_2622_;
v_isShared_2627_ = v_isSharedCheck_2647_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_val_2624_);
lean_dec(v___x_2622_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2647_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v_scheme_2628_; lean_object* v_userInfo_2629_; lean_object* v_port_2630_; lean_object* v_pathSegments_2631_; lean_object* v_query_2632_; lean_object* v_fragment_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2645_; 
v_scheme_2628_ = lean_ctor_get(v_b_2620_, 0);
v_userInfo_2629_ = lean_ctor_get(v_b_2620_, 1);
v_port_2630_ = lean_ctor_get(v_b_2620_, 3);
v_pathSegments_2631_ = lean_ctor_get(v_b_2620_, 4);
v_query_2632_ = lean_ctor_get(v_b_2620_, 5);
v_fragment_2633_ = lean_ctor_get(v_b_2620_, 6);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_b_2620_);
if (v_isSharedCheck_2645_ == 0)
{
lean_object* v_unused_2646_; 
v_unused_2646_ = lean_ctor_get(v_b_2620_, 2);
lean_dec(v_unused_2646_);
v___x_2635_ = v_b_2620_;
v_isShared_2636_ = v_isSharedCheck_2645_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_fragment_2633_);
lean_inc(v_query_2632_);
lean_inc(v_pathSegments_2631_);
lean_inc(v_port_2630_);
lean_inc(v_userInfo_2629_);
lean_inc(v_scheme_2628_);
lean_dec(v_b_2620_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2645_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v_val_2624_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v___x_2637_);
v___x_2639_ = v___x_2626_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2637_);
v___x_2639_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2641_; 
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 2, v___x_2639_);
v___x_2641_ = v___x_2635_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_scheme_2628_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_userInfo_2629_);
lean_ctor_set(v_reuseFailAlloc_2643_, 2, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2643_, 3, v_port_2630_);
lean_ctor_set(v_reuseFailAlloc_2643_, 4, v_pathSegments_2631_);
lean_ctor_set(v_reuseFailAlloc_2643_, 5, v_query_2632_);
lean_ctor_set(v_reuseFailAlloc_2643_, 6, v_fragment_2633_);
v___x_2641_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2642_; 
v___x_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
return v___x_2642_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x21(lean_object* v_b_2650_, lean_object* v_name_2651_){
_start:
{
lean_object* v___x_2652_; 
lean_inc_ref(v_name_2651_);
v___x_2652_ = l_Std_Http_URI_Builder_setHost_x3f(v_b_2650_, v_name_2651_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2653_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2654_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__0));
v___x_2655_ = lean_unsigned_to_nat(723u);
v___x_2656_ = lean_unsigned_to_nat(14u);
v___x_2657_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__1));
v___x_2658_ = l_String_quote(v_name_2651_);
v___x_2659_ = lean_string_append(v___x_2657_, v___x_2658_);
lean_dec_ref(v___x_2658_);
v___x_2660_ = l_mkPanicMessageWithDecl(v___x_2653_, v___x_2654_, v___x_2655_, v___x_2656_, v___x_2659_);
lean_dec_ref(v___x_2659_);
v___x_2661_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2660_);
return v___x_2661_;
}
else
{
lean_object* v_val_2662_; 
lean_dec_ref(v_name_2651_);
v_val_2662_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_val_2662_);
lean_dec_ref_known(v___x_2652_, 1);
return v_val_2662_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv4(lean_object* v_b_2663_, lean_object* v_addr_2664_){
_start:
{
lean_object* v_scheme_2665_; lean_object* v_userInfo_2666_; lean_object* v_port_2667_; lean_object* v_pathSegments_2668_; lean_object* v_query_2669_; lean_object* v_fragment_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2679_; 
v_scheme_2665_ = lean_ctor_get(v_b_2663_, 0);
v_userInfo_2666_ = lean_ctor_get(v_b_2663_, 1);
v_port_2667_ = lean_ctor_get(v_b_2663_, 3);
v_pathSegments_2668_ = lean_ctor_get(v_b_2663_, 4);
v_query_2669_ = lean_ctor_get(v_b_2663_, 5);
v_fragment_2670_ = lean_ctor_get(v_b_2663_, 6);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_b_2663_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; 
v_unused_2680_ = lean_ctor_get(v_b_2663_, 2);
lean_dec(v_unused_2680_);
v___x_2672_ = v_b_2663_;
v_isShared_2673_ = v_isSharedCheck_2679_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_fragment_2670_);
lean_inc(v_query_2669_);
lean_inc(v_pathSegments_2668_);
lean_inc(v_port_2667_);
lean_inc(v_userInfo_2666_);
lean_inc(v_scheme_2665_);
lean_dec(v_b_2663_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2679_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2677_; 
v___x_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2674_, 0, v_addr_2664_);
v___x_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 2, v___x_2675_);
v___x_2677_ = v___x_2672_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_scheme_2665_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_userInfo_2666_);
lean_ctor_set(v_reuseFailAlloc_2678_, 2, v___x_2675_);
lean_ctor_set(v_reuseFailAlloc_2678_, 3, v_port_2667_);
lean_ctor_set(v_reuseFailAlloc_2678_, 4, v_pathSegments_2668_);
lean_ctor_set(v_reuseFailAlloc_2678_, 5, v_query_2669_);
lean_ctor_set(v_reuseFailAlloc_2678_, 6, v_fragment_2670_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv6(lean_object* v_b_2681_, lean_object* v_addr_2682_){
_start:
{
lean_object* v_scheme_2683_; lean_object* v_userInfo_2684_; lean_object* v_port_2685_; lean_object* v_pathSegments_2686_; lean_object* v_query_2687_; lean_object* v_fragment_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2697_; 
v_scheme_2683_ = lean_ctor_get(v_b_2681_, 0);
v_userInfo_2684_ = lean_ctor_get(v_b_2681_, 1);
v_port_2685_ = lean_ctor_get(v_b_2681_, 3);
v_pathSegments_2686_ = lean_ctor_get(v_b_2681_, 4);
v_query_2687_ = lean_ctor_get(v_b_2681_, 5);
v_fragment_2688_ = lean_ctor_get(v_b_2681_, 6);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_b_2681_);
if (v_isSharedCheck_2697_ == 0)
{
lean_object* v_unused_2698_; 
v_unused_2698_ = lean_ctor_get(v_b_2681_, 2);
lean_dec(v_unused_2698_);
v___x_2690_ = v_b_2681_;
v_isShared_2691_ = v_isSharedCheck_2697_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_fragment_2688_);
lean_inc(v_query_2687_);
lean_inc(v_pathSegments_2686_);
lean_inc(v_port_2685_);
lean_inc(v_userInfo_2684_);
lean_inc(v_scheme_2683_);
lean_dec(v_b_2681_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2697_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2695_; 
v___x_2692_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2692_, 0, v_addr_2682_);
v___x_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 2, v___x_2693_);
v___x_2695_ = v___x_2690_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_scheme_2683_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_userInfo_2684_);
lean_ctor_set(v_reuseFailAlloc_2696_, 2, v___x_2693_);
lean_ctor_set(v_reuseFailAlloc_2696_, 3, v_port_2685_);
lean_ctor_set(v_reuseFailAlloc_2696_, 4, v_pathSegments_2686_);
lean_ctor_set(v_reuseFailAlloc_2696_, 5, v_query_2687_);
lean_ctor_set(v_reuseFailAlloc_2696_, 6, v_fragment_2688_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort(lean_object* v_b_2699_, uint16_t v_port_2700_){
_start:
{
lean_object* v_scheme_2701_; lean_object* v_userInfo_2702_; lean_object* v_host_2703_; lean_object* v_pathSegments_2704_; lean_object* v_query_2705_; lean_object* v_fragment_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2714_; 
v_scheme_2701_ = lean_ctor_get(v_b_2699_, 0);
v_userInfo_2702_ = lean_ctor_get(v_b_2699_, 1);
v_host_2703_ = lean_ctor_get(v_b_2699_, 2);
v_pathSegments_2704_ = lean_ctor_get(v_b_2699_, 4);
v_query_2705_ = lean_ctor_get(v_b_2699_, 5);
v_fragment_2706_ = lean_ctor_get(v_b_2699_, 6);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_b_2699_);
if (v_isSharedCheck_2714_ == 0)
{
lean_object* v_unused_2715_; 
v_unused_2715_ = lean_ctor_get(v_b_2699_, 3);
lean_dec(v_unused_2715_);
v___x_2708_ = v_b_2699_;
v_isShared_2709_ = v_isSharedCheck_2714_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_fragment_2706_);
lean_inc(v_query_2705_);
lean_inc(v_pathSegments_2704_);
lean_inc(v_host_2703_);
lean_inc(v_userInfo_2702_);
lean_inc(v_scheme_2701_);
lean_dec(v_b_2699_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2714_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2710_; lean_object* v___x_2712_; 
v___x_2710_ = lean_alloc_ctor(2, 0, 2);
lean_ctor_set_uint16(v___x_2710_, 0, v_port_2700_);
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 3, v___x_2710_);
v___x_2712_ = v___x_2708_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_scheme_2701_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v_userInfo_2702_);
lean_ctor_set(v_reuseFailAlloc_2713_, 2, v_host_2703_);
lean_ctor_set(v_reuseFailAlloc_2713_, 3, v___x_2710_);
lean_ctor_set(v_reuseFailAlloc_2713_, 4, v_pathSegments_2704_);
lean_ctor_set(v_reuseFailAlloc_2713_, 5, v_query_2705_);
lean_ctor_set(v_reuseFailAlloc_2713_, 6, v_fragment_2706_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort___boxed(lean_object* v_b_2716_, lean_object* v_port_2717_){
_start:
{
uint16_t v_port_boxed_2718_; lean_object* v_res_2719_; 
v_port_boxed_2718_ = lean_unbox(v_port_2717_);
v_res_2719_ = l_Std_Http_URI_Builder_setPort(v_b_2716_, v_port_boxed_2718_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPath(lean_object* v_b_2720_, lean_object* v_segments_2721_){
_start:
{
lean_object* v_scheme_2722_; lean_object* v_userInfo_2723_; lean_object* v_host_2724_; lean_object* v_port_2725_; lean_object* v_query_2726_; lean_object* v_fragment_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
v_scheme_2722_ = lean_ctor_get(v_b_2720_, 0);
v_userInfo_2723_ = lean_ctor_get(v_b_2720_, 1);
v_host_2724_ = lean_ctor_get(v_b_2720_, 2);
v_port_2725_ = lean_ctor_get(v_b_2720_, 3);
v_query_2726_ = lean_ctor_get(v_b_2720_, 5);
v_fragment_2727_ = lean_ctor_get(v_b_2720_, 6);
v_isSharedCheck_2734_ = !lean_is_exclusive(v_b_2720_);
if (v_isSharedCheck_2734_ == 0)
{
lean_object* v_unused_2735_; 
v_unused_2735_ = lean_ctor_get(v_b_2720_, 4);
lean_dec(v_unused_2735_);
v___x_2729_ = v_b_2720_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_fragment_2727_);
lean_inc(v_query_2726_);
lean_inc(v_port_2725_);
lean_inc(v_host_2724_);
lean_inc(v_userInfo_2723_);
lean_inc(v_scheme_2722_);
lean_dec(v_b_2720_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 4, v_segments_2721_);
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_scheme_2722_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_userInfo_2723_);
lean_ctor_set(v_reuseFailAlloc_2733_, 2, v_host_2724_);
lean_ctor_set(v_reuseFailAlloc_2733_, 3, v_port_2725_);
lean_ctor_set(v_reuseFailAlloc_2733_, 4, v_segments_2721_);
lean_ctor_set(v_reuseFailAlloc_2733_, 5, v_query_2726_);
lean_ctor_set(v_reuseFailAlloc_2733_, 6, v_fragment_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_appendPathSegment(lean_object* v_b_2736_, lean_object* v_segment_2737_){
_start:
{
lean_object* v_scheme_2738_; lean_object* v_userInfo_2739_; lean_object* v_host_2740_; lean_object* v_port_2741_; lean_object* v_pathSegments_2742_; lean_object* v_query_2743_; lean_object* v_fragment_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2752_; 
v_scheme_2738_ = lean_ctor_get(v_b_2736_, 0);
v_userInfo_2739_ = lean_ctor_get(v_b_2736_, 1);
v_host_2740_ = lean_ctor_get(v_b_2736_, 2);
v_port_2741_ = lean_ctor_get(v_b_2736_, 3);
v_pathSegments_2742_ = lean_ctor_get(v_b_2736_, 4);
v_query_2743_ = lean_ctor_get(v_b_2736_, 5);
v_fragment_2744_ = lean_ctor_get(v_b_2736_, 6);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_b_2736_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2746_ = v_b_2736_;
v_isShared_2747_ = v_isSharedCheck_2752_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_fragment_2744_);
lean_inc(v_query_2743_);
lean_inc(v_pathSegments_2742_);
lean_inc(v_port_2741_);
lean_inc(v_host_2740_);
lean_inc(v_userInfo_2739_);
lean_inc(v_scheme_2738_);
lean_dec(v_b_2736_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2752_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2748_; lean_object* v___x_2750_; 
v___x_2748_ = lean_array_push(v_pathSegments_2742_, v_segment_2737_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 4, v___x_2748_);
v___x_2750_ = v___x_2746_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_scheme_2738_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_userInfo_2739_);
lean_ctor_set(v_reuseFailAlloc_2751_, 2, v_host_2740_);
lean_ctor_set(v_reuseFailAlloc_2751_, 3, v_port_2741_);
lean_ctor_set(v_reuseFailAlloc_2751_, 4, v___x_2748_);
lean_ctor_set(v_reuseFailAlloc_2751_, 5, v_query_2743_);
lean_ctor_set(v_reuseFailAlloc_2751_, 6, v_fragment_2744_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryParam(lean_object* v_b_2753_, lean_object* v_key_2754_, lean_object* v_value_2755_){
_start:
{
lean_object* v_scheme_2756_; lean_object* v_userInfo_2757_; lean_object* v_host_2758_; lean_object* v_port_2759_; lean_object* v_pathSegments_2760_; lean_object* v_query_2761_; lean_object* v_fragment_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2772_; 
v_scheme_2756_ = lean_ctor_get(v_b_2753_, 0);
v_userInfo_2757_ = lean_ctor_get(v_b_2753_, 1);
v_host_2758_ = lean_ctor_get(v_b_2753_, 2);
v_port_2759_ = lean_ctor_get(v_b_2753_, 3);
v_pathSegments_2760_ = lean_ctor_get(v_b_2753_, 4);
v_query_2761_ = lean_ctor_get(v_b_2753_, 5);
v_fragment_2762_ = lean_ctor_get(v_b_2753_, 6);
v_isSharedCheck_2772_ = !lean_is_exclusive(v_b_2753_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2764_ = v_b_2753_;
v_isShared_2765_ = v_isSharedCheck_2772_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_fragment_2762_);
lean_inc(v_query_2761_);
lean_inc(v_pathSegments_2760_);
lean_inc(v_port_2759_);
lean_inc(v_host_2758_);
lean_inc(v_userInfo_2757_);
lean_inc(v_scheme_2756_);
lean_dec(v_b_2753_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2772_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2770_; 
v___x_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2766_, 0, v_value_2755_);
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_key_2754_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = lean_array_push(v_query_2761_, v___x_2767_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 5, v___x_2768_);
v___x_2770_ = v___x_2764_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_scheme_2756_);
lean_ctor_set(v_reuseFailAlloc_2771_, 1, v_userInfo_2757_);
lean_ctor_set(v_reuseFailAlloc_2771_, 2, v_host_2758_);
lean_ctor_set(v_reuseFailAlloc_2771_, 3, v_port_2759_);
lean_ctor_set(v_reuseFailAlloc_2771_, 4, v_pathSegments_2760_);
lean_ctor_set(v_reuseFailAlloc_2771_, 5, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2771_, 6, v_fragment_2762_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryFlag(lean_object* v_b_2773_, lean_object* v_key_2774_){
_start:
{
lean_object* v_scheme_2775_; lean_object* v_userInfo_2776_; lean_object* v_host_2777_; lean_object* v_port_2778_; lean_object* v_pathSegments_2779_; lean_object* v_query_2780_; lean_object* v_fragment_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2791_; 
v_scheme_2775_ = lean_ctor_get(v_b_2773_, 0);
v_userInfo_2776_ = lean_ctor_get(v_b_2773_, 1);
v_host_2777_ = lean_ctor_get(v_b_2773_, 2);
v_port_2778_ = lean_ctor_get(v_b_2773_, 3);
v_pathSegments_2779_ = lean_ctor_get(v_b_2773_, 4);
v_query_2780_ = lean_ctor_get(v_b_2773_, 5);
v_fragment_2781_ = lean_ctor_get(v_b_2773_, 6);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_b_2773_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2783_ = v_b_2773_;
v_isShared_2784_ = v_isSharedCheck_2791_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_fragment_2781_);
lean_inc(v_query_2780_);
lean_inc(v_pathSegments_2779_);
lean_inc(v_port_2778_);
lean_inc(v_host_2777_);
lean_inc(v_userInfo_2776_);
lean_inc(v_scheme_2775_);
lean_dec(v_b_2773_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2791_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2785_ = lean_box(0);
v___x_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2786_, 0, v_key_2774_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
v___x_2787_ = lean_array_push(v_query_2780_, v___x_2786_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 5, v___x_2787_);
v___x_2789_ = v___x_2783_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_scheme_2775_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_userInfo_2776_);
lean_ctor_set(v_reuseFailAlloc_2790_, 2, v_host_2777_);
lean_ctor_set(v_reuseFailAlloc_2790_, 3, v_port_2778_);
lean_ctor_set(v_reuseFailAlloc_2790_, 4, v_pathSegments_2779_);
lean_ctor_set(v_reuseFailAlloc_2790_, 5, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2790_, 6, v_fragment_2781_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setQuery(lean_object* v_b_2792_, lean_object* v_query_2793_){
_start:
{
lean_object* v_scheme_2794_; lean_object* v_userInfo_2795_; lean_object* v_host_2796_; lean_object* v_port_2797_; lean_object* v_pathSegments_2798_; lean_object* v_fragment_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
v_scheme_2794_ = lean_ctor_get(v_b_2792_, 0);
v_userInfo_2795_ = lean_ctor_get(v_b_2792_, 1);
v_host_2796_ = lean_ctor_get(v_b_2792_, 2);
v_port_2797_ = lean_ctor_get(v_b_2792_, 3);
v_pathSegments_2798_ = lean_ctor_get(v_b_2792_, 4);
v_fragment_2799_ = lean_ctor_get(v_b_2792_, 6);
v_isSharedCheck_2806_ = !lean_is_exclusive(v_b_2792_);
if (v_isSharedCheck_2806_ == 0)
{
lean_object* v_unused_2807_; 
v_unused_2807_ = lean_ctor_get(v_b_2792_, 5);
lean_dec(v_unused_2807_);
v___x_2801_ = v_b_2792_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_fragment_2799_);
lean_inc(v_pathSegments_2798_);
lean_inc(v_port_2797_);
lean_inc(v_host_2796_);
lean_inc(v_userInfo_2795_);
lean_inc(v_scheme_2794_);
lean_dec(v_b_2792_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 5, v_query_2793_);
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_scheme_2794_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_userInfo_2795_);
lean_ctor_set(v_reuseFailAlloc_2805_, 2, v_host_2796_);
lean_ctor_set(v_reuseFailAlloc_2805_, 3, v_port_2797_);
lean_ctor_set(v_reuseFailAlloc_2805_, 4, v_pathSegments_2798_);
lean_ctor_set(v_reuseFailAlloc_2805_, 5, v_query_2793_);
lean_ctor_set(v_reuseFailAlloc_2805_, 6, v_fragment_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setFragment(lean_object* v_b_2808_, lean_object* v_fragment_2809_){
_start:
{
lean_object* v_scheme_2810_; lean_object* v_userInfo_2811_; lean_object* v_host_2812_; lean_object* v_port_2813_; lean_object* v_pathSegments_2814_; lean_object* v_query_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2823_; 
v_scheme_2810_ = lean_ctor_get(v_b_2808_, 0);
v_userInfo_2811_ = lean_ctor_get(v_b_2808_, 1);
v_host_2812_ = lean_ctor_get(v_b_2808_, 2);
v_port_2813_ = lean_ctor_get(v_b_2808_, 3);
v_pathSegments_2814_ = lean_ctor_get(v_b_2808_, 4);
v_query_2815_ = lean_ctor_get(v_b_2808_, 5);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_b_2808_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v_b_2808_, 6);
lean_dec(v_unused_2824_);
v___x_2817_ = v_b_2808_;
v_isShared_2818_ = v_isSharedCheck_2823_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_query_2815_);
lean_inc(v_pathSegments_2814_);
lean_inc(v_port_2813_);
lean_inc(v_host_2812_);
lean_inc(v_userInfo_2811_);
lean_inc(v_scheme_2810_);
lean_dec(v_b_2808_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2823_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2819_, 0, v_fragment_2809_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 6, v___x_2819_);
v___x_2821_ = v___x_2817_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_scheme_2810_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_userInfo_2811_);
lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_host_2812_);
lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_port_2813_);
lean_ctor_set(v_reuseFailAlloc_2822_, 4, v_pathSegments_2814_);
lean_ctor_set(v_reuseFailAlloc_2822_, 5, v_query_2815_);
lean_ctor_set(v_reuseFailAlloc_2822_, 6, v___x_2819_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(size_t v_sz_2825_, size_t v_i_2826_, lean_object* v_bs_2827_){
_start:
{
uint8_t v___x_2828_; 
v___x_2828_ = lean_usize_dec_lt(v_i_2826_, v_sz_2825_);
if (v___x_2828_ == 0)
{
return v_bs_2827_;
}
else
{
lean_object* v_v_2829_; lean_object* v___x_2830_; lean_object* v_bs_x27_2831_; lean_object* v___x_2832_; size_t v___x_2833_; size_t v___x_2834_; lean_object* v___x_2835_; 
v_v_2829_ = lean_array_uget(v_bs_2827_, v_i_2826_);
v___x_2830_ = lean_unsigned_to_nat(0u);
v_bs_x27_2831_ = lean_array_uset(v_bs_2827_, v_i_2826_, v___x_2830_);
v___x_2832_ = l_Std_Http_URI_EncodedSegment_encode(v_v_2829_);
v___x_2833_ = ((size_t)1ULL);
v___x_2834_ = lean_usize_add(v_i_2826_, v___x_2833_);
v___x_2835_ = lean_array_uset(v_bs_x27_2831_, v_i_2826_, v___x_2832_);
v_i_2826_ = v___x_2834_;
v_bs_2827_ = v___x_2835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0___boxed(lean_object* v_sz_2837_, lean_object* v_i_2838_, lean_object* v_bs_2839_){
_start:
{
size_t v_sz_boxed_2840_; size_t v_i_boxed_2841_; lean_object* v_res_2842_; 
v_sz_boxed_2840_ = lean_unbox_usize(v_sz_2837_);
lean_dec(v_sz_2837_);
v_i_boxed_2841_ = lean_unbox_usize(v_i_2838_);
lean_dec(v_i_2838_);
v_res_2842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_boxed_2840_, v_i_boxed_2841_, v_bs_2839_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(size_t v_sz_2843_, size_t v_i_2844_, lean_object* v_bs_2845_){
_start:
{
uint8_t v___x_2846_; 
v___x_2846_ = lean_usize_dec_lt(v_i_2844_, v_sz_2843_);
if (v___x_2846_ == 0)
{
return v_bs_2845_;
}
else
{
lean_object* v_v_2847_; lean_object* v_fst_2848_; lean_object* v_snd_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2878_; 
v_v_2847_ = lean_array_uget(v_bs_2845_, v_i_2844_);
v_fst_2848_ = lean_ctor_get(v_v_2847_, 0);
v_snd_2849_ = lean_ctor_get(v_v_2847_, 1);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_v_2847_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2851_ = v_v_2847_;
v_isShared_2852_ = v_isSharedCheck_2878_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_snd_2849_);
lean_inc(v_fst_2848_);
lean_dec(v_v_2847_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2878_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; lean_object* v_bs_x27_2854_; lean_object* v___y_2856_; lean_object* v___x_2861_; 
v___x_2853_ = lean_unsigned_to_nat(0u);
v_bs_x27_2854_ = lean_array_uset(v_bs_2845_, v_i_2844_, v___x_2853_);
v___x_2861_ = l_Std_Http_URI_EncodedQueryParam_encode(v_fst_2848_);
if (lean_obj_tag(v_snd_2849_) == 0)
{
lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___x_2862_ = lean_box(0);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v___x_2862_);
lean_ctor_set(v___x_2851_, 0, v___x_2861_);
v___x_2864_ = v___x_2851_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
v___y_2856_ = v___x_2864_;
goto v___jp_2855_;
}
}
else
{
lean_object* v_val_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2877_; 
v_val_2866_ = lean_ctor_get(v_snd_2849_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v_snd_2849_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2868_ = v_snd_2849_;
v_isShared_2869_ = v_isSharedCheck_2877_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_val_2866_);
lean_dec(v_snd_2849_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2877_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v___x_2872_; 
v___x_2870_ = l_Std_Http_URI_EncodedQueryParam_encode(v_val_2866_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v___x_2870_);
v___x_2872_ = v___x_2868_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2870_);
v___x_2872_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2874_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v___x_2872_);
lean_ctor_set(v___x_2851_, 0, v___x_2861_);
v___x_2874_ = v___x_2851_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
v___y_2856_ = v___x_2874_;
goto v___jp_2855_;
}
}
}
}
v___jp_2855_:
{
size_t v___x_2857_; size_t v___x_2858_; lean_object* v___x_2859_; 
v___x_2857_ = ((size_t)1ULL);
v___x_2858_ = lean_usize_add(v_i_2844_, v___x_2857_);
v___x_2859_ = lean_array_uset(v_bs_x27_2854_, v_i_2844_, v___y_2856_);
v_i_2844_ = v___x_2858_;
v_bs_2845_ = v___x_2859_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1___boxed(lean_object* v_sz_2879_, lean_object* v_i_2880_, lean_object* v_bs_2881_){
_start:
{
size_t v_sz_boxed_2882_; size_t v_i_boxed_2883_; lean_object* v_res_2884_; 
v_sz_boxed_2882_ = lean_unbox_usize(v_sz_2879_);
lean_dec(v_sz_2879_);
v_i_boxed_2883_ = lean_unbox_usize(v_i_2880_);
lean_dec(v_i_2880_);
v_res_2884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_boxed_2882_, v_i_boxed_2883_, v_bs_2881_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_build(lean_object* v_b_2885_){
_start:
{
lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; uint8_t v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v_scheme_2908_; lean_object* v_userInfo_2909_; lean_object* v_host_2910_; lean_object* v_port_2911_; lean_object* v_pathSegments_2912_; lean_object* v_query_2913_; lean_object* v_fragment_2914_; lean_object* v___y_2916_; 
v_scheme_2908_ = lean_ctor_get(v_b_2885_, 0);
lean_inc(v_scheme_2908_);
v_userInfo_2909_ = lean_ctor_get(v_b_2885_, 1);
lean_inc(v_userInfo_2909_);
v_host_2910_ = lean_ctor_get(v_b_2885_, 2);
lean_inc(v_host_2910_);
v_port_2911_ = lean_ctor_get(v_b_2885_, 3);
lean_inc(v_port_2911_);
v_pathSegments_2912_ = lean_ctor_get(v_b_2885_, 4);
lean_inc_ref(v_pathSegments_2912_);
v_query_2913_ = lean_ctor_get(v_b_2885_, 5);
lean_inc_ref(v_query_2913_);
v_fragment_2914_ = lean_ctor_get(v_b_2885_, 6);
lean_inc(v_fragment_2914_);
lean_dec_ref(v_b_2885_);
if (lean_obj_tag(v_scheme_2908_) == 0)
{
lean_object* v___x_2929_; 
v___x_2929_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___y_2916_ = v___x_2929_;
goto v___jp_2915_;
}
else
{
lean_object* v_val_2930_; 
v_val_2930_ = lean_ctor_get(v_scheme_2908_, 0);
lean_inc(v_val_2930_);
lean_dec_ref_known(v_scheme_2908_, 1);
v___y_2916_ = v_val_2930_;
goto v___jp_2915_;
}
v___jp_2886_:
{
size_t v_sz_2893_; size_t v___x_2894_; lean_object* v___x_2895_; lean_object* v_path_2896_; size_t v_sz_2897_; lean_object* v_query_2898_; lean_object* v___x_2899_; lean_object* v_query_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; 
v_sz_2893_ = lean_array_size(v___y_2887_);
v___x_2894_ = ((size_t)0ULL);
v___x_2895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_2893_, v___x_2894_, v___y_2887_);
v_path_2896_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_path_2896_, 0, v___x_2895_);
lean_ctor_set_uint8(v_path_2896_, sizeof(void*)*1, v___y_2890_);
v_sz_2897_ = lean_array_size(v___y_2888_);
v_query_2898_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_2897_, v___x_2894_, v___y_2888_);
v___x_2899_ = lean_array_to_list(v_query_2898_);
v_query_2900_ = lean_array_mk(v___x_2899_);
v___x_2901_ = lean_array_get_size(v_query_2900_);
v___x_2902_ = lean_unsigned_to_nat(0u);
v___x_2903_ = lean_nat_dec_eq(v___x_2901_, v___x_2902_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2904_, 0, v_query_2900_);
v___x_2905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2905_, 0, v___y_2889_);
lean_ctor_set(v___x_2905_, 1, v___y_2892_);
lean_ctor_set(v___x_2905_, 2, v_path_2896_);
lean_ctor_set(v___x_2905_, 3, v___x_2904_);
lean_ctor_set(v___x_2905_, 4, v___y_2891_);
return v___x_2905_;
}
else
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_dec_ref(v_query_2900_);
v___x_2906_ = lean_box(0);
v___x_2907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2907_, 0, v___y_2889_);
lean_ctor_set(v___x_2907_, 1, v___y_2892_);
lean_ctor_set(v___x_2907_, 2, v_path_2896_);
lean_ctor_set(v___x_2907_, 3, v___x_2906_);
lean_ctor_set(v___x_2907_, 4, v___y_2891_);
return v___x_2907_;
}
}
v___jp_2915_:
{
if (lean_obj_tag(v_host_2910_) == 0)
{
uint8_t v___x_2917_; lean_object* v___x_2918_; 
lean_dec(v_port_2911_);
lean_dec(v_userInfo_2909_);
v___x_2917_ = 1;
v___x_2918_ = lean_box(0);
v___y_2887_ = v_pathSegments_2912_;
v___y_2888_ = v_query_2913_;
v___y_2889_ = v___y_2916_;
v___y_2890_ = v___x_2917_;
v___y_2891_ = v_fragment_2914_;
v___y_2892_ = v___x_2918_;
goto v___jp_2886_;
}
else
{
lean_object* v_val_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2928_; 
v_val_2919_ = lean_ctor_get(v_host_2910_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_host_2910_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2921_ = v_host_2910_;
v_isShared_2922_ = v_isSharedCheck_2928_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_val_2919_);
lean_dec(v_host_2910_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2928_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
uint8_t v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2926_; 
v___x_2923_ = 1;
v___x_2924_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2924_, 0, v_userInfo_2909_);
lean_ctor_set(v___x_2924_, 1, v_val_2919_);
lean_ctor_set(v___x_2924_, 2, v_port_2911_);
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 0, v___x_2924_);
v___x_2926_ = v___x_2921_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___x_2924_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
v___y_2887_ = v_pathSegments_2912_;
v___y_2888_ = v_query_2913_;
v___y_2889_ = v___y_2916_;
v___y_2890_ = v___x_2923_;
v___y_2891_ = v_fragment_2914_;
v___y_2892_ = v___x_2926_;
goto v___jp_2886_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withScheme_x21(lean_object* v_uri_2931_, lean_object* v_scheme_2932_){
_start:
{
lean_object* v_authority_2933_; lean_object* v_path_2934_; lean_object* v_query_2935_; lean_object* v_fragment_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2944_; 
v_authority_2933_ = lean_ctor_get(v_uri_2931_, 1);
v_path_2934_ = lean_ctor_get(v_uri_2931_, 2);
v_query_2935_ = lean_ctor_get(v_uri_2931_, 3);
v_fragment_2936_ = lean_ctor_get(v_uri_2931_, 4);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_uri_2931_);
if (v_isSharedCheck_2944_ == 0)
{
lean_object* v_unused_2945_; 
v_unused_2945_ = lean_ctor_get(v_uri_2931_, 0);
lean_dec(v_unused_2945_);
v___x_2938_ = v_uri_2931_;
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_fragment_2936_);
lean_inc(v_query_2935_);
lean_inc(v_path_2934_);
lean_inc(v_authority_2933_);
lean_dec(v_uri_2931_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2942_; 
v___x_2940_ = l_Std_Http_URI_Scheme_ofString_x21(v_scheme_2932_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2940_);
v___x_2942_ = v___x_2938_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_authority_2933_);
lean_ctor_set(v_reuseFailAlloc_2943_, 2, v_path_2934_);
lean_ctor_set(v_reuseFailAlloc_2943_, 3, v_query_2935_);
lean_ctor_set(v_reuseFailAlloc_2943_, 4, v_fragment_2936_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withAuthority(lean_object* v_uri_2946_, lean_object* v_authority_2947_){
_start:
{
lean_object* v_scheme_2948_; lean_object* v_path_2949_; lean_object* v_query_2950_; lean_object* v_fragment_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
v_scheme_2948_ = lean_ctor_get(v_uri_2946_, 0);
v_path_2949_ = lean_ctor_get(v_uri_2946_, 2);
v_query_2950_ = lean_ctor_get(v_uri_2946_, 3);
v_fragment_2951_ = lean_ctor_get(v_uri_2946_, 4);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_uri_2946_);
if (v_isSharedCheck_2958_ == 0)
{
lean_object* v_unused_2959_; 
v_unused_2959_ = lean_ctor_get(v_uri_2946_, 1);
lean_dec(v_unused_2959_);
v___x_2953_ = v_uri_2946_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_fragment_2951_);
lean_inc(v_query_2950_);
lean_inc(v_path_2949_);
lean_inc(v_scheme_2948_);
lean_dec(v_uri_2946_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 1, v_authority_2947_);
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_scheme_2948_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_authority_2947_);
lean_ctor_set(v_reuseFailAlloc_2957_, 2, v_path_2949_);
lean_ctor_set(v_reuseFailAlloc_2957_, 3, v_query_2950_);
lean_ctor_set(v_reuseFailAlloc_2957_, 4, v_fragment_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withPath(lean_object* v_uri_2960_, lean_object* v_path_2961_){
_start:
{
lean_object* v_scheme_2962_; lean_object* v_authority_2963_; lean_object* v_query_2964_; lean_object* v_fragment_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
v_scheme_2962_ = lean_ctor_get(v_uri_2960_, 0);
v_authority_2963_ = lean_ctor_get(v_uri_2960_, 1);
v_query_2964_ = lean_ctor_get(v_uri_2960_, 3);
v_fragment_2965_ = lean_ctor_get(v_uri_2960_, 4);
v_isSharedCheck_2972_ = !lean_is_exclusive(v_uri_2960_);
if (v_isSharedCheck_2972_ == 0)
{
lean_object* v_unused_2973_; 
v_unused_2973_ = lean_ctor_get(v_uri_2960_, 2);
lean_dec(v_unused_2973_);
v___x_2967_ = v_uri_2960_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_fragment_2965_);
lean_inc(v_query_2964_);
lean_inc(v_authority_2963_);
lean_inc(v_scheme_2962_);
lean_dec(v_uri_2960_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 2, v_path_2961_);
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_scheme_2962_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_authority_2963_);
lean_ctor_set(v_reuseFailAlloc_2971_, 2, v_path_2961_);
lean_ctor_set(v_reuseFailAlloc_2971_, 3, v_query_2964_);
lean_ctor_set(v_reuseFailAlloc_2971_, 4, v_fragment_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withQuery(lean_object* v_uri_2974_, lean_object* v_query_2975_){
_start:
{
lean_object* v_scheme_2976_; lean_object* v_authority_2977_; lean_object* v_path_2978_; lean_object* v_fragment_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2987_; 
v_scheme_2976_ = lean_ctor_get(v_uri_2974_, 0);
v_authority_2977_ = lean_ctor_get(v_uri_2974_, 1);
v_path_2978_ = lean_ctor_get(v_uri_2974_, 2);
v_fragment_2979_ = lean_ctor_get(v_uri_2974_, 4);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_uri_2974_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v_uri_2974_, 3);
lean_dec(v_unused_2988_);
v___x_2981_ = v_uri_2974_;
v_isShared_2982_ = v_isSharedCheck_2987_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_fragment_2979_);
lean_inc(v_path_2978_);
lean_inc(v_authority_2977_);
lean_inc(v_scheme_2976_);
lean_dec(v_uri_2974_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2987_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2983_; lean_object* v___x_2985_; 
v___x_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2983_, 0, v_query_2975_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 3, v___x_2983_);
v___x_2985_ = v___x_2981_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_scheme_2976_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_authority_2977_);
lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_path_2978_);
lean_ctor_set(v_reuseFailAlloc_2986_, 3, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_2986_, 4, v_fragment_2979_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withFragment(lean_object* v_uri_2989_, lean_object* v_fragment_2990_){
_start:
{
lean_object* v_scheme_2991_; lean_object* v_authority_2992_; lean_object* v_path_2993_; lean_object* v_query_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
v_scheme_2991_ = lean_ctor_get(v_uri_2989_, 0);
v_authority_2992_ = lean_ctor_get(v_uri_2989_, 1);
v_path_2993_ = lean_ctor_get(v_uri_2989_, 2);
v_query_2994_ = lean_ctor_get(v_uri_2989_, 3);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_uri_2989_);
if (v_isSharedCheck_3001_ == 0)
{
lean_object* v_unused_3002_; 
v_unused_3002_ = lean_ctor_get(v_uri_2989_, 4);
lean_dec(v_unused_3002_);
v___x_2996_ = v_uri_2989_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_query_2994_);
lean_inc(v_path_2993_);
lean_inc(v_authority_2992_);
lean_inc(v_scheme_2991_);
lean_dec(v_uri_2989_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 4, v_fragment_2990_);
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_scheme_2991_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v_authority_2992_);
lean_ctor_set(v_reuseFailAlloc_3000_, 2, v_path_2993_);
lean_ctor_set(v_reuseFailAlloc_3000_, 3, v_query_2994_);
lean_ctor_set(v_reuseFailAlloc_3000_, 4, v_fragment_2990_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_normalize(lean_object* v_uri_3003_){
_start:
{
lean_object* v_scheme_3004_; lean_object* v_authority_3005_; lean_object* v_path_3006_; lean_object* v_query_3007_; lean_object* v_fragment_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3016_; 
v_scheme_3004_ = lean_ctor_get(v_uri_3003_, 0);
v_authority_3005_ = lean_ctor_get(v_uri_3003_, 1);
v_path_3006_ = lean_ctor_get(v_uri_3003_, 2);
v_query_3007_ = lean_ctor_get(v_uri_3003_, 3);
v_fragment_3008_ = lean_ctor_get(v_uri_3003_, 4);
v_isSharedCheck_3016_ = !lean_is_exclusive(v_uri_3003_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3010_ = v_uri_3003_;
v_isShared_3011_ = v_isSharedCheck_3016_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_fragment_3008_);
lean_inc(v_query_3007_);
lean_inc(v_path_3006_);
lean_inc(v_authority_3005_);
lean_inc(v_scheme_3004_);
lean_dec(v_uri_3003_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3016_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; lean_object* v___x_3014_; 
v___x_3012_ = l_Std_Http_URI_Path_normalize(v_path_3006_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 2, v___x_3012_);
v___x_3014_ = v___x_3010_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_scheme_3004_);
lean_ctor_set(v_reuseFailAlloc_3015_, 1, v_authority_3005_);
lean_ctor_set(v_reuseFailAlloc_3015_, 2, v___x_3012_);
lean_ctor_set(v_reuseFailAlloc_3015_, 3, v_query_3007_);
lean_ctor_set(v_reuseFailAlloc_3015_, 4, v_fragment_3008_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___redArg(lean_object* v_x_3017_){
_start:
{
lean_object* v_scheme_3018_; lean_object* v_host_3019_; uint16_t v_port_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; uint8_t v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v_ctr_3041_; lean_object* v_a_3042_; 
v_scheme_3018_ = lean_ctor_get(v_x_3017_, 0);
lean_inc_ref(v_scheme_3018_);
v_host_3019_ = lean_ctor_get(v_x_3017_, 1);
lean_inc_ref(v_host_3019_);
v_port_3020_ = lean_ctor_get_uint16(v_x_3017_, sizeof(void*)*2);
lean_dec_ref(v_x_3017_);
v___x_3021_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_3022_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_3023_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_3024_ = l_String_quote(v_scheme_3018_);
v___x_3025_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
v___x_3026_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3023_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = 0;
v___x_3028_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3028_, 0, v___x_3026_);
lean_ctor_set_uint8(v___x_3028_, sizeof(void*)*1, v___x_3027_);
v___x_3029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3022_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_3031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3029_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
v___x_3032_ = lean_box(1);
v___x_3033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3031_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
v___x_3034_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_3035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3033_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
v___x_3036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
lean_ctor_set(v___x_3036_, 1, v___x_3021_);
v___x_3037_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_3038_ = lean_unsigned_to_nat(0u);
v___x_3039_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_3019_))
{
case 0:
{
lean_object* v_name_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3081_; 
v_name_3072_ = lean_ctor_get(v_host_3019_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v_host_3019_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3074_ = v_host_3019_;
v_isShared_3075_ = v_isSharedCheck_3081_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_name_3072_);
lean_dec(v_host_3019_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3081_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3079_; 
v___x_3076_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_3077_ = l_String_quote(v_name_3072_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set_tag(v___x_3074_, 3);
lean_ctor_set(v___x_3074_, 0, v___x_3077_);
v___x_3079_ = v___x_3074_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3077_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
v_ctr_3041_ = v___x_3076_;
v_a_3042_ = v___x_3079_;
goto v___jp_3040_;
}
}
}
case 1:
{
lean_object* v_ipv4_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3091_; 
v_ipv4_3082_ = lean_ctor_get(v_host_3019_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_host_3019_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3084_ = v_host_3019_;
v_isShared_3085_ = v_isSharedCheck_3091_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_ipv4_3082_);
lean_dec(v_host_3019_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3091_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3089_; 
v___x_3086_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_3087_ = lean_uv_ntop_v4(v_ipv4_3082_);
lean_dec_ref(v_ipv4_3082_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set_tag(v___x_3084_, 3);
lean_ctor_set(v___x_3084_, 0, v___x_3087_);
v___x_3089_ = v___x_3084_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v___x_3087_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
v_ctr_3041_ = v___x_3086_;
v_a_3042_ = v___x_3089_;
goto v___jp_3040_;
}
}
}
default: 
{
lean_object* v_ipv6_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3101_; 
v_ipv6_3092_ = lean_ctor_get(v_host_3019_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_host_3019_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3094_ = v_host_3019_;
v_isShared_3095_ = v_isSharedCheck_3101_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_ipv6_3092_);
lean_dec(v_host_3019_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3101_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3099_; 
v___x_3096_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_3097_ = lean_uv_ntop_v6(v_ipv6_3092_);
lean_dec_ref(v_ipv6_3092_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set_tag(v___x_3094_, 3);
lean_ctor_set(v___x_3094_, 0, v___x_3097_);
v___x_3099_ = v___x_3094_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
v_ctr_3041_ = v___x_3096_;
v_a_3042_ = v___x_3099_;
goto v___jp_3040_;
}
}
}
}
v___jp_3040_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3043_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_3044_ = lean_string_append(v___x_3043_, v_ctr_3041_);
v___x_3045_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
v___x_3046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
lean_ctor_set(v___x_3046_, 1, v___x_3032_);
v___x_3047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
lean_ctor_set(v___x_3047_, 1, v_a_3042_);
v___x_3048_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3039_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
lean_ctor_set_uint8(v___x_3049_, sizeof(void*)*1, v___x_3027_);
v___x_3050_ = l_Repr_addAppParen(v___x_3049_, v___x_3038_);
v___x_3051_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3037_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
v___x_3052_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
lean_ctor_set_uint8(v___x_3052_, sizeof(void*)*1, v___x_3027_);
v___x_3053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3036_);
lean_ctor_set(v___x_3053_, 1, v___x_3052_);
v___x_3054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
lean_ctor_set(v___x_3054_, 1, v___x_3030_);
v___x_3055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v___x_3032_);
v___x_3056_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_3057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3055_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
v___x_3058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
lean_ctor_set(v___x_3058_, 1, v___x_3021_);
v___x_3059_ = lean_uint16_to_nat(v_port_3020_);
v___x_3060_ = l_Nat_reprFast(v___x_3059_);
v___x_3061_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3060_);
v___x_3062_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3037_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
lean_ctor_set_uint8(v___x_3063_, sizeof(void*)*1, v___x_3027_);
v___x_3064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3058_);
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
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*1, v___x_3027_);
return v___x_3071_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr(lean_object* v_x_3102_, lean_object* v_prec_3103_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Std_Http_URI_instReprOrigin_repr___redArg(v_x_3102_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___boxed(lean_object* v_x_3105_, lean_object* v_prec_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Std_Http_URI_instReprOrigin_repr(v_x_3105_, v_prec_3106_);
lean_dec(v_prec_3106_);
return v_res_3107_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqOrigin_beq(lean_object* v_x_3110_, lean_object* v_x_3111_){
_start:
{
lean_object* v_scheme_3112_; lean_object* v_host_3113_; uint16_t v_port_3114_; lean_object* v_scheme_3115_; lean_object* v_host_3116_; uint16_t v_port_3117_; uint8_t v___x_3118_; 
v_scheme_3112_ = lean_ctor_get(v_x_3110_, 0);
v_host_3113_ = lean_ctor_get(v_x_3110_, 1);
v_port_3114_ = lean_ctor_get_uint16(v_x_3110_, sizeof(void*)*2);
v_scheme_3115_ = lean_ctor_get(v_x_3111_, 0);
v_host_3116_ = lean_ctor_get(v_x_3111_, 1);
v_port_3117_ = lean_ctor_get_uint16(v_x_3111_, sizeof(void*)*2);
v___x_3118_ = lean_string_dec_eq(v_scheme_3112_, v_scheme_3115_);
if (v___x_3118_ == 0)
{
return v___x_3118_;
}
else
{
uint8_t v___x_3119_; 
v___x_3119_ = l_Std_Http_URI_instBEqHost_beq(v_host_3113_, v_host_3116_);
if (v___x_3119_ == 0)
{
return v___x_3119_;
}
else
{
uint8_t v___x_3120_; 
v___x_3120_ = lean_uint16_dec_eq(v_port_3114_, v_port_3117_);
return v___x_3120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqOrigin_beq___boxed(lean_object* v_x_3121_, lean_object* v_x_3122_){
_start:
{
uint8_t v_res_3123_; lean_object* v_r_3124_; 
v_res_3123_ = l_Std_Http_URI_instBEqOrigin_beq(v_x_3121_, v_x_3122_);
lean_dec_ref(v_x_3122_);
lean_dec_ref(v_x_3121_);
v_r_3124_ = lean_box(v_res_3123_);
return v_r_3124_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Origin_hostHeader(lean_object* v_o_3127_){
_start:
{
lean_object* v_scheme_3128_; lean_object* v_host_3129_; uint16_t v_port_3130_; lean_object* v___y_3132_; uint16_t v_defaultPort_3138_; uint8_t v___x_3139_; 
v_scheme_3128_ = lean_ctor_get(v_o_3127_, 0);
lean_inc_ref(v_scheme_3128_);
v_host_3129_ = lean_ctor_get(v_o_3127_, 1);
lean_inc_ref(v_host_3129_);
v_port_3130_ = lean_ctor_get_uint16(v_o_3127_, sizeof(void*)*2);
lean_dec_ref(v_o_3127_);
v_defaultPort_3138_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_3128_);
lean_dec_ref(v_scheme_3128_);
v___x_3139_ = lean_uint16_dec_eq(v_port_3130_, v_defaultPort_3138_);
if (v___x_3139_ == 0)
{
switch(lean_obj_tag(v_host_3129_))
{
case 0:
{
lean_object* v_name_3140_; 
v_name_3140_ = lean_ctor_get(v_host_3129_, 0);
lean_inc_ref(v_name_3140_);
lean_dec_ref_known(v_host_3129_, 1);
v___y_3132_ = v_name_3140_;
goto v___jp_3131_;
}
case 1:
{
lean_object* v_ipv4_3141_; lean_object* v___x_3142_; 
v_ipv4_3141_ = lean_ctor_get(v_host_3129_, 0);
lean_inc_ref(v_ipv4_3141_);
lean_dec_ref_known(v_host_3129_, 1);
v___x_3142_ = lean_uv_ntop_v4(v_ipv4_3141_);
lean_dec_ref(v_ipv4_3141_);
v___y_3132_ = v___x_3142_;
goto v___jp_3131_;
}
default: 
{
lean_object* v_ipv6_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v_ipv6_3143_ = lean_ctor_get(v_host_3129_, 0);
lean_inc_ref(v_ipv6_3143_);
lean_dec_ref_known(v_host_3129_, 1);
v___x_3144_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3145_ = lean_uv_ntop_v6(v_ipv6_3143_);
lean_dec_ref(v_ipv6_3143_);
v___x_3146_ = lean_string_append(v___x_3144_, v___x_3145_);
lean_dec_ref(v___x_3145_);
v___x_3147_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3148_ = lean_string_append(v___x_3146_, v___x_3147_);
v___y_3132_ = v___x_3148_;
goto v___jp_3131_;
}
}
}
else
{
switch(lean_obj_tag(v_host_3129_))
{
case 0:
{
lean_object* v_name_3149_; 
v_name_3149_ = lean_ctor_get(v_host_3129_, 0);
lean_inc_ref(v_name_3149_);
lean_dec_ref_known(v_host_3129_, 1);
return v_name_3149_;
}
case 1:
{
lean_object* v_ipv4_3150_; lean_object* v___x_3151_; 
v_ipv4_3150_ = lean_ctor_get(v_host_3129_, 0);
lean_inc_ref(v_ipv4_3150_);
lean_dec_ref_known(v_host_3129_, 1);
v___x_3151_ = lean_uv_ntop_v4(v_ipv4_3150_);
lean_dec_ref(v_ipv4_3150_);
return v___x_3151_;
}
default: 
{
lean_object* v_ipv6_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_ipv6_3152_ = lean_ctor_get(v_host_3129_, 0);
lean_inc_ref(v_ipv6_3152_);
lean_dec_ref_known(v_host_3129_, 1);
v___x_3153_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3154_ = lean_uv_ntop_v6(v_ipv6_3152_);
lean_dec_ref(v_ipv6_3152_);
v___x_3155_ = lean_string_append(v___x_3153_, v___x_3154_);
lean_dec_ref(v___x_3154_);
v___x_3156_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3157_ = lean_string_append(v___x_3155_, v___x_3156_);
return v___x_3157_;
}
}
}
v___jp_3131_:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3133_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3134_ = lean_string_append(v___y_3132_, v___x_3133_);
v___x_3135_ = lean_uint16_to_nat(v_port_3130_);
v___x_3136_ = l_Nat_reprFast(v___x_3135_);
v___x_3137_ = lean_string_append(v___x_3134_, v___x_3136_);
lean_dec_ref(v___x_3136_);
return v___x_3137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___redArg(lean_object* v_x_3164_){
_start:
{
lean_object* v_authority_3165_; lean_object* v_path_3166_; lean_object* v_query_3167_; lean_object* v_fragment_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; uint8_t v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v_authority_3165_ = lean_ctor_get(v_x_3164_, 0);
lean_inc(v_authority_3165_);
v_path_3166_ = lean_ctor_get(v_x_3164_, 1);
lean_inc_ref(v_path_3166_);
v_query_3167_ = lean_ctor_get(v_x_3164_, 2);
lean_inc(v_query_3167_);
v_fragment_3168_ = lean_ctor_get(v_x_3164_, 3);
lean_inc(v_fragment_3168_);
lean_dec_ref(v_x_3164_);
v___x_3169_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_3170_ = ((lean_object*)(l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__1));
v___x_3171_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_3172_ = lean_unsigned_to_nat(0u);
v___x_3173_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_3165_, v___x_3172_);
v___x_3174_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3171_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
v___x_3175_ = 0;
v___x_3176_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3176_, 0, v___x_3174_);
lean_ctor_set_uint8(v___x_3176_, sizeof(void*)*1, v___x_3175_);
v___x_3177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3170_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_3179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3177_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = lean_box(1);
v___x_3181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3179_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_3183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3181_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
lean_ctor_set(v___x_3184_, 1, v___x_3169_);
v___x_3185_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_3186_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3166_);
v___x_3187_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3185_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
v___x_3188_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3188_, 0, v___x_3187_);
lean_ctor_set_uint8(v___x_3188_, sizeof(void*)*1, v___x_3175_);
v___x_3189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3184_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
v___x_3190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
lean_ctor_set(v___x_3190_, 1, v___x_3178_);
v___x_3191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
lean_ctor_set(v___x_3191_, 1, v___x_3180_);
v___x_3192_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_3193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3191_);
lean_ctor_set(v___x_3193_, 1, v___x_3192_);
v___x_3194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
lean_ctor_set(v___x_3194_, 1, v___x_3169_);
v___x_3195_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_3196_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3167_, v___x_3172_);
v___x_3197_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3195_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
v___x_3198_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3198_, 0, v___x_3197_);
lean_ctor_set_uint8(v___x_3198_, sizeof(void*)*1, v___x_3175_);
v___x_3199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3194_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
v___x_3200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
lean_ctor_set(v___x_3200_, 1, v___x_3178_);
v___x_3201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
lean_ctor_set(v___x_3201_, 1, v___x_3180_);
v___x_3202_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_3203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3201_);
lean_ctor_set(v___x_3203_, 1, v___x_3202_);
v___x_3204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
lean_ctor_set(v___x_3204_, 1, v___x_3169_);
v___x_3205_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_3206_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_3168_, v___x_3172_);
v___x_3207_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3205_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
v___x_3208_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
lean_ctor_set_uint8(v___x_3208_, sizeof(void*)*1, v___x_3175_);
v___x_3209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3204_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_3211_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_3212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
lean_ctor_set(v___x_3212_, 1, v___x_3209_);
v___x_3213_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_3214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3212_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
v___x_3215_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3210_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
v___x_3216_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
lean_ctor_set_uint8(v___x_3216_, sizeof(void*)*1, v___x_3175_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr(lean_object* v_x_3217_, lean_object* v_prec_3218_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_x_3217_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___boxed(lean_object* v_x_3220_, lean_object* v_prec_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Std_Http_URI_instReprRelativeRef_repr(v_x_3220_, v_prec_3221_);
lean_dec(v_prec_3221_);
return v_res_3222_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqRelativeRef_beq(lean_object* v_x_3230_, lean_object* v_x_3231_){
_start:
{
lean_object* v_authority_3232_; lean_object* v_path_3233_; lean_object* v_query_3234_; lean_object* v_fragment_3235_; lean_object* v_authority_3236_; lean_object* v_path_3237_; lean_object* v_query_3238_; lean_object* v_fragment_3239_; uint8_t v___x_3240_; 
v_authority_3232_ = lean_ctor_get(v_x_3230_, 0);
v_path_3233_ = lean_ctor_get(v_x_3230_, 1);
v_query_3234_ = lean_ctor_get(v_x_3230_, 2);
v_fragment_3235_ = lean_ctor_get(v_x_3230_, 3);
v_authority_3236_ = lean_ctor_get(v_x_3231_, 0);
v_path_3237_ = lean_ctor_get(v_x_3231_, 1);
v_query_3238_ = lean_ctor_get(v_x_3231_, 2);
v_fragment_3239_ = lean_ctor_get(v_x_3231_, 3);
v___x_3240_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_3232_, v_authority_3236_);
if (v___x_3240_ == 0)
{
return v___x_3240_;
}
else
{
uint8_t v___x_3241_; 
v___x_3241_ = l_Std_Http_URI_instBEqPath_beq(v_path_3233_, v_path_3237_);
if (v___x_3241_ == 0)
{
return v___x_3241_;
}
else
{
uint8_t v___x_3242_; 
v___x_3242_ = l_instBEqOption_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_3234_, v_query_3238_);
if (v___x_3242_ == 0)
{
return v___x_3242_;
}
else
{
uint8_t v___x_3243_; 
v___x_3243_ = l_instBEqOption_beq___at___00__private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Query_nameIs_spec__0(v_fragment_3235_, v_fragment_3239_);
return v___x_3243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqRelativeRef_beq___boxed(lean_object* v_x_3244_, lean_object* v_x_3245_){
_start:
{
uint8_t v_res_3246_; lean_object* v_r_3247_; 
v_res_3246_ = l_Std_Http_URI_instBEqRelativeRef_beq(v_x_3244_, v_x_3245_);
lean_dec_ref(v_x_3245_);
lean_dec_ref(v_x_3244_);
v_r_3247_ = lean_box(v_res_3246_);
return v_r_3247_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringRelativeRef___lam__1(lean_object* v___f_3250_, lean_object* v_ref_3251_){
_start:
{
lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v_authority_3260_; lean_object* v_path_3261_; lean_object* v_query_3262_; lean_object* v_fragment_3263_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3275_; 
v_authority_3260_ = lean_ctor_get(v_ref_3251_, 0);
lean_inc(v_authority_3260_);
v_path_3261_ = lean_ctor_get(v_ref_3251_, 1);
lean_inc_ref(v_path_3261_);
v_query_3262_ = lean_ctor_get(v_ref_3251_, 2);
lean_inc(v_query_3262_);
v_fragment_3263_ = lean_ctor_get(v_ref_3251_, 3);
lean_inc(v_fragment_3263_);
lean_dec_ref(v_ref_3251_);
if (lean_obj_tag(v_authority_3260_) == 0)
{
lean_object* v___x_3286_; 
v___x_3286_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3275_ = v___x_3286_;
goto v___jp_3274_;
}
else
{
lean_object* v_val_3287_; lean_object* v_userInfo_3288_; lean_object* v_host_3289_; lean_object* v_port_3290_; lean_object* v___x_3291_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3310_; 
v_val_3287_ = lean_ctor_get(v_authority_3260_, 0);
lean_inc(v_val_3287_);
lean_dec_ref_known(v_authority_3260_, 1);
v_userInfo_3288_ = lean_ctor_get(v_val_3287_, 0);
lean_inc(v_userInfo_3288_);
v_host_3289_ = lean_ctor_get(v_val_3287_, 1);
lean_inc_ref(v_host_3289_);
v_port_3290_ = lean_ctor_get(v_val_3287_, 2);
lean_inc(v_port_3290_);
lean_dec(v_val_3287_);
v___x_3291_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3288_) == 0)
{
lean_object* v___x_3320_; 
v___x_3320_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3310_ = v___x_3320_;
goto v___jp_3309_;
}
else
{
lean_object* v_val_3321_; lean_object* v_password_3322_; 
v_val_3321_ = lean_ctor_get(v_userInfo_3288_, 0);
lean_inc(v_val_3321_);
lean_dec_ref_known(v_userInfo_3288_, 1);
v_password_3322_ = lean_ctor_get(v_val_3321_, 1);
if (lean_obj_tag(v_password_3322_) == 0)
{
lean_object* v_username_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v_username_3323_ = lean_ctor_get(v_val_3321_, 0);
lean_inc_ref(v_username_3323_);
lean_dec(v_val_3321_);
v___x_3324_ = lean_string_from_utf8_unchecked(v_username_3323_);
v___x_3325_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3326_ = lean_string_append(v___x_3324_, v___x_3325_);
v___y_3310_ = v___x_3326_;
goto v___jp_3309_;
}
else
{
lean_object* v_username_3327_; lean_object* v_val_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_inc_ref(v_password_3322_);
v_username_3327_ = lean_ctor_get(v_val_3321_, 0);
lean_inc_ref(v_username_3327_);
lean_dec(v_val_3321_);
v_val_3328_ = lean_ctor_get(v_password_3322_, 0);
lean_inc(v_val_3328_);
lean_dec_ref_known(v_password_3322_, 1);
v___x_3329_ = lean_string_from_utf8_unchecked(v_username_3327_);
v___x_3330_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3331_ = lean_string_append(v___x_3329_, v___x_3330_);
v___x_3332_ = lean_string_from_utf8_unchecked(v_val_3328_);
v___x_3333_ = lean_string_append(v___x_3331_, v___x_3332_);
lean_dec_ref(v___x_3332_);
v___x_3334_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3335_ = lean_string_append(v___x_3333_, v___x_3334_);
v___y_3310_ = v___x_3335_;
goto v___jp_3309_;
}
}
v___jp_3292_:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3296_ = lean_string_append(v___y_3294_, v___y_3293_);
lean_dec_ref(v___y_3293_);
v___x_3297_ = lean_string_append(v___x_3296_, v___y_3295_);
lean_dec_ref(v___y_3295_);
v___x_3298_ = lean_string_append(v___x_3291_, v___x_3297_);
lean_dec_ref(v___x_3297_);
v___y_3275_ = v___x_3298_;
goto v___jp_3274_;
}
v___jp_3299_:
{
switch(lean_obj_tag(v_port_3290_))
{
case 0:
{
lean_object* v___x_3302_; 
v___x_3302_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3293_ = v___y_3301_;
v___y_3294_ = v___y_3300_;
v___y_3295_ = v___x_3302_;
goto v___jp_3292_;
}
case 1:
{
lean_object* v___x_3303_; 
v___x_3303_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3293_ = v___y_3301_;
v___y_3294_ = v___y_3300_;
v___y_3295_ = v___x_3303_;
goto v___jp_3292_;
}
default: 
{
uint16_t v_port_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v_port_3304_ = lean_ctor_get_uint16(v_port_3290_, 0);
lean_dec_ref_known(v_port_3290_, 0);
v___x_3305_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3306_ = lean_uint16_to_nat(v_port_3304_);
v___x_3307_ = l_Nat_reprFast(v___x_3306_);
v___x_3308_ = lean_string_append(v___x_3305_, v___x_3307_);
lean_dec_ref(v___x_3307_);
v___y_3293_ = v___y_3301_;
v___y_3294_ = v___y_3300_;
v___y_3295_ = v___x_3308_;
goto v___jp_3292_;
}
}
}
v___jp_3309_:
{
switch(lean_obj_tag(v_host_3289_))
{
case 0:
{
lean_object* v_name_3311_; 
v_name_3311_ = lean_ctor_get(v_host_3289_, 0);
lean_inc_ref(v_name_3311_);
lean_dec_ref_known(v_host_3289_, 1);
v___y_3300_ = v___y_3310_;
v___y_3301_ = v_name_3311_;
goto v___jp_3299_;
}
case 1:
{
lean_object* v_ipv4_3312_; lean_object* v___x_3313_; 
v_ipv4_3312_ = lean_ctor_get(v_host_3289_, 0);
lean_inc_ref(v_ipv4_3312_);
lean_dec_ref_known(v_host_3289_, 1);
v___x_3313_ = lean_uv_ntop_v4(v_ipv4_3312_);
lean_dec_ref(v_ipv4_3312_);
v___y_3300_ = v___y_3310_;
v___y_3301_ = v___x_3313_;
goto v___jp_3299_;
}
default: 
{
lean_object* v_ipv6_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_ipv6_3314_ = lean_ctor_get(v_host_3289_, 0);
lean_inc_ref(v_ipv6_3314_);
lean_dec_ref_known(v_host_3289_, 1);
v___x_3315_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3316_ = lean_uv_ntop_v6(v_ipv6_3314_);
lean_dec_ref(v_ipv6_3314_);
v___x_3317_ = lean_string_append(v___x_3315_, v___x_3316_);
lean_dec_ref(v___x_3316_);
v___x_3318_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3319_ = lean_string_append(v___x_3317_, v___x_3318_);
v___y_3300_ = v___y_3310_;
v___y_3301_ = v___x_3319_;
goto v___jp_3299_;
}
}
}
}
v___jp_3252_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = lean_string_append(v___y_3253_, v___y_3254_);
lean_dec_ref(v___y_3254_);
v___x_3258_ = lean_string_append(v___x_3257_, v___y_3255_);
lean_dec_ref(v___y_3255_);
v___x_3259_ = lean_string_append(v___x_3258_, v___y_3256_);
lean_dec_ref(v___y_3256_);
return v___x_3259_;
}
v___jp_3264_:
{
lean_object* v_queryPart_3267_; 
v_queryPart_3267_ = l_Std_Http_URI_Query_formatOption(v_query_3262_);
if (lean_obj_tag(v_fragment_3263_) == 0)
{
lean_object* v___x_3268_; 
v___x_3268_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3253_ = v___y_3265_;
v___y_3254_ = v___y_3266_;
v___y_3255_ = v_queryPart_3267_;
v___y_3256_ = v___x_3268_;
goto v___jp_3252_;
}
else
{
lean_object* v_val_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v_val_3269_ = lean_ctor_get(v_fragment_3263_, 0);
lean_inc(v_val_3269_);
lean_dec_ref_known(v_fragment_3263_, 1);
v___x_3270_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3271_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3269_);
v___x_3272_ = lean_string_from_utf8_unchecked(v___x_3271_);
v___x_3273_ = lean_string_append(v___x_3270_, v___x_3272_);
lean_dec_ref(v___x_3272_);
v___y_3253_ = v___y_3265_;
v___y_3254_ = v___y_3266_;
v___y_3255_ = v_queryPart_3267_;
v___y_3256_ = v___x_3273_;
goto v___jp_3252_;
}
}
v___jp_3274_:
{
lean_object* v_segments_3276_; uint8_t v_absolute_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; size_t v_sz_3280_; size_t v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v_result_3284_; 
v_segments_3276_ = lean_ctor_get(v_path_3261_, 0);
lean_inc_ref(v_segments_3276_);
v_absolute_3277_ = lean_ctor_get_uint8(v_path_3261_, sizeof(void*)*1);
lean_dec_ref(v_path_3261_);
v___x_3278_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3279_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3280_ = lean_array_size(v_segments_3276_);
v___x_3281_ = ((size_t)0ULL);
v___x_3282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3279_, v___f_3250_, v_sz_3280_, v___x_3281_, v_segments_3276_);
v___x_3283_ = lean_array_to_list(v___x_3282_);
v_result_3284_ = l_String_intercalate(v___x_3278_, v___x_3283_);
if (v_absolute_3277_ == 0)
{
v___y_3265_ = v___y_3275_;
v___y_3266_ = v_result_3284_;
goto v___jp_3264_;
}
else
{
lean_object* v___x_3285_; 
v___x_3285_ = lean_string_append(v___x_3278_, v_result_3284_);
lean_dec_ref(v_result_3284_);
v___y_3265_ = v___y_3275_;
v___y_3266_ = v___x_3285_;
goto v___jp_3264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___impl(lean_object* v_x_3339_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = lean_obj_tag_nat(v_x_3339_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___impl___boxed(lean_object* v_x_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Std_Http_URIReference_ctorIdx___impl(v_x_3341_);
lean_dec_ref(v_x_3341_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___redArg(lean_object* v_t_3343_, lean_object* v_k_3344_){
_start:
{
lean_object* v_uri_3345_; lean_object* v___x_3346_; 
v_uri_3345_ = lean_ctor_get(v_t_3343_, 0);
lean_inc_ref(v_uri_3345_);
lean_dec_ref(v_t_3343_);
v___x_3346_ = lean_apply_1(v_k_3344_, v_uri_3345_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim(lean_object* v_motive_3347_, lean_object* v_ctorIdx_3348_, lean_object* v_t_3349_, lean_object* v_h_3350_, lean_object* v_k_3351_){
_start:
{
lean_object* v___x_3352_; 
v___x_3352_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3349_, v_k_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___boxed(lean_object* v_motive_3353_, lean_object* v_ctorIdx_3354_, lean_object* v_t_3355_, lean_object* v_h_3356_, lean_object* v_k_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Std_Http_URIReference_ctorElim(v_motive_3353_, v_ctorIdx_3354_, v_t_3355_, v_h_3356_, v_k_3357_);
lean_dec(v_ctorIdx_3354_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim___redArg(lean_object* v_t_3359_, lean_object* v_absolute_3360_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3359_, v_absolute_3360_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim(lean_object* v_motive_3362_, lean_object* v_t_3363_, lean_object* v_h_3364_, lean_object* v_absolute_3365_){
_start:
{
lean_object* v___x_3366_; 
v___x_3366_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3363_, v_absolute_3365_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim___redArg(lean_object* v_t_3367_, lean_object* v_relative_3368_){
_start:
{
lean_object* v___x_3369_; 
v___x_3369_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3367_, v_relative_3368_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim(lean_object* v_motive_3370_, lean_object* v_t_3371_, lean_object* v_h_3372_, lean_object* v_relative_3373_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3371_, v_relative_3373_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr(lean_object* v_x_3387_, lean_object* v_prec_3388_){
_start:
{
if (lean_obj_tag(v_x_3387_) == 0)
{
lean_object* v_uri_3389_; lean_object* v___y_3391_; lean_object* v___x_3399_; uint8_t v___x_3400_; 
v_uri_3389_ = lean_ctor_get(v_x_3387_, 0);
lean_inc_ref(v_uri_3389_);
lean_dec_ref_known(v_x_3387_, 1);
v___x_3399_ = lean_unsigned_to_nat(1024u);
v___x_3400_ = lean_nat_dec_le(v___x_3399_, v_prec_3388_);
if (v___x_3400_ == 0)
{
lean_object* v___x_3401_; 
v___x_3401_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3391_ = v___x_3401_;
goto v___jp_3390_;
}
else
{
lean_object* v___x_3402_; 
v___x_3402_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3391_ = v___x_3402_;
goto v___jp_3390_;
}
v___jp_3390_:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3392_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__2));
v___x_3393_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3389_);
v___x_3394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3392_);
lean_ctor_set(v___x_3394_, 1, v___x_3393_);
lean_inc(v___y_3391_);
v___x_3395_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___y_3391_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
v___x_3396_ = 0;
v___x_3397_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3397_, 0, v___x_3395_);
lean_ctor_set_uint8(v___x_3397_, sizeof(void*)*1, v___x_3396_);
v___x_3398_ = l_Repr_addAppParen(v___x_3397_, v_prec_3388_);
return v___x_3398_;
}
}
else
{
lean_object* v_ref_3403_; lean_object* v___y_3405_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v_ref_3403_ = lean_ctor_get(v_x_3387_, 0);
lean_inc_ref(v_ref_3403_);
lean_dec_ref_known(v_x_3387_, 1);
v___x_3413_ = lean_unsigned_to_nat(1024u);
v___x_3414_ = lean_nat_dec_le(v___x_3413_, v_prec_3388_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; 
v___x_3415_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3405_ = v___x_3415_;
goto v___jp_3404_;
}
else
{
lean_object* v___x_3416_; 
v___x_3416_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3405_ = v___x_3416_;
goto v___jp_3404_;
}
v___jp_3404_:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; uint8_t v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3406_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__5));
v___x_3407_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_ref_3403_);
v___x_3408_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3406_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
lean_inc(v___y_3405_);
v___x_3409_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___y_3405_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = 0;
v___x_3411_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3411_, 0, v___x_3409_);
lean_ctor_set_uint8(v___x_3411_, sizeof(void*)*1, v___x_3410_);
v___x_3412_ = l_Repr_addAppParen(v___x_3411_, v_prec_3388_);
return v___x_3412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr___boxed(lean_object* v_x_3417_, lean_object* v_prec_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Std_Http_instReprURIReference_repr(v_x_3417_, v_prec_3418_);
lean_dec(v_prec_3418_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURIReference___lam__2(lean_object* v___f_3426_, lean_object* v___f_3427_, lean_object* v_x_3428_){
_start:
{
lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; 
if (lean_obj_tag(v_x_3428_) == 0)
{
lean_object* v_uri_3437_; lean_object* v_scheme_3438_; lean_object* v_authority_3439_; lean_object* v_path_3440_; lean_object* v_query_3441_; lean_object* v_fragment_3442_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3465_; 
lean_dec_ref(v___f_3427_);
v_uri_3437_ = lean_ctor_get(v_x_3428_, 0);
lean_inc_ref(v_uri_3437_);
lean_dec_ref_known(v_x_3428_, 1);
v_scheme_3438_ = lean_ctor_get(v_uri_3437_, 0);
lean_inc_ref(v_scheme_3438_);
v_authority_3439_ = lean_ctor_get(v_uri_3437_, 1);
lean_inc(v_authority_3439_);
v_path_3440_ = lean_ctor_get(v_uri_3437_, 2);
lean_inc_ref(v_path_3440_);
v_query_3441_ = lean_ctor_get(v_uri_3437_, 3);
lean_inc(v_query_3441_);
v_fragment_3442_ = lean_ctor_get(v_uri_3437_, 4);
lean_inc(v_fragment_3442_);
lean_dec_ref(v_uri_3437_);
if (lean_obj_tag(v_authority_3439_) == 0)
{
lean_object* v___x_3476_; 
v___x_3476_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3465_ = v___x_3476_;
goto v___jp_3464_;
}
else
{
lean_object* v_val_3477_; lean_object* v_userInfo_3478_; lean_object* v_host_3479_; lean_object* v_port_3480_; lean_object* v___x_3481_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3500_; 
v_val_3477_ = lean_ctor_get(v_authority_3439_, 0);
lean_inc(v_val_3477_);
lean_dec_ref_known(v_authority_3439_, 1);
v_userInfo_3478_ = lean_ctor_get(v_val_3477_, 0);
lean_inc(v_userInfo_3478_);
v_host_3479_ = lean_ctor_get(v_val_3477_, 1);
lean_inc_ref(v_host_3479_);
v_port_3480_ = lean_ctor_get(v_val_3477_, 2);
lean_inc(v_port_3480_);
lean_dec(v_val_3477_);
v___x_3481_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3478_) == 0)
{
lean_object* v___x_3510_; 
v___x_3510_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3500_ = v___x_3510_;
goto v___jp_3499_;
}
else
{
lean_object* v_val_3511_; lean_object* v_password_3512_; 
v_val_3511_ = lean_ctor_get(v_userInfo_3478_, 0);
lean_inc(v_val_3511_);
lean_dec_ref_known(v_userInfo_3478_, 1);
v_password_3512_ = lean_ctor_get(v_val_3511_, 1);
if (lean_obj_tag(v_password_3512_) == 0)
{
lean_object* v_username_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v_username_3513_ = lean_ctor_get(v_val_3511_, 0);
lean_inc_ref(v_username_3513_);
lean_dec(v_val_3511_);
v___x_3514_ = lean_string_from_utf8_unchecked(v_username_3513_);
v___x_3515_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3516_ = lean_string_append(v___x_3514_, v___x_3515_);
v___y_3500_ = v___x_3516_;
goto v___jp_3499_;
}
else
{
lean_object* v_username_3517_; lean_object* v_val_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
lean_inc_ref(v_password_3512_);
v_username_3517_ = lean_ctor_get(v_val_3511_, 0);
lean_inc_ref(v_username_3517_);
lean_dec(v_val_3511_);
v_val_3518_ = lean_ctor_get(v_password_3512_, 0);
lean_inc(v_val_3518_);
lean_dec_ref_known(v_password_3512_, 1);
v___x_3519_ = lean_string_from_utf8_unchecked(v_username_3517_);
v___x_3520_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3521_ = lean_string_append(v___x_3519_, v___x_3520_);
v___x_3522_ = lean_string_from_utf8_unchecked(v_val_3518_);
v___x_3523_ = lean_string_append(v___x_3521_, v___x_3522_);
lean_dec_ref(v___x_3522_);
v___x_3524_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3525_ = lean_string_append(v___x_3523_, v___x_3524_);
v___y_3500_ = v___x_3525_;
goto v___jp_3499_;
}
}
v___jp_3482_:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3486_ = lean_string_append(v___y_3484_, v___y_3483_);
lean_dec_ref(v___y_3483_);
v___x_3487_ = lean_string_append(v___x_3486_, v___y_3485_);
lean_dec_ref(v___y_3485_);
v___x_3488_ = lean_string_append(v___x_3481_, v___x_3487_);
lean_dec_ref(v___x_3487_);
v___y_3465_ = v___x_3488_;
goto v___jp_3464_;
}
v___jp_3489_:
{
switch(lean_obj_tag(v_port_3480_))
{
case 0:
{
lean_object* v___x_3492_; 
v___x_3492_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3483_ = v___y_3491_;
v___y_3484_ = v___y_3490_;
v___y_3485_ = v___x_3492_;
goto v___jp_3482_;
}
case 1:
{
lean_object* v___x_3493_; 
v___x_3493_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3483_ = v___y_3491_;
v___y_3484_ = v___y_3490_;
v___y_3485_ = v___x_3493_;
goto v___jp_3482_;
}
default: 
{
uint16_t v_port_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v_port_3494_ = lean_ctor_get_uint16(v_port_3480_, 0);
lean_dec_ref_known(v_port_3480_, 0);
v___x_3495_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3496_ = lean_uint16_to_nat(v_port_3494_);
v___x_3497_ = l_Nat_reprFast(v___x_3496_);
v___x_3498_ = lean_string_append(v___x_3495_, v___x_3497_);
lean_dec_ref(v___x_3497_);
v___y_3483_ = v___y_3491_;
v___y_3484_ = v___y_3490_;
v___y_3485_ = v___x_3498_;
goto v___jp_3482_;
}
}
}
v___jp_3499_:
{
switch(lean_obj_tag(v_host_3479_))
{
case 0:
{
lean_object* v_name_3501_; 
v_name_3501_ = lean_ctor_get(v_host_3479_, 0);
lean_inc_ref(v_name_3501_);
lean_dec_ref_known(v_host_3479_, 1);
v___y_3490_ = v___y_3500_;
v___y_3491_ = v_name_3501_;
goto v___jp_3489_;
}
case 1:
{
lean_object* v_ipv4_3502_; lean_object* v___x_3503_; 
v_ipv4_3502_ = lean_ctor_get(v_host_3479_, 0);
lean_inc_ref(v_ipv4_3502_);
lean_dec_ref_known(v_host_3479_, 1);
v___x_3503_ = lean_uv_ntop_v4(v_ipv4_3502_);
lean_dec_ref(v_ipv4_3502_);
v___y_3490_ = v___y_3500_;
v___y_3491_ = v___x_3503_;
goto v___jp_3489_;
}
default: 
{
lean_object* v_ipv6_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v_ipv6_3504_ = lean_ctor_get(v_host_3479_, 0);
lean_inc_ref(v_ipv6_3504_);
lean_dec_ref_known(v_host_3479_, 1);
v___x_3505_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3506_ = lean_uv_ntop_v6(v_ipv6_3504_);
lean_dec_ref(v_ipv6_3504_);
v___x_3507_ = lean_string_append(v___x_3505_, v___x_3506_);
lean_dec_ref(v___x_3506_);
v___x_3508_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3509_ = lean_string_append(v___x_3507_, v___x_3508_);
v___y_3490_ = v___y_3500_;
v___y_3491_ = v___x_3509_;
goto v___jp_3489_;
}
}
}
}
v___jp_3443_:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3448_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3449_ = lean_string_append(v_scheme_3438_, v___x_3448_);
v___x_3450_ = lean_string_append(v___x_3449_, v___y_3444_);
lean_dec_ref(v___y_3444_);
v___x_3451_ = lean_string_append(v___x_3450_, v___y_3445_);
lean_dec_ref(v___y_3445_);
v___x_3452_ = lean_string_append(v___x_3451_, v___y_3446_);
lean_dec_ref(v___y_3446_);
v___x_3453_ = lean_string_append(v___x_3452_, v___y_3447_);
lean_dec_ref(v___y_3447_);
return v___x_3453_;
}
v___jp_3454_:
{
lean_object* v_queryPart_3457_; 
v_queryPart_3457_ = l_Std_Http_URI_Query_formatOption(v_query_3441_);
if (lean_obj_tag(v_fragment_3442_) == 0)
{
lean_object* v___x_3458_; 
v___x_3458_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3444_ = v___y_3455_;
v___y_3445_ = v___y_3456_;
v___y_3446_ = v_queryPart_3457_;
v___y_3447_ = v___x_3458_;
goto v___jp_3443_;
}
else
{
lean_object* v_val_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v_val_3459_ = lean_ctor_get(v_fragment_3442_, 0);
lean_inc(v_val_3459_);
lean_dec_ref_known(v_fragment_3442_, 1);
v___x_3460_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3461_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3459_);
v___x_3462_ = lean_string_from_utf8_unchecked(v___x_3461_);
v___x_3463_ = lean_string_append(v___x_3460_, v___x_3462_);
lean_dec_ref(v___x_3462_);
v___y_3444_ = v___y_3455_;
v___y_3445_ = v___y_3456_;
v___y_3446_ = v_queryPart_3457_;
v___y_3447_ = v___x_3463_;
goto v___jp_3443_;
}
}
v___jp_3464_:
{
lean_object* v_segments_3466_; uint8_t v_absolute_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; size_t v_sz_3470_; size_t v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v_result_3474_; 
v_segments_3466_ = lean_ctor_get(v_path_3440_, 0);
lean_inc_ref(v_segments_3466_);
v_absolute_3467_ = lean_ctor_get_uint8(v_path_3440_, sizeof(void*)*1);
lean_dec_ref(v_path_3440_);
v___x_3468_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3469_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3470_ = lean_array_size(v_segments_3466_);
v___x_3471_ = ((size_t)0ULL);
v___x_3472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3469_, v___f_3426_, v_sz_3470_, v___x_3471_, v_segments_3466_);
v___x_3473_ = lean_array_to_list(v___x_3472_);
v_result_3474_ = l_String_intercalate(v___x_3468_, v___x_3473_);
if (v_absolute_3467_ == 0)
{
v___y_3455_ = v___y_3465_;
v___y_3456_ = v_result_3474_;
goto v___jp_3454_;
}
else
{
lean_object* v___x_3475_; 
v___x_3475_ = lean_string_append(v___x_3468_, v_result_3474_);
lean_dec_ref(v_result_3474_);
v___y_3455_ = v___y_3465_;
v___y_3456_ = v___x_3475_;
goto v___jp_3454_;
}
}
}
else
{
lean_object* v_ref_3526_; lean_object* v_authority_3527_; lean_object* v_path_3528_; lean_object* v_query_3529_; lean_object* v_fragment_3530_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3542_; 
lean_dec_ref(v___f_3426_);
v_ref_3526_ = lean_ctor_get(v_x_3428_, 0);
lean_inc_ref(v_ref_3526_);
lean_dec_ref_known(v_x_3428_, 1);
v_authority_3527_ = lean_ctor_get(v_ref_3526_, 0);
lean_inc(v_authority_3527_);
v_path_3528_ = lean_ctor_get(v_ref_3526_, 1);
lean_inc_ref(v_path_3528_);
v_query_3529_ = lean_ctor_get(v_ref_3526_, 2);
lean_inc(v_query_3529_);
v_fragment_3530_ = lean_ctor_get(v_ref_3526_, 3);
lean_inc(v_fragment_3530_);
lean_dec_ref(v_ref_3526_);
if (lean_obj_tag(v_authority_3527_) == 0)
{
lean_object* v___x_3553_; 
v___x_3553_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3542_ = v___x_3553_;
goto v___jp_3541_;
}
else
{
lean_object* v_val_3554_; lean_object* v_userInfo_3555_; lean_object* v_host_3556_; lean_object* v_port_3557_; lean_object* v___x_3558_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3577_; 
v_val_3554_ = lean_ctor_get(v_authority_3527_, 0);
lean_inc(v_val_3554_);
lean_dec_ref_known(v_authority_3527_, 1);
v_userInfo_3555_ = lean_ctor_get(v_val_3554_, 0);
lean_inc(v_userInfo_3555_);
v_host_3556_ = lean_ctor_get(v_val_3554_, 1);
lean_inc_ref(v_host_3556_);
v_port_3557_ = lean_ctor_get(v_val_3554_, 2);
lean_inc(v_port_3557_);
lean_dec(v_val_3554_);
v___x_3558_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3555_) == 0)
{
lean_object* v___x_3587_; 
v___x_3587_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3577_ = v___x_3587_;
goto v___jp_3576_;
}
else
{
lean_object* v_val_3588_; lean_object* v_password_3589_; 
v_val_3588_ = lean_ctor_get(v_userInfo_3555_, 0);
lean_inc(v_val_3588_);
lean_dec_ref_known(v_userInfo_3555_, 1);
v_password_3589_ = lean_ctor_get(v_val_3588_, 1);
if (lean_obj_tag(v_password_3589_) == 0)
{
lean_object* v_username_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v_username_3590_ = lean_ctor_get(v_val_3588_, 0);
lean_inc_ref(v_username_3590_);
lean_dec(v_val_3588_);
v___x_3591_ = lean_string_from_utf8_unchecked(v_username_3590_);
v___x_3592_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3593_ = lean_string_append(v___x_3591_, v___x_3592_);
v___y_3577_ = v___x_3593_;
goto v___jp_3576_;
}
else
{
lean_object* v_username_3594_; lean_object* v_val_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
lean_inc_ref(v_password_3589_);
v_username_3594_ = lean_ctor_get(v_val_3588_, 0);
lean_inc_ref(v_username_3594_);
lean_dec(v_val_3588_);
v_val_3595_ = lean_ctor_get(v_password_3589_, 0);
lean_inc(v_val_3595_);
lean_dec_ref_known(v_password_3589_, 1);
v___x_3596_ = lean_string_from_utf8_unchecked(v_username_3594_);
v___x_3597_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3598_ = lean_string_append(v___x_3596_, v___x_3597_);
v___x_3599_ = lean_string_from_utf8_unchecked(v_val_3595_);
v___x_3600_ = lean_string_append(v___x_3598_, v___x_3599_);
lean_dec_ref(v___x_3599_);
v___x_3601_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3602_ = lean_string_append(v___x_3600_, v___x_3601_);
v___y_3577_ = v___x_3602_;
goto v___jp_3576_;
}
}
v___jp_3559_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3563_ = lean_string_append(v___y_3561_, v___y_3560_);
lean_dec_ref(v___y_3560_);
v___x_3564_ = lean_string_append(v___x_3563_, v___y_3562_);
lean_dec_ref(v___y_3562_);
v___x_3565_ = lean_string_append(v___x_3558_, v___x_3564_);
lean_dec_ref(v___x_3564_);
v___y_3542_ = v___x_3565_;
goto v___jp_3541_;
}
v___jp_3566_:
{
switch(lean_obj_tag(v_port_3557_))
{
case 0:
{
lean_object* v___x_3569_; 
v___x_3569_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3560_ = v___y_3568_;
v___y_3561_ = v___y_3567_;
v___y_3562_ = v___x_3569_;
goto v___jp_3559_;
}
case 1:
{
lean_object* v___x_3570_; 
v___x_3570_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3560_ = v___y_3568_;
v___y_3561_ = v___y_3567_;
v___y_3562_ = v___x_3570_;
goto v___jp_3559_;
}
default: 
{
uint16_t v_port_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v_port_3571_ = lean_ctor_get_uint16(v_port_3557_, 0);
lean_dec_ref_known(v_port_3557_, 0);
v___x_3572_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3573_ = lean_uint16_to_nat(v_port_3571_);
v___x_3574_ = l_Nat_reprFast(v___x_3573_);
v___x_3575_ = lean_string_append(v___x_3572_, v___x_3574_);
lean_dec_ref(v___x_3574_);
v___y_3560_ = v___y_3568_;
v___y_3561_ = v___y_3567_;
v___y_3562_ = v___x_3575_;
goto v___jp_3559_;
}
}
}
v___jp_3576_:
{
switch(lean_obj_tag(v_host_3556_))
{
case 0:
{
lean_object* v_name_3578_; 
v_name_3578_ = lean_ctor_get(v_host_3556_, 0);
lean_inc_ref(v_name_3578_);
lean_dec_ref_known(v_host_3556_, 1);
v___y_3567_ = v___y_3577_;
v___y_3568_ = v_name_3578_;
goto v___jp_3566_;
}
case 1:
{
lean_object* v_ipv4_3579_; lean_object* v___x_3580_; 
v_ipv4_3579_ = lean_ctor_get(v_host_3556_, 0);
lean_inc_ref(v_ipv4_3579_);
lean_dec_ref_known(v_host_3556_, 1);
v___x_3580_ = lean_uv_ntop_v4(v_ipv4_3579_);
lean_dec_ref(v_ipv4_3579_);
v___y_3567_ = v___y_3577_;
v___y_3568_ = v___x_3580_;
goto v___jp_3566_;
}
default: 
{
lean_object* v_ipv6_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v_ipv6_3581_ = lean_ctor_get(v_host_3556_, 0);
lean_inc_ref(v_ipv6_3581_);
lean_dec_ref_known(v_host_3556_, 1);
v___x_3582_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3583_ = lean_uv_ntop_v6(v_ipv6_3581_);
lean_dec_ref(v_ipv6_3581_);
v___x_3584_ = lean_string_append(v___x_3582_, v___x_3583_);
lean_dec_ref(v___x_3583_);
v___x_3585_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3586_ = lean_string_append(v___x_3584_, v___x_3585_);
v___y_3567_ = v___y_3577_;
v___y_3568_ = v___x_3586_;
goto v___jp_3566_;
}
}
}
}
v___jp_3531_:
{
lean_object* v_queryPart_3534_; 
v_queryPart_3534_ = l_Std_Http_URI_Query_formatOption(v_query_3529_);
if (lean_obj_tag(v_fragment_3530_) == 0)
{
lean_object* v___x_3535_; 
v___x_3535_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3430_ = v___y_3532_;
v___y_3431_ = v___y_3533_;
v___y_3432_ = v_queryPart_3534_;
v___y_3433_ = v___x_3535_;
goto v___jp_3429_;
}
else
{
lean_object* v_val_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v_val_3536_ = lean_ctor_get(v_fragment_3530_, 0);
lean_inc(v_val_3536_);
lean_dec_ref_known(v_fragment_3530_, 1);
v___x_3537_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3538_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3536_);
v___x_3539_ = lean_string_from_utf8_unchecked(v___x_3538_);
v___x_3540_ = lean_string_append(v___x_3537_, v___x_3539_);
lean_dec_ref(v___x_3539_);
v___y_3430_ = v___y_3532_;
v___y_3431_ = v___y_3533_;
v___y_3432_ = v_queryPart_3534_;
v___y_3433_ = v___x_3540_;
goto v___jp_3429_;
}
}
v___jp_3541_:
{
lean_object* v_segments_3543_; uint8_t v_absolute_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; size_t v_sz_3547_; size_t v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v_result_3551_; 
v_segments_3543_ = lean_ctor_get(v_path_3528_, 0);
lean_inc_ref(v_segments_3543_);
v_absolute_3544_ = lean_ctor_get_uint8(v_path_3528_, sizeof(void*)*1);
lean_dec_ref(v_path_3528_);
v___x_3545_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3546_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3547_ = lean_array_size(v_segments_3543_);
v___x_3548_ = ((size_t)0ULL);
v___x_3549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3546_, v___f_3427_, v_sz_3547_, v___x_3548_, v_segments_3543_);
v___x_3550_ = lean_array_to_list(v___x_3549_);
v_result_3551_ = l_String_intercalate(v___x_3545_, v___x_3550_);
if (v_absolute_3544_ == 0)
{
v___y_3532_ = v___y_3542_;
v___y_3533_ = v_result_3551_;
goto v___jp_3531_;
}
else
{
lean_object* v___x_3552_; 
v___x_3552_ = lean_string_append(v___x_3545_, v_result_3551_);
lean_dec_ref(v_result_3551_);
v___y_3532_ = v___y_3542_;
v___y_3533_ = v___x_3552_;
goto v___jp_3531_;
}
}
}
v___jp_3429_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3434_ = lean_string_append(v___y_3430_, v___y_3431_);
lean_dec_ref(v___y_3431_);
v___x_3435_ = lean_string_append(v___x_3434_, v___y_3432_);
lean_dec_ref(v___y_3432_);
v___x_3436_ = lean_string_append(v___x_3435_, v___y_3433_);
lean_dec_ref(v___y_3433_);
return v___x_3436_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___impl(lean_object* v_x_3606_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = lean_obj_tag_nat(v_x_3606_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___impl___boxed(lean_object* v_x_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Std_Http_RequestTarget_ctorIdx___impl(v_x_3608_);
lean_dec(v_x_3608_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___redArg(lean_object* v_t_3610_, lean_object* v_k_3611_){
_start:
{
switch(lean_obj_tag(v_t_3610_))
{
case 0:
{
lean_object* v_path_3612_; lean_object* v_query_3613_; lean_object* v___x_3614_; 
v_path_3612_ = lean_ctor_get(v_t_3610_, 0);
lean_inc_ref(v_path_3612_);
v_query_3613_ = lean_ctor_get(v_t_3610_, 1);
lean_inc(v_query_3613_);
lean_dec_ref_known(v_t_3610_, 2);
v___x_3614_ = lean_apply_2(v_k_3611_, v_path_3612_, v_query_3613_);
return v___x_3614_;
}
case 3:
{
return v_k_3611_;
}
default: 
{
lean_object* v_uri_3615_; lean_object* v___x_3616_; 
v_uri_3615_ = lean_ctor_get(v_t_3610_, 0);
lean_inc_ref(v_uri_3615_);
lean_dec(v_t_3610_);
v___x_3616_ = lean_apply_1(v_k_3611_, v_uri_3615_);
return v___x_3616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim(lean_object* v_motive_3617_, lean_object* v_ctorIdx_3618_, lean_object* v_t_3619_, lean_object* v_h_3620_, lean_object* v_k_3621_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3619_, v_k_3621_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___boxed(lean_object* v_motive_3623_, lean_object* v_ctorIdx_3624_, lean_object* v_t_3625_, lean_object* v_h_3626_, lean_object* v_k_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Std_Http_RequestTarget_ctorElim(v_motive_3623_, v_ctorIdx_3624_, v_t_3625_, v_h_3626_, v_k_3627_);
lean_dec(v_ctorIdx_3624_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim___redArg(lean_object* v_t_3629_, lean_object* v_originForm_3630_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3629_, v_originForm_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim(lean_object* v_motive_3632_, lean_object* v_t_3633_, lean_object* v_h_3634_, lean_object* v_originForm_3635_){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3633_, v_originForm_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim___redArg(lean_object* v_t_3637_, lean_object* v_absoluteForm_3638_){
_start:
{
lean_object* v___x_3639_; 
v___x_3639_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3637_, v_absoluteForm_3638_);
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim(lean_object* v_motive_3640_, lean_object* v_t_3641_, lean_object* v_h_3642_, lean_object* v_absoluteForm_3643_){
_start:
{
lean_object* v___x_3644_; 
v___x_3644_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3641_, v_absoluteForm_3643_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim___redArg(lean_object* v_t_3645_, lean_object* v_authorityForm_3646_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3645_, v_authorityForm_3646_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim(lean_object* v_motive_3648_, lean_object* v_t_3649_, lean_object* v_h_3650_, lean_object* v_authorityForm_3651_){
_start:
{
lean_object* v___x_3652_; 
v___x_3652_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3649_, v_authorityForm_3651_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim___redArg(lean_object* v_t_3653_, lean_object* v_asteriskForm_3654_){
_start:
{
lean_object* v___x_3655_; 
v___x_3655_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3653_, v_asteriskForm_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim(lean_object* v_motive_3656_, lean_object* v_t_3657_, lean_object* v_h_3658_, lean_object* v_asteriskForm_3659_){
_start:
{
lean_object* v___x_3660_; 
v___x_3660_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3657_, v_asteriskForm_3659_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object* v_x_3687_, lean_object* v_prec_3688_){
_start:
{
lean_object* v___y_3690_; 
switch(lean_obj_tag(v_x_3687_))
{
case 0:
{
lean_object* v_path_3696_; lean_object* v_query_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3721_; 
v_path_3696_ = lean_ctor_get(v_x_3687_, 0);
v_query_3697_ = lean_ctor_get(v_x_3687_, 1);
v_isSharedCheck_3721_ = !lean_is_exclusive(v_x_3687_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3699_ = v_x_3687_;
v_isShared_3700_ = v_isSharedCheck_3721_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_query_3697_);
lean_inc(v_path_3696_);
lean_dec(v_x_3687_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3721_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___y_3702_; lean_object* v___x_3717_; uint8_t v___x_3718_; 
v___x_3717_ = lean_unsigned_to_nat(1024u);
v___x_3718_ = lean_nat_dec_le(v___x_3717_, v_prec_3688_);
if (v___x_3718_ == 0)
{
lean_object* v___x_3719_; 
v___x_3719_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3702_ = v___x_3719_;
goto v___jp_3701_;
}
else
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3702_ = v___x_3720_;
goto v___jp_3701_;
}
v___jp_3701_:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3708_; 
v___x_3703_ = lean_box(1);
v___x_3704_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__4));
v___x_3705_ = lean_unsigned_to_nat(1024u);
v___x_3706_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3696_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set_tag(v___x_3699_, 5);
lean_ctor_set(v___x_3699_, 1, v___x_3706_);
lean_ctor_set(v___x_3699_, 0, v___x_3704_);
v___x_3708_ = v___x_3699_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3716_, 1, v___x_3706_);
v___x_3708_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; uint8_t v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3708_);
lean_ctor_set(v___x_3709_, 1, v___x_3703_);
v___x_3710_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3697_, v___x_3705_);
v___x_3711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3709_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
lean_inc(v___y_3702_);
v___x_3712_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___y_3702_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v___x_3713_ = 0;
v___x_3714_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set_uint8(v___x_3714_, sizeof(void*)*1, v___x_3713_);
v___x_3715_ = l_Repr_addAppParen(v___x_3714_, v_prec_3688_);
return v___x_3715_;
}
}
}
}
case 1:
{
lean_object* v_uri_3722_; lean_object* v___y_3724_; lean_object* v___x_3732_; uint8_t v___x_3733_; 
v_uri_3722_ = lean_ctor_get(v_x_3687_, 0);
lean_inc_ref(v_uri_3722_);
lean_dec_ref_known(v_x_3687_, 1);
v___x_3732_ = lean_unsigned_to_nat(1024u);
v___x_3733_ = lean_nat_dec_le(v___x_3732_, v_prec_3688_);
if (v___x_3733_ == 0)
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3724_ = v___x_3734_;
goto v___jp_3723_;
}
else
{
lean_object* v___x_3735_; 
v___x_3735_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3724_ = v___x_3735_;
goto v___jp_3723_;
}
v___jp_3723_:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3725_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__7));
v___x_3726_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3722_);
v___x_3727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3725_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
lean_inc(v___y_3724_);
v___x_3728_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___y_3724_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = 0;
v___x_3730_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3730_, 0, v___x_3728_);
lean_ctor_set_uint8(v___x_3730_, sizeof(void*)*1, v___x_3729_);
v___x_3731_ = l_Repr_addAppParen(v___x_3730_, v_prec_3688_);
return v___x_3731_;
}
}
case 2:
{
lean_object* v_authority_3736_; lean_object* v___y_3738_; lean_object* v___x_3746_; uint8_t v___x_3747_; 
v_authority_3736_ = lean_ctor_get(v_x_3687_, 0);
lean_inc_ref(v_authority_3736_);
lean_dec_ref_known(v_x_3687_, 1);
v___x_3746_ = lean_unsigned_to_nat(1024u);
v___x_3747_ = lean_nat_dec_le(v___x_3746_, v_prec_3688_);
if (v___x_3747_ == 0)
{
lean_object* v___x_3748_; 
v___x_3748_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3738_ = v___x_3748_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3749_; 
v___x_3749_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3738_ = v___x_3749_;
goto v___jp_3737_;
}
v___jp_3737_:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; uint8_t v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3739_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__10));
v___x_3740_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_authority_3736_);
v___x_3741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3739_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
lean_inc(v___y_3738_);
v___x_3742_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___y_3738_);
lean_ctor_set(v___x_3742_, 1, v___x_3741_);
v___x_3743_ = 0;
v___x_3744_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3744_, 0, v___x_3742_);
lean_ctor_set_uint8(v___x_3744_, sizeof(void*)*1, v___x_3743_);
v___x_3745_ = l_Repr_addAppParen(v___x_3744_, v_prec_3688_);
return v___x_3745_;
}
}
default: 
{
lean_object* v___x_3750_; uint8_t v___x_3751_; 
v___x_3750_ = lean_unsigned_to_nat(1024u);
v___x_3751_ = lean_nat_dec_le(v___x_3750_, v_prec_3688_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; 
v___x_3752_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3690_ = v___x_3752_;
goto v___jp_3689_;
}
else
{
lean_object* v___x_3753_; 
v___x_3753_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3690_ = v___x_3753_;
goto v___jp_3689_;
}
}
}
v___jp_3689_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; uint8_t v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3691_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__1));
lean_inc(v___y_3690_);
v___x_3692_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___y_3690_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = 0;
v___x_3694_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set_uint8(v___x_3694_, sizeof(void*)*1, v___x_3693_);
v___x_3695_ = l_Repr_addAppParen(v___x_3694_, v_prec_3688_);
return v___x_3695_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr___boxed(lean_object* v_x_3754_, lean_object* v_prec_3755_){
_start:
{
lean_object* v_res_3756_; 
v_res_3756_ = l_Std_Http_instReprRequestTarget_repr(v_x_3754_, v_prec_3755_);
lean_dec(v_prec_3755_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path(lean_object* v_x_3764_){
_start:
{
switch(lean_obj_tag(v_x_3764_))
{
case 0:
{
lean_object* v_path_3765_; 
v_path_3765_ = lean_ctor_get(v_x_3764_, 0);
lean_inc_ref(v_path_3765_);
return v_path_3765_;
}
case 1:
{
lean_object* v_uri_3766_; lean_object* v_path_3767_; 
v_uri_3766_ = lean_ctor_get(v_x_3764_, 0);
v_path_3767_ = lean_ctor_get(v_uri_3766_, 2);
lean_inc_ref(v_path_3767_);
return v_path_3767_;
}
default: 
{
lean_object* v___x_3768_; 
v___x_3768_ = ((lean_object*)(l_Std_Http_RequestTarget_path___closed__1));
return v___x_3768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path___boxed(lean_object* v_x_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l_Std_Http_RequestTarget_path(v_x_3769_);
lean_dec(v_x_3769_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query(lean_object* v_x_3771_){
_start:
{
switch(lean_obj_tag(v_x_3771_))
{
case 0:
{
lean_object* v_query_3772_; 
v_query_3772_ = lean_ctor_get(v_x_3771_, 1);
if (lean_obj_tag(v_query_3772_) == 0)
{
lean_object* v___x_3773_; 
v___x_3773_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3773_;
}
else
{
lean_object* v_val_3774_; 
v_val_3774_ = lean_ctor_get(v_query_3772_, 0);
lean_inc(v_val_3774_);
return v_val_3774_;
}
}
case 1:
{
lean_object* v_uri_3775_; lean_object* v_query_3776_; 
v_uri_3775_ = lean_ctor_get(v_x_3771_, 0);
v_query_3776_ = lean_ctor_get(v_uri_3775_, 3);
if (lean_obj_tag(v_query_3776_) == 0)
{
lean_object* v___x_3777_; 
v___x_3777_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3777_;
}
else
{
lean_object* v_val_3778_; 
v_val_3778_ = lean_ctor_get(v_query_3776_, 0);
lean_inc(v_val_3778_);
return v_val_3778_;
}
}
default: 
{
lean_object* v___x_3779_; 
v___x_3779_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query___boxed(lean_object* v_x_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l_Std_Http_RequestTarget_query(v_x_3780_);
lean_dec(v_x_3780_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authority_x3f(lean_object* v_x_3782_){
_start:
{
switch(lean_obj_tag(v_x_3782_))
{
case 2:
{
lean_object* v_authority_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
v_authority_3783_ = lean_ctor_get(v_x_3782_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v_x_3782_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v_x_3782_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_authority_3783_);
lean_dec(v_x_3782_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
lean_ctor_set_tag(v___x_3785_, 1);
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_authority_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
case 1:
{
lean_object* v_uri_3791_; lean_object* v_authority_3792_; 
v_uri_3791_ = lean_ctor_get(v_x_3782_, 0);
lean_inc_ref(v_uri_3791_);
lean_dec_ref_known(v_x_3782_, 1);
v_authority_3792_ = lean_ctor_get(v_uri_3791_, 1);
lean_inc(v_authority_3792_);
lean_dec_ref(v_uri_3791_);
return v_authority_3792_;
}
default: 
{
lean_object* v___x_3793_; 
lean_dec(v_x_3782_);
v___x_3793_ = lean_box(0);
return v___x_3793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__2(lean_object* v___f_3795_, lean_object* v___f_3796_, lean_object* v_x_3797_){
_start:
{
lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; 
switch(lean_obj_tag(v_x_3797_))
{
case 0:
{
lean_object* v_path_3804_; lean_object* v_query_3805_; lean_object* v___y_3807_; lean_object* v_segments_3810_; uint8_t v_absolute_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; size_t v_sz_3814_; size_t v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v_result_3818_; 
lean_dec_ref(v___f_3796_);
v_path_3804_ = lean_ctor_get(v_x_3797_, 0);
lean_inc_ref(v_path_3804_);
v_query_3805_ = lean_ctor_get(v_x_3797_, 1);
lean_inc(v_query_3805_);
lean_dec_ref_known(v_x_3797_, 2);
v_segments_3810_ = lean_ctor_get(v_path_3804_, 0);
lean_inc_ref(v_segments_3810_);
v_absolute_3811_ = lean_ctor_get_uint8(v_path_3804_, sizeof(void*)*1);
lean_dec_ref(v_path_3804_);
v___x_3812_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3813_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3814_ = lean_array_size(v_segments_3810_);
v___x_3815_ = ((size_t)0ULL);
v___x_3816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3813_, v___f_3795_, v_sz_3814_, v___x_3815_, v_segments_3810_);
v___x_3817_ = lean_array_to_list(v___x_3816_);
v_result_3818_ = l_String_intercalate(v___x_3812_, v___x_3817_);
if (v_absolute_3811_ == 0)
{
v___y_3807_ = v_result_3818_;
goto v___jp_3806_;
}
else
{
lean_object* v___x_3819_; 
v___x_3819_ = lean_string_append(v___x_3812_, v_result_3818_);
lean_dec_ref(v_result_3818_);
v___y_3807_ = v___x_3819_;
goto v___jp_3806_;
}
v___jp_3806_:
{
lean_object* v_queryStr_3808_; lean_object* v___x_3809_; 
v_queryStr_3808_ = l_Std_Http_URI_Query_formatOption(v_query_3805_);
v___x_3809_ = lean_string_append(v___y_3807_, v_queryStr_3808_);
lean_dec_ref(v_queryStr_3808_);
return v___x_3809_;
}
}
case 1:
{
lean_object* v_uri_3820_; lean_object* v_scheme_3821_; lean_object* v_authority_3822_; lean_object* v_path_3823_; lean_object* v_query_3824_; lean_object* v_fragment_3825_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3848_; 
lean_dec_ref(v___f_3795_);
v_uri_3820_ = lean_ctor_get(v_x_3797_, 0);
lean_inc_ref(v_uri_3820_);
lean_dec_ref_known(v_x_3797_, 1);
v_scheme_3821_ = lean_ctor_get(v_uri_3820_, 0);
lean_inc_ref(v_scheme_3821_);
v_authority_3822_ = lean_ctor_get(v_uri_3820_, 1);
lean_inc(v_authority_3822_);
v_path_3823_ = lean_ctor_get(v_uri_3820_, 2);
lean_inc_ref(v_path_3823_);
v_query_3824_ = lean_ctor_get(v_uri_3820_, 3);
lean_inc(v_query_3824_);
v_fragment_3825_ = lean_ctor_get(v_uri_3820_, 4);
lean_inc(v_fragment_3825_);
lean_dec_ref(v_uri_3820_);
if (lean_obj_tag(v_authority_3822_) == 0)
{
lean_object* v___x_3859_; 
v___x_3859_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3848_ = v___x_3859_;
goto v___jp_3847_;
}
else
{
lean_object* v_val_3860_; lean_object* v_userInfo_3861_; lean_object* v_host_3862_; lean_object* v_port_3863_; lean_object* v___x_3864_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3883_; 
v_val_3860_ = lean_ctor_get(v_authority_3822_, 0);
lean_inc(v_val_3860_);
lean_dec_ref_known(v_authority_3822_, 1);
v_userInfo_3861_ = lean_ctor_get(v_val_3860_, 0);
lean_inc(v_userInfo_3861_);
v_host_3862_ = lean_ctor_get(v_val_3860_, 1);
lean_inc_ref(v_host_3862_);
v_port_3863_ = lean_ctor_get(v_val_3860_, 2);
lean_inc(v_port_3863_);
lean_dec(v_val_3860_);
v___x_3864_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3861_) == 0)
{
lean_object* v___x_3893_; 
v___x_3893_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3883_ = v___x_3893_;
goto v___jp_3882_;
}
else
{
lean_object* v_val_3894_; lean_object* v_password_3895_; 
v_val_3894_ = lean_ctor_get(v_userInfo_3861_, 0);
lean_inc(v_val_3894_);
lean_dec_ref_known(v_userInfo_3861_, 1);
v_password_3895_ = lean_ctor_get(v_val_3894_, 1);
if (lean_obj_tag(v_password_3895_) == 0)
{
lean_object* v_username_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v_username_3896_ = lean_ctor_get(v_val_3894_, 0);
lean_inc_ref(v_username_3896_);
lean_dec(v_val_3894_);
v___x_3897_ = lean_string_from_utf8_unchecked(v_username_3896_);
v___x_3898_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3899_ = lean_string_append(v___x_3897_, v___x_3898_);
v___y_3883_ = v___x_3899_;
goto v___jp_3882_;
}
else
{
lean_object* v_username_3900_; lean_object* v_val_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
lean_inc_ref(v_password_3895_);
v_username_3900_ = lean_ctor_get(v_val_3894_, 0);
lean_inc_ref(v_username_3900_);
lean_dec(v_val_3894_);
v_val_3901_ = lean_ctor_get(v_password_3895_, 0);
lean_inc(v_val_3901_);
lean_dec_ref_known(v_password_3895_, 1);
v___x_3902_ = lean_string_from_utf8_unchecked(v_username_3900_);
v___x_3903_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3904_ = lean_string_append(v___x_3902_, v___x_3903_);
v___x_3905_ = lean_string_from_utf8_unchecked(v_val_3901_);
v___x_3906_ = lean_string_append(v___x_3904_, v___x_3905_);
lean_dec_ref(v___x_3905_);
v___x_3907_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3908_ = lean_string_append(v___x_3906_, v___x_3907_);
v___y_3883_ = v___x_3908_;
goto v___jp_3882_;
}
}
v___jp_3865_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3869_ = lean_string_append(v___y_3867_, v___y_3866_);
lean_dec_ref(v___y_3866_);
v___x_3870_ = lean_string_append(v___x_3869_, v___y_3868_);
lean_dec_ref(v___y_3868_);
v___x_3871_ = lean_string_append(v___x_3864_, v___x_3870_);
lean_dec_ref(v___x_3870_);
v___y_3848_ = v___x_3871_;
goto v___jp_3847_;
}
v___jp_3872_:
{
switch(lean_obj_tag(v_port_3863_))
{
case 0:
{
lean_object* v___x_3875_; 
v___x_3875_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3866_ = v___y_3874_;
v___y_3867_ = v___y_3873_;
v___y_3868_ = v___x_3875_;
goto v___jp_3865_;
}
case 1:
{
lean_object* v___x_3876_; 
v___x_3876_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3866_ = v___y_3874_;
v___y_3867_ = v___y_3873_;
v___y_3868_ = v___x_3876_;
goto v___jp_3865_;
}
default: 
{
uint16_t v_port_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v_port_3877_ = lean_ctor_get_uint16(v_port_3863_, 0);
lean_dec_ref_known(v_port_3863_, 0);
v___x_3878_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3879_ = lean_uint16_to_nat(v_port_3877_);
v___x_3880_ = l_Nat_reprFast(v___x_3879_);
v___x_3881_ = lean_string_append(v___x_3878_, v___x_3880_);
lean_dec_ref(v___x_3880_);
v___y_3866_ = v___y_3874_;
v___y_3867_ = v___y_3873_;
v___y_3868_ = v___x_3881_;
goto v___jp_3865_;
}
}
}
v___jp_3882_:
{
switch(lean_obj_tag(v_host_3862_))
{
case 0:
{
lean_object* v_name_3884_; 
v_name_3884_ = lean_ctor_get(v_host_3862_, 0);
lean_inc_ref(v_name_3884_);
lean_dec_ref_known(v_host_3862_, 1);
v___y_3873_ = v___y_3883_;
v___y_3874_ = v_name_3884_;
goto v___jp_3872_;
}
case 1:
{
lean_object* v_ipv4_3885_; lean_object* v___x_3886_; 
v_ipv4_3885_ = lean_ctor_get(v_host_3862_, 0);
lean_inc_ref(v_ipv4_3885_);
lean_dec_ref_known(v_host_3862_, 1);
v___x_3886_ = lean_uv_ntop_v4(v_ipv4_3885_);
lean_dec_ref(v_ipv4_3885_);
v___y_3873_ = v___y_3883_;
v___y_3874_ = v___x_3886_;
goto v___jp_3872_;
}
default: 
{
lean_object* v_ipv6_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v_ipv6_3887_ = lean_ctor_get(v_host_3862_, 0);
lean_inc_ref(v_ipv6_3887_);
lean_dec_ref_known(v_host_3862_, 1);
v___x_3888_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3889_ = lean_uv_ntop_v6(v_ipv6_3887_);
lean_dec_ref(v_ipv6_3887_);
v___x_3890_ = lean_string_append(v___x_3888_, v___x_3889_);
lean_dec_ref(v___x_3889_);
v___x_3891_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3892_ = lean_string_append(v___x_3890_, v___x_3891_);
v___y_3873_ = v___y_3883_;
v___y_3874_ = v___x_3892_;
goto v___jp_3872_;
}
}
}
}
v___jp_3826_:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3831_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3832_ = lean_string_append(v_scheme_3821_, v___x_3831_);
v___x_3833_ = lean_string_append(v___x_3832_, v___y_3829_);
lean_dec_ref(v___y_3829_);
v___x_3834_ = lean_string_append(v___x_3833_, v___y_3827_);
lean_dec_ref(v___y_3827_);
v___x_3835_ = lean_string_append(v___x_3834_, v___y_3828_);
lean_dec_ref(v___y_3828_);
v___x_3836_ = lean_string_append(v___x_3835_, v___y_3830_);
lean_dec_ref(v___y_3830_);
return v___x_3836_;
}
v___jp_3837_:
{
lean_object* v_queryPart_3840_; 
v_queryPart_3840_ = l_Std_Http_URI_Query_formatOption(v_query_3824_);
if (lean_obj_tag(v_fragment_3825_) == 0)
{
lean_object* v___x_3841_; 
v___x_3841_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3827_ = v___y_3839_;
v___y_3828_ = v_queryPart_3840_;
v___y_3829_ = v___y_3838_;
v___y_3830_ = v___x_3841_;
goto v___jp_3826_;
}
else
{
lean_object* v_val_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v_val_3842_ = lean_ctor_get(v_fragment_3825_, 0);
lean_inc(v_val_3842_);
lean_dec_ref_known(v_fragment_3825_, 1);
v___x_3843_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3844_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3842_);
v___x_3845_ = lean_string_from_utf8_unchecked(v___x_3844_);
v___x_3846_ = lean_string_append(v___x_3843_, v___x_3845_);
lean_dec_ref(v___x_3845_);
v___y_3827_ = v___y_3839_;
v___y_3828_ = v_queryPart_3840_;
v___y_3829_ = v___y_3838_;
v___y_3830_ = v___x_3846_;
goto v___jp_3826_;
}
}
v___jp_3847_:
{
lean_object* v_segments_3849_; uint8_t v_absolute_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; size_t v_sz_3853_; size_t v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v_result_3857_; 
v_segments_3849_ = lean_ctor_get(v_path_3823_, 0);
lean_inc_ref(v_segments_3849_);
v_absolute_3850_ = lean_ctor_get_uint8(v_path_3823_, sizeof(void*)*1);
lean_dec_ref(v_path_3823_);
v___x_3851_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3852_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3853_ = lean_array_size(v_segments_3849_);
v___x_3854_ = ((size_t)0ULL);
v___x_3855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3852_, v___f_3796_, v_sz_3853_, v___x_3854_, v_segments_3849_);
v___x_3856_ = lean_array_to_list(v___x_3855_);
v_result_3857_ = l_String_intercalate(v___x_3851_, v___x_3856_);
if (v_absolute_3850_ == 0)
{
v___y_3838_ = v___y_3848_;
v___y_3839_ = v_result_3857_;
goto v___jp_3837_;
}
else
{
lean_object* v___x_3858_; 
v___x_3858_ = lean_string_append(v___x_3851_, v_result_3857_);
lean_dec_ref(v_result_3857_);
v___y_3838_ = v___y_3848_;
v___y_3839_ = v___x_3858_;
goto v___jp_3837_;
}
}
}
case 2:
{
lean_object* v_authority_3909_; lean_object* v_userInfo_3910_; lean_object* v_host_3911_; lean_object* v_port_3912_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3924_; 
lean_dec_ref(v___f_3796_);
lean_dec_ref(v___f_3795_);
v_authority_3909_ = lean_ctor_get(v_x_3797_, 0);
lean_inc_ref(v_authority_3909_);
lean_dec_ref_known(v_x_3797_, 1);
v_userInfo_3910_ = lean_ctor_get(v_authority_3909_, 0);
lean_inc(v_userInfo_3910_);
v_host_3911_ = lean_ctor_get(v_authority_3909_, 1);
lean_inc_ref(v_host_3911_);
v_port_3912_ = lean_ctor_get(v_authority_3909_, 2);
lean_inc(v_port_3912_);
lean_dec_ref(v_authority_3909_);
if (lean_obj_tag(v_userInfo_3910_) == 0)
{
lean_object* v___x_3934_; 
v___x_3934_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3924_ = v___x_3934_;
goto v___jp_3923_;
}
else
{
lean_object* v_val_3935_; lean_object* v_password_3936_; 
v_val_3935_ = lean_ctor_get(v_userInfo_3910_, 0);
lean_inc(v_val_3935_);
lean_dec_ref_known(v_userInfo_3910_, 1);
v_password_3936_ = lean_ctor_get(v_val_3935_, 1);
if (lean_obj_tag(v_password_3936_) == 0)
{
lean_object* v_username_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v_username_3937_ = lean_ctor_get(v_val_3935_, 0);
lean_inc_ref(v_username_3937_);
lean_dec(v_val_3935_);
v___x_3938_ = lean_string_from_utf8_unchecked(v_username_3937_);
v___x_3939_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3940_ = lean_string_append(v___x_3938_, v___x_3939_);
v___y_3924_ = v___x_3940_;
goto v___jp_3923_;
}
else
{
lean_object* v_username_3941_; lean_object* v_val_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
lean_inc_ref(v_password_3936_);
v_username_3941_ = lean_ctor_get(v_val_3935_, 0);
lean_inc_ref(v_username_3941_);
lean_dec(v_val_3935_);
v_val_3942_ = lean_ctor_get(v_password_3936_, 0);
lean_inc(v_val_3942_);
lean_dec_ref_known(v_password_3936_, 1);
v___x_3943_ = lean_string_from_utf8_unchecked(v_username_3941_);
v___x_3944_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3945_ = lean_string_append(v___x_3943_, v___x_3944_);
v___x_3946_ = lean_string_from_utf8_unchecked(v_val_3942_);
v___x_3947_ = lean_string_append(v___x_3945_, v___x_3946_);
lean_dec_ref(v___x_3946_);
v___x_3948_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3949_ = lean_string_append(v___x_3947_, v___x_3948_);
v___y_3924_ = v___x_3949_;
goto v___jp_3923_;
}
}
v___jp_3913_:
{
switch(lean_obj_tag(v_port_3912_))
{
case 0:
{
lean_object* v___x_3916_; 
v___x_3916_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3799_ = v___y_3915_;
v___y_3800_ = v___y_3914_;
v___y_3801_ = v___x_3916_;
goto v___jp_3798_;
}
case 1:
{
lean_object* v___x_3917_; 
v___x_3917_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3799_ = v___y_3915_;
v___y_3800_ = v___y_3914_;
v___y_3801_ = v___x_3917_;
goto v___jp_3798_;
}
default: 
{
uint16_t v_port_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v_port_3918_ = lean_ctor_get_uint16(v_port_3912_, 0);
lean_dec_ref_known(v_port_3912_, 0);
v___x_3919_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3920_ = lean_uint16_to_nat(v_port_3918_);
v___x_3921_ = l_Nat_reprFast(v___x_3920_);
v___x_3922_ = lean_string_append(v___x_3919_, v___x_3921_);
lean_dec_ref(v___x_3921_);
v___y_3799_ = v___y_3915_;
v___y_3800_ = v___y_3914_;
v___y_3801_ = v___x_3922_;
goto v___jp_3798_;
}
}
}
v___jp_3923_:
{
switch(lean_obj_tag(v_host_3911_))
{
case 0:
{
lean_object* v_name_3925_; 
v_name_3925_ = lean_ctor_get(v_host_3911_, 0);
lean_inc_ref(v_name_3925_);
lean_dec_ref_known(v_host_3911_, 1);
v___y_3914_ = v___y_3924_;
v___y_3915_ = v_name_3925_;
goto v___jp_3913_;
}
case 1:
{
lean_object* v_ipv4_3926_; lean_object* v___x_3927_; 
v_ipv4_3926_ = lean_ctor_get(v_host_3911_, 0);
lean_inc_ref(v_ipv4_3926_);
lean_dec_ref_known(v_host_3911_, 1);
v___x_3927_ = lean_uv_ntop_v4(v_ipv4_3926_);
lean_dec_ref(v_ipv4_3926_);
v___y_3914_ = v___y_3924_;
v___y_3915_ = v___x_3927_;
goto v___jp_3913_;
}
default: 
{
lean_object* v_ipv6_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v_ipv6_3928_ = lean_ctor_get(v_host_3911_, 0);
lean_inc_ref(v_ipv6_3928_);
lean_dec_ref_known(v_host_3911_, 1);
v___x_3929_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3930_ = lean_uv_ntop_v6(v_ipv6_3928_);
lean_dec_ref(v_ipv6_3928_);
v___x_3931_ = lean_string_append(v___x_3929_, v___x_3930_);
lean_dec_ref(v___x_3930_);
v___x_3932_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3933_ = lean_string_append(v___x_3931_, v___x_3932_);
v___y_3914_ = v___y_3924_;
v___y_3915_ = v___x_3933_;
goto v___jp_3913_;
}
}
}
}
default: 
{
lean_object* v___x_3950_; 
lean_dec_ref(v___f_3796_);
lean_dec_ref(v___f_3795_);
v___x_3950_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__2___closed__0));
return v___x_3950_;
}
}
v___jp_3798_:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3802_ = lean_string_append(v___y_3800_, v___y_3799_);
lean_dec_ref(v___y_3799_);
v___x_3803_ = lean_string_append(v___x_3802_, v___y_3801_);
lean_dec_ref(v___y_3801_);
return v___x_3803_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__2(lean_object* v___f_3954_, lean_object* v___f_3955_, lean_object* v_out_3956_, lean_object* v_target_3957_){
_start:
{
lean_object* v___y_3959_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; 
switch(lean_obj_tag(v_target_3957_))
{
case 0:
{
lean_object* v_path_3972_; lean_object* v_query_3973_; lean_object* v___y_3975_; lean_object* v_segments_3978_; uint8_t v_absolute_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; size_t v_sz_3982_; size_t v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v_result_3986_; 
lean_dec_ref(v___f_3955_);
v_path_3972_ = lean_ctor_get(v_target_3957_, 0);
lean_inc_ref(v_path_3972_);
v_query_3973_ = lean_ctor_get(v_target_3957_, 1);
lean_inc(v_query_3973_);
lean_dec_ref_known(v_target_3957_, 2);
v_segments_3978_ = lean_ctor_get(v_path_3972_, 0);
lean_inc_ref(v_segments_3978_);
v_absolute_3979_ = lean_ctor_get_uint8(v_path_3972_, sizeof(void*)*1);
lean_dec_ref(v_path_3972_);
v___x_3980_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3981_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3982_ = lean_array_size(v_segments_3978_);
v___x_3983_ = ((size_t)0ULL);
v___x_3984_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3981_, v___f_3954_, v_sz_3982_, v___x_3983_, v_segments_3978_);
v___x_3985_ = lean_array_to_list(v___x_3984_);
v_result_3986_ = l_String_intercalate(v___x_3980_, v___x_3985_);
if (v_absolute_3979_ == 0)
{
v___y_3975_ = v_result_3986_;
goto v___jp_3974_;
}
else
{
lean_object* v___x_3987_; 
v___x_3987_ = lean_string_append(v___x_3980_, v_result_3986_);
lean_dec_ref(v_result_3986_);
v___y_3975_ = v___x_3987_;
goto v___jp_3974_;
}
v___jp_3974_:
{
lean_object* v_queryStr_3976_; lean_object* v___x_3977_; 
v_queryStr_3976_ = l_Std_Http_URI_Query_formatOption(v_query_3973_);
v___x_3977_ = lean_string_append(v___y_3975_, v_queryStr_3976_);
lean_dec_ref(v_queryStr_3976_);
v___y_3959_ = v___x_3977_;
goto v___jp_3958_;
}
}
case 1:
{
lean_object* v_uri_3988_; lean_object* v_scheme_3989_; lean_object* v_authority_3990_; lean_object* v_path_3991_; lean_object* v_query_3992_; lean_object* v_fragment_3993_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4016_; 
lean_dec_ref(v___f_3954_);
v_uri_3988_ = lean_ctor_get(v_target_3957_, 0);
lean_inc_ref(v_uri_3988_);
lean_dec_ref_known(v_target_3957_, 1);
v_scheme_3989_ = lean_ctor_get(v_uri_3988_, 0);
lean_inc_ref(v_scheme_3989_);
v_authority_3990_ = lean_ctor_get(v_uri_3988_, 1);
lean_inc(v_authority_3990_);
v_path_3991_ = lean_ctor_get(v_uri_3988_, 2);
lean_inc_ref(v_path_3991_);
v_query_3992_ = lean_ctor_get(v_uri_3988_, 3);
lean_inc(v_query_3992_);
v_fragment_3993_ = lean_ctor_get(v_uri_3988_, 4);
lean_inc(v_fragment_3993_);
lean_dec_ref(v_uri_3988_);
if (lean_obj_tag(v_authority_3990_) == 0)
{
lean_object* v___x_4027_; 
v___x_4027_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4016_ = v___x_4027_;
goto v___jp_4015_;
}
else
{
lean_object* v_val_4028_; lean_object* v_userInfo_4029_; lean_object* v_host_4030_; lean_object* v_port_4031_; lean_object* v___x_4032_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4051_; 
v_val_4028_ = lean_ctor_get(v_authority_3990_, 0);
lean_inc(v_val_4028_);
lean_dec_ref_known(v_authority_3990_, 1);
v_userInfo_4029_ = lean_ctor_get(v_val_4028_, 0);
lean_inc(v_userInfo_4029_);
v_host_4030_ = lean_ctor_get(v_val_4028_, 1);
lean_inc_ref(v_host_4030_);
v_port_4031_ = lean_ctor_get(v_val_4028_, 2);
lean_inc(v_port_4031_);
lean_dec(v_val_4028_);
v___x_4032_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_4029_) == 0)
{
lean_object* v___x_4061_; 
v___x_4061_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4051_ = v___x_4061_;
goto v___jp_4050_;
}
else
{
lean_object* v_val_4062_; lean_object* v_password_4063_; 
v_val_4062_ = lean_ctor_get(v_userInfo_4029_, 0);
lean_inc(v_val_4062_);
lean_dec_ref_known(v_userInfo_4029_, 1);
v_password_4063_ = lean_ctor_get(v_val_4062_, 1);
if (lean_obj_tag(v_password_4063_) == 0)
{
lean_object* v_username_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v_username_4064_ = lean_ctor_get(v_val_4062_, 0);
lean_inc_ref(v_username_4064_);
lean_dec(v_val_4062_);
v___x_4065_ = lean_string_from_utf8_unchecked(v_username_4064_);
v___x_4066_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4067_ = lean_string_append(v___x_4065_, v___x_4066_);
v___y_4051_ = v___x_4067_;
goto v___jp_4050_;
}
else
{
lean_object* v_username_4068_; lean_object* v_val_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
lean_inc_ref(v_password_4063_);
v_username_4068_ = lean_ctor_get(v_val_4062_, 0);
lean_inc_ref(v_username_4068_);
lean_dec(v_val_4062_);
v_val_4069_ = lean_ctor_get(v_password_4063_, 0);
lean_inc(v_val_4069_);
lean_dec_ref_known(v_password_4063_, 1);
v___x_4070_ = lean_string_from_utf8_unchecked(v_username_4068_);
v___x_4071_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4072_ = lean_string_append(v___x_4070_, v___x_4071_);
v___x_4073_ = lean_string_from_utf8_unchecked(v_val_4069_);
v___x_4074_ = lean_string_append(v___x_4072_, v___x_4073_);
lean_dec_ref(v___x_4073_);
v___x_4075_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4076_ = lean_string_append(v___x_4074_, v___x_4075_);
v___y_4051_ = v___x_4076_;
goto v___jp_4050_;
}
}
v___jp_4033_:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4037_ = lean_string_append(v___y_4034_, v___y_4035_);
lean_dec_ref(v___y_4035_);
v___x_4038_ = lean_string_append(v___x_4037_, v___y_4036_);
lean_dec_ref(v___y_4036_);
v___x_4039_ = lean_string_append(v___x_4032_, v___x_4038_);
lean_dec_ref(v___x_4038_);
v___y_4016_ = v___x_4039_;
goto v___jp_4015_;
}
v___jp_4040_:
{
switch(lean_obj_tag(v_port_4031_))
{
case 0:
{
lean_object* v___x_4043_; 
v___x_4043_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4034_ = v___y_4041_;
v___y_4035_ = v___y_4042_;
v___y_4036_ = v___x_4043_;
goto v___jp_4033_;
}
case 1:
{
lean_object* v___x_4044_; 
v___x_4044_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_4034_ = v___y_4041_;
v___y_4035_ = v___y_4042_;
v___y_4036_ = v___x_4044_;
goto v___jp_4033_;
}
default: 
{
uint16_t v_port_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v_port_4045_ = lean_ctor_get_uint16(v_port_4031_, 0);
lean_dec_ref_known(v_port_4031_, 0);
v___x_4046_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4047_ = lean_uint16_to_nat(v_port_4045_);
v___x_4048_ = l_Nat_reprFast(v___x_4047_);
v___x_4049_ = lean_string_append(v___x_4046_, v___x_4048_);
lean_dec_ref(v___x_4048_);
v___y_4034_ = v___y_4041_;
v___y_4035_ = v___y_4042_;
v___y_4036_ = v___x_4049_;
goto v___jp_4033_;
}
}
}
v___jp_4050_:
{
switch(lean_obj_tag(v_host_4030_))
{
case 0:
{
lean_object* v_name_4052_; 
v_name_4052_ = lean_ctor_get(v_host_4030_, 0);
lean_inc_ref(v_name_4052_);
lean_dec_ref_known(v_host_4030_, 1);
v___y_4041_ = v___y_4051_;
v___y_4042_ = v_name_4052_;
goto v___jp_4040_;
}
case 1:
{
lean_object* v_ipv4_4053_; lean_object* v___x_4054_; 
v_ipv4_4053_ = lean_ctor_get(v_host_4030_, 0);
lean_inc_ref(v_ipv4_4053_);
lean_dec_ref_known(v_host_4030_, 1);
v___x_4054_ = lean_uv_ntop_v4(v_ipv4_4053_);
lean_dec_ref(v_ipv4_4053_);
v___y_4041_ = v___y_4051_;
v___y_4042_ = v___x_4054_;
goto v___jp_4040_;
}
default: 
{
lean_object* v_ipv6_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v_ipv6_4055_ = lean_ctor_get(v_host_4030_, 0);
lean_inc_ref(v_ipv6_4055_);
lean_dec_ref_known(v_host_4030_, 1);
v___x_4056_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4057_ = lean_uv_ntop_v6(v_ipv6_4055_);
lean_dec_ref(v_ipv6_4055_);
v___x_4058_ = lean_string_append(v___x_4056_, v___x_4057_);
lean_dec_ref(v___x_4057_);
v___x_4059_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4060_ = lean_string_append(v___x_4058_, v___x_4059_);
v___y_4041_ = v___y_4051_;
v___y_4042_ = v___x_4060_;
goto v___jp_4040_;
}
}
}
}
v___jp_3994_:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_3999_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4000_ = lean_string_append(v_scheme_3989_, v___x_3999_);
v___x_4001_ = lean_string_append(v___x_4000_, v___y_3995_);
lean_dec_ref(v___y_3995_);
v___x_4002_ = lean_string_append(v___x_4001_, v___y_3997_);
lean_dec_ref(v___y_3997_);
v___x_4003_ = lean_string_append(v___x_4002_, v___y_3996_);
lean_dec_ref(v___y_3996_);
v___x_4004_ = lean_string_append(v___x_4003_, v___y_3998_);
lean_dec_ref(v___y_3998_);
v___y_3959_ = v___x_4004_;
goto v___jp_3958_;
}
v___jp_4005_:
{
lean_object* v_queryPart_4008_; 
v_queryPart_4008_ = l_Std_Http_URI_Query_formatOption(v_query_3992_);
if (lean_obj_tag(v_fragment_3993_) == 0)
{
lean_object* v___x_4009_; 
v___x_4009_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3995_ = v___y_4006_;
v___y_3996_ = v_queryPart_4008_;
v___y_3997_ = v___y_4007_;
v___y_3998_ = v___x_4009_;
goto v___jp_3994_;
}
else
{
lean_object* v_val_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v_val_4010_ = lean_ctor_get(v_fragment_3993_, 0);
lean_inc(v_val_4010_);
lean_dec_ref_known(v_fragment_3993_, 1);
v___x_4011_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_4012_ = l_Std_Http_URI_EncodedFragment_encode(v_val_4010_);
v___x_4013_ = lean_string_from_utf8_unchecked(v___x_4012_);
v___x_4014_ = lean_string_append(v___x_4011_, v___x_4013_);
lean_dec_ref(v___x_4013_);
v___y_3995_ = v___y_4006_;
v___y_3996_ = v_queryPart_4008_;
v___y_3997_ = v___y_4007_;
v___y_3998_ = v___x_4014_;
goto v___jp_3994_;
}
}
v___jp_4015_:
{
lean_object* v_segments_4017_; uint8_t v_absolute_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; size_t v_sz_4021_; size_t v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v_result_4025_; 
v_segments_4017_ = lean_ctor_get(v_path_3991_, 0);
lean_inc_ref(v_segments_4017_);
v_absolute_4018_ = lean_ctor_get_uint8(v_path_3991_, sizeof(void*)*1);
lean_dec_ref(v_path_3991_);
v___x_4019_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_4020_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_4021_ = lean_array_size(v_segments_4017_);
v___x_4022_ = ((size_t)0ULL);
v___x_4023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4020_, v___f_3955_, v_sz_4021_, v___x_4022_, v_segments_4017_);
v___x_4024_ = lean_array_to_list(v___x_4023_);
v_result_4025_ = l_String_intercalate(v___x_4019_, v___x_4024_);
if (v_absolute_4018_ == 0)
{
v___y_4006_ = v___y_4016_;
v___y_4007_ = v_result_4025_;
goto v___jp_4005_;
}
else
{
lean_object* v___x_4026_; 
v___x_4026_ = lean_string_append(v___x_4019_, v_result_4025_);
lean_dec_ref(v_result_4025_);
v___y_4006_ = v___y_4016_;
v___y_4007_ = v___x_4026_;
goto v___jp_4005_;
}
}
}
case 2:
{
lean_object* v_authority_4077_; lean_object* v_userInfo_4078_; lean_object* v_host_4079_; lean_object* v_port_4080_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4092_; 
lean_dec_ref(v___f_3955_);
lean_dec_ref(v___f_3954_);
v_authority_4077_ = lean_ctor_get(v_target_3957_, 0);
lean_inc_ref(v_authority_4077_);
lean_dec_ref_known(v_target_3957_, 1);
v_userInfo_4078_ = lean_ctor_get(v_authority_4077_, 0);
lean_inc(v_userInfo_4078_);
v_host_4079_ = lean_ctor_get(v_authority_4077_, 1);
lean_inc_ref(v_host_4079_);
v_port_4080_ = lean_ctor_get(v_authority_4077_, 2);
lean_inc(v_port_4080_);
lean_dec_ref(v_authority_4077_);
if (lean_obj_tag(v_userInfo_4078_) == 0)
{
lean_object* v___x_4102_; 
v___x_4102_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4092_ = v___x_4102_;
goto v___jp_4091_;
}
else
{
lean_object* v_val_4103_; lean_object* v_password_4104_; 
v_val_4103_ = lean_ctor_get(v_userInfo_4078_, 0);
lean_inc(v_val_4103_);
lean_dec_ref_known(v_userInfo_4078_, 1);
v_password_4104_ = lean_ctor_get(v_val_4103_, 1);
if (lean_obj_tag(v_password_4104_) == 0)
{
lean_object* v_username_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v_username_4105_ = lean_ctor_get(v_val_4103_, 0);
lean_inc_ref(v_username_4105_);
lean_dec(v_val_4103_);
v___x_4106_ = lean_string_from_utf8_unchecked(v_username_4105_);
v___x_4107_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4108_ = lean_string_append(v___x_4106_, v___x_4107_);
v___y_4092_ = v___x_4108_;
goto v___jp_4091_;
}
else
{
lean_object* v_username_4109_; lean_object* v_val_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
lean_inc_ref(v_password_4104_);
v_username_4109_ = lean_ctor_get(v_val_4103_, 0);
lean_inc_ref(v_username_4109_);
lean_dec(v_val_4103_);
v_val_4110_ = lean_ctor_get(v_password_4104_, 0);
lean_inc(v_val_4110_);
lean_dec_ref_known(v_password_4104_, 1);
v___x_4111_ = lean_string_from_utf8_unchecked(v_username_4109_);
v___x_4112_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4113_ = lean_string_append(v___x_4111_, v___x_4112_);
v___x_4114_ = lean_string_from_utf8_unchecked(v_val_4110_);
v___x_4115_ = lean_string_append(v___x_4113_, v___x_4114_);
lean_dec_ref(v___x_4114_);
v___x_4116_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4117_ = lean_string_append(v___x_4115_, v___x_4116_);
v___y_4092_ = v___x_4117_;
goto v___jp_4091_;
}
}
v___jp_4081_:
{
switch(lean_obj_tag(v_port_4080_))
{
case 0:
{
lean_object* v___x_4084_; 
v___x_4084_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3967_ = v___y_4083_;
v___y_3968_ = v___y_4082_;
v___y_3969_ = v___x_4084_;
goto v___jp_3966_;
}
case 1:
{
lean_object* v___x_4085_; 
v___x_4085_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3967_ = v___y_4083_;
v___y_3968_ = v___y_4082_;
v___y_3969_ = v___x_4085_;
goto v___jp_3966_;
}
default: 
{
uint16_t v_port_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v_port_4086_ = lean_ctor_get_uint16(v_port_4080_, 0);
lean_dec_ref_known(v_port_4080_, 0);
v___x_4087_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4088_ = lean_uint16_to_nat(v_port_4086_);
v___x_4089_ = l_Nat_reprFast(v___x_4088_);
v___x_4090_ = lean_string_append(v___x_4087_, v___x_4089_);
lean_dec_ref(v___x_4089_);
v___y_3967_ = v___y_4083_;
v___y_3968_ = v___y_4082_;
v___y_3969_ = v___x_4090_;
goto v___jp_3966_;
}
}
}
v___jp_4091_:
{
switch(lean_obj_tag(v_host_4079_))
{
case 0:
{
lean_object* v_name_4093_; 
v_name_4093_ = lean_ctor_get(v_host_4079_, 0);
lean_inc_ref(v_name_4093_);
lean_dec_ref_known(v_host_4079_, 1);
v___y_4082_ = v___y_4092_;
v___y_4083_ = v_name_4093_;
goto v___jp_4081_;
}
case 1:
{
lean_object* v_ipv4_4094_; lean_object* v___x_4095_; 
v_ipv4_4094_ = lean_ctor_get(v_host_4079_, 0);
lean_inc_ref(v_ipv4_4094_);
lean_dec_ref_known(v_host_4079_, 1);
v___x_4095_ = lean_uv_ntop_v4(v_ipv4_4094_);
lean_dec_ref(v_ipv4_4094_);
v___y_4082_ = v___y_4092_;
v___y_4083_ = v___x_4095_;
goto v___jp_4081_;
}
default: 
{
lean_object* v_ipv6_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v_ipv6_4096_ = lean_ctor_get(v_host_4079_, 0);
lean_inc_ref(v_ipv6_4096_);
lean_dec_ref_known(v_host_4079_, 1);
v___x_4097_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4098_ = lean_uv_ntop_v6(v_ipv6_4096_);
lean_dec_ref(v_ipv6_4096_);
v___x_4099_ = lean_string_append(v___x_4097_, v___x_4098_);
lean_dec_ref(v___x_4098_);
v___x_4100_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4101_ = lean_string_append(v___x_4099_, v___x_4100_);
v___y_4082_ = v___y_4092_;
v___y_4083_ = v___x_4101_;
goto v___jp_4081_;
}
}
}
}
default: 
{
lean_object* v___x_4118_; 
lean_dec_ref(v___f_3955_);
lean_dec_ref(v___f_3954_);
v___x_4118_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__2___closed__0));
v___y_3959_ = v___x_4118_;
goto v___jp_3958_;
}
}
v___jp_3958_:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; lean_object* v___x_3965_; 
v___x_3960_ = lean_string_to_utf8(v___y_3959_);
v___x_3961_ = lean_unsigned_to_nat(0u);
v___x_3962_ = lean_byte_array_size(v_out_3956_);
v___x_3963_ = lean_byte_array_size(v___x_3960_);
v___x_3964_ = 0;
v___x_3965_ = lean_byte_array_copy_slice(v___x_3960_, v___x_3961_, v_out_3956_, v___x_3962_, v___x_3963_, v___x_3964_);
lean_dec_ref(v___x_3960_);
return v___x_3965_;
}
v___jp_3966_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = lean_string_append(v___y_3968_, v___y_3967_);
lean_dec_ref(v___y_3967_);
v___x_3971_ = lean_string_append(v___x_3970_, v___y_3969_);
lean_dec_ref(v___y_3969_);
v___y_3959_ = v___x_3971_;
goto v___jp_3958_;
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
