// Lean compiler output
// Module: Std.Internal.Http.Data.URI.Basic
// Imports: import Init.Data.ToString public import Std.Net public import Std.Internal.Http.Internal public import Std.Internal.Http.Data.URI.Encoding public import Init.Data.String.Search
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
uint8_t lean_sarray_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t l_Std_Http_Internal_instDecidableIsLowerCase(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_data(lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
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
lean_object* l_Std_Http_URI_EncodedString_empty(lean_object*);
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_List_getLast_x3f___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object*);
extern lean_object* l_Std_Net_instInhabitedIPv4Addr_default;
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Http_URI_Scheme_ofString_x3f___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x3f___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_Scheme_ofString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_Scheme_ofString_x3f___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_Scheme_ofString_x3f___closed__0 = (const lean_object*)&l_Std_Http_URI_Scheme_ofString_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(lean_object*);
static const lean_string_object l_Std_Http_URI_Scheme_ofString_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Std.Internal.Http.Data.URI.Basic"};
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
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21;
LEAN_EXPORT uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_URI_instInhabitedUserInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instInhabitedUserInfo_default___closed__0 = (const lean_object*)&l_Std_Http_URI_instInhabitedUserInfo_default___closed__0_value;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instInhabitedUserInfo_default___closed__1;
static lean_once_cell_t l_Std_Http_URI_instInhabitedUserInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instInhabitedUserInfo_default___closed__2;
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
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidDomainLabel___lam__0(uint8_t, uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidDomainLabel___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidDomainLabel___boxed(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_DomainName_ofString_x3f(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".."};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_normalize(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_toDecodedSegments(lean_object*);
static const lean_closure_object l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l_Std_Http_instInhabitedURI_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_URI_instInhabitedScheme___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_URI_instInhabitedPath_default___closed__1_value),((lean_object*)&l_Std_Http_URI_instInhabitedQuery___aux__1___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_instInhabitedURI_default___closed__0 = (const lean_object*)&l_Std_Http_instInhabitedURI_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instInhabitedURI_default = (const lean_object*)&l_Std_Http_instInhabitedURI_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instInhabitedURI = (const lean_object*)&l_Std_Http_instInhabitedURI_default___closed__0_value;
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instBEqURI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instBEqURI_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instBEqURI___closed__0 = (const lean_object*)&l_Std_Http_instBEqURI___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instBEqURI = (const lean_object*)&l_Std_Http_instBEqURI___closed__0_value;
static const lean_string_object l_Std_Http_instToStringURI___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Std_Http_instToStringURI___lam__2___closed__0 = (const lean_object*)&l_Std_Http_instToStringURI___lam__2___closed__0_value;
static const lean_string_object l_Std_Http_instToStringURI___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "//"};
static const lean_object* l_Std_Http_instToStringURI___lam__2___closed__1 = (const lean_object*)&l_Std_Http_instToStringURI___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instToStringURI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instToStringURI___lam__2, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_URI_Query_instToString___closed__0_value),((lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value)} };
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
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Std_Http_RequestTarget_instToString___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Std_Http_RequestTarget_instToString___lam__4___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_instToString___lam__4___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_RequestTarget_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_RequestTarget_instToString___lam__4, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Std_Http_URI_Query_instToString___closed__0_value),((lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value),((lean_object*)&l_Std_Http_URI_Query_instToString___closed__0_value),((lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value)} };
static const lean_object* l_Std_Http_RequestTarget_instToString___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_RequestTarget_instToString = (const lean_object*)&l_Std_Http_RequestTarget_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_RequestTarget_instEncodeV11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_RequestTarget_instEncodeV11___lam__4, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Std_Http_URI_Query_instToString___closed__0_value),((lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value),((lean_object*)&l_Std_Http_URI_Query_instToString___closed__0_value),((lean_object*)&l_Std_Http_URI_instToStringPath___closed__0_value)} };
static const lean_object* l_Std_Http_RequestTarget_instEncodeV11___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_instEncodeV11___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_RequestTarget_instEncodeV11 = (const lean_object*)&l_Std_Http_RequestTarget_instEncodeV11___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_URI_Scheme_ofString_x3f___lam__0(uint32_t v___y_3_){
_start:
{
uint8_t v___y_5_; lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; uint8_t v___y_21_; 
v___x_17_ = lean_uint32_to_nat(v___y_3_);
v___x_18_ = lean_unsigned_to_nat(128u);
v___x_19_ = lean_nat_dec_lt(v___x_17_, v___x_18_);
lean_dec(v___x_17_);
if (v___x_19_ == 0)
{
v___y_5_ = v___x_19_;
goto v___jp_4_;
}
else
{
uint32_t v___x_26_; uint8_t v___x_27_; 
v___x_26_ = 48;
v___x_27_ = lean_uint32_dec_le(v___x_26_, v___y_3_);
if (v___x_27_ == 0)
{
v___y_21_ = v___x_27_;
goto v___jp_20_;
}
else
{
uint32_t v___x_28_; uint8_t v___x_29_; 
v___x_28_ = 57;
v___x_29_ = lean_uint32_dec_le(v___y_3_, v___x_28_);
v___y_21_ = v___x_29_;
goto v___jp_20_;
}
}
v___jp_4_:
{
if (v___y_5_ == 0)
{
uint32_t v___x_6_; uint8_t v___x_7_; 
v___x_6_ = 43;
v___x_7_ = lean_uint32_dec_eq(v___y_3_, v___x_6_);
if (v___x_7_ == 0)
{
uint32_t v___x_8_; uint8_t v___x_9_; 
v___x_8_ = 45;
v___x_9_ = lean_uint32_dec_eq(v___y_3_, v___x_8_);
if (v___x_9_ == 0)
{
uint32_t v___x_10_; uint8_t v___x_11_; 
v___x_10_ = 46;
v___x_11_ = lean_uint32_dec_eq(v___y_3_, v___x_10_);
if (v___x_11_ == 0)
{
return v___y_5_;
}
else
{
return v___x_11_;
}
}
else
{
return v___x_9_;
}
}
else
{
return v___x_7_;
}
}
else
{
return v___y_5_;
}
}
v___jp_12_:
{
uint32_t v___x_13_; uint8_t v___x_14_; 
v___x_13_ = 97;
v___x_14_ = lean_uint32_dec_le(v___x_13_, v___y_3_);
if (v___x_14_ == 0)
{
v___y_5_ = v___x_14_;
goto v___jp_4_;
}
else
{
uint32_t v___x_15_; uint8_t v___x_16_; 
v___x_15_ = 122;
v___x_16_ = lean_uint32_dec_le(v___y_3_, v___x_15_);
v___y_5_ = v___x_16_;
goto v___jp_4_;
}
}
v___jp_20_:
{
if (v___y_21_ == 0)
{
uint32_t v___x_22_; uint8_t v___x_23_; 
v___x_22_ = 65;
v___x_23_ = lean_uint32_dec_le(v___x_22_, v___y_3_);
if (v___x_23_ == 0)
{
goto v___jp_12_;
}
else
{
uint32_t v___x_24_; uint8_t v___x_25_; 
v___x_24_ = 90;
v___x_25_ = lean_uint32_dec_le(v___y_3_, v___x_24_);
if (v___x_25_ == 0)
{
goto v___jp_12_;
}
else
{
v___y_5_ = v___x_19_;
goto v___jp_4_;
}
}
}
else
{
return v___y_21_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x3f___lam__0___boxed(lean_object* v___y_30_){
_start:
{
uint32_t v___y_570__boxed_31_; uint8_t v_res_32_; lean_object* v_r_33_; 
v___y_570__boxed_31_ = lean_unbox_uint32(v___y_30_);
lean_dec(v___y_30_);
v_res_32_ = l_Std_Http_URI_Scheme_ofString_x3f___lam__0(v___y_570__boxed_31_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(lean_object* v_s_34_, lean_object* v_p_35_){
_start:
{
uint32_t v___y_37_; lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_42_ = lean_string_utf8_byte_size(v_s_34_);
v___x_43_ = lean_nat_dec_eq(v_p_35_, v___x_42_);
if (v___x_43_ == 0)
{
uint32_t v___x_44_; uint32_t v___x_45_; uint8_t v___x_46_; 
v___x_44_ = lean_string_utf8_get_fast(v_s_34_, v_p_35_);
v___x_45_ = 65;
v___x_46_ = lean_uint32_dec_le(v___x_45_, v___x_44_);
if (v___x_46_ == 0)
{
v___y_37_ = v___x_44_;
goto v___jp_36_;
}
else
{
uint32_t v___x_47_; uint8_t v___x_48_; 
v___x_47_ = 90;
v___x_48_ = lean_uint32_dec_le(v___x_44_, v___x_47_);
if (v___x_48_ == 0)
{
v___y_37_ = v___x_44_;
goto v___jp_36_;
}
else
{
uint32_t v___x_49_; uint32_t v___x_50_; 
v___x_49_ = 32;
v___x_50_ = lean_uint32_add(v___x_44_, v___x_49_);
v___y_37_ = v___x_50_;
goto v___jp_36_;
}
}
}
else
{
lean_dec(v_p_35_);
return v_s_34_;
}
v___jp_36_:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
lean_inc(v_p_35_);
v___x_38_ = lean_string_utf8_set(v_s_34_, v_p_35_, v___y_37_);
v___x_39_ = l_Char_utf8Size(v___y_37_);
v___x_40_ = lean_nat_add(v_p_35_, v___x_39_);
lean_dec(v___x_39_);
lean_dec(v_p_35_);
v_s_34_ = v___x_38_;
v_p_35_ = v___x_40_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x3f(lean_object* v_s_52_){
_start:
{
lean_object* v___x_53_; lean_object* v_lower_54_; uint8_t v_val_56_; uint8_t v___x_59_; 
v___x_53_ = lean_unsigned_to_nat(0u);
v_lower_54_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_52_, v___x_53_);
lean_inc_ref(v_lower_54_);
v___x_59_ = l_Std_Http_Internal_instDecidableIsLowerCase(v_lower_54_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
lean_dec_ref(v_lower_54_);
v___x_60_ = lean_box(0);
return v___x_60_;
}
else
{
lean_object* v___f_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v___f_61_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x3f___closed__0));
lean_inc_ref(v_lower_54_);
v___x_62_ = lean_string_data(v_lower_54_);
lean_inc(v___x_62_);
v___x_63_ = l_List_all___redArg(v___x_62_, v___f_61_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; 
lean_dec(v___x_62_);
lean_dec_ref(v_lower_54_);
v___x_64_ = lean_box(0);
return v___x_64_;
}
else
{
lean_object* v___x_65_; 
v___x_65_ = l_List_head_x3f___redArg(v___x_62_);
lean_dec(v___x_62_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v___x_66_; 
lean_dec_ref(v_lower_54_);
v___x_66_ = lean_box(0);
return v___x_66_;
}
else
{
lean_object* v_val_67_; uint32_t v___x_75_; uint32_t v___x_76_; uint8_t v___x_77_; 
v_val_67_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_val_67_);
lean_dec_ref(v___x_65_);
v___x_75_ = 65;
v___x_76_ = lean_unbox_uint32(v_val_67_);
v___x_77_ = lean_uint32_dec_le(v___x_75_, v___x_76_);
if (v___x_77_ == 0)
{
goto v___jp_68_;
}
else
{
uint32_t v___x_78_; uint32_t v___x_79_; uint8_t v___x_80_; 
v___x_78_ = 90;
v___x_79_ = lean_unbox_uint32(v_val_67_);
v___x_80_ = lean_uint32_dec_le(v___x_79_, v___x_78_);
if (v___x_80_ == 0)
{
goto v___jp_68_;
}
else
{
lean_dec(v_val_67_);
v_val_56_ = v___x_63_;
goto v___jp_55_;
}
}
v___jp_68_:
{
uint32_t v___x_69_; uint32_t v___x_70_; uint8_t v___x_71_; 
v___x_69_ = 97;
v___x_70_ = lean_unbox_uint32(v_val_67_);
v___x_71_ = lean_uint32_dec_le(v___x_69_, v___x_70_);
if (v___x_71_ == 0)
{
lean_dec(v_val_67_);
v_val_56_ = v___x_71_;
goto v___jp_55_;
}
else
{
uint32_t v___x_72_; uint32_t v___x_73_; uint8_t v___x_74_; 
v___x_72_ = 122;
v___x_73_ = lean_unbox_uint32(v_val_67_);
lean_dec(v_val_67_);
v___x_74_ = lean_uint32_dec_le(v___x_73_, v___x_72_);
v_val_56_ = v___x_74_;
goto v___jp_55_;
}
}
}
}
}
v___jp_55_:
{
if (v_val_56_ == 0)
{
lean_object* v___x_57_; 
lean_dec_ref(v_lower_54_);
v___x_57_ = lean_box(0);
return v___x_57_;
}
else
{
lean_object* v___x_58_; 
v___x_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_58_, 0, v_lower_54_);
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(lean_object* v_msg_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l_Std_Http_URI_instInhabitedScheme___closed__0));
v___x_83_ = lean_panic_fn_borrowed(v___x_82_, v_msg_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x21(lean_object* v_s_87_){
_start:
{
lean_object* v___x_88_; 
lean_inc_ref(v_s_87_);
v___x_88_ = l_Std_Http_URI_Scheme_ofString_x3f(v_s_87_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_89_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_90_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__1));
v___x_91_ = lean_unsigned_to_nat(83u);
v___x_92_ = lean_unsigned_to_nat(12u);
v___x_93_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_94_ = l_String_quote(v_s_87_);
v___x_95_ = lean_string_append(v___x_93_, v___x_94_);
lean_dec_ref(v___x_94_);
v___x_96_ = l_mkPanicMessageWithDecl(v___x_89_, v___x_90_, v___x_91_, v___x_92_, v___x_95_);
lean_dec_ref(v___x_95_);
v___x_97_ = l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(v___x_96_);
return v___x_97_;
}
else
{
lean_object* v_val_98_; 
lean_dec_ref(v_s_87_);
v_val_98_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_val_98_);
lean_dec_ref(v___x_88_);
return v_val_98_;
}
}
}
LEAN_EXPORT uint16_t l_Std_Http_URI_Scheme_defaultPort(lean_object* v_scheme_100_){
_start:
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___x_102_ = lean_string_dec_eq(v_scheme_100_, v___x_101_);
if (v___x_102_ == 0)
{
uint16_t v___x_103_; 
v___x_103_ = 80;
return v___x_103_;
}
else
{
uint16_t v___x_104_; 
v___x_104_ = 443;
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_defaultPort___boxed(lean_object* v_scheme_105_){
_start:
{
uint16_t v_res_106_; lean_object* v_r_107_; 
v_res_106_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_105_);
lean_dec_ref(v_scheme_105_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofPort(uint16_t v_port_108_){
_start:
{
uint16_t v___x_109_; uint8_t v___x_110_; 
v___x_109_ = 443;
v___x_110_ = lean_uint16_dec_eq(v_port_108_, v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
v___x_111_ = ((lean_object*)(l_Std_Http_URI_instInhabitedScheme___closed__0));
return v___x_111_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofPort___boxed(lean_object* v_port_113_){
_start:
{
uint16_t v_port_boxed_114_; lean_object* v_res_115_; 
v_port_boxed_114_ = lean_unbox(v_port_113_);
v_res_115_ = l_Std_Http_URI_Scheme_ofPort(v_port_boxed_114_);
return v_res_115_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0(void){
_start:
{
uint32_t v___x_116_; uint8_t v___x_117_; 
v___x_116_ = 58;
v___x_117_ = lean_uint32_to_uint8(v___x_116_);
return v___x_117_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1(void){
_start:
{
uint32_t v___x_118_; uint8_t v___x_119_; 
v___x_118_ = 38;
v___x_119_ = lean_uint32_to_uint8(v___x_118_);
return v___x_119_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2(void){
_start:
{
uint32_t v___x_120_; uint8_t v___x_121_; 
v___x_120_ = 39;
v___x_121_ = lean_uint32_to_uint8(v___x_120_);
return v___x_121_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3(void){
_start:
{
uint32_t v___x_122_; uint8_t v___x_123_; 
v___x_122_ = 40;
v___x_123_ = lean_uint32_to_uint8(v___x_122_);
return v___x_123_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4(void){
_start:
{
uint32_t v___x_124_; uint8_t v___x_125_; 
v___x_124_ = 41;
v___x_125_ = lean_uint32_to_uint8(v___x_124_);
return v___x_125_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5(void){
_start:
{
uint32_t v___x_126_; uint8_t v___x_127_; 
v___x_126_ = 42;
v___x_127_ = lean_uint32_to_uint8(v___x_126_);
return v___x_127_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6(void){
_start:
{
uint32_t v___x_128_; uint8_t v___x_129_; 
v___x_128_ = 43;
v___x_129_ = lean_uint32_to_uint8(v___x_128_);
return v___x_129_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7(void){
_start:
{
uint32_t v___x_130_; uint8_t v___x_131_; 
v___x_130_ = 44;
v___x_131_ = lean_uint32_to_uint8(v___x_130_);
return v___x_131_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8(void){
_start:
{
uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = 59;
v___x_133_ = lean_uint32_to_uint8(v___x_132_);
return v___x_133_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9(void){
_start:
{
uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_134_ = 61;
v___x_135_ = lean_uint32_to_uint8(v___x_134_);
return v___x_135_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10(void){
_start:
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 33;
v___x_137_ = lean_uint32_to_uint8(v___x_136_);
return v___x_137_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11(void){
_start:
{
uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = 36;
v___x_139_ = lean_uint32_to_uint8(v___x_138_);
return v___x_139_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12(void){
_start:
{
uint32_t v___x_140_; uint8_t v___x_141_; 
v___x_140_ = 95;
v___x_141_ = lean_uint32_to_uint8(v___x_140_);
return v___x_141_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13(void){
_start:
{
uint32_t v___x_142_; uint8_t v___x_143_; 
v___x_142_ = 126;
v___x_143_ = lean_uint32_to_uint8(v___x_142_);
return v___x_143_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14(void){
_start:
{
uint32_t v___x_144_; uint8_t v___x_145_; 
v___x_144_ = 45;
v___x_145_ = lean_uint32_to_uint8(v___x_144_);
return v___x_145_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15(void){
_start:
{
uint32_t v___x_146_; uint8_t v___x_147_; 
v___x_146_ = 46;
v___x_147_ = lean_uint32_to_uint8(v___x_146_);
return v___x_147_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16(void){
_start:
{
uint32_t v___x_148_; uint8_t v___x_149_; 
v___x_148_ = 65;
v___x_149_ = lean_uint32_to_uint8(v___x_148_);
return v___x_149_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17(void){
_start:
{
uint32_t v___x_150_; uint8_t v___x_151_; 
v___x_150_ = 90;
v___x_151_ = lean_uint32_to_uint8(v___x_150_);
return v___x_151_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18(void){
_start:
{
uint32_t v___x_152_; uint8_t v___x_153_; 
v___x_152_ = 97;
v___x_153_ = lean_uint32_to_uint8(v___x_152_);
return v___x_153_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19(void){
_start:
{
uint32_t v___x_154_; uint8_t v___x_155_; 
v___x_154_ = 122;
v___x_155_ = lean_uint32_to_uint8(v___x_154_);
return v___x_155_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20(void){
_start:
{
uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = 48;
v___x_157_ = lean_uint32_to_uint8(v___x_156_);
return v___x_157_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21(void){
_start:
{
uint32_t v___x_158_; uint8_t v___x_159_; 
v___x_158_ = 57;
v___x_159_ = lean_uint32_to_uint8(v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0(uint8_t v___y_160_){
_start:
{
uint8_t v___y_162_; uint8_t v___y_166_; uint8_t v___y_186_; uint8_t v___y_192_; uint8_t v___y_198_; uint8_t v___y_204_; uint8_t v___y_210_; uint8_t v___x_215_; uint8_t v___x_216_; 
v___x_215_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20);
v___x_216_ = lean_uint8_dec_le(v___x_215_, v___y_160_);
if (v___x_216_ == 0)
{
v___y_210_ = v___x_216_;
goto v___jp_209_;
}
else
{
uint8_t v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21);
v___x_218_ = lean_uint8_dec_le(v___y_160_, v___x_217_);
v___y_210_ = v___x_218_;
goto v___jp_209_;
}
v___jp_161_:
{
if (v___y_162_ == 0)
{
uint8_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0);
v___x_164_ = lean_uint8_dec_eq(v___y_160_, v___x_163_);
return v___x_164_;
}
else
{
return v___y_162_;
}
}
v___jp_165_:
{
if (v___y_166_ == 0)
{
uint8_t v___x_167_; uint8_t v___x_168_; 
v___x_167_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1);
v___x_168_ = lean_uint8_dec_eq(v___y_160_, v___x_167_);
if (v___x_168_ == 0)
{
uint8_t v___x_169_; uint8_t v___x_170_; 
v___x_169_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2);
v___x_170_ = lean_uint8_dec_eq(v___y_160_, v___x_169_);
if (v___x_170_ == 0)
{
uint8_t v___x_171_; uint8_t v___x_172_; 
v___x_171_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3);
v___x_172_ = lean_uint8_dec_eq(v___y_160_, v___x_171_);
if (v___x_172_ == 0)
{
uint8_t v___x_173_; uint8_t v___x_174_; 
v___x_173_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4);
v___x_174_ = lean_uint8_dec_eq(v___y_160_, v___x_173_);
if (v___x_174_ == 0)
{
uint8_t v___x_175_; uint8_t v___x_176_; 
v___x_175_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5);
v___x_176_ = lean_uint8_dec_eq(v___y_160_, v___x_175_);
if (v___x_176_ == 0)
{
uint8_t v___x_177_; uint8_t v___x_178_; 
v___x_177_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6);
v___x_178_ = lean_uint8_dec_eq(v___y_160_, v___x_177_);
if (v___x_178_ == 0)
{
uint8_t v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7);
v___x_180_ = lean_uint8_dec_eq(v___y_160_, v___x_179_);
if (v___x_180_ == 0)
{
uint8_t v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8);
v___x_182_ = lean_uint8_dec_eq(v___y_160_, v___x_181_);
if (v___x_182_ == 0)
{
uint8_t v___x_183_; uint8_t v___x_184_; 
v___x_183_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9);
v___x_184_ = lean_uint8_dec_eq(v___y_160_, v___x_183_);
v___y_162_ = v___x_184_;
goto v___jp_161_;
}
else
{
v___y_162_ = v___x_182_;
goto v___jp_161_;
}
}
else
{
v___y_162_ = v___x_180_;
goto v___jp_161_;
}
}
else
{
v___y_162_ = v___x_178_;
goto v___jp_161_;
}
}
else
{
v___y_162_ = v___x_176_;
goto v___jp_161_;
}
}
else
{
v___y_162_ = v___x_174_;
goto v___jp_161_;
}
}
else
{
v___y_162_ = v___x_172_;
goto v___jp_161_;
}
}
else
{
v___y_162_ = v___x_170_;
goto v___jp_161_;
}
}
else
{
v___y_162_ = v___x_168_;
goto v___jp_161_;
}
}
else
{
return v___y_166_;
}
}
v___jp_185_:
{
if (v___y_186_ == 0)
{
uint8_t v___x_187_; uint8_t v___x_188_; 
v___x_187_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10);
v___x_188_ = lean_uint8_dec_eq(v___y_160_, v___x_187_);
if (v___x_188_ == 0)
{
uint8_t v___x_189_; uint8_t v___x_190_; 
v___x_189_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11);
v___x_190_ = lean_uint8_dec_eq(v___y_160_, v___x_189_);
v___y_166_ = v___x_190_;
goto v___jp_165_;
}
else
{
v___y_166_ = v___x_188_;
goto v___jp_165_;
}
}
else
{
return v___y_186_;
}
}
v___jp_191_:
{
if (v___y_192_ == 0)
{
uint8_t v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12);
v___x_194_ = lean_uint8_dec_eq(v___y_160_, v___x_193_);
if (v___x_194_ == 0)
{
uint8_t v___x_195_; uint8_t v___x_196_; 
v___x_195_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13);
v___x_196_ = lean_uint8_dec_eq(v___y_160_, v___x_195_);
v___y_186_ = v___x_196_;
goto v___jp_185_;
}
else
{
v___y_186_ = v___x_194_;
goto v___jp_185_;
}
}
else
{
return v___y_192_;
}
}
v___jp_197_:
{
if (v___y_198_ == 0)
{
uint8_t v___x_199_; uint8_t v___x_200_; 
v___x_199_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14);
v___x_200_ = lean_uint8_dec_eq(v___y_160_, v___x_199_);
if (v___x_200_ == 0)
{
uint8_t v___x_201_; uint8_t v___x_202_; 
v___x_201_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15);
v___x_202_ = lean_uint8_dec_eq(v___y_160_, v___x_201_);
v___y_192_ = v___x_202_;
goto v___jp_191_;
}
else
{
v___y_192_ = v___x_200_;
goto v___jp_191_;
}
}
else
{
return v___y_198_;
}
}
v___jp_203_:
{
if (v___y_204_ == 0)
{
uint8_t v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16);
v___x_206_ = lean_uint8_dec_le(v___x_205_, v___y_160_);
if (v___x_206_ == 0)
{
v___y_198_ = v___x_206_;
goto v___jp_197_;
}
else
{
uint8_t v___x_207_; uint8_t v___x_208_; 
v___x_207_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17);
v___x_208_ = lean_uint8_dec_le(v___y_160_, v___x_207_);
v___y_198_ = v___x_208_;
goto v___jp_197_;
}
}
else
{
return v___y_204_;
}
}
v___jp_209_:
{
if (v___y_210_ == 0)
{
uint8_t v___x_211_; uint8_t v___x_212_; 
v___x_211_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18);
v___x_212_ = lean_uint8_dec_le(v___x_211_, v___y_160_);
if (v___x_212_ == 0)
{
v___y_204_ = v___x_212_;
goto v___jp_203_;
}
else
{
uint8_t v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19);
v___x_214_ = lean_uint8_dec_le(v___y_160_, v___x_213_);
v___y_204_ = v___x_214_;
goto v___jp_203_;
}
}
else
{
return v___y_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___boxed(lean_object* v___y_219_){
_start:
{
uint8_t v___y_322__boxed_220_; uint8_t v_res_221_; lean_object* v_r_222_; 
v___y_322__boxed_220_ = lean_unbox(v___y_219_);
v_res_221_ = l_Std_Http_URI_instInhabitedUserInfo_default___lam__0(v___y_322__boxed_220_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__1(void){
_start:
{
lean_object* v___f_224_; lean_object* v___x_225_; 
v___f_224_ = ((lean_object*)(l_Std_Http_URI_instInhabitedUserInfo_default___closed__0));
v___x_225_ = l_Std_Http_URI_EncodedString_empty(v___f_224_);
return v___x_225_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__2(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = lean_box(0);
v___x_227_ = lean_obj_once(&l_Std_Http_URI_instInhabitedUserInfo_default___closed__1, &l_Std_Http_URI_instInhabitedUserInfo_default___closed__1_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__1);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___x_226_);
return v___x_228_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default(void){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = lean_obj_once(&l_Std_Http_URI_instInhabitedUserInfo_default___closed__2, &l_Std_Http_URI_instInhabitedUserInfo_default___closed__2_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__2);
return v___x_229_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo(void){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Std_Http_URI_instInhabitedUserInfo_default;
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
if (lean_obj_tag(v_x_237_) == 0)
{
lean_object* v___x_239_; 
v___x_239_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_239_;
}
else
{
lean_object* v_val_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_252_; 
v_val_240_ = lean_ctor_get(v_x_237_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v_x_237_);
if (v_isSharedCheck_252_ == 0)
{
v___x_242_ = v_x_237_;
v_isShared_243_ = v_isSharedCheck_252_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_val_240_);
lean_dec(v_x_237_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_252_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_244_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_245_ = lean_string_from_utf8_unchecked(v_val_240_);
v___x_246_ = l_String_quote(v___x_245_);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 3);
lean_ctor_set(v___x_242_, 0, v___x_246_);
v___x_248_ = v___x_242_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_251_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_244_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = l_Repr_addAppParen(v___x_249_, v_x_238_);
return v___x_250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___boxed(lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_x_253_, v_x_254_);
lean_dec(v_x_254_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_URI_instReprUserInfo_repr_spec__1(lean_object* v_a_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_nat_to_int(v_a_256_);
return v___x_257_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_unsigned_to_nat(12u);
v___x_272_ = lean_nat_to_int(v___x_271_);
return v___x_272_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0));
v___x_281_ = lean_string_length(v___x_280_);
return v___x_281_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13);
v___x_283_ = lean_nat_to_int(v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg(lean_object* v_x_288_){
_start:
{
lean_object* v_username_289_; lean_object* v_password_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_325_; 
v_username_289_ = lean_ctor_get(v_x_288_, 0);
v_password_290_ = lean_ctor_get(v_x_288_, 1);
v_isSharedCheck_325_ = !lean_is_exclusive(v_x_288_);
if (v_isSharedCheck_325_ == 0)
{
v___x_292_ = v_x_288_;
v_isShared_293_ = v_isSharedCheck_325_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_password_290_);
lean_inc(v_username_289_);
lean_dec(v_x_288_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_325_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_294_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_295_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__6));
v___x_296_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_297_ = lean_string_from_utf8_unchecked(v_username_289_);
v___x_298_ = l_String_quote(v___x_297_);
v___x_299_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
if (v_isShared_293_ == 0)
{
lean_ctor_set_tag(v___x_292_, 4);
lean_ctor_set(v___x_292_, 1, v___x_299_);
lean_ctor_set(v___x_292_, 0, v___x_296_);
v___x_301_ = v___x_292_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v___x_299_);
v___x_301_ = v_reuseFailAlloc_324_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
uint8_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_302_ = 0;
v___x_303_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_303_, 0, v___x_301_);
lean_ctor_set_uint8(v___x_303_, sizeof(void*)*1, v___x_302_);
v___x_304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_295_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_304_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = lean_box(1);
v___x_308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__11));
v___x_310_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_294_);
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_password_290_, v___x_312_);
v___x_314_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_296_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set_uint8(v___x_315_, sizeof(void*)*1, v___x_302_);
v___x_316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_311_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_318_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_316_);
v___x_320_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_317_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set_uint8(v___x_323_, sizeof(void*)*1, v___x_302_);
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr(lean_object* v_x_326_, lean_object* v_prec_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_x_326_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___boxed(lean_object* v_x_329_, lean_object* v_prec_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_Http_URI_instReprUserInfo_repr(v_x_329_, v_prec_330_);
lean_dec(v_prec_330_);
return v_res_331_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
if (lean_obj_tag(v_x_334_) == 0)
{
if (lean_obj_tag(v_x_335_) == 0)
{
uint8_t v___x_336_; 
v___x_336_ = 1;
return v___x_336_;
}
else
{
uint8_t v___x_337_; 
v___x_337_ = 0;
return v___x_337_;
}
}
else
{
if (lean_obj_tag(v_x_335_) == 0)
{
uint8_t v___x_338_; 
v___x_338_ = 0;
return v___x_338_;
}
else
{
lean_object* v_val_339_; lean_object* v_val_340_; uint8_t v___x_341_; 
v_val_339_ = lean_ctor_get(v_x_334_, 0);
v_val_340_ = lean_ctor_get(v_x_335_, 0);
v___x_341_ = lean_sarray_dec_eq(v_val_339_, v_val_340_);
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0___boxed(lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
uint8_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_x_342_, v_x_343_);
lean_dec(v_x_343_);
lean_dec(v_x_342_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqUserInfo_beq(lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
lean_object* v_username_348_; lean_object* v_password_349_; lean_object* v_username_350_; lean_object* v_password_351_; uint8_t v___x_352_; 
v_username_348_ = lean_ctor_get(v_x_346_, 0);
v_password_349_ = lean_ctor_get(v_x_346_, 1);
v_username_350_ = lean_ctor_get(v_x_347_, 0);
v_password_351_ = lean_ctor_get(v_x_347_, 1);
v___x_352_ = lean_sarray_dec_eq(v_username_348_, v_username_350_);
if (v___x_352_ == 0)
{
return v___x_352_;
}
else
{
uint8_t v___x_353_; 
v___x_353_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_password_349_, v_password_351_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqUserInfo_beq___boxed(lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_Std_Http_URI_instBEqUserInfo_beq(v_x_354_, v_x_355_);
lean_dec_ref(v_x_355_);
lean_dec_ref(v_x_354_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings(lean_object* v_username_360_, lean_object* v_password_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_360_);
if (lean_obj_tag(v_password_361_) == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_box(0);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
return v___x_364_;
}
else
{
lean_object* v_val_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_374_; 
v_val_365_ = lean_ctor_get(v_password_361_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v_password_361_);
if (v_isSharedCheck_374_ == 0)
{
v___x_367_ = v_password_361_;
v_isShared_368_ = v_isSharedCheck_374_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_val_365_);
lean_dec(v_password_361_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_374_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_365_);
lean_dec(v_val_365_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_373_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; 
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_362_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
return v___x_372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings___boxed(lean_object* v_username_375_, lean_object* v_password_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Std_Http_URI_UserInfo_ofStrings(v_username_375_, v_password_376_);
lean_dec_ref(v_username_375_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f(lean_object* v_ui_378_){
_start:
{
lean_object* v_username_379_; lean_object* v___x_380_; 
v_username_379_ = lean_ctor_get(v_ui_378_, 0);
v___x_380_ = l_Std_Http_URI_EncodedUserInfo_decode(v_username_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f___boxed(lean_object* v_ui_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Std_Http_URI_UserInfo_username_x3f(v_ui_381_);
lean_dec_ref(v_ui_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f(lean_object* v_ui_383_){
_start:
{
lean_object* v_password_384_; 
v_password_384_ = lean_ctor_get(v_ui_383_, 1);
if (lean_obj_tag(v_password_384_) == 0)
{
lean_object* v___x_385_; 
v___x_385_ = lean_box(0);
return v___x_385_;
}
else
{
lean_object* v_val_386_; lean_object* v___x_387_; 
v_val_386_ = lean_ctor_get(v_password_384_, 0);
v___x_387_ = l_Std_Http_URI_EncodedUserInfo_decode(v_val_386_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f___boxed(lean_object* v_ui_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_Http_URI_UserInfo_password_x3f(v_ui_388_);
lean_dec_ref(v_ui_388_);
return v_res_389_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidDomainLabel___lam__0(uint8_t v___x_390_, uint32_t v_c_391_){
_start:
{
uint8_t v___y_393_; lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; uint8_t v___y_405_; 
v___x_401_ = lean_uint32_to_nat(v_c_391_);
v___x_402_ = lean_unsigned_to_nat(128u);
v___x_403_ = lean_nat_dec_lt(v___x_401_, v___x_402_);
lean_dec(v___x_401_);
if (v___x_403_ == 0)
{
v___y_393_ = v___x_403_;
goto v___jp_392_;
}
else
{
uint32_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = 48;
v___x_411_ = lean_uint32_dec_le(v___x_410_, v_c_391_);
if (v___x_411_ == 0)
{
v___y_405_ = v___x_411_;
goto v___jp_404_;
}
else
{
uint32_t v___x_412_; uint8_t v___x_413_; 
v___x_412_ = 57;
v___x_413_ = lean_uint32_dec_le(v_c_391_, v___x_412_);
v___y_405_ = v___x_413_;
goto v___jp_404_;
}
}
v___jp_392_:
{
if (v___y_393_ == 0)
{
uint32_t v___x_394_; uint8_t v___x_395_; 
v___x_394_ = 45;
v___x_395_ = lean_uint32_dec_eq(v_c_391_, v___x_394_);
if (v___x_395_ == 0)
{
return v___y_393_;
}
else
{
return v___x_390_;
}
}
else
{
return v___x_390_;
}
}
v___jp_396_:
{
uint32_t v___x_397_; uint8_t v___x_398_; 
v___x_397_ = 97;
v___x_398_ = lean_uint32_dec_le(v___x_397_, v_c_391_);
if (v___x_398_ == 0)
{
v___y_393_ = v___x_398_;
goto v___jp_392_;
}
else
{
uint32_t v___x_399_; uint8_t v___x_400_; 
v___x_399_ = 122;
v___x_400_ = lean_uint32_dec_le(v_c_391_, v___x_399_);
v___y_393_ = v___x_400_;
goto v___jp_392_;
}
}
v___jp_404_:
{
if (v___y_405_ == 0)
{
uint32_t v___x_406_; uint8_t v___x_407_; 
v___x_406_ = 65;
v___x_407_ = lean_uint32_dec_le(v___x_406_, v_c_391_);
if (v___x_407_ == 0)
{
goto v___jp_396_;
}
else
{
uint32_t v___x_408_; uint8_t v___x_409_; 
v___x_408_ = 90;
v___x_409_ = lean_uint32_dec_le(v_c_391_, v___x_408_);
if (v___x_409_ == 0)
{
goto v___jp_396_;
}
else
{
v___y_393_ = v___x_403_;
goto v___jp_392_;
}
}
}
else
{
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidDomainLabel___lam__0___boxed(lean_object* v___x_414_, lean_object* v_c_415_){
_start:
{
uint8_t v___x_514__boxed_416_; uint32_t v_c_boxed_417_; uint8_t v_res_418_; lean_object* v_r_419_; 
v___x_514__boxed_416_ = lean_unbox(v___x_414_);
v_c_boxed_417_ = lean_unbox_uint32(v_c_415_);
lean_dec(v_c_415_);
v_res_418_ = l_Std_Http_URI_isValidDomainLabel___lam__0(v___x_514__boxed_416_, v_c_boxed_417_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object* v_s_420_){
_start:
{
uint32_t v___y_422_; uint32_t v___y_428_; uint8_t v___y_429_; uint8_t v___y_430_; lean_object* v_chars_435_; uint8_t v___y_453_; uint32_t v___y_455_; uint8_t v___y_461_; uint32_t v___y_462_; uint8_t v___y_463_; uint8_t v___y_469_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_chars_435_ = lean_string_data(v_s_420_);
v___x_485_ = l_List_lengthTR___redArg(v_chars_435_);
v___x_486_ = lean_unsigned_to_nat(63u);
v___x_487_ = lean_nat_dec_le(v___x_485_, v___x_486_);
lean_dec(v___x_485_);
if (v___x_487_ == 0)
{
v___y_469_ = v___x_487_;
goto v___jp_468_;
}
else
{
lean_object* v___x_488_; lean_object* v___f_489_; uint8_t v___x_490_; 
v___x_488_ = lean_box(v___x_487_);
v___f_489_ = lean_alloc_closure((void*)(l_Std_Http_URI_isValidDomainLabel___lam__0___boxed), 2, 1);
lean_closure_set(v___f_489_, 0, v___x_488_);
lean_inc(v_chars_435_);
v___x_490_ = l_List_all___redArg(v_chars_435_, v___f_489_);
v___y_469_ = v___x_490_;
goto v___jp_468_;
}
v___jp_421_:
{
uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 97;
v___x_424_ = lean_uint32_dec_le(v___x_423_, v___y_422_);
if (v___x_424_ == 0)
{
return v___x_424_;
}
else
{
uint32_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = 122;
v___x_426_ = lean_uint32_dec_le(v___y_422_, v___x_425_);
return v___x_426_;
}
}
v___jp_427_:
{
if (v___y_430_ == 0)
{
uint32_t v___x_431_; uint8_t v___x_432_; 
v___x_431_ = 65;
v___x_432_ = lean_uint32_dec_le(v___x_431_, v___y_428_);
if (v___x_432_ == 0)
{
v___y_422_ = v___y_428_;
goto v___jp_421_;
}
else
{
uint32_t v___x_433_; uint8_t v___x_434_; 
v___x_433_ = 90;
v___x_434_ = lean_uint32_dec_le(v___y_428_, v___x_433_);
if (v___x_434_ == 0)
{
v___y_422_ = v___y_428_;
goto v___jp_421_;
}
else
{
return v___y_429_;
}
}
}
else
{
return v___y_430_;
}
}
v___jp_436_:
{
lean_object* v___x_437_; 
v___x_437_ = l_List_getLast_x3f___redArg(v_chars_435_);
lean_dec(v_chars_435_);
if (lean_obj_tag(v___x_437_) == 0)
{
uint8_t v___x_438_; 
v___x_438_ = 0;
return v___x_438_;
}
else
{
lean_object* v_val_439_; uint32_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v_val_439_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_val_439_);
lean_dec_ref(v___x_437_);
v___x_440_ = lean_unbox_uint32(v_val_439_);
v___x_441_ = lean_uint32_to_nat(v___x_440_);
v___x_442_ = lean_unsigned_to_nat(128u);
v___x_443_ = lean_nat_dec_lt(v___x_441_, v___x_442_);
lean_dec(v___x_441_);
if (v___x_443_ == 0)
{
lean_dec(v_val_439_);
return v___x_443_;
}
else
{
uint32_t v___x_444_; uint32_t v___x_445_; uint8_t v___x_446_; 
v___x_444_ = 48;
v___x_445_ = lean_unbox_uint32(v_val_439_);
v___x_446_ = lean_uint32_dec_le(v___x_444_, v___x_445_);
if (v___x_446_ == 0)
{
uint32_t v___x_447_; 
v___x_447_ = lean_unbox_uint32(v_val_439_);
lean_dec(v_val_439_);
v___y_428_ = v___x_447_;
v___y_429_ = v___x_443_;
v___y_430_ = v___x_446_;
goto v___jp_427_;
}
else
{
uint32_t v___x_448_; uint32_t v___x_449_; uint8_t v___x_450_; uint32_t v___x_451_; 
v___x_448_ = 57;
v___x_449_ = lean_unbox_uint32(v_val_439_);
v___x_450_ = lean_uint32_dec_le(v___x_449_, v___x_448_);
v___x_451_ = lean_unbox_uint32(v_val_439_);
lean_dec(v_val_439_);
v___y_428_ = v___x_451_;
v___y_429_ = v___x_443_;
v___y_430_ = v___x_450_;
goto v___jp_427_;
}
}
}
}
v___jp_452_:
{
if (v___y_453_ == 0)
{
lean_dec(v_chars_435_);
return v___y_453_;
}
else
{
goto v___jp_436_;
}
}
v___jp_454_:
{
uint32_t v___x_456_; uint8_t v___x_457_; 
v___x_456_ = 97;
v___x_457_ = lean_uint32_dec_le(v___x_456_, v___y_455_);
if (v___x_457_ == 0)
{
v___y_453_ = v___x_457_;
goto v___jp_452_;
}
else
{
uint32_t v___x_458_; uint8_t v___x_459_; 
v___x_458_ = 122;
v___x_459_ = lean_uint32_dec_le(v___y_455_, v___x_458_);
v___y_453_ = v___x_459_;
goto v___jp_452_;
}
}
v___jp_460_:
{
if (v___y_463_ == 0)
{
uint32_t v___x_464_; uint8_t v___x_465_; 
v___x_464_ = 65;
v___x_465_ = lean_uint32_dec_le(v___x_464_, v___y_462_);
if (v___x_465_ == 0)
{
v___y_455_ = v___y_462_;
goto v___jp_454_;
}
else
{
uint32_t v___x_466_; uint8_t v___x_467_; 
v___x_466_ = 90;
v___x_467_ = lean_uint32_dec_le(v___y_462_, v___x_466_);
if (v___x_467_ == 0)
{
v___y_455_ = v___y_462_;
goto v___jp_454_;
}
else
{
v___y_453_ = v___y_461_;
goto v___jp_452_;
}
}
}
else
{
goto v___jp_436_;
}
}
v___jp_468_:
{
if (v___y_469_ == 0)
{
lean_dec(v_chars_435_);
return v___y_469_;
}
else
{
lean_object* v___x_470_; 
v___x_470_ = l_List_head_x3f___redArg(v_chars_435_);
if (lean_obj_tag(v___x_470_) == 0)
{
uint8_t v___x_471_; 
lean_dec(v_chars_435_);
v___x_471_ = 0;
return v___x_471_;
}
else
{
lean_object* v_val_472_; uint32_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_val_472_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_val_472_);
lean_dec_ref(v___x_470_);
v___x_473_ = lean_unbox_uint32(v_val_472_);
v___x_474_ = lean_uint32_to_nat(v___x_473_);
v___x_475_ = lean_unsigned_to_nat(128u);
v___x_476_ = lean_nat_dec_lt(v___x_474_, v___x_475_);
lean_dec(v___x_474_);
if (v___x_476_ == 0)
{
lean_dec(v_val_472_);
v___y_453_ = v___x_476_;
goto v___jp_452_;
}
else
{
uint32_t v___x_477_; uint32_t v___x_478_; uint8_t v___x_479_; 
v___x_477_ = 48;
v___x_478_ = lean_unbox_uint32(v_val_472_);
v___x_479_ = lean_uint32_dec_le(v___x_477_, v___x_478_);
if (v___x_479_ == 0)
{
uint32_t v___x_480_; 
v___x_480_ = lean_unbox_uint32(v_val_472_);
lean_dec(v_val_472_);
v___y_461_ = v___x_476_;
v___y_462_ = v___x_480_;
v___y_463_ = v___x_479_;
goto v___jp_460_;
}
else
{
uint32_t v___x_481_; uint32_t v___x_482_; uint8_t v___x_483_; uint32_t v___x_484_; 
v___x_481_ = 57;
v___x_482_ = lean_unbox_uint32(v_val_472_);
v___x_483_ = lean_uint32_dec_le(v___x_482_, v___x_481_);
v___x_484_ = lean_unbox_uint32(v_val_472_);
lean_dec(v_val_472_);
v___y_461_ = v___x_476_;
v___y_462_ = v___x_484_;
v___y_463_ = v___x_483_;
goto v___jp_460_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidDomainLabel___boxed(lean_object* v_s_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l_Std_Http_URI_isValidDomainLabel(v_s_491_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(lean_object* v_s_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0));
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___boxed(lean_object* v_s_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(v_s_498_);
lean_dec_ref(v_s_498_);
return v_res_499_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(lean_object* v___x_500_, lean_object* v_lower_501_, lean_object* v___x_502_, lean_object* v_a_503_, uint8_t v_b_504_){
_start:
{
if (lean_obj_tag(v_a_503_) == 0)
{
lean_object* v_currPos_505_; lean_object* v_searcher_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_524_; 
v_currPos_505_ = lean_ctor_get(v_a_503_, 0);
v_searcher_506_ = lean_ctor_get(v_a_503_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_a_503_);
if (v_isSharedCheck_524_ == 0)
{
v___x_508_ = v_a_503_;
v_isShared_509_ = v_isSharedCheck_524_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_searcher_506_);
lean_inc(v_currPos_505_);
lean_dec(v_a_503_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_524_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v_startInclusive_510_; lean_object* v_endExclusive_511_; lean_object* v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_startInclusive_510_ = lean_ctor_get(v___x_502_, 1);
v_endExclusive_511_ = lean_ctor_get(v___x_502_, 2);
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = lean_nat_dec_eq(v___x_500_, v___x_512_);
v___x_514_ = lean_nat_sub(v_endExclusive_511_, v_startInclusive_510_);
v___x_515_ = lean_nat_dec_eq(v_searcher_506_, v___x_514_);
lean_dec(v___x_514_);
if (v___x_515_ == 0)
{
uint32_t v___x_516_; uint32_t v___x_517_; uint8_t v___x_518_; 
v___x_516_ = 46;
v___x_517_ = lean_string_utf8_get_fast(v_lower_501_, v_searcher_506_);
v___x_518_ = lean_uint32_dec_eq(v___x_517_, v___x_516_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = lean_string_utf8_next_fast(v_lower_501_, v_searcher_506_);
lean_dec(v_searcher_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v___x_519_);
v___x_521_ = v___x_508_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_currPos_505_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v___x_519_);
v___x_521_ = v_reuseFailAlloc_523_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
v_a_503_ = v___x_521_;
goto _start;
}
}
else
{
lean_del_object(v___x_508_);
lean_dec(v_searcher_506_);
lean_dec(v_currPos_505_);
return v___x_513_;
}
}
else
{
lean_del_object(v___x_508_);
lean_dec(v_searcher_506_);
lean_dec(v_currPos_505_);
return v___x_513_;
}
}
}
else
{
return v_b_504_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg___boxed(lean_object* v___x_525_, lean_object* v_lower_526_, lean_object* v___x_527_, lean_object* v_a_528_, lean_object* v_b_529_){
_start:
{
uint8_t v_b_boxed_530_; uint8_t v_res_531_; lean_object* v_r_532_; 
v_b_boxed_530_ = lean_unbox(v_b_529_);
v_res_531_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_525_, v_lower_526_, v___x_527_, v_a_528_, v_b_boxed_530_);
lean_dec_ref(v___x_527_);
lean_dec_ref(v_lower_526_);
lean_dec(v___x_525_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(lean_object* v_lower_533_, lean_object* v___x_534_, lean_object* v___x_535_, lean_object* v_a_536_, uint8_t v_b_537_){
_start:
{
if (lean_obj_tag(v_a_536_) == 0)
{
lean_object* v_currPos_538_; lean_object* v_searcher_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_573_; 
v_currPos_538_ = lean_ctor_get(v_a_536_, 0);
v_searcher_539_ = lean_ctor_get(v_a_536_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_a_536_);
if (v_isSharedCheck_573_ == 0)
{
v___x_541_ = v_a_536_;
v_isShared_542_ = v_isSharedCheck_573_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_searcher_539_);
lean_inc(v_currPos_538_);
lean_dec(v_a_536_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_573_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_startInclusive_543_; lean_object* v_endExclusive_544_; uint8_t v___x_545_; lean_object* v_it_547_; lean_object* v_startInclusive_548_; lean_object* v_endExclusive_549_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_startInclusive_543_ = lean_ctor_get(v___x_534_, 1);
v_endExclusive_544_ = lean_ctor_get(v___x_534_, 2);
v___x_545_ = 1;
v___x_553_ = lean_nat_sub(v_endExclusive_544_, v_startInclusive_543_);
v___x_554_ = lean_nat_dec_eq(v_searcher_539_, v___x_553_);
lean_dec(v___x_553_);
if (v___x_554_ == 0)
{
uint32_t v___x_555_; uint32_t v___x_556_; uint8_t v___x_557_; 
v___x_555_ = 46;
v___x_556_ = lean_string_utf8_get_fast(v_lower_533_, v_searcher_539_);
v___x_557_ = lean_uint32_dec_eq(v___x_556_, v___x_555_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = lean_string_utf8_next_fast(v_lower_533_, v_searcher_539_);
lean_dec(v_searcher_539_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v___x_558_);
v___x_560_ = v___x_541_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_currPos_538_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_558_);
v___x_560_ = v_reuseFailAlloc_562_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
v_a_536_ = v___x_560_;
goto _start;
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v_slice_566_; lean_object* v_nextIt_568_; 
v___x_563_ = lean_string_utf8_next_fast(v_lower_533_, v_searcher_539_);
v___x_564_ = lean_nat_sub(v___x_563_, v_searcher_539_);
v___x_565_ = lean_nat_add(v_searcher_539_, v___x_564_);
lean_dec(v___x_564_);
v_slice_566_ = l_String_Slice_subslice_x21(v___x_534_, v_currPos_538_, v_searcher_539_);
lean_inc(v___x_565_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v___x_565_);
lean_ctor_set(v___x_541_, 0, v___x_565_);
v_nextIt_568_ = v___x_541_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_565_);
v_nextIt_568_ = v_reuseFailAlloc_571_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v_startInclusive_569_; lean_object* v_endExclusive_570_; 
v_startInclusive_569_ = lean_ctor_get(v_slice_566_, 0);
lean_inc(v_startInclusive_569_);
v_endExclusive_570_ = lean_ctor_get(v_slice_566_, 1);
lean_inc(v_endExclusive_570_);
lean_dec_ref(v_slice_566_);
v_it_547_ = v_nextIt_568_;
v_startInclusive_548_ = v_startInclusive_569_;
v_endExclusive_549_ = v_endExclusive_570_;
goto v___jp_546_;
}
}
}
else
{
lean_object* v___x_572_; 
lean_del_object(v___x_541_);
lean_dec(v_searcher_539_);
v___x_572_ = lean_box(1);
lean_inc(v___x_535_);
v_it_547_ = v___x_572_;
v_startInclusive_548_ = v_currPos_538_;
v_endExclusive_549_ = v___x_535_;
goto v___jp_546_;
}
v___jp_546_:
{
lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_550_ = lean_string_utf8_extract(v_lower_533_, v_startInclusive_548_, v_endExclusive_549_);
lean_dec(v_endExclusive_549_);
lean_dec(v_startInclusive_548_);
v___x_551_ = l_Std_Http_URI_isValidDomainLabel(v___x_550_);
if (v___x_551_ == 0)
{
lean_dec(v_it_547_);
lean_dec(v___x_535_);
return v___x_551_;
}
else
{
v_a_536_ = v_it_547_;
v_b_537_ = v___x_545_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_535_);
return v_b_537_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg___boxed(lean_object* v_lower_574_, lean_object* v___x_575_, lean_object* v___x_576_, lean_object* v_a_577_, lean_object* v_b_578_){
_start:
{
uint8_t v_b_boxed_579_; uint8_t v_res_580_; lean_object* v_r_581_; 
v_b_boxed_579_ = lean_unbox(v_b_578_);
v_res_580_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v_lower_574_, v___x_575_, v___x_576_, v_a_577_, v_b_boxed_579_);
lean_dec_ref(v___x_575_);
lean_dec_ref(v_lower_574_);
v_r_581_ = lean_box(v_res_580_);
return v_r_581_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_DomainName_ofString_x3f(lean_object* v_s_582_){
_start:
{
lean_object* v___x_583_; lean_object* v_lower_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_583_ = lean_unsigned_to_nat(0u);
v_lower_584_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_582_, v___x_583_);
v___x_585_ = lean_string_utf8_byte_size(v_lower_584_);
v___x_586_ = lean_nat_dec_eq(v___x_585_, v___x_583_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; uint8_t v___x_590_; 
lean_inc_ref(v_lower_584_);
v___x_587_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_587_, 0, v_lower_584_);
lean_ctor_set(v___x_587_, 1, v___x_583_);
lean_ctor_set(v___x_587_, 2, v___x_585_);
v___x_588_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(v___x_587_);
v___x_589_ = 1;
lean_inc(v___x_588_);
v___x_590_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_585_, v_lower_584_, v___x_587_, v___x_588_, v___x_589_);
if (v___x_590_ == 0)
{
uint8_t v___x_591_; 
v___x_591_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v_lower_584_, v___x_587_, v___x_585_, v___x_588_, v___x_589_);
lean_dec_ref(v___x_587_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
lean_dec_ref(v_lower_584_);
v___x_592_ = lean_box(0);
return v___x_592_;
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_593_ = lean_string_length(v_lower_584_);
v___x_594_ = lean_unsigned_to_nat(255u);
v___x_595_ = lean_nat_dec_le(v___x_593_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
lean_dec_ref(v_lower_584_);
v___x_596_ = lean_box(0);
return v___x_596_;
}
else
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v_lower_584_);
return v___x_597_;
}
}
}
else
{
lean_object* v___x_598_; 
lean_dec(v___x_588_);
lean_dec_ref(v___x_587_);
lean_dec_ref(v_lower_584_);
v___x_598_ = lean_box(0);
return v___x_598_;
}
}
else
{
lean_object* v___x_599_; 
lean_dec_ref(v_lower_584_);
v___x_599_ = lean_box(0);
return v___x_599_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(lean_object* v_lower_600_, lean_object* v___x_601_, lean_object* v___x_602_, lean_object* v_inst_603_, lean_object* v_R_604_, lean_object* v_a_605_, uint8_t v_b_606_, lean_object* v_c_607_){
_start:
{
uint8_t v___x_608_; 
v___x_608_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v_lower_600_, v___x_601_, v___x_602_, v_a_605_, v_b_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___boxed(lean_object* v_lower_609_, lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v_inst_612_, lean_object* v_R_613_, lean_object* v_a_614_, lean_object* v_b_615_, lean_object* v_c_616_){
_start:
{
uint8_t v_b_boxed_617_; uint8_t v_res_618_; lean_object* v_r_619_; 
v_b_boxed_617_ = lean_unbox(v_b_615_);
v_res_618_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(v_lower_609_, v___x_610_, v___x_611_, v_inst_612_, v_R_613_, v_a_614_, v_b_boxed_617_, v_c_616_);
lean_dec_ref(v___x_610_);
lean_dec_ref(v_lower_609_);
v_r_619_ = lean_box(v_res_618_);
return v_r_619_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(lean_object* v___x_620_, lean_object* v_lower_621_, lean_object* v___x_622_, lean_object* v___x_623_, lean_object* v_inst_624_, lean_object* v_R_625_, lean_object* v_a_626_, uint8_t v_b_627_, lean_object* v_c_628_){
_start:
{
uint8_t v___x_629_; 
v___x_629_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_620_, v_lower_621_, v___x_622_, v_a_626_, v_b_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___boxed(lean_object* v___x_630_, lean_object* v_lower_631_, lean_object* v___x_632_, lean_object* v___x_633_, lean_object* v_inst_634_, lean_object* v_R_635_, lean_object* v_a_636_, lean_object* v_b_637_, lean_object* v_c_638_){
_start:
{
uint8_t v_b_boxed_639_; uint8_t v_res_640_; lean_object* v_r_641_; 
v_b_boxed_639_ = lean_unbox(v_b_637_);
v_res_640_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(v___x_630_, v_lower_631_, v___x_632_, v___x_633_, v_inst_634_, v_R_635_, v_a_636_, v_b_boxed_639_, v_c_638_);
lean_dec(v___x_633_);
lean_dec_ref(v___x_632_);
lean_dec_ref(v_lower_631_);
lean_dec(v___x_630_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx(lean_object* v_x_642_){
_start:
{
switch(lean_obj_tag(v_x_642_))
{
case 0:
{
lean_object* v___x_643_; 
v___x_643_ = lean_unsigned_to_nat(0u);
return v___x_643_;
}
case 1:
{
lean_object* v___x_644_; 
v___x_644_ = lean_unsigned_to_nat(1u);
return v___x_644_;
}
default: 
{
lean_object* v___x_645_; 
v___x_645_ = lean_unsigned_to_nat(2u);
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx___boxed(lean_object* v_x_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Std_Http_URI_Host_ctorIdx(v_x_646_);
lean_dec_ref(v_x_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___redArg(lean_object* v_t_648_, lean_object* v_k_649_){
_start:
{
lean_object* v_name_650_; lean_object* v___x_651_; 
v_name_650_ = lean_ctor_get(v_t_648_, 0);
lean_inc_ref(v_name_650_);
lean_dec_ref(v_t_648_);
v___x_651_ = lean_apply_1(v_k_649_, v_name_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim(lean_object* v_motive_652_, lean_object* v_ctorIdx_653_, lean_object* v_t_654_, lean_object* v_h_655_, lean_object* v_k_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_654_, v_k_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___boxed(lean_object* v_motive_658_, lean_object* v_ctorIdx_659_, lean_object* v_t_660_, lean_object* v_h_661_, lean_object* v_k_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Std_Http_URI_Host_ctorElim(v_motive_658_, v_ctorIdx_659_, v_t_660_, v_h_661_, v_k_662_);
lean_dec(v_ctorIdx_659_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim___redArg(lean_object* v_t_664_, lean_object* v_name_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_664_, v_name_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim(lean_object* v_motive_667_, lean_object* v_t_668_, lean_object* v_h_669_, lean_object* v_name_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_668_, v_name_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim___redArg(lean_object* v_t_672_, lean_object* v_ipv4_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_672_, v_ipv4_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim(lean_object* v_motive_675_, lean_object* v_t_676_, lean_object* v_h_677_, lean_object* v_ipv4_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_676_, v_ipv4_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim___redArg(lean_object* v_t_680_, lean_object* v_ipv6_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_680_, v_ipv6_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim(lean_object* v_motive_683_, lean_object* v_t_684_, lean_object* v_h_685_, lean_object* v_ipv6_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_684_, v_ipv6_686_);
return v___x_687_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default___closed__0(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default(void){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = lean_obj_once(&l_Std_Http_URI_instInhabitedHost_default___closed__0, &l_Std_Http_URI_instInhabitedHost_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedHost_default___closed__0);
return v___x_690_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost(void){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Std_Http_URI_instInhabitedHost_default;
return v___x_691_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqHost_beq(lean_object* v_x_692_, lean_object* v_x_693_){
_start:
{
switch(lean_obj_tag(v_x_692_))
{
case 0:
{
if (lean_obj_tag(v_x_693_) == 0)
{
lean_object* v_name_694_; lean_object* v_name_695_; uint8_t v___x_696_; 
v_name_694_ = lean_ctor_get(v_x_692_, 0);
v_name_695_ = lean_ctor_get(v_x_693_, 0);
v___x_696_ = lean_string_dec_eq(v_name_694_, v_name_695_);
return v___x_696_;
}
else
{
uint8_t v___x_697_; 
v___x_697_ = 0;
return v___x_697_;
}
}
case 1:
{
if (lean_obj_tag(v_x_693_) == 1)
{
lean_object* v_ipv4_698_; lean_object* v_ipv4_699_; uint8_t v___x_700_; 
v_ipv4_698_ = lean_ctor_get(v_x_692_, 0);
v_ipv4_699_ = lean_ctor_get(v_x_693_, 0);
v___x_700_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_ipv4_698_, v_ipv4_699_);
return v___x_700_;
}
else
{
uint8_t v___x_701_; 
v___x_701_ = 0;
return v___x_701_;
}
}
default: 
{
if (lean_obj_tag(v_x_693_) == 2)
{
lean_object* v_ipv6_702_; lean_object* v_ipv6_703_; uint8_t v___x_704_; 
v_ipv6_702_ = lean_ctor_get(v_x_692_, 0);
v_ipv6_703_ = lean_ctor_get(v_x_693_, 0);
v___x_704_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_ipv6_702_, v_ipv6_703_);
return v___x_704_;
}
else
{
uint8_t v___x_705_; 
v___x_705_ = 0;
return v___x_705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqHost_beq___boxed(lean_object* v_x_706_, lean_object* v_x_707_){
_start:
{
uint8_t v_res_708_; lean_object* v_r_709_; 
v_res_708_ = l_Std_Http_URI_instBEqHost_beq(v_x_706_, v_x_707_);
lean_dec_ref(v_x_707_);
lean_dec_ref(v_x_706_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__4(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_unsigned_to_nat(2u);
v___x_717_ = lean_nat_to_int(v___x_716_);
return v___x_717_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__5(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_nat_to_int(v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0(lean_object* v_x_720_, lean_object* v_prec_721_){
_start:
{
lean_object* v___y_723_; lean_object* v_ctr_724_; lean_object* v_a_725_; lean_object* v___y_737_; lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(1024u);
v___x_769_ = lean_nat_dec_le(v___x_768_, v_prec_721_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
v___x_770_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_737_ = v___x_770_;
goto v___jp_736_;
}
else
{
lean_object* v___x_771_; 
v___x_771_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_737_ = v___x_771_;
goto v___jp_736_;
}
v___jp_722_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_726_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_727_ = lean_string_append(v___x_726_, v_ctr_724_);
v___x_728_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
v___x_729_ = lean_box(1);
v___x_730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v_a_725_);
lean_inc(v___y_723_);
v___x_732_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_732_, 0, v___y_723_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = 0;
v___x_734_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set_uint8(v___x_734_, sizeof(void*)*1, v___x_733_);
v___x_735_ = l_Repr_addAppParen(v___x_734_, v_prec_721_);
return v___x_735_;
}
v___jp_736_:
{
switch(lean_obj_tag(v_x_720_))
{
case 0:
{
lean_object* v_name_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_747_; 
v_name_738_ = lean_ctor_get(v_x_720_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v_x_720_);
if (v_isSharedCheck_747_ == 0)
{
v___x_740_ = v_x_720_;
v_isShared_741_ = v_isSharedCheck_747_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_name_738_);
lean_dec(v_x_720_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_747_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_742_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_743_ = l_String_quote(v_name_738_);
if (v_isShared_741_ == 0)
{
lean_ctor_set_tag(v___x_740_, 3);
lean_ctor_set(v___x_740_, 0, v___x_743_);
v___x_745_ = v___x_740_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
v___y_723_ = v___y_737_;
v_ctr_724_ = v___x_742_;
v_a_725_ = v___x_745_;
goto v___jp_722_;
}
}
}
case 1:
{
lean_object* v_ipv4_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_757_; 
v_ipv4_748_ = lean_ctor_get(v_x_720_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v_x_720_);
if (v_isSharedCheck_757_ == 0)
{
v___x_750_ = v_x_720_;
v_isShared_751_ = v_isSharedCheck_757_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_ipv4_748_);
lean_dec(v_x_720_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_757_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_752_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_753_ = lean_uv_ntop_v4(v_ipv4_748_);
lean_dec_ref(v_ipv4_748_);
if (v_isShared_751_ == 0)
{
lean_ctor_set_tag(v___x_750_, 3);
lean_ctor_set(v___x_750_, 0, v___x_753_);
v___x_755_ = v___x_750_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
v___y_723_ = v___y_737_;
v_ctr_724_ = v___x_752_;
v_a_725_ = v___x_755_;
goto v___jp_722_;
}
}
}
default: 
{
lean_object* v_ipv6_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_767_; 
v_ipv6_758_ = lean_ctor_get(v_x_720_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v_x_720_);
if (v_isSharedCheck_767_ == 0)
{
v___x_760_ = v_x_720_;
v_isShared_761_ = v_isSharedCheck_767_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_ipv6_758_);
lean_dec(v_x_720_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_767_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_762_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_763_ = lean_uv_ntop_v6(v_ipv6_758_);
lean_dec_ref(v_ipv6_758_);
if (v_isShared_761_ == 0)
{
lean_ctor_set_tag(v___x_760_, 3);
lean_ctor_set(v___x_760_, 0, v___x_763_);
v___x_765_ = v___x_760_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
v___y_723_ = v___y_737_;
v_ctr_724_ = v___x_762_;
v_a_725_ = v___x_765_;
goto v___jp_722_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0___boxed(lean_object* v_x_772_, lean_object* v_prec_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_Http_URI_instReprHost___lam__0(v_x_772_, v_prec_773_);
lean_dec(v_prec_773_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0(lean_object* v_x_779_){
_start:
{
switch(lean_obj_tag(v_x_779_))
{
case 0:
{
lean_object* v_name_780_; 
v_name_780_ = lean_ctor_get(v_x_779_, 0);
lean_inc_ref(v_name_780_);
return v_name_780_;
}
case 1:
{
lean_object* v_ipv4_781_; lean_object* v___x_782_; 
v_ipv4_781_ = lean_ctor_get(v_x_779_, 0);
v___x_782_ = lean_uv_ntop_v4(v_ipv4_781_);
return v___x_782_;
}
default: 
{
lean_object* v_ipv6_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_ipv6_783_ = lean_ctor_get(v_x_779_, 0);
v___x_784_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_785_ = lean_uv_ntop_v6(v_ipv6_783_);
v___x_786_ = lean_string_append(v___x_784_, v___x_785_);
lean_dec_ref(v___x_785_);
v___x_787_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_788_ = lean_string_append(v___x_786_, v___x_787_);
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0___boxed(lean_object* v_x_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Std_Http_URI_instToStringHost___lam__0(v_x_789_);
lean_dec_ref(v_x_789_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx(lean_object* v_x_793_){
_start:
{
switch(lean_obj_tag(v_x_793_))
{
case 0:
{
lean_object* v___x_794_; 
v___x_794_ = lean_unsigned_to_nat(0u);
return v___x_794_;
}
case 1:
{
lean_object* v___x_795_; 
v___x_795_ = lean_unsigned_to_nat(1u);
return v___x_795_;
}
default: 
{
lean_object* v___x_796_; 
v___x_796_ = lean_unsigned_to_nat(2u);
return v___x_796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___boxed(lean_object* v_x_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Std_Http_URI_Port_ctorIdx(v_x_797_);
lean_dec(v_x_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg(lean_object* v_t_799_, lean_object* v_k_800_){
_start:
{
if (lean_obj_tag(v_t_799_) == 2)
{
uint16_t v_port_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_port_801_ = lean_ctor_get_uint16(v_t_799_, 0);
v___x_802_ = lean_box(v_port_801_);
v___x_803_ = lean_apply_1(v_k_800_, v___x_802_);
return v___x_803_;
}
else
{
return v_k_800_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg___boxed(lean_object* v_t_804_, lean_object* v_k_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_804_, v_k_805_);
lean_dec(v_t_804_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim(lean_object* v_motive_807_, lean_object* v_ctorIdx_808_, lean_object* v_t_809_, lean_object* v_h_810_, lean_object* v_k_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_809_, v_k_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___boxed(lean_object* v_motive_813_, lean_object* v_ctorIdx_814_, lean_object* v_t_815_, lean_object* v_h_816_, lean_object* v_k_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_Http_URI_Port_ctorElim(v_motive_813_, v_ctorIdx_814_, v_t_815_, v_h_816_, v_k_817_);
lean_dec(v_t_815_);
lean_dec(v_ctorIdx_814_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg(lean_object* v_t_819_, lean_object* v_omitted_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_819_, v_omitted_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg___boxed(lean_object* v_t_822_, lean_object* v_omitted_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_Http_URI_Port_omitted_elim___redArg(v_t_822_, v_omitted_823_);
lean_dec(v_t_822_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim(lean_object* v_motive_825_, lean_object* v_t_826_, lean_object* v_h_827_, lean_object* v_omitted_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_826_, v_omitted_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___boxed(lean_object* v_motive_830_, lean_object* v_t_831_, lean_object* v_h_832_, lean_object* v_omitted_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Std_Http_URI_Port_omitted_elim(v_motive_830_, v_t_831_, v_h_832_, v_omitted_833_);
lean_dec(v_t_831_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg(lean_object* v_t_835_, lean_object* v_empty_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_835_, v_empty_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg___boxed(lean_object* v_t_838_, lean_object* v_empty_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_Http_URI_Port_empty_elim___redArg(v_t_838_, v_empty_839_);
lean_dec(v_t_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim(lean_object* v_motive_841_, lean_object* v_t_842_, lean_object* v_h_843_, lean_object* v_empty_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_842_, v_empty_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___boxed(lean_object* v_motive_846_, lean_object* v_t_847_, lean_object* v_h_848_, lean_object* v_empty_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Std_Http_URI_Port_empty_elim(v_motive_846_, v_t_847_, v_h_848_, v_empty_849_);
lean_dec(v_t_847_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg(lean_object* v_t_851_, lean_object* v_value_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_851_, v_value_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg___boxed(lean_object* v_t_854_, lean_object* v_value_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_Http_URI_Port_value_elim___redArg(v_t_854_, v_value_855_);
lean_dec(v_t_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim(lean_object* v_motive_857_, lean_object* v_t_858_, lean_object* v_h_859_, lean_object* v_value_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_858_, v_value_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___boxed(lean_object* v_motive_862_, lean_object* v_t_863_, lean_object* v_h_864_, lean_object* v_value_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Std_Http_URI_Port_value_elim(v_motive_862_, v_t_863_, v_h_864_, v_value_865_);
lean_dec(v_t_863_);
return v_res_866_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort_default(void){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = lean_box(0);
return v___x_867_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort(void){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = lean_box(0);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr(lean_object* v_x_881_, lean_object* v_prec_882_){
_start:
{
lean_object* v___y_884_; lean_object* v___y_891_; 
switch(lean_obj_tag(v_x_881_))
{
case 0:
{
lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_897_ = lean_unsigned_to_nat(1024u);
v___x_898_ = lean_nat_dec_le(v___x_897_, v_prec_882_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; 
v___x_899_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_891_ = v___x_899_;
goto v___jp_890_;
}
else
{
lean_object* v___x_900_; 
v___x_900_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_891_ = v___x_900_;
goto v___jp_890_;
}
}
case 1:
{
lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_901_ = lean_unsigned_to_nat(1024u);
v___x_902_ = lean_nat_dec_le(v___x_901_, v_prec_882_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
v___x_903_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_884_ = v___x_903_;
goto v___jp_883_;
}
else
{
lean_object* v___x_904_; 
v___x_904_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_884_ = v___x_904_;
goto v___jp_883_;
}
}
default: 
{
uint16_t v_port_905_; lean_object* v___y_907_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_port_905_ = lean_ctor_get_uint16(v_x_881_, 0);
v___x_917_ = lean_unsigned_to_nat(1024u);
v___x_918_ = lean_nat_dec_le(v___x_917_, v_prec_882_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
v___x_919_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_907_ = v___x_919_;
goto v___jp_906_;
}
else
{
lean_object* v___x_920_; 
v___x_920_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_907_ = v___x_920_;
goto v___jp_906_;
}
v___jp_906_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_908_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__6));
v___x_909_ = lean_uint16_to_nat(v_port_905_);
v___x_910_ = l_Nat_reprFast(v___x_909_);
v___x_911_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
v___x_912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_908_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
lean_inc(v___y_907_);
v___x_913_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_913_, 0, v___y_907_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = 0;
v___x_915_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*1, v___x_914_);
v___x_916_ = l_Repr_addAppParen(v___x_915_, v_prec_882_);
return v___x_916_;
}
}
}
v___jp_883_:
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_885_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__1));
lean_inc(v___y_884_);
v___x_886_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_886_, 0, v___y_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = 0;
v___x_888_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set_uint8(v___x_888_, sizeof(void*)*1, v___x_887_);
v___x_889_ = l_Repr_addAppParen(v___x_888_, v_prec_882_);
return v___x_889_;
}
v___jp_890_:
{
lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_892_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__3));
lean_inc(v___y_891_);
v___x_893_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_893_, 0, v___y_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = 0;
v___x_895_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set_uint8(v___x_895_, sizeof(void*)*1, v___x_894_);
v___x_896_ = l_Repr_addAppParen(v___x_895_, v_prec_882_);
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr___boxed(lean_object* v_x_921_, lean_object* v_prec_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_Http_URI_instReprPort_repr(v_x_921_, v_prec_922_);
lean_dec(v_prec_922_);
lean_dec(v_x_921_);
return v_res_923_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort_decEq(lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
switch(lean_obj_tag(v_x_926_))
{
case 0:
{
if (lean_obj_tag(v_x_927_) == 0)
{
uint8_t v___x_928_; 
v___x_928_ = 1;
return v___x_928_;
}
else
{
uint8_t v___x_929_; 
v___x_929_ = 0;
return v___x_929_;
}
}
case 1:
{
if (lean_obj_tag(v_x_927_) == 1)
{
uint8_t v___x_930_; 
v___x_930_ = 1;
return v___x_930_;
}
else
{
uint8_t v___x_931_; 
v___x_931_ = 0;
return v___x_931_;
}
}
default: 
{
uint16_t v_port_932_; uint8_t v___x_933_; 
v_port_932_ = lean_ctor_get_uint16(v_x_926_, 0);
v___x_933_ = 0;
if (lean_obj_tag(v_x_927_) == 2)
{
uint16_t v_port_934_; uint8_t v___x_935_; 
v_port_934_ = lean_ctor_get_uint16(v_x_927_, 0);
v___x_935_ = lean_uint16_dec_eq(v_port_932_, v_port_934_);
if (v___x_935_ == 0)
{
return v___x_933_;
}
else
{
return v___x_935_;
}
}
else
{
return v___x_933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort_decEq___boxed(lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
uint8_t v_res_938_; lean_object* v_r_939_; 
v_res_938_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_936_, v_x_937_);
lean_dec(v_x_937_);
lean_dec(v_x_936_);
v_r_939_ = lean_box(v_res_938_);
return v_r_939_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort(lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
uint8_t v___x_942_; 
v___x_942_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_940_, v_x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort___boxed(lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
uint8_t v_res_945_; lean_object* v_r_946_; 
v_res_945_ = l_Std_Http_URI_instDecidableEqPort(v_x_943_, v_x_944_);
lean_dec(v_x_944_);
lean_dec(v_x_943_);
v_r_946_ = lean_box(v_res_945_);
return v_r_946_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_947_ = lean_box(0);
v___x_948_ = l_Std_Http_URI_instInhabitedHost_default;
v___x_949_ = lean_box(0);
v___x_950_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___x_948_);
lean_ctor_set(v___x_950_, 2, v___x_947_);
return v___x_950_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default(void){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = lean_obj_once(&l_Std_Http_URI_instInhabitedAuthority_default___closed__0, &l_Std_Http_URI_instInhabitedAuthority_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0);
return v___x_951_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority(void){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Std_Http_URI_instInhabitedAuthority_default;
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
if (lean_obj_tag(v_x_953_) == 0)
{
lean_object* v___x_955_; 
v___x_955_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_955_;
}
else
{
lean_object* v_val_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_val_956_ = lean_ctor_get(v_x_953_, 0);
lean_inc(v_val_956_);
lean_dec_ref(v_x_953_);
v___x_957_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_958_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_val_956_);
v___x_959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = l_Repr_addAppParen(v___x_959_, v_x_954_);
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0___boxed(lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_x_961_, v_x_962_);
lean_dec(v_x_962_);
return v_res_963_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_unsigned_to_nat(8u);
v___x_977_ = lean_nat_to_int(v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg(lean_object* v_x_981_){
_start:
{
lean_object* v_userInfo_982_; lean_object* v_host_983_; lean_object* v_port_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v_ctr_1004_; lean_object* v_a_1005_; 
v_userInfo_982_ = lean_ctor_get(v_x_981_, 0);
lean_inc(v_userInfo_982_);
v_host_983_ = lean_ctor_get(v_x_981_, 1);
lean_inc_ref(v_host_983_);
v_port_984_ = lean_ctor_get(v_x_981_, 2);
lean_inc(v_port_984_);
lean_dec_ref(v_x_981_);
v___x_985_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_986_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3));
v___x_987_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_userInfo_982_, v___x_988_);
v___x_990_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_987_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = 0;
v___x_992_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*1, v___x_991_);
v___x_993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_986_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = lean_box(1);
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_985_);
v___x_1001_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_1002_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_983_))
{
case 0:
{
lean_object* v_name_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1042_; 
v_name_1033_ = lean_ctor_get(v_host_983_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_host_983_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1035_ = v_host_983_;
v_isShared_1036_ = v_isSharedCheck_1042_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_name_1033_);
lean_dec(v_host_983_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1042_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1037_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_1038_ = l_String_quote(v_name_1033_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set_tag(v___x_1035_, 3);
lean_ctor_set(v___x_1035_, 0, v___x_1038_);
v___x_1040_ = v___x_1035_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
v_ctr_1004_ = v___x_1037_;
v_a_1005_ = v___x_1040_;
goto v___jp_1003_;
}
}
}
case 1:
{
lean_object* v_ipv4_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1052_; 
v_ipv4_1043_ = lean_ctor_get(v_host_983_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_host_983_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1045_ = v_host_983_;
v_isShared_1046_ = v_isSharedCheck_1052_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_ipv4_1043_);
lean_dec(v_host_983_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1052_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1047_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_1048_ = lean_uv_ntop_v4(v_ipv4_1043_);
lean_dec_ref(v_ipv4_1043_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 3);
lean_ctor_set(v___x_1045_, 0, v___x_1048_);
v___x_1050_ = v___x_1045_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
v_ctr_1004_ = v___x_1047_;
v_a_1005_ = v___x_1050_;
goto v___jp_1003_;
}
}
}
default: 
{
lean_object* v_ipv6_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1062_; 
v_ipv6_1053_ = lean_ctor_get(v_host_983_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_host_983_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1055_ = v_host_983_;
v_isShared_1056_ = v_isSharedCheck_1062_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_ipv6_1053_);
lean_dec(v_host_983_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1062_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1057_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_1058_ = lean_uv_ntop_v6(v_ipv6_1053_);
lean_dec_ref(v_ipv6_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 3);
lean_ctor_set(v___x_1055_, 0, v___x_1058_);
v___x_1060_ = v___x_1055_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
v_ctr_1004_ = v___x_1057_;
v_a_1005_ = v___x_1060_;
goto v___jp_1003_;
}
}
}
}
v___jp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1006_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_1007_ = lean_string_append(v___x_1006_, v_ctr_1004_);
v___x_1008_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_996_);
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v_a_1005_);
v___x_1011_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1002_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*1, v___x_991_);
v___x_1013_ = l_Repr_addAppParen(v___x_1012_, v___x_988_);
v___x_1014_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1001_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set_uint8(v___x_1015_, sizeof(void*)*1, v___x_991_);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1000_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___x_994_);
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v___x_996_);
v___x_1019_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___x_985_);
v___x_1022_ = l_Std_Http_URI_instReprPort_repr(v_port_984_, v___x_988_);
lean_dec(v_port_984_);
v___x_1023_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1001_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set_uint8(v___x_1024_, sizeof(void*)*1, v___x_991_);
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1021_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1027_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v___x_1025_);
v___x_1029_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1026_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*1, v___x_991_);
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr(lean_object* v_x_1063_, lean_object* v_prec_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_x_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___boxed(lean_object* v_x_1066_, lean_object* v_prec_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Std_Http_URI_instReprAuthority_repr(v_x_1066_, v_prec_1067_);
lean_dec(v_prec_1067_);
return v_res_1068_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
if (lean_obj_tag(v_x_1071_) == 0)
{
if (lean_obj_tag(v_x_1072_) == 0)
{
uint8_t v___x_1073_; 
v___x_1073_ = 1;
return v___x_1073_;
}
else
{
uint8_t v___x_1074_; 
v___x_1074_ = 0;
return v___x_1074_;
}
}
else
{
if (lean_obj_tag(v_x_1072_) == 0)
{
uint8_t v___x_1075_; 
v___x_1075_ = 0;
return v___x_1075_;
}
else
{
lean_object* v_val_1076_; lean_object* v_val_1077_; uint8_t v___x_1078_; 
v_val_1076_ = lean_ctor_get(v_x_1071_, 0);
v_val_1077_ = lean_ctor_get(v_x_1072_, 0);
v___x_1078_ = l_Std_Http_URI_instBEqUserInfo_beq(v_val_1076_, v_val_1077_);
return v___x_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0___boxed(lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
uint8_t v_res_1081_; lean_object* v_r_1082_; 
v_res_1081_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_x_1079_, v_x_1080_);
lean_dec(v_x_1080_);
lean_dec(v_x_1079_);
v_r_1082_ = lean_box(v_res_1081_);
return v_r_1082_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqAuthority_beq(lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v_userInfo_1085_; lean_object* v_host_1086_; lean_object* v_port_1087_; lean_object* v_userInfo_1088_; lean_object* v_host_1089_; lean_object* v_port_1090_; uint8_t v___x_1091_; 
v_userInfo_1085_ = lean_ctor_get(v_x_1083_, 0);
v_host_1086_ = lean_ctor_get(v_x_1083_, 1);
v_port_1087_ = lean_ctor_get(v_x_1083_, 2);
v_userInfo_1088_ = lean_ctor_get(v_x_1084_, 0);
v_host_1089_ = lean_ctor_get(v_x_1084_, 1);
v_port_1090_ = lean_ctor_get(v_x_1084_, 2);
v___x_1091_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_userInfo_1085_, v_userInfo_1088_);
if (v___x_1091_ == 0)
{
return v___x_1091_;
}
else
{
uint8_t v___x_1092_; 
v___x_1092_ = l_Std_Http_URI_instBEqHost_beq(v_host_1086_, v_host_1089_);
if (v___x_1092_ == 0)
{
return v___x_1092_;
}
else
{
uint8_t v___x_1093_; 
v___x_1093_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1087_, v_port_1090_);
return v___x_1093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqAuthority_beq___boxed(lean_object* v_x_1094_, lean_object* v_x_1095_){
_start:
{
uint8_t v_res_1096_; lean_object* v_r_1097_; 
v_res_1096_ = l_Std_Http_URI_instBEqAuthority_beq(v_x_1094_, v_x_1095_);
lean_dec_ref(v_x_1095_);
lean_dec_ref(v_x_1094_);
v_r_1097_ = lean_box(v_res_1096_);
return v_r_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringAuthority___lam__0(lean_object* v_auth_1103_){
_start:
{
lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v_userInfo_1110_; lean_object* v_host_1111_; lean_object* v_port_1112_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1124_; 
v_userInfo_1110_ = lean_ctor_get(v_auth_1103_, 0);
lean_inc(v_userInfo_1110_);
v_host_1111_ = lean_ctor_get(v_auth_1103_, 1);
lean_inc_ref(v_host_1111_);
v_port_1112_ = lean_ctor_get(v_auth_1103_, 2);
lean_inc(v_port_1112_);
lean_dec_ref(v_auth_1103_);
if (lean_obj_tag(v_userInfo_1110_) == 0)
{
lean_object* v___x_1134_; 
v___x_1134_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1124_ = v___x_1134_;
goto v___jp_1123_;
}
else
{
lean_object* v_val_1135_; lean_object* v_password_1136_; 
v_val_1135_ = lean_ctor_get(v_userInfo_1110_, 0);
lean_inc(v_val_1135_);
lean_dec_ref(v_userInfo_1110_);
v_password_1136_ = lean_ctor_get(v_val_1135_, 1);
if (lean_obj_tag(v_password_1136_) == 0)
{
lean_object* v_username_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_username_1137_ = lean_ctor_get(v_val_1135_, 0);
lean_inc_ref(v_username_1137_);
lean_dec(v_val_1135_);
v___x_1138_ = lean_string_from_utf8_unchecked(v_username_1137_);
v___x_1139_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1140_ = lean_string_append(v___x_1138_, v___x_1139_);
v___y_1124_ = v___x_1140_;
goto v___jp_1123_;
}
else
{
lean_object* v_username_1141_; lean_object* v_val_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_inc_ref(v_password_1136_);
v_username_1141_ = lean_ctor_get(v_val_1135_, 0);
lean_inc_ref(v_username_1141_);
lean_dec(v_val_1135_);
v_val_1142_ = lean_ctor_get(v_password_1136_, 0);
lean_inc(v_val_1142_);
lean_dec_ref(v_password_1136_);
v___x_1143_ = lean_string_from_utf8_unchecked(v_username_1141_);
v___x_1144_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1145_ = lean_string_append(v___x_1143_, v___x_1144_);
v___x_1146_ = lean_string_from_utf8_unchecked(v_val_1142_);
v___x_1147_ = lean_string_append(v___x_1145_, v___x_1146_);
lean_dec_ref(v___x_1146_);
v___x_1148_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1149_ = lean_string_append(v___x_1147_, v___x_1148_);
v___y_1124_ = v___x_1149_;
goto v___jp_1123_;
}
}
v___jp_1104_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_string_append(v___y_1106_, v___y_1105_);
lean_dec_ref(v___y_1105_);
v___x_1109_ = lean_string_append(v___x_1108_, v___y_1107_);
lean_dec_ref(v___y_1107_);
return v___x_1109_;
}
v___jp_1113_:
{
switch(lean_obj_tag(v_port_1112_))
{
case 0:
{
lean_object* v___x_1116_; 
v___x_1116_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1105_ = v___y_1115_;
v___y_1106_ = v___y_1114_;
v___y_1107_ = v___x_1116_;
goto v___jp_1104_;
}
case 1:
{
lean_object* v___x_1117_; 
v___x_1117_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_1105_ = v___y_1115_;
v___y_1106_ = v___y_1114_;
v___y_1107_ = v___x_1117_;
goto v___jp_1104_;
}
default: 
{
uint16_t v_port_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v_port_1118_ = lean_ctor_get_uint16(v_port_1112_, 0);
lean_dec_ref(v_port_1112_);
v___x_1119_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1120_ = lean_uint16_to_nat(v_port_1118_);
v___x_1121_ = l_Nat_reprFast(v___x_1120_);
v___x_1122_ = lean_string_append(v___x_1119_, v___x_1121_);
lean_dec_ref(v___x_1121_);
v___y_1105_ = v___y_1115_;
v___y_1106_ = v___y_1114_;
v___y_1107_ = v___x_1122_;
goto v___jp_1104_;
}
}
}
v___jp_1123_:
{
switch(lean_obj_tag(v_host_1111_))
{
case 0:
{
lean_object* v_name_1125_; 
v_name_1125_ = lean_ctor_get(v_host_1111_, 0);
lean_inc_ref(v_name_1125_);
lean_dec_ref(v_host_1111_);
v___y_1114_ = v___y_1124_;
v___y_1115_ = v_name_1125_;
goto v___jp_1113_;
}
case 1:
{
lean_object* v_ipv4_1126_; lean_object* v___x_1127_; 
v_ipv4_1126_ = lean_ctor_get(v_host_1111_, 0);
lean_inc_ref(v_ipv4_1126_);
lean_dec_ref(v_host_1111_);
v___x_1127_ = lean_uv_ntop_v4(v_ipv4_1126_);
lean_dec_ref(v_ipv4_1126_);
v___y_1114_ = v___y_1124_;
v___y_1115_ = v___x_1127_;
goto v___jp_1113_;
}
default: 
{
lean_object* v_ipv6_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_ipv6_1128_ = lean_ctor_get(v_host_1111_, 0);
lean_inc_ref(v_ipv6_1128_);
lean_dec_ref(v_host_1111_);
v___x_1129_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_1130_ = lean_uv_ntop_v6(v_ipv6_1128_);
lean_dec_ref(v_ipv6_1128_);
v___x_1131_ = lean_string_append(v___x_1129_, v___x_1130_);
lean_dec_ref(v___x_1130_);
v___x_1132_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_1133_ = lean_string_append(v___x_1131_, v___x_1132_);
v___y_1114_ = v___y_1124_;
v___y_1115_ = v___x_1133_;
goto v___jp_1113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1159_, lean_object* v_x_1160_, lean_object* v_x_1161_){
_start:
{
if (lean_obj_tag(v_x_1161_) == 0)
{
lean_dec(v_x_1159_);
return v_x_1160_;
}
else
{
lean_object* v_head_1162_; lean_object* v_tail_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1175_; 
v_head_1162_ = lean_ctor_get(v_x_1161_, 0);
v_tail_1163_ = lean_ctor_get(v_x_1161_, 1);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_x_1161_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1165_ = v_x_1161_;
v_isShared_1166_ = v_isSharedCheck_1175_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_tail_1163_);
lean_inc(v_head_1162_);
lean_dec(v_x_1161_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1175_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
lean_inc(v_x_1159_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set_tag(v___x_1165_, 5);
lean_ctor_set(v___x_1165_, 1, v_x_1159_);
lean_ctor_set(v___x_1165_, 0, v_x_1160_);
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_x_1160_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_x_1159_);
v___x_1168_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1169_ = lean_string_from_utf8_unchecked(v_head_1162_);
v___x_1170_ = l_String_quote(v___x_1169_);
v___x_1171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
v___x_1172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1168_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v_x_1160_ = v___x_1172_;
v_x_1161_ = v_tail_1163_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(lean_object* v_x_1176_, lean_object* v_x_1177_, lean_object* v_x_1178_){
_start:
{
if (lean_obj_tag(v_x_1178_) == 0)
{
lean_dec(v_x_1176_);
return v_x_1177_;
}
else
{
lean_object* v_head_1179_; lean_object* v_tail_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1192_; 
v_head_1179_ = lean_ctor_get(v_x_1178_, 0);
v_tail_1180_ = lean_ctor_get(v_x_1178_, 1);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_x_1178_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1182_ = v_x_1178_;
v_isShared_1183_ = v_isSharedCheck_1192_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_tail_1180_);
lean_inc(v_head_1179_);
lean_dec(v_x_1178_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1192_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
lean_inc(v_x_1176_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set_tag(v___x_1182_, 5);
lean_ctor_set(v___x_1182_, 1, v_x_1176_);
lean_ctor_set(v___x_1182_, 0, v_x_1177_);
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_x_1177_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_x_1176_);
v___x_1185_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1186_ = lean_string_from_utf8_unchecked(v_head_1179_);
v___x_1187_ = l_String_quote(v___x_1186_);
v___x_1188_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1185_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(v_x_1176_, v___x_1189_, v_tail_1180_);
return v___x_1190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = lean_string_from_utf8_unchecked(v___y_1193_);
v___x_1195_ = l_String_quote(v___x_1194_);
v___x_1196_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(lean_object* v_x_1197_, lean_object* v_x_1198_){
_start:
{
if (lean_obj_tag(v_x_1197_) == 0)
{
lean_object* v___x_1199_; 
lean_dec(v_x_1198_);
v___x_1199_ = lean_box(0);
return v___x_1199_;
}
else
{
lean_object* v_tail_1200_; 
v_tail_1200_ = lean_ctor_get(v_x_1197_, 1);
if (lean_obj_tag(v_tail_1200_) == 0)
{
lean_object* v_head_1201_; lean_object* v___x_1202_; 
lean_dec(v_x_1198_);
v_head_1201_ = lean_ctor_get(v_x_1197_, 0);
lean_inc(v_head_1201_);
lean_dec_ref(v_x_1197_);
v___x_1202_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1201_);
return v___x_1202_;
}
else
{
lean_object* v_head_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_inc(v_tail_1200_);
v_head_1203_ = lean_ctor_get(v_x_1197_, 0);
lean_inc(v_head_1203_);
lean_dec_ref(v_x_1197_);
v___x_1204_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1203_);
v___x_1205_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(v_x_1198_, v___x_1204_, v_tail_1200_);
return v___x_1205_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0));
v___x_1211_ = lean_string_length(v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2);
v___x_1213_ = lean_nat_to_int(v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(lean_object* v_xs_1221_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1222_ = lean_array_get_size(v_xs_1221_);
v___x_1223_ = lean_unsigned_to_nat(0u);
v___x_1224_ = lean_nat_dec_eq(v___x_1222_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1225_ = lean_array_to_list(v_xs_1221_);
v___x_1226_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1227_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(v___x_1225_, v___x_1226_);
v___x_1228_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1229_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v___x_1227_);
v___x_1231_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1228_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = l_Std_Format_fill(v___x_1233_);
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; 
lean_dec_ref(v_xs_1221_);
v___x_1235_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___redArg(lean_object* v_x_1248_){
_start:
{
lean_object* v_segments_1249_; uint8_t v_absolute_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1282_; 
v_segments_1249_ = lean_ctor_get(v_x_1248_, 0);
v_absolute_1250_ = lean_ctor_get_uint8(v_x_1248_, sizeof(void*)*1);
v_isSharedCheck_1282_ = !lean_is_exclusive(v_x_1248_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1252_ = v_x_1248_;
v_isShared_1253_ = v_isSharedCheck_1282_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_segments_1249_);
lean_dec(v_x_1248_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1282_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; lean_object* v___x_1261_; 
v___x_1254_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1255_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__3));
v___x_1256_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_1257_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(v_segments_1249_);
v___x_1258_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1256_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = 0;
if (v_isShared_1253_ == 0)
{
lean_ctor_set_tag(v___x_1252_, 6);
lean_ctor_set(v___x_1252_, 0, v___x_1258_);
v___x_1261_ = v___x_1252_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1258_);
v___x_1261_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_ctor_set_uint8(v___x_1261_, sizeof(void*)*1, v___x_1259_);
v___x_1262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1255_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = lean_box(1);
v___x_1266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1264_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__5));
v___x_1268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
lean_ctor_set(v___x_1269_, 1, v___x_1254_);
v___x_1270_ = l_Bool_repr___redArg(v_absolute_1250_);
v___x_1271_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1256_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set_uint8(v___x_1272_, sizeof(void*)*1, v___x_1259_);
v___x_1273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1269_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1275_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v___x_1273_);
v___x_1277_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1274_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*1, v___x_1259_);
return v___x_1280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr(lean_object* v_x_1283_, lean_object* v_prec_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Std_Http_URI_instReprPath_repr___redArg(v_x_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___boxed(lean_object* v_x_1286_, lean_object* v_prec_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Std_Http_URI_instReprPath_repr(v_x_1286_, v_prec_1287_);
lean_dec(v_prec_1287_);
return v_res_1288_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(lean_object* v_xs_1291_, lean_object* v_ys_1292_, lean_object* v_x_1293_){
_start:
{
lean_object* v_zero_1294_; uint8_t v_isZero_1295_; 
v_zero_1294_ = lean_unsigned_to_nat(0u);
v_isZero_1295_ = lean_nat_dec_eq(v_x_1293_, v_zero_1294_);
if (v_isZero_1295_ == 1)
{
lean_dec(v_x_1293_);
return v_isZero_1295_;
}
else
{
lean_object* v_one_1296_; lean_object* v_n_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; 
v_one_1296_ = lean_unsigned_to_nat(1u);
v_n_1297_ = lean_nat_sub(v_x_1293_, v_one_1296_);
lean_dec(v_x_1293_);
v___x_1298_ = lean_array_fget_borrowed(v_xs_1291_, v_n_1297_);
v___x_1299_ = lean_array_fget_borrowed(v_ys_1292_, v_n_1297_);
v___x_1300_ = lean_sarray_dec_eq(v___x_1298_, v___x_1299_);
if (v___x_1300_ == 0)
{
lean_dec(v_n_1297_);
return v___x_1300_;
}
else
{
v_x_1293_ = v_n_1297_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg___boxed(lean_object* v_xs_1302_, lean_object* v_ys_1303_, lean_object* v_x_1304_){
_start:
{
uint8_t v_res_1305_; lean_object* v_r_1306_; 
v_res_1305_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1302_, v_ys_1303_, v_x_1304_);
lean_dec_ref(v_ys_1303_);
lean_dec_ref(v_xs_1302_);
v_r_1306_ = lean_box(v_res_1305_);
return v_r_1306_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqPath_beq(lean_object* v_x_1307_, lean_object* v_x_1308_){
_start:
{
lean_object* v_segments_1309_; uint8_t v_absolute_1310_; lean_object* v_segments_1311_; uint8_t v_absolute_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v_segments_1309_ = lean_ctor_get(v_x_1307_, 0);
v_absolute_1310_ = lean_ctor_get_uint8(v_x_1307_, sizeof(void*)*1);
v_segments_1311_ = lean_ctor_get(v_x_1308_, 0);
v_absolute_1312_ = lean_ctor_get_uint8(v_x_1308_, sizeof(void*)*1);
v___x_1313_ = lean_array_get_size(v_segments_1309_);
v___x_1314_ = lean_array_get_size(v_segments_1311_);
v___x_1315_ = lean_nat_dec_eq(v___x_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
return v___x_1315_;
}
else
{
uint8_t v___x_1316_; 
v___x_1316_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_segments_1309_, v_segments_1311_, v___x_1313_);
if (v___x_1316_ == 0)
{
return v___x_1316_;
}
else
{
if (v_absolute_1310_ == 0)
{
if (v_absolute_1312_ == 0)
{
return v___x_1316_;
}
else
{
return v_absolute_1310_;
}
}
else
{
return v_absolute_1312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqPath_beq___boxed(lean_object* v_x_1317_, lean_object* v_x_1318_){
_start:
{
uint8_t v_res_1319_; lean_object* v_r_1320_; 
v_res_1319_ = l_Std_Http_URI_instBEqPath_beq(v_x_1317_, v_x_1318_);
lean_dec_ref(v_x_1318_);
lean_dec_ref(v_x_1317_);
v_r_1320_ = lean_box(v_res_1319_);
return v_r_1320_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(lean_object* v_xs_1321_, lean_object* v_ys_1322_, lean_object* v_hsz_1323_, lean_object* v_x_1324_, lean_object* v_x_1325_){
_start:
{
uint8_t v___x_1326_; 
v___x_1326_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1321_, v_ys_1322_, v_x_1324_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___boxed(lean_object* v_xs_1327_, lean_object* v_ys_1328_, lean_object* v_hsz_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_){
_start:
{
uint8_t v_res_1332_; lean_object* v_r_1333_; 
v_res_1332_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(v_xs_1327_, v_ys_1328_, v_hsz_1329_, v_x_1330_, v_x_1331_);
lean_dec_ref(v_ys_1328_);
lean_dec_ref(v_xs_1327_);
v_r_1333_ = lean_box(v_res_1332_);
return v_r_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__0(lean_object* v_x_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_string_from_utf8_unchecked(v_x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__1(lean_object* v___f_1358_, lean_object* v_path_1359_){
_start:
{
lean_object* v_segments_1360_; uint8_t v_absolute_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; size_t v_sz_1364_; size_t v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v_result_1368_; 
v_segments_1360_ = lean_ctor_get(v_path_1359_, 0);
lean_inc_ref(v_segments_1360_);
v_absolute_1361_ = lean_ctor_get_uint8(v_path_1359_, sizeof(void*)*1);
lean_dec_ref(v_path_1359_);
v___x_1362_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_1363_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_1364_ = lean_array_size(v_segments_1360_);
v___x_1365_ = ((size_t)0ULL);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1363_, v___f_1358_, v_sz_1364_, v___x_1365_, v_segments_1360_);
v___x_1367_ = lean_array_to_list(v___x_1366_);
v_result_1368_ = l_String_intercalate(v___x_1362_, v___x_1367_);
if (v_absolute_1361_ == 0)
{
return v_result_1368_;
}
else
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_string_append(v___x_1362_, v_result_1368_);
lean_dec_ref(v_result_1368_);
return v___x_1369_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Path_isEmpty(lean_object* v_p_1374_){
_start:
{
lean_object* v_segments_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v_segments_1375_ = lean_ctor_get(v_p_1374_, 0);
v___x_1376_ = lean_array_get_size(v_segments_1375_);
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = lean_nat_dec_eq(v___x_1376_, v___x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_isEmpty___boxed(lean_object* v_p_1379_){
_start:
{
uint8_t v_res_1380_; lean_object* v_r_1381_; 
v_res_1380_ = l_Std_Http_URI_Path_isEmpty(v_p_1379_);
lean_dec_ref(v_p_1379_);
v_r_1381_ = lean_box(v_res_1380_);
return v_r_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parent(lean_object* v_p_1382_){
_start:
{
lean_object* v_segments_1383_; uint8_t v_absolute_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_segments_1383_ = lean_ctor_get(v_p_1382_, 0);
v_absolute_1384_ = lean_ctor_get_uint8(v_p_1382_, sizeof(void*)*1);
v___x_1385_ = lean_array_get_size(v_segments_1383_);
v___x_1386_ = lean_unsigned_to_nat(0u);
v___x_1387_ = lean_nat_dec_eq(v___x_1385_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1395_; 
lean_inc_ref(v_segments_1383_);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_p_1382_);
if (v_isSharedCheck_1395_ == 0)
{
lean_object* v_unused_1396_; 
v_unused_1396_ = lean_ctor_get(v_p_1382_, 0);
lean_dec(v_unused_1396_);
v___x_1389_ = v_p_1382_;
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
else
{
lean_dec(v_p_1382_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = lean_array_pop(v_segments_1383_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1391_);
v___x_1393_ = v___x_1389_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
lean_ctor_set_uint8(v_reuseFailAlloc_1394_, sizeof(void*)*1, v_absolute_1384_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
else
{
return v_p_1382_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join(lean_object* v_p1_1397_, lean_object* v_p2_1398_){
_start:
{
uint8_t v_absolute_1399_; 
v_absolute_1399_ = lean_ctor_get_uint8(v_p2_1398_, sizeof(void*)*1);
if (v_absolute_1399_ == 0)
{
lean_object* v_segments_1400_; lean_object* v_segments_1401_; uint8_t v_absolute_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1410_; 
v_segments_1400_ = lean_ctor_get(v_p2_1398_, 0);
v_segments_1401_ = lean_ctor_get(v_p1_1397_, 0);
v_absolute_1402_ = lean_ctor_get_uint8(v_p1_1397_, sizeof(void*)*1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_p1_1397_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1404_ = v_p1_1397_;
v_isShared_1405_ = v_isSharedCheck_1410_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_segments_1401_);
lean_dec(v_p1_1397_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1410_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1406_ = l_Array_append___redArg(v_segments_1401_, v_segments_1400_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1406_);
v___x_1408_ = v___x_1404_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
lean_ctor_set_uint8(v_reuseFailAlloc_1409_, sizeof(void*)*1, v_absolute_1402_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
else
{
lean_dec_ref(v_p1_1397_);
lean_inc_ref(v_p2_1398_);
return v_p2_1398_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join___boxed(lean_object* v_p1_1411_, lean_object* v_p2_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Std_Http_URI_Path_join(v_p1_1411_, v_p2_1412_);
lean_dec_ref(v_p2_1412_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append(lean_object* v_p_1414_, lean_object* v_segment_1415_){
_start:
{
lean_object* v_segments_1416_; uint8_t v_absolute_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1426_; 
v_segments_1416_ = lean_ctor_get(v_p_1414_, 0);
v_absolute_1417_ = lean_ctor_get_uint8(v_p_1414_, sizeof(void*)*1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_p_1414_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1419_ = v_p_1414_;
v_isShared_1420_ = v_isSharedCheck_1426_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_segments_1416_);
lean_dec(v_p_1414_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1426_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1421_ = l_Std_Http_URI_EncodedSegment_encode(v_segment_1415_);
v___x_1422_ = lean_array_push(v_segments_1416_, v___x_1421_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1422_);
v___x_1424_ = v___x_1419_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
lean_ctor_set_uint8(v_reuseFailAlloc_1425_, sizeof(void*)*1, v_absolute_1417_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append___boxed(lean_object* v_p_1427_, lean_object* v_segment_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Std_Http_URI_Path_append(v_p_1427_, v_segment_1428_);
lean_dec_ref(v_segment_1428_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_appendEncoded(lean_object* v_p_1430_, lean_object* v_segment_1431_){
_start:
{
lean_object* v_segments_1432_; uint8_t v_absolute_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1441_; 
v_segments_1432_ = lean_ctor_get(v_p_1430_, 0);
v_absolute_1433_ = lean_ctor_get_uint8(v_p_1430_, sizeof(void*)*1);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_p_1430_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1435_ = v_p_1430_;
v_isShared_1436_ = v_isSharedCheck_1441_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_segments_1432_);
lean_dec(v_p_1430_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1441_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1437_ = lean_array_push(v_segments_1432_, v_segment_1431_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1437_);
v___x_1439_ = v___x_1435_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
lean_ctor_set_uint8(v_reuseFailAlloc_1440_, sizeof(void*)*1, v_absolute_1433_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(lean_object* v_input_1444_, lean_object* v_output_1445_){
_start:
{
if (lean_obj_tag(v_input_1444_) == 0)
{
lean_object* v___x_1446_; 
v___x_1446_ = l_List_reverse___redArg(v_output_1445_);
return v___x_1446_;
}
else
{
lean_object* v_head_1447_; lean_object* v_tail_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1465_; 
v_head_1447_ = lean_ctor_get(v_input_1444_, 0);
v_tail_1448_ = lean_ctor_get(v_input_1444_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_input_1444_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1450_ = v_input_1444_;
v_isShared_1451_ = v_isSharedCheck_1465_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_tail_1448_);
lean_inc(v_head_1447_);
lean_dec(v_input_1444_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1465_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
lean_inc(v_head_1447_);
v___x_1452_ = lean_string_from_utf8_unchecked(v_head_1447_);
v___x_1453_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0));
v___x_1454_ = lean_string_dec_eq(v___x_1452_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1455_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1));
v___x_1456_ = lean_string_dec_eq(v___x_1452_, v___x_1455_);
lean_dec_ref(v___x_1452_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1458_; 
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 1, v_output_1445_);
v___x_1458_ = v___x_1450_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_head_1447_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_output_1445_);
v___x_1458_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
v_input_1444_ = v_tail_1448_;
v_output_1445_ = v___x_1458_;
goto _start;
}
}
else
{
lean_del_object(v___x_1450_);
lean_dec(v_head_1447_);
if (lean_obj_tag(v_output_1445_) == 0)
{
v_input_1444_ = v_tail_1448_;
goto _start;
}
else
{
lean_object* v_tail_1462_; 
v_tail_1462_ = lean_ctor_get(v_output_1445_, 1);
lean_inc(v_tail_1462_);
lean_dec_ref(v_output_1445_);
v_input_1444_ = v_tail_1448_;
v_output_1445_ = v_tail_1462_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_1452_);
lean_del_object(v___x_1450_);
lean_dec(v_head_1447_);
v_input_1444_ = v_tail_1448_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_normalize(lean_object* v_p_1466_){
_start:
{
lean_object* v_segments_1467_; uint8_t v_absolute_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1479_; 
v_segments_1467_ = lean_ctor_get(v_p_1466_, 0);
v_absolute_1468_ = lean_ctor_get_uint8(v_p_1466_, sizeof(void*)*1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_p_1466_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1470_ = v_p_1466_;
v_isShared_1471_ = v_isSharedCheck_1479_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_segments_1467_);
lean_dec(v_p_1466_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1479_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1472_ = lean_array_to_list(v_segments_1467_);
v___x_1473_ = lean_box(0);
v___x_1474_ = l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(v___x_1472_, v___x_1473_);
v___x_1475_ = lean_array_mk(v___x_1474_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v___x_1475_);
v___x_1477_ = v___x_1470_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
lean_ctor_set_uint8(v_reuseFailAlloc_1478_, sizeof(void*)*1, v_absolute_1468_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(size_t v_sz_1480_, size_t v_i_1481_, lean_object* v_bs_1482_){
_start:
{
uint8_t v___x_1483_; 
v___x_1483_ = lean_usize_dec_lt(v_i_1481_, v_sz_1480_);
if (v___x_1483_ == 0)
{
return v_bs_1482_;
}
else
{
lean_object* v_v_1484_; lean_object* v___x_1485_; lean_object* v_bs_x27_1486_; lean_object* v___y_1488_; lean_object* v___x_1493_; 
v_v_1484_ = lean_array_uget(v_bs_1482_, v_i_1481_);
v___x_1485_ = lean_unsigned_to_nat(0u);
v_bs_x27_1486_ = lean_array_uset(v_bs_1482_, v_i_1481_, v___x_1485_);
v___x_1493_ = l_Std_Http_URI_EncodedSegment_decode(v_v_1484_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_string_from_utf8_unchecked(v_v_1484_);
v___y_1488_ = v___x_1494_;
goto v___jp_1487_;
}
else
{
lean_object* v_val_1495_; 
lean_dec(v_v_1484_);
v_val_1495_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_val_1495_);
lean_dec_ref(v___x_1493_);
v___y_1488_ = v_val_1495_;
goto v___jp_1487_;
}
v___jp_1487_:
{
size_t v___x_1489_; size_t v___x_1490_; lean_object* v___x_1491_; 
v___x_1489_ = ((size_t)1ULL);
v___x_1490_ = lean_usize_add(v_i_1481_, v___x_1489_);
v___x_1491_ = lean_array_uset(v_bs_x27_1486_, v_i_1481_, v___y_1488_);
v_i_1481_ = v___x_1490_;
v_bs_1482_ = v___x_1491_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0___boxed(lean_object* v_sz_1496_, lean_object* v_i_1497_, lean_object* v_bs_1498_){
_start:
{
size_t v_sz_boxed_1499_; size_t v_i_boxed_1500_; lean_object* v_res_1501_; 
v_sz_boxed_1499_ = lean_unbox_usize(v_sz_1496_);
lean_dec(v_sz_1496_);
v_i_boxed_1500_ = lean_unbox_usize(v_i_1497_);
lean_dec(v_i_1497_);
v_res_1501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_boxed_1499_, v_i_boxed_1500_, v_bs_1498_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_toDecodedSegments(lean_object* v_p_1502_){
_start:
{
lean_object* v_segments_1503_; size_t v_sz_1504_; size_t v___x_1505_; lean_object* v___x_1506_; 
v_segments_1503_ = lean_ctor_get(v_p_1502_, 0);
lean_inc_ref(v_segments_1503_);
lean_dec_ref(v_p_1502_);
v_sz_1504_ = lean_array_size(v_segments_1503_);
v___x_1505_ = ((size_t)0ULL);
v___x_1506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_1504_, v___x_1505_, v_segments_1503_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___redArg(lean_object* v_xs_1515_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1517_ = l_Array_repr___redArg(v___x_1516_, v_xs_1515_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1(lean_object* v_xs_1518_, lean_object* v_x_1519_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1521_ = l_Array_repr___redArg(v___x_1520_, v_xs_1518_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___boxed(lean_object* v_xs_1522_, lean_object* v_x_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Std_Http_URI_instReprQuery___aux__1(v_xs_1522_, v_x_1523_);
lean_dec(v_x_1523_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_1525_, lean_object* v_x_1526_, lean_object* v_x_1527_){
_start:
{
if (lean_obj_tag(v_x_1527_) == 0)
{
lean_dec(v_x_1525_);
return v_x_1526_;
}
else
{
lean_object* v_head_1528_; lean_object* v_tail_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1538_; 
v_head_1528_ = lean_ctor_get(v_x_1527_, 0);
v_tail_1529_ = lean_ctor_get(v_x_1527_, 1);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_x_1527_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1531_ = v_x_1527_;
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_tail_1529_);
lean_inc(v_head_1528_);
lean_dec(v_x_1527_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
lean_inc(v_x_1525_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 5);
lean_ctor_set(v___x_1531_, 1, v_x_1525_);
lean_ctor_set(v___x_1531_, 0, v_x_1526_);
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_x_1526_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_x_1525_);
v___x_1534_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v_head_1528_);
v_x_1526_ = v___x_1535_;
v_x_1527_ = v_tail_1529_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(lean_object* v_x_1539_, lean_object* v_x_1540_){
_start:
{
if (lean_obj_tag(v_x_1539_) == 0)
{
lean_object* v___x_1541_; 
lean_dec(v_x_1540_);
v___x_1541_ = lean_box(0);
return v___x_1541_;
}
else
{
lean_object* v_tail_1542_; 
v_tail_1542_ = lean_ctor_get(v_x_1539_, 1);
if (lean_obj_tag(v_tail_1542_) == 0)
{
lean_object* v_head_1543_; 
lean_dec(v_x_1540_);
v_head_1543_ = lean_ctor_get(v_x_1539_, 0);
lean_inc(v_head_1543_);
lean_dec_ref(v_x_1539_);
return v_head_1543_;
}
else
{
lean_object* v_head_1544_; lean_object* v___x_1545_; 
lean_inc(v_tail_1542_);
v_head_1544_ = lean_ctor_get(v_x_1539_, 0);
lean_inc(v_head_1544_);
lean_dec_ref(v_x_1539_);
v___x_1545_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(v_x_1540_, v_head_1544_, v_tail_1542_);
return v___x_1545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(lean_object* v_x_1546_, lean_object* v_x_1547_){
_start:
{
if (lean_obj_tag(v_x_1546_) == 0)
{
lean_object* v___x_1548_; 
v___x_1548_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1548_;
}
else
{
lean_object* v_val_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1561_; 
v_val_1549_ = lean_ctor_get(v_x_1546_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_x_1546_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1551_ = v_x_1546_;
v_isShared_1552_ = v_isSharedCheck_1561_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_val_1549_);
lean_dec(v_x_1546_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1561_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1553_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1554_ = lean_string_from_utf8_unchecked(v_val_1549_);
v___x_1555_ = l_String_quote(v___x_1554_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 3);
lean_ctor_set(v___x_1551_, 0, v___x_1555_);
v___x_1557_ = v___x_1551_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1553_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = l_Repr_addAppParen(v___x_1558_, v_x_1547_);
return v___x_1559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1562_, lean_object* v_x_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_x_1562_, v_x_1563_);
lean_dec(v_x_1563_);
return v_res_1564_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0));
v___x_1568_ = lean_string_length(v___x_1567_);
return v___x_1568_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2);
v___x_1570_ = lean_nat_to_int(v___x_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(lean_object* v_x_1575_){
_start:
{
lean_object* v_fst_1576_; lean_object* v_snd_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1602_; 
v_fst_1576_ = lean_ctor_get(v_x_1575_, 0);
v_snd_1577_ = lean_ctor_get(v_x_1575_, 1);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_x_1575_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1579_ = v_x_1575_;
v_isShared_1580_ = v_isSharedCheck_1602_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_snd_1577_);
lean_inc(v_fst_1576_);
lean_dec(v_x_1575_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1602_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
v___x_1581_ = lean_string_from_utf8_unchecked(v_fst_1576_);
v___x_1582_ = l_String_quote(v___x_1581_);
v___x_1583_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
v___x_1584_ = lean_box(0);
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 1);
lean_ctor_set(v___x_1579_, 1, v___x_1584_);
lean_ctor_set(v___x_1579_, 0, v___x_1583_);
v___x_1586_ = v___x_1579_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; lean_object* v___x_1600_; 
v___x_1587_ = lean_unsigned_to_nat(0u);
v___x_1588_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_snd_1577_, v___x_1587_);
v___x_1589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v___x_1586_);
v___x_1590_ = l_List_reverse___redArg(v___x_1589_);
v___x_1591_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1592_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(v___x_1590_, v___x_1591_);
v___x_1593_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3);
v___x_1594_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4));
v___x_1595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
lean_ctor_set(v___x_1595_, 1, v___x_1592_);
v___x_1596_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5));
v___x_1597_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1593_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = 0;
v___x_1600_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1600_, 0, v___x_1598_);
lean_ctor_set_uint8(v___x_1600_, sizeof(void*)*1, v___x_1599_);
return v___x_1600_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(lean_object* v_x_1603_, lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
if (lean_obj_tag(v_x_1605_) == 0)
{
lean_dec(v_x_1603_);
return v_x_1604_;
}
else
{
lean_object* v_head_1606_; lean_object* v_tail_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1617_; 
v_head_1606_ = lean_ctor_get(v_x_1605_, 0);
v_tail_1607_ = lean_ctor_get(v_x_1605_, 1);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_x_1605_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1609_ = v_x_1605_;
v_isShared_1610_ = v_isSharedCheck_1617_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_tail_1607_);
lean_inc(v_head_1606_);
lean_dec(v_x_1605_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1617_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
lean_inc(v_x_1603_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set_tag(v___x_1609_, 5);
lean_ctor_set(v___x_1609_, 1, v_x_1603_);
lean_ctor_set(v___x_1609_, 0, v_x_1604_);
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_x_1604_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_x_1603_);
v___x_1612_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1606_);
v___x_1614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v_x_1604_ = v___x_1614_;
v_x_1605_ = v_tail_1607_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(lean_object* v_x_1618_, lean_object* v_x_1619_, lean_object* v_x_1620_){
_start:
{
if (lean_obj_tag(v_x_1620_) == 0)
{
lean_dec(v_x_1618_);
return v_x_1619_;
}
else
{
lean_object* v_head_1621_; lean_object* v_tail_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1632_; 
v_head_1621_ = lean_ctor_get(v_x_1620_, 0);
v_tail_1622_ = lean_ctor_get(v_x_1620_, 1);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_x_1620_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1624_ = v_x_1620_;
v_isShared_1625_ = v_isSharedCheck_1632_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_tail_1622_);
lean_inc(v_head_1621_);
lean_dec(v_x_1620_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1632_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
lean_inc(v_x_1618_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set_tag(v___x_1624_, 5);
lean_ctor_set(v___x_1624_, 1, v_x_1618_);
lean_ctor_set(v___x_1624_, 0, v_x_1619_);
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_x_1619_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_x_1618_);
v___x_1627_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1621_);
v___x_1629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(v_x_1618_, v___x_1629_, v_tail_1622_);
return v___x_1630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(lean_object* v_x_1633_, lean_object* v_x_1634_){
_start:
{
if (lean_obj_tag(v_x_1633_) == 0)
{
lean_object* v___x_1635_; 
lean_dec(v_x_1634_);
v___x_1635_ = lean_box(0);
return v___x_1635_;
}
else
{
lean_object* v_tail_1636_; 
v_tail_1636_ = lean_ctor_get(v_x_1633_, 1);
if (lean_obj_tag(v_tail_1636_) == 0)
{
lean_object* v_head_1637_; lean_object* v___x_1638_; 
lean_dec(v_x_1634_);
v_head_1637_ = lean_ctor_get(v_x_1633_, 0);
lean_inc(v_head_1637_);
lean_dec_ref(v_x_1633_);
v___x_1638_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1637_);
return v___x_1638_;
}
else
{
lean_object* v_head_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_inc(v_tail_1636_);
v_head_1639_ = lean_ctor_get(v_x_1633_, 0);
lean_inc(v_head_1639_);
lean_dec_ref(v_x_1633_);
v___x_1640_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1639_);
v___x_1641_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(v_x_1634_, v___x_1640_, v_tail_1636_);
return v___x_1641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(lean_object* v_xs_1642_){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1643_ = lean_array_get_size(v_xs_1642_);
v___x_1644_ = lean_unsigned_to_nat(0u);
v___x_1645_ = lean_nat_dec_eq(v___x_1643_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1646_ = lean_array_to_list(v_xs_1642_);
v___x_1647_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1648_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(v___x_1646_, v___x_1647_);
v___x_1649_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1650_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v___x_1648_);
v___x_1652_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1649_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = l_Std_Format_fill(v___x_1654_);
return v___x_1655_;
}
else
{
lean_object* v___x_1656_; 
lean_dec_ref(v_xs_1642_);
v___x_1656_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0(lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v___y_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0___boxed(lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Std_Http_URI_instReprQuery___lam__0(v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(lean_object* v_x_1665_, lean_object* v_x_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_x_1665_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___boxed(lean_object* v_x_1668_, lean_object* v_x_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(v_x_1668_, v_x_1669_);
lean_dec(v_x_1669_);
return v_res_1670_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1___lam__0(lean_object* v___f_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_){
_start:
{
lean_object* v_fst_1678_; lean_object* v_snd_1679_; lean_object* v_fst_1680_; lean_object* v_snd_1681_; uint8_t v___x_1682_; 
v_fst_1678_ = lean_ctor_get(v_x_1676_, 0);
lean_inc(v_fst_1678_);
v_snd_1679_ = lean_ctor_get(v_x_1676_, 1);
lean_inc(v_snd_1679_);
lean_dec_ref(v_x_1676_);
v_fst_1680_ = lean_ctor_get(v_x_1677_, 0);
lean_inc(v_fst_1680_);
v_snd_1681_ = lean_ctor_get(v_x_1677_, 1);
lean_inc(v_snd_1681_);
lean_dec_ref(v_x_1677_);
v___x_1682_ = lean_sarray_dec_eq(v_fst_1678_, v_fst_1680_);
lean_dec(v_fst_1680_);
lean_dec(v_fst_1678_);
if (v___x_1682_ == 0)
{
lean_dec(v_snd_1681_);
lean_dec(v_snd_1679_);
lean_dec_ref(v___f_1675_);
return v___x_1682_;
}
else
{
uint8_t v___x_1683_; 
v___x_1683_ = l_Option_instBEq_beq___redArg(v___f_1675_, v_snd_1679_, v_snd_1681_);
return v___x_1683_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___lam__0___boxed(lean_object* v___f_1684_, lean_object* v_x_1685_, lean_object* v_x_1686_){
_start:
{
uint8_t v_res_1687_; lean_object* v_r_1688_; 
v_res_1687_ = l_Std_Http_URI_instBEqQuery___aux__1___lam__0(v___f_1684_, v_x_1685_, v_x_1686_);
v_r_1688_ = lean_box(v_res_1687_);
return v_r_1688_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1(lean_object* v_xs_1692_, lean_object* v_ys_1693_){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1694_ = lean_array_get_size(v_xs_1692_);
v___x_1695_ = lean_array_get_size(v_ys_1693_);
v___x_1696_ = lean_nat_dec_eq(v___x_1694_, v___x_1695_);
if (v___x_1696_ == 0)
{
return v___x_1696_;
}
else
{
lean_object* v___f_1697_; uint8_t v___x_1698_; 
v___f_1697_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__1));
v___x_1698_ = l_Array_isEqvAux___redArg(v_xs_1692_, v_ys_1693_, v___f_1697_, v___x_1694_);
return v___x_1698_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___boxed(lean_object* v_xs_1699_, lean_object* v_ys_1700_){
_start:
{
uint8_t v_res_1701_; lean_object* v_r_1702_; 
v_res_1701_ = l_Std_Http_URI_instBEqQuery___aux__1(v_xs_1699_, v_ys_1700_);
lean_dec_ref(v_ys_1700_);
lean_dec_ref(v_xs_1699_);
v_r_1702_ = lean_box(v_res_1701_);
return v_r_1702_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(lean_object* v_x_1703_, lean_object* v_x_1704_){
_start:
{
if (lean_obj_tag(v_x_1703_) == 0)
{
if (lean_obj_tag(v_x_1704_) == 0)
{
uint8_t v___x_1705_; 
v___x_1705_ = 1;
return v___x_1705_;
}
else
{
uint8_t v___x_1706_; 
v___x_1706_ = 0;
return v___x_1706_;
}
}
else
{
if (lean_obj_tag(v_x_1704_) == 0)
{
uint8_t v___x_1707_; 
v___x_1707_ = 0;
return v___x_1707_;
}
else
{
lean_object* v_val_1708_; lean_object* v_val_1709_; uint8_t v___x_1710_; 
v_val_1708_ = lean_ctor_get(v_x_1703_, 0);
v_val_1709_ = lean_ctor_get(v_x_1704_, 0);
v___x_1710_ = lean_sarray_dec_eq(v_val_1708_, v_val_1709_);
return v___x_1710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0___boxed(lean_object* v_x_1711_, lean_object* v_x_1712_){
_start:
{
uint8_t v_res_1713_; lean_object* v_r_1714_; 
v_res_1713_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_x_1711_, v_x_1712_);
lean_dec(v_x_1712_);
lean_dec(v_x_1711_);
v_r_1714_ = lean_box(v_res_1713_);
return v_r_1714_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(lean_object* v_xs_1715_, lean_object* v_ys_1716_, lean_object* v_x_1717_){
_start:
{
lean_object* v_zero_1718_; uint8_t v_isZero_1719_; 
v_zero_1718_ = lean_unsigned_to_nat(0u);
v_isZero_1719_ = lean_nat_dec_eq(v_x_1717_, v_zero_1718_);
if (v_isZero_1719_ == 1)
{
lean_dec(v_x_1717_);
return v_isZero_1719_;
}
else
{
lean_object* v_one_1720_; lean_object* v_n_1721_; uint8_t v___y_1723_; lean_object* v___x_1725_; lean_object* v_fst_1726_; lean_object* v_snd_1727_; lean_object* v___x_1728_; lean_object* v_fst_1729_; lean_object* v_snd_1730_; uint8_t v___x_1731_; 
v_one_1720_ = lean_unsigned_to_nat(1u);
v_n_1721_ = lean_nat_sub(v_x_1717_, v_one_1720_);
lean_dec(v_x_1717_);
v___x_1725_ = lean_array_fget_borrowed(v_xs_1715_, v_n_1721_);
v_fst_1726_ = lean_ctor_get(v___x_1725_, 0);
v_snd_1727_ = lean_ctor_get(v___x_1725_, 1);
v___x_1728_ = lean_array_fget_borrowed(v_ys_1716_, v_n_1721_);
v_fst_1729_ = lean_ctor_get(v___x_1728_, 0);
v_snd_1730_ = lean_ctor_get(v___x_1728_, 1);
v___x_1731_ = lean_sarray_dec_eq(v_fst_1726_, v_fst_1729_);
if (v___x_1731_ == 0)
{
v___y_1723_ = v___x_1731_;
goto v___jp_1722_;
}
else
{
uint8_t v___x_1732_; 
v___x_1732_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_snd_1727_, v_snd_1730_);
v___y_1723_ = v___x_1732_;
goto v___jp_1722_;
}
v___jp_1722_:
{
if (v___y_1723_ == 0)
{
lean_dec(v_n_1721_);
return v___y_1723_;
}
else
{
v_x_1717_ = v_n_1721_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg___boxed(lean_object* v_xs_1733_, lean_object* v_ys_1734_, lean_object* v_x_1735_){
_start:
{
uint8_t v_res_1736_; lean_object* v_r_1737_; 
v_res_1736_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1733_, v_ys_1734_, v_x_1735_);
lean_dec_ref(v_ys_1734_);
lean_dec_ref(v_xs_1733_);
v_r_1737_ = lean_box(v_res_1736_);
return v_r_1737_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___lam__0(lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1740_ = lean_array_get_size(v___y_1738_);
v___x_1741_ = lean_array_get_size(v___y_1739_);
v___x_1742_ = lean_nat_dec_eq(v___x_1740_, v___x_1741_);
if (v___x_1742_ == 0)
{
return v___x_1742_;
}
else
{
uint8_t v___x_1743_; 
v___x_1743_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v___y_1738_, v___y_1739_, v___x_1740_);
return v___x_1743_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___lam__0___boxed(lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
uint8_t v_res_1746_; lean_object* v_r_1747_; 
v_res_1746_ = l_Std_Http_URI_instBEqQuery___lam__0(v___y_1744_, v___y_1745_);
lean_dec_ref(v___y_1745_);
lean_dec_ref(v___y_1744_);
v_r_1747_ = lean_box(v_res_1746_);
return v_r_1747_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(lean_object* v_xs_1750_, lean_object* v_ys_1751_, lean_object* v_hsz_1752_, lean_object* v_x_1753_, lean_object* v_x_1754_){
_start:
{
uint8_t v___x_1755_; 
v___x_1755_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1750_, v_ys_1751_, v_x_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___boxed(lean_object* v_xs_1756_, lean_object* v_ys_1757_, lean_object* v_hsz_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_){
_start:
{
uint8_t v_res_1761_; lean_object* v_r_1762_; 
v_res_1761_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(v_xs_1756_, v_ys_1757_, v_hsz_1758_, v_x_1759_, v_x_1760_);
lean_dec_ref(v_ys_1757_);
lean_dec_ref(v_xs_1756_);
v_r_1762_ = lean_box(v_res_1761_);
return v_r_1762_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(lean_object* v_as_1763_){
_start:
{
lean_object* v___f_1764_; lean_object* v___x_1765_; 
v___f_1764_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__0));
v___x_1765_ = l_List_eraseDupsBy___redArg(v___f_1764_, v_as_1763_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(size_t v_sz_1766_, size_t v_i_1767_, lean_object* v_bs_1768_){
_start:
{
uint8_t v___x_1769_; 
v___x_1769_ = lean_usize_dec_lt(v_i_1767_, v_sz_1766_);
if (v___x_1769_ == 0)
{
return v_bs_1768_;
}
else
{
lean_object* v_v_1770_; lean_object* v_fst_1771_; lean_object* v___x_1772_; lean_object* v_bs_x27_1773_; size_t v___x_1774_; size_t v___x_1775_; lean_object* v___x_1776_; 
v_v_1770_ = lean_array_uget_borrowed(v_bs_1768_, v_i_1767_);
v_fst_1771_ = lean_ctor_get(v_v_1770_, 0);
lean_inc(v_fst_1771_);
v___x_1772_ = lean_unsigned_to_nat(0u);
v_bs_x27_1773_ = lean_array_uset(v_bs_1768_, v_i_1767_, v___x_1772_);
v___x_1774_ = ((size_t)1ULL);
v___x_1775_ = lean_usize_add(v_i_1767_, v___x_1774_);
v___x_1776_ = lean_array_uset(v_bs_x27_1773_, v_i_1767_, v_fst_1771_);
v_i_1767_ = v___x_1775_;
v_bs_1768_ = v___x_1776_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0___boxed(lean_object* v_sz_1778_, lean_object* v_i_1779_, lean_object* v_bs_1780_){
_start:
{
size_t v_sz_boxed_1781_; size_t v_i_boxed_1782_; lean_object* v_res_1783_; 
v_sz_boxed_1781_ = lean_unbox_usize(v_sz_1778_);
lean_dec(v_sz_1778_);
v_i_boxed_1782_ = lean_unbox_usize(v_i_1779_);
lean_dec(v_i_1779_);
v_res_1783_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_boxed_1781_, v_i_boxed_1782_, v_bs_1780_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names(lean_object* v_query_1784_){
_start:
{
size_t v_sz_1785_; size_t v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_sz_1785_ = lean_array_size(v_query_1784_);
v___x_1786_ = ((size_t)0ULL);
v___x_1787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_1785_, v___x_1786_, v_query_1784_);
v___x_1788_ = lean_array_to_list(v___x_1787_);
v___x_1789_ = l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(v___x_1788_);
v___x_1790_ = lean_array_mk(v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(size_t v_sz_1791_, size_t v_i_1792_, lean_object* v_bs_1793_){
_start:
{
uint8_t v___x_1794_; 
v___x_1794_ = lean_usize_dec_lt(v_i_1792_, v_sz_1791_);
if (v___x_1794_ == 0)
{
return v_bs_1793_;
}
else
{
lean_object* v_v_1795_; lean_object* v_snd_1796_; lean_object* v___x_1797_; lean_object* v_bs_x27_1798_; size_t v___x_1799_; size_t v___x_1800_; lean_object* v___x_1801_; 
v_v_1795_ = lean_array_uget_borrowed(v_bs_1793_, v_i_1792_);
v_snd_1796_ = lean_ctor_get(v_v_1795_, 1);
lean_inc(v_snd_1796_);
v___x_1797_ = lean_unsigned_to_nat(0u);
v_bs_x27_1798_ = lean_array_uset(v_bs_1793_, v_i_1792_, v___x_1797_);
v___x_1799_ = ((size_t)1ULL);
v___x_1800_ = lean_usize_add(v_i_1792_, v___x_1799_);
v___x_1801_ = lean_array_uset(v_bs_x27_1798_, v_i_1792_, v_snd_1796_);
v_i_1792_ = v___x_1800_;
v_bs_1793_ = v___x_1801_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0___boxed(lean_object* v_sz_1803_, lean_object* v_i_1804_, lean_object* v_bs_1805_){
_start:
{
size_t v_sz_boxed_1806_; size_t v_i_boxed_1807_; lean_object* v_res_1808_; 
v_sz_boxed_1806_ = lean_unbox_usize(v_sz_1803_);
lean_dec(v_sz_1803_);
v_i_boxed_1807_ = lean_unbox_usize(v_i_1804_);
lean_dec(v_i_1804_);
v_res_1808_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_boxed_1806_, v_i_boxed_1807_, v_bs_1805_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_values(lean_object* v_query_1809_){
_start:
{
size_t v_sz_1810_; size_t v___x_1811_; lean_object* v___x_1812_; 
v_sz_1810_ = lean_array_size(v_query_1809_);
v___x_1811_ = ((size_t)0ULL);
v___x_1812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_1810_, v___x_1811_, v_query_1809_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray(lean_object* v_query_1813_){
_start:
{
lean_inc_ref(v_query_1813_);
return v_query_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray___boxed(lean_object* v_query_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Std_Http_URI_Query_toArray(v_query_1814_);
lean_dec_ref(v_query_1814_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object* v_key_1817_, lean_object* v_value_1818_){
_start:
{
if (lean_obj_tag(v_value_1818_) == 0)
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_string_from_utf8_unchecked(v_key_1817_);
return v___x_1819_;
}
else
{
lean_object* v_val_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v_val_1820_ = lean_ctor_get(v_value_1818_, 0);
lean_inc(v_val_1820_);
lean_dec_ref(v_value_1818_);
v___x_1821_ = lean_string_from_utf8_unchecked(v_key_1817_);
v___x_1822_ = ((lean_object*)(l_Std_Http_URI_Query_formatQueryParam___closed__0));
v___x_1823_ = lean_string_append(v___x_1821_, v___x_1822_);
v___x_1824_ = lean_string_from_utf8_unchecked(v_val_1820_);
v___x_1825_ = lean_string_append(v___x_1823_, v___x_1824_);
lean_dec_ref(v___x_1824_);
return v___x_1825_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(lean_object* v_key_1829_, lean_object* v_as_1830_, size_t v_sz_1831_, size_t v_i_1832_, lean_object* v_b_1833_){
_start:
{
uint8_t v___x_1834_; 
v___x_1834_ = lean_usize_dec_lt(v_i_1832_, v_sz_1831_);
if (v___x_1834_ == 0)
{
lean_inc_ref(v_b_1833_);
return v_b_1833_;
}
else
{
lean_object* v_a_1835_; lean_object* v_fst_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
v_a_1835_ = lean_array_uget_borrowed(v_as_1830_, v_i_1832_);
v_fst_1836_ = lean_ctor_get(v_a_1835_, 0);
v___x_1837_ = lean_box(0);
v___x_1838_ = lean_sarray_dec_eq(v_fst_1836_, v_key_1829_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; size_t v___x_1840_; size_t v___x_1841_; 
v___x_1839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v___x_1840_ = ((size_t)1ULL);
v___x_1841_ = lean_usize_add(v_i_1832_, v___x_1840_);
v_i_1832_ = v___x_1841_;
v_b_1833_ = v___x_1839_;
goto _start;
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_inc(v_a_1835_);
v___x_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_a_1835_);
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v___x_1837_);
return v___x_1845_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___boxed(lean_object* v_key_1846_, lean_object* v_as_1847_, lean_object* v_sz_1848_, lean_object* v_i_1849_, lean_object* v_b_1850_){
_start:
{
size_t v_sz_boxed_1851_; size_t v_i_boxed_1852_; lean_object* v_res_1853_; 
v_sz_boxed_1851_ = lean_unbox_usize(v_sz_1848_);
lean_dec(v_sz_1848_);
v_i_boxed_1852_ = lean_unbox_usize(v_i_1849_);
lean_dec(v_i_1849_);
v_res_1853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1846_, v_as_1847_, v_sz_boxed_1851_, v_i_boxed_1852_, v_b_1850_);
lean_dec_ref(v_b_1850_);
lean_dec_ref(v_as_1847_);
lean_dec_ref(v_key_1846_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f(lean_object* v_query_1854_, lean_object* v_key_1855_){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; size_t v_sz_1858_; size_t v___x_1859_; lean_object* v___x_1860_; lean_object* v_fst_1861_; 
v___x_1856_ = lean_box(0);
v___x_1857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v_sz_1858_ = lean_array_size(v_query_1854_);
v___x_1859_ = ((size_t)0ULL);
v___x_1860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1855_, v_query_1854_, v_sz_1858_, v___x_1859_, v___x_1857_);
v_fst_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_fst_1861_);
lean_dec_ref(v___x_1860_);
if (lean_obj_tag(v_fst_1861_) == 0)
{
return v___x_1856_;
}
else
{
lean_object* v_val_1862_; 
v_val_1862_ = lean_ctor_get(v_fst_1861_, 0);
lean_inc(v_val_1862_);
lean_dec_ref(v_fst_1861_);
if (lean_obj_tag(v_val_1862_) == 0)
{
return v___x_1856_;
}
else
{
lean_object* v_val_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1871_; 
v_val_1863_ = lean_ctor_get(v_val_1862_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_val_1862_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1865_ = v_val_1862_;
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_val_1863_);
lean_dec(v_val_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v_snd_1867_; lean_object* v___x_1869_; 
v_snd_1867_ = lean_ctor_get(v_val_1863_, 1);
lean_inc(v_snd_1867_);
lean_dec(v_val_1863_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v_snd_1867_);
v___x_1869_ = v___x_1865_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_snd_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f___boxed(lean_object* v_query_1872_, lean_object* v_key_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1872_, v_key_1873_);
lean_dec_ref(v_key_1873_);
lean_dec_ref(v_query_1872_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f(lean_object* v_query_1875_, lean_object* v_key_1876_){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1876_);
v___x_1878_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1875_, v___x_1877_);
lean_dec_ref(v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f___boxed(lean_object* v_query_1879_, lean_object* v_key_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Std_Http_URI_Query_find_x3f(v_query_1879_, v_key_1880_);
lean_dec_ref(v_key_1880_);
lean_dec_ref(v_query_1879_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(lean_object* v_key_1882_, lean_object* v_as_1883_, size_t v_i_1884_, size_t v_stop_1885_, lean_object* v_b_1886_){
_start:
{
lean_object* v___y_1888_; uint8_t v___x_1892_; 
v___x_1892_ = lean_usize_dec_eq(v_i_1884_, v_stop_1885_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v_fst_1894_; lean_object* v_snd_1895_; uint8_t v___x_1896_; 
v___x_1893_ = lean_array_uget_borrowed(v_as_1883_, v_i_1884_);
v_fst_1894_ = lean_ctor_get(v___x_1893_, 0);
v_snd_1895_ = lean_ctor_get(v___x_1893_, 1);
v___x_1896_ = lean_sarray_dec_eq(v_fst_1894_, v_key_1882_);
if (v___x_1896_ == 0)
{
v___y_1888_ = v_b_1886_;
goto v___jp_1887_;
}
else
{
lean_object* v___x_1897_; 
lean_inc(v_snd_1895_);
v___x_1897_ = lean_array_push(v_b_1886_, v_snd_1895_);
v___y_1888_ = v___x_1897_;
goto v___jp_1887_;
}
}
else
{
return v_b_1886_;
}
v___jp_1887_:
{
size_t v___x_1889_; size_t v___x_1890_; 
v___x_1889_ = ((size_t)1ULL);
v___x_1890_ = lean_usize_add(v_i_1884_, v___x_1889_);
v_i_1884_ = v___x_1890_;
v_b_1886_ = v___y_1888_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0___boxed(lean_object* v_key_1898_, lean_object* v_as_1899_, lean_object* v_i_1900_, lean_object* v_stop_1901_, lean_object* v_b_1902_){
_start:
{
size_t v_i_boxed_1903_; size_t v_stop_boxed_1904_; lean_object* v_res_1905_; 
v_i_boxed_1903_ = lean_unbox_usize(v_i_1900_);
lean_dec(v_i_1900_);
v_stop_boxed_1904_ = lean_unbox_usize(v_stop_1901_);
lean_dec(v_stop_1901_);
v_res_1905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1898_, v_as_1899_, v_i_boxed_1903_, v_stop_boxed_1904_, v_b_1902_);
lean_dec_ref(v_as_1899_);
lean_dec_ref(v_key_1898_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(lean_object* v_key_1908_, lean_object* v_as_1909_, lean_object* v_start_1910_, lean_object* v_stop_1911_){
_start:
{
lean_object* v___x_1912_; uint8_t v___x_1913_; 
v___x_1912_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_1913_ = lean_nat_dec_lt(v_start_1910_, v_stop_1911_);
if (v___x_1913_ == 0)
{
return v___x_1912_;
}
else
{
lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1914_ = lean_array_get_size(v_as_1909_);
v___x_1915_ = lean_nat_dec_le(v_stop_1911_, v___x_1914_);
if (v___x_1915_ == 0)
{
uint8_t v___x_1916_; 
v___x_1916_ = lean_nat_dec_lt(v_start_1910_, v___x_1914_);
if (v___x_1916_ == 0)
{
return v___x_1912_;
}
else
{
size_t v___x_1917_; size_t v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = lean_usize_of_nat(v_start_1910_);
v___x_1918_ = lean_usize_of_nat(v___x_1914_);
v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1908_, v_as_1909_, v___x_1917_, v___x_1918_, v___x_1912_);
return v___x_1919_;
}
}
else
{
size_t v___x_1920_; size_t v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = lean_usize_of_nat(v_start_1910_);
v___x_1921_ = lean_usize_of_nat(v_stop_1911_);
v___x_1922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1908_, v_as_1909_, v___x_1920_, v___x_1921_, v___x_1912_);
return v___x_1922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___boxed(lean_object* v_key_1923_, lean_object* v_as_1924_, lean_object* v_start_1925_, lean_object* v_stop_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1923_, v_as_1924_, v_start_1925_, v_stop_1926_);
lean_dec(v_stop_1926_);
lean_dec(v_start_1925_);
lean_dec_ref(v_as_1924_);
lean_dec_ref(v_key_1923_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded(lean_object* v_query_1928_, lean_object* v_key_1929_){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = lean_unsigned_to_nat(0u);
v___x_1931_ = lean_array_get_size(v_query_1928_);
v___x_1932_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1929_, v_query_1928_, v___x_1930_, v___x_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded___boxed(lean_object* v_query_1933_, lean_object* v_key_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1933_, v_key_1934_);
lean_dec_ref(v_key_1934_);
lean_dec_ref(v_query_1933_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll(lean_object* v_query_1936_, lean_object* v_key_1937_){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1937_);
v___x_1939_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1936_, v___x_1938_);
lean_dec_ref(v___x_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll___boxed(lean_object* v_query_1940_, lean_object* v_key_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Std_Http_URI_Query_findAll(v_query_1940_, v_key_1941_);
lean_dec_ref(v_key_1941_);
lean_dec_ref(v_query_1940_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert(lean_object* v_query_1943_, lean_object* v_key_1944_, lean_object* v_value_1945_){
_start:
{
lean_object* v_encodedKey_1946_; lean_object* v_encodedValue_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v_encodedKey_1946_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1944_);
v_encodedValue_1947_ = l_Std_Http_URI_EncodedQueryParam_encode(v_value_1945_);
v___x_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1948_, 0, v_encodedValue_1947_);
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v_encodedKey_1946_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = lean_array_push(v_query_1943_, v___x_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert___boxed(lean_object* v_query_1951_, lean_object* v_key_1952_, lean_object* v_value_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Std_Http_URI_Query_insert(v_query_1951_, v_key_1952_, v_value_1953_);
lean_dec_ref(v_value_1953_);
lean_dec_ref(v_key_1952_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object* v_query_1955_, lean_object* v_key_1956_, lean_object* v_value_1957_){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1958_, 0, v_key_1956_);
lean_ctor_set(v___x_1958_, 1, v_value_1957_);
v___x_1959_ = lean_array_push(v_query_1955_, v___x_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_ofList(lean_object* v_pairs_1963_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = lean_array_mk(v_pairs_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(lean_object* v_key_1965_, lean_object* v_as_1966_, size_t v_i_1967_, size_t v_stop_1968_){
_start:
{
uint8_t v___x_1969_; 
v___x_1969_ = lean_usize_dec_eq(v_i_1967_, v_stop_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; lean_object* v_fst_1971_; uint8_t v___x_1972_; 
v___x_1970_ = lean_array_uget_borrowed(v_as_1966_, v_i_1967_);
v_fst_1971_ = lean_ctor_get(v___x_1970_, 0);
v___x_1972_ = lean_sarray_dec_eq(v_fst_1971_, v_key_1965_);
if (v___x_1972_ == 0)
{
size_t v___x_1973_; size_t v___x_1974_; 
v___x_1973_ = ((size_t)1ULL);
v___x_1974_ = lean_usize_add(v_i_1967_, v___x_1973_);
v_i_1967_ = v___x_1974_;
goto _start;
}
else
{
return v___x_1972_;
}
}
else
{
uint8_t v___x_1976_; 
v___x_1976_ = 0;
return v___x_1976_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(lean_object* v_key_1977_, lean_object* v_as_1978_, lean_object* v_i_1979_, lean_object* v_stop_1980_){
_start:
{
size_t v_i_boxed_1981_; size_t v_stop_boxed_1982_; uint8_t v_res_1983_; lean_object* v_r_1984_; 
v_i_boxed_1981_ = lean_unbox_usize(v_i_1979_);
lean_dec(v_i_1979_);
v_stop_boxed_1982_ = lean_unbox_usize(v_stop_1980_);
lean_dec(v_stop_1980_);
v_res_1983_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1977_, v_as_1978_, v_i_boxed_1981_, v_stop_boxed_1982_);
lean_dec_ref(v_as_1978_);
lean_dec_ref(v_key_1977_);
v_r_1984_ = lean_box(v_res_1983_);
return v_r_1984_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_containsEncoded(lean_object* v_query_1985_, lean_object* v_key_1986_){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1987_ = lean_unsigned_to_nat(0u);
v___x_1988_ = lean_array_get_size(v_query_1985_);
v___x_1989_ = lean_nat_dec_lt(v___x_1987_, v___x_1988_);
if (v___x_1989_ == 0)
{
return v___x_1989_;
}
else
{
if (v___x_1989_ == 0)
{
return v___x_1989_;
}
else
{
size_t v___x_1990_; size_t v___x_1991_; uint8_t v___x_1992_; 
v___x_1990_ = ((size_t)0ULL);
v___x_1991_ = lean_usize_of_nat(v___x_1988_);
v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1986_, v_query_1985_, v___x_1990_, v___x_1991_);
return v___x_1992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_containsEncoded___boxed(lean_object* v_query_1993_, lean_object* v_key_1994_){
_start:
{
uint8_t v_res_1995_; lean_object* v_r_1996_; 
v_res_1995_ = l_Std_Http_URI_Query_containsEncoded(v_query_1993_, v_key_1994_);
lean_dec_ref(v_key_1994_);
lean_dec_ref(v_query_1993_);
v_r_1996_ = lean_box(v_res_1995_);
return v_r_1996_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_contains(lean_object* v_query_1997_, lean_object* v_key_1998_){
_start:
{
lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1999_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1998_);
v___x_2000_ = l_Std_Http_URI_Query_containsEncoded(v_query_1997_, v___x_1999_);
lean_dec_ref(v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_contains___boxed(lean_object* v_query_2001_, lean_object* v_key_2002_){
_start:
{
uint8_t v_res_2003_; lean_object* v_r_2004_; 
v_res_2003_ = l_Std_Http_URI_Query_contains(v_query_2001_, v_key_2002_);
lean_dec_ref(v_key_2002_);
lean_dec_ref(v_query_2001_);
v_r_2004_ = lean_box(v_res_2003_);
return v_r_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(lean_object* v_key_2005_, lean_object* v_as_2006_, size_t v_i_2007_, size_t v_stop_2008_, lean_object* v_b_2009_){
_start:
{
lean_object* v___y_2011_; uint8_t v___x_2015_; 
v___x_2015_ = lean_usize_dec_eq(v_i_2007_, v_stop_2008_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; lean_object* v_fst_2019_; uint8_t v___x_2020_; 
v___x_2016_ = lean_array_uget_borrowed(v_as_2006_, v_i_2007_);
v_fst_2019_ = lean_ctor_get(v___x_2016_, 0);
v___x_2020_ = lean_sarray_dec_eq(v_fst_2019_, v_key_2005_);
if (v___x_2020_ == 0)
{
goto v___jp_2017_;
}
else
{
if (v___x_2015_ == 0)
{
v___y_2011_ = v_b_2009_;
goto v___jp_2010_;
}
else
{
goto v___jp_2017_;
}
}
v___jp_2017_:
{
lean_object* v___x_2018_; 
lean_inc(v___x_2016_);
v___x_2018_ = lean_array_push(v_b_2009_, v___x_2016_);
v___y_2011_ = v___x_2018_;
goto v___jp_2010_;
}
}
else
{
return v_b_2009_;
}
v___jp_2010_:
{
size_t v___x_2012_; size_t v___x_2013_; 
v___x_2012_ = ((size_t)1ULL);
v___x_2013_ = lean_usize_add(v_i_2007_, v___x_2012_);
v_i_2007_ = v___x_2013_;
v_b_2009_ = v___y_2011_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(lean_object* v_key_2021_, lean_object* v_as_2022_, lean_object* v_i_2023_, lean_object* v_stop_2024_, lean_object* v_b_2025_){
_start:
{
size_t v_i_boxed_2026_; size_t v_stop_boxed_2027_; lean_object* v_res_2028_; 
v_i_boxed_2026_ = lean_unbox_usize(v_i_2023_);
lean_dec(v_i_2023_);
v_stop_boxed_2027_ = lean_unbox_usize(v_stop_2024_);
lean_dec(v_stop_2024_);
v_res_2028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2021_, v_as_2022_, v_i_boxed_2026_, v_stop_boxed_2027_, v_b_2025_);
lean_dec_ref(v_as_2022_);
lean_dec_ref(v_key_2021_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded(lean_object* v_query_2029_, lean_object* v_key_2030_){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2031_ = lean_unsigned_to_nat(0u);
v___x_2032_ = lean_array_get_size(v_query_2029_);
v___x_2033_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_2034_ = lean_nat_dec_lt(v___x_2031_, v___x_2032_);
if (v___x_2034_ == 0)
{
return v___x_2033_;
}
else
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_nat_dec_le(v___x_2032_, v___x_2032_);
if (v___x_2035_ == 0)
{
if (v___x_2034_ == 0)
{
return v___x_2033_;
}
else
{
size_t v___x_2036_; size_t v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = ((size_t)0ULL);
v___x_2037_ = lean_usize_of_nat(v___x_2032_);
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2030_, v_query_2029_, v___x_2036_, v___x_2037_, v___x_2033_);
return v___x_2038_;
}
}
else
{
size_t v___x_2039_; size_t v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = ((size_t)0ULL);
v___x_2040_ = lean_usize_of_nat(v___x_2032_);
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2030_, v_query_2029_, v___x_2039_, v___x_2040_, v___x_2033_);
return v___x_2041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded___boxed(lean_object* v_query_2042_, lean_object* v_key_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Std_Http_URI_Query_eraseEncoded(v_query_2042_, v_key_2043_);
lean_dec_ref(v_key_2043_);
lean_dec_ref(v_query_2042_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase(lean_object* v_query_2045_, lean_object* v_key_2046_){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_2046_);
v___x_2048_ = l_Std_Http_URI_Query_eraseEncoded(v_query_2045_, v___x_2047_);
lean_dec_ref(v___x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase___boxed(lean_object* v_query_2049_, lean_object* v_key_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Std_Http_URI_Query_erase(v_query_2049_, v_key_2050_);
lean_dec_ref(v_key_2050_);
lean_dec_ref(v_query_2049_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get(lean_object* v_query_2054_, lean_object* v_key_2055_){
_start:
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Std_Http_URI_Query_find_x3f(v_query_2054_, v_key_2055_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_box(0);
return v___x_2057_;
}
else
{
lean_object* v_val_2058_; 
v_val_2058_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_val_2058_);
lean_dec_ref(v___x_2056_);
if (lean_obj_tag(v_val_2058_) == 0)
{
lean_object* v___x_2059_; 
v___x_2059_ = ((lean_object*)(l_Std_Http_URI_Query_get___closed__0));
return v___x_2059_;
}
else
{
lean_object* v_val_2060_; lean_object* v___x_2061_; 
v_val_2060_ = lean_ctor_get(v_val_2058_, 0);
lean_inc(v_val_2060_);
lean_dec_ref(v_val_2058_);
v___x_2061_ = l_Std_Http_URI_EncodedQueryParam_decode(v_val_2060_);
lean_dec(v_val_2060_);
return v___x_2061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get___boxed(lean_object* v_query_2062_, lean_object* v_key_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Std_Http_URI_Query_get(v_query_2062_, v_key_2063_);
lean_dec_ref(v_key_2063_);
lean_dec_ref(v_query_2062_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD(lean_object* v_query_2065_, lean_object* v_key_2066_, lean_object* v_default_2067_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Std_Http_URI_Query_get(v_query_2065_, v_key_2066_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_inc_ref(v_default_2067_);
return v_default_2067_;
}
else
{
lean_object* v_val_2069_; 
v_val_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_val_2069_);
lean_dec_ref(v___x_2068_);
return v_val_2069_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD___boxed(lean_object* v_query_2070_, lean_object* v_key_2071_, lean_object* v_default_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Std_Http_URI_Query_getD(v_query_2070_, v_key_2071_, v_default_2072_);
lean_dec_ref(v_default_2072_);
lean_dec_ref(v_key_2071_);
lean_dec_ref(v_query_2070_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set(lean_object* v_query_2074_, lean_object* v_key_2075_, lean_object* v_value_2076_){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = l_Std_Http_URI_Query_erase(v_query_2074_, v_key_2075_);
v___x_2078_ = l_Std_Http_URI_Query_insert(v___x_2077_, v_key_2075_, v_value_2076_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set___boxed(lean_object* v_query_2079_, lean_object* v_key_2080_, lean_object* v_value_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Std_Http_URI_Query_set(v_query_2079_, v_key_2080_, v_value_2081_);
lean_dec_ref(v_value_2081_);
lean_dec_ref(v_key_2080_);
lean_dec_ref(v_query_2079_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(size_t v_sz_2083_, size_t v_i_2084_, lean_object* v_bs_2085_){
_start:
{
uint8_t v___x_2086_; 
v___x_2086_ = lean_usize_dec_lt(v_i_2084_, v_sz_2083_);
if (v___x_2086_ == 0)
{
return v_bs_2085_;
}
else
{
lean_object* v_v_2087_; lean_object* v_fst_2088_; lean_object* v_snd_2089_; lean_object* v___x_2090_; lean_object* v_bs_x27_2091_; lean_object* v___x_2092_; size_t v___x_2093_; size_t v___x_2094_; lean_object* v___x_2095_; 
v_v_2087_ = lean_array_uget_borrowed(v_bs_2085_, v_i_2084_);
v_fst_2088_ = lean_ctor_get(v_v_2087_, 0);
lean_inc(v_fst_2088_);
v_snd_2089_ = lean_ctor_get(v_v_2087_, 1);
lean_inc(v_snd_2089_);
v___x_2090_ = lean_unsigned_to_nat(0u);
v_bs_x27_2091_ = lean_array_uset(v_bs_2085_, v_i_2084_, v___x_2090_);
v___x_2092_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2088_, v_snd_2089_);
v___x_2093_ = ((size_t)1ULL);
v___x_2094_ = lean_usize_add(v_i_2084_, v___x_2093_);
v___x_2095_ = lean_array_uset(v_bs_x27_2091_, v_i_2084_, v___x_2092_);
v_i_2084_ = v___x_2094_;
v_bs_2085_ = v___x_2095_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0___boxed(lean_object* v_sz_2097_, lean_object* v_i_2098_, lean_object* v_bs_2099_){
_start:
{
size_t v_sz_boxed_2100_; size_t v_i_boxed_2101_; lean_object* v_res_2102_; 
v_sz_boxed_2100_ = lean_unbox_usize(v_sz_2097_);
lean_dec(v_sz_2097_);
v_i_boxed_2101_ = lean_unbox_usize(v_i_2098_);
lean_dec(v_i_2098_);
v_res_2102_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_boxed_2100_, v_i_boxed_2101_, v_bs_2099_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toRawString(lean_object* v_query_2104_){
_start:
{
size_t v_sz_2105_; size_t v___x_2106_; lean_object* v_params_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v_sz_2105_ = lean_array_size(v_query_2104_);
v___x_2106_ = ((size_t)0ULL);
v_params_2107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_2105_, v___x_2106_, v_query_2104_);
v___x_2108_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2109_ = lean_array_to_list(v_params_2107_);
v___x_2110_ = l_String_intercalate(v___x_2108_, v___x_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0(lean_object* v_x_2112_){
_start:
{
lean_object* v_fst_2113_; lean_object* v_snd_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v_fst_2113_ = lean_ctor_get(v_x_2112_, 0);
v_snd_2114_ = lean_ctor_get(v_x_2112_, 1);
v___x_2115_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
v___x_2116_ = l_Std_Http_URI_Query_insert(v___x_2115_, v_fst_2113_, v_snd_2114_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0___boxed(lean_object* v_x_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Std_Http_URI_Query_instSingletonProdString___lam__0(v_x_2117_);
lean_dec_ref(v_x_2117_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0(lean_object* v_x_2121_, lean_object* v_q_2122_){
_start:
{
lean_object* v_fst_2123_; lean_object* v_snd_2124_; lean_object* v___x_2125_; 
v_fst_2123_ = lean_ctor_get(v_x_2121_, 0);
v_snd_2124_ = lean_ctor_get(v_x_2121_, 1);
v___x_2125_ = l_Std_Http_URI_Query_insert(v_q_2122_, v_fst_2123_, v_snd_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0___boxed(lean_object* v_x_2126_, lean_object* v_q_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Std_Http_URI_Query_instInsertProdString___lam__0(v_x_2126_, v_q_2127_);
lean_dec_ref(v_x_2126_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__0(lean_object* v_x_2131_){
_start:
{
lean_object* v_fst_2132_; lean_object* v_snd_2133_; lean_object* v___x_2134_; 
v_fst_2132_ = lean_ctor_get(v_x_2131_, 0);
lean_inc(v_fst_2132_);
v_snd_2133_ = lean_ctor_get(v_x_2131_, 1);
lean_inc(v_snd_2133_);
lean_dec_ref(v_x_2131_);
v___x_2134_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2132_, v_snd_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__1(lean_object* v___f_2136_, lean_object* v_q_2137_){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2138_ = lean_array_get_size(v_q_2137_);
v___x_2139_ = lean_unsigned_to_nat(0u);
v___x_2140_ = lean_nat_dec_eq(v___x_2138_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v_encodedParams_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2141_ = lean_array_to_list(v_q_2137_);
v___x_2142_ = lean_box(0);
v_encodedParams_2143_ = l_List_mapTR_loop___redArg(v___f_2136_, v___x_2141_, v___x_2142_);
v___x_2144_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2145_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2146_ = l_String_intercalate(v___x_2145_, v_encodedParams_2143_);
v___x_2147_ = lean_string_append(v___x_2144_, v___x_2146_);
lean_dec_ref(v___x_2146_);
return v___x_2147_;
}
else
{
lean_object* v___x_2148_; 
lean_dec_ref(v_q_2137_);
lean_dec_ref(v___f_2136_);
v___x_2148_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2148_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(lean_object* v_x_2153_, lean_object* v_x_2154_){
_start:
{
if (lean_obj_tag(v_x_2153_) == 0)
{
lean_object* v___x_2155_; 
v___x_2155_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2155_;
}
else
{
lean_object* v_val_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v_val_2156_ = lean_ctor_get(v_x_2153_, 0);
lean_inc(v_val_2156_);
lean_dec_ref(v_x_2153_);
v___x_2157_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2158_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_val_2156_);
v___x_2159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2157_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = l_Repr_addAppParen(v___x_2159_, v_x_2154_);
return v___x_2160_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(lean_object* v_x_2161_, lean_object* v_x_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_x_2161_, v_x_2162_);
lean_dec(v_x_2162_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object* v_x_2164_, lean_object* v_x_2165_){
_start:
{
if (lean_obj_tag(v_x_2164_) == 0)
{
lean_object* v___x_2166_; 
v___x_2166_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2166_;
}
else
{
lean_object* v_val_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2178_; 
v_val_2167_ = lean_ctor_get(v_x_2164_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_x_2164_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2169_ = v_x_2164_;
v_isShared_2170_ = v_isSharedCheck_2178_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_val_2167_);
lean_dec(v_x_2164_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2178_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2171_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2172_ = l_String_quote(v_val_2167_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set_tag(v___x_2169_, 3);
lean_ctor_set(v___x_2169_, 0, v___x_2172_);
v___x_2174_ = v___x_2169_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2171_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
v___x_2176_ = l_Repr_addAppParen(v___x_2175_, v_x_2165_);
return v___x_2176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1___boxed(lean_object* v_x_2179_, lean_object* v_x_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_x_2179_, v_x_2180_);
lean_dec(v_x_2180_);
return v_res_2181_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = lean_unsigned_to_nat(10u);
v___x_2192_ = lean_nat_to_int(v___x_2191_);
return v___x_2192_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = lean_unsigned_to_nat(13u);
v___x_2197_ = lean_nat_to_int(v___x_2196_);
return v___x_2197_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = lean_unsigned_to_nat(9u);
v___x_2205_ = lean_nat_to_int(v___x_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___redArg(lean_object* v_x_2209_){
_start:
{
lean_object* v_scheme_2210_; lean_object* v_authority_2211_; lean_object* v_path_2212_; lean_object* v_query_2213_; lean_object* v_fragment_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v_scheme_2210_ = lean_ctor_get(v_x_2209_, 0);
lean_inc_ref(v_scheme_2210_);
v_authority_2211_ = lean_ctor_get(v_x_2209_, 1);
lean_inc(v_authority_2211_);
v_path_2212_ = lean_ctor_get(v_x_2209_, 2);
lean_inc_ref(v_path_2212_);
v_query_2213_ = lean_ctor_get(v_x_2209_, 3);
lean_inc_ref(v_query_2213_);
v_fragment_2214_ = lean_ctor_get(v_x_2209_, 4);
lean_inc(v_fragment_2214_);
lean_dec_ref(v_x_2209_);
v___x_2215_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2216_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2217_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2218_ = l_String_quote(v_scheme_2210_);
v___x_2219_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
v___x_2220_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2217_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = 0;
v___x_2222_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2222_, 0, v___x_2220_);
lean_ctor_set_uint8(v___x_2222_, sizeof(void*)*1, v___x_2221_);
v___x_2223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2216_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
v___x_2224_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2223_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
v___x_2226_ = lean_box(1);
v___x_2227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2225_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
v___x_2228_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__6));
v___x_2229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2227_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
v___x_2230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set(v___x_2230_, 1, v___x_2215_);
v___x_2231_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_2232_ = lean_unsigned_to_nat(0u);
v___x_2233_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_2211_, v___x_2232_);
v___x_2234_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2231_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*1, v___x_2221_);
v___x_2236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2230_);
lean_ctor_set(v___x_2236_, 1, v___x_2235_);
v___x_2237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
lean_ctor_set(v___x_2237_, 1, v___x_2224_);
v___x_2238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
lean_ctor_set(v___x_2238_, 1, v___x_2226_);
v___x_2239_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_2240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2238_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
lean_ctor_set(v___x_2241_, 1, v___x_2215_);
v___x_2242_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2243_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_2212_);
v___x_2244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2242_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
lean_ctor_set_uint8(v___x_2245_, sizeof(void*)*1, v___x_2221_);
v___x_2246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2241_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
v___x_2247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
lean_ctor_set(v___x_2247_, 1, v___x_2224_);
v___x_2248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
lean_ctor_set(v___x_2248_, 1, v___x_2226_);
v___x_2249_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_2250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2248_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
lean_ctor_set(v___x_2251_, 1, v___x_2215_);
v___x_2252_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_2253_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_query_2213_);
v___x_2254_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
lean_ctor_set_uint8(v___x_2255_, sizeof(void*)*1, v___x_2221_);
v___x_2256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2251_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_ctor_set(v___x_2257_, 1, v___x_2224_);
v___x_2258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
lean_ctor_set(v___x_2258_, 1, v___x_2226_);
v___x_2259_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_2260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2258_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
lean_ctor_set(v___x_2261_, 1, v___x_2215_);
v___x_2262_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_2263_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_fragment_2214_, v___x_2232_);
v___x_2264_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2262_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
v___x_2265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*1, v___x_2221_);
v___x_2266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2261_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2268_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set(v___x_2269_, 1, v___x_2266_);
v___x_2270_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2269_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2267_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
v___x_2273_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set_uint8(v___x_2273_, sizeof(void*)*1, v___x_2221_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr(lean_object* v_x_2274_, lean_object* v_prec_2275_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l_Std_Http_instReprURI_repr___redArg(v_x_2274_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___boxed(lean_object* v_x_2277_, lean_object* v_prec_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Std_Http_instReprURI_repr(v_x_2277_, v_prec_2278_);
lean_dec(v_prec_2278_);
return v_res_2279_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object* v_x_2289_, lean_object* v_x_2290_){
_start:
{
if (lean_obj_tag(v_x_2289_) == 0)
{
if (lean_obj_tag(v_x_2290_) == 0)
{
uint8_t v___x_2291_; 
v___x_2291_ = 1;
return v___x_2291_;
}
else
{
uint8_t v___x_2292_; 
v___x_2292_ = 0;
return v___x_2292_;
}
}
else
{
if (lean_obj_tag(v_x_2290_) == 0)
{
uint8_t v___x_2293_; 
v___x_2293_ = 0;
return v___x_2293_;
}
else
{
lean_object* v_val_2294_; lean_object* v_val_2295_; uint8_t v___x_2296_; 
v_val_2294_ = lean_ctor_get(v_x_2289_, 0);
v_val_2295_ = lean_ctor_get(v_x_2290_, 0);
v___x_2296_ = l_Std_Http_URI_instBEqAuthority_beq(v_val_2294_, v_val_2295_);
return v___x_2296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object* v_x_2297_, lean_object* v_x_2298_){
_start:
{
uint8_t v_res_2299_; lean_object* v_r_2300_; 
v_res_2299_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_x_2297_, v_x_2298_);
lean_dec(v_x_2298_);
lean_dec(v_x_2297_);
v_r_2300_ = lean_box(v_res_2299_);
return v_r_2300_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object* v_x_2301_, lean_object* v_x_2302_){
_start:
{
if (lean_obj_tag(v_x_2301_) == 0)
{
if (lean_obj_tag(v_x_2302_) == 0)
{
uint8_t v___x_2303_; 
v___x_2303_ = 1;
return v___x_2303_;
}
else
{
uint8_t v___x_2304_; 
v___x_2304_ = 0;
return v___x_2304_;
}
}
else
{
if (lean_obj_tag(v_x_2302_) == 0)
{
uint8_t v___x_2305_; 
v___x_2305_ = 0;
return v___x_2305_;
}
else
{
lean_object* v_val_2306_; lean_object* v_val_2307_; uint8_t v___x_2308_; 
v_val_2306_ = lean_ctor_get(v_x_2301_, 0);
v_val_2307_ = lean_ctor_get(v_x_2302_, 0);
v___x_2308_ = lean_string_dec_eq(v_val_2306_, v_val_2307_);
return v___x_2308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object* v_x_2309_, lean_object* v_x_2310_){
_start:
{
uint8_t v_res_2311_; lean_object* v_r_2312_; 
v_res_2311_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_x_2309_, v_x_2310_);
lean_dec(v_x_2310_);
lean_dec(v_x_2309_);
v_r_2312_ = lean_box(v_res_2311_);
return v_r_2312_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object* v_x_2313_, lean_object* v_x_2314_){
_start:
{
lean_object* v_scheme_2315_; lean_object* v_authority_2316_; lean_object* v_path_2317_; lean_object* v_query_2318_; lean_object* v_fragment_2319_; lean_object* v_scheme_2320_; lean_object* v_authority_2321_; lean_object* v_path_2322_; lean_object* v_query_2323_; lean_object* v_fragment_2324_; uint8_t v___x_2325_; 
v_scheme_2315_ = lean_ctor_get(v_x_2313_, 0);
v_authority_2316_ = lean_ctor_get(v_x_2313_, 1);
v_path_2317_ = lean_ctor_get(v_x_2313_, 2);
v_query_2318_ = lean_ctor_get(v_x_2313_, 3);
v_fragment_2319_ = lean_ctor_get(v_x_2313_, 4);
v_scheme_2320_ = lean_ctor_get(v_x_2314_, 0);
v_authority_2321_ = lean_ctor_get(v_x_2314_, 1);
v_path_2322_ = lean_ctor_get(v_x_2314_, 2);
v_query_2323_ = lean_ctor_get(v_x_2314_, 3);
v_fragment_2324_ = lean_ctor_get(v_x_2314_, 4);
v___x_2325_ = lean_string_dec_eq(v_scheme_2315_, v_scheme_2320_);
if (v___x_2325_ == 0)
{
return v___x_2325_;
}
else
{
uint8_t v___x_2326_; 
v___x_2326_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_2316_, v_authority_2321_);
if (v___x_2326_ == 0)
{
return v___x_2326_;
}
else
{
uint8_t v___x_2327_; 
v___x_2327_ = l_Std_Http_URI_instBEqPath_beq(v_path_2317_, v_path_2322_);
if (v___x_2327_ == 0)
{
return v___x_2327_;
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; 
v___x_2328_ = lean_array_get_size(v_query_2318_);
v___x_2329_ = lean_array_get_size(v_query_2323_);
v___x_2330_ = lean_nat_dec_eq(v___x_2328_, v___x_2329_);
if (v___x_2330_ == 0)
{
return v___x_2330_;
}
else
{
uint8_t v___x_2331_; 
v___x_2331_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_query_2318_, v_query_2323_, v___x_2328_);
if (v___x_2331_ == 0)
{
return v___x_2331_;
}
else
{
uint8_t v___x_2332_; 
v___x_2332_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_fragment_2319_, v_fragment_2324_);
return v___x_2332_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object* v_x_2333_, lean_object* v_x_2334_){
_start:
{
uint8_t v_res_2335_; lean_object* v_r_2336_; 
v_res_2335_ = l_Std_Http_instBEqURI_beq(v_x_2333_, v_x_2334_);
lean_dec_ref(v_x_2334_);
lean_dec_ref(v_x_2333_);
v_r_2336_ = lean_box(v_res_2335_);
return v_r_2336_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__2(lean_object* v___f_2341_, lean_object* v___f_2342_, lean_object* v_uri_2343_){
_start:
{
lean_object* v_scheme_2344_; lean_object* v_authority_2345_; lean_object* v_path_2346_; lean_object* v_query_2347_; lean_object* v_fragment_2348_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2385_; 
v_scheme_2344_ = lean_ctor_get(v_uri_2343_, 0);
lean_inc_ref(v_scheme_2344_);
v_authority_2345_ = lean_ctor_get(v_uri_2343_, 1);
lean_inc(v_authority_2345_);
v_path_2346_ = lean_ctor_get(v_uri_2343_, 2);
lean_inc_ref(v_path_2346_);
v_query_2347_ = lean_ctor_get(v_uri_2343_, 3);
lean_inc_ref(v_query_2347_);
v_fragment_2348_ = lean_ctor_get(v_uri_2343_, 4);
lean_inc(v_fragment_2348_);
lean_dec_ref(v_uri_2343_);
if (lean_obj_tag(v_authority_2345_) == 0)
{
lean_object* v___x_2396_; 
v___x_2396_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2385_ = v___x_2396_;
goto v___jp_2384_;
}
else
{
lean_object* v_val_2397_; lean_object* v_userInfo_2398_; lean_object* v_host_2399_; lean_object* v_port_2400_; lean_object* v___x_2401_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2420_; 
v_val_2397_ = lean_ctor_get(v_authority_2345_, 0);
lean_inc(v_val_2397_);
lean_dec_ref(v_authority_2345_);
v_userInfo_2398_ = lean_ctor_get(v_val_2397_, 0);
lean_inc(v_userInfo_2398_);
v_host_2399_ = lean_ctor_get(v_val_2397_, 1);
lean_inc_ref(v_host_2399_);
v_port_2400_ = lean_ctor_get(v_val_2397_, 2);
lean_inc(v_port_2400_);
lean_dec(v_val_2397_);
v___x_2401_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__1));
if (lean_obj_tag(v_userInfo_2398_) == 0)
{
lean_object* v___x_2430_; 
v___x_2430_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2420_ = v___x_2430_;
goto v___jp_2419_;
}
else
{
lean_object* v_val_2431_; lean_object* v_password_2432_; 
v_val_2431_ = lean_ctor_get(v_userInfo_2398_, 0);
lean_inc(v_val_2431_);
lean_dec_ref(v_userInfo_2398_);
v_password_2432_ = lean_ctor_get(v_val_2431_, 1);
if (lean_obj_tag(v_password_2432_) == 0)
{
lean_object* v_username_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v_username_2433_ = lean_ctor_get(v_val_2431_, 0);
lean_inc_ref(v_username_2433_);
lean_dec(v_val_2431_);
v___x_2434_ = lean_string_from_utf8_unchecked(v_username_2433_);
v___x_2435_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2436_ = lean_string_append(v___x_2434_, v___x_2435_);
v___y_2420_ = v___x_2436_;
goto v___jp_2419_;
}
else
{
lean_object* v_username_2437_; lean_object* v_val_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
lean_inc_ref(v_password_2432_);
v_username_2437_ = lean_ctor_get(v_val_2431_, 0);
lean_inc_ref(v_username_2437_);
lean_dec(v_val_2431_);
v_val_2438_ = lean_ctor_get(v_password_2432_, 0);
lean_inc(v_val_2438_);
lean_dec_ref(v_password_2432_);
v___x_2439_ = lean_string_from_utf8_unchecked(v_username_2437_);
v___x_2440_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2441_ = lean_string_append(v___x_2439_, v___x_2440_);
v___x_2442_ = lean_string_from_utf8_unchecked(v_val_2438_);
v___x_2443_ = lean_string_append(v___x_2441_, v___x_2442_);
lean_dec_ref(v___x_2442_);
v___x_2444_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2445_ = lean_string_append(v___x_2443_, v___x_2444_);
v___y_2420_ = v___x_2445_;
goto v___jp_2419_;
}
}
v___jp_2402_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2406_ = lean_string_append(v___y_2403_, v___y_2404_);
lean_dec_ref(v___y_2404_);
v___x_2407_ = lean_string_append(v___x_2406_, v___y_2405_);
lean_dec_ref(v___y_2405_);
v___x_2408_ = lean_string_append(v___x_2401_, v___x_2407_);
lean_dec_ref(v___x_2407_);
v___y_2385_ = v___x_2408_;
goto v___jp_2384_;
}
v___jp_2409_:
{
switch(lean_obj_tag(v_port_2400_))
{
case 0:
{
lean_object* v___x_2412_; 
v___x_2412_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2403_ = v___y_2410_;
v___y_2404_ = v___y_2411_;
v___y_2405_ = v___x_2412_;
goto v___jp_2402_;
}
case 1:
{
lean_object* v___x_2413_; 
v___x_2413_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_2403_ = v___y_2410_;
v___y_2404_ = v___y_2411_;
v___y_2405_ = v___x_2413_;
goto v___jp_2402_;
}
default: 
{
uint16_t v_port_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v_port_2414_ = lean_ctor_get_uint16(v_port_2400_, 0);
lean_dec_ref(v_port_2400_);
v___x_2415_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2416_ = lean_uint16_to_nat(v_port_2414_);
v___x_2417_ = l_Nat_reprFast(v___x_2416_);
v___x_2418_ = lean_string_append(v___x_2415_, v___x_2417_);
lean_dec_ref(v___x_2417_);
v___y_2403_ = v___y_2410_;
v___y_2404_ = v___y_2411_;
v___y_2405_ = v___x_2418_;
goto v___jp_2402_;
}
}
}
v___jp_2419_:
{
switch(lean_obj_tag(v_host_2399_))
{
case 0:
{
lean_object* v_name_2421_; 
v_name_2421_ = lean_ctor_get(v_host_2399_, 0);
lean_inc_ref(v_name_2421_);
lean_dec_ref(v_host_2399_);
v___y_2410_ = v___y_2420_;
v___y_2411_ = v_name_2421_;
goto v___jp_2409_;
}
case 1:
{
lean_object* v_ipv4_2422_; lean_object* v___x_2423_; 
v_ipv4_2422_ = lean_ctor_get(v_host_2399_, 0);
lean_inc_ref(v_ipv4_2422_);
lean_dec_ref(v_host_2399_);
v___x_2423_ = lean_uv_ntop_v4(v_ipv4_2422_);
lean_dec_ref(v_ipv4_2422_);
v___y_2410_ = v___y_2420_;
v___y_2411_ = v___x_2423_;
goto v___jp_2409_;
}
default: 
{
lean_object* v_ipv6_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v_ipv6_2424_ = lean_ctor_get(v_host_2399_, 0);
lean_inc_ref(v_ipv6_2424_);
lean_dec_ref(v_host_2399_);
v___x_2425_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_2426_ = lean_uv_ntop_v6(v_ipv6_2424_);
lean_dec_ref(v_ipv6_2424_);
v___x_2427_ = lean_string_append(v___x_2425_, v___x_2426_);
lean_dec_ref(v___x_2426_);
v___x_2428_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_2429_ = lean_string_append(v___x_2427_, v___x_2428_);
v___y_2410_ = v___y_2420_;
v___y_2411_ = v___x_2429_;
goto v___jp_2409_;
}
}
}
}
v___jp_2349_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2354_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2355_ = lean_string_append(v_scheme_2344_, v___x_2354_);
v___x_2356_ = lean_string_append(v___x_2355_, v___y_2352_);
lean_dec_ref(v___y_2352_);
v___x_2357_ = lean_string_append(v___x_2356_, v___y_2351_);
lean_dec_ref(v___y_2351_);
v___x_2358_ = lean_string_append(v___x_2357_, v___y_2350_);
lean_dec_ref(v___y_2350_);
v___x_2359_ = lean_string_append(v___x_2358_, v___y_2353_);
lean_dec_ref(v___y_2353_);
return v___x_2359_;
}
v___jp_2360_:
{
if (lean_obj_tag(v_fragment_2348_) == 0)
{
lean_object* v___x_2364_; 
v___x_2364_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2350_ = v___y_2363_;
v___y_2351_ = v___y_2361_;
v___y_2352_ = v___y_2362_;
v___y_2353_ = v___x_2364_;
goto v___jp_2349_;
}
else
{
lean_object* v_val_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v_val_2365_ = lean_ctor_get(v_fragment_2348_, 0);
lean_inc(v_val_2365_);
lean_dec_ref(v_fragment_2348_);
v___x_2366_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__0));
v___x_2367_ = l_Std_Http_URI_EncodedFragment_encode(v_val_2365_);
lean_dec(v_val_2365_);
v___x_2368_ = lean_string_from_utf8_unchecked(v___x_2367_);
v___x_2369_ = lean_string_append(v___x_2366_, v___x_2368_);
lean_dec_ref(v___x_2368_);
v___y_2350_ = v___y_2363_;
v___y_2351_ = v___y_2361_;
v___y_2352_ = v___y_2362_;
v___y_2353_ = v___x_2369_;
goto v___jp_2349_;
}
}
v___jp_2370_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; 
v___x_2373_ = lean_array_get_size(v_query_2347_);
v___x_2374_ = lean_unsigned_to_nat(0u);
v___x_2375_ = lean_nat_dec_eq(v___x_2373_, v___x_2374_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v_encodedParams_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2376_ = lean_array_to_list(v_query_2347_);
v___x_2377_ = lean_box(0);
v_encodedParams_2378_ = l_List_mapTR_loop___redArg(v___f_2341_, v___x_2376_, v___x_2377_);
v___x_2379_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2380_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2381_ = l_String_intercalate(v___x_2380_, v_encodedParams_2378_);
v___x_2382_ = lean_string_append(v___x_2379_, v___x_2381_);
lean_dec_ref(v___x_2381_);
v___y_2361_ = v___y_2372_;
v___y_2362_ = v___y_2371_;
v___y_2363_ = v___x_2382_;
goto v___jp_2360_;
}
else
{
lean_object* v___x_2383_; 
lean_dec_ref(v_query_2347_);
lean_dec_ref(v___f_2341_);
v___x_2383_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2361_ = v___y_2372_;
v___y_2362_ = v___y_2371_;
v___y_2363_ = v___x_2383_;
goto v___jp_2360_;
}
}
v___jp_2384_:
{
lean_object* v_segments_2386_; uint8_t v_absolute_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; size_t v_sz_2390_; size_t v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v_result_2394_; 
v_segments_2386_ = lean_ctor_get(v_path_2346_, 0);
lean_inc_ref(v_segments_2386_);
v_absolute_2387_ = lean_ctor_get_uint8(v_path_2346_, sizeof(void*)*1);
lean_dec_ref(v_path_2346_);
v___x_2388_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_2389_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_2390_ = lean_array_size(v_segments_2386_);
v___x_2391_ = ((size_t)0ULL);
v___x_2392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2389_, v___f_2342_, v_sz_2390_, v___x_2391_, v_segments_2386_);
v___x_2393_ = lean_array_to_list(v___x_2392_);
v_result_2394_ = l_String_intercalate(v___x_2388_, v___x_2393_);
if (v_absolute_2387_ == 0)
{
v___y_2371_ = v___y_2385_;
v___y_2372_ = v_result_2394_;
goto v___jp_2370_;
}
else
{
lean_object* v___x_2395_; 
v___x_2395_ = lean_string_append(v___x_2388_, v_result_2394_);
lean_dec_ref(v_result_2394_);
v___y_2371_ = v___y_2385_;
v___y_2372_ = v___x_2395_;
goto v___jp_2370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x3f(lean_object* v_b_2459_, lean_object* v_scheme_2460_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Std_Http_URI_Scheme_ofString_x3f(v_scheme_2460_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v___x_2462_; 
lean_dec_ref(v_b_2459_);
v___x_2462_ = lean_box(0);
return v___x_2462_;
}
else
{
lean_object* v_userInfo_2463_; lean_object* v_host_2464_; lean_object* v_port_2465_; lean_object* v_pathSegments_2466_; lean_object* v_query_2467_; lean_object* v_fragment_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2483_; 
v_userInfo_2463_ = lean_ctor_get(v_b_2459_, 1);
v_host_2464_ = lean_ctor_get(v_b_2459_, 2);
v_port_2465_ = lean_ctor_get(v_b_2459_, 3);
v_pathSegments_2466_ = lean_ctor_get(v_b_2459_, 4);
v_query_2467_ = lean_ctor_get(v_b_2459_, 5);
v_fragment_2468_ = lean_ctor_get(v_b_2459_, 6);
v_isSharedCheck_2483_ = !lean_is_exclusive(v_b_2459_);
if (v_isSharedCheck_2483_ == 0)
{
lean_object* v_unused_2484_; 
v_unused_2484_ = lean_ctor_get(v_b_2459_, 0);
lean_dec(v_unused_2484_);
v___x_2470_ = v_b_2459_;
v_isShared_2471_ = v_isSharedCheck_2483_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_fragment_2468_);
lean_inc(v_query_2467_);
lean_inc(v_pathSegments_2466_);
lean_inc(v_port_2465_);
lean_inc(v_host_2464_);
lean_inc(v_userInfo_2463_);
lean_dec(v_b_2459_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2483_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
lean_inc_ref(v___x_2461_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v___x_2461_);
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_userInfo_2463_);
lean_ctor_set(v_reuseFailAlloc_2482_, 2, v_host_2464_);
lean_ctor_set(v_reuseFailAlloc_2482_, 3, v_port_2465_);
lean_ctor_set(v_reuseFailAlloc_2482_, 4, v_pathSegments_2466_);
lean_ctor_set(v_reuseFailAlloc_2482_, 5, v_query_2467_);
lean_ctor_set(v_reuseFailAlloc_2482_, 6, v_fragment_2468_);
v___x_2473_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; 
v_unused_2481_ = lean_ctor_get(v___x_2461_, 0);
lean_dec(v_unused_2481_);
v___x_2475_ = v___x_2461_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_dec(v___x_2461_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(lean_object* v_msg_2485_){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = ((lean_object*)(l_Std_Http_URI_instInhabitedBuilder_default));
v___x_2487_ = lean_panic_fn_borrowed(v___x_2486_, v_msg_2485_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x21(lean_object* v_b_2489_, lean_object* v_scheme_2490_){
_start:
{
lean_object* v___x_2491_; 
lean_inc_ref(v_scheme_2490_);
v___x_2491_ = l_Std_Http_URI_Builder_setScheme_x3f(v_b_2489_, v_scheme_2490_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2492_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2493_ = ((lean_object*)(l_Std_Http_URI_Builder_setScheme_x21___closed__0));
v___x_2494_ = lean_unsigned_to_nat(678u);
v___x_2495_ = lean_unsigned_to_nat(14u);
v___x_2496_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_2497_ = l_String_quote(v_scheme_2490_);
v___x_2498_ = lean_string_append(v___x_2496_, v___x_2497_);
lean_dec_ref(v___x_2497_);
v___x_2499_ = l_mkPanicMessageWithDecl(v___x_2492_, v___x_2493_, v___x_2494_, v___x_2495_, v___x_2498_);
lean_dec_ref(v___x_2498_);
v___x_2500_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2499_);
return v___x_2500_;
}
else
{
lean_object* v_val_2501_; 
lean_dec_ref(v_scheme_2490_);
v_val_2501_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_val_2501_);
lean_dec_ref(v___x_2491_);
return v_val_2501_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo(lean_object* v_b_2502_, lean_object* v_username_2503_, lean_object* v_password_2504_){
_start:
{
lean_object* v_scheme_2505_; lean_object* v_host_2506_; lean_object* v_port_2507_; lean_object* v_pathSegments_2508_; lean_object* v_query_2509_; lean_object* v_fragment_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2533_; 
v_scheme_2505_ = lean_ctor_get(v_b_2502_, 0);
v_host_2506_ = lean_ctor_get(v_b_2502_, 2);
v_port_2507_ = lean_ctor_get(v_b_2502_, 3);
v_pathSegments_2508_ = lean_ctor_get(v_b_2502_, 4);
v_query_2509_ = lean_ctor_get(v_b_2502_, 5);
v_fragment_2510_ = lean_ctor_get(v_b_2502_, 6);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_b_2502_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; 
v_unused_2534_ = lean_ctor_get(v_b_2502_, 1);
lean_dec(v_unused_2534_);
v___x_2512_ = v_b_2502_;
v_isShared_2513_ = v_isSharedCheck_2533_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_fragment_2510_);
lean_inc(v_query_2509_);
lean_inc(v_pathSegments_2508_);
lean_inc(v_port_2507_);
lean_inc(v_host_2506_);
lean_inc(v_scheme_2505_);
lean_dec(v_b_2502_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2533_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___y_2515_; lean_object* v___x_2520_; 
v___x_2520_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_2503_);
if (lean_obj_tag(v_password_2504_) == 0)
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_box(0);
v___x_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___y_2515_ = v___x_2522_;
goto v___jp_2514_;
}
else
{
lean_object* v_val_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2532_; 
v_val_2523_ = lean_ctor_get(v_password_2504_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_password_2504_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2525_ = v_password_2504_;
v_isShared_2526_ = v_isSharedCheck_2532_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_val_2523_);
lean_dec(v_password_2504_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2532_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2527_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_2523_);
lean_dec(v_val_2523_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2527_);
v___x_2529_ = v___x_2525_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2520_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v___y_2515_ = v___x_2530_;
goto v___jp_2514_;
}
}
}
v___jp_2514_:
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2516_, 0, v___y_2515_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 1, v___x_2516_);
v___x_2518_ = v___x_2512_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_scheme_2505_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2519_, 2, v_host_2506_);
lean_ctor_set(v_reuseFailAlloc_2519_, 3, v_port_2507_);
lean_ctor_set(v_reuseFailAlloc_2519_, 4, v_pathSegments_2508_);
lean_ctor_set(v_reuseFailAlloc_2519_, 5, v_query_2509_);
lean_ctor_set(v_reuseFailAlloc_2519_, 6, v_fragment_2510_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo___boxed(lean_object* v_b_2535_, lean_object* v_username_2536_, lean_object* v_password_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Std_Http_URI_Builder_setUserInfo(v_b_2535_, v_username_2536_, v_password_2537_);
lean_dec_ref(v_username_2536_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x3f(lean_object* v_b_2539_, lean_object* v_name_2540_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Std_Http_URI_DomainName_ofString_x3f(v_name_2540_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v___x_2542_; 
lean_dec_ref(v_b_2539_);
v___x_2542_ = lean_box(0);
return v___x_2542_;
}
else
{
lean_object* v_val_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2566_; 
v_val_2543_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2545_ = v___x_2541_;
v_isShared_2546_ = v_isSharedCheck_2566_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_val_2543_);
lean_dec(v___x_2541_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2566_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v_scheme_2547_; lean_object* v_userInfo_2548_; lean_object* v_port_2549_; lean_object* v_pathSegments_2550_; lean_object* v_query_2551_; lean_object* v_fragment_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2564_; 
v_scheme_2547_ = lean_ctor_get(v_b_2539_, 0);
v_userInfo_2548_ = lean_ctor_get(v_b_2539_, 1);
v_port_2549_ = lean_ctor_get(v_b_2539_, 3);
v_pathSegments_2550_ = lean_ctor_get(v_b_2539_, 4);
v_query_2551_ = lean_ctor_get(v_b_2539_, 5);
v_fragment_2552_ = lean_ctor_get(v_b_2539_, 6);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_b_2539_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; 
v_unused_2565_ = lean_ctor_get(v_b_2539_, 2);
lean_dec(v_unused_2565_);
v___x_2554_ = v_b_2539_;
v_isShared_2555_ = v_isSharedCheck_2564_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_fragment_2552_);
lean_inc(v_query_2551_);
lean_inc(v_pathSegments_2550_);
lean_inc(v_port_2549_);
lean_inc(v_userInfo_2548_);
lean_inc(v_scheme_2547_);
lean_dec(v_b_2539_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2564_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_val_2543_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2556_);
v___x_2558_ = v___x_2545_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2560_; 
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 2, v___x_2558_);
v___x_2560_ = v___x_2554_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_scheme_2547_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_userInfo_2548_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_port_2549_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v_pathSegments_2550_);
lean_ctor_set(v_reuseFailAlloc_2562_, 5, v_query_2551_);
lean_ctor_set(v_reuseFailAlloc_2562_, 6, v_fragment_2552_);
v___x_2560_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
return v___x_2561_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x21(lean_object* v_b_2569_, lean_object* v_name_2570_){
_start:
{
lean_object* v___x_2571_; 
lean_inc_ref(v_name_2570_);
v___x_2571_ = l_Std_Http_URI_Builder_setHost_x3f(v_b_2569_, v_name_2570_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2572_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2573_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__0));
v___x_2574_ = lean_unsigned_to_nat(707u);
v___x_2575_ = lean_unsigned_to_nat(14u);
v___x_2576_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__1));
v___x_2577_ = l_String_quote(v_name_2570_);
v___x_2578_ = lean_string_append(v___x_2576_, v___x_2577_);
lean_dec_ref(v___x_2577_);
v___x_2579_ = l_mkPanicMessageWithDecl(v___x_2572_, v___x_2573_, v___x_2574_, v___x_2575_, v___x_2578_);
lean_dec_ref(v___x_2578_);
v___x_2580_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2579_);
return v___x_2580_;
}
else
{
lean_object* v_val_2581_; 
lean_dec_ref(v_name_2570_);
v_val_2581_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_val_2581_);
lean_dec_ref(v___x_2571_);
return v_val_2581_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv4(lean_object* v_b_2582_, lean_object* v_addr_2583_){
_start:
{
lean_object* v_scheme_2584_; lean_object* v_userInfo_2585_; lean_object* v_port_2586_; lean_object* v_pathSegments_2587_; lean_object* v_query_2588_; lean_object* v_fragment_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2598_; 
v_scheme_2584_ = lean_ctor_get(v_b_2582_, 0);
v_userInfo_2585_ = lean_ctor_get(v_b_2582_, 1);
v_port_2586_ = lean_ctor_get(v_b_2582_, 3);
v_pathSegments_2587_ = lean_ctor_get(v_b_2582_, 4);
v_query_2588_ = lean_ctor_get(v_b_2582_, 5);
v_fragment_2589_ = lean_ctor_get(v_b_2582_, 6);
v_isSharedCheck_2598_ = !lean_is_exclusive(v_b_2582_);
if (v_isSharedCheck_2598_ == 0)
{
lean_object* v_unused_2599_; 
v_unused_2599_ = lean_ctor_get(v_b_2582_, 2);
lean_dec(v_unused_2599_);
v___x_2591_ = v_b_2582_;
v_isShared_2592_ = v_isSharedCheck_2598_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_fragment_2589_);
lean_inc(v_query_2588_);
lean_inc(v_pathSegments_2587_);
lean_inc(v_port_2586_);
lean_inc(v_userInfo_2585_);
lean_inc(v_scheme_2584_);
lean_dec(v_b_2582_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2598_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2593_, 0, v_addr_2583_);
v___x_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 2, v___x_2594_);
v___x_2596_ = v___x_2591_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_scheme_2584_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_userInfo_2585_);
lean_ctor_set(v_reuseFailAlloc_2597_, 2, v___x_2594_);
lean_ctor_set(v_reuseFailAlloc_2597_, 3, v_port_2586_);
lean_ctor_set(v_reuseFailAlloc_2597_, 4, v_pathSegments_2587_);
lean_ctor_set(v_reuseFailAlloc_2597_, 5, v_query_2588_);
lean_ctor_set(v_reuseFailAlloc_2597_, 6, v_fragment_2589_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv6(lean_object* v_b_2600_, lean_object* v_addr_2601_){
_start:
{
lean_object* v_scheme_2602_; lean_object* v_userInfo_2603_; lean_object* v_port_2604_; lean_object* v_pathSegments_2605_; lean_object* v_query_2606_; lean_object* v_fragment_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2616_; 
v_scheme_2602_ = lean_ctor_get(v_b_2600_, 0);
v_userInfo_2603_ = lean_ctor_get(v_b_2600_, 1);
v_port_2604_ = lean_ctor_get(v_b_2600_, 3);
v_pathSegments_2605_ = lean_ctor_get(v_b_2600_, 4);
v_query_2606_ = lean_ctor_get(v_b_2600_, 5);
v_fragment_2607_ = lean_ctor_get(v_b_2600_, 6);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_b_2600_);
if (v_isSharedCheck_2616_ == 0)
{
lean_object* v_unused_2617_; 
v_unused_2617_ = lean_ctor_get(v_b_2600_, 2);
lean_dec(v_unused_2617_);
v___x_2609_ = v_b_2600_;
v_isShared_2610_ = v_isSharedCheck_2616_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_fragment_2607_);
lean_inc(v_query_2606_);
lean_inc(v_pathSegments_2605_);
lean_inc(v_port_2604_);
lean_inc(v_userInfo_2603_);
lean_inc(v_scheme_2602_);
lean_dec(v_b_2600_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2616_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2611_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2611_, 0, v_addr_2601_);
v___x_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 2, v___x_2612_);
v___x_2614_ = v___x_2609_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_scheme_2602_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_userInfo_2603_);
lean_ctor_set(v_reuseFailAlloc_2615_, 2, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2615_, 3, v_port_2604_);
lean_ctor_set(v_reuseFailAlloc_2615_, 4, v_pathSegments_2605_);
lean_ctor_set(v_reuseFailAlloc_2615_, 5, v_query_2606_);
lean_ctor_set(v_reuseFailAlloc_2615_, 6, v_fragment_2607_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort(lean_object* v_b_2618_, uint16_t v_port_2619_){
_start:
{
lean_object* v_scheme_2620_; lean_object* v_userInfo_2621_; lean_object* v_host_2622_; lean_object* v_pathSegments_2623_; lean_object* v_query_2624_; lean_object* v_fragment_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2633_; 
v_scheme_2620_ = lean_ctor_get(v_b_2618_, 0);
v_userInfo_2621_ = lean_ctor_get(v_b_2618_, 1);
v_host_2622_ = lean_ctor_get(v_b_2618_, 2);
v_pathSegments_2623_ = lean_ctor_get(v_b_2618_, 4);
v_query_2624_ = lean_ctor_get(v_b_2618_, 5);
v_fragment_2625_ = lean_ctor_get(v_b_2618_, 6);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_b_2618_);
if (v_isSharedCheck_2633_ == 0)
{
lean_object* v_unused_2634_; 
v_unused_2634_ = lean_ctor_get(v_b_2618_, 3);
lean_dec(v_unused_2634_);
v___x_2627_ = v_b_2618_;
v_isShared_2628_ = v_isSharedCheck_2633_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_fragment_2625_);
lean_inc(v_query_2624_);
lean_inc(v_pathSegments_2623_);
lean_inc(v_host_2622_);
lean_inc(v_userInfo_2621_);
lean_inc(v_scheme_2620_);
lean_dec(v_b_2618_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2633_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2629_; lean_object* v___x_2631_; 
v___x_2629_ = lean_alloc_ctor(2, 0, 2);
lean_ctor_set_uint16(v___x_2629_, 0, v_port_2619_);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 3, v___x_2629_);
v___x_2631_ = v___x_2627_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_scheme_2620_);
lean_ctor_set(v_reuseFailAlloc_2632_, 1, v_userInfo_2621_);
lean_ctor_set(v_reuseFailAlloc_2632_, 2, v_host_2622_);
lean_ctor_set(v_reuseFailAlloc_2632_, 3, v___x_2629_);
lean_ctor_set(v_reuseFailAlloc_2632_, 4, v_pathSegments_2623_);
lean_ctor_set(v_reuseFailAlloc_2632_, 5, v_query_2624_);
lean_ctor_set(v_reuseFailAlloc_2632_, 6, v_fragment_2625_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort___boxed(lean_object* v_b_2635_, lean_object* v_port_2636_){
_start:
{
uint16_t v_port_boxed_2637_; lean_object* v_res_2638_; 
v_port_boxed_2637_ = lean_unbox(v_port_2636_);
v_res_2638_ = l_Std_Http_URI_Builder_setPort(v_b_2635_, v_port_boxed_2637_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPath(lean_object* v_b_2639_, lean_object* v_segments_2640_){
_start:
{
lean_object* v_scheme_2641_; lean_object* v_userInfo_2642_; lean_object* v_host_2643_; lean_object* v_port_2644_; lean_object* v_query_2645_; lean_object* v_fragment_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
v_scheme_2641_ = lean_ctor_get(v_b_2639_, 0);
v_userInfo_2642_ = lean_ctor_get(v_b_2639_, 1);
v_host_2643_ = lean_ctor_get(v_b_2639_, 2);
v_port_2644_ = lean_ctor_get(v_b_2639_, 3);
v_query_2645_ = lean_ctor_get(v_b_2639_, 5);
v_fragment_2646_ = lean_ctor_get(v_b_2639_, 6);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_b_2639_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; 
v_unused_2654_ = lean_ctor_get(v_b_2639_, 4);
lean_dec(v_unused_2654_);
v___x_2648_ = v_b_2639_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_fragment_2646_);
lean_inc(v_query_2645_);
lean_inc(v_port_2644_);
lean_inc(v_host_2643_);
lean_inc(v_userInfo_2642_);
lean_inc(v_scheme_2641_);
lean_dec(v_b_2639_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 4, v_segments_2640_);
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_scheme_2641_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v_userInfo_2642_);
lean_ctor_set(v_reuseFailAlloc_2652_, 2, v_host_2643_);
lean_ctor_set(v_reuseFailAlloc_2652_, 3, v_port_2644_);
lean_ctor_set(v_reuseFailAlloc_2652_, 4, v_segments_2640_);
lean_ctor_set(v_reuseFailAlloc_2652_, 5, v_query_2645_);
lean_ctor_set(v_reuseFailAlloc_2652_, 6, v_fragment_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_appendPathSegment(lean_object* v_b_2655_, lean_object* v_segment_2656_){
_start:
{
lean_object* v_scheme_2657_; lean_object* v_userInfo_2658_; lean_object* v_host_2659_; lean_object* v_port_2660_; lean_object* v_pathSegments_2661_; lean_object* v_query_2662_; lean_object* v_fragment_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2671_; 
v_scheme_2657_ = lean_ctor_get(v_b_2655_, 0);
v_userInfo_2658_ = lean_ctor_get(v_b_2655_, 1);
v_host_2659_ = lean_ctor_get(v_b_2655_, 2);
v_port_2660_ = lean_ctor_get(v_b_2655_, 3);
v_pathSegments_2661_ = lean_ctor_get(v_b_2655_, 4);
v_query_2662_ = lean_ctor_get(v_b_2655_, 5);
v_fragment_2663_ = lean_ctor_get(v_b_2655_, 6);
v_isSharedCheck_2671_ = !lean_is_exclusive(v_b_2655_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2665_ = v_b_2655_;
v_isShared_2666_ = v_isSharedCheck_2671_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_fragment_2663_);
lean_inc(v_query_2662_);
lean_inc(v_pathSegments_2661_);
lean_inc(v_port_2660_);
lean_inc(v_host_2659_);
lean_inc(v_userInfo_2658_);
lean_inc(v_scheme_2657_);
lean_dec(v_b_2655_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2671_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2667_ = lean_array_push(v_pathSegments_2661_, v_segment_2656_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 4, v___x_2667_);
v___x_2669_ = v___x_2665_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_scheme_2657_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_userInfo_2658_);
lean_ctor_set(v_reuseFailAlloc_2670_, 2, v_host_2659_);
lean_ctor_set(v_reuseFailAlloc_2670_, 3, v_port_2660_);
lean_ctor_set(v_reuseFailAlloc_2670_, 4, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2670_, 5, v_query_2662_);
lean_ctor_set(v_reuseFailAlloc_2670_, 6, v_fragment_2663_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryParam(lean_object* v_b_2672_, lean_object* v_key_2673_, lean_object* v_value_2674_){
_start:
{
lean_object* v_scheme_2675_; lean_object* v_userInfo_2676_; lean_object* v_host_2677_; lean_object* v_port_2678_; lean_object* v_pathSegments_2679_; lean_object* v_query_2680_; lean_object* v_fragment_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2691_; 
v_scheme_2675_ = lean_ctor_get(v_b_2672_, 0);
v_userInfo_2676_ = lean_ctor_get(v_b_2672_, 1);
v_host_2677_ = lean_ctor_get(v_b_2672_, 2);
v_port_2678_ = lean_ctor_get(v_b_2672_, 3);
v_pathSegments_2679_ = lean_ctor_get(v_b_2672_, 4);
v_query_2680_ = lean_ctor_get(v_b_2672_, 5);
v_fragment_2681_ = lean_ctor_get(v_b_2672_, 6);
v_isSharedCheck_2691_ = !lean_is_exclusive(v_b_2672_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2683_ = v_b_2672_;
v_isShared_2684_ = v_isSharedCheck_2691_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_fragment_2681_);
lean_inc(v_query_2680_);
lean_inc(v_pathSegments_2679_);
lean_inc(v_port_2678_);
lean_inc(v_host_2677_);
lean_inc(v_userInfo_2676_);
lean_inc(v_scheme_2675_);
lean_dec(v_b_2672_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2691_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2685_, 0, v_value_2674_);
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v_key_2673_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
v___x_2687_ = lean_array_push(v_query_2680_, v___x_2686_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 5, v___x_2687_);
v___x_2689_ = v___x_2683_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_scheme_2675_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_userInfo_2676_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v_host_2677_);
lean_ctor_set(v_reuseFailAlloc_2690_, 3, v_port_2678_);
lean_ctor_set(v_reuseFailAlloc_2690_, 4, v_pathSegments_2679_);
lean_ctor_set(v_reuseFailAlloc_2690_, 5, v___x_2687_);
lean_ctor_set(v_reuseFailAlloc_2690_, 6, v_fragment_2681_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryFlag(lean_object* v_b_2692_, lean_object* v_key_2693_){
_start:
{
lean_object* v_scheme_2694_; lean_object* v_userInfo_2695_; lean_object* v_host_2696_; lean_object* v_port_2697_; lean_object* v_pathSegments_2698_; lean_object* v_query_2699_; lean_object* v_fragment_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2710_; 
v_scheme_2694_ = lean_ctor_get(v_b_2692_, 0);
v_userInfo_2695_ = lean_ctor_get(v_b_2692_, 1);
v_host_2696_ = lean_ctor_get(v_b_2692_, 2);
v_port_2697_ = lean_ctor_get(v_b_2692_, 3);
v_pathSegments_2698_ = lean_ctor_get(v_b_2692_, 4);
v_query_2699_ = lean_ctor_get(v_b_2692_, 5);
v_fragment_2700_ = lean_ctor_get(v_b_2692_, 6);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_b_2692_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2702_ = v_b_2692_;
v_isShared_2703_ = v_isSharedCheck_2710_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_fragment_2700_);
lean_inc(v_query_2699_);
lean_inc(v_pathSegments_2698_);
lean_inc(v_port_2697_);
lean_inc(v_host_2696_);
lean_inc(v_userInfo_2695_);
lean_inc(v_scheme_2694_);
lean_dec(v_b_2692_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2710_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2708_; 
v___x_2704_ = lean_box(0);
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v_key_2693_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = lean_array_push(v_query_2699_, v___x_2705_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 5, v___x_2706_);
v___x_2708_ = v___x_2702_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_scheme_2694_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_userInfo_2695_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_host_2696_);
lean_ctor_set(v_reuseFailAlloc_2709_, 3, v_port_2697_);
lean_ctor_set(v_reuseFailAlloc_2709_, 4, v_pathSegments_2698_);
lean_ctor_set(v_reuseFailAlloc_2709_, 5, v___x_2706_);
lean_ctor_set(v_reuseFailAlloc_2709_, 6, v_fragment_2700_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setQuery(lean_object* v_b_2711_, lean_object* v_query_2712_){
_start:
{
lean_object* v_scheme_2713_; lean_object* v_userInfo_2714_; lean_object* v_host_2715_; lean_object* v_port_2716_; lean_object* v_pathSegments_2717_; lean_object* v_fragment_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
v_scheme_2713_ = lean_ctor_get(v_b_2711_, 0);
v_userInfo_2714_ = lean_ctor_get(v_b_2711_, 1);
v_host_2715_ = lean_ctor_get(v_b_2711_, 2);
v_port_2716_ = lean_ctor_get(v_b_2711_, 3);
v_pathSegments_2717_ = lean_ctor_get(v_b_2711_, 4);
v_fragment_2718_ = lean_ctor_get(v_b_2711_, 6);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_b_2711_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; 
v_unused_2726_ = lean_ctor_get(v_b_2711_, 5);
lean_dec(v_unused_2726_);
v___x_2720_ = v_b_2711_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_fragment_2718_);
lean_inc(v_pathSegments_2717_);
lean_inc(v_port_2716_);
lean_inc(v_host_2715_);
lean_inc(v_userInfo_2714_);
lean_inc(v_scheme_2713_);
lean_dec(v_b_2711_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 5, v_query_2712_);
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_scheme_2713_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_userInfo_2714_);
lean_ctor_set(v_reuseFailAlloc_2724_, 2, v_host_2715_);
lean_ctor_set(v_reuseFailAlloc_2724_, 3, v_port_2716_);
lean_ctor_set(v_reuseFailAlloc_2724_, 4, v_pathSegments_2717_);
lean_ctor_set(v_reuseFailAlloc_2724_, 5, v_query_2712_);
lean_ctor_set(v_reuseFailAlloc_2724_, 6, v_fragment_2718_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setFragment(lean_object* v_b_2727_, lean_object* v_fragment_2728_){
_start:
{
lean_object* v_scheme_2729_; lean_object* v_userInfo_2730_; lean_object* v_host_2731_; lean_object* v_port_2732_; lean_object* v_pathSegments_2733_; lean_object* v_query_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2742_; 
v_scheme_2729_ = lean_ctor_get(v_b_2727_, 0);
v_userInfo_2730_ = lean_ctor_get(v_b_2727_, 1);
v_host_2731_ = lean_ctor_get(v_b_2727_, 2);
v_port_2732_ = lean_ctor_get(v_b_2727_, 3);
v_pathSegments_2733_ = lean_ctor_get(v_b_2727_, 4);
v_query_2734_ = lean_ctor_get(v_b_2727_, 5);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_b_2727_);
if (v_isSharedCheck_2742_ == 0)
{
lean_object* v_unused_2743_; 
v_unused_2743_ = lean_ctor_get(v_b_2727_, 6);
lean_dec(v_unused_2743_);
v___x_2736_ = v_b_2727_;
v_isShared_2737_ = v_isSharedCheck_2742_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_query_2734_);
lean_inc(v_pathSegments_2733_);
lean_inc(v_port_2732_);
lean_inc(v_host_2731_);
lean_inc(v_userInfo_2730_);
lean_inc(v_scheme_2729_);
lean_dec(v_b_2727_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2742_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
v___x_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2738_, 0, v_fragment_2728_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 6, v___x_2738_);
v___x_2740_ = v___x_2736_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_scheme_2729_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_userInfo_2730_);
lean_ctor_set(v_reuseFailAlloc_2741_, 2, v_host_2731_);
lean_ctor_set(v_reuseFailAlloc_2741_, 3, v_port_2732_);
lean_ctor_set(v_reuseFailAlloc_2741_, 4, v_pathSegments_2733_);
lean_ctor_set(v_reuseFailAlloc_2741_, 5, v_query_2734_);
lean_ctor_set(v_reuseFailAlloc_2741_, 6, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(size_t v_sz_2744_, size_t v_i_2745_, lean_object* v_bs_2746_){
_start:
{
uint8_t v___x_2747_; 
v___x_2747_ = lean_usize_dec_lt(v_i_2745_, v_sz_2744_);
if (v___x_2747_ == 0)
{
return v_bs_2746_;
}
else
{
lean_object* v_v_2748_; lean_object* v___x_2749_; lean_object* v_bs_x27_2750_; lean_object* v___x_2751_; size_t v___x_2752_; size_t v___x_2753_; lean_object* v___x_2754_; 
v_v_2748_ = lean_array_uget(v_bs_2746_, v_i_2745_);
v___x_2749_ = lean_unsigned_to_nat(0u);
v_bs_x27_2750_ = lean_array_uset(v_bs_2746_, v_i_2745_, v___x_2749_);
v___x_2751_ = l_Std_Http_URI_EncodedSegment_encode(v_v_2748_);
lean_dec(v_v_2748_);
v___x_2752_ = ((size_t)1ULL);
v___x_2753_ = lean_usize_add(v_i_2745_, v___x_2752_);
v___x_2754_ = lean_array_uset(v_bs_x27_2750_, v_i_2745_, v___x_2751_);
v_i_2745_ = v___x_2753_;
v_bs_2746_ = v___x_2754_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0___boxed(lean_object* v_sz_2756_, lean_object* v_i_2757_, lean_object* v_bs_2758_){
_start:
{
size_t v_sz_boxed_2759_; size_t v_i_boxed_2760_; lean_object* v_res_2761_; 
v_sz_boxed_2759_ = lean_unbox_usize(v_sz_2756_);
lean_dec(v_sz_2756_);
v_i_boxed_2760_ = lean_unbox_usize(v_i_2757_);
lean_dec(v_i_2757_);
v_res_2761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_boxed_2759_, v_i_boxed_2760_, v_bs_2758_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(size_t v_sz_2762_, size_t v_i_2763_, lean_object* v_bs_2764_){
_start:
{
uint8_t v___x_2765_; 
v___x_2765_ = lean_usize_dec_lt(v_i_2763_, v_sz_2762_);
if (v___x_2765_ == 0)
{
return v_bs_2764_;
}
else
{
lean_object* v_v_2766_; lean_object* v_fst_2767_; lean_object* v_snd_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2797_; 
v_v_2766_ = lean_array_uget(v_bs_2764_, v_i_2763_);
v_fst_2767_ = lean_ctor_get(v_v_2766_, 0);
v_snd_2768_ = lean_ctor_get(v_v_2766_, 1);
v_isSharedCheck_2797_ = !lean_is_exclusive(v_v_2766_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2770_ = v_v_2766_;
v_isShared_2771_ = v_isSharedCheck_2797_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_snd_2768_);
lean_inc(v_fst_2767_);
lean_dec(v_v_2766_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2797_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2772_; lean_object* v_bs_x27_2773_; lean_object* v___y_2775_; lean_object* v___x_2780_; 
v___x_2772_ = lean_unsigned_to_nat(0u);
v_bs_x27_2773_ = lean_array_uset(v_bs_2764_, v_i_2763_, v___x_2772_);
v___x_2780_ = l_Std_Http_URI_EncodedQueryParam_encode(v_fst_2767_);
lean_dec(v_fst_2767_);
if (lean_obj_tag(v_snd_2768_) == 0)
{
lean_object* v___x_2781_; lean_object* v___x_2783_; 
v___x_2781_ = lean_box(0);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 1, v___x_2781_);
lean_ctor_set(v___x_2770_, 0, v___x_2780_);
v___x_2783_ = v___x_2770_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v___x_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
v___y_2775_ = v___x_2783_;
goto v___jp_2774_;
}
}
else
{
lean_object* v_val_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2796_; 
v_val_2785_ = lean_ctor_get(v_snd_2768_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_snd_2768_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2787_ = v_snd_2768_;
v_isShared_2788_ = v_isSharedCheck_2796_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_val_2785_);
lean_dec(v_snd_2768_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2796_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; lean_object* v___x_2791_; 
v___x_2789_ = l_Std_Http_URI_EncodedQueryParam_encode(v_val_2785_);
lean_dec(v_val_2785_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2789_);
v___x_2791_ = v___x_2787_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2789_);
v___x_2791_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2793_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 1, v___x_2791_);
lean_ctor_set(v___x_2770_, 0, v___x_2780_);
v___x_2793_ = v___x_2770_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v___x_2791_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
v___y_2775_ = v___x_2793_;
goto v___jp_2774_;
}
}
}
}
v___jp_2774_:
{
size_t v___x_2776_; size_t v___x_2777_; lean_object* v___x_2778_; 
v___x_2776_ = ((size_t)1ULL);
v___x_2777_ = lean_usize_add(v_i_2763_, v___x_2776_);
v___x_2778_ = lean_array_uset(v_bs_x27_2773_, v_i_2763_, v___y_2775_);
v_i_2763_ = v___x_2777_;
v_bs_2764_ = v___x_2778_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1___boxed(lean_object* v_sz_2798_, lean_object* v_i_2799_, lean_object* v_bs_2800_){
_start:
{
size_t v_sz_boxed_2801_; size_t v_i_boxed_2802_; lean_object* v_res_2803_; 
v_sz_boxed_2801_ = lean_unbox_usize(v_sz_2798_);
lean_dec(v_sz_2798_);
v_i_boxed_2802_ = lean_unbox_usize(v_i_2799_);
lean_dec(v_i_2799_);
v_res_2803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_boxed_2801_, v_i_boxed_2802_, v_bs_2800_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_build(lean_object* v_b_2804_){
_start:
{
lean_object* v___y_2806_; lean_object* v___y_2807_; uint8_t v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v_scheme_2821_; lean_object* v_userInfo_2822_; lean_object* v_host_2823_; lean_object* v_port_2824_; lean_object* v_pathSegments_2825_; lean_object* v_query_2826_; lean_object* v_fragment_2827_; lean_object* v___y_2829_; 
v_scheme_2821_ = lean_ctor_get(v_b_2804_, 0);
lean_inc(v_scheme_2821_);
v_userInfo_2822_ = lean_ctor_get(v_b_2804_, 1);
lean_inc(v_userInfo_2822_);
v_host_2823_ = lean_ctor_get(v_b_2804_, 2);
lean_inc(v_host_2823_);
v_port_2824_ = lean_ctor_get(v_b_2804_, 3);
lean_inc(v_port_2824_);
v_pathSegments_2825_ = lean_ctor_get(v_b_2804_, 4);
lean_inc_ref(v_pathSegments_2825_);
v_query_2826_ = lean_ctor_get(v_b_2804_, 5);
lean_inc_ref(v_query_2826_);
v_fragment_2827_ = lean_ctor_get(v_b_2804_, 6);
lean_inc(v_fragment_2827_);
lean_dec_ref(v_b_2804_);
if (lean_obj_tag(v_scheme_2821_) == 0)
{
lean_object* v___x_2842_; 
v___x_2842_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___y_2829_ = v___x_2842_;
goto v___jp_2828_;
}
else
{
lean_object* v_val_2843_; 
v_val_2843_ = lean_ctor_get(v_scheme_2821_, 0);
lean_inc(v_val_2843_);
lean_dec_ref(v_scheme_2821_);
v___y_2829_ = v_val_2843_;
goto v___jp_2828_;
}
v___jp_2805_:
{
size_t v_sz_2812_; size_t v___x_2813_; lean_object* v___x_2814_; lean_object* v_path_2815_; size_t v_sz_2816_; lean_object* v_query_2817_; lean_object* v___x_2818_; lean_object* v_query_2819_; lean_object* v___x_2820_; 
v_sz_2812_ = lean_array_size(v___y_2809_);
v___x_2813_ = ((size_t)0ULL);
v___x_2814_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_2812_, v___x_2813_, v___y_2809_);
v_path_2815_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_path_2815_, 0, v___x_2814_);
lean_ctor_set_uint8(v_path_2815_, sizeof(void*)*1, v___y_2808_);
v_sz_2816_ = lean_array_size(v___y_2806_);
v_query_2817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_2816_, v___x_2813_, v___y_2806_);
v___x_2818_ = lean_array_to_list(v_query_2817_);
v_query_2819_ = lean_array_mk(v___x_2818_);
v___x_2820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2820_, 0, v___y_2807_);
lean_ctor_set(v___x_2820_, 1, v___y_2811_);
lean_ctor_set(v___x_2820_, 2, v_path_2815_);
lean_ctor_set(v___x_2820_, 3, v_query_2819_);
lean_ctor_set(v___x_2820_, 4, v___y_2810_);
return v___x_2820_;
}
v___jp_2828_:
{
if (lean_obj_tag(v_host_2823_) == 0)
{
uint8_t v___x_2830_; lean_object* v___x_2831_; 
lean_dec(v_port_2824_);
lean_dec(v_userInfo_2822_);
v___x_2830_ = 1;
v___x_2831_ = lean_box(0);
v___y_2806_ = v_query_2826_;
v___y_2807_ = v___y_2829_;
v___y_2808_ = v___x_2830_;
v___y_2809_ = v_pathSegments_2825_;
v___y_2810_ = v_fragment_2827_;
v___y_2811_ = v___x_2831_;
goto v___jp_2805_;
}
else
{
lean_object* v_val_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2841_; 
v_val_2832_ = lean_ctor_get(v_host_2823_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_host_2823_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2834_ = v_host_2823_;
v_isShared_2835_ = v_isSharedCheck_2841_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_val_2832_);
lean_dec(v_host_2823_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2841_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
uint8_t v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2839_; 
v___x_2836_ = 1;
v___x_2837_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2837_, 0, v_userInfo_2822_);
lean_ctor_set(v___x_2837_, 1, v_val_2832_);
lean_ctor_set(v___x_2837_, 2, v_port_2824_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2837_);
v___x_2839_ = v___x_2834_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
v___y_2806_ = v_query_2826_;
v___y_2807_ = v___y_2829_;
v___y_2808_ = v___x_2836_;
v___y_2809_ = v_pathSegments_2825_;
v___y_2810_ = v_fragment_2827_;
v___y_2811_ = v___x_2839_;
goto v___jp_2805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withScheme_x21(lean_object* v_uri_2844_, lean_object* v_scheme_2845_){
_start:
{
lean_object* v_authority_2846_; lean_object* v_path_2847_; lean_object* v_query_2848_; lean_object* v_fragment_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2857_; 
v_authority_2846_ = lean_ctor_get(v_uri_2844_, 1);
v_path_2847_ = lean_ctor_get(v_uri_2844_, 2);
v_query_2848_ = lean_ctor_get(v_uri_2844_, 3);
v_fragment_2849_ = lean_ctor_get(v_uri_2844_, 4);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_uri_2844_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; 
v_unused_2858_ = lean_ctor_get(v_uri_2844_, 0);
lean_dec(v_unused_2858_);
v___x_2851_ = v_uri_2844_;
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_fragment_2849_);
lean_inc(v_query_2848_);
lean_inc(v_path_2847_);
lean_inc(v_authority_2846_);
lean_dec(v_uri_2844_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; lean_object* v___x_2855_; 
v___x_2853_ = l_Std_Http_URI_Scheme_ofString_x21(v_scheme_2845_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v___x_2853_);
v___x_2855_ = v___x_2851_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2853_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_authority_2846_);
lean_ctor_set(v_reuseFailAlloc_2856_, 2, v_path_2847_);
lean_ctor_set(v_reuseFailAlloc_2856_, 3, v_query_2848_);
lean_ctor_set(v_reuseFailAlloc_2856_, 4, v_fragment_2849_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withAuthority(lean_object* v_uri_2859_, lean_object* v_authority_2860_){
_start:
{
lean_object* v_scheme_2861_; lean_object* v_path_2862_; lean_object* v_query_2863_; lean_object* v_fragment_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
v_scheme_2861_ = lean_ctor_get(v_uri_2859_, 0);
v_path_2862_ = lean_ctor_get(v_uri_2859_, 2);
v_query_2863_ = lean_ctor_get(v_uri_2859_, 3);
v_fragment_2864_ = lean_ctor_get(v_uri_2859_, 4);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_uri_2859_);
if (v_isSharedCheck_2871_ == 0)
{
lean_object* v_unused_2872_; 
v_unused_2872_ = lean_ctor_get(v_uri_2859_, 1);
lean_dec(v_unused_2872_);
v___x_2866_ = v_uri_2859_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_fragment_2864_);
lean_inc(v_query_2863_);
lean_inc(v_path_2862_);
lean_inc(v_scheme_2861_);
lean_dec(v_uri_2859_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 1, v_authority_2860_);
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_scheme_2861_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_authority_2860_);
lean_ctor_set(v_reuseFailAlloc_2870_, 2, v_path_2862_);
lean_ctor_set(v_reuseFailAlloc_2870_, 3, v_query_2863_);
lean_ctor_set(v_reuseFailAlloc_2870_, 4, v_fragment_2864_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_withPath(lean_object* v_uri_2873_, lean_object* v_path_2874_){
_start:
{
lean_object* v_scheme_2875_; lean_object* v_authority_2876_; lean_object* v_query_2877_; lean_object* v_fragment_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
v_scheme_2875_ = lean_ctor_get(v_uri_2873_, 0);
v_authority_2876_ = lean_ctor_get(v_uri_2873_, 1);
v_query_2877_ = lean_ctor_get(v_uri_2873_, 3);
v_fragment_2878_ = lean_ctor_get(v_uri_2873_, 4);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_uri_2873_);
if (v_isSharedCheck_2885_ == 0)
{
lean_object* v_unused_2886_; 
v_unused_2886_ = lean_ctor_get(v_uri_2873_, 2);
lean_dec(v_unused_2886_);
v___x_2880_ = v_uri_2873_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_fragment_2878_);
lean_inc(v_query_2877_);
lean_inc(v_authority_2876_);
lean_inc(v_scheme_2875_);
lean_dec(v_uri_2873_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 2, v_path_2874_);
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_scheme_2875_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_authority_2876_);
lean_ctor_set(v_reuseFailAlloc_2884_, 2, v_path_2874_);
lean_ctor_set(v_reuseFailAlloc_2884_, 3, v_query_2877_);
lean_ctor_set(v_reuseFailAlloc_2884_, 4, v_fragment_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withQuery(lean_object* v_uri_2887_, lean_object* v_query_2888_){
_start:
{
lean_object* v_scheme_2889_; lean_object* v_authority_2890_; lean_object* v_path_2891_; lean_object* v_fragment_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
v_scheme_2889_ = lean_ctor_get(v_uri_2887_, 0);
v_authority_2890_ = lean_ctor_get(v_uri_2887_, 1);
v_path_2891_ = lean_ctor_get(v_uri_2887_, 2);
v_fragment_2892_ = lean_ctor_get(v_uri_2887_, 4);
v_isSharedCheck_2899_ = !lean_is_exclusive(v_uri_2887_);
if (v_isSharedCheck_2899_ == 0)
{
lean_object* v_unused_2900_; 
v_unused_2900_ = lean_ctor_get(v_uri_2887_, 3);
lean_dec(v_unused_2900_);
v___x_2894_ = v_uri_2887_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_fragment_2892_);
lean_inc(v_path_2891_);
lean_inc(v_authority_2890_);
lean_inc(v_scheme_2889_);
lean_dec(v_uri_2887_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 3, v_query_2888_);
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_scheme_2889_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v_authority_2890_);
lean_ctor_set(v_reuseFailAlloc_2898_, 2, v_path_2891_);
lean_ctor_set(v_reuseFailAlloc_2898_, 3, v_query_2888_);
lean_ctor_set(v_reuseFailAlloc_2898_, 4, v_fragment_2892_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_withFragment(lean_object* v_uri_2901_, lean_object* v_fragment_2902_){
_start:
{
lean_object* v_scheme_2903_; lean_object* v_authority_2904_; lean_object* v_path_2905_; lean_object* v_query_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
v_scheme_2903_ = lean_ctor_get(v_uri_2901_, 0);
v_authority_2904_ = lean_ctor_get(v_uri_2901_, 1);
v_path_2905_ = lean_ctor_get(v_uri_2901_, 2);
v_query_2906_ = lean_ctor_get(v_uri_2901_, 3);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_uri_2901_);
if (v_isSharedCheck_2913_ == 0)
{
lean_object* v_unused_2914_; 
v_unused_2914_ = lean_ctor_get(v_uri_2901_, 4);
lean_dec(v_unused_2914_);
v___x_2908_ = v_uri_2901_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_query_2906_);
lean_inc(v_path_2905_);
lean_inc(v_authority_2904_);
lean_inc(v_scheme_2903_);
lean_dec(v_uri_2901_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 4, v_fragment_2902_);
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_scheme_2903_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_authority_2904_);
lean_ctor_set(v_reuseFailAlloc_2912_, 2, v_path_2905_);
lean_ctor_set(v_reuseFailAlloc_2912_, 3, v_query_2906_);
lean_ctor_set(v_reuseFailAlloc_2912_, 4, v_fragment_2902_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_normalize(lean_object* v_uri_2915_){
_start:
{
lean_object* v_scheme_2916_; lean_object* v_authority_2917_; lean_object* v_path_2918_; lean_object* v_query_2919_; lean_object* v_fragment_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2928_; 
v_scheme_2916_ = lean_ctor_get(v_uri_2915_, 0);
v_authority_2917_ = lean_ctor_get(v_uri_2915_, 1);
v_path_2918_ = lean_ctor_get(v_uri_2915_, 2);
v_query_2919_ = lean_ctor_get(v_uri_2915_, 3);
v_fragment_2920_ = lean_ctor_get(v_uri_2915_, 4);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_uri_2915_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2922_ = v_uri_2915_;
v_isShared_2923_ = v_isSharedCheck_2928_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_fragment_2920_);
lean_inc(v_query_2919_);
lean_inc(v_path_2918_);
lean_inc(v_authority_2917_);
lean_inc(v_scheme_2916_);
lean_dec(v_uri_2915_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2928_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2924_; lean_object* v___x_2926_; 
v___x_2924_ = l_Std_Http_URI_Path_normalize(v_path_2918_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 2, v___x_2924_);
v___x_2926_ = v___x_2922_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_scheme_2916_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_authority_2917_);
lean_ctor_set(v_reuseFailAlloc_2927_, 2, v___x_2924_);
lean_ctor_set(v_reuseFailAlloc_2927_, 3, v_query_2919_);
lean_ctor_set(v_reuseFailAlloc_2927_, 4, v_fragment_2920_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx(lean_object* v_x_2929_){
_start:
{
switch(lean_obj_tag(v_x_2929_))
{
case 0:
{
lean_object* v___x_2930_; 
v___x_2930_ = lean_unsigned_to_nat(0u);
return v___x_2930_;
}
case 1:
{
lean_object* v___x_2931_; 
v___x_2931_ = lean_unsigned_to_nat(1u);
return v___x_2931_;
}
case 2:
{
lean_object* v___x_2932_; 
v___x_2932_ = lean_unsigned_to_nat(2u);
return v___x_2932_;
}
default: 
{
lean_object* v___x_2933_; 
v___x_2933_ = lean_unsigned_to_nat(3u);
return v___x_2933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___boxed(lean_object* v_x_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Std_Http_RequestTarget_ctorIdx(v_x_2934_);
lean_dec(v_x_2934_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___redArg(lean_object* v_t_2936_, lean_object* v_k_2937_){
_start:
{
switch(lean_obj_tag(v_t_2936_))
{
case 0:
{
lean_object* v_path_2938_; lean_object* v_query_2939_; lean_object* v___x_2940_; 
v_path_2938_ = lean_ctor_get(v_t_2936_, 0);
lean_inc_ref(v_path_2938_);
v_query_2939_ = lean_ctor_get(v_t_2936_, 1);
lean_inc(v_query_2939_);
lean_dec_ref(v_t_2936_);
v___x_2940_ = lean_apply_2(v_k_2937_, v_path_2938_, v_query_2939_);
return v___x_2940_;
}
case 3:
{
return v_k_2937_;
}
default: 
{
lean_object* v_uri_2941_; lean_object* v___x_2942_; 
v_uri_2941_ = lean_ctor_get(v_t_2936_, 0);
lean_inc_ref(v_uri_2941_);
lean_dec(v_t_2936_);
v___x_2942_ = lean_apply_1(v_k_2937_, v_uri_2941_);
return v___x_2942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim(lean_object* v_motive_2943_, lean_object* v_ctorIdx_2944_, lean_object* v_t_2945_, lean_object* v_h_2946_, lean_object* v_k_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2945_, v_k_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___boxed(lean_object* v_motive_2949_, lean_object* v_ctorIdx_2950_, lean_object* v_t_2951_, lean_object* v_h_2952_, lean_object* v_k_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Std_Http_RequestTarget_ctorElim(v_motive_2949_, v_ctorIdx_2950_, v_t_2951_, v_h_2952_, v_k_2953_);
lean_dec(v_ctorIdx_2950_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim___redArg(lean_object* v_t_2955_, lean_object* v_originForm_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2955_, v_originForm_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim(lean_object* v_motive_2958_, lean_object* v_t_2959_, lean_object* v_h_2960_, lean_object* v_originForm_2961_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2959_, v_originForm_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim___redArg(lean_object* v_t_2963_, lean_object* v_absoluteForm_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2963_, v_absoluteForm_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim(lean_object* v_motive_2966_, lean_object* v_t_2967_, lean_object* v_h_2968_, lean_object* v_absoluteForm_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2967_, v_absoluteForm_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim___redArg(lean_object* v_t_2971_, lean_object* v_authorityForm_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2971_, v_authorityForm_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim(lean_object* v_motive_2974_, lean_object* v_t_2975_, lean_object* v_h_2976_, lean_object* v_authorityForm_2977_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2975_, v_authorityForm_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim___redArg(lean_object* v_t_2979_, lean_object* v_asteriskForm_2980_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2979_, v_asteriskForm_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim(lean_object* v_motive_2982_, lean_object* v_t_2983_, lean_object* v_h_2984_, lean_object* v_asteriskForm_2985_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2983_, v_asteriskForm_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0(lean_object* v_x_2992_, lean_object* v_x_2993_){
_start:
{
if (lean_obj_tag(v_x_2992_) == 0)
{
lean_object* v___x_2994_; 
v___x_2994_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2994_;
}
else
{
lean_object* v_val_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v_val_2995_ = lean_ctor_get(v_x_2992_, 0);
lean_inc(v_val_2995_);
lean_dec_ref(v_x_2992_);
v___x_2996_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2997_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_val_2995_);
v___x_2998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2996_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
v___x_2999_ = l_Repr_addAppParen(v___x_2998_, v_x_2993_);
return v___x_2999_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0___boxed(lean_object* v_x_3000_, lean_object* v_x_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0(v_x_3000_, v_x_3001_);
lean_dec(v_x_3001_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object* v_x_3024_, lean_object* v_prec_3025_){
_start:
{
lean_object* v___y_3027_; 
switch(lean_obj_tag(v_x_3024_))
{
case 0:
{
lean_object* v_path_3033_; lean_object* v_query_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3058_; 
v_path_3033_ = lean_ctor_get(v_x_3024_, 0);
v_query_3034_ = lean_ctor_get(v_x_3024_, 1);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_x_3024_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3036_ = v_x_3024_;
v_isShared_3037_ = v_isSharedCheck_3058_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_query_3034_);
lean_inc(v_path_3033_);
lean_dec(v_x_3024_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3058_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___y_3039_; lean_object* v___x_3054_; uint8_t v___x_3055_; 
v___x_3054_ = lean_unsigned_to_nat(1024u);
v___x_3055_ = lean_nat_dec_le(v___x_3054_, v_prec_3025_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; 
v___x_3056_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3039_ = v___x_3056_;
goto v___jp_3038_;
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3039_ = v___x_3057_;
goto v___jp_3038_;
}
v___jp_3038_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3045_; 
v___x_3040_ = lean_box(1);
v___x_3041_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__4));
v___x_3042_ = lean_unsigned_to_nat(1024u);
v___x_3043_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3033_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set_tag(v___x_3036_, 5);
lean_ctor_set(v___x_3036_, 1, v___x_3043_);
lean_ctor_set(v___x_3036_, 0, v___x_3041_);
v___x_3045_ = v___x_3036_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3041_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v___x_3043_);
v___x_3045_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; uint8_t v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
lean_ctor_set(v___x_3046_, 1, v___x_3040_);
v___x_3047_ = l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0(v_query_3034_, v___x_3042_);
v___x_3048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3046_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
lean_inc(v___y_3039_);
v___x_3049_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___y_3039_);
lean_ctor_set(v___x_3049_, 1, v___x_3048_);
v___x_3050_ = 0;
v___x_3051_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3051_, 0, v___x_3049_);
lean_ctor_set_uint8(v___x_3051_, sizeof(void*)*1, v___x_3050_);
v___x_3052_ = l_Repr_addAppParen(v___x_3051_, v_prec_3025_);
return v___x_3052_;
}
}
}
}
case 1:
{
lean_object* v_uri_3059_; lean_object* v___y_3061_; lean_object* v___x_3069_; uint8_t v___x_3070_; 
v_uri_3059_ = lean_ctor_get(v_x_3024_, 0);
lean_inc_ref(v_uri_3059_);
lean_dec_ref(v_x_3024_);
v___x_3069_ = lean_unsigned_to_nat(1024u);
v___x_3070_ = lean_nat_dec_le(v___x_3069_, v_prec_3025_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; 
v___x_3071_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3061_ = v___x_3071_;
goto v___jp_3060_;
}
else
{
lean_object* v___x_3072_; 
v___x_3072_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3061_ = v___x_3072_;
goto v___jp_3060_;
}
v___jp_3060_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3062_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__7));
v___x_3063_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3059_);
v___x_3064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3062_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
lean_inc(v___y_3061_);
v___x_3065_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___y_3061_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = 0;
v___x_3067_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3067_, 0, v___x_3065_);
lean_ctor_set_uint8(v___x_3067_, sizeof(void*)*1, v___x_3066_);
v___x_3068_ = l_Repr_addAppParen(v___x_3067_, v_prec_3025_);
return v___x_3068_;
}
}
case 2:
{
lean_object* v_authority_3073_; lean_object* v___y_3075_; lean_object* v___x_3083_; uint8_t v___x_3084_; 
v_authority_3073_ = lean_ctor_get(v_x_3024_, 0);
lean_inc_ref(v_authority_3073_);
lean_dec_ref(v_x_3024_);
v___x_3083_ = lean_unsigned_to_nat(1024u);
v___x_3084_ = lean_nat_dec_le(v___x_3083_, v_prec_3025_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; 
v___x_3085_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3075_ = v___x_3085_;
goto v___jp_3074_;
}
else
{
lean_object* v___x_3086_; 
v___x_3086_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3075_ = v___x_3086_;
goto v___jp_3074_;
}
v___jp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3076_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__10));
v___x_3077_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_authority_3073_);
v___x_3078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3076_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
lean_inc(v___y_3075_);
v___x_3079_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___y_3075_);
lean_ctor_set(v___x_3079_, 1, v___x_3078_);
v___x_3080_ = 0;
v___x_3081_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3081_, 0, v___x_3079_);
lean_ctor_set_uint8(v___x_3081_, sizeof(void*)*1, v___x_3080_);
v___x_3082_ = l_Repr_addAppParen(v___x_3081_, v_prec_3025_);
return v___x_3082_;
}
}
default: 
{
lean_object* v___x_3087_; uint8_t v___x_3088_; 
v___x_3087_ = lean_unsigned_to_nat(1024u);
v___x_3088_ = lean_nat_dec_le(v___x_3087_, v_prec_3025_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; 
v___x_3089_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3027_ = v___x_3089_;
goto v___jp_3026_;
}
else
{
lean_object* v___x_3090_; 
v___x_3090_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3027_ = v___x_3090_;
goto v___jp_3026_;
}
}
}
v___jp_3026_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; uint8_t v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3028_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__1));
lean_inc(v___y_3027_);
v___x_3029_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___y_3027_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = 0;
v___x_3031_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3031_, 0, v___x_3029_);
lean_ctor_set_uint8(v___x_3031_, sizeof(void*)*1, v___x_3030_);
v___x_3032_ = l_Repr_addAppParen(v___x_3031_, v_prec_3025_);
return v___x_3032_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr___boxed(lean_object* v_x_3091_, lean_object* v_prec_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Std_Http_instReprRequestTarget_repr(v_x_3091_, v_prec_3092_);
lean_dec(v_prec_3092_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path(lean_object* v_x_3101_){
_start:
{
switch(lean_obj_tag(v_x_3101_))
{
case 0:
{
lean_object* v_path_3102_; 
v_path_3102_ = lean_ctor_get(v_x_3101_, 0);
lean_inc_ref(v_path_3102_);
return v_path_3102_;
}
case 1:
{
lean_object* v_uri_3103_; lean_object* v_path_3104_; 
v_uri_3103_ = lean_ctor_get(v_x_3101_, 0);
v_path_3104_ = lean_ctor_get(v_uri_3103_, 2);
lean_inc_ref(v_path_3104_);
return v_path_3104_;
}
default: 
{
lean_object* v___x_3105_; 
v___x_3105_ = ((lean_object*)(l_Std_Http_RequestTarget_path___closed__1));
return v___x_3105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path___boxed(lean_object* v_x_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Std_Http_RequestTarget_path(v_x_3106_);
lean_dec(v_x_3106_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query(lean_object* v_x_3108_){
_start:
{
switch(lean_obj_tag(v_x_3108_))
{
case 0:
{
lean_object* v_query_3109_; 
v_query_3109_ = lean_ctor_get(v_x_3108_, 1);
if (lean_obj_tag(v_query_3109_) == 0)
{
lean_object* v___x_3110_; 
v___x_3110_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3110_;
}
else
{
lean_object* v_val_3111_; 
v_val_3111_ = lean_ctor_get(v_query_3109_, 0);
lean_inc(v_val_3111_);
return v_val_3111_;
}
}
case 1:
{
lean_object* v_uri_3112_; lean_object* v_query_3113_; 
v_uri_3112_ = lean_ctor_get(v_x_3108_, 0);
v_query_3113_ = lean_ctor_get(v_uri_3112_, 3);
lean_inc_ref(v_query_3113_);
return v_query_3113_;
}
default: 
{
lean_object* v___x_3114_; 
v___x_3114_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query___boxed(lean_object* v_x_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Std_Http_RequestTarget_query(v_x_3115_);
lean_dec(v_x_3115_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authority_x3f(lean_object* v_x_3117_){
_start:
{
switch(lean_obj_tag(v_x_3117_))
{
case 2:
{
lean_object* v_authority_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
v_authority_3118_ = lean_ctor_get(v_x_3117_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_x_3117_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v_x_3117_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_authority_3118_);
lean_dec(v_x_3117_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
lean_ctor_set_tag(v___x_3120_, 1);
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_authority_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
case 1:
{
lean_object* v_uri_3126_; lean_object* v_authority_3127_; 
v_uri_3126_ = lean_ctor_get(v_x_3117_, 0);
lean_inc_ref(v_uri_3126_);
lean_dec_ref(v_x_3117_);
v_authority_3127_ = lean_ctor_get(v_uri_3126_, 1);
lean_inc(v_authority_3127_);
lean_dec_ref(v_uri_3126_);
return v_authority_3127_;
}
default: 
{
lean_object* v___x_3128_; 
lean_dec(v_x_3117_);
v___x_3128_ = lean_box(0);
return v___x_3128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__4(lean_object* v___f_3130_, lean_object* v___f_3131_, lean_object* v___f_3132_, lean_object* v___f_3133_, lean_object* v_x_3134_){
_start:
{
lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; 
switch(lean_obj_tag(v_x_3134_))
{
case 0:
{
lean_object* v_path_3141_; lean_object* v_query_3142_; lean_object* v___y_3144_; lean_object* v_segments_3157_; uint8_t v_absolute_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; size_t v_sz_3161_; size_t v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v_result_3165_; 
lean_dec_ref(v___f_3133_);
lean_dec_ref(v___f_3132_);
v_path_3141_ = lean_ctor_get(v_x_3134_, 0);
lean_inc_ref(v_path_3141_);
v_query_3142_ = lean_ctor_get(v_x_3134_, 1);
lean_inc(v_query_3142_);
lean_dec_ref(v_x_3134_);
v_segments_3157_ = lean_ctor_get(v_path_3141_, 0);
lean_inc_ref(v_segments_3157_);
v_absolute_3158_ = lean_ctor_get_uint8(v_path_3141_, sizeof(void*)*1);
lean_dec_ref(v_path_3141_);
v___x_3159_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3160_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3161_ = lean_array_size(v_segments_3157_);
v___x_3162_ = ((size_t)0ULL);
v___x_3163_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3160_, v___f_3131_, v_sz_3161_, v___x_3162_, v_segments_3157_);
v___x_3164_ = lean_array_to_list(v___x_3163_);
v_result_3165_ = l_String_intercalate(v___x_3159_, v___x_3164_);
if (v_absolute_3158_ == 0)
{
v___y_3144_ = v_result_3165_;
goto v___jp_3143_;
}
else
{
lean_object* v___x_3166_; 
v___x_3166_ = lean_string_append(v___x_3159_, v_result_3165_);
lean_dec_ref(v_result_3165_);
v___y_3144_ = v___x_3166_;
goto v___jp_3143_;
}
v___jp_3143_:
{
if (lean_obj_tag(v_query_3142_) == 0)
{
lean_dec_ref(v___f_3130_);
return v___y_3144_;
}
else
{
lean_object* v_val_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; uint8_t v___x_3148_; 
v_val_3145_ = lean_ctor_get(v_query_3142_, 0);
lean_inc(v_val_3145_);
lean_dec_ref(v_query_3142_);
v___x_3146_ = lean_array_get_size(v_val_3145_);
v___x_3147_ = lean_unsigned_to_nat(0u);
v___x_3148_ = lean_nat_dec_eq(v___x_3146_, v___x_3147_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v_encodedParams_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3149_ = lean_array_to_list(v_val_3145_);
v___x_3150_ = lean_box(0);
v_encodedParams_3151_ = l_List_mapTR_loop___redArg(v___f_3130_, v___x_3149_, v___x_3150_);
v___x_3152_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_3153_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_3154_ = l_String_intercalate(v___x_3153_, v_encodedParams_3151_);
v___x_3155_ = lean_string_append(v___x_3152_, v___x_3154_);
lean_dec_ref(v___x_3154_);
v___x_3156_ = lean_string_append(v___y_3144_, v___x_3155_);
lean_dec_ref(v___x_3155_);
return v___x_3156_;
}
else
{
lean_dec(v_val_3145_);
lean_dec_ref(v___f_3130_);
return v___y_3144_;
}
}
}
}
case 1:
{
lean_object* v_uri_3167_; lean_object* v_scheme_3168_; lean_object* v_authority_3169_; lean_object* v_path_3170_; lean_object* v_query_3171_; lean_object* v_fragment_3172_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3209_; 
lean_dec_ref(v___f_3131_);
lean_dec_ref(v___f_3130_);
v_uri_3167_ = lean_ctor_get(v_x_3134_, 0);
lean_inc_ref(v_uri_3167_);
lean_dec_ref(v_x_3134_);
v_scheme_3168_ = lean_ctor_get(v_uri_3167_, 0);
lean_inc_ref(v_scheme_3168_);
v_authority_3169_ = lean_ctor_get(v_uri_3167_, 1);
lean_inc(v_authority_3169_);
v_path_3170_ = lean_ctor_get(v_uri_3167_, 2);
lean_inc_ref(v_path_3170_);
v_query_3171_ = lean_ctor_get(v_uri_3167_, 3);
lean_inc_ref(v_query_3171_);
v_fragment_3172_ = lean_ctor_get(v_uri_3167_, 4);
lean_inc(v_fragment_3172_);
lean_dec_ref(v_uri_3167_);
if (lean_obj_tag(v_authority_3169_) == 0)
{
lean_object* v___x_3220_; 
v___x_3220_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3209_ = v___x_3220_;
goto v___jp_3208_;
}
else
{
lean_object* v_val_3221_; lean_object* v_userInfo_3222_; lean_object* v_host_3223_; lean_object* v_port_3224_; lean_object* v___x_3225_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3244_; 
v_val_3221_ = lean_ctor_get(v_authority_3169_, 0);
lean_inc(v_val_3221_);
lean_dec_ref(v_authority_3169_);
v_userInfo_3222_ = lean_ctor_get(v_val_3221_, 0);
lean_inc(v_userInfo_3222_);
v_host_3223_ = lean_ctor_get(v_val_3221_, 1);
lean_inc_ref(v_host_3223_);
v_port_3224_ = lean_ctor_get(v_val_3221_, 2);
lean_inc(v_port_3224_);
lean_dec(v_val_3221_);
v___x_3225_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__1));
if (lean_obj_tag(v_userInfo_3222_) == 0)
{
lean_object* v___x_3254_; 
v___x_3254_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3244_ = v___x_3254_;
goto v___jp_3243_;
}
else
{
lean_object* v_val_3255_; lean_object* v_password_3256_; 
v_val_3255_ = lean_ctor_get(v_userInfo_3222_, 0);
lean_inc(v_val_3255_);
lean_dec_ref(v_userInfo_3222_);
v_password_3256_ = lean_ctor_get(v_val_3255_, 1);
if (lean_obj_tag(v_password_3256_) == 0)
{
lean_object* v_username_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v_username_3257_ = lean_ctor_get(v_val_3255_, 0);
lean_inc_ref(v_username_3257_);
lean_dec(v_val_3255_);
v___x_3258_ = lean_string_from_utf8_unchecked(v_username_3257_);
v___x_3259_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3260_ = lean_string_append(v___x_3258_, v___x_3259_);
v___y_3244_ = v___x_3260_;
goto v___jp_3243_;
}
else
{
lean_object* v_username_3261_; lean_object* v_val_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
lean_inc_ref(v_password_3256_);
v_username_3261_ = lean_ctor_get(v_val_3255_, 0);
lean_inc_ref(v_username_3261_);
lean_dec(v_val_3255_);
v_val_3262_ = lean_ctor_get(v_password_3256_, 0);
lean_inc(v_val_3262_);
lean_dec_ref(v_password_3256_);
v___x_3263_ = lean_string_from_utf8_unchecked(v_username_3261_);
v___x_3264_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3265_ = lean_string_append(v___x_3263_, v___x_3264_);
v___x_3266_ = lean_string_from_utf8_unchecked(v_val_3262_);
v___x_3267_ = lean_string_append(v___x_3265_, v___x_3266_);
lean_dec_ref(v___x_3266_);
v___x_3268_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3269_ = lean_string_append(v___x_3267_, v___x_3268_);
v___y_3244_ = v___x_3269_;
goto v___jp_3243_;
}
}
v___jp_3226_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = lean_string_append(v___y_3228_, v___y_3227_);
lean_dec_ref(v___y_3227_);
v___x_3231_ = lean_string_append(v___x_3230_, v___y_3229_);
lean_dec_ref(v___y_3229_);
v___x_3232_ = lean_string_append(v___x_3225_, v___x_3231_);
lean_dec_ref(v___x_3231_);
v___y_3209_ = v___x_3232_;
goto v___jp_3208_;
}
v___jp_3233_:
{
switch(lean_obj_tag(v_port_3224_))
{
case 0:
{
lean_object* v___x_3236_; 
v___x_3236_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3227_ = v___y_3235_;
v___y_3228_ = v___y_3234_;
v___y_3229_ = v___x_3236_;
goto v___jp_3226_;
}
case 1:
{
lean_object* v___x_3237_; 
v___x_3237_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3227_ = v___y_3235_;
v___y_3228_ = v___y_3234_;
v___y_3229_ = v___x_3237_;
goto v___jp_3226_;
}
default: 
{
uint16_t v_port_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v_port_3238_ = lean_ctor_get_uint16(v_port_3224_, 0);
lean_dec_ref(v_port_3224_);
v___x_3239_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3240_ = lean_uint16_to_nat(v_port_3238_);
v___x_3241_ = l_Nat_reprFast(v___x_3240_);
v___x_3242_ = lean_string_append(v___x_3239_, v___x_3241_);
lean_dec_ref(v___x_3241_);
v___y_3227_ = v___y_3235_;
v___y_3228_ = v___y_3234_;
v___y_3229_ = v___x_3242_;
goto v___jp_3226_;
}
}
}
v___jp_3243_:
{
switch(lean_obj_tag(v_host_3223_))
{
case 0:
{
lean_object* v_name_3245_; 
v_name_3245_ = lean_ctor_get(v_host_3223_, 0);
lean_inc_ref(v_name_3245_);
lean_dec_ref(v_host_3223_);
v___y_3234_ = v___y_3244_;
v___y_3235_ = v_name_3245_;
goto v___jp_3233_;
}
case 1:
{
lean_object* v_ipv4_3246_; lean_object* v___x_3247_; 
v_ipv4_3246_ = lean_ctor_get(v_host_3223_, 0);
lean_inc_ref(v_ipv4_3246_);
lean_dec_ref(v_host_3223_);
v___x_3247_ = lean_uv_ntop_v4(v_ipv4_3246_);
lean_dec_ref(v_ipv4_3246_);
v___y_3234_ = v___y_3244_;
v___y_3235_ = v___x_3247_;
goto v___jp_3233_;
}
default: 
{
lean_object* v_ipv6_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v_ipv6_3248_ = lean_ctor_get(v_host_3223_, 0);
lean_inc_ref(v_ipv6_3248_);
lean_dec_ref(v_host_3223_);
v___x_3249_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3250_ = lean_uv_ntop_v6(v_ipv6_3248_);
lean_dec_ref(v_ipv6_3248_);
v___x_3251_ = lean_string_append(v___x_3249_, v___x_3250_);
lean_dec_ref(v___x_3250_);
v___x_3252_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3253_ = lean_string_append(v___x_3251_, v___x_3252_);
v___y_3234_ = v___y_3244_;
v___y_3235_ = v___x_3253_;
goto v___jp_3233_;
}
}
}
}
v___jp_3173_:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3178_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3179_ = lean_string_append(v_scheme_3168_, v___x_3178_);
v___x_3180_ = lean_string_append(v___x_3179_, v___y_3176_);
lean_dec_ref(v___y_3176_);
v___x_3181_ = lean_string_append(v___x_3180_, v___y_3175_);
lean_dec_ref(v___y_3175_);
v___x_3182_ = lean_string_append(v___x_3181_, v___y_3174_);
lean_dec_ref(v___y_3174_);
v___x_3183_ = lean_string_append(v___x_3182_, v___y_3177_);
lean_dec_ref(v___y_3177_);
return v___x_3183_;
}
v___jp_3184_:
{
if (lean_obj_tag(v_fragment_3172_) == 0)
{
lean_object* v___x_3188_; 
v___x_3188_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3174_ = v___y_3187_;
v___y_3175_ = v___y_3185_;
v___y_3176_ = v___y_3186_;
v___y_3177_ = v___x_3188_;
goto v___jp_3173_;
}
else
{
lean_object* v_val_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v_val_3189_ = lean_ctor_get(v_fragment_3172_, 0);
lean_inc(v_val_3189_);
lean_dec_ref(v_fragment_3172_);
v___x_3190_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__0));
v___x_3191_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3189_);
lean_dec(v_val_3189_);
v___x_3192_ = lean_string_from_utf8_unchecked(v___x_3191_);
v___x_3193_ = lean_string_append(v___x_3190_, v___x_3192_);
lean_dec_ref(v___x_3192_);
v___y_3174_ = v___y_3187_;
v___y_3175_ = v___y_3185_;
v___y_3176_ = v___y_3186_;
v___y_3177_ = v___x_3193_;
goto v___jp_3173_;
}
}
v___jp_3194_:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; 
v___x_3197_ = lean_array_get_size(v_query_3171_);
v___x_3198_ = lean_unsigned_to_nat(0u);
v___x_3199_ = lean_nat_dec_eq(v___x_3197_, v___x_3198_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v_encodedParams_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3200_ = lean_array_to_list(v_query_3171_);
v___x_3201_ = lean_box(0);
v_encodedParams_3202_ = l_List_mapTR_loop___redArg(v___f_3132_, v___x_3200_, v___x_3201_);
v___x_3203_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_3204_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_3205_ = l_String_intercalate(v___x_3204_, v_encodedParams_3202_);
v___x_3206_ = lean_string_append(v___x_3203_, v___x_3205_);
lean_dec_ref(v___x_3205_);
v___y_3185_ = v___y_3196_;
v___y_3186_ = v___y_3195_;
v___y_3187_ = v___x_3206_;
goto v___jp_3184_;
}
else
{
lean_object* v___x_3207_; 
lean_dec_ref(v_query_3171_);
lean_dec_ref(v___f_3132_);
v___x_3207_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3185_ = v___y_3196_;
v___y_3186_ = v___y_3195_;
v___y_3187_ = v___x_3207_;
goto v___jp_3184_;
}
}
v___jp_3208_:
{
lean_object* v_segments_3210_; uint8_t v_absolute_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; size_t v_sz_3214_; size_t v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v_result_3218_; 
v_segments_3210_ = lean_ctor_get(v_path_3170_, 0);
lean_inc_ref(v_segments_3210_);
v_absolute_3211_ = lean_ctor_get_uint8(v_path_3170_, sizeof(void*)*1);
lean_dec_ref(v_path_3170_);
v___x_3212_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3213_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3214_ = lean_array_size(v_segments_3210_);
v___x_3215_ = ((size_t)0ULL);
v___x_3216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3213_, v___f_3133_, v_sz_3214_, v___x_3215_, v_segments_3210_);
v___x_3217_ = lean_array_to_list(v___x_3216_);
v_result_3218_ = l_String_intercalate(v___x_3212_, v___x_3217_);
if (v_absolute_3211_ == 0)
{
v___y_3195_ = v___y_3209_;
v___y_3196_ = v_result_3218_;
goto v___jp_3194_;
}
else
{
lean_object* v___x_3219_; 
v___x_3219_ = lean_string_append(v___x_3212_, v_result_3218_);
lean_dec_ref(v_result_3218_);
v___y_3195_ = v___y_3209_;
v___y_3196_ = v___x_3219_;
goto v___jp_3194_;
}
}
}
case 2:
{
lean_object* v_authority_3270_; lean_object* v_userInfo_3271_; lean_object* v_host_3272_; lean_object* v_port_3273_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3285_; 
lean_dec_ref(v___f_3133_);
lean_dec_ref(v___f_3132_);
lean_dec_ref(v___f_3131_);
lean_dec_ref(v___f_3130_);
v_authority_3270_ = lean_ctor_get(v_x_3134_, 0);
lean_inc_ref(v_authority_3270_);
lean_dec_ref(v_x_3134_);
v_userInfo_3271_ = lean_ctor_get(v_authority_3270_, 0);
lean_inc(v_userInfo_3271_);
v_host_3272_ = lean_ctor_get(v_authority_3270_, 1);
lean_inc_ref(v_host_3272_);
v_port_3273_ = lean_ctor_get(v_authority_3270_, 2);
lean_inc(v_port_3273_);
lean_dec_ref(v_authority_3270_);
if (lean_obj_tag(v_userInfo_3271_) == 0)
{
lean_object* v___x_3295_; 
v___x_3295_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3285_ = v___x_3295_;
goto v___jp_3284_;
}
else
{
lean_object* v_val_3296_; lean_object* v_password_3297_; 
v_val_3296_ = lean_ctor_get(v_userInfo_3271_, 0);
lean_inc(v_val_3296_);
lean_dec_ref(v_userInfo_3271_);
v_password_3297_ = lean_ctor_get(v_val_3296_, 1);
if (lean_obj_tag(v_password_3297_) == 0)
{
lean_object* v_username_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v_username_3298_ = lean_ctor_get(v_val_3296_, 0);
lean_inc_ref(v_username_3298_);
lean_dec(v_val_3296_);
v___x_3299_ = lean_string_from_utf8_unchecked(v_username_3298_);
v___x_3300_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3301_ = lean_string_append(v___x_3299_, v___x_3300_);
v___y_3285_ = v___x_3301_;
goto v___jp_3284_;
}
else
{
lean_object* v_username_3302_; lean_object* v_val_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
lean_inc_ref(v_password_3297_);
v_username_3302_ = lean_ctor_get(v_val_3296_, 0);
lean_inc_ref(v_username_3302_);
lean_dec(v_val_3296_);
v_val_3303_ = lean_ctor_get(v_password_3297_, 0);
lean_inc(v_val_3303_);
lean_dec_ref(v_password_3297_);
v___x_3304_ = lean_string_from_utf8_unchecked(v_username_3302_);
v___x_3305_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3306_ = lean_string_append(v___x_3304_, v___x_3305_);
v___x_3307_ = lean_string_from_utf8_unchecked(v_val_3303_);
v___x_3308_ = lean_string_append(v___x_3306_, v___x_3307_);
lean_dec_ref(v___x_3307_);
v___x_3309_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3310_ = lean_string_append(v___x_3308_, v___x_3309_);
v___y_3285_ = v___x_3310_;
goto v___jp_3284_;
}
}
v___jp_3274_:
{
switch(lean_obj_tag(v_port_3273_))
{
case 0:
{
lean_object* v___x_3277_; 
v___x_3277_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3136_ = v___y_3275_;
v___y_3137_ = v___y_3276_;
v___y_3138_ = v___x_3277_;
goto v___jp_3135_;
}
case 1:
{
lean_object* v___x_3278_; 
v___x_3278_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3136_ = v___y_3275_;
v___y_3137_ = v___y_3276_;
v___y_3138_ = v___x_3278_;
goto v___jp_3135_;
}
default: 
{
uint16_t v_port_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v_port_3279_ = lean_ctor_get_uint16(v_port_3273_, 0);
lean_dec_ref(v_port_3273_);
v___x_3280_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3281_ = lean_uint16_to_nat(v_port_3279_);
v___x_3282_ = l_Nat_reprFast(v___x_3281_);
v___x_3283_ = lean_string_append(v___x_3280_, v___x_3282_);
lean_dec_ref(v___x_3282_);
v___y_3136_ = v___y_3275_;
v___y_3137_ = v___y_3276_;
v___y_3138_ = v___x_3283_;
goto v___jp_3135_;
}
}
}
v___jp_3284_:
{
switch(lean_obj_tag(v_host_3272_))
{
case 0:
{
lean_object* v_name_3286_; 
v_name_3286_ = lean_ctor_get(v_host_3272_, 0);
lean_inc_ref(v_name_3286_);
lean_dec_ref(v_host_3272_);
v___y_3275_ = v___y_3285_;
v___y_3276_ = v_name_3286_;
goto v___jp_3274_;
}
case 1:
{
lean_object* v_ipv4_3287_; lean_object* v___x_3288_; 
v_ipv4_3287_ = lean_ctor_get(v_host_3272_, 0);
lean_inc_ref(v_ipv4_3287_);
lean_dec_ref(v_host_3272_);
v___x_3288_ = lean_uv_ntop_v4(v_ipv4_3287_);
lean_dec_ref(v_ipv4_3287_);
v___y_3275_ = v___y_3285_;
v___y_3276_ = v___x_3288_;
goto v___jp_3274_;
}
default: 
{
lean_object* v_ipv6_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v_ipv6_3289_ = lean_ctor_get(v_host_3272_, 0);
lean_inc_ref(v_ipv6_3289_);
lean_dec_ref(v_host_3272_);
v___x_3290_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3291_ = lean_uv_ntop_v6(v_ipv6_3289_);
lean_dec_ref(v_ipv6_3289_);
v___x_3292_ = lean_string_append(v___x_3290_, v___x_3291_);
lean_dec_ref(v___x_3291_);
v___x_3293_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3294_ = lean_string_append(v___x_3292_, v___x_3293_);
v___y_3275_ = v___y_3285_;
v___y_3276_ = v___x_3294_;
goto v___jp_3274_;
}
}
}
}
default: 
{
lean_object* v___x_3311_; 
lean_dec_ref(v___f_3133_);
lean_dec_ref(v___f_3132_);
lean_dec_ref(v___f_3131_);
lean_dec_ref(v___f_3130_);
v___x_3311_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__4___closed__0));
return v___x_3311_;
}
}
v___jp_3135_:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3139_ = lean_string_append(v___y_3136_, v___y_3137_);
lean_dec_ref(v___y_3137_);
v___x_3140_ = lean_string_append(v___x_3139_, v___y_3138_);
lean_dec_ref(v___y_3138_);
return v___x_3140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__4(lean_object* v___f_3316_, lean_object* v___f_3317_, lean_object* v___f_3318_, lean_object* v___f_3319_, lean_object* v_buffer_3320_, lean_object* v_target_3321_){
_start:
{
lean_object* v___y_3323_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; 
switch(lean_obj_tag(v_target_3321_))
{
case 0:
{
lean_object* v_path_3343_; lean_object* v_query_3344_; lean_object* v___y_3346_; lean_object* v_segments_3359_; uint8_t v_absolute_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; size_t v_sz_3363_; size_t v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v_result_3367_; 
lean_dec_ref(v___f_3319_);
lean_dec_ref(v___f_3318_);
v_path_3343_ = lean_ctor_get(v_target_3321_, 0);
lean_inc_ref(v_path_3343_);
v_query_3344_ = lean_ctor_get(v_target_3321_, 1);
lean_inc(v_query_3344_);
lean_dec_ref(v_target_3321_);
v_segments_3359_ = lean_ctor_get(v_path_3343_, 0);
lean_inc_ref(v_segments_3359_);
v_absolute_3360_ = lean_ctor_get_uint8(v_path_3343_, sizeof(void*)*1);
lean_dec_ref(v_path_3343_);
v___x_3361_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3362_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3363_ = lean_array_size(v_segments_3359_);
v___x_3364_ = ((size_t)0ULL);
v___x_3365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3362_, v___f_3317_, v_sz_3363_, v___x_3364_, v_segments_3359_);
v___x_3366_ = lean_array_to_list(v___x_3365_);
v_result_3367_ = l_String_intercalate(v___x_3361_, v___x_3366_);
if (v_absolute_3360_ == 0)
{
v___y_3346_ = v_result_3367_;
goto v___jp_3345_;
}
else
{
lean_object* v___x_3368_; 
v___x_3368_ = lean_string_append(v___x_3361_, v_result_3367_);
lean_dec_ref(v_result_3367_);
v___y_3346_ = v___x_3368_;
goto v___jp_3345_;
}
v___jp_3345_:
{
if (lean_obj_tag(v_query_3344_) == 0)
{
lean_dec_ref(v___f_3316_);
v___y_3323_ = v___y_3346_;
goto v___jp_3322_;
}
else
{
lean_object* v_val_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; uint8_t v___x_3350_; 
v_val_3347_ = lean_ctor_get(v_query_3344_, 0);
lean_inc(v_val_3347_);
lean_dec_ref(v_query_3344_);
v___x_3348_ = lean_array_get_size(v_val_3347_);
v___x_3349_ = lean_unsigned_to_nat(0u);
v___x_3350_ = lean_nat_dec_eq(v___x_3348_, v___x_3349_);
if (v___x_3350_ == 0)
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v_encodedParams_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3351_ = lean_array_to_list(v_val_3347_);
v___x_3352_ = lean_box(0);
v_encodedParams_3353_ = l_List_mapTR_loop___redArg(v___f_3316_, v___x_3351_, v___x_3352_);
v___x_3354_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_3355_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_3356_ = l_String_intercalate(v___x_3355_, v_encodedParams_3353_);
v___x_3357_ = lean_string_append(v___x_3354_, v___x_3356_);
lean_dec_ref(v___x_3356_);
v___x_3358_ = lean_string_append(v___y_3346_, v___x_3357_);
lean_dec_ref(v___x_3357_);
v___y_3323_ = v___x_3358_;
goto v___jp_3322_;
}
else
{
lean_dec(v_val_3347_);
lean_dec_ref(v___f_3316_);
v___y_3323_ = v___y_3346_;
goto v___jp_3322_;
}
}
}
}
case 1:
{
lean_object* v_uri_3369_; lean_object* v_scheme_3370_; lean_object* v_authority_3371_; lean_object* v_path_3372_; lean_object* v_query_3373_; lean_object* v_fragment_3374_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3411_; 
lean_dec_ref(v___f_3317_);
lean_dec_ref(v___f_3316_);
v_uri_3369_ = lean_ctor_get(v_target_3321_, 0);
lean_inc_ref(v_uri_3369_);
lean_dec_ref(v_target_3321_);
v_scheme_3370_ = lean_ctor_get(v_uri_3369_, 0);
lean_inc_ref(v_scheme_3370_);
v_authority_3371_ = lean_ctor_get(v_uri_3369_, 1);
lean_inc(v_authority_3371_);
v_path_3372_ = lean_ctor_get(v_uri_3369_, 2);
lean_inc_ref(v_path_3372_);
v_query_3373_ = lean_ctor_get(v_uri_3369_, 3);
lean_inc_ref(v_query_3373_);
v_fragment_3374_ = lean_ctor_get(v_uri_3369_, 4);
lean_inc(v_fragment_3374_);
lean_dec_ref(v_uri_3369_);
if (lean_obj_tag(v_authority_3371_) == 0)
{
lean_object* v___x_3422_; 
v___x_3422_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3411_ = v___x_3422_;
goto v___jp_3410_;
}
else
{
lean_object* v_val_3423_; lean_object* v_userInfo_3424_; lean_object* v_host_3425_; lean_object* v_port_3426_; lean_object* v___x_3427_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3446_; 
v_val_3423_ = lean_ctor_get(v_authority_3371_, 0);
lean_inc(v_val_3423_);
lean_dec_ref(v_authority_3371_);
v_userInfo_3424_ = lean_ctor_get(v_val_3423_, 0);
lean_inc(v_userInfo_3424_);
v_host_3425_ = lean_ctor_get(v_val_3423_, 1);
lean_inc_ref(v_host_3425_);
v_port_3426_ = lean_ctor_get(v_val_3423_, 2);
lean_inc(v_port_3426_);
lean_dec(v_val_3423_);
v___x_3427_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__1));
if (lean_obj_tag(v_userInfo_3424_) == 0)
{
lean_object* v___x_3456_; 
v___x_3456_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3446_ = v___x_3456_;
goto v___jp_3445_;
}
else
{
lean_object* v_val_3457_; lean_object* v_password_3458_; 
v_val_3457_ = lean_ctor_get(v_userInfo_3424_, 0);
lean_inc(v_val_3457_);
lean_dec_ref(v_userInfo_3424_);
v_password_3458_ = lean_ctor_get(v_val_3457_, 1);
if (lean_obj_tag(v_password_3458_) == 0)
{
lean_object* v_username_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v_username_3459_ = lean_ctor_get(v_val_3457_, 0);
lean_inc_ref(v_username_3459_);
lean_dec(v_val_3457_);
v___x_3460_ = lean_string_from_utf8_unchecked(v_username_3459_);
v___x_3461_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3462_ = lean_string_append(v___x_3460_, v___x_3461_);
v___y_3446_ = v___x_3462_;
goto v___jp_3445_;
}
else
{
lean_object* v_username_3463_; lean_object* v_val_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_inc_ref(v_password_3458_);
v_username_3463_ = lean_ctor_get(v_val_3457_, 0);
lean_inc_ref(v_username_3463_);
lean_dec(v_val_3457_);
v_val_3464_ = lean_ctor_get(v_password_3458_, 0);
lean_inc(v_val_3464_);
lean_dec_ref(v_password_3458_);
v___x_3465_ = lean_string_from_utf8_unchecked(v_username_3463_);
v___x_3466_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3467_ = lean_string_append(v___x_3465_, v___x_3466_);
v___x_3468_ = lean_string_from_utf8_unchecked(v_val_3464_);
v___x_3469_ = lean_string_append(v___x_3467_, v___x_3468_);
lean_dec_ref(v___x_3468_);
v___x_3470_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3471_ = lean_string_append(v___x_3469_, v___x_3470_);
v___y_3446_ = v___x_3471_;
goto v___jp_3445_;
}
}
v___jp_3428_:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3432_ = lean_string_append(v___y_3430_, v___y_3429_);
lean_dec_ref(v___y_3429_);
v___x_3433_ = lean_string_append(v___x_3432_, v___y_3431_);
lean_dec_ref(v___y_3431_);
v___x_3434_ = lean_string_append(v___x_3427_, v___x_3433_);
lean_dec_ref(v___x_3433_);
v___y_3411_ = v___x_3434_;
goto v___jp_3410_;
}
v___jp_3435_:
{
switch(lean_obj_tag(v_port_3426_))
{
case 0:
{
lean_object* v___x_3438_; 
v___x_3438_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3429_ = v___y_3437_;
v___y_3430_ = v___y_3436_;
v___y_3431_ = v___x_3438_;
goto v___jp_3428_;
}
case 1:
{
lean_object* v___x_3439_; 
v___x_3439_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3429_ = v___y_3437_;
v___y_3430_ = v___y_3436_;
v___y_3431_ = v___x_3439_;
goto v___jp_3428_;
}
default: 
{
uint16_t v_port_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v_port_3440_ = lean_ctor_get_uint16(v_port_3426_, 0);
lean_dec_ref(v_port_3426_);
v___x_3441_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3442_ = lean_uint16_to_nat(v_port_3440_);
v___x_3443_ = l_Nat_reprFast(v___x_3442_);
v___x_3444_ = lean_string_append(v___x_3441_, v___x_3443_);
lean_dec_ref(v___x_3443_);
v___y_3429_ = v___y_3437_;
v___y_3430_ = v___y_3436_;
v___y_3431_ = v___x_3444_;
goto v___jp_3428_;
}
}
}
v___jp_3445_:
{
switch(lean_obj_tag(v_host_3425_))
{
case 0:
{
lean_object* v_name_3447_; 
v_name_3447_ = lean_ctor_get(v_host_3425_, 0);
lean_inc_ref(v_name_3447_);
lean_dec_ref(v_host_3425_);
v___y_3436_ = v___y_3446_;
v___y_3437_ = v_name_3447_;
goto v___jp_3435_;
}
case 1:
{
lean_object* v_ipv4_3448_; lean_object* v___x_3449_; 
v_ipv4_3448_ = lean_ctor_get(v_host_3425_, 0);
lean_inc_ref(v_ipv4_3448_);
lean_dec_ref(v_host_3425_);
v___x_3449_ = lean_uv_ntop_v4(v_ipv4_3448_);
lean_dec_ref(v_ipv4_3448_);
v___y_3436_ = v___y_3446_;
v___y_3437_ = v___x_3449_;
goto v___jp_3435_;
}
default: 
{
lean_object* v_ipv6_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v_ipv6_3450_ = lean_ctor_get(v_host_3425_, 0);
lean_inc_ref(v_ipv6_3450_);
lean_dec_ref(v_host_3425_);
v___x_3451_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3452_ = lean_uv_ntop_v6(v_ipv6_3450_);
lean_dec_ref(v_ipv6_3450_);
v___x_3453_ = lean_string_append(v___x_3451_, v___x_3452_);
lean_dec_ref(v___x_3452_);
v___x_3454_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3455_ = lean_string_append(v___x_3453_, v___x_3454_);
v___y_3436_ = v___y_3446_;
v___y_3437_ = v___x_3455_;
goto v___jp_3435_;
}
}
}
}
v___jp_3375_:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3380_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3381_ = lean_string_append(v_scheme_3370_, v___x_3380_);
v___x_3382_ = lean_string_append(v___x_3381_, v___y_3376_);
lean_dec_ref(v___y_3376_);
v___x_3383_ = lean_string_append(v___x_3382_, v___y_3378_);
lean_dec_ref(v___y_3378_);
v___x_3384_ = lean_string_append(v___x_3383_, v___y_3377_);
lean_dec_ref(v___y_3377_);
v___x_3385_ = lean_string_append(v___x_3384_, v___y_3379_);
lean_dec_ref(v___y_3379_);
v___y_3323_ = v___x_3385_;
goto v___jp_3322_;
}
v___jp_3386_:
{
if (lean_obj_tag(v_fragment_3374_) == 0)
{
lean_object* v___x_3390_; 
v___x_3390_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3376_ = v___y_3387_;
v___y_3377_ = v___y_3389_;
v___y_3378_ = v___y_3388_;
v___y_3379_ = v___x_3390_;
goto v___jp_3375_;
}
else
{
lean_object* v_val_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v_val_3391_ = lean_ctor_get(v_fragment_3374_, 0);
lean_inc(v_val_3391_);
lean_dec_ref(v_fragment_3374_);
v___x_3392_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__0));
v___x_3393_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3391_);
lean_dec(v_val_3391_);
v___x_3394_ = lean_string_from_utf8_unchecked(v___x_3393_);
v___x_3395_ = lean_string_append(v___x_3392_, v___x_3394_);
lean_dec_ref(v___x_3394_);
v___y_3376_ = v___y_3387_;
v___y_3377_ = v___y_3389_;
v___y_3378_ = v___y_3388_;
v___y_3379_ = v___x_3395_;
goto v___jp_3375_;
}
}
v___jp_3396_:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v___x_3399_ = lean_array_get_size(v_query_3373_);
v___x_3400_ = lean_unsigned_to_nat(0u);
v___x_3401_ = lean_nat_dec_eq(v___x_3399_, v___x_3400_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v_encodedParams_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3402_ = lean_array_to_list(v_query_3373_);
v___x_3403_ = lean_box(0);
v_encodedParams_3404_ = l_List_mapTR_loop___redArg(v___f_3318_, v___x_3402_, v___x_3403_);
v___x_3405_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_3406_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_3407_ = l_String_intercalate(v___x_3406_, v_encodedParams_3404_);
v___x_3408_ = lean_string_append(v___x_3405_, v___x_3407_);
lean_dec_ref(v___x_3407_);
v___y_3387_ = v___y_3397_;
v___y_3388_ = v___y_3398_;
v___y_3389_ = v___x_3408_;
goto v___jp_3386_;
}
else
{
lean_object* v___x_3409_; 
lean_dec_ref(v_query_3373_);
lean_dec_ref(v___f_3318_);
v___x_3409_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3387_ = v___y_3397_;
v___y_3388_ = v___y_3398_;
v___y_3389_ = v___x_3409_;
goto v___jp_3386_;
}
}
v___jp_3410_:
{
lean_object* v_segments_3412_; uint8_t v_absolute_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; size_t v_sz_3416_; size_t v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v_result_3420_; 
v_segments_3412_ = lean_ctor_get(v_path_3372_, 0);
lean_inc_ref(v_segments_3412_);
v_absolute_3413_ = lean_ctor_get_uint8(v_path_3372_, sizeof(void*)*1);
lean_dec_ref(v_path_3372_);
v___x_3414_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3415_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3416_ = lean_array_size(v_segments_3412_);
v___x_3417_ = ((size_t)0ULL);
v___x_3418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3415_, v___f_3319_, v_sz_3416_, v___x_3417_, v_segments_3412_);
v___x_3419_ = lean_array_to_list(v___x_3418_);
v_result_3420_ = l_String_intercalate(v___x_3414_, v___x_3419_);
if (v_absolute_3413_ == 0)
{
v___y_3397_ = v___y_3411_;
v___y_3398_ = v_result_3420_;
goto v___jp_3396_;
}
else
{
lean_object* v___x_3421_; 
v___x_3421_ = lean_string_append(v___x_3414_, v_result_3420_);
lean_dec_ref(v_result_3420_);
v___y_3397_ = v___y_3411_;
v___y_3398_ = v___x_3421_;
goto v___jp_3396_;
}
}
}
case 2:
{
lean_object* v_authority_3472_; lean_object* v_userInfo_3473_; lean_object* v_host_3474_; lean_object* v_port_3475_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3487_; 
lean_dec_ref(v___f_3319_);
lean_dec_ref(v___f_3318_);
lean_dec_ref(v___f_3317_);
lean_dec_ref(v___f_3316_);
v_authority_3472_ = lean_ctor_get(v_target_3321_, 0);
lean_inc_ref(v_authority_3472_);
lean_dec_ref(v_target_3321_);
v_userInfo_3473_ = lean_ctor_get(v_authority_3472_, 0);
lean_inc(v_userInfo_3473_);
v_host_3474_ = lean_ctor_get(v_authority_3472_, 1);
lean_inc_ref(v_host_3474_);
v_port_3475_ = lean_ctor_get(v_authority_3472_, 2);
lean_inc(v_port_3475_);
lean_dec_ref(v_authority_3472_);
if (lean_obj_tag(v_userInfo_3473_) == 0)
{
lean_object* v___x_3497_; 
v___x_3497_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3487_ = v___x_3497_;
goto v___jp_3486_;
}
else
{
lean_object* v_val_3498_; lean_object* v_password_3499_; 
v_val_3498_ = lean_ctor_get(v_userInfo_3473_, 0);
lean_inc(v_val_3498_);
lean_dec_ref(v_userInfo_3473_);
v_password_3499_ = lean_ctor_get(v_val_3498_, 1);
if (lean_obj_tag(v_password_3499_) == 0)
{
lean_object* v_username_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v_username_3500_ = lean_ctor_get(v_val_3498_, 0);
lean_inc_ref(v_username_3500_);
lean_dec(v_val_3498_);
v___x_3501_ = lean_string_from_utf8_unchecked(v_username_3500_);
v___x_3502_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3503_ = lean_string_append(v___x_3501_, v___x_3502_);
v___y_3487_ = v___x_3503_;
goto v___jp_3486_;
}
else
{
lean_object* v_username_3504_; lean_object* v_val_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_inc_ref(v_password_3499_);
v_username_3504_ = lean_ctor_get(v_val_3498_, 0);
lean_inc_ref(v_username_3504_);
lean_dec(v_val_3498_);
v_val_3505_ = lean_ctor_get(v_password_3499_, 0);
lean_inc(v_val_3505_);
lean_dec_ref(v_password_3499_);
v___x_3506_ = lean_string_from_utf8_unchecked(v_username_3504_);
v___x_3507_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3508_ = lean_string_append(v___x_3506_, v___x_3507_);
v___x_3509_ = lean_string_from_utf8_unchecked(v_val_3505_);
v___x_3510_ = lean_string_append(v___x_3508_, v___x_3509_);
lean_dec_ref(v___x_3509_);
v___x_3511_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3512_ = lean_string_append(v___x_3510_, v___x_3511_);
v___y_3487_ = v___x_3512_;
goto v___jp_3486_;
}
}
v___jp_3476_:
{
switch(lean_obj_tag(v_port_3475_))
{
case 0:
{
lean_object* v___x_3479_; 
v___x_3479_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3338_ = v___y_3478_;
v___y_3339_ = v___y_3477_;
v___y_3340_ = v___x_3479_;
goto v___jp_3337_;
}
case 1:
{
lean_object* v___x_3480_; 
v___x_3480_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3338_ = v___y_3478_;
v___y_3339_ = v___y_3477_;
v___y_3340_ = v___x_3480_;
goto v___jp_3337_;
}
default: 
{
uint16_t v_port_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v_port_3481_ = lean_ctor_get_uint16(v_port_3475_, 0);
lean_dec_ref(v_port_3475_);
v___x_3482_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3483_ = lean_uint16_to_nat(v_port_3481_);
v___x_3484_ = l_Nat_reprFast(v___x_3483_);
v___x_3485_ = lean_string_append(v___x_3482_, v___x_3484_);
lean_dec_ref(v___x_3484_);
v___y_3338_ = v___y_3478_;
v___y_3339_ = v___y_3477_;
v___y_3340_ = v___x_3485_;
goto v___jp_3337_;
}
}
}
v___jp_3486_:
{
switch(lean_obj_tag(v_host_3474_))
{
case 0:
{
lean_object* v_name_3488_; 
v_name_3488_ = lean_ctor_get(v_host_3474_, 0);
lean_inc_ref(v_name_3488_);
lean_dec_ref(v_host_3474_);
v___y_3477_ = v___y_3487_;
v___y_3478_ = v_name_3488_;
goto v___jp_3476_;
}
case 1:
{
lean_object* v_ipv4_3489_; lean_object* v___x_3490_; 
v_ipv4_3489_ = lean_ctor_get(v_host_3474_, 0);
lean_inc_ref(v_ipv4_3489_);
lean_dec_ref(v_host_3474_);
v___x_3490_ = lean_uv_ntop_v4(v_ipv4_3489_);
lean_dec_ref(v_ipv4_3489_);
v___y_3477_ = v___y_3487_;
v___y_3478_ = v___x_3490_;
goto v___jp_3476_;
}
default: 
{
lean_object* v_ipv6_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v_ipv6_3491_ = lean_ctor_get(v_host_3474_, 0);
lean_inc_ref(v_ipv6_3491_);
lean_dec_ref(v_host_3474_);
v___x_3492_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3493_ = lean_uv_ntop_v6(v_ipv6_3491_);
lean_dec_ref(v_ipv6_3491_);
v___x_3494_ = lean_string_append(v___x_3492_, v___x_3493_);
lean_dec_ref(v___x_3493_);
v___x_3495_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3496_ = lean_string_append(v___x_3494_, v___x_3495_);
v___y_3477_ = v___y_3487_;
v___y_3478_ = v___x_3496_;
goto v___jp_3476_;
}
}
}
}
default: 
{
lean_object* v___x_3513_; 
lean_dec_ref(v___f_3319_);
lean_dec_ref(v___f_3318_);
lean_dec_ref(v___f_3317_);
lean_dec_ref(v___f_3316_);
v___x_3513_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__4___closed__0));
v___y_3323_ = v___x_3513_;
goto v___jp_3322_;
}
}
v___jp_3322_:
{
lean_object* v_data_3324_; lean_object* v_size_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3336_; 
v_data_3324_ = lean_ctor_get(v_buffer_3320_, 0);
v_size_3325_ = lean_ctor_get(v_buffer_3320_, 1);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_buffer_3320_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3327_ = v_buffer_3320_;
v_isShared_3328_ = v_isSharedCheck_3336_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_size_3325_);
lean_inc(v_data_3324_);
lean_dec(v_buffer_3320_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3336_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3334_; 
v___x_3329_ = lean_string_to_utf8(v___y_3323_);
lean_dec_ref(v___y_3323_);
lean_inc_ref(v___x_3329_);
v___x_3330_ = lean_array_push(v_data_3324_, v___x_3329_);
v___x_3331_ = lean_byte_array_size(v___x_3329_);
lean_dec_ref(v___x_3329_);
v___x_3332_ = lean_nat_add(v_size_3325_, v___x_3331_);
lean_dec(v_size_3325_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 1, v___x_3332_);
lean_ctor_set(v___x_3327_, 0, v___x_3330_);
v___x_3334_ = v___x_3327_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3330_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v___x_3332_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
v___jp_3337_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = lean_string_append(v___y_3339_, v___y_3338_);
lean_dec_ref(v___y_3338_);
v___x_3342_ = lean_string_append(v___x_3341_, v___y_3340_);
lean_dec_ref(v___y_3340_);
v___y_3323_ = v___x_3342_;
goto v___jp_3322_;
}
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Std_Net(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Internal(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_URI_Encoding(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Data_URI_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Net(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_URI_Encoding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Data_URI_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Std_Net(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Internal(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_URI_Encoding(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Data_URI_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Net(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_URI_Encoding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_URI_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Data_URI_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Data_URI_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
