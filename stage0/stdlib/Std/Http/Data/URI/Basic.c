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
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0_value;
static const lean_string_object l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".."};
static const lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(lean_object*, lean_object*);
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
uint32_t v___y_6_; lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_string_utf8_byte_size(v_s_3_);
v___x_12_ = lean_nat_dec_eq(v_p_4_, v___x_11_);
if (v___x_12_ == 0)
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
lean_object* v_head_22_; lean_object* v_tail_23_; uint8_t v___y_25_; uint32_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; uint8_t v___y_51_; 
v_head_22_ = lean_ctor_get(v_x_20_, 0);
v_tail_23_ = lean_ctor_get(v_x_20_, 1);
v___x_46_ = lean_unbox_uint32(v_head_22_);
v___x_47_ = lean_uint32_to_nat(v___x_46_);
v___x_48_ = lean_unsigned_to_nat(128u);
v___x_49_ = lean_nat_dec_lt(v___x_47_, v___x_48_);
lean_dec(v___x_47_);
if (v___x_49_ == 0)
{
v___y_25_ = v___x_49_;
goto v___jp_24_;
}
else
{
uint32_t v___x_59_; uint32_t v___x_60_; uint8_t v___x_61_; 
v___x_59_ = 48;
v___x_60_ = lean_unbox_uint32(v_head_22_);
v___x_61_ = lean_uint32_dec_le(v___x_59_, v___x_60_);
if (v___x_61_ == 0)
{
v___y_51_ = v___x_61_;
goto v___jp_50_;
}
else
{
uint32_t v___x_62_; uint32_t v___x_63_; uint8_t v___x_64_; 
v___x_62_ = 57;
v___x_63_ = lean_unbox_uint32(v_head_22_);
v___x_64_ = lean_uint32_dec_le(v___x_63_, v___x_62_);
v___y_51_ = v___x_64_;
goto v___jp_50_;
}
}
v___jp_24_:
{
if (v___y_25_ == 0)
{
uint32_t v___x_26_; uint32_t v___x_27_; uint8_t v___x_28_; 
v___x_26_ = 43;
v___x_27_ = lean_unbox_uint32(v_head_22_);
v___x_28_ = lean_uint32_dec_eq(v___x_27_, v___x_26_);
if (v___x_28_ == 0)
{
uint32_t v___x_29_; uint32_t v___x_30_; uint8_t v___x_31_; 
v___x_29_ = 45;
v___x_30_ = lean_unbox_uint32(v_head_22_);
v___x_31_ = lean_uint32_dec_eq(v___x_30_, v___x_29_);
if (v___x_31_ == 0)
{
uint32_t v___x_32_; uint32_t v___x_33_; uint8_t v___x_34_; 
v___x_32_ = 46;
v___x_33_ = lean_unbox_uint32(v_head_22_);
v___x_34_ = lean_uint32_dec_eq(v___x_33_, v___x_32_);
if (v___x_34_ == 0)
{
return v___y_25_;
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
else
{
v_x_20_ = v_tail_23_;
goto _start;
}
}
v___jp_39_:
{
uint32_t v___x_40_; uint32_t v___x_41_; uint8_t v___x_42_; 
v___x_40_ = 97;
v___x_41_ = lean_unbox_uint32(v_head_22_);
v___x_42_ = lean_uint32_dec_le(v___x_40_, v___x_41_);
if (v___x_42_ == 0)
{
v___y_25_ = v___x_42_;
goto v___jp_24_;
}
else
{
uint32_t v___x_43_; uint32_t v___x_44_; uint8_t v___x_45_; 
v___x_43_ = 122;
v___x_44_ = lean_unbox_uint32(v_head_22_);
v___x_45_ = lean_uint32_dec_le(v___x_44_, v___x_43_);
v___y_25_ = v___x_45_;
goto v___jp_24_;
}
}
v___jp_50_:
{
if (v___y_51_ == 0)
{
uint32_t v___x_52_; uint32_t v___x_53_; uint8_t v___x_54_; 
v___x_52_ = 65;
v___x_53_ = lean_unbox_uint32(v_head_22_);
v___x_54_ = lean_uint32_dec_le(v___x_52_, v___x_53_);
if (v___x_54_ == 0)
{
goto v___jp_39_;
}
else
{
uint32_t v___x_55_; uint32_t v___x_56_; uint8_t v___x_57_; 
v___x_55_ = 90;
v___x_56_ = lean_unbox_uint32(v_head_22_);
v___x_57_ = lean_uint32_dec_le(v___x_56_, v___x_55_);
if (v___x_57_ == 0)
{
goto v___jp_39_;
}
else
{
v___y_25_ = v___x_49_;
goto v___jp_24_;
}
}
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
lean_object* v___x_69_; lean_object* v_lower_70_; uint8_t v_val_72_; uint8_t v___x_75_; 
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
v___x_77_ = lean_string_data(v_lower_70_);
v___x_78_ = l_List_all___at___00Std_Http_URI_Scheme_ofString_x3f_spec__1(v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
lean_dec(v___x_77_);
lean_dec_ref(v_lower_70_);
v___x_79_ = lean_box(0);
return v___x_79_;
}
else
{
lean_object* v___x_80_; 
v___x_80_ = l_List_head_x3f___redArg(v___x_77_);
lean_dec(v___x_77_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v___x_81_; 
lean_dec_ref(v_lower_70_);
v___x_81_ = lean_box(0);
return v___x_81_;
}
else
{
lean_object* v_val_82_; uint32_t v___x_90_; uint32_t v___x_91_; uint8_t v___x_92_; 
v_val_82_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_val_82_);
lean_dec_ref_known(v___x_80_, 1);
v___x_90_ = 65;
v___x_91_ = lean_unbox_uint32(v_val_82_);
v___x_92_ = lean_uint32_dec_le(v___x_90_, v___x_91_);
if (v___x_92_ == 0)
{
goto v___jp_83_;
}
else
{
uint32_t v___x_93_; uint32_t v___x_94_; uint8_t v___x_95_; 
v___x_93_ = 90;
v___x_94_ = lean_unbox_uint32(v_val_82_);
v___x_95_ = lean_uint32_dec_le(v___x_94_, v___x_93_);
if (v___x_95_ == 0)
{
goto v___jp_83_;
}
else
{
lean_dec(v_val_82_);
v_val_72_ = v___x_78_;
goto v___jp_71_;
}
}
v___jp_83_:
{
uint32_t v___x_84_; uint32_t v___x_85_; uint8_t v___x_86_; 
v___x_84_ = 97;
v___x_85_ = lean_unbox_uint32(v_val_82_);
v___x_86_ = lean_uint32_dec_le(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_dec(v_val_82_);
v_val_72_ = v___x_86_;
goto v___jp_71_;
}
else
{
uint32_t v___x_87_; uint32_t v___x_88_; uint8_t v___x_89_; 
v___x_87_ = 122;
v___x_88_ = lean_unbox_uint32(v_val_82_);
lean_dec(v_val_82_);
v___x_89_ = lean_uint32_dec_le(v___x_88_, v___x_87_);
v_val_72_ = v___x_89_;
goto v___jp_71_;
}
}
}
}
}
v___jp_71_:
{
if (v_val_72_ == 0)
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
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(lean_object* v_msg_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = ((lean_object*)(l_Std_Http_URI_instInhabitedScheme___closed__0));
v___x_98_ = lean_panic_fn_borrowed(v___x_97_, v_msg_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofString_x21(lean_object* v_s_102_){
_start:
{
lean_object* v___x_103_; 
lean_inc_ref(v_s_102_);
v___x_103_ = l_Std_Http_URI_Scheme_ofString_x3f(v_s_102_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_104_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_105_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__1));
v___x_106_ = lean_unsigned_to_nat(84u);
v___x_107_ = lean_unsigned_to_nat(12u);
v___x_108_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_109_ = l_String_quote(v_s_102_);
v___x_110_ = lean_string_append(v___x_108_, v___x_109_);
lean_dec_ref(v___x_109_);
v___x_111_ = l_mkPanicMessageWithDecl(v___x_104_, v___x_105_, v___x_106_, v___x_107_, v___x_110_);
lean_dec_ref(v___x_110_);
v___x_112_ = l_panic___at___00Std_Http_URI_Scheme_ofString_x21_spec__0(v___x_111_);
return v___x_112_;
}
else
{
lean_object* v_val_113_; 
lean_dec_ref(v_s_102_);
v_val_113_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_val_113_);
lean_dec_ref_known(v___x_103_, 1);
return v_val_113_;
}
}
}
LEAN_EXPORT uint16_t l_Std_Http_URI_Scheme_defaultPort(lean_object* v_scheme_115_){
_start:
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___x_117_ = lean_string_dec_eq(v_scheme_115_, v___x_116_);
if (v___x_117_ == 0)
{
uint16_t v___x_118_; 
v___x_118_ = 80;
return v___x_118_;
}
else
{
uint16_t v___x_119_; 
v___x_119_ = 443;
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_defaultPort___boxed(lean_object* v_scheme_120_){
_start:
{
uint16_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_120_);
lean_dec_ref(v_scheme_120_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofPort(uint16_t v_port_123_){
_start:
{
uint16_t v___x_124_; uint8_t v___x_125_; 
v___x_124_ = 443;
v___x_125_ = lean_uint16_dec_eq(v_port_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
v___x_126_ = ((lean_object*)(l_Std_Http_URI_instInhabitedScheme___closed__0));
return v___x_126_;
}
else
{
lean_object* v___x_127_; 
v___x_127_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Scheme_ofPort___boxed(lean_object* v_port_128_){
_start:
{
uint16_t v_port_boxed_129_; lean_object* v_res_130_; 
v_port_boxed_129_ = lean_unbox(v_port_128_);
v_res_130_ = l_Std_Http_URI_Scheme_ofPort(v_port_boxed_129_);
return v_res_130_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0(void){
_start:
{
uint32_t v___x_131_; uint8_t v___x_132_; 
v___x_131_ = 58;
v___x_132_ = lean_uint32_to_uint8(v___x_131_);
return v___x_132_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1(void){
_start:
{
uint32_t v___x_133_; uint8_t v___x_134_; 
v___x_133_ = 38;
v___x_134_ = lean_uint32_to_uint8(v___x_133_);
return v___x_134_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2(void){
_start:
{
uint32_t v___x_135_; uint8_t v___x_136_; 
v___x_135_ = 39;
v___x_136_ = lean_uint32_to_uint8(v___x_135_);
return v___x_136_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3(void){
_start:
{
uint32_t v___x_137_; uint8_t v___x_138_; 
v___x_137_ = 40;
v___x_138_ = lean_uint32_to_uint8(v___x_137_);
return v___x_138_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4(void){
_start:
{
uint32_t v___x_139_; uint8_t v___x_140_; 
v___x_139_ = 41;
v___x_140_ = lean_uint32_to_uint8(v___x_139_);
return v___x_140_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5(void){
_start:
{
uint32_t v___x_141_; uint8_t v___x_142_; 
v___x_141_ = 42;
v___x_142_ = lean_uint32_to_uint8(v___x_141_);
return v___x_142_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6(void){
_start:
{
uint32_t v___x_143_; uint8_t v___x_144_; 
v___x_143_ = 43;
v___x_144_ = lean_uint32_to_uint8(v___x_143_);
return v___x_144_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7(void){
_start:
{
uint32_t v___x_145_; uint8_t v___x_146_; 
v___x_145_ = 44;
v___x_146_ = lean_uint32_to_uint8(v___x_145_);
return v___x_146_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8(void){
_start:
{
uint32_t v___x_147_; uint8_t v___x_148_; 
v___x_147_ = 59;
v___x_148_ = lean_uint32_to_uint8(v___x_147_);
return v___x_148_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9(void){
_start:
{
uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = 61;
v___x_150_ = lean_uint32_to_uint8(v___x_149_);
return v___x_150_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10(void){
_start:
{
uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 33;
v___x_152_ = lean_uint32_to_uint8(v___x_151_);
return v___x_152_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11(void){
_start:
{
uint32_t v___x_153_; uint8_t v___x_154_; 
v___x_153_ = 36;
v___x_154_ = lean_uint32_to_uint8(v___x_153_);
return v___x_154_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12(void){
_start:
{
uint32_t v___x_155_; uint8_t v___x_156_; 
v___x_155_ = 95;
v___x_156_ = lean_uint32_to_uint8(v___x_155_);
return v___x_156_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13(void){
_start:
{
uint32_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 126;
v___x_158_ = lean_uint32_to_uint8(v___x_157_);
return v___x_158_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14(void){
_start:
{
uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 45;
v___x_160_ = lean_uint32_to_uint8(v___x_159_);
return v___x_160_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15(void){
_start:
{
uint32_t v___x_161_; uint8_t v___x_162_; 
v___x_161_ = 46;
v___x_162_ = lean_uint32_to_uint8(v___x_161_);
return v___x_162_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16(void){
_start:
{
uint32_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = 65;
v___x_164_ = lean_uint32_to_uint8(v___x_163_);
return v___x_164_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17(void){
_start:
{
uint32_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = 90;
v___x_166_ = lean_uint32_to_uint8(v___x_165_);
return v___x_166_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18(void){
_start:
{
uint32_t v___x_167_; uint8_t v___x_168_; 
v___x_167_ = 97;
v___x_168_ = lean_uint32_to_uint8(v___x_167_);
return v___x_168_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19(void){
_start:
{
uint32_t v___x_169_; uint8_t v___x_170_; 
v___x_169_ = 122;
v___x_170_ = lean_uint32_to_uint8(v___x_169_);
return v___x_170_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20(void){
_start:
{
uint32_t v___x_171_; uint8_t v___x_172_; 
v___x_171_ = 48;
v___x_172_ = lean_uint32_to_uint8(v___x_171_);
return v___x_172_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21(void){
_start:
{
uint32_t v___x_173_; uint8_t v___x_174_; 
v___x_173_ = 57;
v___x_174_ = lean_uint32_to_uint8(v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0(uint8_t v___y_175_){
_start:
{
uint8_t v___y_177_; uint8_t v___y_181_; uint8_t v___y_201_; uint8_t v___y_207_; uint8_t v___y_213_; uint8_t v___y_219_; uint8_t v___y_225_; uint8_t v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20);
v___x_231_ = lean_uint8_dec_le(v___x_230_, v___y_175_);
if (v___x_231_ == 0)
{
v___y_225_ = v___x_231_;
goto v___jp_224_;
}
else
{
uint8_t v___x_232_; uint8_t v___x_233_; 
v___x_232_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21);
v___x_233_ = lean_uint8_dec_le(v___y_175_, v___x_232_);
v___y_225_ = v___x_233_;
goto v___jp_224_;
}
v___jp_176_:
{
if (v___y_177_ == 0)
{
uint8_t v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0);
v___x_179_ = lean_uint8_dec_eq(v___y_175_, v___x_178_);
return v___x_179_;
}
else
{
return v___y_177_;
}
}
v___jp_180_:
{
if (v___y_181_ == 0)
{
uint8_t v___x_182_; uint8_t v___x_183_; 
v___x_182_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1);
v___x_183_ = lean_uint8_dec_eq(v___y_175_, v___x_182_);
if (v___x_183_ == 0)
{
uint8_t v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2);
v___x_185_ = lean_uint8_dec_eq(v___y_175_, v___x_184_);
if (v___x_185_ == 0)
{
uint8_t v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3);
v___x_187_ = lean_uint8_dec_eq(v___y_175_, v___x_186_);
if (v___x_187_ == 0)
{
uint8_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4);
v___x_189_ = lean_uint8_dec_eq(v___y_175_, v___x_188_);
if (v___x_189_ == 0)
{
uint8_t v___x_190_; uint8_t v___x_191_; 
v___x_190_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5);
v___x_191_ = lean_uint8_dec_eq(v___y_175_, v___x_190_);
if (v___x_191_ == 0)
{
uint8_t v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6);
v___x_193_ = lean_uint8_dec_eq(v___y_175_, v___x_192_);
if (v___x_193_ == 0)
{
uint8_t v___x_194_; uint8_t v___x_195_; 
v___x_194_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7);
v___x_195_ = lean_uint8_dec_eq(v___y_175_, v___x_194_);
if (v___x_195_ == 0)
{
uint8_t v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8);
v___x_197_ = lean_uint8_dec_eq(v___y_175_, v___x_196_);
if (v___x_197_ == 0)
{
uint8_t v___x_198_; uint8_t v___x_199_; 
v___x_198_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9);
v___x_199_ = lean_uint8_dec_eq(v___y_175_, v___x_198_);
v___y_177_ = v___x_199_;
goto v___jp_176_;
}
else
{
v___y_177_ = v___x_197_;
goto v___jp_176_;
}
}
else
{
v___y_177_ = v___x_195_;
goto v___jp_176_;
}
}
else
{
v___y_177_ = v___x_193_;
goto v___jp_176_;
}
}
else
{
v___y_177_ = v___x_191_;
goto v___jp_176_;
}
}
else
{
v___y_177_ = v___x_189_;
goto v___jp_176_;
}
}
else
{
v___y_177_ = v___x_187_;
goto v___jp_176_;
}
}
else
{
v___y_177_ = v___x_185_;
goto v___jp_176_;
}
}
else
{
v___y_177_ = v___x_183_;
goto v___jp_176_;
}
}
else
{
return v___y_181_;
}
}
v___jp_200_:
{
if (v___y_201_ == 0)
{
uint8_t v___x_202_; uint8_t v___x_203_; 
v___x_202_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10);
v___x_203_ = lean_uint8_dec_eq(v___y_175_, v___x_202_);
if (v___x_203_ == 0)
{
uint8_t v___x_204_; uint8_t v___x_205_; 
v___x_204_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11);
v___x_205_ = lean_uint8_dec_eq(v___y_175_, v___x_204_);
v___y_181_ = v___x_205_;
goto v___jp_180_;
}
else
{
v___y_181_ = v___x_203_;
goto v___jp_180_;
}
}
else
{
return v___y_201_;
}
}
v___jp_206_:
{
if (v___y_207_ == 0)
{
uint8_t v___x_208_; uint8_t v___x_209_; 
v___x_208_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12);
v___x_209_ = lean_uint8_dec_eq(v___y_175_, v___x_208_);
if (v___x_209_ == 0)
{
uint8_t v___x_210_; uint8_t v___x_211_; 
v___x_210_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13);
v___x_211_ = lean_uint8_dec_eq(v___y_175_, v___x_210_);
v___y_201_ = v___x_211_;
goto v___jp_200_;
}
else
{
v___y_201_ = v___x_209_;
goto v___jp_200_;
}
}
else
{
return v___y_207_;
}
}
v___jp_212_:
{
if (v___y_213_ == 0)
{
uint8_t v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14);
v___x_215_ = lean_uint8_dec_eq(v___y_175_, v___x_214_);
if (v___x_215_ == 0)
{
uint8_t v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15);
v___x_217_ = lean_uint8_dec_eq(v___y_175_, v___x_216_);
v___y_207_ = v___x_217_;
goto v___jp_206_;
}
else
{
v___y_207_ = v___x_215_;
goto v___jp_206_;
}
}
else
{
return v___y_213_;
}
}
v___jp_218_:
{
if (v___y_219_ == 0)
{
uint8_t v___x_220_; uint8_t v___x_221_; 
v___x_220_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16);
v___x_221_ = lean_uint8_dec_le(v___x_220_, v___y_175_);
if (v___x_221_ == 0)
{
v___y_213_ = v___x_221_;
goto v___jp_212_;
}
else
{
uint8_t v___x_222_; uint8_t v___x_223_; 
v___x_222_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17);
v___x_223_ = lean_uint8_dec_le(v___y_175_, v___x_222_);
v___y_213_ = v___x_223_;
goto v___jp_212_;
}
}
else
{
return v___y_219_;
}
}
v___jp_224_:
{
if (v___y_225_ == 0)
{
uint8_t v___x_226_; uint8_t v___x_227_; 
v___x_226_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18);
v___x_227_ = lean_uint8_dec_le(v___x_226_, v___y_175_);
if (v___x_227_ == 0)
{
v___y_219_ = v___x_227_;
goto v___jp_218_;
}
else
{
uint8_t v___x_228_; uint8_t v___x_229_; 
v___x_228_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19);
v___x_229_ = lean_uint8_dec_le(v___y_175_, v___x_228_);
v___y_219_ = v___x_229_;
goto v___jp_218_;
}
}
else
{
return v___y_225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___boxed(lean_object* v___y_234_){
_start:
{
uint8_t v___y_322__boxed_235_; uint8_t v_res_236_; lean_object* v_r_237_; 
v___y_322__boxed_235_ = lean_unbox(v___y_234_);
v_res_236_ = l_Std_Http_URI_instInhabitedUserInfo_default___lam__0(v___y_322__boxed_235_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__1(void){
_start:
{
lean_object* v___f_239_; lean_object* v___x_240_; 
v___f_239_ = ((lean_object*)(l_Std_Http_URI_instInhabitedUserInfo_default___closed__0));
v___x_240_ = l_Std_Http_URI_EncodedString_empty(v___f_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__2(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_box(0);
v___x_242_ = lean_obj_once(&l_Std_Http_URI_instInhabitedUserInfo_default___closed__1, &l_Std_Http_URI_instInhabitedUserInfo_default___closed__1_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__1);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
return v___x_243_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default(void){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_obj_once(&l_Std_Http_URI_instInhabitedUserInfo_default___closed__2, &l_Std_Http_URI_instInhabitedUserInfo_default___closed__2_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__2);
return v___x_244_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo(void){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Std_Http_URI_instInhabitedUserInfo_default;
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
lean_object* v___x_254_; 
v___x_254_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_254_;
}
else
{
lean_object* v_val_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_267_; 
v_val_255_ = lean_ctor_get(v_x_252_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v_x_252_);
if (v_isSharedCheck_267_ == 0)
{
v___x_257_ = v_x_252_;
v_isShared_258_ = v_isSharedCheck_267_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_val_255_);
lean_dec(v_x_252_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_267_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_259_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_260_ = lean_string_from_utf8_unchecked(v_val_255_);
v___x_261_ = l_String_quote(v___x_260_);
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 3);
lean_ctor_set(v___x_257_, 0, v___x_261_);
v___x_263_ = v___x_257_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_266_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_259_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = l_Repr_addAppParen(v___x_264_, v_x_253_);
return v___x_265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___boxed(lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_x_268_, v_x_269_);
lean_dec(v_x_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_URI_instReprUserInfo_repr_spec__1(lean_object* v_a_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_nat_to_int(v_a_271_);
return v___x_272_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(12u);
v___x_287_ = lean_nat_to_int(v___x_286_);
return v___x_287_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0));
v___x_296_ = lean_string_length(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13);
v___x_298_ = lean_nat_to_int(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg(lean_object* v_x_303_){
_start:
{
lean_object* v_username_304_; lean_object* v_password_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_340_; 
v_username_304_ = lean_ctor_get(v_x_303_, 0);
v_password_305_ = lean_ctor_get(v_x_303_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v_x_303_);
if (v_isSharedCheck_340_ == 0)
{
v___x_307_ = v_x_303_;
v_isShared_308_ = v_isSharedCheck_340_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_password_305_);
lean_inc(v_username_304_);
lean_dec(v_x_303_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_340_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_309_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_310_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__6));
v___x_311_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_312_ = lean_string_from_utf8_unchecked(v_username_304_);
v___x_313_ = l_String_quote(v___x_312_);
v___x_314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 4);
lean_ctor_set(v___x_307_, 1, v___x_314_);
lean_ctor_set(v___x_307_, 0, v___x_311_);
v___x_316_ = v___x_307_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v___x_314_);
v___x_316_ = v_reuseFailAlloc_339_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_317_ = 0;
v___x_318_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*1, v___x_317_);
v___x_319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_310_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = lean_box(1);
v___x_323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__11));
v___x_325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_309_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_password_305_, v___x_327_);
v___x_329_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_311_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set_uint8(v___x_330_, sizeof(void*)*1, v___x_317_);
v___x_331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_326_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_333_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_331_);
v___x_335_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_332_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*1, v___x_317_);
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr(lean_object* v_x_341_, lean_object* v_prec_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_x_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___boxed(lean_object* v_x_344_, lean_object* v_prec_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Std_Http_URI_instReprUserInfo_repr(v_x_344_, v_prec_345_);
lean_dec(v_prec_345_);
return v_res_346_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_349_) == 0)
{
if (lean_obj_tag(v_x_350_) == 0)
{
uint8_t v___x_351_; 
v___x_351_ = 1;
return v___x_351_;
}
else
{
uint8_t v___x_352_; 
v___x_352_ = 0;
return v___x_352_;
}
}
else
{
if (lean_obj_tag(v_x_350_) == 0)
{
uint8_t v___x_353_; 
v___x_353_ = 0;
return v___x_353_;
}
else
{
lean_object* v_val_354_; lean_object* v_val_355_; uint8_t v___x_356_; 
v_val_354_ = lean_ctor_get(v_x_349_, 0);
v_val_355_ = lean_ctor_get(v_x_350_, 0);
v___x_356_ = lean_sarray_dec_eq(v_val_354_, v_val_355_);
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0___boxed(lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_x_357_, v_x_358_);
lean_dec(v_x_358_);
lean_dec(v_x_357_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqUserInfo_beq(lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
lean_object* v_username_363_; lean_object* v_password_364_; lean_object* v_username_365_; lean_object* v_password_366_; uint8_t v___x_367_; 
v_username_363_ = lean_ctor_get(v_x_361_, 0);
v_password_364_ = lean_ctor_get(v_x_361_, 1);
v_username_365_ = lean_ctor_get(v_x_362_, 0);
v_password_366_ = lean_ctor_get(v_x_362_, 1);
v___x_367_ = lean_sarray_dec_eq(v_username_363_, v_username_365_);
if (v___x_367_ == 0)
{
return v___x_367_;
}
else
{
uint8_t v___x_368_; 
v___x_368_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_password_364_, v_password_366_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqUserInfo_beq___boxed(lean_object* v_x_369_, lean_object* v_x_370_){
_start:
{
uint8_t v_res_371_; lean_object* v_r_372_; 
v_res_371_ = l_Std_Http_URI_instBEqUserInfo_beq(v_x_369_, v_x_370_);
lean_dec_ref(v_x_370_);
lean_dec_ref(v_x_369_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings(lean_object* v_username_375_, lean_object* v_password_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_375_);
if (lean_obj_tag(v_password_376_) == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_box(0);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
return v___x_379_;
}
else
{
lean_object* v_val_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_389_; 
v_val_380_ = lean_ctor_get(v_password_376_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v_password_376_);
if (v_isSharedCheck_389_ == 0)
{
v___x_382_ = v_password_376_;
v_isShared_383_ = v_isSharedCheck_389_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_val_380_);
lean_dec(v_password_376_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_389_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_384_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_380_);
lean_dec(v_val_380_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_384_);
v___x_386_ = v___x_382_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_388_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; 
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_377_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
return v___x_387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings___boxed(lean_object* v_username_390_, lean_object* v_password_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_Http_URI_UserInfo_ofStrings(v_username_390_, v_password_391_);
lean_dec_ref(v_username_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f(lean_object* v_ui_393_){
_start:
{
lean_object* v_username_394_; lean_object* v___x_395_; 
v_username_394_ = lean_ctor_get(v_ui_393_, 0);
v___x_395_ = l_Std_Http_URI_EncodedUserInfo_decode(v_username_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f___boxed(lean_object* v_ui_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_Http_URI_UserInfo_username_x3f(v_ui_396_);
lean_dec_ref(v_ui_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f(lean_object* v_ui_398_){
_start:
{
lean_object* v_password_399_; 
v_password_399_ = lean_ctor_get(v_ui_398_, 1);
if (lean_obj_tag(v_password_399_) == 0)
{
lean_object* v___x_400_; 
v___x_400_ = lean_box(0);
return v___x_400_;
}
else
{
lean_object* v_val_401_; lean_object* v___x_402_; 
v_val_401_ = lean_ctor_get(v_password_399_, 0);
v___x_402_ = l_Std_Http_URI_EncodedUserInfo_decode(v_val_401_);
return v___x_402_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f___boxed(lean_object* v_ui_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Std_Http_URI_UserInfo_password_x3f(v_ui_403_);
lean_dec_ref(v_ui_403_);
return v_res_404_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(lean_object* v___x_405_, lean_object* v_x_406_){
_start:
{
if (lean_obj_tag(v_x_406_) == 0)
{
uint8_t v___x_407_; 
v___x_407_ = 1;
return v___x_407_;
}
else
{
lean_object* v_head_408_; lean_object* v_tail_409_; lean_object* v___x_410_; uint8_t v___x_411_; uint8_t v___y_415_; uint32_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; uint8_t v___y_431_; 
v_head_408_ = lean_ctor_get(v_x_406_, 0);
v_tail_409_ = lean_ctor_get(v_x_406_, 1);
v___x_410_ = lean_unsigned_to_nat(63u);
v___x_411_ = lean_nat_dec_le(v___x_405_, v___x_410_);
v___x_426_ = lean_unbox_uint32(v_head_408_);
v___x_427_ = lean_uint32_to_nat(v___x_426_);
v___x_428_ = lean_unsigned_to_nat(128u);
v___x_429_ = lean_nat_dec_lt(v___x_427_, v___x_428_);
lean_dec(v___x_427_);
if (v___x_429_ == 0)
{
v___y_415_ = v___x_429_;
goto v___jp_414_;
}
else
{
uint32_t v___x_438_; uint32_t v___x_439_; uint8_t v___x_440_; 
v___x_438_ = 48;
v___x_439_ = lean_unbox_uint32(v_head_408_);
v___x_440_ = lean_uint32_dec_le(v___x_438_, v___x_439_);
if (v___x_440_ == 0)
{
v___y_431_ = v___x_440_;
goto v___jp_430_;
}
else
{
uint32_t v___x_441_; uint32_t v___x_442_; uint8_t v___x_443_; 
v___x_441_ = 57;
v___x_442_ = lean_unbox_uint32(v_head_408_);
v___x_443_ = lean_uint32_dec_le(v___x_442_, v___x_441_);
v___y_431_ = v___x_443_;
goto v___jp_430_;
}
}
v___jp_412_:
{
if (v___x_411_ == 0)
{
return v___x_411_;
}
else
{
v_x_406_ = v_tail_409_;
goto _start;
}
}
v___jp_414_:
{
if (v___y_415_ == 0)
{
uint32_t v___x_416_; uint32_t v___x_417_; uint8_t v___x_418_; 
v___x_416_ = 45;
v___x_417_ = lean_unbox_uint32(v_head_408_);
v___x_418_ = lean_uint32_dec_eq(v___x_417_, v___x_416_);
if (v___x_418_ == 0)
{
return v___y_415_;
}
else
{
goto v___jp_412_;
}
}
else
{
goto v___jp_412_;
}
}
v___jp_419_:
{
uint32_t v___x_420_; uint32_t v___x_421_; uint8_t v___x_422_; 
v___x_420_ = 97;
v___x_421_ = lean_unbox_uint32(v_head_408_);
v___x_422_ = lean_uint32_dec_le(v___x_420_, v___x_421_);
if (v___x_422_ == 0)
{
v___y_415_ = v___x_422_;
goto v___jp_414_;
}
else
{
uint32_t v___x_423_; uint32_t v___x_424_; uint8_t v___x_425_; 
v___x_423_ = 122;
v___x_424_ = lean_unbox_uint32(v_head_408_);
v___x_425_ = lean_uint32_dec_le(v___x_424_, v___x_423_);
v___y_415_ = v___x_425_;
goto v___jp_414_;
}
}
v___jp_430_:
{
if (v___y_431_ == 0)
{
uint32_t v___x_432_; uint32_t v___x_433_; uint8_t v___x_434_; 
v___x_432_ = 65;
v___x_433_ = lean_unbox_uint32(v_head_408_);
v___x_434_ = lean_uint32_dec_le(v___x_432_, v___x_433_);
if (v___x_434_ == 0)
{
goto v___jp_419_;
}
else
{
uint32_t v___x_435_; uint32_t v___x_436_; uint8_t v___x_437_; 
v___x_435_ = 90;
v___x_436_ = lean_unbox_uint32(v_head_408_);
v___x_437_ = lean_uint32_dec_le(v___x_436_, v___x_435_);
if (v___x_437_ == 0)
{
goto v___jp_419_;
}
else
{
v___y_415_ = v___x_429_;
goto v___jp_414_;
}
}
}
else
{
goto v___jp_412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0___boxed(lean_object* v___x_444_, lean_object* v_x_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v___x_444_, v_x_445_);
lean_dec(v_x_445_);
lean_dec(v___x_444_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object* v_s_448_){
_start:
{
uint32_t v___y_450_; uint32_t v___y_456_; uint8_t v___y_457_; uint8_t v___y_458_; lean_object* v_chars_463_; uint8_t v___y_481_; uint32_t v___y_483_; uint32_t v___y_489_; uint8_t v___y_490_; uint8_t v___y_491_; uint8_t v___y_497_; lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_chars_463_ = lean_string_data(v_s_448_);
v___x_513_ = l_List_lengthTR___redArg(v_chars_463_);
v___x_514_ = lean_unsigned_to_nat(63u);
v___x_515_ = lean_nat_dec_le(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_dec(v___x_513_);
v___y_497_ = v___x_515_;
goto v___jp_496_;
}
else
{
uint8_t v___x_516_; 
v___x_516_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v___x_513_, v_chars_463_);
lean_dec(v___x_513_);
v___y_497_ = v___x_516_;
goto v___jp_496_;
}
v___jp_449_:
{
uint32_t v___x_451_; uint8_t v___x_452_; 
v___x_451_ = 97;
v___x_452_ = lean_uint32_dec_le(v___x_451_, v___y_450_);
if (v___x_452_ == 0)
{
return v___x_452_;
}
else
{
uint32_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = 122;
v___x_454_ = lean_uint32_dec_le(v___y_450_, v___x_453_);
return v___x_454_;
}
}
v___jp_455_:
{
if (v___y_458_ == 0)
{
uint32_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = 65;
v___x_460_ = lean_uint32_dec_le(v___x_459_, v___y_456_);
if (v___x_460_ == 0)
{
v___y_450_ = v___y_456_;
goto v___jp_449_;
}
else
{
uint32_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = 90;
v___x_462_ = lean_uint32_dec_le(v___y_456_, v___x_461_);
if (v___x_462_ == 0)
{
v___y_450_ = v___y_456_;
goto v___jp_449_;
}
else
{
return v___y_457_;
}
}
}
else
{
return v___y_458_;
}
}
v___jp_464_:
{
lean_object* v___x_465_; 
v___x_465_ = l_List_getLast_x3f___redArg(v_chars_463_);
lean_dec(v_chars_463_);
if (lean_obj_tag(v___x_465_) == 0)
{
uint8_t v___x_466_; 
v___x_466_ = 0;
return v___x_466_;
}
else
{
lean_object* v_val_467_; uint32_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v_val_467_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v___x_465_, 1);
v___x_468_ = lean_unbox_uint32(v_val_467_);
v___x_469_ = lean_uint32_to_nat(v___x_468_);
v___x_470_ = lean_unsigned_to_nat(128u);
v___x_471_ = lean_nat_dec_lt(v___x_469_, v___x_470_);
lean_dec(v___x_469_);
if (v___x_471_ == 0)
{
lean_dec(v_val_467_);
return v___x_471_;
}
else
{
uint32_t v___x_472_; uint32_t v___x_473_; uint8_t v___x_474_; 
v___x_472_ = 48;
v___x_473_ = lean_unbox_uint32(v_val_467_);
v___x_474_ = lean_uint32_dec_le(v___x_472_, v___x_473_);
if (v___x_474_ == 0)
{
uint32_t v___x_475_; 
v___x_475_ = lean_unbox_uint32(v_val_467_);
lean_dec(v_val_467_);
v___y_456_ = v___x_475_;
v___y_457_ = v___x_471_;
v___y_458_ = v___x_474_;
goto v___jp_455_;
}
else
{
uint32_t v___x_476_; uint32_t v___x_477_; uint8_t v___x_478_; uint32_t v___x_479_; 
v___x_476_ = 57;
v___x_477_ = lean_unbox_uint32(v_val_467_);
v___x_478_ = lean_uint32_dec_le(v___x_477_, v___x_476_);
v___x_479_ = lean_unbox_uint32(v_val_467_);
lean_dec(v_val_467_);
v___y_456_ = v___x_479_;
v___y_457_ = v___x_471_;
v___y_458_ = v___x_478_;
goto v___jp_455_;
}
}
}
}
v___jp_480_:
{
if (v___y_481_ == 0)
{
lean_dec(v_chars_463_);
return v___y_481_;
}
else
{
goto v___jp_464_;
}
}
v___jp_482_:
{
uint32_t v___x_484_; uint8_t v___x_485_; 
v___x_484_ = 97;
v___x_485_ = lean_uint32_dec_le(v___x_484_, v___y_483_);
if (v___x_485_ == 0)
{
v___y_481_ = v___x_485_;
goto v___jp_480_;
}
else
{
uint32_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = 122;
v___x_487_ = lean_uint32_dec_le(v___y_483_, v___x_486_);
v___y_481_ = v___x_487_;
goto v___jp_480_;
}
}
v___jp_488_:
{
if (v___y_491_ == 0)
{
uint32_t v___x_492_; uint8_t v___x_493_; 
v___x_492_ = 65;
v___x_493_ = lean_uint32_dec_le(v___x_492_, v___y_489_);
if (v___x_493_ == 0)
{
v___y_483_ = v___y_489_;
goto v___jp_482_;
}
else
{
uint32_t v___x_494_; uint8_t v___x_495_; 
v___x_494_ = 90;
v___x_495_ = lean_uint32_dec_le(v___y_489_, v___x_494_);
if (v___x_495_ == 0)
{
v___y_483_ = v___y_489_;
goto v___jp_482_;
}
else
{
v___y_481_ = v___y_490_;
goto v___jp_480_;
}
}
}
else
{
goto v___jp_464_;
}
}
v___jp_496_:
{
if (v___y_497_ == 0)
{
lean_dec(v_chars_463_);
return v___y_497_;
}
else
{
lean_object* v___x_498_; 
v___x_498_ = l_List_head_x3f___redArg(v_chars_463_);
if (lean_obj_tag(v___x_498_) == 0)
{
uint8_t v___x_499_; 
lean_dec(v_chars_463_);
v___x_499_ = 0;
return v___x_499_;
}
else
{
lean_object* v_val_500_; uint32_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v_val_500_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_val_500_);
lean_dec_ref_known(v___x_498_, 1);
v___x_501_ = lean_unbox_uint32(v_val_500_);
v___x_502_ = lean_uint32_to_nat(v___x_501_);
v___x_503_ = lean_unsigned_to_nat(128u);
v___x_504_ = lean_nat_dec_lt(v___x_502_, v___x_503_);
lean_dec(v___x_502_);
if (v___x_504_ == 0)
{
lean_dec(v_val_500_);
v___y_481_ = v___x_504_;
goto v___jp_480_;
}
else
{
uint32_t v___x_505_; uint32_t v___x_506_; uint8_t v___x_507_; 
v___x_505_ = 48;
v___x_506_ = lean_unbox_uint32(v_val_500_);
v___x_507_ = lean_uint32_dec_le(v___x_505_, v___x_506_);
if (v___x_507_ == 0)
{
uint32_t v___x_508_; 
v___x_508_ = lean_unbox_uint32(v_val_500_);
lean_dec(v_val_500_);
v___y_489_ = v___x_508_;
v___y_490_ = v___x_504_;
v___y_491_ = v___x_507_;
goto v___jp_488_;
}
else
{
uint32_t v___x_509_; uint32_t v___x_510_; uint8_t v___x_511_; uint32_t v___x_512_; 
v___x_509_ = 57;
v___x_510_ = lean_unbox_uint32(v_val_500_);
v___x_511_ = lean_uint32_dec_le(v___x_510_, v___x_509_);
v___x_512_ = lean_unbox_uint32(v_val_500_);
lean_dec(v_val_500_);
v___y_489_ = v___x_512_;
v___y_490_ = v___x_504_;
v___y_491_ = v___x_511_;
goto v___jp_488_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidDomainLabel___boxed(lean_object* v_s_517_){
_start:
{
uint8_t v_res_518_; lean_object* v_r_519_; 
v_res_518_ = l_Std_Http_URI_isValidDomainLabel(v_s_517_);
v_r_519_ = lean_box(v_res_518_);
return v_r_519_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(lean_object* v_s_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0));
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___boxed(lean_object* v_s_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(v_s_524_);
lean_dec_ref(v_s_524_);
return v_res_525_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(lean_object* v___x_526_, lean_object* v_lower_527_, lean_object* v___x_528_, lean_object* v_a_529_, uint8_t v_b_530_){
_start:
{
if (lean_obj_tag(v_a_529_) == 0)
{
lean_object* v_currPos_531_; lean_object* v_searcher_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_550_; 
v_currPos_531_ = lean_ctor_get(v_a_529_, 0);
v_searcher_532_ = lean_ctor_get(v_a_529_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v_a_529_);
if (v_isSharedCheck_550_ == 0)
{
v___x_534_ = v_a_529_;
v_isShared_535_ = v_isSharedCheck_550_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_searcher_532_);
lean_inc(v_currPos_531_);
lean_dec(v_a_529_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_550_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v_startInclusive_536_; lean_object* v_endExclusive_537_; lean_object* v___x_538_; uint8_t v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_startInclusive_536_ = lean_ctor_get(v___x_528_, 1);
v_endExclusive_537_ = lean_ctor_get(v___x_528_, 2);
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_nat_dec_eq(v___x_526_, v___x_538_);
v___x_540_ = lean_nat_sub(v_endExclusive_537_, v_startInclusive_536_);
v___x_541_ = lean_nat_dec_eq(v_searcher_532_, v___x_540_);
lean_dec(v___x_540_);
if (v___x_541_ == 0)
{
uint32_t v___x_542_; uint32_t v___x_543_; uint8_t v___x_544_; 
v___x_542_ = 46;
v___x_543_ = lean_string_utf8_get_fast(v_lower_527_, v_searcher_532_);
v___x_544_ = lean_uint32_dec_eq(v___x_543_, v___x_542_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = lean_string_utf8_next_fast(v_lower_527_, v_searcher_532_);
lean_dec(v_searcher_532_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v___x_545_);
v___x_547_ = v___x_534_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_currPos_531_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v___x_545_);
v___x_547_ = v_reuseFailAlloc_549_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
v_a_529_ = v___x_547_;
goto _start;
}
}
else
{
lean_del_object(v___x_534_);
lean_dec(v_searcher_532_);
lean_dec(v_currPos_531_);
return v___x_539_;
}
}
else
{
lean_del_object(v___x_534_);
lean_dec(v_searcher_532_);
lean_dec(v_currPos_531_);
return v___x_539_;
}
}
}
else
{
return v_b_530_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg___boxed(lean_object* v___x_551_, lean_object* v_lower_552_, lean_object* v___x_553_, lean_object* v_a_554_, lean_object* v_b_555_){
_start:
{
uint8_t v_b_boxed_556_; uint8_t v_res_557_; lean_object* v_r_558_; 
v_b_boxed_556_ = lean_unbox(v_b_555_);
v_res_557_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_551_, v_lower_552_, v___x_553_, v_a_554_, v_b_boxed_556_);
lean_dec_ref(v___x_553_);
lean_dec_ref(v_lower_552_);
lean_dec(v___x_551_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(lean_object* v_lower_559_, lean_object* v___x_560_, lean_object* v___x_561_, lean_object* v_a_562_, uint8_t v_b_563_){
_start:
{
if (lean_obj_tag(v_a_562_) == 0)
{
lean_object* v_currPos_564_; lean_object* v_searcher_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_599_; 
v_currPos_564_ = lean_ctor_get(v_a_562_, 0);
v_searcher_565_ = lean_ctor_get(v_a_562_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v_a_562_);
if (v_isSharedCheck_599_ == 0)
{
v___x_567_ = v_a_562_;
v_isShared_568_ = v_isSharedCheck_599_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_searcher_565_);
lean_inc(v_currPos_564_);
lean_dec(v_a_562_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_599_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v_startInclusive_569_; lean_object* v_endExclusive_570_; uint8_t v___x_571_; lean_object* v_it_573_; lean_object* v_startInclusive_574_; lean_object* v_endExclusive_575_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_startInclusive_569_ = lean_ctor_get(v___x_560_, 1);
v_endExclusive_570_ = lean_ctor_get(v___x_560_, 2);
v___x_571_ = 1;
v___x_579_ = lean_nat_sub(v_endExclusive_570_, v_startInclusive_569_);
v___x_580_ = lean_nat_dec_eq(v_searcher_565_, v___x_579_);
lean_dec(v___x_579_);
if (v___x_580_ == 0)
{
uint32_t v___x_581_; uint32_t v___x_582_; uint8_t v___x_583_; 
v___x_581_ = 46;
v___x_582_ = lean_string_utf8_get_fast(v_lower_559_, v_searcher_565_);
v___x_583_ = lean_uint32_dec_eq(v___x_582_, v___x_581_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_584_ = lean_string_utf8_next_fast(v_lower_559_, v_searcher_565_);
lean_dec(v_searcher_565_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v___x_584_);
v___x_586_ = v___x_567_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_currPos_564_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_584_);
v___x_586_ = v_reuseFailAlloc_588_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
v_a_562_ = v___x_586_;
goto _start;
}
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v_slice_592_; lean_object* v_nextIt_594_; 
v___x_589_ = lean_string_utf8_next_fast(v_lower_559_, v_searcher_565_);
v___x_590_ = lean_nat_sub(v___x_589_, v_searcher_565_);
v___x_591_ = lean_nat_add(v_searcher_565_, v___x_590_);
lean_dec(v___x_590_);
v_slice_592_ = l_String_Slice_subslice_x21(v___x_560_, v_currPos_564_, v_searcher_565_);
lean_inc(v___x_591_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v___x_591_);
lean_ctor_set(v___x_567_, 0, v___x_591_);
v_nextIt_594_ = v___x_567_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_591_);
v_nextIt_594_ = v_reuseFailAlloc_597_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v_startInclusive_595_; lean_object* v_endExclusive_596_; 
v_startInclusive_595_ = lean_ctor_get(v_slice_592_, 0);
lean_inc(v_startInclusive_595_);
v_endExclusive_596_ = lean_ctor_get(v_slice_592_, 1);
lean_inc(v_endExclusive_596_);
lean_dec_ref(v_slice_592_);
v_it_573_ = v_nextIt_594_;
v_startInclusive_574_ = v_startInclusive_595_;
v_endExclusive_575_ = v_endExclusive_596_;
goto v___jp_572_;
}
}
}
else
{
lean_object* v___x_598_; 
lean_del_object(v___x_567_);
lean_dec(v_searcher_565_);
v___x_598_ = lean_box(1);
lean_inc(v___x_561_);
v_it_573_ = v___x_598_;
v_startInclusive_574_ = v_currPos_564_;
v_endExclusive_575_ = v___x_561_;
goto v___jp_572_;
}
v___jp_572_:
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = lean_string_utf8_extract_fast(v_lower_559_, v_startInclusive_574_, v_endExclusive_575_);
lean_dec(v_endExclusive_575_);
lean_dec(v_startInclusive_574_);
v___x_577_ = l_Std_Http_URI_isValidDomainLabel(v___x_576_);
if (v___x_577_ == 0)
{
lean_dec(v_it_573_);
lean_dec(v___x_561_);
return v___x_577_;
}
else
{
v_a_562_ = v_it_573_;
v_b_563_ = v___x_571_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_561_);
return v_b_563_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg___boxed(lean_object* v_lower_600_, lean_object* v___x_601_, lean_object* v___x_602_, lean_object* v_a_603_, lean_object* v_b_604_){
_start:
{
uint8_t v_b_boxed_605_; uint8_t v_res_606_; lean_object* v_r_607_; 
v_b_boxed_605_ = lean_unbox(v_b_604_);
v_res_606_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v_lower_600_, v___x_601_, v___x_602_, v_a_603_, v_b_boxed_605_);
lean_dec_ref(v___x_601_);
lean_dec_ref(v_lower_600_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_DomainName_ofString_x3f(lean_object* v_s_608_){
_start:
{
lean_object* v___x_609_; lean_object* v_lower_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_609_ = lean_unsigned_to_nat(0u);
v_lower_610_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_608_, v___x_609_);
v___x_611_ = lean_string_utf8_byte_size(v_lower_610_);
v___x_612_ = lean_nat_dec_eq(v___x_611_, v___x_609_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; uint8_t v___x_616_; 
lean_inc_ref(v_lower_610_);
v___x_613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_613_, 0, v_lower_610_);
lean_ctor_set(v___x_613_, 1, v___x_609_);
lean_ctor_set(v___x_613_, 2, v___x_611_);
v___x_614_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(v___x_613_);
v___x_615_ = 1;
lean_inc(v___x_614_);
v___x_616_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_611_, v_lower_610_, v___x_613_, v___x_614_, v___x_615_);
if (v___x_616_ == 0)
{
uint8_t v___x_617_; 
v___x_617_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v_lower_610_, v___x_613_, v___x_611_, v___x_614_, v___x_615_);
lean_dec_ref_known(v___x_613_, 3);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
lean_dec_ref(v_lower_610_);
v___x_618_ = lean_box(0);
return v___x_618_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_619_ = lean_string_length(v_lower_610_);
v___x_620_ = lean_unsigned_to_nat(255u);
v___x_621_ = lean_nat_dec_le(v___x_619_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
lean_dec_ref(v_lower_610_);
v___x_622_ = lean_box(0);
return v___x_622_;
}
else
{
lean_object* v___x_623_; 
v___x_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_623_, 0, v_lower_610_);
return v___x_623_;
}
}
}
else
{
lean_object* v___x_624_; 
lean_dec(v___x_614_);
lean_dec_ref_known(v___x_613_, 3);
lean_dec_ref(v_lower_610_);
v___x_624_ = lean_box(0);
return v___x_624_;
}
}
else
{
lean_object* v___x_625_; 
lean_dec_ref(v_lower_610_);
v___x_625_ = lean_box(0);
return v___x_625_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(lean_object* v_lower_626_, lean_object* v___x_627_, lean_object* v___x_628_, lean_object* v_inst_629_, lean_object* v_R_630_, lean_object* v_a_631_, uint8_t v_b_632_, lean_object* v_c_633_){
_start:
{
uint8_t v___x_634_; 
v___x_634_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v_lower_626_, v___x_627_, v___x_628_, v_a_631_, v_b_632_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___boxed(lean_object* v_lower_635_, lean_object* v___x_636_, lean_object* v___x_637_, lean_object* v_inst_638_, lean_object* v_R_639_, lean_object* v_a_640_, lean_object* v_b_641_, lean_object* v_c_642_){
_start:
{
uint8_t v_b_boxed_643_; uint8_t v_res_644_; lean_object* v_r_645_; 
v_b_boxed_643_ = lean_unbox(v_b_641_);
v_res_644_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(v_lower_635_, v___x_636_, v___x_637_, v_inst_638_, v_R_639_, v_a_640_, v_b_boxed_643_, v_c_642_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v_lower_635_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(lean_object* v___x_646_, lean_object* v_lower_647_, lean_object* v___x_648_, lean_object* v___x_649_, lean_object* v_inst_650_, lean_object* v_R_651_, lean_object* v_a_652_, uint8_t v_b_653_, lean_object* v_c_654_){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v___x_646_, v_lower_647_, v___x_648_, v_a_652_, v_b_653_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___boxed(lean_object* v___x_656_, lean_object* v_lower_657_, lean_object* v___x_658_, lean_object* v___x_659_, lean_object* v_inst_660_, lean_object* v_R_661_, lean_object* v_a_662_, lean_object* v_b_663_, lean_object* v_c_664_){
_start:
{
uint8_t v_b_boxed_665_; uint8_t v_res_666_; lean_object* v_r_667_; 
v_b_boxed_665_ = lean_unbox(v_b_663_);
v_res_666_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(v___x_656_, v_lower_657_, v___x_658_, v___x_659_, v_inst_660_, v_R_661_, v_a_662_, v_b_boxed_665_, v_c_664_);
lean_dec(v___x_659_);
lean_dec_ref(v___x_658_);
lean_dec_ref(v_lower_657_);
lean_dec(v___x_656_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx(lean_object* v_x_668_){
_start:
{
switch(lean_obj_tag(v_x_668_))
{
case 0:
{
lean_object* v___x_669_; 
v___x_669_ = lean_unsigned_to_nat(0u);
return v___x_669_;
}
case 1:
{
lean_object* v___x_670_; 
v___x_670_ = lean_unsigned_to_nat(1u);
return v___x_670_;
}
default: 
{
lean_object* v___x_671_; 
v___x_671_ = lean_unsigned_to_nat(2u);
return v___x_671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx___boxed(lean_object* v_x_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_Http_URI_Host_ctorIdx(v_x_672_);
lean_dec_ref(v_x_672_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___redArg(lean_object* v_t_674_, lean_object* v_k_675_){
_start:
{
lean_object* v_name_676_; lean_object* v___x_677_; 
v_name_676_ = lean_ctor_get(v_t_674_, 0);
lean_inc_ref(v_name_676_);
lean_dec_ref(v_t_674_);
v___x_677_ = lean_apply_1(v_k_675_, v_name_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim(lean_object* v_motive_678_, lean_object* v_ctorIdx_679_, lean_object* v_t_680_, lean_object* v_h_681_, lean_object* v_k_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_680_, v_k_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___boxed(lean_object* v_motive_684_, lean_object* v_ctorIdx_685_, lean_object* v_t_686_, lean_object* v_h_687_, lean_object* v_k_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Std_Http_URI_Host_ctorElim(v_motive_684_, v_ctorIdx_685_, v_t_686_, v_h_687_, v_k_688_);
lean_dec(v_ctorIdx_685_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim___redArg(lean_object* v_t_690_, lean_object* v_name_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_690_, v_name_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim(lean_object* v_motive_693_, lean_object* v_t_694_, lean_object* v_h_695_, lean_object* v_name_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_694_, v_name_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim___redArg(lean_object* v_t_698_, lean_object* v_ipv4_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_698_, v_ipv4_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim(lean_object* v_motive_701_, lean_object* v_t_702_, lean_object* v_h_703_, lean_object* v_ipv4_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_702_, v_ipv4_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim___redArg(lean_object* v_t_706_, lean_object* v_ipv6_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_706_, v_ipv6_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim(lean_object* v_motive_709_, lean_object* v_t_710_, lean_object* v_h_711_, lean_object* v_ipv6_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_710_, v_ipv6_712_);
return v___x_713_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default___closed__0(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default(void){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = lean_obj_once(&l_Std_Http_URI_instInhabitedHost_default___closed__0, &l_Std_Http_URI_instInhabitedHost_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedHost_default___closed__0);
return v___x_716_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost(void){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Std_Http_URI_instInhabitedHost_default;
return v___x_717_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqHost_beq(lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
switch(lean_obj_tag(v_x_718_))
{
case 0:
{
if (lean_obj_tag(v_x_719_) == 0)
{
lean_object* v_name_720_; lean_object* v_name_721_; uint8_t v___x_722_; 
v_name_720_ = lean_ctor_get(v_x_718_, 0);
v_name_721_ = lean_ctor_get(v_x_719_, 0);
v___x_722_ = lean_string_dec_eq(v_name_720_, v_name_721_);
return v___x_722_;
}
else
{
uint8_t v___x_723_; 
v___x_723_ = 0;
return v___x_723_;
}
}
case 1:
{
if (lean_obj_tag(v_x_719_) == 1)
{
lean_object* v_ipv4_724_; lean_object* v_ipv4_725_; uint8_t v___x_726_; 
v_ipv4_724_ = lean_ctor_get(v_x_718_, 0);
v_ipv4_725_ = lean_ctor_get(v_x_719_, 0);
v___x_726_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_ipv4_724_, v_ipv4_725_);
return v___x_726_;
}
else
{
uint8_t v___x_727_; 
v___x_727_ = 0;
return v___x_727_;
}
}
default: 
{
if (lean_obj_tag(v_x_719_) == 2)
{
lean_object* v_ipv6_728_; lean_object* v_ipv6_729_; uint8_t v___x_730_; 
v_ipv6_728_ = lean_ctor_get(v_x_718_, 0);
v_ipv6_729_ = lean_ctor_get(v_x_719_, 0);
v___x_730_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_ipv6_728_, v_ipv6_729_);
return v___x_730_;
}
else
{
uint8_t v___x_731_; 
v___x_731_ = 0;
return v___x_731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqHost_beq___boxed(lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
uint8_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l_Std_Http_URI_instBEqHost_beq(v_x_732_, v_x_733_);
lean_dec_ref(v_x_733_);
lean_dec_ref(v_x_732_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__4(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_unsigned_to_nat(2u);
v___x_743_ = lean_nat_to_int(v___x_742_);
return v___x_743_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__5(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = lean_nat_to_int(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0(lean_object* v_x_746_, lean_object* v_prec_747_){
_start:
{
lean_object* v___y_749_; lean_object* v_ctr_750_; lean_object* v_a_751_; lean_object* v___y_763_; lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = lean_unsigned_to_nat(1024u);
v___x_795_ = lean_nat_dec_le(v___x_794_, v_prec_747_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
v___x_796_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_763_ = v___x_796_;
goto v___jp_762_;
}
else
{
lean_object* v___x_797_; 
v___x_797_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_763_ = v___x_797_;
goto v___jp_762_;
}
v___jp_748_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_752_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_753_ = lean_string_append(v___x_752_, v_ctr_750_);
v___x_754_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
v___x_755_ = lean_box(1);
v___x_756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
lean_ctor_set(v___x_757_, 1, v_a_751_);
lean_inc(v___y_749_);
v___x_758_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_758_, 0, v___y_749_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = 0;
v___x_760_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set_uint8(v___x_760_, sizeof(void*)*1, v___x_759_);
v___x_761_ = l_Repr_addAppParen(v___x_760_, v_prec_747_);
return v___x_761_;
}
v___jp_762_:
{
switch(lean_obj_tag(v_x_746_))
{
case 0:
{
lean_object* v_name_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_773_; 
v_name_764_ = lean_ctor_get(v_x_746_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v_x_746_);
if (v_isSharedCheck_773_ == 0)
{
v___x_766_ = v_x_746_;
v_isShared_767_ = v_isSharedCheck_773_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_name_764_);
lean_dec(v_x_746_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_773_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_768_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_769_ = l_String_quote(v_name_764_);
if (v_isShared_767_ == 0)
{
lean_ctor_set_tag(v___x_766_, 3);
lean_ctor_set(v___x_766_, 0, v___x_769_);
v___x_771_ = v___x_766_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
v___y_749_ = v___y_763_;
v_ctr_750_ = v___x_768_;
v_a_751_ = v___x_771_;
goto v___jp_748_;
}
}
}
case 1:
{
lean_object* v_ipv4_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_783_; 
v_ipv4_774_ = lean_ctor_get(v_x_746_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v_x_746_);
if (v_isSharedCheck_783_ == 0)
{
v___x_776_ = v_x_746_;
v_isShared_777_ = v_isSharedCheck_783_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_ipv4_774_);
lean_dec(v_x_746_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_783_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_778_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_779_ = lean_uv_ntop_v4(v_ipv4_774_);
lean_dec_ref(v_ipv4_774_);
if (v_isShared_777_ == 0)
{
lean_ctor_set_tag(v___x_776_, 3);
lean_ctor_set(v___x_776_, 0, v___x_779_);
v___x_781_ = v___x_776_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
v___y_749_ = v___y_763_;
v_ctr_750_ = v___x_778_;
v_a_751_ = v___x_781_;
goto v___jp_748_;
}
}
}
default: 
{
lean_object* v_ipv6_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_793_; 
v_ipv6_784_ = lean_ctor_get(v_x_746_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v_x_746_);
if (v_isSharedCheck_793_ == 0)
{
v___x_786_ = v_x_746_;
v_isShared_787_ = v_isSharedCheck_793_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_ipv6_784_);
lean_dec(v_x_746_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_793_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_788_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_789_ = lean_uv_ntop_v6(v_ipv6_784_);
lean_dec_ref(v_ipv6_784_);
if (v_isShared_787_ == 0)
{
lean_ctor_set_tag(v___x_786_, 3);
lean_ctor_set(v___x_786_, 0, v___x_789_);
v___x_791_ = v___x_786_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
v___y_749_ = v___y_763_;
v_ctr_750_ = v___x_788_;
v_a_751_ = v___x_791_;
goto v___jp_748_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0___boxed(lean_object* v_x_798_, lean_object* v_prec_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Std_Http_URI_instReprHost___lam__0(v_x_798_, v_prec_799_);
lean_dec(v_prec_799_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0(lean_object* v_x_805_){
_start:
{
switch(lean_obj_tag(v_x_805_))
{
case 0:
{
lean_object* v_name_806_; 
v_name_806_ = lean_ctor_get(v_x_805_, 0);
lean_inc_ref(v_name_806_);
return v_name_806_;
}
case 1:
{
lean_object* v_ipv4_807_; lean_object* v___x_808_; 
v_ipv4_807_ = lean_ctor_get(v_x_805_, 0);
v___x_808_ = lean_uv_ntop_v4(v_ipv4_807_);
return v___x_808_;
}
default: 
{
lean_object* v_ipv6_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v_ipv6_809_ = lean_ctor_get(v_x_805_, 0);
v___x_810_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_811_ = lean_uv_ntop_v6(v_ipv6_809_);
v___x_812_ = lean_string_append(v___x_810_, v___x_811_);
lean_dec_ref(v___x_811_);
v___x_813_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_814_ = lean_string_append(v___x_812_, v___x_813_);
return v___x_814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0___boxed(lean_object* v_x_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_Http_URI_instToStringHost___lam__0(v_x_815_);
lean_dec_ref(v_x_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx(lean_object* v_x_819_){
_start:
{
switch(lean_obj_tag(v_x_819_))
{
case 0:
{
lean_object* v___x_820_; 
v___x_820_ = lean_unsigned_to_nat(0u);
return v___x_820_;
}
case 1:
{
lean_object* v___x_821_; 
v___x_821_ = lean_unsigned_to_nat(1u);
return v___x_821_;
}
default: 
{
lean_object* v___x_822_; 
v___x_822_ = lean_unsigned_to_nat(2u);
return v___x_822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___boxed(lean_object* v_x_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_Http_URI_Port_ctorIdx(v_x_823_);
lean_dec(v_x_823_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg(lean_object* v_t_825_, lean_object* v_k_826_){
_start:
{
if (lean_obj_tag(v_t_825_) == 2)
{
uint16_t v_port_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_port_827_ = lean_ctor_get_uint16(v_t_825_, 0);
v___x_828_ = lean_box(v_port_827_);
v___x_829_ = lean_apply_1(v_k_826_, v___x_828_);
return v___x_829_;
}
else
{
return v_k_826_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg___boxed(lean_object* v_t_830_, lean_object* v_k_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_830_, v_k_831_);
lean_dec(v_t_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim(lean_object* v_motive_833_, lean_object* v_ctorIdx_834_, lean_object* v_t_835_, lean_object* v_h_836_, lean_object* v_k_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_835_, v_k_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___boxed(lean_object* v_motive_839_, lean_object* v_ctorIdx_840_, lean_object* v_t_841_, lean_object* v_h_842_, lean_object* v_k_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_Http_URI_Port_ctorElim(v_motive_839_, v_ctorIdx_840_, v_t_841_, v_h_842_, v_k_843_);
lean_dec(v_t_841_);
lean_dec(v_ctorIdx_840_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg(lean_object* v_t_845_, lean_object* v_omitted_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_845_, v_omitted_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg___boxed(lean_object* v_t_848_, lean_object* v_omitted_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Std_Http_URI_Port_omitted_elim___redArg(v_t_848_, v_omitted_849_);
lean_dec(v_t_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim(lean_object* v_motive_851_, lean_object* v_t_852_, lean_object* v_h_853_, lean_object* v_omitted_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_852_, v_omitted_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___boxed(lean_object* v_motive_856_, lean_object* v_t_857_, lean_object* v_h_858_, lean_object* v_omitted_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Std_Http_URI_Port_omitted_elim(v_motive_856_, v_t_857_, v_h_858_, v_omitted_859_);
lean_dec(v_t_857_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg(lean_object* v_t_861_, lean_object* v_empty_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_861_, v_empty_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg___boxed(lean_object* v_t_864_, lean_object* v_empty_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Std_Http_URI_Port_empty_elim___redArg(v_t_864_, v_empty_865_);
lean_dec(v_t_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim(lean_object* v_motive_867_, lean_object* v_t_868_, lean_object* v_h_869_, lean_object* v_empty_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_868_, v_empty_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___boxed(lean_object* v_motive_872_, lean_object* v_t_873_, lean_object* v_h_874_, lean_object* v_empty_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Std_Http_URI_Port_empty_elim(v_motive_872_, v_t_873_, v_h_874_, v_empty_875_);
lean_dec(v_t_873_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg(lean_object* v_t_877_, lean_object* v_value_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_877_, v_value_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg___boxed(lean_object* v_t_880_, lean_object* v_value_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Std_Http_URI_Port_value_elim___redArg(v_t_880_, v_value_881_);
lean_dec(v_t_880_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim(lean_object* v_motive_883_, lean_object* v_t_884_, lean_object* v_h_885_, lean_object* v_value_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_884_, v_value_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___boxed(lean_object* v_motive_888_, lean_object* v_t_889_, lean_object* v_h_890_, lean_object* v_value_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_Http_URI_Port_value_elim(v_motive_888_, v_t_889_, v_h_890_, v_value_891_);
lean_dec(v_t_889_);
return v_res_892_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort_default(void){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = lean_box(0);
return v___x_893_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort(void){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = lean_box(0);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr(lean_object* v_x_907_, lean_object* v_prec_908_){
_start:
{
lean_object* v___y_910_; lean_object* v___y_917_; 
switch(lean_obj_tag(v_x_907_))
{
case 0:
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_unsigned_to_nat(1024u);
v___x_924_ = lean_nat_dec_le(v___x_923_, v_prec_908_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; 
v___x_925_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_917_ = v___x_925_;
goto v___jp_916_;
}
else
{
lean_object* v___x_926_; 
v___x_926_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_917_ = v___x_926_;
goto v___jp_916_;
}
}
case 1:
{
lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_927_ = lean_unsigned_to_nat(1024u);
v___x_928_ = lean_nat_dec_le(v___x_927_, v_prec_908_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
v___x_929_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_910_ = v___x_929_;
goto v___jp_909_;
}
else
{
lean_object* v___x_930_; 
v___x_930_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_910_ = v___x_930_;
goto v___jp_909_;
}
}
default: 
{
uint16_t v_port_931_; lean_object* v___y_933_; lean_object* v___x_943_; uint8_t v___x_944_; 
v_port_931_ = lean_ctor_get_uint16(v_x_907_, 0);
v___x_943_ = lean_unsigned_to_nat(1024u);
v___x_944_ = lean_nat_dec_le(v___x_943_, v_prec_908_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; 
v___x_945_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_933_ = v___x_945_;
goto v___jp_932_;
}
else
{
lean_object* v___x_946_; 
v___x_946_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_933_ = v___x_946_;
goto v___jp_932_;
}
v___jp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_934_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__6));
v___x_935_ = lean_uint16_to_nat(v_port_931_);
v___x_936_ = l_Nat_reprFast(v___x_935_);
v___x_937_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_934_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
lean_inc(v___y_933_);
v___x_939_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_939_, 0, v___y_933_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = 0;
v___x_941_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*1, v___x_940_);
v___x_942_ = l_Repr_addAppParen(v___x_941_, v_prec_908_);
return v___x_942_;
}
}
}
v___jp_909_:
{
lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_911_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__1));
lean_inc(v___y_910_);
v___x_912_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_912_, 0, v___y_910_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = 0;
v___x_914_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*1, v___x_913_);
v___x_915_ = l_Repr_addAppParen(v___x_914_, v_prec_908_);
return v___x_915_;
}
v___jp_916_:
{
lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_918_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__3));
lean_inc(v___y_917_);
v___x_919_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_919_, 0, v___y_917_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = 0;
v___x_921_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set_uint8(v___x_921_, sizeof(void*)*1, v___x_920_);
v___x_922_ = l_Repr_addAppParen(v___x_921_, v_prec_908_);
return v___x_922_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr___boxed(lean_object* v_x_947_, lean_object* v_prec_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_Http_URI_instReprPort_repr(v_x_947_, v_prec_948_);
lean_dec(v_prec_948_);
lean_dec(v_x_947_);
return v_res_949_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort_decEq(lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
switch(lean_obj_tag(v_x_952_))
{
case 0:
{
if (lean_obj_tag(v_x_953_) == 0)
{
uint8_t v___x_954_; 
v___x_954_ = 1;
return v___x_954_;
}
else
{
uint8_t v___x_955_; 
v___x_955_ = 0;
return v___x_955_;
}
}
case 1:
{
if (lean_obj_tag(v_x_953_) == 1)
{
uint8_t v___x_956_; 
v___x_956_ = 1;
return v___x_956_;
}
else
{
uint8_t v___x_957_; 
v___x_957_ = 0;
return v___x_957_;
}
}
default: 
{
uint16_t v_port_958_; uint8_t v___x_959_; 
v_port_958_ = lean_ctor_get_uint16(v_x_952_, 0);
v___x_959_ = 0;
if (lean_obj_tag(v_x_953_) == 2)
{
uint16_t v_port_960_; uint8_t v___x_961_; 
v_port_960_ = lean_ctor_get_uint16(v_x_953_, 0);
v___x_961_ = lean_uint16_dec_eq(v_port_958_, v_port_960_);
if (v___x_961_ == 0)
{
return v___x_959_;
}
else
{
return v___x_961_;
}
}
else
{
return v___x_959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort_decEq___boxed(lean_object* v_x_962_, lean_object* v_x_963_){
_start:
{
uint8_t v_res_964_; lean_object* v_r_965_; 
v_res_964_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_962_, v_x_963_);
lean_dec(v_x_963_);
lean_dec(v_x_962_);
v_r_965_ = lean_box(v_res_964_);
return v_r_965_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort(lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
uint8_t v___x_968_; 
v___x_968_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_966_, v_x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort___boxed(lean_object* v_x_969_, lean_object* v_x_970_){
_start:
{
uint8_t v_res_971_; lean_object* v_r_972_; 
v_res_971_ = l_Std_Http_URI_instDecidableEqPort(v_x_969_, v_x_970_);
lean_dec(v_x_970_);
lean_dec(v_x_969_);
v_r_972_ = lean_box(v_res_971_);
return v_r_972_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_973_ = lean_box(0);
v___x_974_ = l_Std_Http_URI_instInhabitedHost_default;
v___x_975_ = lean_box(0);
v___x_976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v___x_974_);
lean_ctor_set(v___x_976_, 2, v___x_973_);
return v___x_976_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default(void){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = lean_obj_once(&l_Std_Http_URI_instInhabitedAuthority_default___closed__0, &l_Std_Http_URI_instInhabitedAuthority_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0);
return v___x_977_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority(void){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Std_Http_URI_instInhabitedAuthority_default;
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(lean_object* v_x_979_, lean_object* v_x_980_){
_start:
{
if (lean_obj_tag(v_x_979_) == 0)
{
lean_object* v___x_981_; 
v___x_981_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_981_;
}
else
{
lean_object* v_val_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_val_982_ = lean_ctor_get(v_x_979_, 0);
lean_inc(v_val_982_);
lean_dec_ref_known(v_x_979_, 1);
v___x_983_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_984_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_val_982_);
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = l_Repr_addAppParen(v___x_985_, v_x_980_);
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0___boxed(lean_object* v_x_987_, lean_object* v_x_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_x_987_, v_x_988_);
lean_dec(v_x_988_);
return v_res_989_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_unsigned_to_nat(8u);
v___x_1003_ = lean_nat_to_int(v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg(lean_object* v_x_1007_){
_start:
{
lean_object* v_userInfo_1008_; lean_object* v_host_1009_; lean_object* v_port_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v_ctr_1030_; lean_object* v_a_1031_; 
v_userInfo_1008_ = lean_ctor_get(v_x_1007_, 0);
lean_inc(v_userInfo_1008_);
v_host_1009_ = lean_ctor_get(v_x_1007_, 1);
lean_inc_ref(v_host_1009_);
v_port_1010_ = lean_ctor_get(v_x_1007_, 2);
lean_inc(v_port_1010_);
lean_dec_ref(v_x_1007_);
v___x_1011_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1012_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3));
v___x_1013_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_1014_ = lean_unsigned_to_nat(0u);
v___x_1015_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_userInfo_1008_, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1013_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = 0;
v___x_1018_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set_uint8(v___x_1018_, sizeof(void*)*1, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1012_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_box(1);
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v___x_1011_);
v___x_1027_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_1028_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_1009_))
{
case 0:
{
lean_object* v_name_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1068_; 
v_name_1059_ = lean_ctor_get(v_host_1009_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_host_1009_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1061_ = v_host_1009_;
v_isShared_1062_ = v_isSharedCheck_1068_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_name_1059_);
lean_dec(v_host_1009_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1068_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1063_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_1064_ = l_String_quote(v_name_1059_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 3);
lean_ctor_set(v___x_1061_, 0, v___x_1064_);
v___x_1066_ = v___x_1061_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
v_ctr_1030_ = v___x_1063_;
v_a_1031_ = v___x_1066_;
goto v___jp_1029_;
}
}
}
case 1:
{
lean_object* v_ipv4_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1078_; 
v_ipv4_1069_ = lean_ctor_get(v_host_1009_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_host_1009_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1071_ = v_host_1009_;
v_isShared_1072_ = v_isSharedCheck_1078_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_ipv4_1069_);
lean_dec(v_host_1009_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1078_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1073_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_1074_ = lean_uv_ntop_v4(v_ipv4_1069_);
lean_dec_ref(v_ipv4_1069_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set_tag(v___x_1071_, 3);
lean_ctor_set(v___x_1071_, 0, v___x_1074_);
v___x_1076_ = v___x_1071_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
v_ctr_1030_ = v___x_1073_;
v_a_1031_ = v___x_1076_;
goto v___jp_1029_;
}
}
}
default: 
{
lean_object* v_ipv6_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1088_; 
v_ipv6_1079_ = lean_ctor_get(v_host_1009_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_host_1009_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1081_ = v_host_1009_;
v_isShared_1082_ = v_isSharedCheck_1088_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_ipv6_1079_);
lean_dec(v_host_1009_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1088_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1083_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_1084_ = lean_uv_ntop_v6(v_ipv6_1079_);
lean_dec_ref(v_ipv6_1079_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set_tag(v___x_1081_, 3);
lean_ctor_set(v___x_1081_, 0, v___x_1084_);
v___x_1086_ = v___x_1081_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
v_ctr_1030_ = v___x_1083_;
v_a_1031_ = v___x_1086_;
goto v___jp_1029_;
}
}
}
}
v___jp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1032_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_1033_ = lean_string_append(v___x_1032_, v_ctr_1030_);
v___x_1034_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_ctor_set(v___x_1035_, 1, v___x_1022_);
v___x_1036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set(v___x_1036_, 1, v_a_1031_);
v___x_1037_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1028_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*1, v___x_1017_);
v___x_1039_ = l_Repr_addAppParen(v___x_1038_, v___x_1014_);
v___x_1040_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1027_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set_uint8(v___x_1041_, sizeof(void*)*1, v___x_1017_);
v___x_1042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1026_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v___x_1020_);
v___x_1044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v___x_1022_);
v___x_1045_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_1046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___x_1011_);
v___x_1048_ = l_Std_Http_URI_instReprPort_repr(v_port_1010_, v___x_1014_);
lean_dec(v_port_1010_);
v___x_1049_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1027_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*1, v___x_1017_);
v___x_1051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1047_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1053_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___x_1051_);
v___x_1055_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1052_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set_uint8(v___x_1058_, sizeof(void*)*1, v___x_1017_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr(lean_object* v_x_1089_, lean_object* v_prec_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_x_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___boxed(lean_object* v_x_1092_, lean_object* v_prec_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Std_Http_URI_instReprAuthority_repr(v_x_1092_, v_prec_1093_);
lean_dec(v_prec_1093_);
return v_res_1094_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
if (lean_obj_tag(v_x_1097_) == 0)
{
if (lean_obj_tag(v_x_1098_) == 0)
{
uint8_t v___x_1099_; 
v___x_1099_ = 1;
return v___x_1099_;
}
else
{
uint8_t v___x_1100_; 
v___x_1100_ = 0;
return v___x_1100_;
}
}
else
{
if (lean_obj_tag(v_x_1098_) == 0)
{
uint8_t v___x_1101_; 
v___x_1101_ = 0;
return v___x_1101_;
}
else
{
lean_object* v_val_1102_; lean_object* v_val_1103_; uint8_t v___x_1104_; 
v_val_1102_ = lean_ctor_get(v_x_1097_, 0);
v_val_1103_ = lean_ctor_get(v_x_1098_, 0);
v___x_1104_ = l_Std_Http_URI_instBEqUserInfo_beq(v_val_1102_, v_val_1103_);
return v___x_1104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0___boxed(lean_object* v_x_1105_, lean_object* v_x_1106_){
_start:
{
uint8_t v_res_1107_; lean_object* v_r_1108_; 
v_res_1107_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_x_1105_, v_x_1106_);
lean_dec(v_x_1106_);
lean_dec(v_x_1105_);
v_r_1108_ = lean_box(v_res_1107_);
return v_r_1108_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqAuthority_beq(lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
lean_object* v_userInfo_1111_; lean_object* v_host_1112_; lean_object* v_port_1113_; lean_object* v_userInfo_1114_; lean_object* v_host_1115_; lean_object* v_port_1116_; uint8_t v___x_1117_; 
v_userInfo_1111_ = lean_ctor_get(v_x_1109_, 0);
v_host_1112_ = lean_ctor_get(v_x_1109_, 1);
v_port_1113_ = lean_ctor_get(v_x_1109_, 2);
v_userInfo_1114_ = lean_ctor_get(v_x_1110_, 0);
v_host_1115_ = lean_ctor_get(v_x_1110_, 1);
v_port_1116_ = lean_ctor_get(v_x_1110_, 2);
v___x_1117_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_userInfo_1111_, v_userInfo_1114_);
if (v___x_1117_ == 0)
{
return v___x_1117_;
}
else
{
uint8_t v___x_1118_; 
v___x_1118_ = l_Std_Http_URI_instBEqHost_beq(v_host_1112_, v_host_1115_);
if (v___x_1118_ == 0)
{
return v___x_1118_;
}
else
{
uint8_t v___x_1119_; 
v___x_1119_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1113_, v_port_1116_);
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqAuthority_beq___boxed(lean_object* v_x_1120_, lean_object* v_x_1121_){
_start:
{
uint8_t v_res_1122_; lean_object* v_r_1123_; 
v_res_1122_ = l_Std_Http_URI_instBEqAuthority_beq(v_x_1120_, v_x_1121_);
lean_dec_ref(v_x_1121_);
lean_dec_ref(v_x_1120_);
v_r_1123_ = lean_box(v_res_1122_);
return v_r_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringAuthority___lam__0(lean_object* v_auth_1129_){
_start:
{
lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v_userInfo_1136_; lean_object* v_host_1137_; lean_object* v_port_1138_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1150_; 
v_userInfo_1136_ = lean_ctor_get(v_auth_1129_, 0);
lean_inc(v_userInfo_1136_);
v_host_1137_ = lean_ctor_get(v_auth_1129_, 1);
lean_inc_ref(v_host_1137_);
v_port_1138_ = lean_ctor_get(v_auth_1129_, 2);
lean_inc(v_port_1138_);
lean_dec_ref(v_auth_1129_);
if (lean_obj_tag(v_userInfo_1136_) == 0)
{
lean_object* v___x_1160_; 
v___x_1160_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1150_ = v___x_1160_;
goto v___jp_1149_;
}
else
{
lean_object* v_val_1161_; lean_object* v_password_1162_; 
v_val_1161_ = lean_ctor_get(v_userInfo_1136_, 0);
lean_inc(v_val_1161_);
lean_dec_ref_known(v_userInfo_1136_, 1);
v_password_1162_ = lean_ctor_get(v_val_1161_, 1);
if (lean_obj_tag(v_password_1162_) == 0)
{
lean_object* v_username_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_username_1163_ = lean_ctor_get(v_val_1161_, 0);
lean_inc_ref(v_username_1163_);
lean_dec(v_val_1161_);
v___x_1164_ = lean_string_from_utf8_unchecked(v_username_1163_);
v___x_1165_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1166_ = lean_string_append(v___x_1164_, v___x_1165_);
v___y_1150_ = v___x_1166_;
goto v___jp_1149_;
}
else
{
lean_object* v_username_1167_; lean_object* v_val_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_inc_ref(v_password_1162_);
v_username_1167_ = lean_ctor_get(v_val_1161_, 0);
lean_inc_ref(v_username_1167_);
lean_dec(v_val_1161_);
v_val_1168_ = lean_ctor_get(v_password_1162_, 0);
lean_inc(v_val_1168_);
lean_dec_ref_known(v_password_1162_, 1);
v___x_1169_ = lean_string_from_utf8_unchecked(v_username_1167_);
v___x_1170_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1171_ = lean_string_append(v___x_1169_, v___x_1170_);
v___x_1172_ = lean_string_from_utf8_unchecked(v_val_1168_);
v___x_1173_ = lean_string_append(v___x_1171_, v___x_1172_);
lean_dec_ref(v___x_1172_);
v___x_1174_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1175_ = lean_string_append(v___x_1173_, v___x_1174_);
v___y_1150_ = v___x_1175_;
goto v___jp_1149_;
}
}
v___jp_1130_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_string_append(v___y_1131_, v___y_1132_);
lean_dec_ref(v___y_1132_);
v___x_1135_ = lean_string_append(v___x_1134_, v___y_1133_);
lean_dec_ref(v___y_1133_);
return v___x_1135_;
}
v___jp_1139_:
{
switch(lean_obj_tag(v_port_1138_))
{
case 0:
{
lean_object* v___x_1142_; 
v___x_1142_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1131_ = v___y_1140_;
v___y_1132_ = v___y_1141_;
v___y_1133_ = v___x_1142_;
goto v___jp_1130_;
}
case 1:
{
lean_object* v___x_1143_; 
v___x_1143_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_1131_ = v___y_1140_;
v___y_1132_ = v___y_1141_;
v___y_1133_ = v___x_1143_;
goto v___jp_1130_;
}
default: 
{
uint16_t v_port_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v_port_1144_ = lean_ctor_get_uint16(v_port_1138_, 0);
lean_dec_ref_known(v_port_1138_, 0);
v___x_1145_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1146_ = lean_uint16_to_nat(v_port_1144_);
v___x_1147_ = l_Nat_reprFast(v___x_1146_);
v___x_1148_ = lean_string_append(v___x_1145_, v___x_1147_);
lean_dec_ref(v___x_1147_);
v___y_1131_ = v___y_1140_;
v___y_1132_ = v___y_1141_;
v___y_1133_ = v___x_1148_;
goto v___jp_1130_;
}
}
}
v___jp_1149_:
{
switch(lean_obj_tag(v_host_1137_))
{
case 0:
{
lean_object* v_name_1151_; 
v_name_1151_ = lean_ctor_get(v_host_1137_, 0);
lean_inc_ref(v_name_1151_);
lean_dec_ref_known(v_host_1137_, 1);
v___y_1140_ = v___y_1150_;
v___y_1141_ = v_name_1151_;
goto v___jp_1139_;
}
case 1:
{
lean_object* v_ipv4_1152_; lean_object* v___x_1153_; 
v_ipv4_1152_ = lean_ctor_get(v_host_1137_, 0);
lean_inc_ref(v_ipv4_1152_);
lean_dec_ref_known(v_host_1137_, 1);
v___x_1153_ = lean_uv_ntop_v4(v_ipv4_1152_);
lean_dec_ref(v_ipv4_1152_);
v___y_1140_ = v___y_1150_;
v___y_1141_ = v___x_1153_;
goto v___jp_1139_;
}
default: 
{
lean_object* v_ipv6_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_ipv6_1154_ = lean_ctor_get(v_host_1137_, 0);
lean_inc_ref(v_ipv6_1154_);
lean_dec_ref_known(v_host_1137_, 1);
v___x_1155_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_1156_ = lean_uv_ntop_v6(v_ipv6_1154_);
lean_dec_ref(v_ipv6_1154_);
v___x_1157_ = lean_string_append(v___x_1155_, v___x_1156_);
lean_dec_ref(v___x_1156_);
v___x_1158_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_1159_ = lean_string_append(v___x_1157_, v___x_1158_);
v___y_1140_ = v___y_1150_;
v___y_1141_ = v___x_1159_;
goto v___jp_1139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1185_, lean_object* v_x_1186_, lean_object* v_x_1187_){
_start:
{
if (lean_obj_tag(v_x_1187_) == 0)
{
lean_dec(v_x_1185_);
return v_x_1186_;
}
else
{
lean_object* v_head_1188_; lean_object* v_tail_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1201_; 
v_head_1188_ = lean_ctor_get(v_x_1187_, 0);
v_tail_1189_ = lean_ctor_get(v_x_1187_, 1);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_x_1187_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1191_ = v_x_1187_;
v_isShared_1192_ = v_isSharedCheck_1201_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_tail_1189_);
lean_inc(v_head_1188_);
lean_dec(v_x_1187_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1201_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
lean_inc(v_x_1185_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set_tag(v___x_1191_, 5);
lean_ctor_set(v___x_1191_, 1, v_x_1185_);
lean_ctor_set(v___x_1191_, 0, v_x_1186_);
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_x_1186_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_x_1185_);
v___x_1194_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1195_ = lean_string_from_utf8_unchecked(v_head_1188_);
v___x_1196_ = l_String_quote(v___x_1195_);
v___x_1197_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
v___x_1198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1194_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v_x_1186_ = v___x_1198_;
v_x_1187_ = v_tail_1189_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(lean_object* v_x_1202_, lean_object* v_x_1203_, lean_object* v_x_1204_){
_start:
{
if (lean_obj_tag(v_x_1204_) == 0)
{
lean_dec(v_x_1202_);
return v_x_1203_;
}
else
{
lean_object* v_head_1205_; lean_object* v_tail_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1218_; 
v_head_1205_ = lean_ctor_get(v_x_1204_, 0);
v_tail_1206_ = lean_ctor_get(v_x_1204_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_x_1204_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1208_ = v_x_1204_;
v_isShared_1209_ = v_isSharedCheck_1218_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_tail_1206_);
lean_inc(v_head_1205_);
lean_dec(v_x_1204_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1218_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
lean_inc(v_x_1202_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set_tag(v___x_1208_, 5);
lean_ctor_set(v___x_1208_, 1, v_x_1202_);
lean_ctor_set(v___x_1208_, 0, v_x_1203_);
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_x_1203_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_x_1202_);
v___x_1211_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1212_ = lean_string_from_utf8_unchecked(v_head_1205_);
v___x_1213_ = l_String_quote(v___x_1212_);
v___x_1214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1211_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(v_x_1202_, v___x_1215_, v_tail_1206_);
return v___x_1216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = lean_string_from_utf8_unchecked(v___y_1219_);
v___x_1221_ = l_String_quote(v___x_1220_);
v___x_1222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(lean_object* v_x_1223_, lean_object* v_x_1224_){
_start:
{
if (lean_obj_tag(v_x_1223_) == 0)
{
lean_object* v___x_1225_; 
lean_dec(v_x_1224_);
v___x_1225_ = lean_box(0);
return v___x_1225_;
}
else
{
lean_object* v_tail_1226_; 
v_tail_1226_ = lean_ctor_get(v_x_1223_, 1);
if (lean_obj_tag(v_tail_1226_) == 0)
{
lean_object* v_head_1227_; lean_object* v___x_1228_; 
lean_dec(v_x_1224_);
v_head_1227_ = lean_ctor_get(v_x_1223_, 0);
lean_inc(v_head_1227_);
lean_dec_ref_known(v_x_1223_, 2);
v___x_1228_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1227_);
return v___x_1228_;
}
else
{
lean_object* v_head_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_inc(v_tail_1226_);
v_head_1229_ = lean_ctor_get(v_x_1223_, 0);
lean_inc(v_head_1229_);
lean_dec_ref_known(v_x_1223_, 2);
v___x_1230_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1229_);
v___x_1231_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(v_x_1224_, v___x_1230_, v_tail_1226_);
return v___x_1231_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0));
v___x_1237_ = lean_string_length(v___x_1236_);
return v___x_1237_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2);
v___x_1239_ = lean_nat_to_int(v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(lean_object* v_xs_1247_){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1248_ = lean_array_get_size(v_xs_1247_);
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = lean_nat_dec_eq(v___x_1248_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1251_ = lean_array_to_list(v_xs_1247_);
v___x_1252_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1253_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(v___x_1251_, v___x_1252_);
v___x_1254_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1255_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
lean_ctor_set(v___x_1256_, 1, v___x_1253_);
v___x_1257_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1256_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1254_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = l_Std_Format_fill(v___x_1259_);
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; 
lean_dec_ref(v_xs_1247_);
v___x_1261_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___redArg(lean_object* v_x_1274_){
_start:
{
lean_object* v_segments_1275_; uint8_t v_absolute_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1308_; 
v_segments_1275_ = lean_ctor_get(v_x_1274_, 0);
v_absolute_1276_ = lean_ctor_get_uint8(v_x_1274_, sizeof(void*)*1);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_x_1274_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1278_ = v_x_1274_;
v_isShared_1279_ = v_isSharedCheck_1308_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_segments_1275_);
lean_dec(v_x_1274_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1308_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; lean_object* v___x_1287_; 
v___x_1280_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1281_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__3));
v___x_1282_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_1283_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(v_segments_1275_);
v___x_1284_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = 0;
if (v_isShared_1279_ == 0)
{
lean_ctor_set_tag(v___x_1278_, 6);
lean_ctor_set(v___x_1278_, 0, v___x_1284_);
v___x_1287_ = v___x_1278_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1284_);
v___x_1287_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_ctor_set_uint8(v___x_1287_, sizeof(void*)*1, v___x_1285_);
v___x_1288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1281_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = lean_box(1);
v___x_1292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1290_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v___x_1293_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__5));
v___x_1294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1292_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v___x_1280_);
v___x_1296_ = l_Bool_repr___redArg(v_absolute_1276_);
v___x_1297_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1282_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
v___x_1298_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
lean_ctor_set_uint8(v___x_1298_, sizeof(void*)*1, v___x_1285_);
v___x_1299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1295_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1301_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1302_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v___x_1299_);
v___x_1303_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1300_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set_uint8(v___x_1306_, sizeof(void*)*1, v___x_1285_);
return v___x_1306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr(lean_object* v_x_1309_, lean_object* v_prec_1310_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Std_Http_URI_instReprPath_repr___redArg(v_x_1309_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___boxed(lean_object* v_x_1312_, lean_object* v_prec_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Std_Http_URI_instReprPath_repr(v_x_1312_, v_prec_1313_);
lean_dec(v_prec_1313_);
return v_res_1314_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(lean_object* v_xs_1317_, lean_object* v_ys_1318_, lean_object* v_x_1319_){
_start:
{
lean_object* v_zero_1320_; uint8_t v_isZero_1321_; 
v_zero_1320_ = lean_unsigned_to_nat(0u);
v_isZero_1321_ = lean_nat_dec_eq(v_x_1319_, v_zero_1320_);
if (v_isZero_1321_ == 1)
{
lean_dec(v_x_1319_);
return v_isZero_1321_;
}
else
{
lean_object* v_one_1322_; lean_object* v_n_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_one_1322_ = lean_unsigned_to_nat(1u);
v_n_1323_ = lean_nat_sub(v_x_1319_, v_one_1322_);
lean_dec(v_x_1319_);
v___x_1324_ = lean_array_fget_borrowed(v_xs_1317_, v_n_1323_);
v___x_1325_ = lean_array_fget_borrowed(v_ys_1318_, v_n_1323_);
v___x_1326_ = lean_sarray_dec_eq(v___x_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_dec(v_n_1323_);
return v___x_1326_;
}
else
{
v_x_1319_ = v_n_1323_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg___boxed(lean_object* v_xs_1328_, lean_object* v_ys_1329_, lean_object* v_x_1330_){
_start:
{
uint8_t v_res_1331_; lean_object* v_r_1332_; 
v_res_1331_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1328_, v_ys_1329_, v_x_1330_);
lean_dec_ref(v_ys_1329_);
lean_dec_ref(v_xs_1328_);
v_r_1332_ = lean_box(v_res_1331_);
return v_r_1332_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqPath_beq(lean_object* v_x_1333_, lean_object* v_x_1334_){
_start:
{
lean_object* v_segments_1335_; uint8_t v_absolute_1336_; lean_object* v_segments_1337_; uint8_t v_absolute_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v_segments_1335_ = lean_ctor_get(v_x_1333_, 0);
v_absolute_1336_ = lean_ctor_get_uint8(v_x_1333_, sizeof(void*)*1);
v_segments_1337_ = lean_ctor_get(v_x_1334_, 0);
v_absolute_1338_ = lean_ctor_get_uint8(v_x_1334_, sizeof(void*)*1);
v___x_1339_ = lean_array_get_size(v_segments_1335_);
v___x_1340_ = lean_array_get_size(v_segments_1337_);
v___x_1341_ = lean_nat_dec_eq(v___x_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
return v___x_1341_;
}
else
{
uint8_t v___x_1342_; 
v___x_1342_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_segments_1335_, v_segments_1337_, v___x_1339_);
if (v___x_1342_ == 0)
{
return v___x_1342_;
}
else
{
if (v_absolute_1336_ == 0)
{
if (v_absolute_1338_ == 0)
{
return v___x_1342_;
}
else
{
return v_absolute_1336_;
}
}
else
{
return v_absolute_1338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqPath_beq___boxed(lean_object* v_x_1343_, lean_object* v_x_1344_){
_start:
{
uint8_t v_res_1345_; lean_object* v_r_1346_; 
v_res_1345_ = l_Std_Http_URI_instBEqPath_beq(v_x_1343_, v_x_1344_);
lean_dec_ref(v_x_1344_);
lean_dec_ref(v_x_1343_);
v_r_1346_ = lean_box(v_res_1345_);
return v_r_1346_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(lean_object* v_xs_1347_, lean_object* v_ys_1348_, lean_object* v_hsz_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_){
_start:
{
uint8_t v___x_1352_; 
v___x_1352_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1347_, v_ys_1348_, v_x_1350_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___boxed(lean_object* v_xs_1353_, lean_object* v_ys_1354_, lean_object* v_hsz_1355_, lean_object* v_x_1356_, lean_object* v_x_1357_){
_start:
{
uint8_t v_res_1358_; lean_object* v_r_1359_; 
v_res_1358_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(v_xs_1353_, v_ys_1354_, v_hsz_1355_, v_x_1356_, v_x_1357_);
lean_dec_ref(v_ys_1354_);
lean_dec_ref(v_xs_1353_);
v_r_1359_ = lean_box(v_res_1358_);
return v_r_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__0(lean_object* v_x_1362_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_string_from_utf8_unchecked(v_x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__1(lean_object* v___f_1384_, lean_object* v_path_1385_){
_start:
{
lean_object* v_segments_1386_; uint8_t v_absolute_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; size_t v_sz_1390_; size_t v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v_result_1394_; 
v_segments_1386_ = lean_ctor_get(v_path_1385_, 0);
lean_inc_ref(v_segments_1386_);
v_absolute_1387_ = lean_ctor_get_uint8(v_path_1385_, sizeof(void*)*1);
lean_dec_ref(v_path_1385_);
v___x_1388_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_1389_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_1390_ = lean_array_size(v_segments_1386_);
v___x_1391_ = ((size_t)0ULL);
v___x_1392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1389_, v___f_1384_, v_sz_1390_, v___x_1391_, v_segments_1386_);
v___x_1393_ = lean_array_to_list(v___x_1392_);
v_result_1394_ = l_String_intercalate(v___x_1388_, v___x_1393_);
if (v_absolute_1387_ == 0)
{
return v_result_1394_;
}
else
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_string_append(v___x_1388_, v_result_1394_);
lean_dec_ref(v_result_1394_);
return v___x_1395_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Path_isEmpty(lean_object* v_p_1400_){
_start:
{
lean_object* v_segments_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v_segments_1401_ = lean_ctor_get(v_p_1400_, 0);
v___x_1402_ = lean_array_get_size(v_segments_1401_);
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1404_ = lean_nat_dec_eq(v___x_1402_, v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_isEmpty___boxed(lean_object* v_p_1405_){
_start:
{
uint8_t v_res_1406_; lean_object* v_r_1407_; 
v_res_1406_ = l_Std_Http_URI_Path_isEmpty(v_p_1405_);
lean_dec_ref(v_p_1405_);
v_r_1407_ = lean_box(v_res_1406_);
return v_r_1407_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parent(lean_object* v_p_1408_){
_start:
{
lean_object* v_segments_1409_; uint8_t v_absolute_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v_segments_1409_ = lean_ctor_get(v_p_1408_, 0);
v_absolute_1410_ = lean_ctor_get_uint8(v_p_1408_, sizeof(void*)*1);
v___x_1411_ = lean_array_get_size(v_segments_1409_);
v___x_1412_ = lean_unsigned_to_nat(0u);
v___x_1413_ = lean_nat_dec_eq(v___x_1411_, v___x_1412_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1421_; 
lean_inc_ref(v_segments_1409_);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_p_1408_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v_p_1408_, 0);
lean_dec(v_unused_1422_);
v___x_1415_ = v_p_1408_;
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
else
{
lean_dec(v_p_1408_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1417_ = lean_array_pop(v_segments_1409_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1417_);
v___x_1419_ = v___x_1415_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*1, v_absolute_1410_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
else
{
return v_p_1408_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join(lean_object* v_p1_1423_, lean_object* v_p2_1424_){
_start:
{
uint8_t v_absolute_1425_; 
v_absolute_1425_ = lean_ctor_get_uint8(v_p2_1424_, sizeof(void*)*1);
if (v_absolute_1425_ == 0)
{
lean_object* v_segments_1426_; lean_object* v_segments_1427_; uint8_t v_absolute_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1436_; 
v_segments_1426_ = lean_ctor_get(v_p2_1424_, 0);
v_segments_1427_ = lean_ctor_get(v_p1_1423_, 0);
v_absolute_1428_ = lean_ctor_get_uint8(v_p1_1423_, sizeof(void*)*1);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_p1_1423_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1430_ = v_p1_1423_;
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_segments_1427_);
lean_dec(v_p1_1423_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = l_Array_append___redArg(v_segments_1427_, v_segments_1426_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
lean_ctor_set_uint8(v_reuseFailAlloc_1435_, sizeof(void*)*1, v_absolute_1428_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
else
{
lean_dec_ref(v_p1_1423_);
lean_inc_ref(v_p2_1424_);
return v_p2_1424_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join___boxed(lean_object* v_p1_1437_, lean_object* v_p2_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Std_Http_URI_Path_join(v_p1_1437_, v_p2_1438_);
lean_dec_ref(v_p2_1438_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append(lean_object* v_p_1440_, lean_object* v_segment_1441_){
_start:
{
lean_object* v_segments_1442_; uint8_t v_absolute_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1452_; 
v_segments_1442_ = lean_ctor_get(v_p_1440_, 0);
v_absolute_1443_ = lean_ctor_get_uint8(v_p_1440_, sizeof(void*)*1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_p_1440_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1445_ = v_p_1440_;
v_isShared_1446_ = v_isSharedCheck_1452_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_segments_1442_);
lean_dec(v_p_1440_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1452_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1447_ = l_Std_Http_URI_EncodedSegment_encode(v_segment_1441_);
v___x_1448_ = lean_array_push(v_segments_1442_, v___x_1447_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1448_);
v___x_1450_ = v___x_1445_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
lean_ctor_set_uint8(v_reuseFailAlloc_1451_, sizeof(void*)*1, v_absolute_1443_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append___boxed(lean_object* v_p_1453_, lean_object* v_segment_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Std_Http_URI_Path_append(v_p_1453_, v_segment_1454_);
lean_dec_ref(v_segment_1454_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_appendEncoded(lean_object* v_p_1456_, lean_object* v_segment_1457_){
_start:
{
lean_object* v_segments_1458_; uint8_t v_absolute_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1467_; 
v_segments_1458_ = lean_ctor_get(v_p_1456_, 0);
v_absolute_1459_ = lean_ctor_get_uint8(v_p_1456_, sizeof(void*)*1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_p_1456_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1461_ = v_p_1456_;
v_isShared_1462_ = v_isSharedCheck_1467_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_segments_1458_);
lean_dec(v_p_1456_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1467_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1463_ = lean_array_push(v_segments_1458_, v_segment_1457_);
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
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(lean_object* v_input_1470_, lean_object* v_output_1471_){
_start:
{
if (lean_obj_tag(v_input_1470_) == 0)
{
lean_object* v___x_1472_; 
v___x_1472_ = l_List_reverse___redArg(v_output_1471_);
return v___x_1472_;
}
else
{
lean_object* v_head_1473_; lean_object* v_tail_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1491_; 
v_head_1473_ = lean_ctor_get(v_input_1470_, 0);
v_tail_1474_ = lean_ctor_get(v_input_1470_, 1);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_input_1470_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1476_ = v_input_1470_;
v_isShared_1477_ = v_isSharedCheck_1491_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_tail_1474_);
lean_inc(v_head_1473_);
lean_dec(v_input_1470_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1491_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
lean_inc(v_head_1473_);
v___x_1478_ = lean_string_from_utf8_unchecked(v_head_1473_);
v___x_1479_ = ((lean_object*)(l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0));
v___x_1480_ = lean_string_dec_eq(v___x_1478_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1481_ = ((lean_object*)(l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1));
v___x_1482_ = lean_string_dec_eq(v___x_1478_, v___x_1481_);
lean_dec_ref(v___x_1478_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1484_; 
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 1, v_output_1471_);
v___x_1484_ = v___x_1476_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_head_1473_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_output_1471_);
v___x_1484_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
v_input_1470_ = v_tail_1474_;
v_output_1471_ = v___x_1484_;
goto _start;
}
}
else
{
lean_del_object(v___x_1476_);
lean_dec(v_head_1473_);
if (lean_obj_tag(v_output_1471_) == 0)
{
v_input_1470_ = v_tail_1474_;
goto _start;
}
else
{
lean_object* v_tail_1488_; 
v_tail_1488_ = lean_ctor_get(v_output_1471_, 1);
lean_inc(v_tail_1488_);
lean_dec_ref_known(v_output_1471_, 2);
v_input_1470_ = v_tail_1474_;
v_output_1471_ = v_tail_1488_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_1478_);
lean_del_object(v___x_1476_);
lean_dec(v_head_1473_);
v_input_1470_ = v_tail_1474_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_normalize(lean_object* v_p_1492_){
_start:
{
lean_object* v_segments_1493_; uint8_t v_absolute_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1505_; 
v_segments_1493_ = lean_ctor_get(v_p_1492_, 0);
v_absolute_1494_ = lean_ctor_get_uint8(v_p_1492_, sizeof(void*)*1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_p_1492_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1496_ = v_p_1492_;
v_isShared_1497_ = v_isSharedCheck_1505_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_segments_1493_);
lean_dec(v_p_1492_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1505_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1498_ = lean_array_to_list(v_segments_1493_);
v___x_1499_ = lean_box(0);
v___x_1500_ = l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(v___x_1498_, v___x_1499_);
v___x_1501_ = lean_array_mk(v___x_1500_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1501_);
v___x_1503_ = v___x_1496_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
lean_ctor_set_uint8(v_reuseFailAlloc_1504_, sizeof(void*)*1, v_absolute_1494_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(size_t v_sz_1506_, size_t v_i_1507_, lean_object* v_bs_1508_){
_start:
{
uint8_t v___x_1509_; 
v___x_1509_ = lean_usize_dec_lt(v_i_1507_, v_sz_1506_);
if (v___x_1509_ == 0)
{
return v_bs_1508_;
}
else
{
lean_object* v_v_1510_; lean_object* v___x_1511_; lean_object* v_bs_x27_1512_; lean_object* v___y_1514_; lean_object* v___x_1519_; 
v_v_1510_ = lean_array_uget(v_bs_1508_, v_i_1507_);
v___x_1511_ = lean_unsigned_to_nat(0u);
v_bs_x27_1512_ = lean_array_uset(v_bs_1508_, v_i_1507_, v___x_1511_);
v___x_1519_ = l_Std_Http_URI_EncodedSegment_decode(v_v_1510_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_string_from_utf8_unchecked(v_v_1510_);
v___y_1514_ = v___x_1520_;
goto v___jp_1513_;
}
else
{
lean_object* v_val_1521_; 
lean_dec(v_v_1510_);
v_val_1521_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_val_1521_);
lean_dec_ref_known(v___x_1519_, 1);
v___y_1514_ = v_val_1521_;
goto v___jp_1513_;
}
v___jp_1513_:
{
size_t v___x_1515_; size_t v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = ((size_t)1ULL);
v___x_1516_ = lean_usize_add(v_i_1507_, v___x_1515_);
v___x_1517_ = lean_array_uset(v_bs_x27_1512_, v_i_1507_, v___y_1514_);
v_i_1507_ = v___x_1516_;
v_bs_1508_ = v___x_1517_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0___boxed(lean_object* v_sz_1522_, lean_object* v_i_1523_, lean_object* v_bs_1524_){
_start:
{
size_t v_sz_boxed_1525_; size_t v_i_boxed_1526_; lean_object* v_res_1527_; 
v_sz_boxed_1525_ = lean_unbox_usize(v_sz_1522_);
lean_dec(v_sz_1522_);
v_i_boxed_1526_ = lean_unbox_usize(v_i_1523_);
lean_dec(v_i_1523_);
v_res_1527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_boxed_1525_, v_i_boxed_1526_, v_bs_1524_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_toDecodedSegments(lean_object* v_p_1528_){
_start:
{
lean_object* v_segments_1529_; size_t v_sz_1530_; size_t v___x_1531_; lean_object* v___x_1532_; 
v_segments_1529_ = lean_ctor_get(v_p_1528_, 0);
lean_inc_ref(v_segments_1529_);
lean_dec_ref(v_p_1528_);
v_sz_1530_ = lean_array_size(v_segments_1529_);
v___x_1531_ = ((size_t)0ULL);
v___x_1532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_1530_, v___x_1531_, v_segments_1529_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___redArg(lean_object* v_xs_1541_){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1543_ = l_Array_repr___redArg(v___x_1542_, v_xs_1541_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1(lean_object* v_xs_1544_, lean_object* v_x_1545_){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1547_ = l_Array_repr___redArg(v___x_1546_, v_xs_1544_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___boxed(lean_object* v_xs_1548_, lean_object* v_x_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Std_Http_URI_instReprQuery___aux__1(v_xs_1548_, v_x_1549_);
lean_dec(v_x_1549_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_){
_start:
{
if (lean_obj_tag(v_x_1553_) == 0)
{
lean_dec(v_x_1551_);
return v_x_1552_;
}
else
{
lean_object* v_head_1554_; lean_object* v_tail_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1564_; 
v_head_1554_ = lean_ctor_get(v_x_1553_, 0);
v_tail_1555_ = lean_ctor_get(v_x_1553_, 1);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_x_1553_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1557_ = v_x_1553_;
v_isShared_1558_ = v_isSharedCheck_1564_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_tail_1555_);
lean_inc(v_head_1554_);
lean_dec(v_x_1553_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1564_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
lean_inc(v_x_1551_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set_tag(v___x_1557_, 5);
lean_ctor_set(v___x_1557_, 1, v_x_1551_);
lean_ctor_set(v___x_1557_, 0, v_x_1552_);
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_x_1552_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_x_1551_);
v___x_1560_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_ctor_set(v___x_1561_, 1, v_head_1554_);
v_x_1552_ = v___x_1561_;
v_x_1553_ = v_tail_1555_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(lean_object* v_x_1565_, lean_object* v_x_1566_){
_start:
{
if (lean_obj_tag(v_x_1565_) == 0)
{
lean_object* v___x_1567_; 
lean_dec(v_x_1566_);
v___x_1567_ = lean_box(0);
return v___x_1567_;
}
else
{
lean_object* v_tail_1568_; 
v_tail_1568_ = lean_ctor_get(v_x_1565_, 1);
if (lean_obj_tag(v_tail_1568_) == 0)
{
lean_object* v_head_1569_; 
lean_dec(v_x_1566_);
v_head_1569_ = lean_ctor_get(v_x_1565_, 0);
lean_inc(v_head_1569_);
lean_dec_ref_known(v_x_1565_, 2);
return v_head_1569_;
}
else
{
lean_object* v_head_1570_; lean_object* v___x_1571_; 
lean_inc(v_tail_1568_);
v_head_1570_ = lean_ctor_get(v_x_1565_, 0);
lean_inc(v_head_1570_);
lean_dec_ref_known(v_x_1565_, 2);
v___x_1571_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(v_x_1566_, v_head_1570_, v_tail_1568_);
return v___x_1571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(lean_object* v_x_1572_, lean_object* v_x_1573_){
_start:
{
if (lean_obj_tag(v_x_1572_) == 0)
{
lean_object* v___x_1574_; 
v___x_1574_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1574_;
}
else
{
lean_object* v_val_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1587_; 
v_val_1575_ = lean_ctor_get(v_x_1572_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_x_1572_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1577_ = v_x_1572_;
v_isShared_1578_ = v_isSharedCheck_1587_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_val_1575_);
lean_dec(v_x_1572_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1587_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1579_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1580_ = lean_string_from_utf8_unchecked(v_val_1575_);
v___x_1581_ = l_String_quote(v___x_1580_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set_tag(v___x_1577_, 3);
lean_ctor_set(v___x_1577_, 0, v___x_1581_);
v___x_1583_ = v___x_1577_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1579_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = l_Repr_addAppParen(v___x_1584_, v_x_1573_);
return v___x_1585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1588_, lean_object* v_x_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_x_1588_, v_x_1589_);
lean_dec(v_x_1589_);
return v_res_1590_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0));
v___x_1594_ = lean_string_length(v___x_1593_);
return v___x_1594_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2);
v___x_1596_ = lean_nat_to_int(v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(lean_object* v_x_1601_){
_start:
{
lean_object* v_fst_1602_; lean_object* v_snd_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1628_; 
v_fst_1602_ = lean_ctor_get(v_x_1601_, 0);
v_snd_1603_ = lean_ctor_get(v_x_1601_, 1);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_x_1601_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1605_ = v_x_1601_;
v_isShared_1606_ = v_isSharedCheck_1628_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_snd_1603_);
lean_inc(v_fst_1602_);
lean_dec(v_x_1601_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1628_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1607_ = lean_string_from_utf8_unchecked(v_fst_1602_);
v___x_1608_ = l_String_quote(v___x_1607_);
v___x_1609_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
v___x_1610_ = lean_box(0);
if (v_isShared_1606_ == 0)
{
lean_ctor_set_tag(v___x_1605_, 1);
lean_ctor_set(v___x_1605_, 1, v___x_1610_);
lean_ctor_set(v___x_1605_, 0, v___x_1609_);
v___x_1612_ = v___x_1605_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; lean_object* v___x_1626_; 
v___x_1613_ = lean_unsigned_to_nat(0u);
v___x_1614_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_snd_1603_, v___x_1613_);
v___x_1615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
lean_ctor_set(v___x_1615_, 1, v___x_1612_);
v___x_1616_ = l_List_reverse___redArg(v___x_1615_);
v___x_1617_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1618_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(v___x_1616_, v___x_1617_);
v___x_1619_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3);
v___x_1620_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4));
v___x_1621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
lean_ctor_set(v___x_1621_, 1, v___x_1618_);
v___x_1622_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5));
v___x_1623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1619_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = 0;
v___x_1626_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1626_, 0, v___x_1624_);
lean_ctor_set_uint8(v___x_1626_, sizeof(void*)*1, v___x_1625_);
return v___x_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(lean_object* v_x_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_){
_start:
{
if (lean_obj_tag(v_x_1631_) == 0)
{
lean_dec(v_x_1629_);
return v_x_1630_;
}
else
{
lean_object* v_head_1632_; lean_object* v_tail_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1643_; 
v_head_1632_ = lean_ctor_get(v_x_1631_, 0);
v_tail_1633_ = lean_ctor_get(v_x_1631_, 1);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1635_ = v_x_1631_;
v_isShared_1636_ = v_isSharedCheck_1643_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_tail_1633_);
lean_inc(v_head_1632_);
lean_dec(v_x_1631_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1643_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
lean_inc(v_x_1629_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set_tag(v___x_1635_, 5);
lean_ctor_set(v___x_1635_, 1, v_x_1629_);
lean_ctor_set(v___x_1635_, 0, v_x_1630_);
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_x_1630_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_x_1629_);
v___x_1638_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1632_);
v___x_1640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v_x_1630_ = v___x_1640_;
v_x_1631_ = v_tail_1633_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(lean_object* v_x_1644_, lean_object* v_x_1645_, lean_object* v_x_1646_){
_start:
{
if (lean_obj_tag(v_x_1646_) == 0)
{
lean_dec(v_x_1644_);
return v_x_1645_;
}
else
{
lean_object* v_head_1647_; lean_object* v_tail_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1658_; 
v_head_1647_ = lean_ctor_get(v_x_1646_, 0);
v_tail_1648_ = lean_ctor_get(v_x_1646_, 1);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_x_1646_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1650_ = v_x_1646_;
v_isShared_1651_ = v_isSharedCheck_1658_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_tail_1648_);
lean_inc(v_head_1647_);
lean_dec(v_x_1646_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1658_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
lean_inc(v_x_1644_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set_tag(v___x_1650_, 5);
lean_ctor_set(v___x_1650_, 1, v_x_1644_);
lean_ctor_set(v___x_1650_, 0, v_x_1645_);
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_x_1645_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_x_1644_);
v___x_1653_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1647_);
v___x_1655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(v_x_1644_, v___x_1655_, v_tail_1648_);
return v___x_1656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(lean_object* v_x_1659_, lean_object* v_x_1660_){
_start:
{
if (lean_obj_tag(v_x_1659_) == 0)
{
lean_object* v___x_1661_; 
lean_dec(v_x_1660_);
v___x_1661_ = lean_box(0);
return v___x_1661_;
}
else
{
lean_object* v_tail_1662_; 
v_tail_1662_ = lean_ctor_get(v_x_1659_, 1);
if (lean_obj_tag(v_tail_1662_) == 0)
{
lean_object* v_head_1663_; lean_object* v___x_1664_; 
lean_dec(v_x_1660_);
v_head_1663_ = lean_ctor_get(v_x_1659_, 0);
lean_inc(v_head_1663_);
lean_dec_ref_known(v_x_1659_, 2);
v___x_1664_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1663_);
return v___x_1664_;
}
else
{
lean_object* v_head_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_inc(v_tail_1662_);
v_head_1665_ = lean_ctor_get(v_x_1659_, 0);
lean_inc(v_head_1665_);
lean_dec_ref_known(v_x_1659_, 2);
v___x_1666_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1665_);
v___x_1667_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(v_x_1660_, v___x_1666_, v_tail_1662_);
return v___x_1667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(lean_object* v_xs_1668_){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1669_ = lean_array_get_size(v_xs_1668_);
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = lean_nat_dec_eq(v___x_1669_, v___x_1670_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1672_ = lean_array_to_list(v_xs_1668_);
v___x_1673_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1674_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(v___x_1672_, v___x_1673_);
v___x_1675_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1676_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v___x_1674_);
v___x_1678_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1675_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = l_Std_Format_fill(v___x_1680_);
return v___x_1681_;
}
else
{
lean_object* v___x_1682_; 
lean_dec_ref(v_xs_1668_);
v___x_1682_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1682_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0(lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v___y_1683_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0___boxed(lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Std_Http_URI_instReprQuery___lam__0(v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(lean_object* v_x_1691_, lean_object* v_x_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_x_1691_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___boxed(lean_object* v_x_1694_, lean_object* v_x_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(v_x_1694_, v_x_1695_);
lean_dec(v_x_1695_);
return v_res_1696_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1___lam__0(lean_object* v___f_1701_, lean_object* v_x_1702_, lean_object* v_x_1703_){
_start:
{
lean_object* v_fst_1704_; lean_object* v_snd_1705_; lean_object* v_fst_1706_; lean_object* v_snd_1707_; uint8_t v___x_1708_; 
v_fst_1704_ = lean_ctor_get(v_x_1702_, 0);
lean_inc(v_fst_1704_);
v_snd_1705_ = lean_ctor_get(v_x_1702_, 1);
lean_inc(v_snd_1705_);
lean_dec_ref(v_x_1702_);
v_fst_1706_ = lean_ctor_get(v_x_1703_, 0);
lean_inc(v_fst_1706_);
v_snd_1707_ = lean_ctor_get(v_x_1703_, 1);
lean_inc(v_snd_1707_);
lean_dec_ref(v_x_1703_);
v___x_1708_ = lean_sarray_dec_eq(v_fst_1704_, v_fst_1706_);
lean_dec(v_fst_1706_);
lean_dec(v_fst_1704_);
if (v___x_1708_ == 0)
{
lean_dec(v_snd_1707_);
lean_dec(v_snd_1705_);
lean_dec_ref(v___f_1701_);
return v___x_1708_;
}
else
{
uint8_t v___x_1709_; 
v___x_1709_ = l_Option_instBEq_beq___redArg(v___f_1701_, v_snd_1705_, v_snd_1707_);
return v___x_1709_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___lam__0___boxed(lean_object* v___f_1710_, lean_object* v_x_1711_, lean_object* v_x_1712_){
_start:
{
uint8_t v_res_1713_; lean_object* v_r_1714_; 
v_res_1713_ = l_Std_Http_URI_instBEqQuery___aux__1___lam__0(v___f_1710_, v_x_1711_, v_x_1712_);
v_r_1714_ = lean_box(v_res_1713_);
return v_r_1714_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1(lean_object* v_xs_1718_, lean_object* v_ys_1719_){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v___x_1720_ = lean_array_get_size(v_xs_1718_);
v___x_1721_ = lean_array_get_size(v_ys_1719_);
v___x_1722_ = lean_nat_dec_eq(v___x_1720_, v___x_1721_);
if (v___x_1722_ == 0)
{
return v___x_1722_;
}
else
{
lean_object* v___f_1723_; uint8_t v___x_1724_; 
v___f_1723_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__1));
v___x_1724_ = l_Array_isEqvAux___redArg(v_xs_1718_, v_ys_1719_, v___f_1723_, v___x_1720_);
return v___x_1724_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___boxed(lean_object* v_xs_1725_, lean_object* v_ys_1726_){
_start:
{
uint8_t v_res_1727_; lean_object* v_r_1728_; 
v_res_1727_ = l_Std_Http_URI_instBEqQuery___aux__1(v_xs_1725_, v_ys_1726_);
lean_dec_ref(v_ys_1726_);
lean_dec_ref(v_xs_1725_);
v_r_1728_ = lean_box(v_res_1727_);
return v_r_1728_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(lean_object* v_x_1729_, lean_object* v_x_1730_){
_start:
{
if (lean_obj_tag(v_x_1729_) == 0)
{
if (lean_obj_tag(v_x_1730_) == 0)
{
uint8_t v___x_1731_; 
v___x_1731_ = 1;
return v___x_1731_;
}
else
{
uint8_t v___x_1732_; 
v___x_1732_ = 0;
return v___x_1732_;
}
}
else
{
if (lean_obj_tag(v_x_1730_) == 0)
{
uint8_t v___x_1733_; 
v___x_1733_ = 0;
return v___x_1733_;
}
else
{
lean_object* v_val_1734_; lean_object* v_val_1735_; uint8_t v___x_1736_; 
v_val_1734_ = lean_ctor_get(v_x_1729_, 0);
v_val_1735_ = lean_ctor_get(v_x_1730_, 0);
v___x_1736_ = lean_sarray_dec_eq(v_val_1734_, v_val_1735_);
return v___x_1736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0___boxed(lean_object* v_x_1737_, lean_object* v_x_1738_){
_start:
{
uint8_t v_res_1739_; lean_object* v_r_1740_; 
v_res_1739_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_x_1737_, v_x_1738_);
lean_dec(v_x_1738_);
lean_dec(v_x_1737_);
v_r_1740_ = lean_box(v_res_1739_);
return v_r_1740_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(lean_object* v_xs_1741_, lean_object* v_ys_1742_, lean_object* v_x_1743_){
_start:
{
lean_object* v_zero_1744_; uint8_t v_isZero_1745_; 
v_zero_1744_ = lean_unsigned_to_nat(0u);
v_isZero_1745_ = lean_nat_dec_eq(v_x_1743_, v_zero_1744_);
if (v_isZero_1745_ == 1)
{
lean_dec(v_x_1743_);
return v_isZero_1745_;
}
else
{
lean_object* v_one_1746_; lean_object* v_n_1747_; uint8_t v___y_1749_; lean_object* v___x_1751_; lean_object* v_fst_1752_; lean_object* v_snd_1753_; lean_object* v___x_1754_; lean_object* v_fst_1755_; lean_object* v_snd_1756_; uint8_t v___x_1757_; 
v_one_1746_ = lean_unsigned_to_nat(1u);
v_n_1747_ = lean_nat_sub(v_x_1743_, v_one_1746_);
lean_dec(v_x_1743_);
v___x_1751_ = lean_array_fget_borrowed(v_xs_1741_, v_n_1747_);
v_fst_1752_ = lean_ctor_get(v___x_1751_, 0);
v_snd_1753_ = lean_ctor_get(v___x_1751_, 1);
v___x_1754_ = lean_array_fget_borrowed(v_ys_1742_, v_n_1747_);
v_fst_1755_ = lean_ctor_get(v___x_1754_, 0);
v_snd_1756_ = lean_ctor_get(v___x_1754_, 1);
v___x_1757_ = lean_sarray_dec_eq(v_fst_1752_, v_fst_1755_);
if (v___x_1757_ == 0)
{
v___y_1749_ = v___x_1757_;
goto v___jp_1748_;
}
else
{
uint8_t v___x_1758_; 
v___x_1758_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_snd_1753_, v_snd_1756_);
v___y_1749_ = v___x_1758_;
goto v___jp_1748_;
}
v___jp_1748_:
{
if (v___y_1749_ == 0)
{
lean_dec(v_n_1747_);
return v___y_1749_;
}
else
{
v_x_1743_ = v_n_1747_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg___boxed(lean_object* v_xs_1759_, lean_object* v_ys_1760_, lean_object* v_x_1761_){
_start:
{
uint8_t v_res_1762_; lean_object* v_r_1763_; 
v_res_1762_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1759_, v_ys_1760_, v_x_1761_);
lean_dec_ref(v_ys_1760_);
lean_dec_ref(v_xs_1759_);
v_r_1763_ = lean_box(v_res_1762_);
return v_r_1763_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___lam__0(lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1766_ = lean_array_get_size(v___y_1764_);
v___x_1767_ = lean_array_get_size(v___y_1765_);
v___x_1768_ = lean_nat_dec_eq(v___x_1766_, v___x_1767_);
if (v___x_1768_ == 0)
{
return v___x_1768_;
}
else
{
uint8_t v___x_1769_; 
v___x_1769_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v___y_1764_, v___y_1765_, v___x_1766_);
return v___x_1769_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___lam__0___boxed(lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
uint8_t v_res_1772_; lean_object* v_r_1773_; 
v_res_1772_ = l_Std_Http_URI_instBEqQuery___lam__0(v___y_1770_, v___y_1771_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1770_);
v_r_1773_ = lean_box(v_res_1772_);
return v_r_1773_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(lean_object* v_xs_1776_, lean_object* v_ys_1777_, lean_object* v_hsz_1778_, lean_object* v_x_1779_, lean_object* v_x_1780_){
_start:
{
uint8_t v___x_1781_; 
v___x_1781_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1776_, v_ys_1777_, v_x_1779_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___boxed(lean_object* v_xs_1782_, lean_object* v_ys_1783_, lean_object* v_hsz_1784_, lean_object* v_x_1785_, lean_object* v_x_1786_){
_start:
{
uint8_t v_res_1787_; lean_object* v_r_1788_; 
v_res_1787_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(v_xs_1782_, v_ys_1783_, v_hsz_1784_, v_x_1785_, v_x_1786_);
lean_dec_ref(v_ys_1783_);
lean_dec_ref(v_xs_1782_);
v_r_1788_ = lean_box(v_res_1787_);
return v_r_1788_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(lean_object* v_as_1789_){
_start:
{
lean_object* v___f_1790_; lean_object* v___x_1791_; 
v___f_1790_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__0));
v___x_1791_ = l_List_eraseDupsBy___redArg(v___f_1790_, v_as_1789_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(size_t v_sz_1792_, size_t v_i_1793_, lean_object* v_bs_1794_){
_start:
{
uint8_t v___x_1795_; 
v___x_1795_ = lean_usize_dec_lt(v_i_1793_, v_sz_1792_);
if (v___x_1795_ == 0)
{
return v_bs_1794_;
}
else
{
lean_object* v_v_1796_; lean_object* v_fst_1797_; lean_object* v___x_1798_; lean_object* v_bs_x27_1799_; size_t v___x_1800_; size_t v___x_1801_; lean_object* v___x_1802_; 
v_v_1796_ = lean_array_uget_borrowed(v_bs_1794_, v_i_1793_);
v_fst_1797_ = lean_ctor_get(v_v_1796_, 0);
lean_inc(v_fst_1797_);
v___x_1798_ = lean_unsigned_to_nat(0u);
v_bs_x27_1799_ = lean_array_uset(v_bs_1794_, v_i_1793_, v___x_1798_);
v___x_1800_ = ((size_t)1ULL);
v___x_1801_ = lean_usize_add(v_i_1793_, v___x_1800_);
v___x_1802_ = lean_array_uset(v_bs_x27_1799_, v_i_1793_, v_fst_1797_);
v_i_1793_ = v___x_1801_;
v_bs_1794_ = v___x_1802_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0___boxed(lean_object* v_sz_1804_, lean_object* v_i_1805_, lean_object* v_bs_1806_){
_start:
{
size_t v_sz_boxed_1807_; size_t v_i_boxed_1808_; lean_object* v_res_1809_; 
v_sz_boxed_1807_ = lean_unbox_usize(v_sz_1804_);
lean_dec(v_sz_1804_);
v_i_boxed_1808_ = lean_unbox_usize(v_i_1805_);
lean_dec(v_i_1805_);
v_res_1809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_boxed_1807_, v_i_boxed_1808_, v_bs_1806_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names(lean_object* v_query_1810_){
_start:
{
size_t v_sz_1811_; size_t v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v_sz_1811_ = lean_array_size(v_query_1810_);
v___x_1812_ = ((size_t)0ULL);
v___x_1813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_1811_, v___x_1812_, v_query_1810_);
v___x_1814_ = lean_array_to_list(v___x_1813_);
v___x_1815_ = l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(v___x_1814_);
v___x_1816_ = lean_array_mk(v___x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(size_t v_sz_1817_, size_t v_i_1818_, lean_object* v_bs_1819_){
_start:
{
uint8_t v___x_1820_; 
v___x_1820_ = lean_usize_dec_lt(v_i_1818_, v_sz_1817_);
if (v___x_1820_ == 0)
{
return v_bs_1819_;
}
else
{
lean_object* v_v_1821_; lean_object* v_snd_1822_; lean_object* v___x_1823_; lean_object* v_bs_x27_1824_; size_t v___x_1825_; size_t v___x_1826_; lean_object* v___x_1827_; 
v_v_1821_ = lean_array_uget_borrowed(v_bs_1819_, v_i_1818_);
v_snd_1822_ = lean_ctor_get(v_v_1821_, 1);
lean_inc(v_snd_1822_);
v___x_1823_ = lean_unsigned_to_nat(0u);
v_bs_x27_1824_ = lean_array_uset(v_bs_1819_, v_i_1818_, v___x_1823_);
v___x_1825_ = ((size_t)1ULL);
v___x_1826_ = lean_usize_add(v_i_1818_, v___x_1825_);
v___x_1827_ = lean_array_uset(v_bs_x27_1824_, v_i_1818_, v_snd_1822_);
v_i_1818_ = v___x_1826_;
v_bs_1819_ = v___x_1827_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0___boxed(lean_object* v_sz_1829_, lean_object* v_i_1830_, lean_object* v_bs_1831_){
_start:
{
size_t v_sz_boxed_1832_; size_t v_i_boxed_1833_; lean_object* v_res_1834_; 
v_sz_boxed_1832_ = lean_unbox_usize(v_sz_1829_);
lean_dec(v_sz_1829_);
v_i_boxed_1833_ = lean_unbox_usize(v_i_1830_);
lean_dec(v_i_1830_);
v_res_1834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_boxed_1832_, v_i_boxed_1833_, v_bs_1831_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_values(lean_object* v_query_1835_){
_start:
{
size_t v_sz_1836_; size_t v___x_1837_; lean_object* v___x_1838_; 
v_sz_1836_ = lean_array_size(v_query_1835_);
v___x_1837_ = ((size_t)0ULL);
v___x_1838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_1836_, v___x_1837_, v_query_1835_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray(lean_object* v_query_1839_){
_start:
{
lean_inc_ref(v_query_1839_);
return v_query_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray___boxed(lean_object* v_query_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Std_Http_URI_Query_toArray(v_query_1840_);
lean_dec_ref(v_query_1840_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object* v_key_1843_, lean_object* v_value_1844_){
_start:
{
if (lean_obj_tag(v_value_1844_) == 0)
{
lean_object* v___x_1845_; 
v___x_1845_ = lean_string_from_utf8_unchecked(v_key_1843_);
return v___x_1845_;
}
else
{
lean_object* v_val_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_val_1846_ = lean_ctor_get(v_value_1844_, 0);
lean_inc(v_val_1846_);
lean_dec_ref_known(v_value_1844_, 1);
v___x_1847_ = lean_string_from_utf8_unchecked(v_key_1843_);
v___x_1848_ = ((lean_object*)(l_Std_Http_URI_Query_formatQueryParam___closed__0));
v___x_1849_ = lean_string_append(v___x_1847_, v___x_1848_);
v___x_1850_ = lean_string_from_utf8_unchecked(v_val_1846_);
v___x_1851_ = lean_string_append(v___x_1849_, v___x_1850_);
lean_dec_ref(v___x_1850_);
return v___x_1851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(lean_object* v_key_1855_, lean_object* v_as_1856_, size_t v_sz_1857_, size_t v_i_1858_, lean_object* v_b_1859_){
_start:
{
uint8_t v___x_1860_; 
v___x_1860_ = lean_usize_dec_lt(v_i_1858_, v_sz_1857_);
if (v___x_1860_ == 0)
{
lean_inc_ref(v_b_1859_);
return v_b_1859_;
}
else
{
lean_object* v_a_1861_; lean_object* v_fst_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v_a_1861_ = lean_array_uget_borrowed(v_as_1856_, v_i_1858_);
v_fst_1862_ = lean_ctor_get(v_a_1861_, 0);
v___x_1863_ = lean_box(0);
v___x_1864_ = lean_sarray_dec_eq(v_fst_1862_, v_key_1855_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; size_t v___x_1866_; size_t v___x_1867_; 
v___x_1865_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v___x_1866_ = ((size_t)1ULL);
v___x_1867_ = lean_usize_add(v_i_1858_, v___x_1866_);
v_i_1858_ = v___x_1867_;
v_b_1859_ = v___x_1865_;
goto _start;
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
lean_inc(v_a_1861_);
v___x_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1869_, 0, v_a_1861_);
v___x_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
lean_ctor_set(v___x_1871_, 1, v___x_1863_);
return v___x_1871_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___boxed(lean_object* v_key_1872_, lean_object* v_as_1873_, lean_object* v_sz_1874_, lean_object* v_i_1875_, lean_object* v_b_1876_){
_start:
{
size_t v_sz_boxed_1877_; size_t v_i_boxed_1878_; lean_object* v_res_1879_; 
v_sz_boxed_1877_ = lean_unbox_usize(v_sz_1874_);
lean_dec(v_sz_1874_);
v_i_boxed_1878_ = lean_unbox_usize(v_i_1875_);
lean_dec(v_i_1875_);
v_res_1879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1872_, v_as_1873_, v_sz_boxed_1877_, v_i_boxed_1878_, v_b_1876_);
lean_dec_ref(v_b_1876_);
lean_dec_ref(v_as_1873_);
lean_dec_ref(v_key_1872_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f(lean_object* v_query_1880_, lean_object* v_key_1881_){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; size_t v_sz_1884_; size_t v___x_1885_; lean_object* v___x_1886_; lean_object* v_fst_1887_; 
v___x_1882_ = lean_box(0);
v___x_1883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v_sz_1884_ = lean_array_size(v_query_1880_);
v___x_1885_ = ((size_t)0ULL);
v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1881_, v_query_1880_, v_sz_1884_, v___x_1885_, v___x_1883_);
v_fst_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_fst_1887_);
lean_dec_ref(v___x_1886_);
if (lean_obj_tag(v_fst_1887_) == 0)
{
return v___x_1882_;
}
else
{
lean_object* v_val_1888_; 
v_val_1888_ = lean_ctor_get(v_fst_1887_, 0);
lean_inc(v_val_1888_);
lean_dec_ref_known(v_fst_1887_, 1);
if (lean_obj_tag(v_val_1888_) == 0)
{
return v___x_1882_;
}
else
{
lean_object* v_val_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1897_; 
v_val_1889_ = lean_ctor_get(v_val_1888_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_val_1888_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1891_ = v_val_1888_;
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_val_1889_);
lean_dec(v_val_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v_snd_1893_; lean_object* v___x_1895_; 
v_snd_1893_ = lean_ctor_get(v_val_1889_, 1);
lean_inc(v_snd_1893_);
lean_dec(v_val_1889_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v_snd_1893_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_snd_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f___boxed(lean_object* v_query_1898_, lean_object* v_key_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1898_, v_key_1899_);
lean_dec_ref(v_key_1899_);
lean_dec_ref(v_query_1898_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f(lean_object* v_query_1901_, lean_object* v_key_1902_){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1902_);
v___x_1904_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1901_, v___x_1903_);
lean_dec_ref(v___x_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f___boxed(lean_object* v_query_1905_, lean_object* v_key_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Std_Http_URI_Query_find_x3f(v_query_1905_, v_key_1906_);
lean_dec_ref(v_key_1906_);
lean_dec_ref(v_query_1905_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(lean_object* v_key_1908_, lean_object* v_as_1909_, size_t v_i_1910_, size_t v_stop_1911_, lean_object* v_b_1912_){
_start:
{
lean_object* v___y_1914_; uint8_t v___x_1918_; 
v___x_1918_ = lean_usize_dec_eq(v_i_1910_, v_stop_1911_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; lean_object* v_fst_1920_; lean_object* v_snd_1921_; uint8_t v___x_1922_; 
v___x_1919_ = lean_array_uget_borrowed(v_as_1909_, v_i_1910_);
v_fst_1920_ = lean_ctor_get(v___x_1919_, 0);
v_snd_1921_ = lean_ctor_get(v___x_1919_, 1);
v___x_1922_ = lean_sarray_dec_eq(v_fst_1920_, v_key_1908_);
if (v___x_1922_ == 0)
{
v___y_1914_ = v_b_1912_;
goto v___jp_1913_;
}
else
{
lean_object* v___x_1923_; 
lean_inc(v_snd_1921_);
v___x_1923_ = lean_array_push(v_b_1912_, v_snd_1921_);
v___y_1914_ = v___x_1923_;
goto v___jp_1913_;
}
}
else
{
return v_b_1912_;
}
v___jp_1913_:
{
size_t v___x_1915_; size_t v___x_1916_; 
v___x_1915_ = ((size_t)1ULL);
v___x_1916_ = lean_usize_add(v_i_1910_, v___x_1915_);
v_i_1910_ = v___x_1916_;
v_b_1912_ = v___y_1914_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0___boxed(lean_object* v_key_1924_, lean_object* v_as_1925_, lean_object* v_i_1926_, lean_object* v_stop_1927_, lean_object* v_b_1928_){
_start:
{
size_t v_i_boxed_1929_; size_t v_stop_boxed_1930_; lean_object* v_res_1931_; 
v_i_boxed_1929_ = lean_unbox_usize(v_i_1926_);
lean_dec(v_i_1926_);
v_stop_boxed_1930_ = lean_unbox_usize(v_stop_1927_);
lean_dec(v_stop_1927_);
v_res_1931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1924_, v_as_1925_, v_i_boxed_1929_, v_stop_boxed_1930_, v_b_1928_);
lean_dec_ref(v_as_1925_);
lean_dec_ref(v_key_1924_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(lean_object* v_key_1934_, lean_object* v_as_1935_, lean_object* v_start_1936_, lean_object* v_stop_1937_){
_start:
{
lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_1939_ = lean_nat_dec_lt(v_start_1936_, v_stop_1937_);
if (v___x_1939_ == 0)
{
return v___x_1938_;
}
else
{
lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1940_ = lean_array_get_size(v_as_1935_);
v___x_1941_ = lean_nat_dec_le(v_stop_1937_, v___x_1940_);
if (v___x_1941_ == 0)
{
uint8_t v___x_1942_; 
v___x_1942_ = lean_nat_dec_lt(v_start_1936_, v___x_1940_);
if (v___x_1942_ == 0)
{
return v___x_1938_;
}
else
{
size_t v___x_1943_; size_t v___x_1944_; lean_object* v___x_1945_; 
v___x_1943_ = lean_usize_of_nat(v_start_1936_);
v___x_1944_ = lean_usize_of_nat(v___x_1940_);
v___x_1945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1934_, v_as_1935_, v___x_1943_, v___x_1944_, v___x_1938_);
return v___x_1945_;
}
}
else
{
size_t v___x_1946_; size_t v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = lean_usize_of_nat(v_start_1936_);
v___x_1947_ = lean_usize_of_nat(v_stop_1937_);
v___x_1948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1934_, v_as_1935_, v___x_1946_, v___x_1947_, v___x_1938_);
return v___x_1948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___boxed(lean_object* v_key_1949_, lean_object* v_as_1950_, lean_object* v_start_1951_, lean_object* v_stop_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1949_, v_as_1950_, v_start_1951_, v_stop_1952_);
lean_dec(v_stop_1952_);
lean_dec(v_start_1951_);
lean_dec_ref(v_as_1950_);
lean_dec_ref(v_key_1949_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded(lean_object* v_query_1954_, lean_object* v_key_1955_){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1956_ = lean_unsigned_to_nat(0u);
v___x_1957_ = lean_array_get_size(v_query_1954_);
v___x_1958_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1955_, v_query_1954_, v___x_1956_, v___x_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded___boxed(lean_object* v_query_1959_, lean_object* v_key_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1959_, v_key_1960_);
lean_dec_ref(v_key_1960_);
lean_dec_ref(v_query_1959_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll(lean_object* v_query_1962_, lean_object* v_key_1963_){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1963_);
v___x_1965_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1962_, v___x_1964_);
lean_dec_ref(v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll___boxed(lean_object* v_query_1966_, lean_object* v_key_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Std_Http_URI_Query_findAll(v_query_1966_, v_key_1967_);
lean_dec_ref(v_key_1967_);
lean_dec_ref(v_query_1966_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert(lean_object* v_query_1969_, lean_object* v_key_1970_, lean_object* v_value_1971_){
_start:
{
lean_object* v_encodedKey_1972_; lean_object* v_encodedValue_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v_encodedKey_1972_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1970_);
v_encodedValue_1973_ = l_Std_Http_URI_EncodedQueryParam_encode(v_value_1971_);
v___x_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1974_, 0, v_encodedValue_1973_);
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v_encodedKey_1972_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = lean_array_push(v_query_1969_, v___x_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert___boxed(lean_object* v_query_1977_, lean_object* v_key_1978_, lean_object* v_value_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Std_Http_URI_Query_insert(v_query_1977_, v_key_1978_, v_value_1979_);
lean_dec_ref(v_value_1979_);
lean_dec_ref(v_key_1978_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object* v_query_1981_, lean_object* v_key_1982_, lean_object* v_value_1983_){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v_key_1982_);
lean_ctor_set(v___x_1984_, 1, v_value_1983_);
v___x_1985_ = lean_array_push(v_query_1981_, v___x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_ofList(lean_object* v_pairs_1989_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = lean_array_mk(v_pairs_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(lean_object* v_key_1991_, lean_object* v_as_1992_, size_t v_i_1993_, size_t v_stop_1994_){
_start:
{
uint8_t v___x_1995_; 
v___x_1995_ = lean_usize_dec_eq(v_i_1993_, v_stop_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; lean_object* v_fst_1997_; uint8_t v___x_1998_; 
v___x_1996_ = lean_array_uget_borrowed(v_as_1992_, v_i_1993_);
v_fst_1997_ = lean_ctor_get(v___x_1996_, 0);
v___x_1998_ = lean_sarray_dec_eq(v_fst_1997_, v_key_1991_);
if (v___x_1998_ == 0)
{
size_t v___x_1999_; size_t v___x_2000_; 
v___x_1999_ = ((size_t)1ULL);
v___x_2000_ = lean_usize_add(v_i_1993_, v___x_1999_);
v_i_1993_ = v___x_2000_;
goto _start;
}
else
{
return v___x_1998_;
}
}
else
{
uint8_t v___x_2002_; 
v___x_2002_ = 0;
return v___x_2002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(lean_object* v_key_2003_, lean_object* v_as_2004_, lean_object* v_i_2005_, lean_object* v_stop_2006_){
_start:
{
size_t v_i_boxed_2007_; size_t v_stop_boxed_2008_; uint8_t v_res_2009_; lean_object* v_r_2010_; 
v_i_boxed_2007_ = lean_unbox_usize(v_i_2005_);
lean_dec(v_i_2005_);
v_stop_boxed_2008_ = lean_unbox_usize(v_stop_2006_);
lean_dec(v_stop_2006_);
v_res_2009_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_2003_, v_as_2004_, v_i_boxed_2007_, v_stop_boxed_2008_);
lean_dec_ref(v_as_2004_);
lean_dec_ref(v_key_2003_);
v_r_2010_ = lean_box(v_res_2009_);
return v_r_2010_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_containsEncoded(lean_object* v_query_2011_, lean_object* v_key_2012_){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_2013_ = lean_unsigned_to_nat(0u);
v___x_2014_ = lean_array_get_size(v_query_2011_);
v___x_2015_ = lean_nat_dec_lt(v___x_2013_, v___x_2014_);
if (v___x_2015_ == 0)
{
return v___x_2015_;
}
else
{
if (v___x_2015_ == 0)
{
return v___x_2015_;
}
else
{
size_t v___x_2016_; size_t v___x_2017_; uint8_t v___x_2018_; 
v___x_2016_ = ((size_t)0ULL);
v___x_2017_ = lean_usize_of_nat(v___x_2014_);
v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_2012_, v_query_2011_, v___x_2016_, v___x_2017_);
return v___x_2018_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_containsEncoded___boxed(lean_object* v_query_2019_, lean_object* v_key_2020_){
_start:
{
uint8_t v_res_2021_; lean_object* v_r_2022_; 
v_res_2021_ = l_Std_Http_URI_Query_containsEncoded(v_query_2019_, v_key_2020_);
lean_dec_ref(v_key_2020_);
lean_dec_ref(v_query_2019_);
v_r_2022_ = lean_box(v_res_2021_);
return v_r_2022_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_contains(lean_object* v_query_2023_, lean_object* v_key_2024_){
_start:
{
lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_2024_);
v___x_2026_ = l_Std_Http_URI_Query_containsEncoded(v_query_2023_, v___x_2025_);
lean_dec_ref(v___x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_contains___boxed(lean_object* v_query_2027_, lean_object* v_key_2028_){
_start:
{
uint8_t v_res_2029_; lean_object* v_r_2030_; 
v_res_2029_ = l_Std_Http_URI_Query_contains(v_query_2027_, v_key_2028_);
lean_dec_ref(v_key_2028_);
lean_dec_ref(v_query_2027_);
v_r_2030_ = lean_box(v_res_2029_);
return v_r_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(lean_object* v_key_2031_, lean_object* v_as_2032_, size_t v_i_2033_, size_t v_stop_2034_, lean_object* v_b_2035_){
_start:
{
lean_object* v___y_2037_; uint8_t v___x_2041_; 
v___x_2041_ = lean_usize_dec_eq(v_i_2033_, v_stop_2034_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; lean_object* v_fst_2045_; uint8_t v___x_2046_; 
v___x_2042_ = lean_array_uget_borrowed(v_as_2032_, v_i_2033_);
v_fst_2045_ = lean_ctor_get(v___x_2042_, 0);
v___x_2046_ = lean_sarray_dec_eq(v_fst_2045_, v_key_2031_);
if (v___x_2046_ == 0)
{
goto v___jp_2043_;
}
else
{
if (v___x_2041_ == 0)
{
v___y_2037_ = v_b_2035_;
goto v___jp_2036_;
}
else
{
goto v___jp_2043_;
}
}
v___jp_2043_:
{
lean_object* v___x_2044_; 
lean_inc(v___x_2042_);
v___x_2044_ = lean_array_push(v_b_2035_, v___x_2042_);
v___y_2037_ = v___x_2044_;
goto v___jp_2036_;
}
}
else
{
return v_b_2035_;
}
v___jp_2036_:
{
size_t v___x_2038_; size_t v___x_2039_; 
v___x_2038_ = ((size_t)1ULL);
v___x_2039_ = lean_usize_add(v_i_2033_, v___x_2038_);
v_i_2033_ = v___x_2039_;
v_b_2035_ = v___y_2037_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(lean_object* v_key_2047_, lean_object* v_as_2048_, lean_object* v_i_2049_, lean_object* v_stop_2050_, lean_object* v_b_2051_){
_start:
{
size_t v_i_boxed_2052_; size_t v_stop_boxed_2053_; lean_object* v_res_2054_; 
v_i_boxed_2052_ = lean_unbox_usize(v_i_2049_);
lean_dec(v_i_2049_);
v_stop_boxed_2053_ = lean_unbox_usize(v_stop_2050_);
lean_dec(v_stop_2050_);
v_res_2054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2047_, v_as_2048_, v_i_boxed_2052_, v_stop_boxed_2053_, v_b_2051_);
lean_dec_ref(v_as_2048_);
lean_dec_ref(v_key_2047_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded(lean_object* v_query_2055_, lean_object* v_key_2056_){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2057_ = lean_unsigned_to_nat(0u);
v___x_2058_ = lean_array_get_size(v_query_2055_);
v___x_2059_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_2060_ = lean_nat_dec_lt(v___x_2057_, v___x_2058_);
if (v___x_2060_ == 0)
{
return v___x_2059_;
}
else
{
uint8_t v___x_2061_; 
v___x_2061_ = lean_nat_dec_le(v___x_2058_, v___x_2058_);
if (v___x_2061_ == 0)
{
if (v___x_2060_ == 0)
{
return v___x_2059_;
}
else
{
size_t v___x_2062_; size_t v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = ((size_t)0ULL);
v___x_2063_ = lean_usize_of_nat(v___x_2058_);
v___x_2064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2056_, v_query_2055_, v___x_2062_, v___x_2063_, v___x_2059_);
return v___x_2064_;
}
}
else
{
size_t v___x_2065_; size_t v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = ((size_t)0ULL);
v___x_2066_ = lean_usize_of_nat(v___x_2058_);
v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2056_, v_query_2055_, v___x_2065_, v___x_2066_, v___x_2059_);
return v___x_2067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded___boxed(lean_object* v_query_2068_, lean_object* v_key_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Std_Http_URI_Query_eraseEncoded(v_query_2068_, v_key_2069_);
lean_dec_ref(v_key_2069_);
lean_dec_ref(v_query_2068_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase(lean_object* v_query_2071_, lean_object* v_key_2072_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_2072_);
v___x_2074_ = l_Std_Http_URI_Query_eraseEncoded(v_query_2071_, v___x_2073_);
lean_dec_ref(v___x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase___boxed(lean_object* v_query_2075_, lean_object* v_key_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Std_Http_URI_Query_erase(v_query_2075_, v_key_2076_);
lean_dec_ref(v_key_2076_);
lean_dec_ref(v_query_2075_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get(lean_object* v_query_2080_, lean_object* v_key_2081_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l_Std_Http_URI_Query_find_x3f(v_query_2080_, v_key_2081_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v___x_2083_; 
v___x_2083_ = lean_box(0);
return v___x_2083_;
}
else
{
lean_object* v_val_2084_; 
v_val_2084_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_val_2084_);
lean_dec_ref_known(v___x_2082_, 1);
if (lean_obj_tag(v_val_2084_) == 0)
{
lean_object* v___x_2085_; 
v___x_2085_ = ((lean_object*)(l_Std_Http_URI_Query_get___closed__0));
return v___x_2085_;
}
else
{
lean_object* v_val_2086_; lean_object* v___x_2087_; 
v_val_2086_ = lean_ctor_get(v_val_2084_, 0);
lean_inc(v_val_2086_);
lean_dec_ref_known(v_val_2084_, 1);
v___x_2087_ = l_Std_Http_URI_EncodedQueryParam_decode(v_val_2086_);
lean_dec(v_val_2086_);
return v___x_2087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get___boxed(lean_object* v_query_2088_, lean_object* v_key_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Std_Http_URI_Query_get(v_query_2088_, v_key_2089_);
lean_dec_ref(v_key_2089_);
lean_dec_ref(v_query_2088_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD(lean_object* v_query_2091_, lean_object* v_key_2092_, lean_object* v_default_2093_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Std_Http_URI_Query_get(v_query_2091_, v_key_2092_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_inc_ref(v_default_2093_);
return v_default_2093_;
}
else
{
lean_object* v_val_2095_; 
v_val_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_val_2095_);
lean_dec_ref_known(v___x_2094_, 1);
return v_val_2095_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD___boxed(lean_object* v_query_2096_, lean_object* v_key_2097_, lean_object* v_default_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Std_Http_URI_Query_getD(v_query_2096_, v_key_2097_, v_default_2098_);
lean_dec_ref(v_default_2098_);
lean_dec_ref(v_key_2097_);
lean_dec_ref(v_query_2096_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set(lean_object* v_query_2100_, lean_object* v_key_2101_, lean_object* v_value_2102_){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = l_Std_Http_URI_Query_erase(v_query_2100_, v_key_2101_);
v___x_2104_ = l_Std_Http_URI_Query_insert(v___x_2103_, v_key_2101_, v_value_2102_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set___boxed(lean_object* v_query_2105_, lean_object* v_key_2106_, lean_object* v_value_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Std_Http_URI_Query_set(v_query_2105_, v_key_2106_, v_value_2107_);
lean_dec_ref(v_value_2107_);
lean_dec_ref(v_key_2106_);
lean_dec_ref(v_query_2105_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(size_t v_sz_2109_, size_t v_i_2110_, lean_object* v_bs_2111_){
_start:
{
uint8_t v___x_2112_; 
v___x_2112_ = lean_usize_dec_lt(v_i_2110_, v_sz_2109_);
if (v___x_2112_ == 0)
{
return v_bs_2111_;
}
else
{
lean_object* v_v_2113_; lean_object* v_fst_2114_; lean_object* v_snd_2115_; lean_object* v___x_2116_; lean_object* v_bs_x27_2117_; lean_object* v___x_2118_; size_t v___x_2119_; size_t v___x_2120_; lean_object* v___x_2121_; 
v_v_2113_ = lean_array_uget_borrowed(v_bs_2111_, v_i_2110_);
v_fst_2114_ = lean_ctor_get(v_v_2113_, 0);
lean_inc(v_fst_2114_);
v_snd_2115_ = lean_ctor_get(v_v_2113_, 1);
lean_inc(v_snd_2115_);
v___x_2116_ = lean_unsigned_to_nat(0u);
v_bs_x27_2117_ = lean_array_uset(v_bs_2111_, v_i_2110_, v___x_2116_);
v___x_2118_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2114_, v_snd_2115_);
v___x_2119_ = ((size_t)1ULL);
v___x_2120_ = lean_usize_add(v_i_2110_, v___x_2119_);
v___x_2121_ = lean_array_uset(v_bs_x27_2117_, v_i_2110_, v___x_2118_);
v_i_2110_ = v___x_2120_;
v_bs_2111_ = v___x_2121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0___boxed(lean_object* v_sz_2123_, lean_object* v_i_2124_, lean_object* v_bs_2125_){
_start:
{
size_t v_sz_boxed_2126_; size_t v_i_boxed_2127_; lean_object* v_res_2128_; 
v_sz_boxed_2126_ = lean_unbox_usize(v_sz_2123_);
lean_dec(v_sz_2123_);
v_i_boxed_2127_ = lean_unbox_usize(v_i_2124_);
lean_dec(v_i_2124_);
v_res_2128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_boxed_2126_, v_i_boxed_2127_, v_bs_2125_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toRawString(lean_object* v_query_2130_){
_start:
{
size_t v_sz_2131_; size_t v___x_2132_; lean_object* v_params_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v_sz_2131_ = lean_array_size(v_query_2130_);
v___x_2132_ = ((size_t)0ULL);
v_params_2133_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_2131_, v___x_2132_, v_query_2130_);
v___x_2134_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2135_ = lean_array_to_list(v_params_2133_);
v___x_2136_ = l_String_intercalate(v___x_2134_, v___x_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0(lean_object* v_x_2138_){
_start:
{
lean_object* v_fst_2139_; lean_object* v_snd_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v_fst_2139_ = lean_ctor_get(v_x_2138_, 0);
v_snd_2140_ = lean_ctor_get(v_x_2138_, 1);
v___x_2141_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
v___x_2142_ = l_Std_Http_URI_Query_insert(v___x_2141_, v_fst_2139_, v_snd_2140_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0___boxed(lean_object* v_x_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Std_Http_URI_Query_instSingletonProdString___lam__0(v_x_2143_);
lean_dec_ref(v_x_2143_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0(lean_object* v_x_2147_, lean_object* v_q_2148_){
_start:
{
lean_object* v_fst_2149_; lean_object* v_snd_2150_; lean_object* v___x_2151_; 
v_fst_2149_ = lean_ctor_get(v_x_2147_, 0);
v_snd_2150_ = lean_ctor_get(v_x_2147_, 1);
v___x_2151_ = l_Std_Http_URI_Query_insert(v_q_2148_, v_fst_2149_, v_snd_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0___boxed(lean_object* v_x_2152_, lean_object* v_q_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Std_Http_URI_Query_instInsertProdString___lam__0(v_x_2152_, v_q_2153_);
lean_dec_ref(v_x_2152_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__0(lean_object* v_x_2157_){
_start:
{
lean_object* v_fst_2158_; lean_object* v_snd_2159_; lean_object* v___x_2160_; 
v_fst_2158_ = lean_ctor_get(v_x_2157_, 0);
lean_inc(v_fst_2158_);
v_snd_2159_ = lean_ctor_get(v_x_2157_, 1);
lean_inc(v_snd_2159_);
lean_dec_ref(v_x_2157_);
v___x_2160_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2158_, v_snd_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__1(lean_object* v___f_2162_, lean_object* v_q_2163_){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2164_ = lean_array_get_size(v_q_2163_);
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = lean_nat_dec_eq(v___x_2164_, v___x_2165_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v_encodedParams_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2167_ = lean_array_to_list(v_q_2163_);
v___x_2168_ = lean_box(0);
v_encodedParams_2169_ = l_List_mapTR_loop___redArg(v___f_2162_, v___x_2167_, v___x_2168_);
v___x_2170_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2171_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2172_ = l_String_intercalate(v___x_2171_, v_encodedParams_2169_);
v___x_2173_ = lean_string_append(v___x_2170_, v___x_2172_);
lean_dec_ref(v___x_2172_);
return v___x_2173_;
}
else
{
lean_object* v___x_2174_; 
lean_dec_ref(v_q_2163_);
lean_dec_ref(v___f_2162_);
v___x_2174_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2174_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
if (lean_obj_tag(v_a_2179_) == 0)
{
lean_object* v___x_2181_; 
v___x_2181_ = l_List_reverse___redArg(v_a_2180_);
return v___x_2181_;
}
else
{
lean_object* v_head_2182_; lean_object* v_tail_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2194_; 
v_head_2182_ = lean_ctor_get(v_a_2179_, 0);
v_tail_2183_ = lean_ctor_get(v_a_2179_, 1);
v_isSharedCheck_2194_ = !lean_is_exclusive(v_a_2179_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2185_ = v_a_2179_;
v_isShared_2186_ = v_isSharedCheck_2194_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_tail_2183_);
lean_inc(v_head_2182_);
lean_dec(v_a_2179_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2194_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v_fst_2187_; lean_object* v_snd_2188_; lean_object* v___x_2189_; lean_object* v___x_2191_; 
v_fst_2187_ = lean_ctor_get(v_head_2182_, 0);
lean_inc(v_fst_2187_);
v_snd_2188_ = lean_ctor_get(v_head_2182_, 1);
lean_inc(v_snd_2188_);
lean_dec(v_head_2182_);
v___x_2189_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2187_, v_snd_2188_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 1, v_a_2180_);
lean_ctor_set(v___x_2185_, 0, v___x_2189_);
v___x_2191_ = v___x_2185_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_a_2180_);
v___x_2191_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
v_a_2179_ = v_tail_2183_;
v_a_2180_ = v___x_2191_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatOption(lean_object* v_x_2195_){
_start:
{
if (lean_obj_tag(v_x_2195_) == 0)
{
lean_object* v___x_2196_; 
v___x_2196_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2196_;
}
else
{
lean_object* v_val_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v_val_2197_ = lean_ctor_get(v_x_2195_, 0);
lean_inc(v_val_2197_);
lean_dec_ref_known(v_x_2195_, 1);
v___x_2198_ = lean_array_get_size(v_val_2197_);
v___x_2199_ = lean_unsigned_to_nat(0u);
v___x_2200_ = lean_nat_dec_eq(v___x_2198_, v___x_2199_);
if (v___x_2200_ == 0)
{
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v_encodedParams_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2201_ = lean_array_to_list(v_val_2197_);
v___x_2202_ = lean_box(0);
v_encodedParams_2203_ = l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(v___x_2201_, v___x_2202_);
v___x_2204_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2205_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2206_ = l_String_intercalate(v___x_2205_, v_encodedParams_2203_);
v___x_2207_ = lean_string_append(v___x_2204_, v___x_2206_);
lean_dec_ref(v___x_2206_);
return v___x_2207_;
}
else
{
lean_object* v___x_2208_; 
lean_dec(v_val_2197_);
v___x_2208_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2208_;
}
}
else
{
lean_object* v___x_2209_; 
lean_dec(v_val_2197_);
v___x_2209_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
return v___x_2209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(lean_object* v_x_2210_, lean_object* v_x_2211_){
_start:
{
if (lean_obj_tag(v_x_2210_) == 0)
{
lean_object* v___x_2212_; 
v___x_2212_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2212_;
}
else
{
lean_object* v_val_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v_val_2213_ = lean_ctor_get(v_x_2210_, 0);
lean_inc(v_val_2213_);
lean_dec_ref_known(v_x_2210_, 1);
v___x_2214_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2215_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_val_2213_);
v___x_2216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2214_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = l_Repr_addAppParen(v___x_2216_, v_x_2211_);
return v___x_2217_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(lean_object* v_x_2218_, lean_object* v_x_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_x_2218_, v_x_2219_);
lean_dec(v_x_2219_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object* v_x_2221_, lean_object* v_x_2222_){
_start:
{
if (lean_obj_tag(v_x_2221_) == 0)
{
lean_object* v___x_2223_; 
v___x_2223_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2223_;
}
else
{
lean_object* v_val_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v_val_2224_ = lean_ctor_get(v_x_2221_, 0);
lean_inc(v_val_2224_);
lean_dec_ref_known(v_x_2221_, 1);
v___x_2225_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2226_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_val_2224_);
v___x_2227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2225_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
v___x_2228_ = l_Repr_addAppParen(v___x_2227_, v_x_2222_);
return v___x_2228_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1___boxed(lean_object* v_x_2229_, lean_object* v_x_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_x_2229_, v_x_2230_);
lean_dec(v_x_2230_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(lean_object* v_x_2232_, lean_object* v_x_2233_){
_start:
{
if (lean_obj_tag(v_x_2232_) == 0)
{
lean_object* v___x_2234_; 
v___x_2234_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2234_;
}
else
{
lean_object* v_val_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2246_; 
v_val_2235_ = lean_ctor_get(v_x_2232_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_x_2232_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2237_ = v_x_2232_;
v_isShared_2238_ = v_isSharedCheck_2246_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_val_2235_);
lean_dec(v_x_2232_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2246_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2239_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2240_ = l_String_quote(v_val_2235_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set_tag(v___x_2237_, 3);
lean_ctor_set(v___x_2237_, 0, v___x_2240_);
v___x_2242_ = v___x_2237_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2239_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = l_Repr_addAppParen(v___x_2243_, v_x_2233_);
return v___x_2244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2___boxed(lean_object* v_x_2247_, lean_object* v_x_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_x_2247_, v_x_2248_);
lean_dec(v_x_2248_);
return v_res_2249_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = lean_unsigned_to_nat(10u);
v___x_2260_ = lean_nat_to_int(v___x_2259_);
return v___x_2260_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = lean_unsigned_to_nat(13u);
v___x_2265_ = lean_nat_to_int(v___x_2264_);
return v___x_2265_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = lean_unsigned_to_nat(9u);
v___x_2273_ = lean_nat_to_int(v___x_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___redArg(lean_object* v_x_2277_){
_start:
{
lean_object* v_scheme_2278_; lean_object* v_authority_2279_; lean_object* v_path_2280_; lean_object* v_query_2281_; lean_object* v_fragment_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v_scheme_2278_ = lean_ctor_get(v_x_2277_, 0);
lean_inc_ref(v_scheme_2278_);
v_authority_2279_ = lean_ctor_get(v_x_2277_, 1);
lean_inc(v_authority_2279_);
v_path_2280_ = lean_ctor_get(v_x_2277_, 2);
lean_inc_ref(v_path_2280_);
v_query_2281_ = lean_ctor_get(v_x_2277_, 3);
lean_inc(v_query_2281_);
v_fragment_2282_ = lean_ctor_get(v_x_2277_, 4);
lean_inc(v_fragment_2282_);
lean_dec_ref(v_x_2277_);
v___x_2283_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2284_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2285_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2286_ = l_String_quote(v_scheme_2278_);
v___x_2287_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
v___x_2288_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2285_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = 0;
v___x_2290_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2290_, 0, v___x_2288_);
lean_ctor_set_uint8(v___x_2290_, sizeof(void*)*1, v___x_2289_);
v___x_2291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2284_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = lean_box(1);
v___x_2295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2293_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
v___x_2296_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__6));
v___x_2297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2295_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v___x_2283_);
v___x_2299_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_2300_ = lean_unsigned_to_nat(0u);
v___x_2301_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_2279_, v___x_2300_);
v___x_2302_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2299_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
v___x_2303_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set_uint8(v___x_2303_, sizeof(void*)*1, v___x_2289_);
v___x_2304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2298_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
lean_ctor_set(v___x_2305_, 1, v___x_2292_);
v___x_2306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
lean_ctor_set(v___x_2306_, 1, v___x_2294_);
v___x_2307_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_2308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2306_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
v___x_2309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
lean_ctor_set(v___x_2309_, 1, v___x_2283_);
v___x_2310_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2311_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_2280_);
v___x_2312_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
lean_ctor_set_uint8(v___x_2313_, sizeof(void*)*1, v___x_2289_);
v___x_2314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2309_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
lean_ctor_set(v___x_2315_, 1, v___x_2292_);
v___x_2316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
lean_ctor_set(v___x_2316_, 1, v___x_2294_);
v___x_2317_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_2318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
lean_ctor_set(v___x_2319_, 1, v___x_2283_);
v___x_2320_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_2321_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_2281_, v___x_2300_);
v___x_2322_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
lean_ctor_set_uint8(v___x_2323_, sizeof(void*)*1, v___x_2289_);
v___x_2324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2319_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
v___x_2325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
lean_ctor_set(v___x_2325_, 1, v___x_2292_);
v___x_2326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
lean_ctor_set(v___x_2326_, 1, v___x_2294_);
v___x_2327_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_2328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2326_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
lean_ctor_set(v___x_2329_, 1, v___x_2283_);
v___x_2330_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_2331_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_2282_, v___x_2300_);
v___x_2332_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*1, v___x_2289_);
v___x_2334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2329_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2336_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2337_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set(v___x_2337_, 1, v___x_2334_);
v___x_2338_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2337_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
v___x_2340_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2335_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*1, v___x_2289_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr(lean_object* v_x_2342_, lean_object* v_prec_2343_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Std_Http_instReprURI_repr___redArg(v_x_2342_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___boxed(lean_object* v_x_2345_, lean_object* v_prec_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Std_Http_instReprURI_repr(v_x_2345_, v_prec_2346_);
lean_dec(v_prec_2346_);
return v_res_2347_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object* v_x_2356_, lean_object* v_x_2357_){
_start:
{
if (lean_obj_tag(v_x_2356_) == 0)
{
if (lean_obj_tag(v_x_2357_) == 0)
{
uint8_t v___x_2358_; 
v___x_2358_ = 1;
return v___x_2358_;
}
else
{
uint8_t v___x_2359_; 
v___x_2359_ = 0;
return v___x_2359_;
}
}
else
{
if (lean_obj_tag(v_x_2357_) == 0)
{
uint8_t v___x_2360_; 
v___x_2360_ = 0;
return v___x_2360_;
}
else
{
lean_object* v_val_2361_; lean_object* v_val_2362_; uint8_t v___x_2363_; 
v_val_2361_ = lean_ctor_get(v_x_2356_, 0);
v_val_2362_ = lean_ctor_get(v_x_2357_, 0);
v___x_2363_ = l_Std_Http_URI_instBEqAuthority_beq(v_val_2361_, v_val_2362_);
return v___x_2363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object* v_x_2364_, lean_object* v_x_2365_){
_start:
{
uint8_t v_res_2366_; lean_object* v_r_2367_; 
v_res_2366_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_x_2364_, v_x_2365_);
lean_dec(v_x_2365_);
lean_dec(v_x_2364_);
v_r_2367_ = lean_box(v_res_2366_);
return v_r_2367_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object* v_x_2368_, lean_object* v_x_2369_){
_start:
{
if (lean_obj_tag(v_x_2368_) == 0)
{
if (lean_obj_tag(v_x_2369_) == 0)
{
uint8_t v___x_2370_; 
v___x_2370_ = 1;
return v___x_2370_;
}
else
{
uint8_t v___x_2371_; 
v___x_2371_ = 0;
return v___x_2371_;
}
}
else
{
if (lean_obj_tag(v_x_2369_) == 0)
{
uint8_t v___x_2372_; 
v___x_2372_ = 0;
return v___x_2372_;
}
else
{
lean_object* v_val_2373_; lean_object* v_val_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; uint8_t v___x_2377_; 
v_val_2373_ = lean_ctor_get(v_x_2368_, 0);
v_val_2374_ = lean_ctor_get(v_x_2369_, 0);
v___x_2375_ = lean_array_get_size(v_val_2373_);
v___x_2376_ = lean_array_get_size(v_val_2374_);
v___x_2377_ = lean_nat_dec_eq(v___x_2375_, v___x_2376_);
if (v___x_2377_ == 0)
{
return v___x_2377_;
}
else
{
uint8_t v___x_2378_; 
v___x_2378_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_val_2373_, v_val_2374_, v___x_2375_);
return v___x_2378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object* v_x_2379_, lean_object* v_x_2380_){
_start:
{
uint8_t v_res_2381_; lean_object* v_r_2382_; 
v_res_2381_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_x_2379_, v_x_2380_);
lean_dec(v_x_2380_);
lean_dec(v_x_2379_);
v_r_2382_ = lean_box(v_res_2381_);
return v_r_2382_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2(lean_object* v_x_2383_, lean_object* v_x_2384_){
_start:
{
if (lean_obj_tag(v_x_2383_) == 0)
{
if (lean_obj_tag(v_x_2384_) == 0)
{
uint8_t v___x_2385_; 
v___x_2385_ = 1;
return v___x_2385_;
}
else
{
uint8_t v___x_2386_; 
v___x_2386_ = 0;
return v___x_2386_;
}
}
else
{
if (lean_obj_tag(v_x_2384_) == 0)
{
uint8_t v___x_2387_; 
v___x_2387_ = 0;
return v___x_2387_;
}
else
{
lean_object* v_val_2388_; lean_object* v_val_2389_; uint8_t v___x_2390_; 
v_val_2388_ = lean_ctor_get(v_x_2383_, 0);
v_val_2389_ = lean_ctor_get(v_x_2384_, 0);
v___x_2390_ = lean_string_dec_eq(v_val_2388_, v_val_2389_);
return v___x_2390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2___boxed(lean_object* v_x_2391_, lean_object* v_x_2392_){
_start:
{
uint8_t v_res_2393_; lean_object* v_r_2394_; 
v_res_2393_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_x_2391_, v_x_2392_);
lean_dec(v_x_2392_);
lean_dec(v_x_2391_);
v_r_2394_ = lean_box(v_res_2393_);
return v_r_2394_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object* v_x_2395_, lean_object* v_x_2396_){
_start:
{
lean_object* v_scheme_2397_; lean_object* v_authority_2398_; lean_object* v_path_2399_; lean_object* v_query_2400_; lean_object* v_fragment_2401_; lean_object* v_scheme_2402_; lean_object* v_authority_2403_; lean_object* v_path_2404_; lean_object* v_query_2405_; lean_object* v_fragment_2406_; uint8_t v___x_2407_; 
v_scheme_2397_ = lean_ctor_get(v_x_2395_, 0);
v_authority_2398_ = lean_ctor_get(v_x_2395_, 1);
v_path_2399_ = lean_ctor_get(v_x_2395_, 2);
v_query_2400_ = lean_ctor_get(v_x_2395_, 3);
v_fragment_2401_ = lean_ctor_get(v_x_2395_, 4);
v_scheme_2402_ = lean_ctor_get(v_x_2396_, 0);
v_authority_2403_ = lean_ctor_get(v_x_2396_, 1);
v_path_2404_ = lean_ctor_get(v_x_2396_, 2);
v_query_2405_ = lean_ctor_get(v_x_2396_, 3);
v_fragment_2406_ = lean_ctor_get(v_x_2396_, 4);
v___x_2407_ = lean_string_dec_eq(v_scheme_2397_, v_scheme_2402_);
if (v___x_2407_ == 0)
{
return v___x_2407_;
}
else
{
uint8_t v___x_2408_; 
v___x_2408_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_2398_, v_authority_2403_);
if (v___x_2408_ == 0)
{
return v___x_2408_;
}
else
{
uint8_t v___x_2409_; 
v___x_2409_ = l_Std_Http_URI_instBEqPath_beq(v_path_2399_, v_path_2404_);
if (v___x_2409_ == 0)
{
return v___x_2409_;
}
else
{
uint8_t v___x_2410_; 
v___x_2410_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_2400_, v_query_2405_);
if (v___x_2410_ == 0)
{
return v___x_2410_;
}
else
{
uint8_t v___x_2411_; 
v___x_2411_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_2401_, v_fragment_2406_);
return v___x_2411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object* v_x_2412_, lean_object* v_x_2413_){
_start:
{
uint8_t v_res_2414_; lean_object* v_r_2415_; 
v_res_2414_ = l_Std_Http_instBEqURI_beq(v_x_2412_, v_x_2413_);
lean_dec_ref(v_x_2413_);
lean_dec_ref(v_x_2412_);
v_r_2415_ = lean_box(v_res_2414_);
return v_r_2415_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__1(lean_object* v___f_2420_, lean_object* v_uri_2421_){
_start:
{
lean_object* v_scheme_2422_; lean_object* v_authority_2423_; lean_object* v_path_2424_; lean_object* v_query_2425_; lean_object* v_fragment_2426_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2449_; 
v_scheme_2422_ = lean_ctor_get(v_uri_2421_, 0);
lean_inc_ref(v_scheme_2422_);
v_authority_2423_ = lean_ctor_get(v_uri_2421_, 1);
lean_inc(v_authority_2423_);
v_path_2424_ = lean_ctor_get(v_uri_2421_, 2);
lean_inc_ref(v_path_2424_);
v_query_2425_ = lean_ctor_get(v_uri_2421_, 3);
lean_inc(v_query_2425_);
v_fragment_2426_ = lean_ctor_get(v_uri_2421_, 4);
lean_inc(v_fragment_2426_);
lean_dec_ref(v_uri_2421_);
if (lean_obj_tag(v_authority_2423_) == 0)
{
lean_object* v___x_2460_; 
v___x_2460_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2449_ = v___x_2460_;
goto v___jp_2448_;
}
else
{
lean_object* v_val_2461_; lean_object* v_userInfo_2462_; lean_object* v_host_2463_; lean_object* v_port_2464_; lean_object* v___x_2465_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2484_; 
v_val_2461_ = lean_ctor_get(v_authority_2423_, 0);
lean_inc(v_val_2461_);
lean_dec_ref_known(v_authority_2423_, 1);
v_userInfo_2462_ = lean_ctor_get(v_val_2461_, 0);
lean_inc(v_userInfo_2462_);
v_host_2463_ = lean_ctor_get(v_val_2461_, 1);
lean_inc_ref(v_host_2463_);
v_port_2464_ = lean_ctor_get(v_val_2461_, 2);
lean_inc(v_port_2464_);
lean_dec(v_val_2461_);
v___x_2465_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_2462_) == 0)
{
lean_object* v___x_2494_; 
v___x_2494_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2484_ = v___x_2494_;
goto v___jp_2483_;
}
else
{
lean_object* v_val_2495_; lean_object* v_password_2496_; 
v_val_2495_ = lean_ctor_get(v_userInfo_2462_, 0);
lean_inc(v_val_2495_);
lean_dec_ref_known(v_userInfo_2462_, 1);
v_password_2496_ = lean_ctor_get(v_val_2495_, 1);
if (lean_obj_tag(v_password_2496_) == 0)
{
lean_object* v_username_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v_username_2497_ = lean_ctor_get(v_val_2495_, 0);
lean_inc_ref(v_username_2497_);
lean_dec(v_val_2495_);
v___x_2498_ = lean_string_from_utf8_unchecked(v_username_2497_);
v___x_2499_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2500_ = lean_string_append(v___x_2498_, v___x_2499_);
v___y_2484_ = v___x_2500_;
goto v___jp_2483_;
}
else
{
lean_object* v_username_2501_; lean_object* v_val_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
lean_inc_ref(v_password_2496_);
v_username_2501_ = lean_ctor_get(v_val_2495_, 0);
lean_inc_ref(v_username_2501_);
lean_dec(v_val_2495_);
v_val_2502_ = lean_ctor_get(v_password_2496_, 0);
lean_inc(v_val_2502_);
lean_dec_ref_known(v_password_2496_, 1);
v___x_2503_ = lean_string_from_utf8_unchecked(v_username_2501_);
v___x_2504_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2505_ = lean_string_append(v___x_2503_, v___x_2504_);
v___x_2506_ = lean_string_from_utf8_unchecked(v_val_2502_);
v___x_2507_ = lean_string_append(v___x_2505_, v___x_2506_);
lean_dec_ref(v___x_2506_);
v___x_2508_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2509_ = lean_string_append(v___x_2507_, v___x_2508_);
v___y_2484_ = v___x_2509_;
goto v___jp_2483_;
}
}
v___jp_2466_:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = lean_string_append(v___y_2467_, v___y_2468_);
lean_dec_ref(v___y_2468_);
v___x_2471_ = lean_string_append(v___x_2470_, v___y_2469_);
lean_dec_ref(v___y_2469_);
v___x_2472_ = lean_string_append(v___x_2465_, v___x_2471_);
lean_dec_ref(v___x_2471_);
v___y_2449_ = v___x_2472_;
goto v___jp_2448_;
}
v___jp_2473_:
{
switch(lean_obj_tag(v_port_2464_))
{
case 0:
{
lean_object* v___x_2476_; 
v___x_2476_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2467_ = v___y_2474_;
v___y_2468_ = v___y_2475_;
v___y_2469_ = v___x_2476_;
goto v___jp_2466_;
}
case 1:
{
lean_object* v___x_2477_; 
v___x_2477_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_2467_ = v___y_2474_;
v___y_2468_ = v___y_2475_;
v___y_2469_ = v___x_2477_;
goto v___jp_2466_;
}
default: 
{
uint16_t v_port_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v_port_2478_ = lean_ctor_get_uint16(v_port_2464_, 0);
lean_dec_ref_known(v_port_2464_, 0);
v___x_2479_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2480_ = lean_uint16_to_nat(v_port_2478_);
v___x_2481_ = l_Nat_reprFast(v___x_2480_);
v___x_2482_ = lean_string_append(v___x_2479_, v___x_2481_);
lean_dec_ref(v___x_2481_);
v___y_2467_ = v___y_2474_;
v___y_2468_ = v___y_2475_;
v___y_2469_ = v___x_2482_;
goto v___jp_2466_;
}
}
}
v___jp_2483_:
{
switch(lean_obj_tag(v_host_2463_))
{
case 0:
{
lean_object* v_name_2485_; 
v_name_2485_ = lean_ctor_get(v_host_2463_, 0);
lean_inc_ref(v_name_2485_);
lean_dec_ref_known(v_host_2463_, 1);
v___y_2474_ = v___y_2484_;
v___y_2475_ = v_name_2485_;
goto v___jp_2473_;
}
case 1:
{
lean_object* v_ipv4_2486_; lean_object* v___x_2487_; 
v_ipv4_2486_ = lean_ctor_get(v_host_2463_, 0);
lean_inc_ref(v_ipv4_2486_);
lean_dec_ref_known(v_host_2463_, 1);
v___x_2487_ = lean_uv_ntop_v4(v_ipv4_2486_);
lean_dec_ref(v_ipv4_2486_);
v___y_2474_ = v___y_2484_;
v___y_2475_ = v___x_2487_;
goto v___jp_2473_;
}
default: 
{
lean_object* v_ipv6_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v_ipv6_2488_ = lean_ctor_get(v_host_2463_, 0);
lean_inc_ref(v_ipv6_2488_);
lean_dec_ref_known(v_host_2463_, 1);
v___x_2489_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_2490_ = lean_uv_ntop_v6(v_ipv6_2488_);
lean_dec_ref(v_ipv6_2488_);
v___x_2491_ = lean_string_append(v___x_2489_, v___x_2490_);
lean_dec_ref(v___x_2490_);
v___x_2492_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_2493_ = lean_string_append(v___x_2491_, v___x_2492_);
v___y_2474_ = v___y_2484_;
v___y_2475_ = v___x_2493_;
goto v___jp_2473_;
}
}
}
}
v___jp_2427_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2432_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2433_ = lean_string_append(v_scheme_2422_, v___x_2432_);
v___x_2434_ = lean_string_append(v___x_2433_, v___y_2429_);
lean_dec_ref(v___y_2429_);
v___x_2435_ = lean_string_append(v___x_2434_, v___y_2428_);
lean_dec_ref(v___y_2428_);
v___x_2436_ = lean_string_append(v___x_2435_, v___y_2430_);
lean_dec_ref(v___y_2430_);
v___x_2437_ = lean_string_append(v___x_2436_, v___y_2431_);
lean_dec_ref(v___y_2431_);
return v___x_2437_;
}
v___jp_2438_:
{
lean_object* v_queryPart_2441_; 
v_queryPart_2441_ = l_Std_Http_URI_Query_formatOption(v_query_2425_);
if (lean_obj_tag(v_fragment_2426_) == 0)
{
lean_object* v___x_2442_; 
v___x_2442_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2428_ = v___y_2440_;
v___y_2429_ = v___y_2439_;
v___y_2430_ = v_queryPart_2441_;
v___y_2431_ = v___x_2442_;
goto v___jp_2427_;
}
else
{
lean_object* v_val_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v_val_2443_ = lean_ctor_get(v_fragment_2426_, 0);
lean_inc(v_val_2443_);
lean_dec_ref_known(v_fragment_2426_, 1);
v___x_2444_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_2445_ = l_Std_Http_URI_EncodedFragment_encode(v_val_2443_);
lean_dec(v_val_2443_);
v___x_2446_ = lean_string_from_utf8_unchecked(v___x_2445_);
v___x_2447_ = lean_string_append(v___x_2444_, v___x_2446_);
lean_dec_ref(v___x_2446_);
v___y_2428_ = v___y_2440_;
v___y_2429_ = v___y_2439_;
v___y_2430_ = v_queryPart_2441_;
v___y_2431_ = v___x_2447_;
goto v___jp_2427_;
}
}
v___jp_2448_:
{
lean_object* v_segments_2450_; uint8_t v_absolute_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; size_t v_sz_2454_; size_t v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v_result_2458_; 
v_segments_2450_ = lean_ctor_get(v_path_2424_, 0);
lean_inc_ref(v_segments_2450_);
v_absolute_2451_ = lean_ctor_get_uint8(v_path_2424_, sizeof(void*)*1);
lean_dec_ref(v_path_2424_);
v___x_2452_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_2453_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_2454_ = lean_array_size(v_segments_2450_);
v___x_2455_ = ((size_t)0ULL);
v___x_2456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2453_, v___f_2420_, v_sz_2454_, v___x_2455_, v_segments_2450_);
v___x_2457_ = lean_array_to_list(v___x_2456_);
v_result_2458_ = l_String_intercalate(v___x_2452_, v___x_2457_);
if (v_absolute_2451_ == 0)
{
v___y_2439_ = v___y_2449_;
v___y_2440_ = v_result_2458_;
goto v___jp_2438_;
}
else
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_string_append(v___x_2452_, v_result_2458_);
lean_dec_ref(v_result_2458_);
v___y_2439_ = v___y_2449_;
v___y_2440_ = v___x_2459_;
goto v___jp_2438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x3f(lean_object* v_b_2522_, lean_object* v_scheme_2523_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Std_Http_URI_Scheme_ofString_x3f(v_scheme_2523_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v___x_2525_; 
lean_dec_ref(v_b_2522_);
v___x_2525_ = lean_box(0);
return v___x_2525_;
}
else
{
lean_object* v_userInfo_2526_; lean_object* v_host_2527_; lean_object* v_port_2528_; lean_object* v_pathSegments_2529_; lean_object* v_query_2530_; lean_object* v_fragment_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2546_; 
v_userInfo_2526_ = lean_ctor_get(v_b_2522_, 1);
v_host_2527_ = lean_ctor_get(v_b_2522_, 2);
v_port_2528_ = lean_ctor_get(v_b_2522_, 3);
v_pathSegments_2529_ = lean_ctor_get(v_b_2522_, 4);
v_query_2530_ = lean_ctor_get(v_b_2522_, 5);
v_fragment_2531_ = lean_ctor_get(v_b_2522_, 6);
v_isSharedCheck_2546_ = !lean_is_exclusive(v_b_2522_);
if (v_isSharedCheck_2546_ == 0)
{
lean_object* v_unused_2547_; 
v_unused_2547_ = lean_ctor_get(v_b_2522_, 0);
lean_dec(v_unused_2547_);
v___x_2533_ = v_b_2522_;
v_isShared_2534_ = v_isSharedCheck_2546_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_fragment_2531_);
lean_inc(v_query_2530_);
lean_inc(v_pathSegments_2529_);
lean_inc(v_port_2528_);
lean_inc(v_host_2527_);
lean_inc(v_userInfo_2526_);
lean_dec(v_b_2522_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2546_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
lean_inc_ref(v___x_2524_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2524_);
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v_userInfo_2526_);
lean_ctor_set(v_reuseFailAlloc_2545_, 2, v_host_2527_);
lean_ctor_set(v_reuseFailAlloc_2545_, 3, v_port_2528_);
lean_ctor_set(v_reuseFailAlloc_2545_, 4, v_pathSegments_2529_);
lean_ctor_set(v_reuseFailAlloc_2545_, 5, v_query_2530_);
lean_ctor_set(v_reuseFailAlloc_2545_, 6, v_fragment_2531_);
v___x_2536_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; 
v_unused_2544_ = lean_ctor_get(v___x_2524_, 0);
lean_dec(v_unused_2544_);
v___x_2538_ = v___x_2524_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_dec(v___x_2524_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 0, v___x_2536_);
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(lean_object* v_msg_2548_){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = ((lean_object*)(l_Std_Http_URI_instInhabitedBuilder_default));
v___x_2550_ = lean_panic_fn_borrowed(v___x_2549_, v_msg_2548_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x21(lean_object* v_b_2552_, lean_object* v_scheme_2553_){
_start:
{
lean_object* v___x_2554_; 
lean_inc_ref(v_scheme_2553_);
v___x_2554_ = l_Std_Http_URI_Builder_setScheme_x3f(v_b_2552_, v_scheme_2553_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2555_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2556_ = ((lean_object*)(l_Std_Http_URI_Builder_setScheme_x21___closed__0));
v___x_2557_ = lean_unsigned_to_nat(687u);
v___x_2558_ = lean_unsigned_to_nat(14u);
v___x_2559_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_2560_ = l_String_quote(v_scheme_2553_);
v___x_2561_ = lean_string_append(v___x_2559_, v___x_2560_);
lean_dec_ref(v___x_2560_);
v___x_2562_ = l_mkPanicMessageWithDecl(v___x_2555_, v___x_2556_, v___x_2557_, v___x_2558_, v___x_2561_);
lean_dec_ref(v___x_2561_);
v___x_2563_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2562_);
return v___x_2563_;
}
else
{
lean_object* v_val_2564_; 
lean_dec_ref(v_scheme_2553_);
v_val_2564_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_val_2564_);
lean_dec_ref_known(v___x_2554_, 1);
return v_val_2564_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo(lean_object* v_b_2565_, lean_object* v_username_2566_, lean_object* v_password_2567_){
_start:
{
lean_object* v_scheme_2568_; lean_object* v_host_2569_; lean_object* v_port_2570_; lean_object* v_pathSegments_2571_; lean_object* v_query_2572_; lean_object* v_fragment_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2596_; 
v_scheme_2568_ = lean_ctor_get(v_b_2565_, 0);
v_host_2569_ = lean_ctor_get(v_b_2565_, 2);
v_port_2570_ = lean_ctor_get(v_b_2565_, 3);
v_pathSegments_2571_ = lean_ctor_get(v_b_2565_, 4);
v_query_2572_ = lean_ctor_get(v_b_2565_, 5);
v_fragment_2573_ = lean_ctor_get(v_b_2565_, 6);
v_isSharedCheck_2596_ = !lean_is_exclusive(v_b_2565_);
if (v_isSharedCheck_2596_ == 0)
{
lean_object* v_unused_2597_; 
v_unused_2597_ = lean_ctor_get(v_b_2565_, 1);
lean_dec(v_unused_2597_);
v___x_2575_ = v_b_2565_;
v_isShared_2576_ = v_isSharedCheck_2596_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_fragment_2573_);
lean_inc(v_query_2572_);
lean_inc(v_pathSegments_2571_);
lean_inc(v_port_2570_);
lean_inc(v_host_2569_);
lean_inc(v_scheme_2568_);
lean_dec(v_b_2565_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2596_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___y_2578_; lean_object* v___x_2583_; 
v___x_2583_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_2566_);
if (lean_obj_tag(v_password_2567_) == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = lean_box(0);
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2583_);
lean_ctor_set(v___x_2585_, 1, v___x_2584_);
v___y_2578_ = v___x_2585_;
goto v___jp_2577_;
}
else
{
lean_object* v_val_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2595_; 
v_val_2586_ = lean_ctor_get(v_password_2567_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_password_2567_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2588_ = v_password_2567_;
v_isShared_2589_ = v_isSharedCheck_2595_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_val_2586_);
lean_dec(v_password_2567_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2595_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2590_; lean_object* v___x_2592_; 
v___x_2590_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_2586_);
lean_dec(v_val_2586_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2590_);
v___x_2592_ = v___x_2588_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2590_);
v___x_2592_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_object* v___x_2593_; 
v___x_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2583_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
v___y_2578_ = v___x_2593_;
goto v___jp_2577_;
}
}
}
v___jp_2577_:
{
lean_object* v___x_2579_; lean_object* v___x_2581_; 
v___x_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2579_, 0, v___y_2578_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 1, v___x_2579_);
v___x_2581_ = v___x_2575_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_scheme_2568_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v___x_2579_);
lean_ctor_set(v_reuseFailAlloc_2582_, 2, v_host_2569_);
lean_ctor_set(v_reuseFailAlloc_2582_, 3, v_port_2570_);
lean_ctor_set(v_reuseFailAlloc_2582_, 4, v_pathSegments_2571_);
lean_ctor_set(v_reuseFailAlloc_2582_, 5, v_query_2572_);
lean_ctor_set(v_reuseFailAlloc_2582_, 6, v_fragment_2573_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo___boxed(lean_object* v_b_2598_, lean_object* v_username_2599_, lean_object* v_password_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Std_Http_URI_Builder_setUserInfo(v_b_2598_, v_username_2599_, v_password_2600_);
lean_dec_ref(v_username_2599_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x3f(lean_object* v_b_2602_, lean_object* v_name_2603_){
_start:
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Std_Http_URI_DomainName_ofString_x3f(v_name_2603_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v___x_2605_; 
lean_dec_ref(v_b_2602_);
v___x_2605_ = lean_box(0);
return v___x_2605_;
}
else
{
lean_object* v_val_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2629_; 
v_val_2606_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2608_ = v___x_2604_;
v_isShared_2609_ = v_isSharedCheck_2629_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_val_2606_);
lean_dec(v___x_2604_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2629_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v_scheme_2610_; lean_object* v_userInfo_2611_; lean_object* v_port_2612_; lean_object* v_pathSegments_2613_; lean_object* v_query_2614_; lean_object* v_fragment_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2627_; 
v_scheme_2610_ = lean_ctor_get(v_b_2602_, 0);
v_userInfo_2611_ = lean_ctor_get(v_b_2602_, 1);
v_port_2612_ = lean_ctor_get(v_b_2602_, 3);
v_pathSegments_2613_ = lean_ctor_get(v_b_2602_, 4);
v_query_2614_ = lean_ctor_get(v_b_2602_, 5);
v_fragment_2615_ = lean_ctor_get(v_b_2602_, 6);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_b_2602_);
if (v_isSharedCheck_2627_ == 0)
{
lean_object* v_unused_2628_; 
v_unused_2628_ = lean_ctor_get(v_b_2602_, 2);
lean_dec(v_unused_2628_);
v___x_2617_ = v_b_2602_;
v_isShared_2618_ = v_isSharedCheck_2627_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_fragment_2615_);
lean_inc(v_query_2614_);
lean_inc(v_pathSegments_2613_);
lean_inc(v_port_2612_);
lean_inc(v_userInfo_2611_);
lean_inc(v_scheme_2610_);
lean_dec(v_b_2602_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2627_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2619_, 0, v_val_2606_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2619_);
v___x_2621_ = v___x_2608_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2623_; 
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 2, v___x_2621_);
v___x_2623_ = v___x_2617_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_scheme_2610_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_userInfo_2611_);
lean_ctor_set(v_reuseFailAlloc_2625_, 2, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2625_, 3, v_port_2612_);
lean_ctor_set(v_reuseFailAlloc_2625_, 4, v_pathSegments_2613_);
lean_ctor_set(v_reuseFailAlloc_2625_, 5, v_query_2614_);
lean_ctor_set(v_reuseFailAlloc_2625_, 6, v_fragment_2615_);
v___x_2623_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
return v___x_2624_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x21(lean_object* v_b_2632_, lean_object* v_name_2633_){
_start:
{
lean_object* v___x_2634_; 
lean_inc_ref(v_name_2633_);
v___x_2634_ = l_Std_Http_URI_Builder_setHost_x3f(v_b_2632_, v_name_2633_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2635_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2636_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__0));
v___x_2637_ = lean_unsigned_to_nat(716u);
v___x_2638_ = lean_unsigned_to_nat(14u);
v___x_2639_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__1));
v___x_2640_ = l_String_quote(v_name_2633_);
v___x_2641_ = lean_string_append(v___x_2639_, v___x_2640_);
lean_dec_ref(v___x_2640_);
v___x_2642_ = l_mkPanicMessageWithDecl(v___x_2635_, v___x_2636_, v___x_2637_, v___x_2638_, v___x_2641_);
lean_dec_ref(v___x_2641_);
v___x_2643_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2642_);
return v___x_2643_;
}
else
{
lean_object* v_val_2644_; 
lean_dec_ref(v_name_2633_);
v_val_2644_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_val_2644_);
lean_dec_ref_known(v___x_2634_, 1);
return v_val_2644_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv4(lean_object* v_b_2645_, lean_object* v_addr_2646_){
_start:
{
lean_object* v_scheme_2647_; lean_object* v_userInfo_2648_; lean_object* v_port_2649_; lean_object* v_pathSegments_2650_; lean_object* v_query_2651_; lean_object* v_fragment_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2661_; 
v_scheme_2647_ = lean_ctor_get(v_b_2645_, 0);
v_userInfo_2648_ = lean_ctor_get(v_b_2645_, 1);
v_port_2649_ = lean_ctor_get(v_b_2645_, 3);
v_pathSegments_2650_ = lean_ctor_get(v_b_2645_, 4);
v_query_2651_ = lean_ctor_get(v_b_2645_, 5);
v_fragment_2652_ = lean_ctor_get(v_b_2645_, 6);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_b_2645_);
if (v_isSharedCheck_2661_ == 0)
{
lean_object* v_unused_2662_; 
v_unused_2662_ = lean_ctor_get(v_b_2645_, 2);
lean_dec(v_unused_2662_);
v___x_2654_ = v_b_2645_;
v_isShared_2655_ = v_isSharedCheck_2661_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_fragment_2652_);
lean_inc(v_query_2651_);
lean_inc(v_pathSegments_2650_);
lean_inc(v_port_2649_);
lean_inc(v_userInfo_2648_);
lean_inc(v_scheme_2647_);
lean_dec(v_b_2645_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2661_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2659_; 
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_addr_2646_);
v___x_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 2, v___x_2657_);
v___x_2659_ = v___x_2654_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_scheme_2647_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v_userInfo_2648_);
lean_ctor_set(v_reuseFailAlloc_2660_, 2, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2660_, 3, v_port_2649_);
lean_ctor_set(v_reuseFailAlloc_2660_, 4, v_pathSegments_2650_);
lean_ctor_set(v_reuseFailAlloc_2660_, 5, v_query_2651_);
lean_ctor_set(v_reuseFailAlloc_2660_, 6, v_fragment_2652_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv6(lean_object* v_b_2663_, lean_object* v_addr_2664_){
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
v___x_2674_ = lean_alloc_ctor(2, 1, 0);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort(lean_object* v_b_2681_, uint16_t v_port_2682_){
_start:
{
lean_object* v_scheme_2683_; lean_object* v_userInfo_2684_; lean_object* v_host_2685_; lean_object* v_pathSegments_2686_; lean_object* v_query_2687_; lean_object* v_fragment_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2696_; 
v_scheme_2683_ = lean_ctor_get(v_b_2681_, 0);
v_userInfo_2684_ = lean_ctor_get(v_b_2681_, 1);
v_host_2685_ = lean_ctor_get(v_b_2681_, 2);
v_pathSegments_2686_ = lean_ctor_get(v_b_2681_, 4);
v_query_2687_ = lean_ctor_get(v_b_2681_, 5);
v_fragment_2688_ = lean_ctor_get(v_b_2681_, 6);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_b_2681_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; 
v_unused_2697_ = lean_ctor_get(v_b_2681_, 3);
lean_dec(v_unused_2697_);
v___x_2690_ = v_b_2681_;
v_isShared_2691_ = v_isSharedCheck_2696_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_fragment_2688_);
lean_inc(v_query_2687_);
lean_inc(v_pathSegments_2686_);
lean_inc(v_host_2685_);
lean_inc(v_userInfo_2684_);
lean_inc(v_scheme_2683_);
lean_dec(v_b_2681_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2696_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2692_ = lean_alloc_ctor(2, 0, 2);
lean_ctor_set_uint16(v___x_2692_, 0, v_port_2682_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 3, v___x_2692_);
v___x_2694_ = v___x_2690_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_scheme_2683_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v_userInfo_2684_);
lean_ctor_set(v_reuseFailAlloc_2695_, 2, v_host_2685_);
lean_ctor_set(v_reuseFailAlloc_2695_, 3, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2695_, 4, v_pathSegments_2686_);
lean_ctor_set(v_reuseFailAlloc_2695_, 5, v_query_2687_);
lean_ctor_set(v_reuseFailAlloc_2695_, 6, v_fragment_2688_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort___boxed(lean_object* v_b_2698_, lean_object* v_port_2699_){
_start:
{
uint16_t v_port_boxed_2700_; lean_object* v_res_2701_; 
v_port_boxed_2700_ = lean_unbox(v_port_2699_);
v_res_2701_ = l_Std_Http_URI_Builder_setPort(v_b_2698_, v_port_boxed_2700_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPath(lean_object* v_b_2702_, lean_object* v_segments_2703_){
_start:
{
lean_object* v_scheme_2704_; lean_object* v_userInfo_2705_; lean_object* v_host_2706_; lean_object* v_port_2707_; lean_object* v_query_2708_; lean_object* v_fragment_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
v_scheme_2704_ = lean_ctor_get(v_b_2702_, 0);
v_userInfo_2705_ = lean_ctor_get(v_b_2702_, 1);
v_host_2706_ = lean_ctor_get(v_b_2702_, 2);
v_port_2707_ = lean_ctor_get(v_b_2702_, 3);
v_query_2708_ = lean_ctor_get(v_b_2702_, 5);
v_fragment_2709_ = lean_ctor_get(v_b_2702_, 6);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_b_2702_);
if (v_isSharedCheck_2716_ == 0)
{
lean_object* v_unused_2717_; 
v_unused_2717_ = lean_ctor_get(v_b_2702_, 4);
lean_dec(v_unused_2717_);
v___x_2711_ = v_b_2702_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_fragment_2709_);
lean_inc(v_query_2708_);
lean_inc(v_port_2707_);
lean_inc(v_host_2706_);
lean_inc(v_userInfo_2705_);
lean_inc(v_scheme_2704_);
lean_dec(v_b_2702_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 4, v_segments_2703_);
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_scheme_2704_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v_userInfo_2705_);
lean_ctor_set(v_reuseFailAlloc_2715_, 2, v_host_2706_);
lean_ctor_set(v_reuseFailAlloc_2715_, 3, v_port_2707_);
lean_ctor_set(v_reuseFailAlloc_2715_, 4, v_segments_2703_);
lean_ctor_set(v_reuseFailAlloc_2715_, 5, v_query_2708_);
lean_ctor_set(v_reuseFailAlloc_2715_, 6, v_fragment_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_appendPathSegment(lean_object* v_b_2718_, lean_object* v_segment_2719_){
_start:
{
lean_object* v_scheme_2720_; lean_object* v_userInfo_2721_; lean_object* v_host_2722_; lean_object* v_port_2723_; lean_object* v_pathSegments_2724_; lean_object* v_query_2725_; lean_object* v_fragment_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2734_; 
v_scheme_2720_ = lean_ctor_get(v_b_2718_, 0);
v_userInfo_2721_ = lean_ctor_get(v_b_2718_, 1);
v_host_2722_ = lean_ctor_get(v_b_2718_, 2);
v_port_2723_ = lean_ctor_get(v_b_2718_, 3);
v_pathSegments_2724_ = lean_ctor_get(v_b_2718_, 4);
v_query_2725_ = lean_ctor_get(v_b_2718_, 5);
v_fragment_2726_ = lean_ctor_get(v_b_2718_, 6);
v_isSharedCheck_2734_ = !lean_is_exclusive(v_b_2718_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2728_ = v_b_2718_;
v_isShared_2729_ = v_isSharedCheck_2734_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_fragment_2726_);
lean_inc(v_query_2725_);
lean_inc(v_pathSegments_2724_);
lean_inc(v_port_2723_);
lean_inc(v_host_2722_);
lean_inc(v_userInfo_2721_);
lean_inc(v_scheme_2720_);
lean_dec(v_b_2718_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2734_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2730_ = lean_array_push(v_pathSegments_2724_, v_segment_2719_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 4, v___x_2730_);
v___x_2732_ = v___x_2728_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_scheme_2720_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_userInfo_2721_);
lean_ctor_set(v_reuseFailAlloc_2733_, 2, v_host_2722_);
lean_ctor_set(v_reuseFailAlloc_2733_, 3, v_port_2723_);
lean_ctor_set(v_reuseFailAlloc_2733_, 4, v___x_2730_);
lean_ctor_set(v_reuseFailAlloc_2733_, 5, v_query_2725_);
lean_ctor_set(v_reuseFailAlloc_2733_, 6, v_fragment_2726_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryParam(lean_object* v_b_2735_, lean_object* v_key_2736_, lean_object* v_value_2737_){
_start:
{
lean_object* v_scheme_2738_; lean_object* v_userInfo_2739_; lean_object* v_host_2740_; lean_object* v_port_2741_; lean_object* v_pathSegments_2742_; lean_object* v_query_2743_; lean_object* v_fragment_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2754_; 
v_scheme_2738_ = lean_ctor_get(v_b_2735_, 0);
v_userInfo_2739_ = lean_ctor_get(v_b_2735_, 1);
v_host_2740_ = lean_ctor_get(v_b_2735_, 2);
v_port_2741_ = lean_ctor_get(v_b_2735_, 3);
v_pathSegments_2742_ = lean_ctor_get(v_b_2735_, 4);
v_query_2743_ = lean_ctor_get(v_b_2735_, 5);
v_fragment_2744_ = lean_ctor_get(v_b_2735_, 6);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_b_2735_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2746_ = v_b_2735_;
v_isShared_2747_ = v_isSharedCheck_2754_;
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
lean_dec(v_b_2735_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2754_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2748_, 0, v_value_2737_);
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v_key_2736_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = lean_array_push(v_query_2743_, v___x_2749_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 5, v___x_2750_);
v___x_2752_ = v___x_2746_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_scheme_2738_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v_userInfo_2739_);
lean_ctor_set(v_reuseFailAlloc_2753_, 2, v_host_2740_);
lean_ctor_set(v_reuseFailAlloc_2753_, 3, v_port_2741_);
lean_ctor_set(v_reuseFailAlloc_2753_, 4, v_pathSegments_2742_);
lean_ctor_set(v_reuseFailAlloc_2753_, 5, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2753_, 6, v_fragment_2744_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryFlag(lean_object* v_b_2755_, lean_object* v_key_2756_){
_start:
{
lean_object* v_scheme_2757_; lean_object* v_userInfo_2758_; lean_object* v_host_2759_; lean_object* v_port_2760_; lean_object* v_pathSegments_2761_; lean_object* v_query_2762_; lean_object* v_fragment_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2773_; 
v_scheme_2757_ = lean_ctor_get(v_b_2755_, 0);
v_userInfo_2758_ = lean_ctor_get(v_b_2755_, 1);
v_host_2759_ = lean_ctor_get(v_b_2755_, 2);
v_port_2760_ = lean_ctor_get(v_b_2755_, 3);
v_pathSegments_2761_ = lean_ctor_get(v_b_2755_, 4);
v_query_2762_ = lean_ctor_get(v_b_2755_, 5);
v_fragment_2763_ = lean_ctor_get(v_b_2755_, 6);
v_isSharedCheck_2773_ = !lean_is_exclusive(v_b_2755_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2765_ = v_b_2755_;
v_isShared_2766_ = v_isSharedCheck_2773_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_fragment_2763_);
lean_inc(v_query_2762_);
lean_inc(v_pathSegments_2761_);
lean_inc(v_port_2760_);
lean_inc(v_host_2759_);
lean_inc(v_userInfo_2758_);
lean_inc(v_scheme_2757_);
lean_dec(v_b_2755_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2773_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2767_ = lean_box(0);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_key_2756_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = lean_array_push(v_query_2762_, v___x_2768_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 5, v___x_2769_);
v___x_2771_ = v___x_2765_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_scheme_2757_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_userInfo_2758_);
lean_ctor_set(v_reuseFailAlloc_2772_, 2, v_host_2759_);
lean_ctor_set(v_reuseFailAlloc_2772_, 3, v_port_2760_);
lean_ctor_set(v_reuseFailAlloc_2772_, 4, v_pathSegments_2761_);
lean_ctor_set(v_reuseFailAlloc_2772_, 5, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2772_, 6, v_fragment_2763_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setQuery(lean_object* v_b_2774_, lean_object* v_query_2775_){
_start:
{
lean_object* v_scheme_2776_; lean_object* v_userInfo_2777_; lean_object* v_host_2778_; lean_object* v_port_2779_; lean_object* v_pathSegments_2780_; lean_object* v_fragment_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
v_scheme_2776_ = lean_ctor_get(v_b_2774_, 0);
v_userInfo_2777_ = lean_ctor_get(v_b_2774_, 1);
v_host_2778_ = lean_ctor_get(v_b_2774_, 2);
v_port_2779_ = lean_ctor_get(v_b_2774_, 3);
v_pathSegments_2780_ = lean_ctor_get(v_b_2774_, 4);
v_fragment_2781_ = lean_ctor_get(v_b_2774_, 6);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_b_2774_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; 
v_unused_2789_ = lean_ctor_get(v_b_2774_, 5);
lean_dec(v_unused_2789_);
v___x_2783_ = v_b_2774_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_fragment_2781_);
lean_inc(v_pathSegments_2780_);
lean_inc(v_port_2779_);
lean_inc(v_host_2778_);
lean_inc(v_userInfo_2777_);
lean_inc(v_scheme_2776_);
lean_dec(v_b_2774_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 5, v_query_2775_);
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_scheme_2776_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_userInfo_2777_);
lean_ctor_set(v_reuseFailAlloc_2787_, 2, v_host_2778_);
lean_ctor_set(v_reuseFailAlloc_2787_, 3, v_port_2779_);
lean_ctor_set(v_reuseFailAlloc_2787_, 4, v_pathSegments_2780_);
lean_ctor_set(v_reuseFailAlloc_2787_, 5, v_query_2775_);
lean_ctor_set(v_reuseFailAlloc_2787_, 6, v_fragment_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setFragment(lean_object* v_b_2790_, lean_object* v_fragment_2791_){
_start:
{
lean_object* v_scheme_2792_; lean_object* v_userInfo_2793_; lean_object* v_host_2794_; lean_object* v_port_2795_; lean_object* v_pathSegments_2796_; lean_object* v_query_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2805_; 
v_scheme_2792_ = lean_ctor_get(v_b_2790_, 0);
v_userInfo_2793_ = lean_ctor_get(v_b_2790_, 1);
v_host_2794_ = lean_ctor_get(v_b_2790_, 2);
v_port_2795_ = lean_ctor_get(v_b_2790_, 3);
v_pathSegments_2796_ = lean_ctor_get(v_b_2790_, 4);
v_query_2797_ = lean_ctor_get(v_b_2790_, 5);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_b_2790_);
if (v_isSharedCheck_2805_ == 0)
{
lean_object* v_unused_2806_; 
v_unused_2806_ = lean_ctor_get(v_b_2790_, 6);
lean_dec(v_unused_2806_);
v___x_2799_ = v_b_2790_;
v_isShared_2800_ = v_isSharedCheck_2805_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_query_2797_);
lean_inc(v_pathSegments_2796_);
lean_inc(v_port_2795_);
lean_inc(v_host_2794_);
lean_inc(v_userInfo_2793_);
lean_inc(v_scheme_2792_);
lean_dec(v_b_2790_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2805_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2803_; 
v___x_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2801_, 0, v_fragment_2791_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 6, v___x_2801_);
v___x_2803_ = v___x_2799_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_scheme_2792_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v_userInfo_2793_);
lean_ctor_set(v_reuseFailAlloc_2804_, 2, v_host_2794_);
lean_ctor_set(v_reuseFailAlloc_2804_, 3, v_port_2795_);
lean_ctor_set(v_reuseFailAlloc_2804_, 4, v_pathSegments_2796_);
lean_ctor_set(v_reuseFailAlloc_2804_, 5, v_query_2797_);
lean_ctor_set(v_reuseFailAlloc_2804_, 6, v___x_2801_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(size_t v_sz_2807_, size_t v_i_2808_, lean_object* v_bs_2809_){
_start:
{
uint8_t v___x_2810_; 
v___x_2810_ = lean_usize_dec_lt(v_i_2808_, v_sz_2807_);
if (v___x_2810_ == 0)
{
return v_bs_2809_;
}
else
{
lean_object* v_v_2811_; lean_object* v___x_2812_; lean_object* v_bs_x27_2813_; lean_object* v___x_2814_; size_t v___x_2815_; size_t v___x_2816_; lean_object* v___x_2817_; 
v_v_2811_ = lean_array_uget(v_bs_2809_, v_i_2808_);
v___x_2812_ = lean_unsigned_to_nat(0u);
v_bs_x27_2813_ = lean_array_uset(v_bs_2809_, v_i_2808_, v___x_2812_);
v___x_2814_ = l_Std_Http_URI_EncodedSegment_encode(v_v_2811_);
lean_dec(v_v_2811_);
v___x_2815_ = ((size_t)1ULL);
v___x_2816_ = lean_usize_add(v_i_2808_, v___x_2815_);
v___x_2817_ = lean_array_uset(v_bs_x27_2813_, v_i_2808_, v___x_2814_);
v_i_2808_ = v___x_2816_;
v_bs_2809_ = v___x_2817_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0___boxed(lean_object* v_sz_2819_, lean_object* v_i_2820_, lean_object* v_bs_2821_){
_start:
{
size_t v_sz_boxed_2822_; size_t v_i_boxed_2823_; lean_object* v_res_2824_; 
v_sz_boxed_2822_ = lean_unbox_usize(v_sz_2819_);
lean_dec(v_sz_2819_);
v_i_boxed_2823_ = lean_unbox_usize(v_i_2820_);
lean_dec(v_i_2820_);
v_res_2824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_boxed_2822_, v_i_boxed_2823_, v_bs_2821_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(size_t v_sz_2825_, size_t v_i_2826_, lean_object* v_bs_2827_){
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
lean_object* v_v_2829_; lean_object* v_fst_2830_; lean_object* v_snd_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2860_; 
v_v_2829_ = lean_array_uget(v_bs_2827_, v_i_2826_);
v_fst_2830_ = lean_ctor_get(v_v_2829_, 0);
v_snd_2831_ = lean_ctor_get(v_v_2829_, 1);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_v_2829_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2833_ = v_v_2829_;
v_isShared_2834_ = v_isSharedCheck_2860_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_snd_2831_);
lean_inc(v_fst_2830_);
lean_dec(v_v_2829_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2860_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; lean_object* v_bs_x27_2836_; lean_object* v___y_2838_; lean_object* v___x_2843_; 
v___x_2835_ = lean_unsigned_to_nat(0u);
v_bs_x27_2836_ = lean_array_uset(v_bs_2827_, v_i_2826_, v___x_2835_);
v___x_2843_ = l_Std_Http_URI_EncodedQueryParam_encode(v_fst_2830_);
lean_dec(v_fst_2830_);
if (lean_obj_tag(v_snd_2831_) == 0)
{
lean_object* v___x_2844_; lean_object* v___x_2846_; 
v___x_2844_ = lean_box(0);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 1, v___x_2844_);
lean_ctor_set(v___x_2833_, 0, v___x_2843_);
v___x_2846_ = v___x_2833_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
v___y_2838_ = v___x_2846_;
goto v___jp_2837_;
}
}
else
{
lean_object* v_val_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2859_; 
v_val_2848_ = lean_ctor_get(v_snd_2831_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v_snd_2831_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2850_ = v_snd_2831_;
v_isShared_2851_ = v_isSharedCheck_2859_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_val_2848_);
lean_dec(v_snd_2831_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2859_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2852_; lean_object* v___x_2854_; 
v___x_2852_ = l_Std_Http_URI_EncodedQueryParam_encode(v_val_2848_);
lean_dec(v_val_2848_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v___x_2852_);
v___x_2854_ = v___x_2850_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2852_);
v___x_2854_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2856_; 
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 1, v___x_2854_);
lean_ctor_set(v___x_2833_, 0, v___x_2843_);
v___x_2856_ = v___x_2833_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
v___y_2838_ = v___x_2856_;
goto v___jp_2837_;
}
}
}
}
v___jp_2837_:
{
size_t v___x_2839_; size_t v___x_2840_; lean_object* v___x_2841_; 
v___x_2839_ = ((size_t)1ULL);
v___x_2840_ = lean_usize_add(v_i_2826_, v___x_2839_);
v___x_2841_ = lean_array_uset(v_bs_x27_2836_, v_i_2826_, v___y_2838_);
v_i_2826_ = v___x_2840_;
v_bs_2827_ = v___x_2841_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1___boxed(lean_object* v_sz_2861_, lean_object* v_i_2862_, lean_object* v_bs_2863_){
_start:
{
size_t v_sz_boxed_2864_; size_t v_i_boxed_2865_; lean_object* v_res_2866_; 
v_sz_boxed_2864_ = lean_unbox_usize(v_sz_2861_);
lean_dec(v_sz_2861_);
v_i_boxed_2865_ = lean_unbox_usize(v_i_2862_);
lean_dec(v_i_2862_);
v_res_2866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_boxed_2864_, v_i_boxed_2865_, v_bs_2863_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_build(lean_object* v_b_2867_){
_start:
{
lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; uint8_t v___y_2873_; lean_object* v___y_2874_; lean_object* v_scheme_2890_; lean_object* v_userInfo_2891_; lean_object* v_host_2892_; lean_object* v_port_2893_; lean_object* v_pathSegments_2894_; lean_object* v_query_2895_; lean_object* v_fragment_2896_; lean_object* v___y_2898_; 
v_scheme_2890_ = lean_ctor_get(v_b_2867_, 0);
lean_inc(v_scheme_2890_);
v_userInfo_2891_ = lean_ctor_get(v_b_2867_, 1);
lean_inc(v_userInfo_2891_);
v_host_2892_ = lean_ctor_get(v_b_2867_, 2);
lean_inc(v_host_2892_);
v_port_2893_ = lean_ctor_get(v_b_2867_, 3);
lean_inc(v_port_2893_);
v_pathSegments_2894_ = lean_ctor_get(v_b_2867_, 4);
lean_inc_ref(v_pathSegments_2894_);
v_query_2895_ = lean_ctor_get(v_b_2867_, 5);
lean_inc_ref(v_query_2895_);
v_fragment_2896_ = lean_ctor_get(v_b_2867_, 6);
lean_inc(v_fragment_2896_);
lean_dec_ref(v_b_2867_);
if (lean_obj_tag(v_scheme_2890_) == 0)
{
lean_object* v___x_2911_; 
v___x_2911_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___y_2898_ = v___x_2911_;
goto v___jp_2897_;
}
else
{
lean_object* v_val_2912_; 
v_val_2912_ = lean_ctor_get(v_scheme_2890_, 0);
lean_inc(v_val_2912_);
lean_dec_ref_known(v_scheme_2890_, 1);
v___y_2898_ = v_val_2912_;
goto v___jp_2897_;
}
v___jp_2868_:
{
size_t v_sz_2875_; size_t v___x_2876_; lean_object* v___x_2877_; lean_object* v_path_2878_; size_t v_sz_2879_; lean_object* v_query_2880_; lean_object* v___x_2881_; lean_object* v_query_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v_sz_2875_ = lean_array_size(v___y_2871_);
v___x_2876_ = ((size_t)0ULL);
v___x_2877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_2875_, v___x_2876_, v___y_2871_);
v_path_2878_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_path_2878_, 0, v___x_2877_);
lean_ctor_set_uint8(v_path_2878_, sizeof(void*)*1, v___y_2873_);
v_sz_2879_ = lean_array_size(v___y_2872_);
v_query_2880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_2879_, v___x_2876_, v___y_2872_);
v___x_2881_ = lean_array_to_list(v_query_2880_);
v_query_2882_ = lean_array_mk(v___x_2881_);
v___x_2883_ = lean_array_get_size(v_query_2882_);
v___x_2884_ = lean_unsigned_to_nat(0u);
v___x_2885_ = lean_nat_dec_eq(v___x_2883_, v___x_2884_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v_query_2882_);
v___x_2887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2887_, 0, v___y_2870_);
lean_ctor_set(v___x_2887_, 1, v___y_2874_);
lean_ctor_set(v___x_2887_, 2, v_path_2878_);
lean_ctor_set(v___x_2887_, 3, v___x_2886_);
lean_ctor_set(v___x_2887_, 4, v___y_2869_);
return v___x_2887_;
}
else
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
lean_dec_ref(v_query_2882_);
v___x_2888_ = lean_box(0);
v___x_2889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2889_, 0, v___y_2870_);
lean_ctor_set(v___x_2889_, 1, v___y_2874_);
lean_ctor_set(v___x_2889_, 2, v_path_2878_);
lean_ctor_set(v___x_2889_, 3, v___x_2888_);
lean_ctor_set(v___x_2889_, 4, v___y_2869_);
return v___x_2889_;
}
}
v___jp_2897_:
{
if (lean_obj_tag(v_host_2892_) == 0)
{
uint8_t v___x_2899_; lean_object* v___x_2900_; 
lean_dec(v_port_2893_);
lean_dec(v_userInfo_2891_);
v___x_2899_ = 1;
v___x_2900_ = lean_box(0);
v___y_2869_ = v_fragment_2896_;
v___y_2870_ = v___y_2898_;
v___y_2871_ = v_pathSegments_2894_;
v___y_2872_ = v_query_2895_;
v___y_2873_ = v___x_2899_;
v___y_2874_ = v___x_2900_;
goto v___jp_2868_;
}
else
{
lean_object* v_val_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2910_; 
v_val_2901_ = lean_ctor_get(v_host_2892_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v_host_2892_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2903_ = v_host_2892_;
v_isShared_2904_ = v_isSharedCheck_2910_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_val_2901_);
lean_dec(v_host_2892_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2910_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
uint8_t v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2905_ = 1;
v___x_2906_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2906_, 0, v_userInfo_2891_);
lean_ctor_set(v___x_2906_, 1, v_val_2901_);
lean_ctor_set(v___x_2906_, 2, v_port_2893_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2906_);
v___x_2908_ = v___x_2903_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
v___y_2869_ = v_fragment_2896_;
v___y_2870_ = v___y_2898_;
v___y_2871_ = v_pathSegments_2894_;
v___y_2872_ = v_query_2895_;
v___y_2873_ = v___x_2905_;
v___y_2874_ = v___x_2908_;
goto v___jp_2868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withScheme_x21(lean_object* v_uri_2913_, lean_object* v_scheme_2914_){
_start:
{
lean_object* v_authority_2915_; lean_object* v_path_2916_; lean_object* v_query_2917_; lean_object* v_fragment_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2926_; 
v_authority_2915_ = lean_ctor_get(v_uri_2913_, 1);
v_path_2916_ = lean_ctor_get(v_uri_2913_, 2);
v_query_2917_ = lean_ctor_get(v_uri_2913_, 3);
v_fragment_2918_ = lean_ctor_get(v_uri_2913_, 4);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_uri_2913_);
if (v_isSharedCheck_2926_ == 0)
{
lean_object* v_unused_2927_; 
v_unused_2927_ = lean_ctor_get(v_uri_2913_, 0);
lean_dec(v_unused_2927_);
v___x_2920_ = v_uri_2913_;
v_isShared_2921_ = v_isSharedCheck_2926_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_fragment_2918_);
lean_inc(v_query_2917_);
lean_inc(v_path_2916_);
lean_inc(v_authority_2915_);
lean_dec(v_uri_2913_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2926_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2922_; lean_object* v___x_2924_; 
v___x_2922_ = l_Std_Http_URI_Scheme_ofString_x21(v_scheme_2914_);
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 0, v___x_2922_);
v___x_2924_ = v___x_2920_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_authority_2915_);
lean_ctor_set(v_reuseFailAlloc_2925_, 2, v_path_2916_);
lean_ctor_set(v_reuseFailAlloc_2925_, 3, v_query_2917_);
lean_ctor_set(v_reuseFailAlloc_2925_, 4, v_fragment_2918_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withAuthority(lean_object* v_uri_2928_, lean_object* v_authority_2929_){
_start:
{
lean_object* v_scheme_2930_; lean_object* v_path_2931_; lean_object* v_query_2932_; lean_object* v_fragment_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
v_scheme_2930_ = lean_ctor_get(v_uri_2928_, 0);
v_path_2931_ = lean_ctor_get(v_uri_2928_, 2);
v_query_2932_ = lean_ctor_get(v_uri_2928_, 3);
v_fragment_2933_ = lean_ctor_get(v_uri_2928_, 4);
v_isSharedCheck_2940_ = !lean_is_exclusive(v_uri_2928_);
if (v_isSharedCheck_2940_ == 0)
{
lean_object* v_unused_2941_; 
v_unused_2941_ = lean_ctor_get(v_uri_2928_, 1);
lean_dec(v_unused_2941_);
v___x_2935_ = v_uri_2928_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_fragment_2933_);
lean_inc(v_query_2932_);
lean_inc(v_path_2931_);
lean_inc(v_scheme_2930_);
lean_dec(v_uri_2928_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 1, v_authority_2929_);
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_scheme_2930_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_authority_2929_);
lean_ctor_set(v_reuseFailAlloc_2939_, 2, v_path_2931_);
lean_ctor_set(v_reuseFailAlloc_2939_, 3, v_query_2932_);
lean_ctor_set(v_reuseFailAlloc_2939_, 4, v_fragment_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withPath(lean_object* v_uri_2942_, lean_object* v_path_2943_){
_start:
{
lean_object* v_scheme_2944_; lean_object* v_authority_2945_; lean_object* v_query_2946_; lean_object* v_fragment_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
v_scheme_2944_ = lean_ctor_get(v_uri_2942_, 0);
v_authority_2945_ = lean_ctor_get(v_uri_2942_, 1);
v_query_2946_ = lean_ctor_get(v_uri_2942_, 3);
v_fragment_2947_ = lean_ctor_get(v_uri_2942_, 4);
v_isSharedCheck_2954_ = !lean_is_exclusive(v_uri_2942_);
if (v_isSharedCheck_2954_ == 0)
{
lean_object* v_unused_2955_; 
v_unused_2955_ = lean_ctor_get(v_uri_2942_, 2);
lean_dec(v_unused_2955_);
v___x_2949_ = v_uri_2942_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_fragment_2947_);
lean_inc(v_query_2946_);
lean_inc(v_authority_2945_);
lean_inc(v_scheme_2944_);
lean_dec(v_uri_2942_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 2, v_path_2943_);
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_scheme_2944_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_authority_2945_);
lean_ctor_set(v_reuseFailAlloc_2953_, 2, v_path_2943_);
lean_ctor_set(v_reuseFailAlloc_2953_, 3, v_query_2946_);
lean_ctor_set(v_reuseFailAlloc_2953_, 4, v_fragment_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withQuery(lean_object* v_uri_2956_, lean_object* v_query_2957_){
_start:
{
lean_object* v_scheme_2958_; lean_object* v_authority_2959_; lean_object* v_path_2960_; lean_object* v_fragment_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2969_; 
v_scheme_2958_ = lean_ctor_get(v_uri_2956_, 0);
v_authority_2959_ = lean_ctor_get(v_uri_2956_, 1);
v_path_2960_ = lean_ctor_get(v_uri_2956_, 2);
v_fragment_2961_ = lean_ctor_get(v_uri_2956_, 4);
v_isSharedCheck_2969_ = !lean_is_exclusive(v_uri_2956_);
if (v_isSharedCheck_2969_ == 0)
{
lean_object* v_unused_2970_; 
v_unused_2970_ = lean_ctor_get(v_uri_2956_, 3);
lean_dec(v_unused_2970_);
v___x_2963_ = v_uri_2956_;
v_isShared_2964_ = v_isSharedCheck_2969_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_fragment_2961_);
lean_inc(v_path_2960_);
lean_inc(v_authority_2959_);
lean_inc(v_scheme_2958_);
lean_dec(v_uri_2956_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2969_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2965_, 0, v_query_2957_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 3, v___x_2965_);
v___x_2967_ = v___x_2963_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_scheme_2958_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_authority_2959_);
lean_ctor_set(v_reuseFailAlloc_2968_, 2, v_path_2960_);
lean_ctor_set(v_reuseFailAlloc_2968_, 3, v___x_2965_);
lean_ctor_set(v_reuseFailAlloc_2968_, 4, v_fragment_2961_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_withFragment(lean_object* v_uri_2971_, lean_object* v_fragment_2972_){
_start:
{
lean_object* v_scheme_2973_; lean_object* v_authority_2974_; lean_object* v_path_2975_; lean_object* v_query_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
v_scheme_2973_ = lean_ctor_get(v_uri_2971_, 0);
v_authority_2974_ = lean_ctor_get(v_uri_2971_, 1);
v_path_2975_ = lean_ctor_get(v_uri_2971_, 2);
v_query_2976_ = lean_ctor_get(v_uri_2971_, 3);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_uri_2971_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; 
v_unused_2984_ = lean_ctor_get(v_uri_2971_, 4);
lean_dec(v_unused_2984_);
v___x_2978_ = v_uri_2971_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_query_2976_);
lean_inc(v_path_2975_);
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
lean_ctor_set(v___x_2978_, 4, v_fragment_2972_);
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_scheme_2973_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_authority_2974_);
lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_path_2975_);
lean_ctor_set(v_reuseFailAlloc_2982_, 3, v_query_2976_);
lean_ctor_set(v_reuseFailAlloc_2982_, 4, v_fragment_2972_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_normalize(lean_object* v_uri_2985_){
_start:
{
lean_object* v_scheme_2986_; lean_object* v_authority_2987_; lean_object* v_path_2988_; lean_object* v_query_2989_; lean_object* v_fragment_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2998_; 
v_scheme_2986_ = lean_ctor_get(v_uri_2985_, 0);
v_authority_2987_ = lean_ctor_get(v_uri_2985_, 1);
v_path_2988_ = lean_ctor_get(v_uri_2985_, 2);
v_query_2989_ = lean_ctor_get(v_uri_2985_, 3);
v_fragment_2990_ = lean_ctor_get(v_uri_2985_, 4);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_uri_2985_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2992_ = v_uri_2985_;
v_isShared_2993_ = v_isSharedCheck_2998_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_fragment_2990_);
lean_inc(v_query_2989_);
lean_inc(v_path_2988_);
lean_inc(v_authority_2987_);
lean_inc(v_scheme_2986_);
lean_dec(v_uri_2985_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2998_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2994_; lean_object* v___x_2996_; 
v___x_2994_ = l_Std_Http_URI_Path_normalize(v_path_2988_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 2, v___x_2994_);
v___x_2996_ = v___x_2992_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_scheme_2986_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v_authority_2987_);
lean_ctor_set(v_reuseFailAlloc_2997_, 2, v___x_2994_);
lean_ctor_set(v_reuseFailAlloc_2997_, 3, v_query_2989_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___redArg(lean_object* v_x_2999_){
_start:
{
lean_object* v_scheme_3000_; lean_object* v_host_3001_; uint16_t v_port_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v_ctr_3023_; lean_object* v_a_3024_; 
v_scheme_3000_ = lean_ctor_get(v_x_2999_, 0);
lean_inc_ref(v_scheme_3000_);
v_host_3001_ = lean_ctor_get(v_x_2999_, 1);
lean_inc_ref(v_host_3001_);
v_port_3002_ = lean_ctor_get_uint16(v_x_2999_, sizeof(void*)*2);
lean_dec_ref(v_x_2999_);
v___x_3003_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_3004_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_3005_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_3006_ = l_String_quote(v_scheme_3000_);
v___x_3007_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
v___x_3008_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3005_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = 0;
v___x_3010_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3010_, 0, v___x_3008_);
lean_ctor_set_uint8(v___x_3010_, sizeof(void*)*1, v___x_3009_);
v___x_3011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3004_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
v___x_3012_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_3013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3011_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
v___x_3014_ = lean_box(1);
v___x_3015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_3017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3015_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
v___x_3018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
lean_ctor_set(v___x_3018_, 1, v___x_3003_);
v___x_3019_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_3020_ = lean_unsigned_to_nat(0u);
v___x_3021_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_3001_))
{
case 0:
{
lean_object* v_name_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3063_; 
v_name_3054_ = lean_ctor_get(v_host_3001_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_host_3001_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3056_ = v_host_3001_;
v_isShared_3057_ = v_isSharedCheck_3063_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_name_3054_);
lean_dec(v_host_3001_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3063_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3061_; 
v___x_3058_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_3059_ = l_String_quote(v_name_3054_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set_tag(v___x_3056_, 3);
lean_ctor_set(v___x_3056_, 0, v___x_3059_);
v___x_3061_ = v___x_3056_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
v_ctr_3023_ = v___x_3058_;
v_a_3024_ = v___x_3061_;
goto v___jp_3022_;
}
}
}
case 1:
{
lean_object* v_ipv4_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3073_; 
v_ipv4_3064_ = lean_ctor_get(v_host_3001_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v_host_3001_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3066_ = v_host_3001_;
v_isShared_3067_ = v_isSharedCheck_3073_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_ipv4_3064_);
lean_dec(v_host_3001_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3073_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3071_; 
v___x_3068_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_3069_ = lean_uv_ntop_v4(v_ipv4_3064_);
lean_dec_ref(v_ipv4_3064_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set_tag(v___x_3066_, 3);
lean_ctor_set(v___x_3066_, 0, v___x_3069_);
v___x_3071_ = v___x_3066_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3069_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
v_ctr_3023_ = v___x_3068_;
v_a_3024_ = v___x_3071_;
goto v___jp_3022_;
}
}
}
default: 
{
lean_object* v_ipv6_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3083_; 
v_ipv6_3074_ = lean_ctor_get(v_host_3001_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v_host_3001_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3076_ = v_host_3001_;
v_isShared_3077_ = v_isSharedCheck_3083_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_ipv6_3074_);
lean_dec(v_host_3001_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3083_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3081_; 
v___x_3078_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_3079_ = lean_uv_ntop_v6(v_ipv6_3074_);
lean_dec_ref(v_ipv6_3074_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set_tag(v___x_3076_, 3);
lean_ctor_set(v___x_3076_, 0, v___x_3079_);
v___x_3081_ = v___x_3076_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v___x_3079_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
v_ctr_3023_ = v___x_3078_;
v_a_3024_ = v___x_3081_;
goto v___jp_3022_;
}
}
}
}
v___jp_3022_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3025_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_3026_ = lean_string_append(v___x_3025_, v_ctr_3023_);
v___x_3027_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
v___x_3028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
lean_ctor_set(v___x_3028_, 1, v___x_3014_);
v___x_3029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
lean_ctor_set(v___x_3029_, 1, v_a_3024_);
v___x_3030_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3021_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v___x_3031_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
lean_ctor_set_uint8(v___x_3031_, sizeof(void*)*1, v___x_3009_);
v___x_3032_ = l_Repr_addAppParen(v___x_3031_, v___x_3020_);
v___x_3033_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3019_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
v___x_3034_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
lean_ctor_set_uint8(v___x_3034_, sizeof(void*)*1, v___x_3009_);
v___x_3035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3018_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
v___x_3036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
lean_ctor_set(v___x_3036_, 1, v___x_3012_);
v___x_3037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v___x_3014_);
v___x_3038_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_3039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3037_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
v___x_3040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v___x_3003_);
v___x_3041_ = lean_uint16_to_nat(v_port_3002_);
v___x_3042_ = l_Nat_reprFast(v___x_3041_);
v___x_3043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
v___x_3044_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3019_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
lean_ctor_set_uint8(v___x_3045_, sizeof(void*)*1, v___x_3009_);
v___x_3046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3040_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_3048_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_3049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
lean_ctor_set(v___x_3049_, 1, v___x_3046_);
v___x_3050_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_3051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3049_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
v___x_3052_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3047_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*1, v___x_3009_);
return v___x_3053_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr(lean_object* v_x_3084_, lean_object* v_prec_3085_){
_start:
{
lean_object* v___x_3086_; 
v___x_3086_ = l_Std_Http_URI_instReprOrigin_repr___redArg(v_x_3084_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___boxed(lean_object* v_x_3087_, lean_object* v_prec_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Std_Http_URI_instReprOrigin_repr(v_x_3087_, v_prec_3088_);
lean_dec(v_prec_3088_);
return v_res_3089_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqOrigin_beq(lean_object* v_x_3092_, lean_object* v_x_3093_){
_start:
{
lean_object* v_scheme_3094_; lean_object* v_host_3095_; uint16_t v_port_3096_; lean_object* v_scheme_3097_; lean_object* v_host_3098_; uint16_t v_port_3099_; uint8_t v___x_3100_; 
v_scheme_3094_ = lean_ctor_get(v_x_3092_, 0);
v_host_3095_ = lean_ctor_get(v_x_3092_, 1);
v_port_3096_ = lean_ctor_get_uint16(v_x_3092_, sizeof(void*)*2);
v_scheme_3097_ = lean_ctor_get(v_x_3093_, 0);
v_host_3098_ = lean_ctor_get(v_x_3093_, 1);
v_port_3099_ = lean_ctor_get_uint16(v_x_3093_, sizeof(void*)*2);
v___x_3100_ = lean_string_dec_eq(v_scheme_3094_, v_scheme_3097_);
if (v___x_3100_ == 0)
{
return v___x_3100_;
}
else
{
uint8_t v___x_3101_; 
v___x_3101_ = l_Std_Http_URI_instBEqHost_beq(v_host_3095_, v_host_3098_);
if (v___x_3101_ == 0)
{
return v___x_3101_;
}
else
{
uint8_t v___x_3102_; 
v___x_3102_ = lean_uint16_dec_eq(v_port_3096_, v_port_3099_);
return v___x_3102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqOrigin_beq___boxed(lean_object* v_x_3103_, lean_object* v_x_3104_){
_start:
{
uint8_t v_res_3105_; lean_object* v_r_3106_; 
v_res_3105_ = l_Std_Http_URI_instBEqOrigin_beq(v_x_3103_, v_x_3104_);
lean_dec_ref(v_x_3104_);
lean_dec_ref(v_x_3103_);
v_r_3106_ = lean_box(v_res_3105_);
return v_r_3106_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Origin_hostHeader(lean_object* v_o_3109_){
_start:
{
lean_object* v_scheme_3110_; lean_object* v_host_3111_; uint16_t v_port_3112_; lean_object* v___y_3114_; uint16_t v_defaultPort_3120_; uint8_t v___x_3121_; 
v_scheme_3110_ = lean_ctor_get(v_o_3109_, 0);
lean_inc_ref(v_scheme_3110_);
v_host_3111_ = lean_ctor_get(v_o_3109_, 1);
lean_inc_ref(v_host_3111_);
v_port_3112_ = lean_ctor_get_uint16(v_o_3109_, sizeof(void*)*2);
lean_dec_ref(v_o_3109_);
v_defaultPort_3120_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_3110_);
lean_dec_ref(v_scheme_3110_);
v___x_3121_ = lean_uint16_dec_eq(v_port_3112_, v_defaultPort_3120_);
if (v___x_3121_ == 0)
{
switch(lean_obj_tag(v_host_3111_))
{
case 0:
{
lean_object* v_name_3122_; 
v_name_3122_ = lean_ctor_get(v_host_3111_, 0);
lean_inc_ref(v_name_3122_);
lean_dec_ref_known(v_host_3111_, 1);
v___y_3114_ = v_name_3122_;
goto v___jp_3113_;
}
case 1:
{
lean_object* v_ipv4_3123_; lean_object* v___x_3124_; 
v_ipv4_3123_ = lean_ctor_get(v_host_3111_, 0);
lean_inc_ref(v_ipv4_3123_);
lean_dec_ref_known(v_host_3111_, 1);
v___x_3124_ = lean_uv_ntop_v4(v_ipv4_3123_);
lean_dec_ref(v_ipv4_3123_);
v___y_3114_ = v___x_3124_;
goto v___jp_3113_;
}
default: 
{
lean_object* v_ipv6_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v_ipv6_3125_ = lean_ctor_get(v_host_3111_, 0);
lean_inc_ref(v_ipv6_3125_);
lean_dec_ref_known(v_host_3111_, 1);
v___x_3126_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3127_ = lean_uv_ntop_v6(v_ipv6_3125_);
lean_dec_ref(v_ipv6_3125_);
v___x_3128_ = lean_string_append(v___x_3126_, v___x_3127_);
lean_dec_ref(v___x_3127_);
v___x_3129_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3130_ = lean_string_append(v___x_3128_, v___x_3129_);
v___y_3114_ = v___x_3130_;
goto v___jp_3113_;
}
}
}
else
{
switch(lean_obj_tag(v_host_3111_))
{
case 0:
{
lean_object* v_name_3131_; 
v_name_3131_ = lean_ctor_get(v_host_3111_, 0);
lean_inc_ref(v_name_3131_);
lean_dec_ref_known(v_host_3111_, 1);
return v_name_3131_;
}
case 1:
{
lean_object* v_ipv4_3132_; lean_object* v___x_3133_; 
v_ipv4_3132_ = lean_ctor_get(v_host_3111_, 0);
lean_inc_ref(v_ipv4_3132_);
lean_dec_ref_known(v_host_3111_, 1);
v___x_3133_ = lean_uv_ntop_v4(v_ipv4_3132_);
lean_dec_ref(v_ipv4_3132_);
return v___x_3133_;
}
default: 
{
lean_object* v_ipv6_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v_ipv6_3134_ = lean_ctor_get(v_host_3111_, 0);
lean_inc_ref(v_ipv6_3134_);
lean_dec_ref_known(v_host_3111_, 1);
v___x_3135_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3136_ = lean_uv_ntop_v6(v_ipv6_3134_);
lean_dec_ref(v_ipv6_3134_);
v___x_3137_ = lean_string_append(v___x_3135_, v___x_3136_);
lean_dec_ref(v___x_3136_);
v___x_3138_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3139_ = lean_string_append(v___x_3137_, v___x_3138_);
return v___x_3139_;
}
}
}
v___jp_3113_:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3115_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3116_ = lean_string_append(v___y_3114_, v___x_3115_);
v___x_3117_ = lean_uint16_to_nat(v_port_3112_);
v___x_3118_ = l_Nat_reprFast(v___x_3117_);
v___x_3119_ = lean_string_append(v___x_3116_, v___x_3118_);
lean_dec_ref(v___x_3118_);
return v___x_3119_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___redArg(lean_object* v_x_3146_){
_start:
{
lean_object* v_authority_3147_; lean_object* v_path_3148_; lean_object* v_query_3149_; lean_object* v_fragment_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; uint8_t v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v_authority_3147_ = lean_ctor_get(v_x_3146_, 0);
lean_inc(v_authority_3147_);
v_path_3148_ = lean_ctor_get(v_x_3146_, 1);
lean_inc_ref(v_path_3148_);
v_query_3149_ = lean_ctor_get(v_x_3146_, 2);
lean_inc(v_query_3149_);
v_fragment_3150_ = lean_ctor_get(v_x_3146_, 3);
lean_inc(v_fragment_3150_);
lean_dec_ref(v_x_3146_);
v___x_3151_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_3152_ = ((lean_object*)(l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__1));
v___x_3153_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_3154_ = lean_unsigned_to_nat(0u);
v___x_3155_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_3147_, v___x_3154_);
v___x_3156_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3153_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = 0;
v___x_3158_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3158_, 0, v___x_3156_);
lean_ctor_set_uint8(v___x_3158_, sizeof(void*)*1, v___x_3157_);
v___x_3159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3152_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_3161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3159_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = lean_box(1);
v___x_3163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3161_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_3165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3163_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
v___x_3166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v___x_3151_);
v___x_3167_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_3168_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3148_);
v___x_3169_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3167_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set_uint8(v___x_3170_, sizeof(void*)*1, v___x_3157_);
v___x_3171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3166_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
lean_ctor_set(v___x_3172_, 1, v___x_3160_);
v___x_3173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
lean_ctor_set(v___x_3173_, 1, v___x_3162_);
v___x_3174_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_3175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
lean_ctor_set(v___x_3176_, 1, v___x_3151_);
v___x_3177_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_3178_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3149_, v___x_3154_);
v___x_3179_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3177_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
lean_ctor_set_uint8(v___x_3180_, sizeof(void*)*1, v___x_3157_);
v___x_3181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3176_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
lean_ctor_set(v___x_3182_, 1, v___x_3160_);
v___x_3183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
lean_ctor_set(v___x_3183_, 1, v___x_3162_);
v___x_3184_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_3185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3183_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
lean_ctor_set(v___x_3186_, 1, v___x_3151_);
v___x_3187_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_3188_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_3150_, v___x_3154_);
v___x_3189_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3187_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
v___x_3190_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
lean_ctor_set_uint8(v___x_3190_, sizeof(void*)*1, v___x_3157_);
v___x_3191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3186_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v___x_3192_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_3193_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_3194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
lean_ctor_set(v___x_3194_, 1, v___x_3191_);
v___x_3195_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_3196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3194_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
v___x_3197_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3192_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
v___x_3198_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3198_, 0, v___x_3197_);
lean_ctor_set_uint8(v___x_3198_, sizeof(void*)*1, v___x_3157_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr(lean_object* v_x_3199_, lean_object* v_prec_3200_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_x_3199_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___boxed(lean_object* v_x_3202_, lean_object* v_prec_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Std_Http_URI_instReprRelativeRef_repr(v_x_3202_, v_prec_3203_);
lean_dec(v_prec_3203_);
return v_res_3204_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqRelativeRef_beq(lean_object* v_x_3212_, lean_object* v_x_3213_){
_start:
{
lean_object* v_authority_3214_; lean_object* v_path_3215_; lean_object* v_query_3216_; lean_object* v_fragment_3217_; lean_object* v_authority_3218_; lean_object* v_path_3219_; lean_object* v_query_3220_; lean_object* v_fragment_3221_; uint8_t v___x_3222_; 
v_authority_3214_ = lean_ctor_get(v_x_3212_, 0);
v_path_3215_ = lean_ctor_get(v_x_3212_, 1);
v_query_3216_ = lean_ctor_get(v_x_3212_, 2);
v_fragment_3217_ = lean_ctor_get(v_x_3212_, 3);
v_authority_3218_ = lean_ctor_get(v_x_3213_, 0);
v_path_3219_ = lean_ctor_get(v_x_3213_, 1);
v_query_3220_ = lean_ctor_get(v_x_3213_, 2);
v_fragment_3221_ = lean_ctor_get(v_x_3213_, 3);
v___x_3222_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_3214_, v_authority_3218_);
if (v___x_3222_ == 0)
{
return v___x_3222_;
}
else
{
uint8_t v___x_3223_; 
v___x_3223_ = l_Std_Http_URI_instBEqPath_beq(v_path_3215_, v_path_3219_);
if (v___x_3223_ == 0)
{
return v___x_3223_;
}
else
{
uint8_t v___x_3224_; 
v___x_3224_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_3216_, v_query_3220_);
if (v___x_3224_ == 0)
{
return v___x_3224_;
}
else
{
uint8_t v___x_3225_; 
v___x_3225_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_3217_, v_fragment_3221_);
return v___x_3225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqRelativeRef_beq___boxed(lean_object* v_x_3226_, lean_object* v_x_3227_){
_start:
{
uint8_t v_res_3228_; lean_object* v_r_3229_; 
v_res_3228_ = l_Std_Http_URI_instBEqRelativeRef_beq(v_x_3226_, v_x_3227_);
lean_dec_ref(v_x_3227_);
lean_dec_ref(v_x_3226_);
v_r_3229_ = lean_box(v_res_3228_);
return v_r_3229_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringRelativeRef___lam__1(lean_object* v___f_3232_, lean_object* v_ref_3233_){
_start:
{
lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v_authority_3242_; lean_object* v_path_3243_; lean_object* v_query_3244_; lean_object* v_fragment_3245_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3257_; 
v_authority_3242_ = lean_ctor_get(v_ref_3233_, 0);
lean_inc(v_authority_3242_);
v_path_3243_ = lean_ctor_get(v_ref_3233_, 1);
lean_inc_ref(v_path_3243_);
v_query_3244_ = lean_ctor_get(v_ref_3233_, 2);
lean_inc(v_query_3244_);
v_fragment_3245_ = lean_ctor_get(v_ref_3233_, 3);
lean_inc(v_fragment_3245_);
lean_dec_ref(v_ref_3233_);
if (lean_obj_tag(v_authority_3242_) == 0)
{
lean_object* v___x_3268_; 
v___x_3268_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3257_ = v___x_3268_;
goto v___jp_3256_;
}
else
{
lean_object* v_val_3269_; lean_object* v_userInfo_3270_; lean_object* v_host_3271_; lean_object* v_port_3272_; lean_object* v___x_3273_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3292_; 
v_val_3269_ = lean_ctor_get(v_authority_3242_, 0);
lean_inc(v_val_3269_);
lean_dec_ref_known(v_authority_3242_, 1);
v_userInfo_3270_ = lean_ctor_get(v_val_3269_, 0);
lean_inc(v_userInfo_3270_);
v_host_3271_ = lean_ctor_get(v_val_3269_, 1);
lean_inc_ref(v_host_3271_);
v_port_3272_ = lean_ctor_get(v_val_3269_, 2);
lean_inc(v_port_3272_);
lean_dec(v_val_3269_);
v___x_3273_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3270_) == 0)
{
lean_object* v___x_3302_; 
v___x_3302_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3292_ = v___x_3302_;
goto v___jp_3291_;
}
else
{
lean_object* v_val_3303_; lean_object* v_password_3304_; 
v_val_3303_ = lean_ctor_get(v_userInfo_3270_, 0);
lean_inc(v_val_3303_);
lean_dec_ref_known(v_userInfo_3270_, 1);
v_password_3304_ = lean_ctor_get(v_val_3303_, 1);
if (lean_obj_tag(v_password_3304_) == 0)
{
lean_object* v_username_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v_username_3305_ = lean_ctor_get(v_val_3303_, 0);
lean_inc_ref(v_username_3305_);
lean_dec(v_val_3303_);
v___x_3306_ = lean_string_from_utf8_unchecked(v_username_3305_);
v___x_3307_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3308_ = lean_string_append(v___x_3306_, v___x_3307_);
v___y_3292_ = v___x_3308_;
goto v___jp_3291_;
}
else
{
lean_object* v_username_3309_; lean_object* v_val_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
lean_inc_ref(v_password_3304_);
v_username_3309_ = lean_ctor_get(v_val_3303_, 0);
lean_inc_ref(v_username_3309_);
lean_dec(v_val_3303_);
v_val_3310_ = lean_ctor_get(v_password_3304_, 0);
lean_inc(v_val_3310_);
lean_dec_ref_known(v_password_3304_, 1);
v___x_3311_ = lean_string_from_utf8_unchecked(v_username_3309_);
v___x_3312_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3313_ = lean_string_append(v___x_3311_, v___x_3312_);
v___x_3314_ = lean_string_from_utf8_unchecked(v_val_3310_);
v___x_3315_ = lean_string_append(v___x_3313_, v___x_3314_);
lean_dec_ref(v___x_3314_);
v___x_3316_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3317_ = lean_string_append(v___x_3315_, v___x_3316_);
v___y_3292_ = v___x_3317_;
goto v___jp_3291_;
}
}
v___jp_3274_:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3278_ = lean_string_append(v___y_3275_, v___y_3276_);
lean_dec_ref(v___y_3276_);
v___x_3279_ = lean_string_append(v___x_3278_, v___y_3277_);
lean_dec_ref(v___y_3277_);
v___x_3280_ = lean_string_append(v___x_3273_, v___x_3279_);
lean_dec_ref(v___x_3279_);
v___y_3257_ = v___x_3280_;
goto v___jp_3256_;
}
v___jp_3281_:
{
switch(lean_obj_tag(v_port_3272_))
{
case 0:
{
lean_object* v___x_3284_; 
v___x_3284_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3275_ = v___y_3282_;
v___y_3276_ = v___y_3283_;
v___y_3277_ = v___x_3284_;
goto v___jp_3274_;
}
case 1:
{
lean_object* v___x_3285_; 
v___x_3285_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3275_ = v___y_3282_;
v___y_3276_ = v___y_3283_;
v___y_3277_ = v___x_3285_;
goto v___jp_3274_;
}
default: 
{
uint16_t v_port_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_port_3286_ = lean_ctor_get_uint16(v_port_3272_, 0);
lean_dec_ref_known(v_port_3272_, 0);
v___x_3287_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3288_ = lean_uint16_to_nat(v_port_3286_);
v___x_3289_ = l_Nat_reprFast(v___x_3288_);
v___x_3290_ = lean_string_append(v___x_3287_, v___x_3289_);
lean_dec_ref(v___x_3289_);
v___y_3275_ = v___y_3282_;
v___y_3276_ = v___y_3283_;
v___y_3277_ = v___x_3290_;
goto v___jp_3274_;
}
}
}
v___jp_3291_:
{
switch(lean_obj_tag(v_host_3271_))
{
case 0:
{
lean_object* v_name_3293_; 
v_name_3293_ = lean_ctor_get(v_host_3271_, 0);
lean_inc_ref(v_name_3293_);
lean_dec_ref_known(v_host_3271_, 1);
v___y_3282_ = v___y_3292_;
v___y_3283_ = v_name_3293_;
goto v___jp_3281_;
}
case 1:
{
lean_object* v_ipv4_3294_; lean_object* v___x_3295_; 
v_ipv4_3294_ = lean_ctor_get(v_host_3271_, 0);
lean_inc_ref(v_ipv4_3294_);
lean_dec_ref_known(v_host_3271_, 1);
v___x_3295_ = lean_uv_ntop_v4(v_ipv4_3294_);
lean_dec_ref(v_ipv4_3294_);
v___y_3282_ = v___y_3292_;
v___y_3283_ = v___x_3295_;
goto v___jp_3281_;
}
default: 
{
lean_object* v_ipv6_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v_ipv6_3296_ = lean_ctor_get(v_host_3271_, 0);
lean_inc_ref(v_ipv6_3296_);
lean_dec_ref_known(v_host_3271_, 1);
v___x_3297_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3298_ = lean_uv_ntop_v6(v_ipv6_3296_);
lean_dec_ref(v_ipv6_3296_);
v___x_3299_ = lean_string_append(v___x_3297_, v___x_3298_);
lean_dec_ref(v___x_3298_);
v___x_3300_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3301_ = lean_string_append(v___x_3299_, v___x_3300_);
v___y_3282_ = v___y_3292_;
v___y_3283_ = v___x_3301_;
goto v___jp_3281_;
}
}
}
}
v___jp_3234_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = lean_string_append(v___y_3237_, v___y_3236_);
lean_dec_ref(v___y_3236_);
v___x_3240_ = lean_string_append(v___x_3239_, v___y_3235_);
lean_dec_ref(v___y_3235_);
v___x_3241_ = lean_string_append(v___x_3240_, v___y_3238_);
lean_dec_ref(v___y_3238_);
return v___x_3241_;
}
v___jp_3246_:
{
lean_object* v_queryPart_3249_; 
v_queryPart_3249_ = l_Std_Http_URI_Query_formatOption(v_query_3244_);
if (lean_obj_tag(v_fragment_3245_) == 0)
{
lean_object* v___x_3250_; 
v___x_3250_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3235_ = v_queryPart_3249_;
v___y_3236_ = v___y_3248_;
v___y_3237_ = v___y_3247_;
v___y_3238_ = v___x_3250_;
goto v___jp_3234_;
}
else
{
lean_object* v_val_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v_val_3251_ = lean_ctor_get(v_fragment_3245_, 0);
lean_inc(v_val_3251_);
lean_dec_ref_known(v_fragment_3245_, 1);
v___x_3252_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3253_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3251_);
lean_dec(v_val_3251_);
v___x_3254_ = lean_string_from_utf8_unchecked(v___x_3253_);
v___x_3255_ = lean_string_append(v___x_3252_, v___x_3254_);
lean_dec_ref(v___x_3254_);
v___y_3235_ = v_queryPart_3249_;
v___y_3236_ = v___y_3248_;
v___y_3237_ = v___y_3247_;
v___y_3238_ = v___x_3255_;
goto v___jp_3234_;
}
}
v___jp_3256_:
{
lean_object* v_segments_3258_; uint8_t v_absolute_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; size_t v_sz_3262_; size_t v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v_result_3266_; 
v_segments_3258_ = lean_ctor_get(v_path_3243_, 0);
lean_inc_ref(v_segments_3258_);
v_absolute_3259_ = lean_ctor_get_uint8(v_path_3243_, sizeof(void*)*1);
lean_dec_ref(v_path_3243_);
v___x_3260_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3261_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3262_ = lean_array_size(v_segments_3258_);
v___x_3263_ = ((size_t)0ULL);
v___x_3264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3261_, v___f_3232_, v_sz_3262_, v___x_3263_, v_segments_3258_);
v___x_3265_ = lean_array_to_list(v___x_3264_);
v_result_3266_ = l_String_intercalate(v___x_3260_, v___x_3265_);
if (v_absolute_3259_ == 0)
{
v___y_3247_ = v___y_3257_;
v___y_3248_ = v_result_3266_;
goto v___jp_3246_;
}
else
{
lean_object* v___x_3267_; 
v___x_3267_ = lean_string_append(v___x_3260_, v_result_3266_);
lean_dec_ref(v_result_3266_);
v___y_3247_ = v___y_3257_;
v___y_3248_ = v___x_3267_;
goto v___jp_3246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx(lean_object* v_x_3321_){
_start:
{
if (lean_obj_tag(v_x_3321_) == 0)
{
lean_object* v___x_3322_; 
v___x_3322_ = lean_unsigned_to_nat(0u);
return v___x_3322_;
}
else
{
lean_object* v___x_3323_; 
v___x_3323_ = lean_unsigned_to_nat(1u);
return v___x_3323_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___boxed(lean_object* v_x_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_Std_Http_URIReference_ctorIdx(v_x_3324_);
lean_dec_ref(v_x_3324_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___redArg(lean_object* v_t_3326_, lean_object* v_k_3327_){
_start:
{
lean_object* v_uri_3328_; lean_object* v___x_3329_; 
v_uri_3328_ = lean_ctor_get(v_t_3326_, 0);
lean_inc_ref(v_uri_3328_);
lean_dec_ref(v_t_3326_);
v___x_3329_ = lean_apply_1(v_k_3327_, v_uri_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim(lean_object* v_motive_3330_, lean_object* v_ctorIdx_3331_, lean_object* v_t_3332_, lean_object* v_h_3333_, lean_object* v_k_3334_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3332_, v_k_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___boxed(lean_object* v_motive_3336_, lean_object* v_ctorIdx_3337_, lean_object* v_t_3338_, lean_object* v_h_3339_, lean_object* v_k_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l_Std_Http_URIReference_ctorElim(v_motive_3336_, v_ctorIdx_3337_, v_t_3338_, v_h_3339_, v_k_3340_);
lean_dec(v_ctorIdx_3337_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim___redArg(lean_object* v_t_3342_, lean_object* v_absolute_3343_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3342_, v_absolute_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim(lean_object* v_motive_3345_, lean_object* v_t_3346_, lean_object* v_h_3347_, lean_object* v_absolute_3348_){
_start:
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3346_, v_absolute_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim___redArg(lean_object* v_t_3350_, lean_object* v_relative_3351_){
_start:
{
lean_object* v___x_3352_; 
v___x_3352_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3350_, v_relative_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim(lean_object* v_motive_3353_, lean_object* v_t_3354_, lean_object* v_h_3355_, lean_object* v_relative_3356_){
_start:
{
lean_object* v___x_3357_; 
v___x_3357_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3354_, v_relative_3356_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr(lean_object* v_x_3370_, lean_object* v_prec_3371_){
_start:
{
if (lean_obj_tag(v_x_3370_) == 0)
{
lean_object* v_uri_3372_; lean_object* v___y_3374_; lean_object* v___x_3382_; uint8_t v___x_3383_; 
v_uri_3372_ = lean_ctor_get(v_x_3370_, 0);
lean_inc_ref(v_uri_3372_);
lean_dec_ref_known(v_x_3370_, 1);
v___x_3382_ = lean_unsigned_to_nat(1024u);
v___x_3383_ = lean_nat_dec_le(v___x_3382_, v_prec_3371_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; 
v___x_3384_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3374_ = v___x_3384_;
goto v___jp_3373_;
}
else
{
lean_object* v___x_3385_; 
v___x_3385_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3374_ = v___x_3385_;
goto v___jp_3373_;
}
v___jp_3373_:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3375_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__2));
v___x_3376_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3372_);
v___x_3377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3375_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
lean_inc(v___y_3374_);
v___x_3378_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___y_3374_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v___x_3379_ = 0;
v___x_3380_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3380_, 0, v___x_3378_);
lean_ctor_set_uint8(v___x_3380_, sizeof(void*)*1, v___x_3379_);
v___x_3381_ = l_Repr_addAppParen(v___x_3380_, v_prec_3371_);
return v___x_3381_;
}
}
else
{
lean_object* v_ref_3386_; lean_object* v___y_3388_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v_ref_3386_ = lean_ctor_get(v_x_3370_, 0);
lean_inc_ref(v_ref_3386_);
lean_dec_ref_known(v_x_3370_, 1);
v___x_3396_ = lean_unsigned_to_nat(1024u);
v___x_3397_ = lean_nat_dec_le(v___x_3396_, v_prec_3371_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; 
v___x_3398_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3388_ = v___x_3398_;
goto v___jp_3387_;
}
else
{
lean_object* v___x_3399_; 
v___x_3399_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3388_ = v___x_3399_;
goto v___jp_3387_;
}
v___jp_3387_:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; uint8_t v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3389_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__5));
v___x_3390_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_ref_3386_);
v___x_3391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3389_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
lean_inc(v___y_3388_);
v___x_3392_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___y_3388_);
lean_ctor_set(v___x_3392_, 1, v___x_3391_);
v___x_3393_ = 0;
v___x_3394_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3394_, 0, v___x_3392_);
lean_ctor_set_uint8(v___x_3394_, sizeof(void*)*1, v___x_3393_);
v___x_3395_ = l_Repr_addAppParen(v___x_3394_, v_prec_3371_);
return v___x_3395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr___boxed(lean_object* v_x_3400_, lean_object* v_prec_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Std_Http_instReprURIReference_repr(v_x_3400_, v_prec_3401_);
lean_dec(v_prec_3401_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURIReference___lam__2(lean_object* v___f_3409_, lean_object* v___f_3410_, lean_object* v_x_3411_){
_start:
{
lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; 
if (lean_obj_tag(v_x_3411_) == 0)
{
lean_object* v_uri_3420_; lean_object* v_scheme_3421_; lean_object* v_authority_3422_; lean_object* v_path_3423_; lean_object* v_query_3424_; lean_object* v_fragment_3425_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3448_; 
lean_dec_ref(v___f_3410_);
v_uri_3420_ = lean_ctor_get(v_x_3411_, 0);
lean_inc_ref(v_uri_3420_);
lean_dec_ref_known(v_x_3411_, 1);
v_scheme_3421_ = lean_ctor_get(v_uri_3420_, 0);
lean_inc_ref(v_scheme_3421_);
v_authority_3422_ = lean_ctor_get(v_uri_3420_, 1);
lean_inc(v_authority_3422_);
v_path_3423_ = lean_ctor_get(v_uri_3420_, 2);
lean_inc_ref(v_path_3423_);
v_query_3424_ = lean_ctor_get(v_uri_3420_, 3);
lean_inc(v_query_3424_);
v_fragment_3425_ = lean_ctor_get(v_uri_3420_, 4);
lean_inc(v_fragment_3425_);
lean_dec_ref(v_uri_3420_);
if (lean_obj_tag(v_authority_3422_) == 0)
{
lean_object* v___x_3459_; 
v___x_3459_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3448_ = v___x_3459_;
goto v___jp_3447_;
}
else
{
lean_object* v_val_3460_; lean_object* v_userInfo_3461_; lean_object* v_host_3462_; lean_object* v_port_3463_; lean_object* v___x_3464_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3483_; 
v_val_3460_ = lean_ctor_get(v_authority_3422_, 0);
lean_inc(v_val_3460_);
lean_dec_ref_known(v_authority_3422_, 1);
v_userInfo_3461_ = lean_ctor_get(v_val_3460_, 0);
lean_inc(v_userInfo_3461_);
v_host_3462_ = lean_ctor_get(v_val_3460_, 1);
lean_inc_ref(v_host_3462_);
v_port_3463_ = lean_ctor_get(v_val_3460_, 2);
lean_inc(v_port_3463_);
lean_dec(v_val_3460_);
v___x_3464_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3461_) == 0)
{
lean_object* v___x_3493_; 
v___x_3493_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3483_ = v___x_3493_;
goto v___jp_3482_;
}
else
{
lean_object* v_val_3494_; lean_object* v_password_3495_; 
v_val_3494_ = lean_ctor_get(v_userInfo_3461_, 0);
lean_inc(v_val_3494_);
lean_dec_ref_known(v_userInfo_3461_, 1);
v_password_3495_ = lean_ctor_get(v_val_3494_, 1);
if (lean_obj_tag(v_password_3495_) == 0)
{
lean_object* v_username_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v_username_3496_ = lean_ctor_get(v_val_3494_, 0);
lean_inc_ref(v_username_3496_);
lean_dec(v_val_3494_);
v___x_3497_ = lean_string_from_utf8_unchecked(v_username_3496_);
v___x_3498_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3499_ = lean_string_append(v___x_3497_, v___x_3498_);
v___y_3483_ = v___x_3499_;
goto v___jp_3482_;
}
else
{
lean_object* v_username_3500_; lean_object* v_val_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
lean_inc_ref(v_password_3495_);
v_username_3500_ = lean_ctor_get(v_val_3494_, 0);
lean_inc_ref(v_username_3500_);
lean_dec(v_val_3494_);
v_val_3501_ = lean_ctor_get(v_password_3495_, 0);
lean_inc(v_val_3501_);
lean_dec_ref_known(v_password_3495_, 1);
v___x_3502_ = lean_string_from_utf8_unchecked(v_username_3500_);
v___x_3503_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3504_ = lean_string_append(v___x_3502_, v___x_3503_);
v___x_3505_ = lean_string_from_utf8_unchecked(v_val_3501_);
v___x_3506_ = lean_string_append(v___x_3504_, v___x_3505_);
lean_dec_ref(v___x_3505_);
v___x_3507_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3508_ = lean_string_append(v___x_3506_, v___x_3507_);
v___y_3483_ = v___x_3508_;
goto v___jp_3482_;
}
}
v___jp_3465_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3469_ = lean_string_append(v___y_3467_, v___y_3466_);
lean_dec_ref(v___y_3466_);
v___x_3470_ = lean_string_append(v___x_3469_, v___y_3468_);
lean_dec_ref(v___y_3468_);
v___x_3471_ = lean_string_append(v___x_3464_, v___x_3470_);
lean_dec_ref(v___x_3470_);
v___y_3448_ = v___x_3471_;
goto v___jp_3447_;
}
v___jp_3472_:
{
switch(lean_obj_tag(v_port_3463_))
{
case 0:
{
lean_object* v___x_3475_; 
v___x_3475_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3466_ = v___y_3474_;
v___y_3467_ = v___y_3473_;
v___y_3468_ = v___x_3475_;
goto v___jp_3465_;
}
case 1:
{
lean_object* v___x_3476_; 
v___x_3476_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3466_ = v___y_3474_;
v___y_3467_ = v___y_3473_;
v___y_3468_ = v___x_3476_;
goto v___jp_3465_;
}
default: 
{
uint16_t v_port_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v_port_3477_ = lean_ctor_get_uint16(v_port_3463_, 0);
lean_dec_ref_known(v_port_3463_, 0);
v___x_3478_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3479_ = lean_uint16_to_nat(v_port_3477_);
v___x_3480_ = l_Nat_reprFast(v___x_3479_);
v___x_3481_ = lean_string_append(v___x_3478_, v___x_3480_);
lean_dec_ref(v___x_3480_);
v___y_3466_ = v___y_3474_;
v___y_3467_ = v___y_3473_;
v___y_3468_ = v___x_3481_;
goto v___jp_3465_;
}
}
}
v___jp_3482_:
{
switch(lean_obj_tag(v_host_3462_))
{
case 0:
{
lean_object* v_name_3484_; 
v_name_3484_ = lean_ctor_get(v_host_3462_, 0);
lean_inc_ref(v_name_3484_);
lean_dec_ref_known(v_host_3462_, 1);
v___y_3473_ = v___y_3483_;
v___y_3474_ = v_name_3484_;
goto v___jp_3472_;
}
case 1:
{
lean_object* v_ipv4_3485_; lean_object* v___x_3486_; 
v_ipv4_3485_ = lean_ctor_get(v_host_3462_, 0);
lean_inc_ref(v_ipv4_3485_);
lean_dec_ref_known(v_host_3462_, 1);
v___x_3486_ = lean_uv_ntop_v4(v_ipv4_3485_);
lean_dec_ref(v_ipv4_3485_);
v___y_3473_ = v___y_3483_;
v___y_3474_ = v___x_3486_;
goto v___jp_3472_;
}
default: 
{
lean_object* v_ipv6_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v_ipv6_3487_ = lean_ctor_get(v_host_3462_, 0);
lean_inc_ref(v_ipv6_3487_);
lean_dec_ref_known(v_host_3462_, 1);
v___x_3488_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3489_ = lean_uv_ntop_v6(v_ipv6_3487_);
lean_dec_ref(v_ipv6_3487_);
v___x_3490_ = lean_string_append(v___x_3488_, v___x_3489_);
lean_dec_ref(v___x_3489_);
v___x_3491_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3492_ = lean_string_append(v___x_3490_, v___x_3491_);
v___y_3473_ = v___y_3483_;
v___y_3474_ = v___x_3492_;
goto v___jp_3472_;
}
}
}
}
v___jp_3426_:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3431_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3432_ = lean_string_append(v_scheme_3421_, v___x_3431_);
v___x_3433_ = lean_string_append(v___x_3432_, v___y_3428_);
lean_dec_ref(v___y_3428_);
v___x_3434_ = lean_string_append(v___x_3433_, v___y_3429_);
lean_dec_ref(v___y_3429_);
v___x_3435_ = lean_string_append(v___x_3434_, v___y_3427_);
lean_dec_ref(v___y_3427_);
v___x_3436_ = lean_string_append(v___x_3435_, v___y_3430_);
lean_dec_ref(v___y_3430_);
return v___x_3436_;
}
v___jp_3437_:
{
lean_object* v_queryPart_3440_; 
v_queryPart_3440_ = l_Std_Http_URI_Query_formatOption(v_query_3424_);
if (lean_obj_tag(v_fragment_3425_) == 0)
{
lean_object* v___x_3441_; 
v___x_3441_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3427_ = v_queryPart_3440_;
v___y_3428_ = v___y_3438_;
v___y_3429_ = v___y_3439_;
v___y_3430_ = v___x_3441_;
goto v___jp_3426_;
}
else
{
lean_object* v_val_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v_val_3442_ = lean_ctor_get(v_fragment_3425_, 0);
lean_inc(v_val_3442_);
lean_dec_ref_known(v_fragment_3425_, 1);
v___x_3443_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3444_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3442_);
lean_dec(v_val_3442_);
v___x_3445_ = lean_string_from_utf8_unchecked(v___x_3444_);
v___x_3446_ = lean_string_append(v___x_3443_, v___x_3445_);
lean_dec_ref(v___x_3445_);
v___y_3427_ = v_queryPart_3440_;
v___y_3428_ = v___y_3438_;
v___y_3429_ = v___y_3439_;
v___y_3430_ = v___x_3446_;
goto v___jp_3426_;
}
}
v___jp_3447_:
{
lean_object* v_segments_3449_; uint8_t v_absolute_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; size_t v_sz_3453_; size_t v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v_result_3457_; 
v_segments_3449_ = lean_ctor_get(v_path_3423_, 0);
lean_inc_ref(v_segments_3449_);
v_absolute_3450_ = lean_ctor_get_uint8(v_path_3423_, sizeof(void*)*1);
lean_dec_ref(v_path_3423_);
v___x_3451_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3452_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3453_ = lean_array_size(v_segments_3449_);
v___x_3454_ = ((size_t)0ULL);
v___x_3455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3452_, v___f_3409_, v_sz_3453_, v___x_3454_, v_segments_3449_);
v___x_3456_ = lean_array_to_list(v___x_3455_);
v_result_3457_ = l_String_intercalate(v___x_3451_, v___x_3456_);
if (v_absolute_3450_ == 0)
{
v___y_3438_ = v___y_3448_;
v___y_3439_ = v_result_3457_;
goto v___jp_3437_;
}
else
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_string_append(v___x_3451_, v_result_3457_);
lean_dec_ref(v_result_3457_);
v___y_3438_ = v___y_3448_;
v___y_3439_ = v___x_3458_;
goto v___jp_3437_;
}
}
}
else
{
lean_object* v_ref_3509_; lean_object* v_authority_3510_; lean_object* v_path_3511_; lean_object* v_query_3512_; lean_object* v_fragment_3513_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3525_; 
lean_dec_ref(v___f_3409_);
v_ref_3509_ = lean_ctor_get(v_x_3411_, 0);
lean_inc_ref(v_ref_3509_);
lean_dec_ref_known(v_x_3411_, 1);
v_authority_3510_ = lean_ctor_get(v_ref_3509_, 0);
lean_inc(v_authority_3510_);
v_path_3511_ = lean_ctor_get(v_ref_3509_, 1);
lean_inc_ref(v_path_3511_);
v_query_3512_ = lean_ctor_get(v_ref_3509_, 2);
lean_inc(v_query_3512_);
v_fragment_3513_ = lean_ctor_get(v_ref_3509_, 3);
lean_inc(v_fragment_3513_);
lean_dec_ref(v_ref_3509_);
if (lean_obj_tag(v_authority_3510_) == 0)
{
lean_object* v___x_3536_; 
v___x_3536_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3525_ = v___x_3536_;
goto v___jp_3524_;
}
else
{
lean_object* v_val_3537_; lean_object* v_userInfo_3538_; lean_object* v_host_3539_; lean_object* v_port_3540_; lean_object* v___x_3541_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3560_; 
v_val_3537_ = lean_ctor_get(v_authority_3510_, 0);
lean_inc(v_val_3537_);
lean_dec_ref_known(v_authority_3510_, 1);
v_userInfo_3538_ = lean_ctor_get(v_val_3537_, 0);
lean_inc(v_userInfo_3538_);
v_host_3539_ = lean_ctor_get(v_val_3537_, 1);
lean_inc_ref(v_host_3539_);
v_port_3540_ = lean_ctor_get(v_val_3537_, 2);
lean_inc(v_port_3540_);
lean_dec(v_val_3537_);
v___x_3541_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3538_) == 0)
{
lean_object* v___x_3570_; 
v___x_3570_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3560_ = v___x_3570_;
goto v___jp_3559_;
}
else
{
lean_object* v_val_3571_; lean_object* v_password_3572_; 
v_val_3571_ = lean_ctor_get(v_userInfo_3538_, 0);
lean_inc(v_val_3571_);
lean_dec_ref_known(v_userInfo_3538_, 1);
v_password_3572_ = lean_ctor_get(v_val_3571_, 1);
if (lean_obj_tag(v_password_3572_) == 0)
{
lean_object* v_username_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v_username_3573_ = lean_ctor_get(v_val_3571_, 0);
lean_inc_ref(v_username_3573_);
lean_dec(v_val_3571_);
v___x_3574_ = lean_string_from_utf8_unchecked(v_username_3573_);
v___x_3575_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3576_ = lean_string_append(v___x_3574_, v___x_3575_);
v___y_3560_ = v___x_3576_;
goto v___jp_3559_;
}
else
{
lean_object* v_username_3577_; lean_object* v_val_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
lean_inc_ref(v_password_3572_);
v_username_3577_ = lean_ctor_get(v_val_3571_, 0);
lean_inc_ref(v_username_3577_);
lean_dec(v_val_3571_);
v_val_3578_ = lean_ctor_get(v_password_3572_, 0);
lean_inc(v_val_3578_);
lean_dec_ref_known(v_password_3572_, 1);
v___x_3579_ = lean_string_from_utf8_unchecked(v_username_3577_);
v___x_3580_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3581_ = lean_string_append(v___x_3579_, v___x_3580_);
v___x_3582_ = lean_string_from_utf8_unchecked(v_val_3578_);
v___x_3583_ = lean_string_append(v___x_3581_, v___x_3582_);
lean_dec_ref(v___x_3582_);
v___x_3584_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3585_ = lean_string_append(v___x_3583_, v___x_3584_);
v___y_3560_ = v___x_3585_;
goto v___jp_3559_;
}
}
v___jp_3542_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3546_ = lean_string_append(v___y_3544_, v___y_3543_);
lean_dec_ref(v___y_3543_);
v___x_3547_ = lean_string_append(v___x_3546_, v___y_3545_);
lean_dec_ref(v___y_3545_);
v___x_3548_ = lean_string_append(v___x_3541_, v___x_3547_);
lean_dec_ref(v___x_3547_);
v___y_3525_ = v___x_3548_;
goto v___jp_3524_;
}
v___jp_3549_:
{
switch(lean_obj_tag(v_port_3540_))
{
case 0:
{
lean_object* v___x_3552_; 
v___x_3552_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3543_ = v___y_3551_;
v___y_3544_ = v___y_3550_;
v___y_3545_ = v___x_3552_;
goto v___jp_3542_;
}
case 1:
{
lean_object* v___x_3553_; 
v___x_3553_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3543_ = v___y_3551_;
v___y_3544_ = v___y_3550_;
v___y_3545_ = v___x_3553_;
goto v___jp_3542_;
}
default: 
{
uint16_t v_port_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v_port_3554_ = lean_ctor_get_uint16(v_port_3540_, 0);
lean_dec_ref_known(v_port_3540_, 0);
v___x_3555_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3556_ = lean_uint16_to_nat(v_port_3554_);
v___x_3557_ = l_Nat_reprFast(v___x_3556_);
v___x_3558_ = lean_string_append(v___x_3555_, v___x_3557_);
lean_dec_ref(v___x_3557_);
v___y_3543_ = v___y_3551_;
v___y_3544_ = v___y_3550_;
v___y_3545_ = v___x_3558_;
goto v___jp_3542_;
}
}
}
v___jp_3559_:
{
switch(lean_obj_tag(v_host_3539_))
{
case 0:
{
lean_object* v_name_3561_; 
v_name_3561_ = lean_ctor_get(v_host_3539_, 0);
lean_inc_ref(v_name_3561_);
lean_dec_ref_known(v_host_3539_, 1);
v___y_3550_ = v___y_3560_;
v___y_3551_ = v_name_3561_;
goto v___jp_3549_;
}
case 1:
{
lean_object* v_ipv4_3562_; lean_object* v___x_3563_; 
v_ipv4_3562_ = lean_ctor_get(v_host_3539_, 0);
lean_inc_ref(v_ipv4_3562_);
lean_dec_ref_known(v_host_3539_, 1);
v___x_3563_ = lean_uv_ntop_v4(v_ipv4_3562_);
lean_dec_ref(v_ipv4_3562_);
v___y_3550_ = v___y_3560_;
v___y_3551_ = v___x_3563_;
goto v___jp_3549_;
}
default: 
{
lean_object* v_ipv6_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v_ipv6_3564_ = lean_ctor_get(v_host_3539_, 0);
lean_inc_ref(v_ipv6_3564_);
lean_dec_ref_known(v_host_3539_, 1);
v___x_3565_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3566_ = lean_uv_ntop_v6(v_ipv6_3564_);
lean_dec_ref(v_ipv6_3564_);
v___x_3567_ = lean_string_append(v___x_3565_, v___x_3566_);
lean_dec_ref(v___x_3566_);
v___x_3568_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3569_ = lean_string_append(v___x_3567_, v___x_3568_);
v___y_3550_ = v___y_3560_;
v___y_3551_ = v___x_3569_;
goto v___jp_3549_;
}
}
}
}
v___jp_3514_:
{
lean_object* v_queryPart_3517_; 
v_queryPart_3517_ = l_Std_Http_URI_Query_formatOption(v_query_3512_);
if (lean_obj_tag(v_fragment_3513_) == 0)
{
lean_object* v___x_3518_; 
v___x_3518_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3413_ = v_queryPart_3517_;
v___y_3414_ = v___y_3516_;
v___y_3415_ = v___y_3515_;
v___y_3416_ = v___x_3518_;
goto v___jp_3412_;
}
else
{
lean_object* v_val_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v_val_3519_ = lean_ctor_get(v_fragment_3513_, 0);
lean_inc(v_val_3519_);
lean_dec_ref_known(v_fragment_3513_, 1);
v___x_3520_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3521_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3519_);
lean_dec(v_val_3519_);
v___x_3522_ = lean_string_from_utf8_unchecked(v___x_3521_);
v___x_3523_ = lean_string_append(v___x_3520_, v___x_3522_);
lean_dec_ref(v___x_3522_);
v___y_3413_ = v_queryPart_3517_;
v___y_3414_ = v___y_3516_;
v___y_3415_ = v___y_3515_;
v___y_3416_ = v___x_3523_;
goto v___jp_3412_;
}
}
v___jp_3524_:
{
lean_object* v_segments_3526_; uint8_t v_absolute_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; size_t v_sz_3530_; size_t v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v_result_3534_; 
v_segments_3526_ = lean_ctor_get(v_path_3511_, 0);
lean_inc_ref(v_segments_3526_);
v_absolute_3527_ = lean_ctor_get_uint8(v_path_3511_, sizeof(void*)*1);
lean_dec_ref(v_path_3511_);
v___x_3528_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3529_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3530_ = lean_array_size(v_segments_3526_);
v___x_3531_ = ((size_t)0ULL);
v___x_3532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3529_, v___f_3410_, v_sz_3530_, v___x_3531_, v_segments_3526_);
v___x_3533_ = lean_array_to_list(v___x_3532_);
v_result_3534_ = l_String_intercalate(v___x_3528_, v___x_3533_);
if (v_absolute_3527_ == 0)
{
v___y_3515_ = v___y_3525_;
v___y_3516_ = v_result_3534_;
goto v___jp_3514_;
}
else
{
lean_object* v___x_3535_; 
v___x_3535_ = lean_string_append(v___x_3528_, v_result_3534_);
lean_dec_ref(v_result_3534_);
v___y_3515_ = v___y_3525_;
v___y_3516_ = v___x_3535_;
goto v___jp_3514_;
}
}
}
v___jp_3412_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3417_ = lean_string_append(v___y_3415_, v___y_3414_);
lean_dec_ref(v___y_3414_);
v___x_3418_ = lean_string_append(v___x_3417_, v___y_3413_);
lean_dec_ref(v___y_3413_);
v___x_3419_ = lean_string_append(v___x_3418_, v___y_3416_);
lean_dec_ref(v___y_3416_);
return v___x_3419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx(lean_object* v_x_3589_){
_start:
{
switch(lean_obj_tag(v_x_3589_))
{
case 0:
{
lean_object* v___x_3590_; 
v___x_3590_ = lean_unsigned_to_nat(0u);
return v___x_3590_;
}
case 1:
{
lean_object* v___x_3591_; 
v___x_3591_ = lean_unsigned_to_nat(1u);
return v___x_3591_;
}
case 2:
{
lean_object* v___x_3592_; 
v___x_3592_ = lean_unsigned_to_nat(2u);
return v___x_3592_;
}
default: 
{
lean_object* v___x_3593_; 
v___x_3593_ = lean_unsigned_to_nat(3u);
return v___x_3593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___boxed(lean_object* v_x_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Std_Http_RequestTarget_ctorIdx(v_x_3594_);
lean_dec(v_x_3594_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___redArg(lean_object* v_t_3596_, lean_object* v_k_3597_){
_start:
{
switch(lean_obj_tag(v_t_3596_))
{
case 0:
{
lean_object* v_path_3598_; lean_object* v_query_3599_; lean_object* v___x_3600_; 
v_path_3598_ = lean_ctor_get(v_t_3596_, 0);
lean_inc_ref(v_path_3598_);
v_query_3599_ = lean_ctor_get(v_t_3596_, 1);
lean_inc(v_query_3599_);
lean_dec_ref_known(v_t_3596_, 2);
v___x_3600_ = lean_apply_2(v_k_3597_, v_path_3598_, v_query_3599_);
return v___x_3600_;
}
case 3:
{
return v_k_3597_;
}
default: 
{
lean_object* v_uri_3601_; lean_object* v___x_3602_; 
v_uri_3601_ = lean_ctor_get(v_t_3596_, 0);
lean_inc_ref(v_uri_3601_);
lean_dec(v_t_3596_);
v___x_3602_ = lean_apply_1(v_k_3597_, v_uri_3601_);
return v___x_3602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim(lean_object* v_motive_3603_, lean_object* v_ctorIdx_3604_, lean_object* v_t_3605_, lean_object* v_h_3606_, lean_object* v_k_3607_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3605_, v_k_3607_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___boxed(lean_object* v_motive_3609_, lean_object* v_ctorIdx_3610_, lean_object* v_t_3611_, lean_object* v_h_3612_, lean_object* v_k_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Std_Http_RequestTarget_ctorElim(v_motive_3609_, v_ctorIdx_3610_, v_t_3611_, v_h_3612_, v_k_3613_);
lean_dec(v_ctorIdx_3610_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim___redArg(lean_object* v_t_3615_, lean_object* v_originForm_3616_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3615_, v_originForm_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim(lean_object* v_motive_3618_, lean_object* v_t_3619_, lean_object* v_h_3620_, lean_object* v_originForm_3621_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3619_, v_originForm_3621_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim___redArg(lean_object* v_t_3623_, lean_object* v_absoluteForm_3624_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3623_, v_absoluteForm_3624_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim(lean_object* v_motive_3626_, lean_object* v_t_3627_, lean_object* v_h_3628_, lean_object* v_absoluteForm_3629_){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3627_, v_absoluteForm_3629_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim___redArg(lean_object* v_t_3631_, lean_object* v_authorityForm_3632_){
_start:
{
lean_object* v___x_3633_; 
v___x_3633_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3631_, v_authorityForm_3632_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim(lean_object* v_motive_3634_, lean_object* v_t_3635_, lean_object* v_h_3636_, lean_object* v_authorityForm_3637_){
_start:
{
lean_object* v___x_3638_; 
v___x_3638_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3635_, v_authorityForm_3637_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim___redArg(lean_object* v_t_3639_, lean_object* v_asteriskForm_3640_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3639_, v_asteriskForm_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim(lean_object* v_motive_3642_, lean_object* v_t_3643_, lean_object* v_h_3644_, lean_object* v_asteriskForm_3645_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3643_, v_asteriskForm_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object* v_x_3673_, lean_object* v_prec_3674_){
_start:
{
lean_object* v___y_3676_; 
switch(lean_obj_tag(v_x_3673_))
{
case 0:
{
lean_object* v_path_3682_; lean_object* v_query_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3707_; 
v_path_3682_ = lean_ctor_get(v_x_3673_, 0);
v_query_3683_ = lean_ctor_get(v_x_3673_, 1);
v_isSharedCheck_3707_ = !lean_is_exclusive(v_x_3673_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3685_ = v_x_3673_;
v_isShared_3686_ = v_isSharedCheck_3707_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_query_3683_);
lean_inc(v_path_3682_);
lean_dec(v_x_3673_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3707_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___y_3688_; lean_object* v___x_3703_; uint8_t v___x_3704_; 
v___x_3703_ = lean_unsigned_to_nat(1024u);
v___x_3704_ = lean_nat_dec_le(v___x_3703_, v_prec_3674_);
if (v___x_3704_ == 0)
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3688_ = v___x_3705_;
goto v___jp_3687_;
}
else
{
lean_object* v___x_3706_; 
v___x_3706_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3688_ = v___x_3706_;
goto v___jp_3687_;
}
v___jp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3694_; 
v___x_3689_ = lean_box(1);
v___x_3690_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__4));
v___x_3691_ = lean_unsigned_to_nat(1024u);
v___x_3692_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3682_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set_tag(v___x_3685_, 5);
lean_ctor_set(v___x_3685_, 1, v___x_3692_);
lean_ctor_set(v___x_3685_, 0, v___x_3690_);
v___x_3694_ = v___x_3685_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3702_, 1, v___x_3692_);
v___x_3694_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; uint8_t v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3694_);
lean_ctor_set(v___x_3695_, 1, v___x_3689_);
v___x_3696_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3683_, v___x_3691_);
v___x_3697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3695_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
lean_inc(v___y_3688_);
v___x_3698_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___y_3688_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
v___x_3699_ = 0;
v___x_3700_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3700_, 0, v___x_3698_);
lean_ctor_set_uint8(v___x_3700_, sizeof(void*)*1, v___x_3699_);
v___x_3701_ = l_Repr_addAppParen(v___x_3700_, v_prec_3674_);
return v___x_3701_;
}
}
}
}
case 1:
{
lean_object* v_uri_3708_; lean_object* v___y_3710_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v_uri_3708_ = lean_ctor_get(v_x_3673_, 0);
lean_inc_ref(v_uri_3708_);
lean_dec_ref_known(v_x_3673_, 1);
v___x_3718_ = lean_unsigned_to_nat(1024u);
v___x_3719_ = lean_nat_dec_le(v___x_3718_, v_prec_3674_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3710_ = v___x_3720_;
goto v___jp_3709_;
}
else
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3710_ = v___x_3721_;
goto v___jp_3709_;
}
v___jp_3709_:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; uint8_t v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3711_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__7));
v___x_3712_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3708_);
v___x_3713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3711_);
lean_ctor_set(v___x_3713_, 1, v___x_3712_);
lean_inc(v___y_3710_);
v___x_3714_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___y_3710_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = 0;
v___x_3716_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3716_, 0, v___x_3714_);
lean_ctor_set_uint8(v___x_3716_, sizeof(void*)*1, v___x_3715_);
v___x_3717_ = l_Repr_addAppParen(v___x_3716_, v_prec_3674_);
return v___x_3717_;
}
}
case 2:
{
lean_object* v_authority_3722_; lean_object* v___y_3724_; lean_object* v___x_3732_; uint8_t v___x_3733_; 
v_authority_3722_ = lean_ctor_get(v_x_3673_, 0);
lean_inc_ref(v_authority_3722_);
lean_dec_ref_known(v_x_3673_, 1);
v___x_3732_ = lean_unsigned_to_nat(1024u);
v___x_3733_ = lean_nat_dec_le(v___x_3732_, v_prec_3674_);
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
v___x_3725_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__10));
v___x_3726_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_authority_3722_);
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
v___x_3731_ = l_Repr_addAppParen(v___x_3730_, v_prec_3674_);
return v___x_3731_;
}
}
default: 
{
lean_object* v___x_3736_; uint8_t v___x_3737_; 
v___x_3736_ = lean_unsigned_to_nat(1024u);
v___x_3737_ = lean_nat_dec_le(v___x_3736_, v_prec_3674_);
if (v___x_3737_ == 0)
{
lean_object* v___x_3738_; 
v___x_3738_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3676_ = v___x_3738_;
goto v___jp_3675_;
}
else
{
lean_object* v___x_3739_; 
v___x_3739_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3676_ = v___x_3739_;
goto v___jp_3675_;
}
}
}
v___jp_3675_:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; uint8_t v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3677_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__1));
lean_inc(v___y_3676_);
v___x_3678_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3678_, 0, v___y_3676_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
v___x_3679_ = 0;
v___x_3680_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3680_, 0, v___x_3678_);
lean_ctor_set_uint8(v___x_3680_, sizeof(void*)*1, v___x_3679_);
v___x_3681_ = l_Repr_addAppParen(v___x_3680_, v_prec_3674_);
return v___x_3681_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr___boxed(lean_object* v_x_3740_, lean_object* v_prec_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Std_Http_instReprRequestTarget_repr(v_x_3740_, v_prec_3741_);
lean_dec(v_prec_3741_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path(lean_object* v_x_3750_){
_start:
{
switch(lean_obj_tag(v_x_3750_))
{
case 0:
{
lean_object* v_path_3751_; 
v_path_3751_ = lean_ctor_get(v_x_3750_, 0);
lean_inc_ref(v_path_3751_);
return v_path_3751_;
}
case 1:
{
lean_object* v_uri_3752_; lean_object* v_path_3753_; 
v_uri_3752_ = lean_ctor_get(v_x_3750_, 0);
v_path_3753_ = lean_ctor_get(v_uri_3752_, 2);
lean_inc_ref(v_path_3753_);
return v_path_3753_;
}
default: 
{
lean_object* v___x_3754_; 
v___x_3754_ = ((lean_object*)(l_Std_Http_RequestTarget_path___closed__1));
return v___x_3754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path___boxed(lean_object* v_x_3755_){
_start:
{
lean_object* v_res_3756_; 
v_res_3756_ = l_Std_Http_RequestTarget_path(v_x_3755_);
lean_dec(v_x_3755_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query(lean_object* v_x_3757_){
_start:
{
switch(lean_obj_tag(v_x_3757_))
{
case 0:
{
lean_object* v_query_3758_; 
v_query_3758_ = lean_ctor_get(v_x_3757_, 1);
if (lean_obj_tag(v_query_3758_) == 0)
{
lean_object* v___x_3759_; 
v___x_3759_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3759_;
}
else
{
lean_object* v_val_3760_; 
v_val_3760_ = lean_ctor_get(v_query_3758_, 0);
lean_inc(v_val_3760_);
return v_val_3760_;
}
}
case 1:
{
lean_object* v_uri_3761_; lean_object* v_query_3762_; 
v_uri_3761_ = lean_ctor_get(v_x_3757_, 0);
v_query_3762_ = lean_ctor_get(v_uri_3761_, 3);
if (lean_obj_tag(v_query_3762_) == 0)
{
lean_object* v___x_3763_; 
v___x_3763_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3763_;
}
else
{
lean_object* v_val_3764_; 
v_val_3764_ = lean_ctor_get(v_query_3762_, 0);
lean_inc(v_val_3764_);
return v_val_3764_;
}
}
default: 
{
lean_object* v___x_3765_; 
v___x_3765_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query___boxed(lean_object* v_x_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Std_Http_RequestTarget_query(v_x_3766_);
lean_dec(v_x_3766_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authority_x3f(lean_object* v_x_3768_){
_start:
{
switch(lean_obj_tag(v_x_3768_))
{
case 2:
{
lean_object* v_authority_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
v_authority_3769_ = lean_ctor_get(v_x_3768_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v_x_3768_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v_x_3768_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_authority_3769_);
lean_dec(v_x_3768_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
lean_ctor_set_tag(v___x_3771_, 1);
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_authority_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
case 1:
{
lean_object* v_uri_3777_; lean_object* v_authority_3778_; 
v_uri_3777_ = lean_ctor_get(v_x_3768_, 0);
lean_inc_ref(v_uri_3777_);
lean_dec_ref_known(v_x_3768_, 1);
v_authority_3778_ = lean_ctor_get(v_uri_3777_, 1);
lean_inc(v_authority_3778_);
lean_dec_ref(v_uri_3777_);
return v_authority_3778_;
}
default: 
{
lean_object* v___x_3779_; 
lean_dec(v_x_3768_);
v___x_3779_ = lean_box(0);
return v___x_3779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__2(lean_object* v___f_3781_, lean_object* v___f_3782_, lean_object* v_x_3783_){
_start:
{
lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; 
switch(lean_obj_tag(v_x_3783_))
{
case 0:
{
lean_object* v_path_3790_; lean_object* v_query_3791_; lean_object* v___y_3793_; lean_object* v_segments_3796_; uint8_t v_absolute_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; size_t v_sz_3800_; size_t v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v_result_3804_; 
lean_dec_ref(v___f_3782_);
v_path_3790_ = lean_ctor_get(v_x_3783_, 0);
lean_inc_ref(v_path_3790_);
v_query_3791_ = lean_ctor_get(v_x_3783_, 1);
lean_inc(v_query_3791_);
lean_dec_ref_known(v_x_3783_, 2);
v_segments_3796_ = lean_ctor_get(v_path_3790_, 0);
lean_inc_ref(v_segments_3796_);
v_absolute_3797_ = lean_ctor_get_uint8(v_path_3790_, sizeof(void*)*1);
lean_dec_ref(v_path_3790_);
v___x_3798_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3799_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3800_ = lean_array_size(v_segments_3796_);
v___x_3801_ = ((size_t)0ULL);
v___x_3802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3799_, v___f_3781_, v_sz_3800_, v___x_3801_, v_segments_3796_);
v___x_3803_ = lean_array_to_list(v___x_3802_);
v_result_3804_ = l_String_intercalate(v___x_3798_, v___x_3803_);
if (v_absolute_3797_ == 0)
{
v___y_3793_ = v_result_3804_;
goto v___jp_3792_;
}
else
{
lean_object* v___x_3805_; 
v___x_3805_ = lean_string_append(v___x_3798_, v_result_3804_);
lean_dec_ref(v_result_3804_);
v___y_3793_ = v___x_3805_;
goto v___jp_3792_;
}
v___jp_3792_:
{
lean_object* v_queryStr_3794_; lean_object* v___x_3795_; 
v_queryStr_3794_ = l_Std_Http_URI_Query_formatOption(v_query_3791_);
v___x_3795_ = lean_string_append(v___y_3793_, v_queryStr_3794_);
lean_dec_ref(v_queryStr_3794_);
return v___x_3795_;
}
}
case 1:
{
lean_object* v_uri_3806_; lean_object* v_scheme_3807_; lean_object* v_authority_3808_; lean_object* v_path_3809_; lean_object* v_query_3810_; lean_object* v_fragment_3811_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3834_; 
lean_dec_ref(v___f_3781_);
v_uri_3806_ = lean_ctor_get(v_x_3783_, 0);
lean_inc_ref(v_uri_3806_);
lean_dec_ref_known(v_x_3783_, 1);
v_scheme_3807_ = lean_ctor_get(v_uri_3806_, 0);
lean_inc_ref(v_scheme_3807_);
v_authority_3808_ = lean_ctor_get(v_uri_3806_, 1);
lean_inc(v_authority_3808_);
v_path_3809_ = lean_ctor_get(v_uri_3806_, 2);
lean_inc_ref(v_path_3809_);
v_query_3810_ = lean_ctor_get(v_uri_3806_, 3);
lean_inc(v_query_3810_);
v_fragment_3811_ = lean_ctor_get(v_uri_3806_, 4);
lean_inc(v_fragment_3811_);
lean_dec_ref(v_uri_3806_);
if (lean_obj_tag(v_authority_3808_) == 0)
{
lean_object* v___x_3845_; 
v___x_3845_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3834_ = v___x_3845_;
goto v___jp_3833_;
}
else
{
lean_object* v_val_3846_; lean_object* v_userInfo_3847_; lean_object* v_host_3848_; lean_object* v_port_3849_; lean_object* v___x_3850_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3869_; 
v_val_3846_ = lean_ctor_get(v_authority_3808_, 0);
lean_inc(v_val_3846_);
lean_dec_ref_known(v_authority_3808_, 1);
v_userInfo_3847_ = lean_ctor_get(v_val_3846_, 0);
lean_inc(v_userInfo_3847_);
v_host_3848_ = lean_ctor_get(v_val_3846_, 1);
lean_inc_ref(v_host_3848_);
v_port_3849_ = lean_ctor_get(v_val_3846_, 2);
lean_inc(v_port_3849_);
lean_dec(v_val_3846_);
v___x_3850_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3847_) == 0)
{
lean_object* v___x_3879_; 
v___x_3879_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3869_ = v___x_3879_;
goto v___jp_3868_;
}
else
{
lean_object* v_val_3880_; lean_object* v_password_3881_; 
v_val_3880_ = lean_ctor_get(v_userInfo_3847_, 0);
lean_inc(v_val_3880_);
lean_dec_ref_known(v_userInfo_3847_, 1);
v_password_3881_ = lean_ctor_get(v_val_3880_, 1);
if (lean_obj_tag(v_password_3881_) == 0)
{
lean_object* v_username_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v_username_3882_ = lean_ctor_get(v_val_3880_, 0);
lean_inc_ref(v_username_3882_);
lean_dec(v_val_3880_);
v___x_3883_ = lean_string_from_utf8_unchecked(v_username_3882_);
v___x_3884_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3885_ = lean_string_append(v___x_3883_, v___x_3884_);
v___y_3869_ = v___x_3885_;
goto v___jp_3868_;
}
else
{
lean_object* v_username_3886_; lean_object* v_val_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
lean_inc_ref(v_password_3881_);
v_username_3886_ = lean_ctor_get(v_val_3880_, 0);
lean_inc_ref(v_username_3886_);
lean_dec(v_val_3880_);
v_val_3887_ = lean_ctor_get(v_password_3881_, 0);
lean_inc(v_val_3887_);
lean_dec_ref_known(v_password_3881_, 1);
v___x_3888_ = lean_string_from_utf8_unchecked(v_username_3886_);
v___x_3889_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3890_ = lean_string_append(v___x_3888_, v___x_3889_);
v___x_3891_ = lean_string_from_utf8_unchecked(v_val_3887_);
v___x_3892_ = lean_string_append(v___x_3890_, v___x_3891_);
lean_dec_ref(v___x_3891_);
v___x_3893_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3894_ = lean_string_append(v___x_3892_, v___x_3893_);
v___y_3869_ = v___x_3894_;
goto v___jp_3868_;
}
}
v___jp_3851_:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3855_ = lean_string_append(v___y_3853_, v___y_3852_);
lean_dec_ref(v___y_3852_);
v___x_3856_ = lean_string_append(v___x_3855_, v___y_3854_);
lean_dec_ref(v___y_3854_);
v___x_3857_ = lean_string_append(v___x_3850_, v___x_3856_);
lean_dec_ref(v___x_3856_);
v___y_3834_ = v___x_3857_;
goto v___jp_3833_;
}
v___jp_3858_:
{
switch(lean_obj_tag(v_port_3849_))
{
case 0:
{
lean_object* v___x_3861_; 
v___x_3861_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3852_ = v___y_3860_;
v___y_3853_ = v___y_3859_;
v___y_3854_ = v___x_3861_;
goto v___jp_3851_;
}
case 1:
{
lean_object* v___x_3862_; 
v___x_3862_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3852_ = v___y_3860_;
v___y_3853_ = v___y_3859_;
v___y_3854_ = v___x_3862_;
goto v___jp_3851_;
}
default: 
{
uint16_t v_port_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v_port_3863_ = lean_ctor_get_uint16(v_port_3849_, 0);
lean_dec_ref_known(v_port_3849_, 0);
v___x_3864_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3865_ = lean_uint16_to_nat(v_port_3863_);
v___x_3866_ = l_Nat_reprFast(v___x_3865_);
v___x_3867_ = lean_string_append(v___x_3864_, v___x_3866_);
lean_dec_ref(v___x_3866_);
v___y_3852_ = v___y_3860_;
v___y_3853_ = v___y_3859_;
v___y_3854_ = v___x_3867_;
goto v___jp_3851_;
}
}
}
v___jp_3868_:
{
switch(lean_obj_tag(v_host_3848_))
{
case 0:
{
lean_object* v_name_3870_; 
v_name_3870_ = lean_ctor_get(v_host_3848_, 0);
lean_inc_ref(v_name_3870_);
lean_dec_ref_known(v_host_3848_, 1);
v___y_3859_ = v___y_3869_;
v___y_3860_ = v_name_3870_;
goto v___jp_3858_;
}
case 1:
{
lean_object* v_ipv4_3871_; lean_object* v___x_3872_; 
v_ipv4_3871_ = lean_ctor_get(v_host_3848_, 0);
lean_inc_ref(v_ipv4_3871_);
lean_dec_ref_known(v_host_3848_, 1);
v___x_3872_ = lean_uv_ntop_v4(v_ipv4_3871_);
lean_dec_ref(v_ipv4_3871_);
v___y_3859_ = v___y_3869_;
v___y_3860_ = v___x_3872_;
goto v___jp_3858_;
}
default: 
{
lean_object* v_ipv6_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v_ipv6_3873_ = lean_ctor_get(v_host_3848_, 0);
lean_inc_ref(v_ipv6_3873_);
lean_dec_ref_known(v_host_3848_, 1);
v___x_3874_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3875_ = lean_uv_ntop_v6(v_ipv6_3873_);
lean_dec_ref(v_ipv6_3873_);
v___x_3876_ = lean_string_append(v___x_3874_, v___x_3875_);
lean_dec_ref(v___x_3875_);
v___x_3877_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3878_ = lean_string_append(v___x_3876_, v___x_3877_);
v___y_3859_ = v___y_3869_;
v___y_3860_ = v___x_3878_;
goto v___jp_3858_;
}
}
}
}
v___jp_3812_:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3817_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3818_ = lean_string_append(v_scheme_3807_, v___x_3817_);
v___x_3819_ = lean_string_append(v___x_3818_, v___y_3814_);
lean_dec_ref(v___y_3814_);
v___x_3820_ = lean_string_append(v___x_3819_, v___y_3815_);
lean_dec_ref(v___y_3815_);
v___x_3821_ = lean_string_append(v___x_3820_, v___y_3813_);
lean_dec_ref(v___y_3813_);
v___x_3822_ = lean_string_append(v___x_3821_, v___y_3816_);
lean_dec_ref(v___y_3816_);
return v___x_3822_;
}
v___jp_3823_:
{
lean_object* v_queryPart_3826_; 
v_queryPart_3826_ = l_Std_Http_URI_Query_formatOption(v_query_3810_);
if (lean_obj_tag(v_fragment_3811_) == 0)
{
lean_object* v___x_3827_; 
v___x_3827_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3813_ = v_queryPart_3826_;
v___y_3814_ = v___y_3824_;
v___y_3815_ = v___y_3825_;
v___y_3816_ = v___x_3827_;
goto v___jp_3812_;
}
else
{
lean_object* v_val_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v_val_3828_ = lean_ctor_get(v_fragment_3811_, 0);
lean_inc(v_val_3828_);
lean_dec_ref_known(v_fragment_3811_, 1);
v___x_3829_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3830_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3828_);
lean_dec(v_val_3828_);
v___x_3831_ = lean_string_from_utf8_unchecked(v___x_3830_);
v___x_3832_ = lean_string_append(v___x_3829_, v___x_3831_);
lean_dec_ref(v___x_3831_);
v___y_3813_ = v_queryPart_3826_;
v___y_3814_ = v___y_3824_;
v___y_3815_ = v___y_3825_;
v___y_3816_ = v___x_3832_;
goto v___jp_3812_;
}
}
v___jp_3833_:
{
lean_object* v_segments_3835_; uint8_t v_absolute_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; size_t v_sz_3839_; size_t v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v_result_3843_; 
v_segments_3835_ = lean_ctor_get(v_path_3809_, 0);
lean_inc_ref(v_segments_3835_);
v_absolute_3836_ = lean_ctor_get_uint8(v_path_3809_, sizeof(void*)*1);
lean_dec_ref(v_path_3809_);
v___x_3837_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3838_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3839_ = lean_array_size(v_segments_3835_);
v___x_3840_ = ((size_t)0ULL);
v___x_3841_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3838_, v___f_3782_, v_sz_3839_, v___x_3840_, v_segments_3835_);
v___x_3842_ = lean_array_to_list(v___x_3841_);
v_result_3843_ = l_String_intercalate(v___x_3837_, v___x_3842_);
if (v_absolute_3836_ == 0)
{
v___y_3824_ = v___y_3834_;
v___y_3825_ = v_result_3843_;
goto v___jp_3823_;
}
else
{
lean_object* v___x_3844_; 
v___x_3844_ = lean_string_append(v___x_3837_, v_result_3843_);
lean_dec_ref(v_result_3843_);
v___y_3824_ = v___y_3834_;
v___y_3825_ = v___x_3844_;
goto v___jp_3823_;
}
}
}
case 2:
{
lean_object* v_authority_3895_; lean_object* v_userInfo_3896_; lean_object* v_host_3897_; lean_object* v_port_3898_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3910_; 
lean_dec_ref(v___f_3782_);
lean_dec_ref(v___f_3781_);
v_authority_3895_ = lean_ctor_get(v_x_3783_, 0);
lean_inc_ref(v_authority_3895_);
lean_dec_ref_known(v_x_3783_, 1);
v_userInfo_3896_ = lean_ctor_get(v_authority_3895_, 0);
lean_inc(v_userInfo_3896_);
v_host_3897_ = lean_ctor_get(v_authority_3895_, 1);
lean_inc_ref(v_host_3897_);
v_port_3898_ = lean_ctor_get(v_authority_3895_, 2);
lean_inc(v_port_3898_);
lean_dec_ref(v_authority_3895_);
if (lean_obj_tag(v_userInfo_3896_) == 0)
{
lean_object* v___x_3920_; 
v___x_3920_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3910_ = v___x_3920_;
goto v___jp_3909_;
}
else
{
lean_object* v_val_3921_; lean_object* v_password_3922_; 
v_val_3921_ = lean_ctor_get(v_userInfo_3896_, 0);
lean_inc(v_val_3921_);
lean_dec_ref_known(v_userInfo_3896_, 1);
v_password_3922_ = lean_ctor_get(v_val_3921_, 1);
if (lean_obj_tag(v_password_3922_) == 0)
{
lean_object* v_username_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v_username_3923_ = lean_ctor_get(v_val_3921_, 0);
lean_inc_ref(v_username_3923_);
lean_dec(v_val_3921_);
v___x_3924_ = lean_string_from_utf8_unchecked(v_username_3923_);
v___x_3925_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3926_ = lean_string_append(v___x_3924_, v___x_3925_);
v___y_3910_ = v___x_3926_;
goto v___jp_3909_;
}
else
{
lean_object* v_username_3927_; lean_object* v_val_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
lean_inc_ref(v_password_3922_);
v_username_3927_ = lean_ctor_get(v_val_3921_, 0);
lean_inc_ref(v_username_3927_);
lean_dec(v_val_3921_);
v_val_3928_ = lean_ctor_get(v_password_3922_, 0);
lean_inc(v_val_3928_);
lean_dec_ref_known(v_password_3922_, 1);
v___x_3929_ = lean_string_from_utf8_unchecked(v_username_3927_);
v___x_3930_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3931_ = lean_string_append(v___x_3929_, v___x_3930_);
v___x_3932_ = lean_string_from_utf8_unchecked(v_val_3928_);
v___x_3933_ = lean_string_append(v___x_3931_, v___x_3932_);
lean_dec_ref(v___x_3932_);
v___x_3934_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3935_ = lean_string_append(v___x_3933_, v___x_3934_);
v___y_3910_ = v___x_3935_;
goto v___jp_3909_;
}
}
v___jp_3899_:
{
switch(lean_obj_tag(v_port_3898_))
{
case 0:
{
lean_object* v___x_3902_; 
v___x_3902_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3785_ = v___y_3901_;
v___y_3786_ = v___y_3900_;
v___y_3787_ = v___x_3902_;
goto v___jp_3784_;
}
case 1:
{
lean_object* v___x_3903_; 
v___x_3903_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3785_ = v___y_3901_;
v___y_3786_ = v___y_3900_;
v___y_3787_ = v___x_3903_;
goto v___jp_3784_;
}
default: 
{
uint16_t v_port_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v_port_3904_ = lean_ctor_get_uint16(v_port_3898_, 0);
lean_dec_ref_known(v_port_3898_, 0);
v___x_3905_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3906_ = lean_uint16_to_nat(v_port_3904_);
v___x_3907_ = l_Nat_reprFast(v___x_3906_);
v___x_3908_ = lean_string_append(v___x_3905_, v___x_3907_);
lean_dec_ref(v___x_3907_);
v___y_3785_ = v___y_3901_;
v___y_3786_ = v___y_3900_;
v___y_3787_ = v___x_3908_;
goto v___jp_3784_;
}
}
}
v___jp_3909_:
{
switch(lean_obj_tag(v_host_3897_))
{
case 0:
{
lean_object* v_name_3911_; 
v_name_3911_ = lean_ctor_get(v_host_3897_, 0);
lean_inc_ref(v_name_3911_);
lean_dec_ref_known(v_host_3897_, 1);
v___y_3900_ = v___y_3910_;
v___y_3901_ = v_name_3911_;
goto v___jp_3899_;
}
case 1:
{
lean_object* v_ipv4_3912_; lean_object* v___x_3913_; 
v_ipv4_3912_ = lean_ctor_get(v_host_3897_, 0);
lean_inc_ref(v_ipv4_3912_);
lean_dec_ref_known(v_host_3897_, 1);
v___x_3913_ = lean_uv_ntop_v4(v_ipv4_3912_);
lean_dec_ref(v_ipv4_3912_);
v___y_3900_ = v___y_3910_;
v___y_3901_ = v___x_3913_;
goto v___jp_3899_;
}
default: 
{
lean_object* v_ipv6_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v_ipv6_3914_ = lean_ctor_get(v_host_3897_, 0);
lean_inc_ref(v_ipv6_3914_);
lean_dec_ref_known(v_host_3897_, 1);
v___x_3915_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3916_ = lean_uv_ntop_v6(v_ipv6_3914_);
lean_dec_ref(v_ipv6_3914_);
v___x_3917_ = lean_string_append(v___x_3915_, v___x_3916_);
lean_dec_ref(v___x_3916_);
v___x_3918_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3919_ = lean_string_append(v___x_3917_, v___x_3918_);
v___y_3900_ = v___y_3910_;
v___y_3901_ = v___x_3919_;
goto v___jp_3899_;
}
}
}
}
default: 
{
lean_object* v___x_3936_; 
lean_dec_ref(v___f_3782_);
lean_dec_ref(v___f_3781_);
v___x_3936_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__2___closed__0));
return v___x_3936_;
}
}
v___jp_3784_:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3788_ = lean_string_append(v___y_3786_, v___y_3785_);
lean_dec_ref(v___y_3785_);
v___x_3789_ = lean_string_append(v___x_3788_, v___y_3787_);
lean_dec_ref(v___y_3787_);
return v___x_3789_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__2(lean_object* v___f_3940_, lean_object* v___f_3941_, lean_object* v_buffer_3942_, lean_object* v_target_3943_){
_start:
{
lean_object* v___y_3945_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; 
switch(lean_obj_tag(v_target_3943_))
{
case 0:
{
lean_object* v_path_3965_; lean_object* v_query_3966_; lean_object* v___y_3968_; lean_object* v_segments_3971_; uint8_t v_absolute_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; size_t v_sz_3975_; size_t v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v_result_3979_; 
lean_dec_ref(v___f_3941_);
v_path_3965_ = lean_ctor_get(v_target_3943_, 0);
lean_inc_ref(v_path_3965_);
v_query_3966_ = lean_ctor_get(v_target_3943_, 1);
lean_inc(v_query_3966_);
lean_dec_ref_known(v_target_3943_, 2);
v_segments_3971_ = lean_ctor_get(v_path_3965_, 0);
lean_inc_ref(v_segments_3971_);
v_absolute_3972_ = lean_ctor_get_uint8(v_path_3965_, sizeof(void*)*1);
lean_dec_ref(v_path_3965_);
v___x_3973_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3974_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3975_ = lean_array_size(v_segments_3971_);
v___x_3976_ = ((size_t)0ULL);
v___x_3977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3974_, v___f_3940_, v_sz_3975_, v___x_3976_, v_segments_3971_);
v___x_3978_ = lean_array_to_list(v___x_3977_);
v_result_3979_ = l_String_intercalate(v___x_3973_, v___x_3978_);
if (v_absolute_3972_ == 0)
{
v___y_3968_ = v_result_3979_;
goto v___jp_3967_;
}
else
{
lean_object* v___x_3980_; 
v___x_3980_ = lean_string_append(v___x_3973_, v_result_3979_);
lean_dec_ref(v_result_3979_);
v___y_3968_ = v___x_3980_;
goto v___jp_3967_;
}
v___jp_3967_:
{
lean_object* v_queryStr_3969_; lean_object* v___x_3970_; 
v_queryStr_3969_ = l_Std_Http_URI_Query_formatOption(v_query_3966_);
v___x_3970_ = lean_string_append(v___y_3968_, v_queryStr_3969_);
lean_dec_ref(v_queryStr_3969_);
v___y_3945_ = v___x_3970_;
goto v___jp_3944_;
}
}
case 1:
{
lean_object* v_uri_3981_; lean_object* v_scheme_3982_; lean_object* v_authority_3983_; lean_object* v_path_3984_; lean_object* v_query_3985_; lean_object* v_fragment_3986_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4009_; 
lean_dec_ref(v___f_3940_);
v_uri_3981_ = lean_ctor_get(v_target_3943_, 0);
lean_inc_ref(v_uri_3981_);
lean_dec_ref_known(v_target_3943_, 1);
v_scheme_3982_ = lean_ctor_get(v_uri_3981_, 0);
lean_inc_ref(v_scheme_3982_);
v_authority_3983_ = lean_ctor_get(v_uri_3981_, 1);
lean_inc(v_authority_3983_);
v_path_3984_ = lean_ctor_get(v_uri_3981_, 2);
lean_inc_ref(v_path_3984_);
v_query_3985_ = lean_ctor_get(v_uri_3981_, 3);
lean_inc(v_query_3985_);
v_fragment_3986_ = lean_ctor_get(v_uri_3981_, 4);
lean_inc(v_fragment_3986_);
lean_dec_ref(v_uri_3981_);
if (lean_obj_tag(v_authority_3983_) == 0)
{
lean_object* v___x_4020_; 
v___x_4020_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4009_ = v___x_4020_;
goto v___jp_4008_;
}
else
{
lean_object* v_val_4021_; lean_object* v_userInfo_4022_; lean_object* v_host_4023_; lean_object* v_port_4024_; lean_object* v___x_4025_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4044_; 
v_val_4021_ = lean_ctor_get(v_authority_3983_, 0);
lean_inc(v_val_4021_);
lean_dec_ref_known(v_authority_3983_, 1);
v_userInfo_4022_ = lean_ctor_get(v_val_4021_, 0);
lean_inc(v_userInfo_4022_);
v_host_4023_ = lean_ctor_get(v_val_4021_, 1);
lean_inc_ref(v_host_4023_);
v_port_4024_ = lean_ctor_get(v_val_4021_, 2);
lean_inc(v_port_4024_);
lean_dec(v_val_4021_);
v___x_4025_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_4022_) == 0)
{
lean_object* v___x_4054_; 
v___x_4054_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4044_ = v___x_4054_;
goto v___jp_4043_;
}
else
{
lean_object* v_val_4055_; lean_object* v_password_4056_; 
v_val_4055_ = lean_ctor_get(v_userInfo_4022_, 0);
lean_inc(v_val_4055_);
lean_dec_ref_known(v_userInfo_4022_, 1);
v_password_4056_ = lean_ctor_get(v_val_4055_, 1);
if (lean_obj_tag(v_password_4056_) == 0)
{
lean_object* v_username_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v_username_4057_ = lean_ctor_get(v_val_4055_, 0);
lean_inc_ref(v_username_4057_);
lean_dec(v_val_4055_);
v___x_4058_ = lean_string_from_utf8_unchecked(v_username_4057_);
v___x_4059_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4060_ = lean_string_append(v___x_4058_, v___x_4059_);
v___y_4044_ = v___x_4060_;
goto v___jp_4043_;
}
else
{
lean_object* v_username_4061_; lean_object* v_val_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
lean_inc_ref(v_password_4056_);
v_username_4061_ = lean_ctor_get(v_val_4055_, 0);
lean_inc_ref(v_username_4061_);
lean_dec(v_val_4055_);
v_val_4062_ = lean_ctor_get(v_password_4056_, 0);
lean_inc(v_val_4062_);
lean_dec_ref_known(v_password_4056_, 1);
v___x_4063_ = lean_string_from_utf8_unchecked(v_username_4061_);
v___x_4064_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4065_ = lean_string_append(v___x_4063_, v___x_4064_);
v___x_4066_ = lean_string_from_utf8_unchecked(v_val_4062_);
v___x_4067_ = lean_string_append(v___x_4065_, v___x_4066_);
lean_dec_ref(v___x_4066_);
v___x_4068_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4069_ = lean_string_append(v___x_4067_, v___x_4068_);
v___y_4044_ = v___x_4069_;
goto v___jp_4043_;
}
}
v___jp_4026_:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4030_ = lean_string_append(v___y_4027_, v___y_4028_);
lean_dec_ref(v___y_4028_);
v___x_4031_ = lean_string_append(v___x_4030_, v___y_4029_);
lean_dec_ref(v___y_4029_);
v___x_4032_ = lean_string_append(v___x_4025_, v___x_4031_);
lean_dec_ref(v___x_4031_);
v___y_4009_ = v___x_4032_;
goto v___jp_4008_;
}
v___jp_4033_:
{
switch(lean_obj_tag(v_port_4024_))
{
case 0:
{
lean_object* v___x_4036_; 
v___x_4036_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4027_ = v___y_4034_;
v___y_4028_ = v___y_4035_;
v___y_4029_ = v___x_4036_;
goto v___jp_4026_;
}
case 1:
{
lean_object* v___x_4037_; 
v___x_4037_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_4027_ = v___y_4034_;
v___y_4028_ = v___y_4035_;
v___y_4029_ = v___x_4037_;
goto v___jp_4026_;
}
default: 
{
uint16_t v_port_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v_port_4038_ = lean_ctor_get_uint16(v_port_4024_, 0);
lean_dec_ref_known(v_port_4024_, 0);
v___x_4039_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4040_ = lean_uint16_to_nat(v_port_4038_);
v___x_4041_ = l_Nat_reprFast(v___x_4040_);
v___x_4042_ = lean_string_append(v___x_4039_, v___x_4041_);
lean_dec_ref(v___x_4041_);
v___y_4027_ = v___y_4034_;
v___y_4028_ = v___y_4035_;
v___y_4029_ = v___x_4042_;
goto v___jp_4026_;
}
}
}
v___jp_4043_:
{
switch(lean_obj_tag(v_host_4023_))
{
case 0:
{
lean_object* v_name_4045_; 
v_name_4045_ = lean_ctor_get(v_host_4023_, 0);
lean_inc_ref(v_name_4045_);
lean_dec_ref_known(v_host_4023_, 1);
v___y_4034_ = v___y_4044_;
v___y_4035_ = v_name_4045_;
goto v___jp_4033_;
}
case 1:
{
lean_object* v_ipv4_4046_; lean_object* v___x_4047_; 
v_ipv4_4046_ = lean_ctor_get(v_host_4023_, 0);
lean_inc_ref(v_ipv4_4046_);
lean_dec_ref_known(v_host_4023_, 1);
v___x_4047_ = lean_uv_ntop_v4(v_ipv4_4046_);
lean_dec_ref(v_ipv4_4046_);
v___y_4034_ = v___y_4044_;
v___y_4035_ = v___x_4047_;
goto v___jp_4033_;
}
default: 
{
lean_object* v_ipv6_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v_ipv6_4048_ = lean_ctor_get(v_host_4023_, 0);
lean_inc_ref(v_ipv6_4048_);
lean_dec_ref_known(v_host_4023_, 1);
v___x_4049_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4050_ = lean_uv_ntop_v6(v_ipv6_4048_);
lean_dec_ref(v_ipv6_4048_);
v___x_4051_ = lean_string_append(v___x_4049_, v___x_4050_);
lean_dec_ref(v___x_4050_);
v___x_4052_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4053_ = lean_string_append(v___x_4051_, v___x_4052_);
v___y_4034_ = v___y_4044_;
v___y_4035_ = v___x_4053_;
goto v___jp_4033_;
}
}
}
}
v___jp_3987_:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3992_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3993_ = lean_string_append(v_scheme_3982_, v___x_3992_);
v___x_3994_ = lean_string_append(v___x_3993_, v___y_3989_);
lean_dec_ref(v___y_3989_);
v___x_3995_ = lean_string_append(v___x_3994_, v___y_3990_);
lean_dec_ref(v___y_3990_);
v___x_3996_ = lean_string_append(v___x_3995_, v___y_3988_);
lean_dec_ref(v___y_3988_);
v___x_3997_ = lean_string_append(v___x_3996_, v___y_3991_);
lean_dec_ref(v___y_3991_);
v___y_3945_ = v___x_3997_;
goto v___jp_3944_;
}
v___jp_3998_:
{
lean_object* v_queryPart_4001_; 
v_queryPart_4001_ = l_Std_Http_URI_Query_formatOption(v_query_3985_);
if (lean_obj_tag(v_fragment_3986_) == 0)
{
lean_object* v___x_4002_; 
v___x_4002_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3988_ = v_queryPart_4001_;
v___y_3989_ = v___y_3999_;
v___y_3990_ = v___y_4000_;
v___y_3991_ = v___x_4002_;
goto v___jp_3987_;
}
else
{
lean_object* v_val_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v_val_4003_ = lean_ctor_get(v_fragment_3986_, 0);
lean_inc(v_val_4003_);
lean_dec_ref_known(v_fragment_3986_, 1);
v___x_4004_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_4005_ = l_Std_Http_URI_EncodedFragment_encode(v_val_4003_);
lean_dec(v_val_4003_);
v___x_4006_ = lean_string_from_utf8_unchecked(v___x_4005_);
v___x_4007_ = lean_string_append(v___x_4004_, v___x_4006_);
lean_dec_ref(v___x_4006_);
v___y_3988_ = v_queryPart_4001_;
v___y_3989_ = v___y_3999_;
v___y_3990_ = v___y_4000_;
v___y_3991_ = v___x_4007_;
goto v___jp_3987_;
}
}
v___jp_4008_:
{
lean_object* v_segments_4010_; uint8_t v_absolute_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; size_t v_sz_4014_; size_t v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v_result_4018_; 
v_segments_4010_ = lean_ctor_get(v_path_3984_, 0);
lean_inc_ref(v_segments_4010_);
v_absolute_4011_ = lean_ctor_get_uint8(v_path_3984_, sizeof(void*)*1);
lean_dec_ref(v_path_3984_);
v___x_4012_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_4013_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_4014_ = lean_array_size(v_segments_4010_);
v___x_4015_ = ((size_t)0ULL);
v___x_4016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4013_, v___f_3941_, v_sz_4014_, v___x_4015_, v_segments_4010_);
v___x_4017_ = lean_array_to_list(v___x_4016_);
v_result_4018_ = l_String_intercalate(v___x_4012_, v___x_4017_);
if (v_absolute_4011_ == 0)
{
v___y_3999_ = v___y_4009_;
v___y_4000_ = v_result_4018_;
goto v___jp_3998_;
}
else
{
lean_object* v___x_4019_; 
v___x_4019_ = lean_string_append(v___x_4012_, v_result_4018_);
lean_dec_ref(v_result_4018_);
v___y_3999_ = v___y_4009_;
v___y_4000_ = v___x_4019_;
goto v___jp_3998_;
}
}
}
case 2:
{
lean_object* v_authority_4070_; lean_object* v_userInfo_4071_; lean_object* v_host_4072_; lean_object* v_port_4073_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4085_; 
lean_dec_ref(v___f_3941_);
lean_dec_ref(v___f_3940_);
v_authority_4070_ = lean_ctor_get(v_target_3943_, 0);
lean_inc_ref(v_authority_4070_);
lean_dec_ref_known(v_target_3943_, 1);
v_userInfo_4071_ = lean_ctor_get(v_authority_4070_, 0);
lean_inc(v_userInfo_4071_);
v_host_4072_ = lean_ctor_get(v_authority_4070_, 1);
lean_inc_ref(v_host_4072_);
v_port_4073_ = lean_ctor_get(v_authority_4070_, 2);
lean_inc(v_port_4073_);
lean_dec_ref(v_authority_4070_);
if (lean_obj_tag(v_userInfo_4071_) == 0)
{
lean_object* v___x_4095_; 
v___x_4095_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4085_ = v___x_4095_;
goto v___jp_4084_;
}
else
{
lean_object* v_val_4096_; lean_object* v_password_4097_; 
v_val_4096_ = lean_ctor_get(v_userInfo_4071_, 0);
lean_inc(v_val_4096_);
lean_dec_ref_known(v_userInfo_4071_, 1);
v_password_4097_ = lean_ctor_get(v_val_4096_, 1);
if (lean_obj_tag(v_password_4097_) == 0)
{
lean_object* v_username_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v_username_4098_ = lean_ctor_get(v_val_4096_, 0);
lean_inc_ref(v_username_4098_);
lean_dec(v_val_4096_);
v___x_4099_ = lean_string_from_utf8_unchecked(v_username_4098_);
v___x_4100_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4101_ = lean_string_append(v___x_4099_, v___x_4100_);
v___y_4085_ = v___x_4101_;
goto v___jp_4084_;
}
else
{
lean_object* v_username_4102_; lean_object* v_val_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
lean_inc_ref(v_password_4097_);
v_username_4102_ = lean_ctor_get(v_val_4096_, 0);
lean_inc_ref(v_username_4102_);
lean_dec(v_val_4096_);
v_val_4103_ = lean_ctor_get(v_password_4097_, 0);
lean_inc(v_val_4103_);
lean_dec_ref_known(v_password_4097_, 1);
v___x_4104_ = lean_string_from_utf8_unchecked(v_username_4102_);
v___x_4105_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4106_ = lean_string_append(v___x_4104_, v___x_4105_);
v___x_4107_ = lean_string_from_utf8_unchecked(v_val_4103_);
v___x_4108_ = lean_string_append(v___x_4106_, v___x_4107_);
lean_dec_ref(v___x_4107_);
v___x_4109_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4110_ = lean_string_append(v___x_4108_, v___x_4109_);
v___y_4085_ = v___x_4110_;
goto v___jp_4084_;
}
}
v___jp_4074_:
{
switch(lean_obj_tag(v_port_4073_))
{
case 0:
{
lean_object* v___x_4077_; 
v___x_4077_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3960_ = v___y_4076_;
v___y_3961_ = v___y_4075_;
v___y_3962_ = v___x_4077_;
goto v___jp_3959_;
}
case 1:
{
lean_object* v___x_4078_; 
v___x_4078_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3960_ = v___y_4076_;
v___y_3961_ = v___y_4075_;
v___y_3962_ = v___x_4078_;
goto v___jp_3959_;
}
default: 
{
uint16_t v_port_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v_port_4079_ = lean_ctor_get_uint16(v_port_4073_, 0);
lean_dec_ref_known(v_port_4073_, 0);
v___x_4080_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4081_ = lean_uint16_to_nat(v_port_4079_);
v___x_4082_ = l_Nat_reprFast(v___x_4081_);
v___x_4083_ = lean_string_append(v___x_4080_, v___x_4082_);
lean_dec_ref(v___x_4082_);
v___y_3960_ = v___y_4076_;
v___y_3961_ = v___y_4075_;
v___y_3962_ = v___x_4083_;
goto v___jp_3959_;
}
}
}
v___jp_4084_:
{
switch(lean_obj_tag(v_host_4072_))
{
case 0:
{
lean_object* v_name_4086_; 
v_name_4086_ = lean_ctor_get(v_host_4072_, 0);
lean_inc_ref(v_name_4086_);
lean_dec_ref_known(v_host_4072_, 1);
v___y_4075_ = v___y_4085_;
v___y_4076_ = v_name_4086_;
goto v___jp_4074_;
}
case 1:
{
lean_object* v_ipv4_4087_; lean_object* v___x_4088_; 
v_ipv4_4087_ = lean_ctor_get(v_host_4072_, 0);
lean_inc_ref(v_ipv4_4087_);
lean_dec_ref_known(v_host_4072_, 1);
v___x_4088_ = lean_uv_ntop_v4(v_ipv4_4087_);
lean_dec_ref(v_ipv4_4087_);
v___y_4075_ = v___y_4085_;
v___y_4076_ = v___x_4088_;
goto v___jp_4074_;
}
default: 
{
lean_object* v_ipv6_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v_ipv6_4089_ = lean_ctor_get(v_host_4072_, 0);
lean_inc_ref(v_ipv6_4089_);
lean_dec_ref_known(v_host_4072_, 1);
v___x_4090_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4091_ = lean_uv_ntop_v6(v_ipv6_4089_);
lean_dec_ref(v_ipv6_4089_);
v___x_4092_ = lean_string_append(v___x_4090_, v___x_4091_);
lean_dec_ref(v___x_4091_);
v___x_4093_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4094_ = lean_string_append(v___x_4092_, v___x_4093_);
v___y_4075_ = v___y_4085_;
v___y_4076_ = v___x_4094_;
goto v___jp_4074_;
}
}
}
}
default: 
{
lean_object* v___x_4111_; 
lean_dec_ref(v___f_3941_);
lean_dec_ref(v___f_3940_);
v___x_4111_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__2___closed__0));
v___y_3945_ = v___x_4111_;
goto v___jp_3944_;
}
}
v___jp_3944_:
{
lean_object* v_data_3946_; lean_object* v_size_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3958_; 
v_data_3946_ = lean_ctor_get(v_buffer_3942_, 0);
v_size_3947_ = lean_ctor_get(v_buffer_3942_, 1);
v_isSharedCheck_3958_ = !lean_is_exclusive(v_buffer_3942_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3949_ = v_buffer_3942_;
v_isShared_3950_ = v_isSharedCheck_3958_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_size_3947_);
lean_inc(v_data_3946_);
lean_dec(v_buffer_3942_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3958_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3956_; 
v___x_3951_ = lean_string_to_utf8(v___y_3945_);
lean_dec_ref(v___y_3945_);
lean_inc_ref(v___x_3951_);
v___x_3952_ = lean_array_push(v_data_3946_, v___x_3951_);
v___x_3953_ = lean_byte_array_size(v___x_3951_);
lean_dec_ref(v___x_3951_);
v___x_3954_ = lean_nat_add(v_size_3947_, v___x_3953_);
lean_dec(v_size_3947_);
if (v_isShared_3950_ == 0)
{
lean_ctor_set(v___x_3949_, 1, v___x_3954_);
lean_ctor_set(v___x_3949_, 0, v___x_3952_);
v___x_3956_ = v___x_3949_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3952_);
lean_ctor_set(v_reuseFailAlloc_3957_, 1, v___x_3954_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
v___jp_3959_:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3963_ = lean_string_append(v___y_3961_, v___y_3960_);
lean_dec_ref(v___y_3960_);
v___x_3964_ = lean_string_append(v___x_3963_, v___y_3962_);
lean_dec_ref(v___y_3962_);
v___y_3945_ = v___x_3964_;
goto v___jp_3944_;
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
