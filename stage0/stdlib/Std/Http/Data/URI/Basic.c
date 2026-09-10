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
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
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
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidDomainLabel___boxed(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0_value;
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
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0(void){
_start:
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 45;
v___x_137_ = lean_uint32_to_uint8(v___x_136_);
return v___x_137_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1(void){
_start:
{
uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = 46;
v___x_139_ = lean_uint32_to_uint8(v___x_138_);
return v___x_139_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2(void){
_start:
{
uint32_t v___x_140_; uint8_t v___x_141_; 
v___x_140_ = 95;
v___x_141_ = lean_uint32_to_uint8(v___x_140_);
return v___x_141_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3(void){
_start:
{
uint32_t v___x_142_; uint8_t v___x_143_; 
v___x_142_ = 126;
v___x_143_ = lean_uint32_to_uint8(v___x_142_);
return v___x_143_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4(void){
_start:
{
uint32_t v___x_144_; uint8_t v___x_145_; 
v___x_144_ = 33;
v___x_145_ = lean_uint32_to_uint8(v___x_144_);
return v___x_145_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5(void){
_start:
{
uint32_t v___x_146_; uint8_t v___x_147_; 
v___x_146_ = 36;
v___x_147_ = lean_uint32_to_uint8(v___x_146_);
return v___x_147_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6(void){
_start:
{
uint32_t v___x_148_; uint8_t v___x_149_; 
v___x_148_ = 38;
v___x_149_ = lean_uint32_to_uint8(v___x_148_);
return v___x_149_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7(void){
_start:
{
uint32_t v___x_150_; uint8_t v___x_151_; 
v___x_150_ = 39;
v___x_151_ = lean_uint32_to_uint8(v___x_150_);
return v___x_151_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8(void){
_start:
{
uint32_t v___x_152_; uint8_t v___x_153_; 
v___x_152_ = 40;
v___x_153_ = lean_uint32_to_uint8(v___x_152_);
return v___x_153_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9(void){
_start:
{
uint32_t v___x_154_; uint8_t v___x_155_; 
v___x_154_ = 41;
v___x_155_ = lean_uint32_to_uint8(v___x_154_);
return v___x_155_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10(void){
_start:
{
uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = 42;
v___x_157_ = lean_uint32_to_uint8(v___x_156_);
return v___x_157_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11(void){
_start:
{
uint32_t v___x_158_; uint8_t v___x_159_; 
v___x_158_ = 43;
v___x_159_ = lean_uint32_to_uint8(v___x_158_);
return v___x_159_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12(void){
_start:
{
uint32_t v___x_160_; uint8_t v___x_161_; 
v___x_160_ = 44;
v___x_161_ = lean_uint32_to_uint8(v___x_160_);
return v___x_161_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13(void){
_start:
{
uint32_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = 59;
v___x_163_ = lean_uint32_to_uint8(v___x_162_);
return v___x_163_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14(void){
_start:
{
uint32_t v___x_164_; uint8_t v___x_165_; 
v___x_164_ = 61;
v___x_165_ = lean_uint32_to_uint8(v___x_164_);
return v___x_165_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15(void){
_start:
{
uint32_t v___x_166_; uint8_t v___x_167_; 
v___x_166_ = 58;
v___x_167_ = lean_uint32_to_uint8(v___x_166_);
return v___x_167_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16(void){
_start:
{
uint32_t v___x_168_; uint8_t v___x_169_; 
v___x_168_ = 65;
v___x_169_ = lean_uint32_to_uint8(v___x_168_);
return v___x_169_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17(void){
_start:
{
uint32_t v___x_170_; uint8_t v___x_171_; 
v___x_170_ = 90;
v___x_171_ = lean_uint32_to_uint8(v___x_170_);
return v___x_171_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18(void){
_start:
{
uint32_t v___x_172_; uint8_t v___x_173_; 
v___x_172_ = 97;
v___x_173_ = lean_uint32_to_uint8(v___x_172_);
return v___x_173_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19(void){
_start:
{
uint32_t v___x_174_; uint8_t v___x_175_; 
v___x_174_ = 122;
v___x_175_ = lean_uint32_to_uint8(v___x_174_);
return v___x_175_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20(void){
_start:
{
uint32_t v___x_176_; uint8_t v___x_177_; 
v___x_176_ = 48;
v___x_177_ = lean_uint32_to_uint8(v___x_176_);
return v___x_177_;
}
}
static uint8_t _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21(void){
_start:
{
uint32_t v___x_178_; uint8_t v___x_179_; 
v___x_178_ = 57;
v___x_179_ = lean_uint32_to_uint8(v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instInhabitedUserInfo_default___lam__0(uint8_t v___y_180_){
_start:
{
uint8_t v___x_224_; uint8_t v___x_225_; 
v___x_224_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__20);
v___x_225_ = lean_uint8_dec_le(v___x_224_, v___y_180_);
if (v___x_225_ == 0)
{
goto v___jp_219_;
}
else
{
uint8_t v___x_226_; uint8_t v___x_227_; 
v___x_226_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__21);
v___x_227_ = lean_uint8_dec_le(v___y_180_, v___x_226_);
if (v___x_227_ == 0)
{
goto v___jp_219_;
}
else
{
return v___x_227_;
}
}
v___jp_181_:
{
uint8_t v___x_182_; uint8_t v___x_183_; 
v___x_182_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__0);
v___x_183_ = lean_uint8_dec_eq(v___y_180_, v___x_182_);
if (v___x_183_ == 0)
{
uint8_t v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__1);
v___x_185_ = lean_uint8_dec_eq(v___y_180_, v___x_184_);
if (v___x_185_ == 0)
{
uint8_t v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__2);
v___x_187_ = lean_uint8_dec_eq(v___y_180_, v___x_186_);
if (v___x_187_ == 0)
{
uint8_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__3);
v___x_189_ = lean_uint8_dec_eq(v___y_180_, v___x_188_);
if (v___x_189_ == 0)
{
uint8_t v___x_190_; uint8_t v___x_191_; 
v___x_190_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__4);
v___x_191_ = lean_uint8_dec_eq(v___y_180_, v___x_190_);
if (v___x_191_ == 0)
{
uint8_t v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__5);
v___x_193_ = lean_uint8_dec_eq(v___y_180_, v___x_192_);
if (v___x_193_ == 0)
{
uint8_t v___x_194_; uint8_t v___x_195_; 
v___x_194_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__6);
v___x_195_ = lean_uint8_dec_eq(v___y_180_, v___x_194_);
if (v___x_195_ == 0)
{
uint8_t v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__7);
v___x_197_ = lean_uint8_dec_eq(v___y_180_, v___x_196_);
if (v___x_197_ == 0)
{
uint8_t v___x_198_; uint8_t v___x_199_; 
v___x_198_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__8);
v___x_199_ = lean_uint8_dec_eq(v___y_180_, v___x_198_);
if (v___x_199_ == 0)
{
uint8_t v___x_200_; uint8_t v___x_201_; 
v___x_200_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__9);
v___x_201_ = lean_uint8_dec_eq(v___y_180_, v___x_200_);
if (v___x_201_ == 0)
{
uint8_t v___x_202_; uint8_t v___x_203_; 
v___x_202_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__10);
v___x_203_ = lean_uint8_dec_eq(v___y_180_, v___x_202_);
if (v___x_203_ == 0)
{
uint8_t v___x_204_; uint8_t v___x_205_; 
v___x_204_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__11);
v___x_205_ = lean_uint8_dec_eq(v___y_180_, v___x_204_);
if (v___x_205_ == 0)
{
uint8_t v___x_206_; uint8_t v___x_207_; 
v___x_206_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__12);
v___x_207_ = lean_uint8_dec_eq(v___y_180_, v___x_206_);
if (v___x_207_ == 0)
{
uint8_t v___x_208_; uint8_t v___x_209_; 
v___x_208_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__13);
v___x_209_ = lean_uint8_dec_eq(v___y_180_, v___x_208_);
if (v___x_209_ == 0)
{
uint8_t v___x_210_; uint8_t v___x_211_; 
v___x_210_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__14);
v___x_211_ = lean_uint8_dec_eq(v___y_180_, v___x_210_);
if (v___x_211_ == 0)
{
uint8_t v___x_212_; uint8_t v___x_213_; 
v___x_212_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__15);
v___x_213_ = lean_uint8_dec_eq(v___y_180_, v___x_212_);
return v___x_213_;
}
else
{
return v___x_211_;
}
}
else
{
return v___x_209_;
}
}
else
{
return v___x_207_;
}
}
else
{
return v___x_205_;
}
}
else
{
return v___x_203_;
}
}
else
{
return v___x_201_;
}
}
else
{
return v___x_199_;
}
}
else
{
return v___x_197_;
}
}
else
{
return v___x_195_;
}
}
else
{
return v___x_193_;
}
}
else
{
return v___x_191_;
}
}
else
{
return v___x_189_;
}
}
else
{
return v___x_187_;
}
}
else
{
return v___x_185_;
}
}
else
{
return v___x_183_;
}
}
v___jp_214_:
{
uint8_t v___x_215_; uint8_t v___x_216_; 
v___x_215_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__16);
v___x_216_ = lean_uint8_dec_le(v___x_215_, v___y_180_);
if (v___x_216_ == 0)
{
goto v___jp_181_;
}
else
{
uint8_t v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__17);
v___x_218_ = lean_uint8_dec_le(v___y_180_, v___x_217_);
if (v___x_218_ == 0)
{
goto v___jp_181_;
}
else
{
return v___x_218_;
}
}
}
v___jp_219_:
{
uint8_t v___x_220_; uint8_t v___x_221_; 
v___x_220_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__18);
v___x_221_ = lean_uint8_dec_le(v___x_220_, v___y_180_);
if (v___x_221_ == 0)
{
goto v___jp_214_;
}
else
{
uint8_t v___x_222_; uint8_t v___x_223_; 
v___x_222_ = lean_uint8_once(&l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19, &l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___closed__19);
v___x_223_ = lean_uint8_dec_le(v___y_180_, v___x_222_);
if (v___x_223_ == 0)
{
goto v___jp_214_;
}
else
{
return v___x_223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instInhabitedUserInfo_default___lam__0___boxed(lean_object* v___y_228_){
_start:
{
uint8_t v___y_348__boxed_229_; uint8_t v_res_230_; lean_object* v_r_231_; 
v___y_348__boxed_229_ = lean_unbox(v___y_228_);
v_res_230_ = l_Std_Http_URI_instInhabitedUserInfo_default___lam__0(v___y_348__boxed_229_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__1(void){
_start:
{
lean_object* v___f_233_; lean_object* v___x_234_; 
v___f_233_ = ((lean_object*)(l_Std_Http_URI_instInhabitedUserInfo_default___closed__0));
v___x_234_ = l_Std_Http_URI_EncodedString_empty(v___f_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__2(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = lean_box(0);
v___x_236_ = lean_obj_once(&l_Std_Http_URI_instInhabitedUserInfo_default___closed__1, &l_Std_Http_URI_instInhabitedUserInfo_default___closed__1_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__1);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___x_235_);
return v___x_237_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo_default(void){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_obj_once(&l_Std_Http_URI_instInhabitedUserInfo_default___closed__2, &l_Std_Http_URI_instInhabitedUserInfo_default___closed__2_once, _init_l_Std_Http_URI_instInhabitedUserInfo_default___closed__2);
return v___x_238_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedUserInfo(void){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Std_Http_URI_instInhabitedUserInfo_default;
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(lean_object* v_x_246_, lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_246_) == 0)
{
lean_object* v___x_248_; 
v___x_248_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_248_;
}
else
{
lean_object* v_val_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_261_; 
v_val_249_ = lean_ctor_get(v_x_246_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v_x_246_);
if (v_isSharedCheck_261_ == 0)
{
v___x_251_ = v_x_246_;
v_isShared_252_ = v_isSharedCheck_261_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_val_249_);
lean_dec(v_x_246_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_261_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_253_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_254_ = lean_string_from_utf8_unchecked(v_val_249_);
v___x_255_ = l_String_quote(v___x_254_);
if (v_isShared_252_ == 0)
{
lean_ctor_set_tag(v___x_251_, 3);
lean_ctor_set(v___x_251_, 0, v___x_255_);
v___x_257_ = v___x_251_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_260_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_253_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = l_Repr_addAppParen(v___x_258_, v_x_247_);
return v___x_259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___boxed(lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_x_262_, v_x_263_);
lean_dec(v_x_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_URI_instReprUserInfo_repr_spec__1(lean_object* v_a_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = lean_nat_to_int(v_a_265_);
return v___x_266_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_unsigned_to_nat(12u);
v___x_281_ = lean_nat_to_int(v___x_280_);
return v___x_281_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__0));
v___x_290_ = lean_string_length(v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__13);
v___x_292_ = lean_nat_to_int(v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___redArg(lean_object* v_x_297_){
_start:
{
lean_object* v_username_298_; lean_object* v_password_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_334_; 
v_username_298_ = lean_ctor_get(v_x_297_, 0);
v_password_299_ = lean_ctor_get(v_x_297_, 1);
v_isSharedCheck_334_ = !lean_is_exclusive(v_x_297_);
if (v_isSharedCheck_334_ == 0)
{
v___x_301_ = v_x_297_;
v_isShared_302_ = v_isSharedCheck_334_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_password_299_);
lean_inc(v_username_298_);
lean_dec(v_x_297_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_334_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_303_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_304_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__6));
v___x_305_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_306_ = lean_string_from_utf8_unchecked(v_username_298_);
v___x_307_ = l_String_quote(v___x_306_);
v___x_308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
if (v_isShared_302_ == 0)
{
lean_ctor_set_tag(v___x_301_, 4);
lean_ctor_set(v___x_301_, 1, v___x_308_);
lean_ctor_set(v___x_301_, 0, v___x_305_);
v___x_310_ = v___x_301_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_308_);
v___x_310_ = v_reuseFailAlloc_333_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
uint8_t v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_311_ = 0;
v___x_312_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set_uint8(v___x_312_, sizeof(void*)*1, v___x_311_);
v___x_313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_304_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_box(1);
v___x_317_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__11));
v___x_319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_303_);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0(v_password_299_, v___x_321_);
v___x_323_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_305_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*1, v___x_311_);
v___x_325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_320_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_327_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_325_);
v___x_329_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_326_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*1, v___x_311_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr(lean_object* v_x_335_, lean_object* v_prec_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_x_335_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprUserInfo_repr___boxed(lean_object* v_x_338_, lean_object* v_prec_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Std_Http_URI_instReprUserInfo_repr(v_x_338_, v_prec_339_);
lean_dec(v_prec_339_);
return v_res_340_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
if (lean_obj_tag(v_x_343_) == 0)
{
if (lean_obj_tag(v_x_344_) == 0)
{
uint8_t v___x_345_; 
v___x_345_ = 1;
return v___x_345_;
}
else
{
uint8_t v___x_346_; 
v___x_346_ = 0;
return v___x_346_;
}
}
else
{
if (lean_obj_tag(v_x_344_) == 0)
{
uint8_t v___x_347_; 
v___x_347_ = 0;
return v___x_347_;
}
else
{
lean_object* v_val_348_; lean_object* v_val_349_; uint8_t v___x_350_; 
v_val_348_ = lean_ctor_get(v_x_343_, 0);
v_val_349_ = lean_ctor_get(v_x_344_, 0);
v___x_350_ = lean_sarray_dec_eq(v_val_348_, v_val_349_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0___boxed(lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_x_351_, v_x_352_);
lean_dec(v_x_352_);
lean_dec(v_x_351_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqUserInfo_beq(lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
lean_object* v_username_357_; lean_object* v_password_358_; lean_object* v_username_359_; lean_object* v_password_360_; uint8_t v___x_361_; 
v_username_357_ = lean_ctor_get(v_x_355_, 0);
v_password_358_ = lean_ctor_get(v_x_355_, 1);
v_username_359_ = lean_ctor_get(v_x_356_, 0);
v_password_360_ = lean_ctor_get(v_x_356_, 1);
v___x_361_ = lean_sarray_dec_eq(v_username_357_, v_username_359_);
if (v___x_361_ == 0)
{
return v___x_361_;
}
else
{
uint8_t v___x_362_; 
v___x_362_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqUserInfo_beq_spec__0(v_password_358_, v_password_360_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqUserInfo_beq___boxed(lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
uint8_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = l_Std_Http_URI_instBEqUserInfo_beq(v_x_363_, v_x_364_);
lean_dec_ref(v_x_364_);
lean_dec_ref(v_x_363_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings(lean_object* v_username_369_, lean_object* v_password_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_369_);
if (lean_obj_tag(v_password_370_) == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_box(0);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
return v___x_373_;
}
else
{
lean_object* v_val_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_383_; 
v_val_374_ = lean_ctor_get(v_password_370_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v_password_370_);
if (v_isSharedCheck_383_ == 0)
{
v___x_376_ = v_password_370_;
v_isShared_377_ = v_isSharedCheck_383_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_val_374_);
lean_dec(v_password_370_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_383_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_378_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_374_);
lean_dec(v_val_374_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_378_);
v___x_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_382_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_381_; 
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_371_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
return v___x_381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_ofStrings___boxed(lean_object* v_username_384_, lean_object* v_password_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Std_Http_URI_UserInfo_ofStrings(v_username_384_, v_password_385_);
lean_dec_ref(v_username_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f(lean_object* v_ui_387_){
_start:
{
lean_object* v_username_388_; lean_object* v___x_389_; 
v_username_388_ = lean_ctor_get(v_ui_387_, 0);
v___x_389_ = l_Std_Http_URI_EncodedUserInfo_decode(v_username_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_username_x3f___boxed(lean_object* v_ui_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Std_Http_URI_UserInfo_username_x3f(v_ui_390_);
lean_dec_ref(v_ui_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f(lean_object* v_ui_392_){
_start:
{
lean_object* v_password_393_; 
v_password_393_ = lean_ctor_get(v_ui_392_, 1);
if (lean_obj_tag(v_password_393_) == 0)
{
lean_object* v___x_394_; 
v___x_394_ = lean_box(0);
return v___x_394_;
}
else
{
lean_object* v_val_395_; lean_object* v___x_396_; 
v_val_395_ = lean_ctor_get(v_password_393_, 0);
v___x_396_ = l_Std_Http_URI_EncodedUserInfo_decode(v_val_395_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_UserInfo_password_x3f___boxed(lean_object* v_ui_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Std_Http_URI_UserInfo_password_x3f(v_ui_397_);
lean_dec_ref(v_ui_397_);
return v_res_398_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(lean_object* v_x_399_){
_start:
{
if (lean_obj_tag(v_x_399_) == 0)
{
uint8_t v___x_400_; 
v___x_400_ = 1;
return v___x_400_;
}
else
{
lean_object* v_head_401_; lean_object* v_tail_402_; uint8_t v___y_404_; uint8_t v___y_411_; uint32_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_head_401_ = lean_ctor_get(v_x_399_, 0);
v_tail_402_ = lean_ctor_get(v_x_399_, 1);
v___x_426_ = lean_unbox_uint32(v_head_401_);
v___x_427_ = lean_uint32_to_nat(v___x_426_);
v___x_428_ = lean_unsigned_to_nat(128u);
v___x_429_ = lean_nat_dec_lt(v___x_427_, v___x_428_);
lean_dec(v___x_427_);
if (v___x_429_ == 0)
{
v___y_404_ = v___x_429_;
goto v___jp_403_;
}
else
{
uint32_t v___x_430_; uint32_t v___x_431_; uint8_t v___x_432_; 
v___x_430_ = 48;
v___x_431_ = lean_unbox_uint32(v_head_401_);
v___x_432_ = lean_uint32_dec_le(v___x_430_, v___x_431_);
if (v___x_432_ == 0)
{
goto v___jp_419_;
}
else
{
uint32_t v___x_433_; uint32_t v___x_434_; uint8_t v___x_435_; 
v___x_433_ = 57;
v___x_434_ = lean_unbox_uint32(v_head_401_);
v___x_435_ = lean_uint32_dec_le(v___x_434_, v___x_433_);
if (v___x_435_ == 0)
{
goto v___jp_419_;
}
else
{
v___y_404_ = v___x_435_;
goto v___jp_403_;
}
}
}
v___jp_403_:
{
if (v___y_404_ == 0)
{
uint32_t v___x_405_; uint32_t v___x_406_; uint8_t v___x_407_; 
v___x_405_ = 45;
v___x_406_ = lean_unbox_uint32(v_head_401_);
v___x_407_ = lean_uint32_dec_eq(v___x_406_, v___x_405_);
if (v___x_407_ == 0)
{
return v___x_407_;
}
else
{
v_x_399_ = v_tail_402_;
goto _start;
}
}
else
{
v_x_399_ = v_tail_402_;
goto _start;
}
}
v___jp_410_:
{
if (v___y_411_ == 0)
{
uint32_t v___x_412_; uint32_t v___x_413_; uint8_t v___x_414_; 
v___x_412_ = 97;
v___x_413_ = lean_unbox_uint32(v_head_401_);
v___x_414_ = lean_uint32_dec_le(v___x_412_, v___x_413_);
if (v___x_414_ == 0)
{
v___y_404_ = v___x_414_;
goto v___jp_403_;
}
else
{
uint32_t v___x_415_; uint32_t v___x_416_; uint8_t v___x_417_; 
v___x_415_ = 122;
v___x_416_ = lean_unbox_uint32(v_head_401_);
v___x_417_ = lean_uint32_dec_le(v___x_416_, v___x_415_);
v___y_404_ = v___x_417_;
goto v___jp_403_;
}
}
else
{
v_x_399_ = v_tail_402_;
goto _start;
}
}
v___jp_419_:
{
uint32_t v___x_420_; uint32_t v___x_421_; uint8_t v___x_422_; 
v___x_420_ = 65;
v___x_421_ = lean_unbox_uint32(v_head_401_);
v___x_422_ = lean_uint32_dec_le(v___x_420_, v___x_421_);
if (v___x_422_ == 0)
{
v___y_411_ = v___x_422_;
goto v___jp_410_;
}
else
{
uint32_t v___x_423_; uint32_t v___x_424_; uint8_t v___x_425_; 
v___x_423_ = 90;
v___x_424_ = lean_unbox_uint32(v_head_401_);
v___x_425_ = lean_uint32_dec_le(v___x_424_, v___x_423_);
v___y_411_ = v___x_425_;
goto v___jp_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0___boxed(lean_object* v_x_436_){
_start:
{
uint8_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v_x_436_);
lean_dec(v_x_436_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object* v_s_439_){
_start:
{
uint32_t v___y_441_; uint8_t v___y_442_; uint32_t v___y_448_; lean_object* v_chars_453_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v_chars_453_ = lean_string_data(v_s_439_);
v___x_470_ = l_List_lengthTR___redArg(v_chars_453_);
v___x_471_ = lean_unsigned_to_nat(63u);
v___x_472_ = lean_nat_dec_le(v___x_470_, v___x_471_);
lean_dec(v___x_470_);
if (v___x_472_ == 0)
{
lean_dec(v_chars_453_);
return v___x_472_;
}
else
{
uint8_t v___x_473_; 
v___x_473_ = l_List_all___at___00Std_Http_URI_isValidDomainLabel_spec__0(v_chars_453_);
if (v___x_473_ == 0)
{
lean_dec(v_chars_453_);
return v___x_473_;
}
else
{
lean_object* v___x_474_; 
v___x_474_ = l_List_head_x3f___redArg(v_chars_453_);
if (lean_obj_tag(v___x_474_) == 0)
{
uint8_t v___x_475_; 
lean_dec(v_chars_453_);
v___x_475_ = 0;
return v___x_475_;
}
else
{
lean_object* v_val_476_; uint8_t v___y_478_; uint32_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v_val_476_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_val_476_);
lean_dec_ref_known(v___x_474_, 1);
v___x_492_ = lean_unbox_uint32(v_val_476_);
v___x_493_ = lean_uint32_to_nat(v___x_492_);
v___x_494_ = lean_unsigned_to_nat(128u);
v___x_495_ = lean_nat_dec_lt(v___x_493_, v___x_494_);
lean_dec(v___x_493_);
if (v___x_495_ == 0)
{
lean_dec(v_val_476_);
lean_dec(v_chars_453_);
return v___x_495_;
}
else
{
uint32_t v___x_496_; uint32_t v___x_497_; uint8_t v___x_498_; 
v___x_496_ = 48;
v___x_497_ = lean_unbox_uint32(v_val_476_);
v___x_498_ = lean_uint32_dec_le(v___x_496_, v___x_497_);
if (v___x_498_ == 0)
{
goto v___jp_485_;
}
else
{
uint32_t v___x_499_; uint32_t v___x_500_; uint8_t v___x_501_; 
v___x_499_ = 57;
v___x_500_ = lean_unbox_uint32(v_val_476_);
v___x_501_ = lean_uint32_dec_le(v___x_500_, v___x_499_);
if (v___x_501_ == 0)
{
goto v___jp_485_;
}
else
{
lean_dec(v_val_476_);
goto v___jp_454_;
}
}
}
v___jp_477_:
{
if (v___y_478_ == 0)
{
uint32_t v___x_479_; uint32_t v___x_480_; uint8_t v___x_481_; 
v___x_479_ = 97;
v___x_480_ = lean_unbox_uint32(v_val_476_);
v___x_481_ = lean_uint32_dec_le(v___x_479_, v___x_480_);
if (v___x_481_ == 0)
{
lean_dec(v_val_476_);
lean_dec(v_chars_453_);
return v___x_481_;
}
else
{
uint32_t v___x_482_; uint32_t v___x_483_; uint8_t v___x_484_; 
v___x_482_ = 122;
v___x_483_ = lean_unbox_uint32(v_val_476_);
lean_dec(v_val_476_);
v___x_484_ = lean_uint32_dec_le(v___x_483_, v___x_482_);
if (v___x_484_ == 0)
{
lean_dec(v_chars_453_);
return v___x_484_;
}
else
{
goto v___jp_454_;
}
}
}
else
{
lean_dec(v_val_476_);
goto v___jp_454_;
}
}
v___jp_485_:
{
uint32_t v___x_486_; uint32_t v___x_487_; uint8_t v___x_488_; 
v___x_486_ = 65;
v___x_487_ = lean_unbox_uint32(v_val_476_);
v___x_488_ = lean_uint32_dec_le(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
v___y_478_ = v___x_488_;
goto v___jp_477_;
}
else
{
uint32_t v___x_489_; uint32_t v___x_490_; uint8_t v___x_491_; 
v___x_489_ = 90;
v___x_490_ = lean_unbox_uint32(v_val_476_);
v___x_491_ = lean_uint32_dec_le(v___x_490_, v___x_489_);
v___y_478_ = v___x_491_;
goto v___jp_477_;
}
}
}
}
}
v___jp_440_:
{
if (v___y_442_ == 0)
{
uint32_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 97;
v___x_444_ = lean_uint32_dec_le(v___x_443_, v___y_441_);
if (v___x_444_ == 0)
{
return v___x_444_;
}
else
{
uint32_t v___x_445_; uint8_t v___x_446_; 
v___x_445_ = 122;
v___x_446_ = lean_uint32_dec_le(v___y_441_, v___x_445_);
return v___x_446_;
}
}
else
{
return v___y_442_;
}
}
v___jp_447_:
{
uint32_t v___x_449_; uint8_t v___x_450_; 
v___x_449_ = 65;
v___x_450_ = lean_uint32_dec_le(v___x_449_, v___y_448_);
if (v___x_450_ == 0)
{
v___y_441_ = v___y_448_;
v___y_442_ = v___x_450_;
goto v___jp_440_;
}
else
{
uint32_t v___x_451_; uint8_t v___x_452_; 
v___x_451_ = 90;
v___x_452_ = lean_uint32_dec_le(v___y_448_, v___x_451_);
v___y_441_ = v___y_448_;
v___y_442_ = v___x_452_;
goto v___jp_440_;
}
}
v___jp_454_:
{
lean_object* v___x_455_; 
v___x_455_ = l_List_getLast_x3f___redArg(v_chars_453_);
lean_dec(v_chars_453_);
if (lean_obj_tag(v___x_455_) == 0)
{
uint8_t v___x_456_; 
v___x_456_ = 0;
return v___x_456_;
}
else
{
lean_object* v_val_457_; uint32_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v_val_457_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_val_457_);
lean_dec_ref_known(v___x_455_, 1);
v___x_458_ = lean_unbox_uint32(v_val_457_);
v___x_459_ = lean_uint32_to_nat(v___x_458_);
v___x_460_ = lean_unsigned_to_nat(128u);
v___x_461_ = lean_nat_dec_lt(v___x_459_, v___x_460_);
lean_dec(v___x_459_);
if (v___x_461_ == 0)
{
lean_dec(v_val_457_);
return v___x_461_;
}
else
{
uint32_t v___x_462_; uint32_t v___x_463_; uint8_t v___x_464_; 
v___x_462_ = 48;
v___x_463_ = lean_unbox_uint32(v_val_457_);
v___x_464_ = lean_uint32_dec_le(v___x_462_, v___x_463_);
if (v___x_464_ == 0)
{
uint32_t v___x_465_; 
v___x_465_ = lean_unbox_uint32(v_val_457_);
lean_dec(v_val_457_);
v___y_448_ = v___x_465_;
goto v___jp_447_;
}
else
{
uint32_t v___x_466_; uint32_t v___x_467_; uint8_t v___x_468_; 
v___x_466_ = 57;
v___x_467_ = lean_unbox_uint32(v_val_457_);
v___x_468_ = lean_uint32_dec_le(v___x_467_, v___x_466_);
if (v___x_468_ == 0)
{
uint32_t v___x_469_; 
v___x_469_ = lean_unbox_uint32(v_val_457_);
lean_dec(v_val_457_);
v___y_448_ = v___x_469_;
goto v___jp_447_;
}
else
{
lean_dec(v_val_457_);
return v___x_468_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_isValidDomainLabel___boxed(lean_object* v_s_502_){
_start:
{
uint8_t v_res_503_; lean_object* v_r_504_; 
v_res_503_ = l_Std_Http_URI_isValidDomainLabel(v_s_502_);
v_r_504_ = lean_box(v_res_503_);
return v_r_504_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(lean_object* v_s_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___closed__0));
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0___boxed(lean_object* v_s_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(v_s_509_);
lean_dec_ref(v_s_509_);
return v_res_510_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___redArg(lean_object* v_lower_511_, lean_object* v___x_512_, lean_object* v___x_513_, lean_object* v_a_514_, uint8_t v_b_515_){
_start:
{
if (lean_obj_tag(v_a_514_) == 0)
{
lean_object* v_currPos_516_; lean_object* v_searcher_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_554_; 
v_currPos_516_ = lean_ctor_get(v_a_514_, 0);
v_searcher_517_ = lean_ctor_get(v_a_514_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_a_514_);
if (v_isSharedCheck_554_ == 0)
{
v___x_519_ = v_a_514_;
v_isShared_520_ = v_isSharedCheck_554_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_searcher_517_);
lean_inc(v_currPos_516_);
lean_dec(v_a_514_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_554_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_str_521_; lean_object* v_startInclusive_522_; lean_object* v_endExclusive_523_; uint8_t v___x_524_; lean_object* v_it_526_; lean_object* v_startInclusive_527_; lean_object* v_endExclusive_528_; lean_object* v___x_532_; uint8_t v_decide_533_; 
v_str_521_ = lean_ctor_get(v___x_512_, 0);
v_startInclusive_522_ = lean_ctor_get(v___x_512_, 1);
v_endExclusive_523_ = lean_ctor_get(v___x_512_, 2);
v___x_524_ = 1;
v___x_532_ = lean_nat_sub(v_endExclusive_523_, v_startInclusive_522_);
v_decide_533_ = lean_nat_dec_eq(v_searcher_517_, v___x_532_);
lean_dec(v___x_532_);
if (v_decide_533_ == 0)
{
uint32_t v___x_534_; lean_object* v___x_535_; uint32_t v___x_536_; uint8_t v___x_537_; 
v___x_534_ = 46;
v___x_535_ = lean_nat_add(v_startInclusive_522_, v_searcher_517_);
v___x_536_ = lean_string_utf8_get_fast(v_str_521_, v___x_535_);
v___x_537_ = lean_uint32_dec_eq(v___x_536_, v___x_534_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
lean_dec(v_searcher_517_);
v___x_538_ = lean_string_utf8_next_fast(v_str_521_, v___x_535_);
lean_dec(v___x_535_);
v___x_539_ = lean_nat_sub(v___x_538_, v_startInclusive_522_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v___x_539_);
v___x_541_ = v___x_519_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_currPos_516_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v___x_539_);
v___x_541_ = v_reuseFailAlloc_543_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
v_a_514_ = v___x_541_;
goto _start;
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_slice_547_; lean_object* v_nextIt_549_; 
v___x_544_ = lean_string_utf8_next_fast(v_str_521_, v___x_535_);
v___x_545_ = lean_nat_sub(v___x_544_, v___x_535_);
lean_dec(v___x_535_);
v___x_546_ = lean_nat_add(v_searcher_517_, v___x_545_);
lean_dec(v___x_545_);
v_slice_547_ = l_String_Slice_subslice_x21(v___x_512_, v_currPos_516_, v_searcher_517_);
lean_inc(v___x_546_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v___x_546_);
lean_ctor_set(v___x_519_, 0, v___x_546_);
v_nextIt_549_ = v___x_519_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___x_546_);
v_nextIt_549_ = v_reuseFailAlloc_552_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v_startInclusive_550_; lean_object* v_endExclusive_551_; 
v_startInclusive_550_ = lean_ctor_get(v_slice_547_, 0);
lean_inc(v_startInclusive_550_);
v_endExclusive_551_ = lean_ctor_get(v_slice_547_, 1);
lean_inc(v_endExclusive_551_);
lean_dec_ref(v_slice_547_);
v_it_526_ = v_nextIt_549_;
v_startInclusive_527_ = v_startInclusive_550_;
v_endExclusive_528_ = v_endExclusive_551_;
goto v___jp_525_;
}
}
}
else
{
lean_object* v___x_553_; 
lean_del_object(v___x_519_);
lean_dec(v_searcher_517_);
v___x_553_ = lean_box(1);
lean_inc(v___x_513_);
v_it_526_ = v___x_553_;
v_startInclusive_527_ = v_currPos_516_;
v_endExclusive_528_ = v___x_513_;
goto v___jp_525_;
}
v___jp_525_:
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_string_utf8_extract_fast(v_lower_511_, v_startInclusive_527_, v_endExclusive_528_);
lean_dec(v_endExclusive_528_);
lean_dec(v_startInclusive_527_);
v___x_530_ = l_Std_Http_URI_isValidDomainLabel(v___x_529_);
if (v___x_530_ == 0)
{
lean_dec(v_it_526_);
lean_dec(v___x_513_);
return v___x_530_;
}
else
{
v_a_514_ = v_it_526_;
v_b_515_ = v___x_524_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_513_);
return v_b_515_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___redArg___boxed(lean_object* v_lower_555_, lean_object* v___x_556_, lean_object* v___x_557_, lean_object* v_a_558_, lean_object* v_b_559_){
_start:
{
uint8_t v_b_boxed_560_; uint8_t v_res_561_; lean_object* v_r_562_; 
v_b_boxed_560_ = lean_unbox(v_b_559_);
v_res_561_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___redArg(v_lower_555_, v___x_556_, v___x_557_, v_a_558_, v_b_boxed_560_);
lean_dec_ref(v___x_556_);
lean_dec_ref(v_lower_555_);
v_r_562_ = lean_box(v_res_561_);
return v_r_562_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(lean_object* v_lower_563_, lean_object* v___x_564_, lean_object* v___x_565_, lean_object* v_a_566_, uint8_t v_b_567_){
_start:
{
if (lean_obj_tag(v_a_566_) == 0)
{
lean_object* v_currPos_568_; lean_object* v_searcher_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_606_; 
v_currPos_568_ = lean_ctor_get(v_a_566_, 0);
v_searcher_569_ = lean_ctor_get(v_a_566_, 1);
v_isSharedCheck_606_ = !lean_is_exclusive(v_a_566_);
if (v_isSharedCheck_606_ == 0)
{
v___x_571_ = v_a_566_;
v_isShared_572_ = v_isSharedCheck_606_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_searcher_569_);
lean_inc(v_currPos_568_);
lean_dec(v_a_566_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_606_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v_str_573_; lean_object* v_startInclusive_574_; lean_object* v_endExclusive_575_; uint8_t v___x_576_; lean_object* v_it_578_; lean_object* v_startInclusive_579_; lean_object* v_endExclusive_580_; lean_object* v___x_584_; uint8_t v_decide_585_; 
v_str_573_ = lean_ctor_get(v___x_564_, 0);
v_startInclusive_574_ = lean_ctor_get(v___x_564_, 1);
v_endExclusive_575_ = lean_ctor_get(v___x_564_, 2);
v___x_576_ = 1;
v___x_584_ = lean_nat_sub(v_endExclusive_575_, v_startInclusive_574_);
v_decide_585_ = lean_nat_dec_eq(v_searcher_569_, v___x_584_);
lean_dec(v___x_584_);
if (v_decide_585_ == 0)
{
lean_object* v___x_586_; uint32_t v___x_587_; uint32_t v___x_588_; uint8_t v___x_589_; 
v___x_586_ = lean_nat_add(v_startInclusive_574_, v_searcher_569_);
v___x_587_ = lean_string_utf8_get_fast(v_str_573_, v___x_586_);
v___x_588_ = 46;
v___x_589_ = lean_uint32_dec_eq(v___x_587_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
lean_dec(v_searcher_569_);
v___x_590_ = lean_string_utf8_next_fast(v_str_573_, v___x_586_);
lean_dec(v___x_586_);
v___x_591_ = lean_nat_sub(v___x_590_, v_startInclusive_574_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 1, v___x_591_);
v___x_593_ = v___x_571_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_currPos_568_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___x_591_);
v___x_593_ = v_reuseFailAlloc_595_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
uint8_t v___x_594_; 
v___x_594_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___redArg(v_lower_563_, v___x_564_, v___x_565_, v___x_593_, v_b_567_);
return v___x_594_;
}
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_slice_599_; lean_object* v_nextIt_601_; 
v___x_596_ = lean_string_utf8_next_fast(v_str_573_, v___x_586_);
v___x_597_ = lean_nat_sub(v___x_596_, v___x_586_);
lean_dec(v___x_586_);
v___x_598_ = lean_nat_add(v_searcher_569_, v___x_597_);
lean_dec(v___x_597_);
v_slice_599_ = l_String_Slice_subslice_x21(v___x_564_, v_currPos_568_, v_searcher_569_);
lean_inc(v___x_598_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 1, v___x_598_);
lean_ctor_set(v___x_571_, 0, v___x_598_);
v_nextIt_601_ = v___x_571_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v___x_598_);
v_nextIt_601_ = v_reuseFailAlloc_604_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v_startInclusive_602_; lean_object* v_endExclusive_603_; 
v_startInclusive_602_ = lean_ctor_get(v_slice_599_, 0);
lean_inc(v_startInclusive_602_);
v_endExclusive_603_ = lean_ctor_get(v_slice_599_, 1);
lean_inc(v_endExclusive_603_);
lean_dec_ref(v_slice_599_);
v_it_578_ = v_nextIt_601_;
v_startInclusive_579_ = v_startInclusive_602_;
v_endExclusive_580_ = v_endExclusive_603_;
goto v___jp_577_;
}
}
}
else
{
lean_object* v___x_605_; 
lean_del_object(v___x_571_);
lean_dec(v_searcher_569_);
v___x_605_ = lean_box(1);
lean_inc(v___x_565_);
v_it_578_ = v___x_605_;
v_startInclusive_579_ = v_currPos_568_;
v_endExclusive_580_ = v___x_565_;
goto v___jp_577_;
}
v___jp_577_:
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = lean_string_utf8_extract_fast(v_lower_563_, v_startInclusive_579_, v_endExclusive_580_);
lean_dec(v_endExclusive_580_);
lean_dec(v_startInclusive_579_);
v___x_582_ = l_Std_Http_URI_isValidDomainLabel(v___x_581_);
if (v___x_582_ == 0)
{
lean_dec(v_it_578_);
lean_dec(v___x_565_);
return v___x_582_;
}
else
{
uint8_t v___x_583_; 
v___x_583_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___redArg(v_lower_563_, v___x_564_, v___x_565_, v_it_578_, v___x_576_);
return v___x_583_;
}
}
}
}
else
{
lean_dec(v___x_565_);
return v_b_567_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg___boxed(lean_object* v_lower_607_, lean_object* v___x_608_, lean_object* v___x_609_, lean_object* v_a_610_, lean_object* v_b_611_){
_start:
{
uint8_t v_b_boxed_612_; uint8_t v_res_613_; lean_object* v_r_614_; 
v_b_boxed_612_ = lean_unbox(v_b_611_);
v_res_613_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v_lower_607_, v___x_608_, v___x_609_, v_a_610_, v_b_boxed_612_);
lean_dec_ref(v___x_608_);
lean_dec_ref(v_lower_607_);
v_r_614_ = lean_box(v_res_613_);
return v_r_614_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1___redArg(lean_object* v___x_615_, lean_object* v___x_616_, lean_object* v_a_617_, uint8_t v_b_618_){
_start:
{
if (lean_obj_tag(v_a_617_) == 0)
{
lean_object* v_currPos_619_; lean_object* v_searcher_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_641_; 
v_currPos_619_ = lean_ctor_get(v_a_617_, 0);
v_searcher_620_ = lean_ctor_get(v_a_617_, 1);
v_isSharedCheck_641_ = !lean_is_exclusive(v_a_617_);
if (v_isSharedCheck_641_ == 0)
{
v___x_622_ = v_a_617_;
v_isShared_623_ = v_isSharedCheck_641_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_searcher_620_);
lean_inc(v_currPos_619_);
lean_dec(v_a_617_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_641_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_str_624_; lean_object* v_startInclusive_625_; lean_object* v_endExclusive_626_; lean_object* v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; uint8_t v_decide_630_; 
v_str_624_ = lean_ctor_get(v___x_616_, 0);
v_startInclusive_625_ = lean_ctor_get(v___x_616_, 1);
v_endExclusive_626_ = lean_ctor_get(v___x_616_, 2);
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_nat_dec_eq(v___x_615_, v___x_627_);
v___x_629_ = lean_nat_sub(v_endExclusive_626_, v_startInclusive_625_);
v_decide_630_ = lean_nat_dec_eq(v_searcher_620_, v___x_629_);
lean_dec(v___x_629_);
if (v_decide_630_ == 0)
{
uint32_t v___x_631_; lean_object* v___x_632_; uint32_t v___x_633_; uint8_t v___x_634_; 
v___x_631_ = 46;
v___x_632_ = lean_nat_add(v_startInclusive_625_, v_searcher_620_);
lean_dec(v_searcher_620_);
v___x_633_ = lean_string_utf8_get_fast(v_str_624_, v___x_632_);
v___x_634_ = lean_uint32_dec_eq(v___x_633_, v___x_631_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_635_ = lean_string_utf8_next_fast(v_str_624_, v___x_632_);
lean_dec(v___x_632_);
v___x_636_ = lean_nat_sub(v___x_635_, v_startInclusive_625_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v___x_636_);
v___x_638_ = v___x_622_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_currPos_619_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_636_);
v___x_638_ = v_reuseFailAlloc_640_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
v_a_617_ = v___x_638_;
goto _start;
}
}
else
{
lean_dec(v___x_632_);
lean_del_object(v___x_622_);
lean_dec(v_currPos_619_);
return v___x_628_;
}
}
else
{
lean_del_object(v___x_622_);
lean_dec(v_searcher_620_);
lean_dec(v_currPos_619_);
return v___x_628_;
}
}
}
else
{
return v_b_618_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1___redArg___boxed(lean_object* v___x_642_, lean_object* v___x_643_, lean_object* v_a_644_, lean_object* v_b_645_){
_start:
{
uint8_t v_b_boxed_646_; uint8_t v_res_647_; lean_object* v_r_648_; 
v_b_boxed_646_ = lean_unbox(v_b_645_);
v_res_647_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1___redArg(v___x_642_, v___x_643_, v_a_644_, v_b_boxed_646_);
lean_dec_ref(v___x_643_);
lean_dec(v___x_642_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(lean_object* v___x_649_, lean_object* v_lower_650_, lean_object* v___x_651_, lean_object* v___x_652_, lean_object* v_a_653_, uint8_t v_b_654_){
_start:
{
if (lean_obj_tag(v_a_653_) == 0)
{
lean_object* v_currPos_655_; lean_object* v_searcher_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_677_; 
v_currPos_655_ = lean_ctor_get(v_a_653_, 0);
v_searcher_656_ = lean_ctor_get(v_a_653_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v_a_653_);
if (v_isSharedCheck_677_ == 0)
{
v___x_658_ = v_a_653_;
v_isShared_659_ = v_isSharedCheck_677_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_searcher_656_);
lean_inc(v_currPos_655_);
lean_dec(v_a_653_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_677_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v_str_660_; lean_object* v_startInclusive_661_; lean_object* v_endExclusive_662_; lean_object* v___x_663_; uint8_t v___x_664_; lean_object* v___x_665_; uint8_t v_decide_666_; 
v_str_660_ = lean_ctor_get(v___x_651_, 0);
v_startInclusive_661_ = lean_ctor_get(v___x_651_, 1);
v_endExclusive_662_ = lean_ctor_get(v___x_651_, 2);
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_nat_dec_eq(v___x_649_, v___x_663_);
v___x_665_ = lean_nat_sub(v_endExclusive_662_, v_startInclusive_661_);
v_decide_666_ = lean_nat_dec_eq(v_searcher_656_, v___x_665_);
lean_dec(v___x_665_);
if (v_decide_666_ == 0)
{
lean_object* v___x_667_; uint32_t v___x_668_; uint32_t v___x_669_; uint8_t v___x_670_; 
v___x_667_ = lean_nat_add(v_startInclusive_661_, v_searcher_656_);
lean_dec(v_searcher_656_);
v___x_668_ = lean_string_utf8_get_fast(v_str_660_, v___x_667_);
v___x_669_ = 46;
v___x_670_ = lean_uint32_dec_eq(v___x_668_, v___x_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_671_ = lean_string_utf8_next_fast(v_str_660_, v___x_667_);
lean_dec(v___x_667_);
v___x_672_ = lean_nat_sub(v___x_671_, v_startInclusive_661_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_672_);
v___x_674_ = v___x_658_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_currPos_655_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_672_);
v___x_674_ = v_reuseFailAlloc_676_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
uint8_t v___x_675_; 
v___x_675_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1___redArg(v___x_649_, v___x_651_, v___x_674_, v_b_654_);
return v___x_675_;
}
}
else
{
lean_dec(v___x_667_);
lean_del_object(v___x_658_);
lean_dec(v_currPos_655_);
return v___x_664_;
}
}
else
{
lean_del_object(v___x_658_);
lean_dec(v_searcher_656_);
lean_dec(v_currPos_655_);
return v___x_664_;
}
}
}
else
{
return v_b_654_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg___boxed(lean_object* v___x_678_, lean_object* v_lower_679_, lean_object* v___x_680_, lean_object* v___x_681_, lean_object* v_a_682_, lean_object* v_b_683_){
_start:
{
uint8_t v_b_boxed_684_; uint8_t v_res_685_; lean_object* v_r_686_; 
v_b_boxed_684_ = lean_unbox(v_b_683_);
v_res_685_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_678_, v_lower_679_, v___x_680_, v___x_681_, v_a_682_, v_b_boxed_684_);
lean_dec(v___x_681_);
lean_dec_ref(v___x_680_);
lean_dec_ref(v_lower_679_);
lean_dec(v___x_678_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_DomainName_ofString_x3f(lean_object* v_s_687_){
_start:
{
lean_object* v___x_688_; lean_object* v_lower_689_; uint8_t v___y_691_; uint8_t v___y_692_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_688_ = lean_unsigned_to_nat(0u);
v_lower_689_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_687_, v___x_688_);
v___x_696_ = lean_string_utf8_byte_size(v_lower_689_);
v___x_697_ = lean_nat_dec_eq(v___x_696_, v___x_688_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; uint8_t v___y_702_; uint8_t v___x_707_; 
lean_inc_ref(v_lower_689_);
v___x_698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_698_, 0, v_lower_689_);
lean_ctor_set(v___x_698_, 1, v___x_688_);
lean_ctor_set(v___x_698_, 2, v___x_696_);
v___x_699_ = l_String_Slice_splitToSubslice___at___00Std_Http_URI_DomainName_ofString_x3f_spec__0(v___x_698_);
v___x_700_ = 1;
lean_inc(v___x_699_);
v___x_707_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_696_, v_lower_689_, v___x_698_, v___x_696_, v___x_699_, v___x_700_);
if (v___x_707_ == 0)
{
v___y_702_ = v___x_700_;
goto v___jp_701_;
}
else
{
v___y_702_ = v___x_697_;
goto v___jp_701_;
}
v___jp_701_:
{
uint8_t v___x_703_; 
v___x_703_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v_lower_689_, v___x_698_, v___x_696_, v___x_699_, v___x_700_);
lean_dec_ref_known(v___x_698_, 3);
if (v___x_703_ == 0)
{
v___y_691_ = v___y_702_;
v___y_692_ = v___x_703_;
goto v___jp_690_;
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_704_ = lean_string_length(v_lower_689_);
v___x_705_ = lean_unsigned_to_nat(255u);
v___x_706_ = lean_nat_dec_le(v___x_704_, v___x_705_);
v___y_691_ = v___y_702_;
v___y_692_ = v___x_706_;
goto v___jp_690_;
}
}
}
else
{
lean_object* v___x_708_; 
lean_dec_ref(v_lower_689_);
v___x_708_ = lean_box(0);
return v___x_708_;
}
v___jp_690_:
{
if (v___y_691_ == 0)
{
lean_object* v___x_693_; 
lean_dec_ref(v_lower_689_);
v___x_693_ = lean_box(0);
return v___x_693_;
}
else
{
if (v___y_692_ == 0)
{
lean_object* v___x_694_; 
lean_dec_ref(v_lower_689_);
v___x_694_ = lean_box(0);
return v___x_694_;
}
else
{
lean_object* v___x_695_; 
v___x_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_695_, 0, v_lower_689_);
return v___x_695_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(lean_object* v___x_709_, lean_object* v_lower_710_, lean_object* v___x_711_, lean_object* v___x_712_, lean_object* v_inst_713_, lean_object* v_R_714_, lean_object* v_a_715_, uint8_t v_b_716_, lean_object* v_c_717_){
_start:
{
uint8_t v___x_718_; 
v___x_718_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___redArg(v___x_709_, v_lower_710_, v___x_711_, v___x_712_, v_a_715_, v_b_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1___boxed(lean_object* v___x_719_, lean_object* v_lower_720_, lean_object* v___x_721_, lean_object* v___x_722_, lean_object* v_inst_723_, lean_object* v_R_724_, lean_object* v_a_725_, lean_object* v_b_726_, lean_object* v_c_727_){
_start:
{
uint8_t v_b_boxed_728_; uint8_t v_res_729_; lean_object* v_r_730_; 
v_b_boxed_728_ = lean_unbox(v_b_726_);
v_res_729_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1(v___x_719_, v_lower_720_, v___x_721_, v___x_722_, v_inst_723_, v_R_724_, v_a_725_, v_b_boxed_728_, v_c_727_);
lean_dec(v___x_722_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v_lower_720_);
lean_dec(v___x_719_);
v_r_730_ = lean_box(v_res_729_);
return v_r_730_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(lean_object* v_lower_731_, lean_object* v___x_732_, lean_object* v___x_733_, lean_object* v_inst_734_, lean_object* v_R_735_, lean_object* v_a_736_, uint8_t v_b_737_, lean_object* v_c_738_){
_start:
{
uint8_t v___x_739_; 
v___x_739_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___redArg(v_lower_731_, v___x_732_, v___x_733_, v_a_736_, v_b_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2___boxed(lean_object* v_lower_740_, lean_object* v___x_741_, lean_object* v___x_742_, lean_object* v_inst_743_, lean_object* v_R_744_, lean_object* v_a_745_, lean_object* v_b_746_, lean_object* v_c_747_){
_start:
{
uint8_t v_b_boxed_748_; uint8_t v_res_749_; lean_object* v_r_750_; 
v_b_boxed_748_ = lean_unbox(v_b_746_);
v_res_749_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2(v_lower_740_, v___x_741_, v___x_742_, v_inst_743_, v_R_744_, v_a_745_, v_b_boxed_748_, v_c_747_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v_lower_740_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1(lean_object* v___x_751_, lean_object* v_lower_752_, lean_object* v___x_753_, lean_object* v___x_754_, lean_object* v_inst_755_, lean_object* v_R_756_, lean_object* v_a_757_, uint8_t v_b_758_, lean_object* v_c_759_){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1___redArg(v___x_751_, v___x_753_, v_a_757_, v_b_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1___boxed(lean_object* v___x_761_, lean_object* v_lower_762_, lean_object* v___x_763_, lean_object* v___x_764_, lean_object* v_inst_765_, lean_object* v_R_766_, lean_object* v_a_767_, lean_object* v_b_768_, lean_object* v_c_769_){
_start:
{
uint8_t v_b_boxed_770_; uint8_t v_res_771_; lean_object* v_r_772_; 
v_b_boxed_770_ = lean_unbox(v_b_768_);
v_res_771_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__1_spec__1(v___x_761_, v_lower_762_, v___x_763_, v___x_764_, v_inst_765_, v_R_766_, v_a_767_, v_b_boxed_770_, v_c_769_);
lean_dec(v___x_764_);
lean_dec_ref(v___x_763_);
lean_dec_ref(v_lower_762_);
lean_dec(v___x_761_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3(lean_object* v_lower_773_, lean_object* v___x_774_, lean_object* v___x_775_, lean_object* v_inst_776_, lean_object* v_R_777_, lean_object* v_a_778_, uint8_t v_b_779_, lean_object* v_c_780_){
_start:
{
uint8_t v___x_781_; 
v___x_781_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___redArg(v_lower_773_, v___x_774_, v___x_775_, v_a_778_, v_b_779_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3___boxed(lean_object* v_lower_782_, lean_object* v___x_783_, lean_object* v___x_784_, lean_object* v_inst_785_, lean_object* v_R_786_, lean_object* v_a_787_, lean_object* v_b_788_, lean_object* v_c_789_){
_start:
{
uint8_t v_b_boxed_790_; uint8_t v_res_791_; lean_object* v_r_792_; 
v_b_boxed_790_ = lean_unbox(v_b_788_);
v_res_791_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Std_Http_URI_DomainName_ofString_x3f_spec__2_spec__3(v_lower_782_, v___x_783_, v___x_784_, v_inst_785_, v_R_786_, v_a_787_, v_b_boxed_790_, v_c_789_);
lean_dec_ref(v___x_783_);
lean_dec_ref(v_lower_782_);
v_r_792_ = lean_box(v_res_791_);
return v_r_792_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx(lean_object* v_x_793_){
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx___boxed(lean_object* v_x_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Std_Http_URI_Host_ctorIdx(v_x_797_);
lean_dec_ref(v_x_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___redArg(lean_object* v_t_799_, lean_object* v_k_800_){
_start:
{
lean_object* v_name_801_; lean_object* v___x_802_; 
v_name_801_ = lean_ctor_get(v_t_799_, 0);
lean_inc_ref(v_name_801_);
lean_dec_ref(v_t_799_);
v___x_802_ = lean_apply_1(v_k_800_, v_name_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim(lean_object* v_motive_803_, lean_object* v_ctorIdx_804_, lean_object* v_t_805_, lean_object* v_h_806_, lean_object* v_k_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_805_, v_k_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___boxed(lean_object* v_motive_809_, lean_object* v_ctorIdx_810_, lean_object* v_t_811_, lean_object* v_h_812_, lean_object* v_k_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Std_Http_URI_Host_ctorElim(v_motive_809_, v_ctorIdx_810_, v_t_811_, v_h_812_, v_k_813_);
lean_dec(v_ctorIdx_810_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim___redArg(lean_object* v_t_815_, lean_object* v_name_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_815_, v_name_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim(lean_object* v_motive_818_, lean_object* v_t_819_, lean_object* v_h_820_, lean_object* v_name_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_819_, v_name_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim___redArg(lean_object* v_t_823_, lean_object* v_ipv4_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_823_, v_ipv4_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim(lean_object* v_motive_826_, lean_object* v_t_827_, lean_object* v_h_828_, lean_object* v_ipv4_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_827_, v_ipv4_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim___redArg(lean_object* v_t_831_, lean_object* v_ipv6_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_831_, v_ipv6_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim(lean_object* v_motive_834_, lean_object* v_t_835_, lean_object* v_h_836_, lean_object* v_ipv6_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_835_, v_ipv6_837_);
return v___x_838_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default___closed__0(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default(void){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = lean_obj_once(&l_Std_Http_URI_instInhabitedHost_default___closed__0, &l_Std_Http_URI_instInhabitedHost_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedHost_default___closed__0);
return v___x_841_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost(void){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Std_Http_URI_instInhabitedHost_default;
return v___x_842_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqHost_beq(lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
switch(lean_obj_tag(v_x_843_))
{
case 0:
{
if (lean_obj_tag(v_x_844_) == 0)
{
lean_object* v_name_845_; lean_object* v_name_846_; uint8_t v___x_847_; 
v_name_845_ = lean_ctor_get(v_x_843_, 0);
v_name_846_ = lean_ctor_get(v_x_844_, 0);
v___x_847_ = lean_string_dec_eq(v_name_845_, v_name_846_);
return v___x_847_;
}
else
{
uint8_t v___x_848_; 
v___x_848_ = 0;
return v___x_848_;
}
}
case 1:
{
if (lean_obj_tag(v_x_844_) == 1)
{
lean_object* v_ipv4_849_; lean_object* v_ipv4_850_; uint8_t v___x_851_; 
v_ipv4_849_ = lean_ctor_get(v_x_843_, 0);
v_ipv4_850_ = lean_ctor_get(v_x_844_, 0);
v___x_851_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_ipv4_849_, v_ipv4_850_);
return v___x_851_;
}
else
{
uint8_t v___x_852_; 
v___x_852_ = 0;
return v___x_852_;
}
}
default: 
{
if (lean_obj_tag(v_x_844_) == 2)
{
lean_object* v_ipv6_853_; lean_object* v_ipv6_854_; uint8_t v___x_855_; 
v_ipv6_853_ = lean_ctor_get(v_x_843_, 0);
v_ipv6_854_ = lean_ctor_get(v_x_844_, 0);
v___x_855_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_ipv6_853_, v_ipv6_854_);
return v___x_855_;
}
else
{
uint8_t v___x_856_; 
v___x_856_ = 0;
return v___x_856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqHost_beq___boxed(lean_object* v_x_857_, lean_object* v_x_858_){
_start:
{
uint8_t v_res_859_; lean_object* v_r_860_; 
v_res_859_ = l_Std_Http_URI_instBEqHost_beq(v_x_857_, v_x_858_);
lean_dec_ref(v_x_858_);
lean_dec_ref(v_x_857_);
v_r_860_ = lean_box(v_res_859_);
return v_r_860_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__4(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = lean_unsigned_to_nat(2u);
v___x_868_ = lean_nat_to_int(v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__5(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_unsigned_to_nat(1u);
v___x_870_ = lean_nat_to_int(v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0(lean_object* v_x_871_, lean_object* v_prec_872_){
_start:
{
lean_object* v___y_874_; lean_object* v_ctr_875_; lean_object* v_a_876_; lean_object* v___y_888_; lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_919_ = lean_unsigned_to_nat(1024u);
v___x_920_ = lean_nat_dec_le(v___x_919_, v_prec_872_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; 
v___x_921_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_888_ = v___x_921_;
goto v___jp_887_;
}
else
{
lean_object* v___x_922_; 
v___x_922_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_888_ = v___x_922_;
goto v___jp_887_;
}
v___jp_873_:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_877_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_878_ = lean_string_append(v___x_877_, v_ctr_875_);
v___x_879_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
v___x_880_ = lean_box(1);
v___x_881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v_a_876_);
lean_inc(v___y_874_);
v___x_883_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_883_, 0, v___y_874_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = 0;
v___x_885_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set_uint8(v___x_885_, sizeof(void*)*1, v___x_884_);
v___x_886_ = l_Repr_addAppParen(v___x_885_, v_prec_872_);
return v___x_886_;
}
v___jp_887_:
{
switch(lean_obj_tag(v_x_871_))
{
case 0:
{
lean_object* v_name_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_898_; 
v_name_889_ = lean_ctor_get(v_x_871_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v_x_871_);
if (v_isSharedCheck_898_ == 0)
{
v___x_891_ = v_x_871_;
v_isShared_892_ = v_isSharedCheck_898_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_name_889_);
lean_dec(v_x_871_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_898_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_893_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_894_ = l_String_quote(v_name_889_);
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 3);
lean_ctor_set(v___x_891_, 0, v___x_894_);
v___x_896_ = v___x_891_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
v___y_874_ = v___y_888_;
v_ctr_875_ = v___x_893_;
v_a_876_ = v___x_896_;
goto v___jp_873_;
}
}
}
case 1:
{
lean_object* v_ipv4_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_908_; 
v_ipv4_899_ = lean_ctor_get(v_x_871_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v_x_871_);
if (v_isSharedCheck_908_ == 0)
{
v___x_901_ = v_x_871_;
v_isShared_902_ = v_isSharedCheck_908_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_ipv4_899_);
lean_dec(v_x_871_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_908_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_903_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_904_ = lean_uv_ntop_v4(v_ipv4_899_);
lean_dec_ref(v_ipv4_899_);
if (v_isShared_902_ == 0)
{
lean_ctor_set_tag(v___x_901_, 3);
lean_ctor_set(v___x_901_, 0, v___x_904_);
v___x_906_ = v___x_901_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
v___y_874_ = v___y_888_;
v_ctr_875_ = v___x_903_;
v_a_876_ = v___x_906_;
goto v___jp_873_;
}
}
}
default: 
{
lean_object* v_ipv6_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_918_; 
v_ipv6_909_ = lean_ctor_get(v_x_871_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v_x_871_);
if (v_isSharedCheck_918_ == 0)
{
v___x_911_ = v_x_871_;
v_isShared_912_ = v_isSharedCheck_918_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_ipv6_909_);
lean_dec(v_x_871_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_918_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_913_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_914_ = lean_uv_ntop_v6(v_ipv6_909_);
lean_dec_ref(v_ipv6_909_);
if (v_isShared_912_ == 0)
{
lean_ctor_set_tag(v___x_911_, 3);
lean_ctor_set(v___x_911_, 0, v___x_914_);
v___x_916_ = v___x_911_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
v___y_874_ = v___y_888_;
v_ctr_875_ = v___x_913_;
v_a_876_ = v___x_916_;
goto v___jp_873_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0___boxed(lean_object* v_x_923_, lean_object* v_prec_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_Http_URI_instReprHost___lam__0(v_x_923_, v_prec_924_);
lean_dec(v_prec_924_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0(lean_object* v_x_930_){
_start:
{
switch(lean_obj_tag(v_x_930_))
{
case 0:
{
lean_object* v_name_931_; 
v_name_931_ = lean_ctor_get(v_x_930_, 0);
lean_inc_ref(v_name_931_);
return v_name_931_;
}
case 1:
{
lean_object* v_ipv4_932_; lean_object* v___x_933_; 
v_ipv4_932_ = lean_ctor_get(v_x_930_, 0);
v___x_933_ = lean_uv_ntop_v4(v_ipv4_932_);
return v___x_933_;
}
default: 
{
lean_object* v_ipv6_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_ipv6_934_ = lean_ctor_get(v_x_930_, 0);
v___x_935_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_936_ = lean_uv_ntop_v6(v_ipv6_934_);
v___x_937_ = lean_string_append(v___x_935_, v___x_936_);
lean_dec_ref(v___x_936_);
v___x_938_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_939_ = lean_string_append(v___x_937_, v___x_938_);
return v___x_939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0___boxed(lean_object* v_x_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Std_Http_URI_instToStringHost___lam__0(v_x_940_);
lean_dec_ref(v_x_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx(lean_object* v_x_944_){
_start:
{
switch(lean_obj_tag(v_x_944_))
{
case 0:
{
lean_object* v___x_945_; 
v___x_945_ = lean_unsigned_to_nat(0u);
return v___x_945_;
}
case 1:
{
lean_object* v___x_946_; 
v___x_946_ = lean_unsigned_to_nat(1u);
return v___x_946_;
}
default: 
{
lean_object* v___x_947_; 
v___x_947_ = lean_unsigned_to_nat(2u);
return v___x_947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___boxed(lean_object* v_x_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_Http_URI_Port_ctorIdx(v_x_948_);
lean_dec(v_x_948_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg(lean_object* v_t_950_, lean_object* v_k_951_){
_start:
{
if (lean_obj_tag(v_t_950_) == 2)
{
uint16_t v_port_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_port_952_ = lean_ctor_get_uint16(v_t_950_, 0);
v___x_953_ = lean_box(v_port_952_);
v___x_954_ = lean_apply_1(v_k_951_, v___x_953_);
return v___x_954_;
}
else
{
return v_k_951_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg___boxed(lean_object* v_t_955_, lean_object* v_k_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_955_, v_k_956_);
lean_dec(v_t_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim(lean_object* v_motive_958_, lean_object* v_ctorIdx_959_, lean_object* v_t_960_, lean_object* v_h_961_, lean_object* v_k_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_960_, v_k_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___boxed(lean_object* v_motive_964_, lean_object* v_ctorIdx_965_, lean_object* v_t_966_, lean_object* v_h_967_, lean_object* v_k_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Std_Http_URI_Port_ctorElim(v_motive_964_, v_ctorIdx_965_, v_t_966_, v_h_967_, v_k_968_);
lean_dec(v_t_966_);
lean_dec(v_ctorIdx_965_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg(lean_object* v_t_970_, lean_object* v_omitted_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_970_, v_omitted_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg___boxed(lean_object* v_t_973_, lean_object* v_omitted_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_Http_URI_Port_omitted_elim___redArg(v_t_973_, v_omitted_974_);
lean_dec(v_t_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim(lean_object* v_motive_976_, lean_object* v_t_977_, lean_object* v_h_978_, lean_object* v_omitted_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_977_, v_omitted_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___boxed(lean_object* v_motive_981_, lean_object* v_t_982_, lean_object* v_h_983_, lean_object* v_omitted_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Std_Http_URI_Port_omitted_elim(v_motive_981_, v_t_982_, v_h_983_, v_omitted_984_);
lean_dec(v_t_982_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg(lean_object* v_t_986_, lean_object* v_empty_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_986_, v_empty_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg___boxed(lean_object* v_t_989_, lean_object* v_empty_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Std_Http_URI_Port_empty_elim___redArg(v_t_989_, v_empty_990_);
lean_dec(v_t_989_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim(lean_object* v_motive_992_, lean_object* v_t_993_, lean_object* v_h_994_, lean_object* v_empty_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_993_, v_empty_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___boxed(lean_object* v_motive_997_, lean_object* v_t_998_, lean_object* v_h_999_, lean_object* v_empty_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Std_Http_URI_Port_empty_elim(v_motive_997_, v_t_998_, v_h_999_, v_empty_1000_);
lean_dec(v_t_998_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg(lean_object* v_t_1002_, lean_object* v_value_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_1002_, v_value_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg___boxed(lean_object* v_t_1005_, lean_object* v_value_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_Http_URI_Port_value_elim___redArg(v_t_1005_, v_value_1006_);
lean_dec(v_t_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim(lean_object* v_motive_1008_, lean_object* v_t_1009_, lean_object* v_h_1010_, lean_object* v_value_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_1009_, v_value_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___boxed(lean_object* v_motive_1013_, lean_object* v_t_1014_, lean_object* v_h_1015_, lean_object* v_value_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Std_Http_URI_Port_value_elim(v_motive_1013_, v_t_1014_, v_h_1015_, v_value_1016_);
lean_dec(v_t_1014_);
return v_res_1017_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort_default(void){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_box(0);
return v___x_1018_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort(void){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_box(0);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr(lean_object* v_x_1032_, lean_object* v_prec_1033_){
_start:
{
lean_object* v___y_1035_; lean_object* v___y_1042_; 
switch(lean_obj_tag(v_x_1032_))
{
case 0:
{
lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1048_ = lean_unsigned_to_nat(1024u);
v___x_1049_ = lean_nat_dec_le(v___x_1048_, v_prec_1033_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_1042_ = v___x_1050_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_1042_ = v___x_1051_;
goto v___jp_1041_;
}
}
case 1:
{
lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = lean_unsigned_to_nat(1024u);
v___x_1053_ = lean_nat_dec_le(v___x_1052_, v_prec_1033_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_1035_ = v___x_1054_;
goto v___jp_1034_;
}
else
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_1035_ = v___x_1055_;
goto v___jp_1034_;
}
}
default: 
{
uint16_t v_port_1056_; lean_object* v___y_1058_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v_port_1056_ = lean_ctor_get_uint16(v_x_1032_, 0);
v___x_1068_ = lean_unsigned_to_nat(1024u);
v___x_1069_ = lean_nat_dec_le(v___x_1068_, v_prec_1033_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_1058_ = v___x_1070_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_1058_ = v___x_1071_;
goto v___jp_1057_;
}
v___jp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1059_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__6));
v___x_1060_ = lean_uint16_to_nat(v_port_1056_);
v___x_1061_ = l_Nat_reprFast(v___x_1060_);
v___x_1062_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1059_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
lean_inc(v___y_1058_);
v___x_1064_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___y_1058_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = 0;
v___x_1066_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set_uint8(v___x_1066_, sizeof(void*)*1, v___x_1065_);
v___x_1067_ = l_Repr_addAppParen(v___x_1066_, v_prec_1033_);
return v___x_1067_;
}
}
}
v___jp_1034_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1036_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__1));
lean_inc(v___y_1035_);
v___x_1037_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___y_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = 0;
v___x_1039_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set_uint8(v___x_1039_, sizeof(void*)*1, v___x_1038_);
v___x_1040_ = l_Repr_addAppParen(v___x_1039_, v_prec_1033_);
return v___x_1040_;
}
v___jp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1043_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__3));
lean_inc(v___y_1042_);
v___x_1044_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___y_1042_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = 0;
v___x_1046_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*1, v___x_1045_);
v___x_1047_ = l_Repr_addAppParen(v___x_1046_, v_prec_1033_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr___boxed(lean_object* v_x_1072_, lean_object* v_prec_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Std_Http_URI_instReprPort_repr(v_x_1072_, v_prec_1073_);
lean_dec(v_prec_1073_);
lean_dec(v_x_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort_decEq(lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
switch(lean_obj_tag(v_x_1077_))
{
case 0:
{
if (lean_obj_tag(v_x_1078_) == 0)
{
uint8_t v___x_1079_; 
v___x_1079_ = 1;
return v___x_1079_;
}
else
{
uint8_t v___x_1080_; 
v___x_1080_ = 0;
return v___x_1080_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1078_) == 1)
{
uint8_t v___x_1081_; 
v___x_1081_ = 1;
return v___x_1081_;
}
else
{
uint8_t v___x_1082_; 
v___x_1082_ = 0;
return v___x_1082_;
}
}
default: 
{
if (lean_obj_tag(v_x_1078_) == 2)
{
uint16_t v_port_1083_; uint16_t v_port_1084_; uint8_t v___x_1085_; 
v_port_1083_ = lean_ctor_get_uint16(v_x_1077_, 0);
v_port_1084_ = lean_ctor_get_uint16(v_x_1078_, 0);
v___x_1085_ = lean_uint16_dec_eq(v_port_1083_, v_port_1084_);
return v___x_1085_;
}
else
{
uint8_t v___x_1086_; 
v___x_1086_ = 0;
return v___x_1086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort_decEq___boxed(lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
uint8_t v_res_1089_; lean_object* v_r_1090_; 
v_res_1089_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_1087_, v_x_1088_);
lean_dec(v_x_1088_);
lean_dec(v_x_1087_);
v_r_1090_ = lean_box(v_res_1089_);
return v_r_1090_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort(lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
uint8_t v___x_1093_; 
v___x_1093_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_1091_, v_x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort___boxed(lean_object* v_x_1094_, lean_object* v_x_1095_){
_start:
{
uint8_t v_res_1096_; lean_object* v_r_1097_; 
v_res_1096_ = l_Std_Http_URI_instDecidableEqPort(v_x_1094_, v_x_1095_);
lean_dec(v_x_1095_);
lean_dec(v_x_1094_);
v_r_1097_ = lean_box(v_res_1096_);
return v_r_1097_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1098_ = lean_box(0);
v___x_1099_ = l_Std_Http_URI_instInhabitedHost_default;
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set(v___x_1101_, 1, v___x_1099_);
lean_ctor_set(v___x_1101_, 2, v___x_1098_);
return v___x_1101_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default(void){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_obj_once(&l_Std_Http_URI_instInhabitedAuthority_default___closed__0, &l_Std_Http_URI_instInhabitedAuthority_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0);
return v___x_1102_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority(void){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Std_Http_URI_instInhabitedAuthority_default;
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(lean_object* v_x_1104_, lean_object* v_x_1105_){
_start:
{
if (lean_obj_tag(v_x_1104_) == 0)
{
lean_object* v___x_1106_; 
v___x_1106_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1106_;
}
else
{
lean_object* v_val_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v_val_1107_ = lean_ctor_get(v_x_1104_, 0);
lean_inc(v_val_1107_);
lean_dec_ref_known(v_x_1104_, 1);
v___x_1108_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1109_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_val_1107_);
v___x_1110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = l_Repr_addAppParen(v___x_1110_, v_x_1105_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0___boxed(lean_object* v_x_1112_, lean_object* v_x_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_x_1112_, v_x_1113_);
lean_dec(v_x_1113_);
return v_res_1114_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_unsigned_to_nat(8u);
v___x_1128_ = lean_nat_to_int(v___x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg(lean_object* v_x_1132_){
_start:
{
lean_object* v_userInfo_1133_; lean_object* v_host_1134_; lean_object* v_port_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_ctr_1155_; lean_object* v_a_1156_; 
v_userInfo_1133_ = lean_ctor_get(v_x_1132_, 0);
lean_inc(v_userInfo_1133_);
v_host_1134_ = lean_ctor_get(v_x_1132_, 1);
lean_inc_ref(v_host_1134_);
v_port_1135_ = lean_ctor_get(v_x_1132_, 2);
lean_inc(v_port_1135_);
lean_dec_ref(v_x_1132_);
v___x_1136_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1137_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3));
v___x_1138_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_userInfo_1133_, v___x_1139_);
v___x_1141_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1138_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = 0;
v___x_1143_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set_uint8(v___x_1143_, sizeof(void*)*1, v___x_1142_);
v___x_1144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1137_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = lean_box(1);
v___x_1148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_1150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
lean_ctor_set(v___x_1151_, 1, v___x_1136_);
v___x_1152_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_1153_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_1134_))
{
case 0:
{
lean_object* v_name_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1193_; 
v_name_1184_ = lean_ctor_get(v_host_1134_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_host_1134_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1186_ = v_host_1134_;
v_isShared_1187_ = v_isSharedCheck_1193_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_name_1184_);
lean_dec(v_host_1134_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1193_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1188_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_1189_ = l_String_quote(v_name_1184_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set_tag(v___x_1186_, 3);
lean_ctor_set(v___x_1186_, 0, v___x_1189_);
v___x_1191_ = v___x_1186_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
v_ctr_1155_ = v___x_1188_;
v_a_1156_ = v___x_1191_;
goto v___jp_1154_;
}
}
}
case 1:
{
lean_object* v_ipv4_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1203_; 
v_ipv4_1194_ = lean_ctor_get(v_host_1134_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_host_1134_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1196_ = v_host_1134_;
v_isShared_1197_ = v_isSharedCheck_1203_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_ipv4_1194_);
lean_dec(v_host_1134_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1203_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1198_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_1199_ = lean_uv_ntop_v4(v_ipv4_1194_);
lean_dec_ref(v_ipv4_1194_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set_tag(v___x_1196_, 3);
lean_ctor_set(v___x_1196_, 0, v___x_1199_);
v___x_1201_ = v___x_1196_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
v_ctr_1155_ = v___x_1198_;
v_a_1156_ = v___x_1201_;
goto v___jp_1154_;
}
}
}
default: 
{
lean_object* v_ipv6_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1213_; 
v_ipv6_1204_ = lean_ctor_get(v_host_1134_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_host_1134_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1206_ = v_host_1134_;
v_isShared_1207_ = v_isSharedCheck_1213_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_ipv6_1204_);
lean_dec(v_host_1134_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1213_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1208_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_1209_ = lean_uv_ntop_v6(v_ipv6_1204_);
lean_dec_ref(v_ipv6_1204_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set_tag(v___x_1206_, 3);
lean_ctor_set(v___x_1206_, 0, v___x_1209_);
v___x_1211_ = v___x_1206_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
v_ctr_1155_ = v___x_1208_;
v_a_1156_ = v___x_1211_;
goto v___jp_1154_;
}
}
}
}
v___jp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1157_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_1158_ = lean_string_append(v___x_1157_, v_ctr_1155_);
v___x_1159_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
v___x_1160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v___x_1147_);
v___x_1161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v_a_1156_);
v___x_1162_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1153_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*1, v___x_1142_);
v___x_1164_ = l_Repr_addAppParen(v___x_1163_, v___x_1139_);
v___x_1165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1152_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*1, v___x_1142_);
v___x_1167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1151_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
lean_ctor_set(v___x_1168_, 1, v___x_1145_);
v___x_1169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v___x_1147_);
v___x_1170_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_1171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1169_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v___x_1136_);
v___x_1173_ = l_Std_Http_URI_instReprPort_repr(v_port_1135_, v___x_1139_);
lean_dec(v_port_1135_);
v___x_1174_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1152_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
lean_ctor_set_uint8(v___x_1175_, sizeof(void*)*1, v___x_1142_);
v___x_1176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1172_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1178_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v___x_1176_);
v___x_1180_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1177_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*1, v___x_1142_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr(lean_object* v_x_1214_, lean_object* v_prec_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_x_1214_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___boxed(lean_object* v_x_1217_, lean_object* v_prec_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Std_Http_URI_instReprAuthority_repr(v_x_1217_, v_prec_1218_);
lean_dec(v_prec_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(lean_object* v_x_1222_, lean_object* v_x_1223_){
_start:
{
if (lean_obj_tag(v_x_1222_) == 0)
{
if (lean_obj_tag(v_x_1223_) == 0)
{
uint8_t v___x_1224_; 
v___x_1224_ = 1;
return v___x_1224_;
}
else
{
uint8_t v___x_1225_; 
v___x_1225_ = 0;
return v___x_1225_;
}
}
else
{
if (lean_obj_tag(v_x_1223_) == 0)
{
uint8_t v___x_1226_; 
v___x_1226_ = 0;
return v___x_1226_;
}
else
{
lean_object* v_val_1227_; lean_object* v_val_1228_; uint8_t v___x_1229_; 
v_val_1227_ = lean_ctor_get(v_x_1222_, 0);
v_val_1228_ = lean_ctor_get(v_x_1223_, 0);
v___x_1229_ = l_Std_Http_URI_instBEqUserInfo_beq(v_val_1227_, v_val_1228_);
return v___x_1229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0___boxed(lean_object* v_x_1230_, lean_object* v_x_1231_){
_start:
{
uint8_t v_res_1232_; lean_object* v_r_1233_; 
v_res_1232_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_x_1230_, v_x_1231_);
lean_dec(v_x_1231_);
lean_dec(v_x_1230_);
v_r_1233_ = lean_box(v_res_1232_);
return v_r_1233_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqAuthority_beq(lean_object* v_x_1234_, lean_object* v_x_1235_){
_start:
{
lean_object* v_userInfo_1236_; lean_object* v_host_1237_; lean_object* v_port_1238_; lean_object* v_userInfo_1239_; lean_object* v_host_1240_; lean_object* v_port_1241_; uint8_t v___x_1242_; 
v_userInfo_1236_ = lean_ctor_get(v_x_1234_, 0);
v_host_1237_ = lean_ctor_get(v_x_1234_, 1);
v_port_1238_ = lean_ctor_get(v_x_1234_, 2);
v_userInfo_1239_ = lean_ctor_get(v_x_1235_, 0);
v_host_1240_ = lean_ctor_get(v_x_1235_, 1);
v_port_1241_ = lean_ctor_get(v_x_1235_, 2);
v___x_1242_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_userInfo_1236_, v_userInfo_1239_);
if (v___x_1242_ == 0)
{
return v___x_1242_;
}
else
{
uint8_t v___x_1243_; 
v___x_1243_ = l_Std_Http_URI_instBEqHost_beq(v_host_1237_, v_host_1240_);
if (v___x_1243_ == 0)
{
return v___x_1243_;
}
else
{
uint8_t v___x_1244_; 
v___x_1244_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1238_, v_port_1241_);
return v___x_1244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqAuthority_beq___boxed(lean_object* v_x_1245_, lean_object* v_x_1246_){
_start:
{
uint8_t v_res_1247_; lean_object* v_r_1248_; 
v_res_1247_ = l_Std_Http_URI_instBEqAuthority_beq(v_x_1245_, v_x_1246_);
lean_dec_ref(v_x_1246_);
lean_dec_ref(v_x_1245_);
v_r_1248_ = lean_box(v_res_1247_);
return v_r_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringAuthority___lam__0(lean_object* v_auth_1254_){
_start:
{
lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v_userInfo_1261_; lean_object* v_host_1262_; lean_object* v_port_1263_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1275_; 
v_userInfo_1261_ = lean_ctor_get(v_auth_1254_, 0);
lean_inc(v_userInfo_1261_);
v_host_1262_ = lean_ctor_get(v_auth_1254_, 1);
lean_inc_ref(v_host_1262_);
v_port_1263_ = lean_ctor_get(v_auth_1254_, 2);
lean_inc(v_port_1263_);
lean_dec_ref(v_auth_1254_);
if (lean_obj_tag(v_userInfo_1261_) == 0)
{
lean_object* v___x_1285_; 
v___x_1285_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1275_ = v___x_1285_;
goto v___jp_1274_;
}
else
{
lean_object* v_val_1286_; lean_object* v_password_1287_; 
v_val_1286_ = lean_ctor_get(v_userInfo_1261_, 0);
lean_inc(v_val_1286_);
lean_dec_ref_known(v_userInfo_1261_, 1);
v_password_1287_ = lean_ctor_get(v_val_1286_, 1);
if (lean_obj_tag(v_password_1287_) == 0)
{
lean_object* v_username_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_username_1288_ = lean_ctor_get(v_val_1286_, 0);
lean_inc_ref(v_username_1288_);
lean_dec(v_val_1286_);
v___x_1289_ = lean_string_from_utf8_unchecked(v_username_1288_);
v___x_1290_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1291_ = lean_string_append(v___x_1289_, v___x_1290_);
v___y_1275_ = v___x_1291_;
goto v___jp_1274_;
}
else
{
lean_object* v_username_1292_; lean_object* v_val_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_inc_ref(v_password_1287_);
v_username_1292_ = lean_ctor_get(v_val_1286_, 0);
lean_inc_ref(v_username_1292_);
lean_dec(v_val_1286_);
v_val_1293_ = lean_ctor_get(v_password_1287_, 0);
lean_inc(v_val_1293_);
lean_dec_ref_known(v_password_1287_, 1);
v___x_1294_ = lean_string_from_utf8_unchecked(v_username_1292_);
v___x_1295_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1296_ = lean_string_append(v___x_1294_, v___x_1295_);
v___x_1297_ = lean_string_from_utf8_unchecked(v_val_1293_);
v___x_1298_ = lean_string_append(v___x_1296_, v___x_1297_);
lean_dec_ref(v___x_1297_);
v___x_1299_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1300_ = lean_string_append(v___x_1298_, v___x_1299_);
v___y_1275_ = v___x_1300_;
goto v___jp_1274_;
}
}
v___jp_1255_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = lean_string_append(v___y_1256_, v___y_1257_);
lean_dec_ref(v___y_1257_);
v___x_1260_ = lean_string_append(v___x_1259_, v___y_1258_);
lean_dec_ref(v___y_1258_);
return v___x_1260_;
}
v___jp_1264_:
{
switch(lean_obj_tag(v_port_1263_))
{
case 0:
{
lean_object* v___x_1267_; 
v___x_1267_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_1256_ = v___y_1265_;
v___y_1257_ = v___y_1266_;
v___y_1258_ = v___x_1267_;
goto v___jp_1255_;
}
case 1:
{
lean_object* v___x_1268_; 
v___x_1268_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_1256_ = v___y_1265_;
v___y_1257_ = v___y_1266_;
v___y_1258_ = v___x_1268_;
goto v___jp_1255_;
}
default: 
{
uint16_t v_port_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v_port_1269_ = lean_ctor_get_uint16(v_port_1263_, 0);
lean_dec_ref_known(v_port_1263_, 0);
v___x_1270_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1271_ = lean_uint16_to_nat(v_port_1269_);
v___x_1272_ = l_Nat_reprFast(v___x_1271_);
v___x_1273_ = lean_string_append(v___x_1270_, v___x_1272_);
lean_dec_ref(v___x_1272_);
v___y_1256_ = v___y_1265_;
v___y_1257_ = v___y_1266_;
v___y_1258_ = v___x_1273_;
goto v___jp_1255_;
}
}
}
v___jp_1274_:
{
switch(lean_obj_tag(v_host_1262_))
{
case 0:
{
lean_object* v_name_1276_; 
v_name_1276_ = lean_ctor_get(v_host_1262_, 0);
lean_inc_ref(v_name_1276_);
lean_dec_ref_known(v_host_1262_, 1);
v___y_1265_ = v___y_1275_;
v___y_1266_ = v_name_1276_;
goto v___jp_1264_;
}
case 1:
{
lean_object* v_ipv4_1277_; lean_object* v___x_1278_; 
v_ipv4_1277_ = lean_ctor_get(v_host_1262_, 0);
lean_inc_ref(v_ipv4_1277_);
lean_dec_ref_known(v_host_1262_, 1);
v___x_1278_ = lean_uv_ntop_v4(v_ipv4_1277_);
lean_dec_ref(v_ipv4_1277_);
v___y_1265_ = v___y_1275_;
v___y_1266_ = v___x_1278_;
goto v___jp_1264_;
}
default: 
{
lean_object* v_ipv6_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v_ipv6_1279_ = lean_ctor_get(v_host_1262_, 0);
lean_inc_ref(v_ipv6_1279_);
lean_dec_ref_known(v_host_1262_, 1);
v___x_1280_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_1281_ = lean_uv_ntop_v6(v_ipv6_1279_);
lean_dec_ref(v_ipv6_1279_);
v___x_1282_ = lean_string_append(v___x_1280_, v___x_1281_);
lean_dec_ref(v___x_1281_);
v___x_1283_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_1284_ = lean_string_append(v___x_1282_, v___x_1283_);
v___y_1265_ = v___y_1275_;
v___y_1266_ = v___x_1284_;
goto v___jp_1264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1310_, lean_object* v_x_1311_, lean_object* v_x_1312_){
_start:
{
if (lean_obj_tag(v_x_1312_) == 0)
{
lean_dec(v_x_1310_);
return v_x_1311_;
}
else
{
lean_object* v_head_1313_; lean_object* v_tail_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1326_; 
v_head_1313_ = lean_ctor_get(v_x_1312_, 0);
v_tail_1314_ = lean_ctor_get(v_x_1312_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_x_1312_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1316_ = v_x_1312_;
v_isShared_1317_ = v_isSharedCheck_1326_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_tail_1314_);
lean_inc(v_head_1313_);
lean_dec(v_x_1312_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1326_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
lean_inc(v_x_1310_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set_tag(v___x_1316_, 5);
lean_ctor_set(v___x_1316_, 1, v_x_1310_);
lean_ctor_set(v___x_1316_, 0, v_x_1311_);
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_x_1311_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_x_1310_);
v___x_1319_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1320_ = lean_string_from_utf8_unchecked(v_head_1313_);
v___x_1321_ = l_String_quote(v___x_1320_);
v___x_1322_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1319_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v_x_1311_ = v___x_1323_;
v_x_1312_ = v_tail_1314_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(lean_object* v_x_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_){
_start:
{
if (lean_obj_tag(v_x_1329_) == 0)
{
lean_dec(v_x_1327_);
return v_x_1328_;
}
else
{
lean_object* v_head_1330_; lean_object* v_tail_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1343_; 
v_head_1330_ = lean_ctor_get(v_x_1329_, 0);
v_tail_1331_ = lean_ctor_get(v_x_1329_, 1);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_x_1329_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1333_ = v_x_1329_;
v_isShared_1334_ = v_isSharedCheck_1343_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_tail_1331_);
lean_inc(v_head_1330_);
lean_dec(v_x_1329_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1343_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
lean_inc(v_x_1327_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set_tag(v___x_1333_, 5);
lean_ctor_set(v___x_1333_, 1, v_x_1327_);
lean_ctor_set(v___x_1333_, 0, v_x_1328_);
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_x_1328_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_x_1327_);
v___x_1336_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1337_ = lean_string_from_utf8_unchecked(v_head_1330_);
v___x_1338_ = l_String_quote(v___x_1337_);
v___x_1339_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
v___x_1340_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1336_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(v_x_1327_, v___x_1340_, v_tail_1331_);
return v___x_1341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = lean_string_from_utf8_unchecked(v___y_1344_);
v___x_1346_ = l_String_quote(v___x_1345_);
v___x_1347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(lean_object* v_x_1348_, lean_object* v_x_1349_){
_start:
{
if (lean_obj_tag(v_x_1348_) == 0)
{
lean_object* v___x_1350_; 
lean_dec(v_x_1349_);
v___x_1350_ = lean_box(0);
return v___x_1350_;
}
else
{
lean_object* v_tail_1351_; 
v_tail_1351_ = lean_ctor_get(v_x_1348_, 1);
if (lean_obj_tag(v_tail_1351_) == 0)
{
lean_object* v_head_1352_; lean_object* v___x_1353_; 
lean_dec(v_x_1349_);
v_head_1352_ = lean_ctor_get(v_x_1348_, 0);
lean_inc(v_head_1352_);
lean_dec_ref_known(v_x_1348_, 2);
v___x_1353_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1352_);
return v___x_1353_;
}
else
{
lean_object* v_head_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_inc(v_tail_1351_);
v_head_1354_ = lean_ctor_get(v_x_1348_, 0);
lean_inc(v_head_1354_);
lean_dec_ref_known(v_x_1348_, 2);
v___x_1355_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1354_);
v___x_1356_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(v_x_1349_, v___x_1355_, v_tail_1351_);
return v___x_1356_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0));
v___x_1362_ = lean_string_length(v___x_1361_);
return v___x_1362_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2);
v___x_1364_ = lean_nat_to_int(v___x_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(lean_object* v_xs_1372_){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1373_ = lean_array_get_size(v_xs_1372_);
v___x_1374_ = lean_unsigned_to_nat(0u);
v___x_1375_ = lean_nat_dec_eq(v___x_1373_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1376_ = lean_array_to_list(v_xs_1372_);
v___x_1377_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1378_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(v___x_1376_, v___x_1377_);
v___x_1379_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1380_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
lean_ctor_set(v___x_1381_, 1, v___x_1378_);
v___x_1382_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1381_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1379_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
v___x_1385_ = l_Std_Format_fill(v___x_1384_);
return v___x_1385_;
}
else
{
lean_object* v___x_1386_; 
lean_dec_ref(v_xs_1372_);
v___x_1386_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1386_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___redArg(lean_object* v_x_1399_){
_start:
{
lean_object* v_segments_1400_; uint8_t v_absolute_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1433_; 
v_segments_1400_ = lean_ctor_get(v_x_1399_, 0);
v_absolute_1401_ = lean_ctor_get_uint8(v_x_1399_, sizeof(void*)*1);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_x_1399_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1403_ = v_x_1399_;
v_isShared_1404_ = v_isSharedCheck_1433_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_segments_1400_);
lean_dec(v_x_1399_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1433_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; lean_object* v___x_1412_; 
v___x_1405_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1406_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__3));
v___x_1407_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_1408_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(v_segments_1400_);
v___x_1409_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1407_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
v___x_1410_ = 0;
if (v_isShared_1404_ == 0)
{
lean_ctor_set_tag(v___x_1403_, 6);
lean_ctor_set(v___x_1403_, 0, v___x_1409_);
v___x_1412_ = v___x_1403_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1409_);
v___x_1412_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*1, v___x_1410_);
v___x_1413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1406_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1415_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1413_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = lean_box(1);
v___x_1417_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1415_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
v___x_1418_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__5));
v___x_1419_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1417_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
v___x_1420_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
lean_ctor_set(v___x_1420_, 1, v___x_1405_);
v___x_1421_ = l_Bool_repr___redArg(v_absolute_1401_);
v___x_1422_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1407_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
lean_ctor_set_uint8(v___x_1423_, sizeof(void*)*1, v___x_1410_);
v___x_1424_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1420_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___x_1425_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1426_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
lean_ctor_set(v___x_1427_, 1, v___x_1424_);
v___x_1428_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1429_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1425_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
v___x_1431_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set_uint8(v___x_1431_, sizeof(void*)*1, v___x_1410_);
return v___x_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr(lean_object* v_x_1434_, lean_object* v_prec_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Std_Http_URI_instReprPath_repr___redArg(v_x_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___boxed(lean_object* v_x_1437_, lean_object* v_prec_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Std_Http_URI_instReprPath_repr(v_x_1437_, v_prec_1438_);
lean_dec(v_prec_1438_);
return v_res_1439_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(lean_object* v_xs_1442_, lean_object* v_ys_1443_, lean_object* v_x_1444_){
_start:
{
lean_object* v_zero_1445_; uint8_t v_isZero_1446_; 
v_zero_1445_ = lean_unsigned_to_nat(0u);
v_isZero_1446_ = lean_nat_dec_eq(v_x_1444_, v_zero_1445_);
if (v_isZero_1446_ == 1)
{
lean_dec(v_x_1444_);
return v_isZero_1446_;
}
else
{
lean_object* v_one_1447_; lean_object* v_n_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v_one_1447_ = lean_unsigned_to_nat(1u);
v_n_1448_ = lean_nat_sub(v_x_1444_, v_one_1447_);
lean_dec(v_x_1444_);
v___x_1449_ = lean_array_fget_borrowed(v_xs_1442_, v_n_1448_);
v___x_1450_ = lean_array_fget_borrowed(v_ys_1443_, v_n_1448_);
v___x_1451_ = lean_sarray_dec_eq(v___x_1449_, v___x_1450_);
if (v___x_1451_ == 0)
{
lean_dec(v_n_1448_);
return v___x_1451_;
}
else
{
v_x_1444_ = v_n_1448_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg___boxed(lean_object* v_xs_1453_, lean_object* v_ys_1454_, lean_object* v_x_1455_){
_start:
{
uint8_t v_res_1456_; lean_object* v_r_1457_; 
v_res_1456_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1453_, v_ys_1454_, v_x_1455_);
lean_dec_ref(v_ys_1454_);
lean_dec_ref(v_xs_1453_);
v_r_1457_ = lean_box(v_res_1456_);
return v_r_1457_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqPath_beq(lean_object* v_x_1458_, lean_object* v_x_1459_){
_start:
{
lean_object* v_segments_1460_; uint8_t v_absolute_1461_; lean_object* v_segments_1462_; uint8_t v_absolute_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v_segments_1460_ = lean_ctor_get(v_x_1458_, 0);
v_absolute_1461_ = lean_ctor_get_uint8(v_x_1458_, sizeof(void*)*1);
v_segments_1462_ = lean_ctor_get(v_x_1459_, 0);
v_absolute_1463_ = lean_ctor_get_uint8(v_x_1459_, sizeof(void*)*1);
v___x_1464_ = lean_array_get_size(v_segments_1460_);
v___x_1465_ = lean_array_get_size(v_segments_1462_);
v___x_1466_ = lean_nat_dec_eq(v___x_1464_, v___x_1465_);
if (v___x_1466_ == 0)
{
return v___x_1466_;
}
else
{
uint8_t v___x_1467_; 
v___x_1467_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_segments_1460_, v_segments_1462_, v___x_1464_);
if (v___x_1467_ == 0)
{
return v___x_1467_;
}
else
{
if (v_absolute_1463_ == 0)
{
if (v_absolute_1461_ == 0)
{
return v___x_1467_;
}
else
{
return v_absolute_1463_;
}
}
else
{
return v_absolute_1461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqPath_beq___boxed(lean_object* v_x_1468_, lean_object* v_x_1469_){
_start:
{
uint8_t v_res_1470_; lean_object* v_r_1471_; 
v_res_1470_ = l_Std_Http_URI_instBEqPath_beq(v_x_1468_, v_x_1469_);
lean_dec_ref(v_x_1469_);
lean_dec_ref(v_x_1468_);
v_r_1471_ = lean_box(v_res_1470_);
return v_r_1471_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(lean_object* v_xs_1472_, lean_object* v_ys_1473_, lean_object* v_hsz_1474_, lean_object* v_x_1475_, lean_object* v_x_1476_){
_start:
{
uint8_t v___x_1477_; 
v___x_1477_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1472_, v_ys_1473_, v_x_1475_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___boxed(lean_object* v_xs_1478_, lean_object* v_ys_1479_, lean_object* v_hsz_1480_, lean_object* v_x_1481_, lean_object* v_x_1482_){
_start:
{
uint8_t v_res_1483_; lean_object* v_r_1484_; 
v_res_1483_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(v_xs_1478_, v_ys_1479_, v_hsz_1480_, v_x_1481_, v_x_1482_);
lean_dec_ref(v_ys_1479_);
lean_dec_ref(v_xs_1478_);
v_r_1484_ = lean_box(v_res_1483_);
return v_r_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__0(lean_object* v_x_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_string_from_utf8_unchecked(v_x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__1(lean_object* v___f_1509_, lean_object* v_path_1510_){
_start:
{
lean_object* v_segments_1511_; uint8_t v_absolute_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; size_t v_sz_1515_; size_t v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v_result_1519_; 
v_segments_1511_ = lean_ctor_get(v_path_1510_, 0);
lean_inc_ref(v_segments_1511_);
v_absolute_1512_ = lean_ctor_get_uint8(v_path_1510_, sizeof(void*)*1);
lean_dec_ref(v_path_1510_);
v___x_1513_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_1514_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_1515_ = lean_array_size(v_segments_1511_);
v___x_1516_ = ((size_t)0ULL);
v___x_1517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1514_, v___f_1509_, v_sz_1515_, v___x_1516_, v_segments_1511_);
v___x_1518_ = lean_array_to_list(v___x_1517_);
v_result_1519_ = l_String_intercalate(v___x_1513_, v___x_1518_);
if (v_absolute_1512_ == 0)
{
return v_result_1519_;
}
else
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_string_append(v___x_1513_, v_result_1519_);
lean_dec_ref(v_result_1519_);
return v___x_1520_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Path_isEmpty(lean_object* v_p_1525_){
_start:
{
lean_object* v_segments_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
v_segments_1526_ = lean_ctor_get(v_p_1525_, 0);
v___x_1527_ = lean_array_get_size(v_segments_1526_);
v___x_1528_ = lean_unsigned_to_nat(0u);
v___x_1529_ = lean_nat_dec_eq(v___x_1527_, v___x_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_isEmpty___boxed(lean_object* v_p_1530_){
_start:
{
uint8_t v_res_1531_; lean_object* v_r_1532_; 
v_res_1531_ = l_Std_Http_URI_Path_isEmpty(v_p_1530_);
lean_dec_ref(v_p_1530_);
v_r_1532_ = lean_box(v_res_1531_);
return v_r_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parent(lean_object* v_p_1533_){
_start:
{
lean_object* v_segments_1534_; uint8_t v_absolute_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_segments_1534_ = lean_ctor_get(v_p_1533_, 0);
v_absolute_1535_ = lean_ctor_get_uint8(v_p_1533_, sizeof(void*)*1);
v___x_1536_ = lean_array_get_size(v_segments_1534_);
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = lean_nat_dec_eq(v___x_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1546_; 
lean_inc_ref(v_segments_1534_);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_p_1533_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v_p_1533_, 0);
lean_dec(v_unused_1547_);
v___x_1540_ = v_p_1533_;
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
else
{
lean_dec(v_p_1533_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1542_ = lean_array_pop(v_segments_1534_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1542_);
v___x_1544_ = v___x_1540_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
lean_ctor_set_uint8(v_reuseFailAlloc_1545_, sizeof(void*)*1, v_absolute_1535_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
else
{
return v_p_1533_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join(lean_object* v_p1_1548_, lean_object* v_p2_1549_){
_start:
{
uint8_t v_absolute_1550_; 
v_absolute_1550_ = lean_ctor_get_uint8(v_p2_1549_, sizeof(void*)*1);
if (v_absolute_1550_ == 0)
{
lean_object* v_segments_1551_; lean_object* v_segments_1552_; uint8_t v_absolute_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1561_; 
v_segments_1551_ = lean_ctor_get(v_p2_1549_, 0);
v_segments_1552_ = lean_ctor_get(v_p1_1548_, 0);
v_absolute_1553_ = lean_ctor_get_uint8(v_p1_1548_, sizeof(void*)*1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_p1_1548_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1555_ = v_p1_1548_;
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_segments_1552_);
lean_dec(v_p1_1548_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = l_Array_append___redArg(v_segments_1552_, v_segments_1551_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1557_);
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
lean_ctor_set_uint8(v_reuseFailAlloc_1560_, sizeof(void*)*1, v_absolute_1553_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
else
{
lean_dec_ref(v_p1_1548_);
lean_inc_ref(v_p2_1549_);
return v_p2_1549_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join___boxed(lean_object* v_p1_1562_, lean_object* v_p2_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Std_Http_URI_Path_join(v_p1_1562_, v_p2_1563_);
lean_dec_ref(v_p2_1563_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append(lean_object* v_p_1565_, lean_object* v_segment_1566_){
_start:
{
lean_object* v_segments_1567_; uint8_t v_absolute_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1577_; 
v_segments_1567_ = lean_ctor_get(v_p_1565_, 0);
v_absolute_1568_ = lean_ctor_get_uint8(v_p_1565_, sizeof(void*)*1);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_p_1565_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1570_ = v_p_1565_;
v_isShared_1571_ = v_isSharedCheck_1577_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_segments_1567_);
lean_dec(v_p_1565_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1577_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1572_ = l_Std_Http_URI_EncodedSegment_encode(v_segment_1566_);
v___x_1573_ = lean_array_push(v_segments_1567_, v___x_1572_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1573_);
v___x_1575_ = v___x_1570_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
lean_ctor_set_uint8(v_reuseFailAlloc_1576_, sizeof(void*)*1, v_absolute_1568_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append___boxed(lean_object* v_p_1578_, lean_object* v_segment_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Std_Http_URI_Path_append(v_p_1578_, v_segment_1579_);
lean_dec_ref(v_segment_1579_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_appendEncoded(lean_object* v_p_1581_, lean_object* v_segment_1582_){
_start:
{
lean_object* v_segments_1583_; uint8_t v_absolute_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1592_; 
v_segments_1583_ = lean_ctor_get(v_p_1581_, 0);
v_absolute_1584_ = lean_ctor_get_uint8(v_p_1581_, sizeof(void*)*1);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_p_1581_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1586_ = v_p_1581_;
v_isShared_1587_ = v_isSharedCheck_1592_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_segments_1583_);
lean_dec(v_p_1581_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1592_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1588_ = lean_array_push(v_segments_1583_, v_segment_1582_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1588_);
v___x_1590_ = v___x_1586_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
lean_ctor_set_uint8(v_reuseFailAlloc_1591_, sizeof(void*)*1, v_absolute_1584_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(lean_object* v_input_1595_, lean_object* v_output_1596_){
_start:
{
if (lean_obj_tag(v_input_1595_) == 0)
{
lean_object* v___x_1597_; 
v___x_1597_ = l_List_reverse___redArg(v_output_1596_);
return v___x_1597_;
}
else
{
lean_object* v_head_1598_; lean_object* v_tail_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1616_; 
v_head_1598_ = lean_ctor_get(v_input_1595_, 0);
v_tail_1599_ = lean_ctor_get(v_input_1595_, 1);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_input_1595_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1601_ = v_input_1595_;
v_isShared_1602_ = v_isSharedCheck_1616_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_tail_1599_);
lean_inc(v_head_1598_);
lean_dec(v_input_1595_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1616_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
lean_inc(v_head_1598_);
v___x_1603_ = lean_string_from_utf8_unchecked(v_head_1598_);
v___x_1604_ = ((lean_object*)(l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0));
v___x_1605_ = lean_string_dec_eq(v___x_1603_, v___x_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1606_ = ((lean_object*)(l___private_Std_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__1));
v___x_1607_ = lean_string_dec_eq(v___x_1603_, v___x_1606_);
lean_dec_ref(v___x_1603_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1609_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 1, v_output_1596_);
v___x_1609_ = v___x_1601_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_head_1598_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_output_1596_);
v___x_1609_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
v_input_1595_ = v_tail_1599_;
v_output_1596_ = v___x_1609_;
goto _start;
}
}
else
{
lean_del_object(v___x_1601_);
lean_dec(v_head_1598_);
if (lean_obj_tag(v_output_1596_) == 0)
{
v_input_1595_ = v_tail_1599_;
goto _start;
}
else
{
lean_object* v_tail_1613_; 
v_tail_1613_ = lean_ctor_get(v_output_1596_, 1);
lean_inc(v_tail_1613_);
lean_dec_ref_known(v_output_1596_, 2);
v_input_1595_ = v_tail_1599_;
v_output_1596_ = v_tail_1613_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_1603_);
lean_del_object(v___x_1601_);
lean_dec(v_head_1598_);
v_input_1595_ = v_tail_1599_;
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
v___x_1834_ = l_Option_instBEq_beq___redArg(v___f_1826_, v_snd_1830_, v_snd_1832_);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(lean_object* v_x_1854_, lean_object* v_x_1855_){
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
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0___boxed(lean_object* v_x_1862_, lean_object* v_x_1863_){
_start:
{
uint8_t v_res_1864_; lean_object* v_r_1865_; 
v_res_1864_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_x_1862_, v_x_1863_);
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
v___x_1880_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_snd_1875_, v_snd_1878_);
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
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(lean_object* v_as_1912_){
_start:
{
lean_object* v___f_1913_; lean_object* v___x_1914_; 
v___f_1913_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__0));
v___x_1914_ = l_List_eraseDupsBy___redArg(v___f_1913_, v_as_1912_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(size_t v_sz_1915_, size_t v_i_1916_, lean_object* v_bs_1917_){
_start:
{
uint8_t v___x_1918_; 
v___x_1918_ = lean_usize_dec_lt(v_i_1916_, v_sz_1915_);
if (v___x_1918_ == 0)
{
return v_bs_1917_;
}
else
{
lean_object* v_v_1919_; lean_object* v_fst_1920_; lean_object* v___x_1921_; lean_object* v_bs_x27_1922_; size_t v___x_1923_; size_t v___x_1924_; lean_object* v___x_1925_; 
v_v_1919_ = lean_array_uget_borrowed(v_bs_1917_, v_i_1916_);
v_fst_1920_ = lean_ctor_get(v_v_1919_, 0);
lean_inc(v_fst_1920_);
v___x_1921_ = lean_unsigned_to_nat(0u);
v_bs_x27_1922_ = lean_array_uset(v_bs_1917_, v_i_1916_, v___x_1921_);
v___x_1923_ = ((size_t)1ULL);
v___x_1924_ = lean_usize_add(v_i_1916_, v___x_1923_);
v___x_1925_ = lean_array_uset(v_bs_x27_1922_, v_i_1916_, v_fst_1920_);
v_i_1916_ = v___x_1924_;
v_bs_1917_ = v___x_1925_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0___boxed(lean_object* v_sz_1927_, lean_object* v_i_1928_, lean_object* v_bs_1929_){
_start:
{
size_t v_sz_boxed_1930_; size_t v_i_boxed_1931_; lean_object* v_res_1932_; 
v_sz_boxed_1930_ = lean_unbox_usize(v_sz_1927_);
lean_dec(v_sz_1927_);
v_i_boxed_1931_ = lean_unbox_usize(v_i_1928_);
lean_dec(v_i_1928_);
v_res_1932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_boxed_1930_, v_i_boxed_1931_, v_bs_1929_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names(lean_object* v_query_1933_){
_start:
{
size_t v_sz_1934_; size_t v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_sz_1934_ = lean_array_size(v_query_1933_);
v___x_1935_ = ((size_t)0ULL);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_1934_, v___x_1935_, v_query_1933_);
v___x_1937_ = lean_array_to_list(v___x_1936_);
v___x_1938_ = l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(v___x_1937_);
v___x_1939_ = lean_array_mk(v___x_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(size_t v_sz_1940_, size_t v_i_1941_, lean_object* v_bs_1942_){
_start:
{
uint8_t v___x_1943_; 
v___x_1943_ = lean_usize_dec_lt(v_i_1941_, v_sz_1940_);
if (v___x_1943_ == 0)
{
return v_bs_1942_;
}
else
{
lean_object* v_v_1944_; lean_object* v_snd_1945_; lean_object* v___x_1946_; lean_object* v_bs_x27_1947_; size_t v___x_1948_; size_t v___x_1949_; lean_object* v___x_1950_; 
v_v_1944_ = lean_array_uget_borrowed(v_bs_1942_, v_i_1941_);
v_snd_1945_ = lean_ctor_get(v_v_1944_, 1);
lean_inc(v_snd_1945_);
v___x_1946_ = lean_unsigned_to_nat(0u);
v_bs_x27_1947_ = lean_array_uset(v_bs_1942_, v_i_1941_, v___x_1946_);
v___x_1948_ = ((size_t)1ULL);
v___x_1949_ = lean_usize_add(v_i_1941_, v___x_1948_);
v___x_1950_ = lean_array_uset(v_bs_x27_1947_, v_i_1941_, v_snd_1945_);
v_i_1941_ = v___x_1949_;
v_bs_1942_ = v___x_1950_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0___boxed(lean_object* v_sz_1952_, lean_object* v_i_1953_, lean_object* v_bs_1954_){
_start:
{
size_t v_sz_boxed_1955_; size_t v_i_boxed_1956_; lean_object* v_res_1957_; 
v_sz_boxed_1955_ = lean_unbox_usize(v_sz_1952_);
lean_dec(v_sz_1952_);
v_i_boxed_1956_ = lean_unbox_usize(v_i_1953_);
lean_dec(v_i_1953_);
v_res_1957_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_boxed_1955_, v_i_boxed_1956_, v_bs_1954_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_values(lean_object* v_query_1958_){
_start:
{
size_t v_sz_1959_; size_t v___x_1960_; lean_object* v___x_1961_; 
v_sz_1959_ = lean_array_size(v_query_1958_);
v___x_1960_ = ((size_t)0ULL);
v___x_1961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_1959_, v___x_1960_, v_query_1958_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray(lean_object* v_query_1962_){
_start:
{
lean_inc_ref(v_query_1962_);
return v_query_1962_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray___boxed(lean_object* v_query_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Std_Http_URI_Query_toArray(v_query_1963_);
lean_dec_ref(v_query_1963_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object* v_key_1966_, lean_object* v_value_1967_){
_start:
{
if (lean_obj_tag(v_value_1967_) == 0)
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_string_from_utf8_unchecked(v_key_1966_);
return v___x_1968_;
}
else
{
lean_object* v_val_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v_val_1969_ = lean_ctor_get(v_value_1967_, 0);
lean_inc(v_val_1969_);
lean_dec_ref_known(v_value_1967_, 1);
v___x_1970_ = lean_string_from_utf8_unchecked(v_key_1966_);
v___x_1971_ = ((lean_object*)(l_Std_Http_URI_Query_formatQueryParam___closed__0));
v___x_1972_ = lean_string_append(v___x_1970_, v___x_1971_);
v___x_1973_ = lean_string_from_utf8_unchecked(v_val_1969_);
v___x_1974_ = lean_string_append(v___x_1972_, v___x_1973_);
lean_dec_ref(v___x_1973_);
return v___x_1974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(lean_object* v_key_1978_, lean_object* v_as_1979_, size_t v_sz_1980_, size_t v_i_1981_, lean_object* v_b_1982_){
_start:
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_usize_dec_lt(v_i_1981_, v_sz_1980_);
if (v___x_1983_ == 0)
{
lean_inc_ref(v_b_1982_);
return v_b_1982_;
}
else
{
lean_object* v_a_1984_; lean_object* v_fst_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v_a_1984_ = lean_array_uget_borrowed(v_as_1979_, v_i_1981_);
v_fst_1985_ = lean_ctor_get(v_a_1984_, 0);
v___x_1986_ = lean_box(0);
v___x_1987_ = lean_sarray_dec_eq(v_fst_1985_, v_key_1978_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; size_t v___x_1989_; size_t v___x_1990_; 
v___x_1988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v___x_1989_ = ((size_t)1ULL);
v___x_1990_ = lean_usize_add(v_i_1981_, v___x_1989_);
v_i_1981_ = v___x_1990_;
v_b_1982_ = v___x_1988_;
goto _start;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
lean_inc(v_a_1984_);
v___x_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1992_, 0, v_a_1984_);
v___x_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
v___x_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
lean_ctor_set(v___x_1994_, 1, v___x_1986_);
return v___x_1994_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___boxed(lean_object* v_key_1995_, lean_object* v_as_1996_, lean_object* v_sz_1997_, lean_object* v_i_1998_, lean_object* v_b_1999_){
_start:
{
size_t v_sz_boxed_2000_; size_t v_i_boxed_2001_; lean_object* v_res_2002_; 
v_sz_boxed_2000_ = lean_unbox_usize(v_sz_1997_);
lean_dec(v_sz_1997_);
v_i_boxed_2001_ = lean_unbox_usize(v_i_1998_);
lean_dec(v_i_1998_);
v_res_2002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1995_, v_as_1996_, v_sz_boxed_2000_, v_i_boxed_2001_, v_b_1999_);
lean_dec_ref(v_b_1999_);
lean_dec_ref(v_as_1996_);
lean_dec_ref(v_key_1995_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f(lean_object* v_query_2003_, lean_object* v_key_2004_){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; size_t v_sz_2007_; size_t v___x_2008_; lean_object* v___x_2009_; lean_object* v_fst_2010_; 
v___x_2005_ = lean_box(0);
v___x_2006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v_sz_2007_ = lean_array_size(v_query_2003_);
v___x_2008_ = ((size_t)0ULL);
v___x_2009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_2004_, v_query_2003_, v_sz_2007_, v___x_2008_, v___x_2006_);
v_fst_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_fst_2010_);
lean_dec_ref(v___x_2009_);
if (lean_obj_tag(v_fst_2010_) == 0)
{
return v___x_2005_;
}
else
{
lean_object* v_val_2011_; 
v_val_2011_ = lean_ctor_get(v_fst_2010_, 0);
lean_inc(v_val_2011_);
lean_dec_ref_known(v_fst_2010_, 1);
if (lean_obj_tag(v_val_2011_) == 0)
{
return v___x_2005_;
}
else
{
lean_object* v_val_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2020_; 
v_val_2012_ = lean_ctor_get(v_val_2011_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_val_2011_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2014_ = v_val_2011_;
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_val_2012_);
lean_dec(v_val_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v_snd_2016_; lean_object* v___x_2018_; 
v_snd_2016_ = lean_ctor_get(v_val_2012_, 1);
lean_inc(v_snd_2016_);
lean_dec(v_val_2012_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v_snd_2016_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_snd_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f___boxed(lean_object* v_query_2021_, lean_object* v_key_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_2021_, v_key_2022_);
lean_dec_ref(v_key_2022_);
lean_dec_ref(v_query_2021_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f(lean_object* v_query_2024_, lean_object* v_key_2025_){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_2025_);
v___x_2027_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_2024_, v___x_2026_);
lean_dec_ref(v___x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f___boxed(lean_object* v_query_2028_, lean_object* v_key_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Std_Http_URI_Query_find_x3f(v_query_2028_, v_key_2029_);
lean_dec_ref(v_key_2029_);
lean_dec_ref(v_query_2028_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(lean_object* v_key_2031_, lean_object* v_as_2032_, size_t v_i_2033_, size_t v_stop_2034_, lean_object* v_b_2035_){
_start:
{
lean_object* v___y_2037_; uint8_t v___x_2041_; 
v___x_2041_ = lean_usize_dec_eq(v_i_2033_, v_stop_2034_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; lean_object* v_fst_2043_; lean_object* v_snd_2044_; uint8_t v___x_2045_; 
v___x_2042_ = lean_array_uget_borrowed(v_as_2032_, v_i_2033_);
v_fst_2043_ = lean_ctor_get(v___x_2042_, 0);
v_snd_2044_ = lean_ctor_get(v___x_2042_, 1);
v___x_2045_ = lean_sarray_dec_eq(v_fst_2043_, v_key_2031_);
if (v___x_2045_ == 0)
{
v___y_2037_ = v_b_2035_;
goto v___jp_2036_;
}
else
{
lean_object* v___x_2046_; 
lean_inc(v_snd_2044_);
v___x_2046_ = lean_array_push(v_b_2035_, v_snd_2044_);
v___y_2037_ = v___x_2046_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0___boxed(lean_object* v_key_2047_, lean_object* v_as_2048_, lean_object* v_i_2049_, lean_object* v_stop_2050_, lean_object* v_b_2051_){
_start:
{
size_t v_i_boxed_2052_; size_t v_stop_boxed_2053_; lean_object* v_res_2054_; 
v_i_boxed_2052_ = lean_unbox_usize(v_i_2049_);
lean_dec(v_i_2049_);
v_stop_boxed_2053_ = lean_unbox_usize(v_stop_2050_);
lean_dec(v_stop_2050_);
v_res_2054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_2047_, v_as_2048_, v_i_boxed_2052_, v_stop_boxed_2053_, v_b_2051_);
lean_dec_ref(v_as_2048_);
lean_dec_ref(v_key_2047_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(lean_object* v_key_2057_, lean_object* v_as_2058_, lean_object* v_start_2059_, lean_object* v_stop_2060_){
_start:
{
lean_object* v___x_2061_; uint8_t v___x_2062_; 
v___x_2061_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_2062_ = lean_nat_dec_lt(v_start_2059_, v_stop_2060_);
if (v___x_2062_ == 0)
{
return v___x_2061_;
}
else
{
lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2063_ = lean_array_get_size(v_as_2058_);
v___x_2064_ = lean_nat_dec_le(v_stop_2060_, v___x_2063_);
if (v___x_2064_ == 0)
{
uint8_t v___x_2065_; 
v___x_2065_ = lean_nat_dec_lt(v_start_2059_, v___x_2063_);
if (v___x_2065_ == 0)
{
return v___x_2061_;
}
else
{
size_t v___x_2066_; size_t v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = lean_usize_of_nat(v_start_2059_);
v___x_2067_ = lean_usize_of_nat(v___x_2063_);
v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_2057_, v_as_2058_, v___x_2066_, v___x_2067_, v___x_2061_);
return v___x_2068_;
}
}
else
{
size_t v___x_2069_; size_t v___x_2070_; lean_object* v___x_2071_; 
v___x_2069_ = lean_usize_of_nat(v_start_2059_);
v___x_2070_ = lean_usize_of_nat(v_stop_2060_);
v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_2057_, v_as_2058_, v___x_2069_, v___x_2070_, v___x_2061_);
return v___x_2071_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___boxed(lean_object* v_key_2072_, lean_object* v_as_2073_, lean_object* v_start_2074_, lean_object* v_stop_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_2072_, v_as_2073_, v_start_2074_, v_stop_2075_);
lean_dec(v_stop_2075_);
lean_dec(v_start_2074_);
lean_dec_ref(v_as_2073_);
lean_dec_ref(v_key_2072_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded(lean_object* v_query_2077_, lean_object* v_key_2078_){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_unsigned_to_nat(0u);
v___x_2080_ = lean_array_get_size(v_query_2077_);
v___x_2081_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_2078_, v_query_2077_, v___x_2079_, v___x_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded___boxed(lean_object* v_query_2082_, lean_object* v_key_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Std_Http_URI_Query_findAllEncoded(v_query_2082_, v_key_2083_);
lean_dec_ref(v_key_2083_);
lean_dec_ref(v_query_2082_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll(lean_object* v_query_2085_, lean_object* v_key_2086_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_2086_);
v___x_2088_ = l_Std_Http_URI_Query_findAllEncoded(v_query_2085_, v___x_2087_);
lean_dec_ref(v___x_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll___boxed(lean_object* v_query_2089_, lean_object* v_key_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Std_Http_URI_Query_findAll(v_query_2089_, v_key_2090_);
lean_dec_ref(v_key_2090_);
lean_dec_ref(v_query_2089_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert(lean_object* v_query_2092_, lean_object* v_key_2093_, lean_object* v_value_2094_){
_start:
{
lean_object* v_encodedKey_2095_; lean_object* v_encodedValue_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_encodedKey_2095_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_2093_);
v_encodedValue_2096_ = l_Std_Http_URI_EncodedQueryParam_encode(v_value_2094_);
v___x_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2097_, 0, v_encodedValue_2096_);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v_encodedKey_2095_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = lean_array_push(v_query_2092_, v___x_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert___boxed(lean_object* v_query_2100_, lean_object* v_key_2101_, lean_object* v_value_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Std_Http_URI_Query_insert(v_query_2100_, v_key_2101_, v_value_2102_);
lean_dec_ref(v_value_2102_);
lean_dec_ref(v_key_2101_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object* v_query_2104_, lean_object* v_key_2105_, lean_object* v_value_2106_){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v_key_2105_);
lean_ctor_set(v___x_2107_, 1, v_value_2106_);
v___x_2108_ = lean_array_push(v_query_2104_, v___x_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_ofList(lean_object* v_pairs_2112_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_array_mk(v_pairs_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(lean_object* v_key_2114_, lean_object* v_as_2115_, size_t v_i_2116_, size_t v_stop_2117_){
_start:
{
uint8_t v___x_2118_; 
v___x_2118_ = lean_usize_dec_eq(v_i_2116_, v_stop_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; lean_object* v_fst_2120_; uint8_t v___x_2121_; 
v___x_2119_ = lean_array_uget_borrowed(v_as_2115_, v_i_2116_);
v_fst_2120_ = lean_ctor_get(v___x_2119_, 0);
v___x_2121_ = lean_sarray_dec_eq(v_fst_2120_, v_key_2114_);
if (v___x_2121_ == 0)
{
size_t v___x_2122_; size_t v___x_2123_; 
v___x_2122_ = ((size_t)1ULL);
v___x_2123_ = lean_usize_add(v_i_2116_, v___x_2122_);
v_i_2116_ = v___x_2123_;
goto _start;
}
else
{
return v___x_2121_;
}
}
else
{
uint8_t v___x_2125_; 
v___x_2125_ = 0;
return v___x_2125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(lean_object* v_key_2126_, lean_object* v_as_2127_, lean_object* v_i_2128_, lean_object* v_stop_2129_){
_start:
{
size_t v_i_boxed_2130_; size_t v_stop_boxed_2131_; uint8_t v_res_2132_; lean_object* v_r_2133_; 
v_i_boxed_2130_ = lean_unbox_usize(v_i_2128_);
lean_dec(v_i_2128_);
v_stop_boxed_2131_ = lean_unbox_usize(v_stop_2129_);
lean_dec(v_stop_2129_);
v_res_2132_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_2126_, v_as_2127_, v_i_boxed_2130_, v_stop_boxed_2131_);
lean_dec_ref(v_as_2127_);
lean_dec_ref(v_key_2126_);
v_r_2133_ = lean_box(v_res_2132_);
return v_r_2133_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_containsEncoded(lean_object* v_query_2134_, lean_object* v_key_2135_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2136_ = lean_unsigned_to_nat(0u);
v___x_2137_ = lean_array_get_size(v_query_2134_);
v___x_2138_ = lean_nat_dec_lt(v___x_2136_, v___x_2137_);
if (v___x_2138_ == 0)
{
return v___x_2138_;
}
else
{
if (v___x_2138_ == 0)
{
return v___x_2138_;
}
else
{
size_t v___x_2139_; size_t v___x_2140_; uint8_t v___x_2141_; 
v___x_2139_ = ((size_t)0ULL);
v___x_2140_ = lean_usize_of_nat(v___x_2137_);
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_2135_, v_query_2134_, v___x_2139_, v___x_2140_);
return v___x_2141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_containsEncoded___boxed(lean_object* v_query_2142_, lean_object* v_key_2143_){
_start:
{
uint8_t v_res_2144_; lean_object* v_r_2145_; 
v_res_2144_ = l_Std_Http_URI_Query_containsEncoded(v_query_2142_, v_key_2143_);
lean_dec_ref(v_key_2143_);
lean_dec_ref(v_query_2142_);
v_r_2145_ = lean_box(v_res_2144_);
return v_r_2145_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_contains(lean_object* v_query_2146_, lean_object* v_key_2147_){
_start:
{
lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2148_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_2147_);
v___x_2149_ = l_Std_Http_URI_Query_containsEncoded(v_query_2146_, v___x_2148_);
lean_dec_ref(v___x_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_contains___boxed(lean_object* v_query_2150_, lean_object* v_key_2151_){
_start:
{
uint8_t v_res_2152_; lean_object* v_r_2153_; 
v_res_2152_ = l_Std_Http_URI_Query_contains(v_query_2150_, v_key_2151_);
lean_dec_ref(v_key_2151_);
lean_dec_ref(v_query_2150_);
v_r_2153_ = lean_box(v_res_2152_);
return v_r_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(lean_object* v_key_2154_, lean_object* v_as_2155_, size_t v_i_2156_, size_t v_stop_2157_, lean_object* v_b_2158_){
_start:
{
lean_object* v___y_2160_; uint8_t v___x_2164_; 
v___x_2164_ = lean_usize_dec_eq(v_i_2156_, v_stop_2157_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v_fst_2168_; uint8_t v___x_2169_; 
v___x_2165_ = lean_array_uget_borrowed(v_as_2155_, v_i_2156_);
v_fst_2168_ = lean_ctor_get(v___x_2165_, 0);
v___x_2169_ = lean_sarray_dec_eq(v_fst_2168_, v_key_2154_);
if (v___x_2169_ == 0)
{
goto v___jp_2166_;
}
else
{
if (v___x_2164_ == 0)
{
v___y_2160_ = v_b_2158_;
goto v___jp_2159_;
}
else
{
goto v___jp_2166_;
}
}
v___jp_2166_:
{
lean_object* v___x_2167_; 
lean_inc(v___x_2165_);
v___x_2167_ = lean_array_push(v_b_2158_, v___x_2165_);
v___y_2160_ = v___x_2167_;
goto v___jp_2159_;
}
}
else
{
return v_b_2158_;
}
v___jp_2159_:
{
size_t v___x_2161_; size_t v___x_2162_; 
v___x_2161_ = ((size_t)1ULL);
v___x_2162_ = lean_usize_add(v_i_2156_, v___x_2161_);
v_i_2156_ = v___x_2162_;
v_b_2158_ = v___y_2160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(lean_object* v_key_2170_, lean_object* v_as_2171_, lean_object* v_i_2172_, lean_object* v_stop_2173_, lean_object* v_b_2174_){
_start:
{
size_t v_i_boxed_2175_; size_t v_stop_boxed_2176_; lean_object* v_res_2177_; 
v_i_boxed_2175_ = lean_unbox_usize(v_i_2172_);
lean_dec(v_i_2172_);
v_stop_boxed_2176_ = lean_unbox_usize(v_stop_2173_);
lean_dec(v_stop_2173_);
v_res_2177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2170_, v_as_2171_, v_i_boxed_2175_, v_stop_boxed_2176_, v_b_2174_);
lean_dec_ref(v_as_2171_);
lean_dec_ref(v_key_2170_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded(lean_object* v_query_2178_, lean_object* v_key_2179_){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2180_ = lean_unsigned_to_nat(0u);
v___x_2181_ = lean_array_get_size(v_query_2178_);
v___x_2182_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_2183_ = lean_nat_dec_lt(v___x_2180_, v___x_2181_);
if (v___x_2183_ == 0)
{
return v___x_2182_;
}
else
{
uint8_t v___x_2184_; 
v___x_2184_ = lean_nat_dec_le(v___x_2181_, v___x_2181_);
if (v___x_2184_ == 0)
{
if (v___x_2183_ == 0)
{
return v___x_2182_;
}
else
{
size_t v___x_2185_; size_t v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = ((size_t)0ULL);
v___x_2186_ = lean_usize_of_nat(v___x_2181_);
v___x_2187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2179_, v_query_2178_, v___x_2185_, v___x_2186_, v___x_2182_);
return v___x_2187_;
}
}
else
{
size_t v___x_2188_; size_t v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = ((size_t)0ULL);
v___x_2189_ = lean_usize_of_nat(v___x_2181_);
v___x_2190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_2179_, v_query_2178_, v___x_2188_, v___x_2189_, v___x_2182_);
return v___x_2190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded___boxed(lean_object* v_query_2191_, lean_object* v_key_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Std_Http_URI_Query_eraseEncoded(v_query_2191_, v_key_2192_);
lean_dec_ref(v_key_2192_);
lean_dec_ref(v_query_2191_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase(lean_object* v_query_2194_, lean_object* v_key_2195_){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_2195_);
v___x_2197_ = l_Std_Http_URI_Query_eraseEncoded(v_query_2194_, v___x_2196_);
lean_dec_ref(v___x_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase___boxed(lean_object* v_query_2198_, lean_object* v_key_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Std_Http_URI_Query_erase(v_query_2198_, v_key_2199_);
lean_dec_ref(v_key_2199_);
lean_dec_ref(v_query_2198_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get(lean_object* v_query_2203_, lean_object* v_key_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Std_Http_URI_Query_find_x3f(v_query_2203_, v_key_2204_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v___x_2206_; 
v___x_2206_ = lean_box(0);
return v___x_2206_;
}
else
{
lean_object* v_val_2207_; 
v_val_2207_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_val_2207_);
lean_dec_ref_known(v___x_2205_, 1);
if (lean_obj_tag(v_val_2207_) == 0)
{
lean_object* v___x_2208_; 
v___x_2208_ = ((lean_object*)(l_Std_Http_URI_Query_get___closed__0));
return v___x_2208_;
}
else
{
lean_object* v_val_2209_; lean_object* v___x_2210_; 
v_val_2209_ = lean_ctor_get(v_val_2207_, 0);
lean_inc(v_val_2209_);
lean_dec_ref_known(v_val_2207_, 1);
v___x_2210_ = l_Std_Http_URI_EncodedQueryParam_decode(v_val_2209_);
lean_dec(v_val_2209_);
return v___x_2210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get___boxed(lean_object* v_query_2211_, lean_object* v_key_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Std_Http_URI_Query_get(v_query_2211_, v_key_2212_);
lean_dec_ref(v_key_2212_);
lean_dec_ref(v_query_2211_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD(lean_object* v_query_2214_, lean_object* v_key_2215_, lean_object* v_default_2216_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Std_Http_URI_Query_get(v_query_2214_, v_key_2215_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_inc_ref(v_default_2216_);
return v_default_2216_;
}
else
{
lean_object* v_val_2218_; 
v_val_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_val_2218_);
lean_dec_ref_known(v___x_2217_, 1);
return v_val_2218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD___boxed(lean_object* v_query_2219_, lean_object* v_key_2220_, lean_object* v_default_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Std_Http_URI_Query_getD(v_query_2219_, v_key_2220_, v_default_2221_);
lean_dec_ref(v_default_2221_);
lean_dec_ref(v_key_2220_);
lean_dec_ref(v_query_2219_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set(lean_object* v_query_2223_, lean_object* v_key_2224_, lean_object* v_value_2225_){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = l_Std_Http_URI_Query_erase(v_query_2223_, v_key_2224_);
v___x_2227_ = l_Std_Http_URI_Query_insert(v___x_2226_, v_key_2224_, v_value_2225_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set___boxed(lean_object* v_query_2228_, lean_object* v_key_2229_, lean_object* v_value_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Std_Http_URI_Query_set(v_query_2228_, v_key_2229_, v_value_2230_);
lean_dec_ref(v_value_2230_);
lean_dec_ref(v_key_2229_);
lean_dec_ref(v_query_2228_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(size_t v_sz_2232_, size_t v_i_2233_, lean_object* v_bs_2234_){
_start:
{
uint8_t v___x_2235_; 
v___x_2235_ = lean_usize_dec_lt(v_i_2233_, v_sz_2232_);
if (v___x_2235_ == 0)
{
return v_bs_2234_;
}
else
{
lean_object* v_v_2236_; lean_object* v_fst_2237_; lean_object* v_snd_2238_; lean_object* v___x_2239_; lean_object* v_bs_x27_2240_; lean_object* v___x_2241_; size_t v___x_2242_; size_t v___x_2243_; lean_object* v___x_2244_; 
v_v_2236_ = lean_array_uget_borrowed(v_bs_2234_, v_i_2233_);
v_fst_2237_ = lean_ctor_get(v_v_2236_, 0);
lean_inc(v_fst_2237_);
v_snd_2238_ = lean_ctor_get(v_v_2236_, 1);
lean_inc(v_snd_2238_);
v___x_2239_ = lean_unsigned_to_nat(0u);
v_bs_x27_2240_ = lean_array_uset(v_bs_2234_, v_i_2233_, v___x_2239_);
v___x_2241_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2237_, v_snd_2238_);
v___x_2242_ = ((size_t)1ULL);
v___x_2243_ = lean_usize_add(v_i_2233_, v___x_2242_);
v___x_2244_ = lean_array_uset(v_bs_x27_2240_, v_i_2233_, v___x_2241_);
v_i_2233_ = v___x_2243_;
v_bs_2234_ = v___x_2244_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0___boxed(lean_object* v_sz_2246_, lean_object* v_i_2247_, lean_object* v_bs_2248_){
_start:
{
size_t v_sz_boxed_2249_; size_t v_i_boxed_2250_; lean_object* v_res_2251_; 
v_sz_boxed_2249_ = lean_unbox_usize(v_sz_2246_);
lean_dec(v_sz_2246_);
v_i_boxed_2250_ = lean_unbox_usize(v_i_2247_);
lean_dec(v_i_2247_);
v_res_2251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_boxed_2249_, v_i_boxed_2250_, v_bs_2248_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toRawString(lean_object* v_query_2253_){
_start:
{
size_t v_sz_2254_; size_t v___x_2255_; lean_object* v_params_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v_sz_2254_ = lean_array_size(v_query_2253_);
v___x_2255_ = ((size_t)0ULL);
v_params_2256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_2254_, v___x_2255_, v_query_2253_);
v___x_2257_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2258_ = lean_array_to_list(v_params_2256_);
v___x_2259_ = l_String_intercalate(v___x_2257_, v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0(lean_object* v_x_2261_){
_start:
{
lean_object* v_fst_2262_; lean_object* v_snd_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v_fst_2262_ = lean_ctor_get(v_x_2261_, 0);
v_snd_2263_ = lean_ctor_get(v_x_2261_, 1);
v___x_2264_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
v___x_2265_ = l_Std_Http_URI_Query_insert(v___x_2264_, v_fst_2262_, v_snd_2263_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0___boxed(lean_object* v_x_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_Std_Http_URI_Query_instSingletonProdString___lam__0(v_x_2266_);
lean_dec_ref(v_x_2266_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0(lean_object* v_x_2270_, lean_object* v_q_2271_){
_start:
{
lean_object* v_fst_2272_; lean_object* v_snd_2273_; lean_object* v___x_2274_; 
v_fst_2272_ = lean_ctor_get(v_x_2270_, 0);
v_snd_2273_ = lean_ctor_get(v_x_2270_, 1);
v___x_2274_ = l_Std_Http_URI_Query_insert(v_q_2271_, v_fst_2272_, v_snd_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0___boxed(lean_object* v_x_2275_, lean_object* v_q_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Std_Http_URI_Query_instInsertProdString___lam__0(v_x_2275_, v_q_2276_);
lean_dec_ref(v_x_2275_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__0(lean_object* v_x_2280_){
_start:
{
lean_object* v_fst_2281_; lean_object* v_snd_2282_; lean_object* v___x_2283_; 
v_fst_2281_ = lean_ctor_get(v_x_2280_, 0);
lean_inc(v_fst_2281_);
v_snd_2282_ = lean_ctor_get(v_x_2280_, 1);
lean_inc(v_snd_2282_);
lean_dec_ref(v_x_2280_);
v___x_2283_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2281_, v_snd_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__1(lean_object* v___f_2285_, lean_object* v_q_2286_){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v___x_2287_ = lean_array_get_size(v_q_2286_);
v___x_2288_ = lean_unsigned_to_nat(0u);
v___x_2289_ = lean_nat_dec_eq(v___x_2287_, v___x_2288_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v_encodedParams_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2290_ = lean_array_to_list(v_q_2286_);
v___x_2291_ = lean_box(0);
v_encodedParams_2292_ = l_List_mapTR_loop___redArg(v___f_2285_, v___x_2290_, v___x_2291_);
v___x_2293_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2294_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2295_ = l_String_intercalate(v___x_2294_, v_encodedParams_2292_);
v___x_2296_ = lean_string_append(v___x_2293_, v___x_2295_);
lean_dec_ref(v___x_2295_);
return v___x_2296_;
}
else
{
lean_object* v___x_2297_; 
lean_dec_ref(v_q_2286_);
lean_dec_ref(v___f_2285_);
v___x_2297_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2297_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
if (lean_obj_tag(v_a_2302_) == 0)
{
lean_object* v___x_2304_; 
v___x_2304_ = l_List_reverse___redArg(v_a_2303_);
return v___x_2304_;
}
else
{
lean_object* v_head_2305_; lean_object* v_tail_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2317_; 
v_head_2305_ = lean_ctor_get(v_a_2302_, 0);
v_tail_2306_ = lean_ctor_get(v_a_2302_, 1);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_a_2302_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2308_ = v_a_2302_;
v_isShared_2309_ = v_isSharedCheck_2317_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_tail_2306_);
lean_inc(v_head_2305_);
lean_dec(v_a_2302_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2317_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v_fst_2310_; lean_object* v_snd_2311_; lean_object* v___x_2312_; lean_object* v___x_2314_; 
v_fst_2310_ = lean_ctor_get(v_head_2305_, 0);
lean_inc(v_fst_2310_);
v_snd_2311_ = lean_ctor_get(v_head_2305_, 1);
lean_inc(v_snd_2311_);
lean_dec(v_head_2305_);
v___x_2312_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2310_, v_snd_2311_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 1, v_a_2303_);
lean_ctor_set(v___x_2308_, 0, v___x_2312_);
v___x_2314_ = v___x_2308_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_a_2303_);
v___x_2314_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
v_a_2302_ = v_tail_2306_;
v_a_2303_ = v___x_2314_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatOption(lean_object* v_x_2318_){
_start:
{
if (lean_obj_tag(v_x_2318_) == 0)
{
lean_object* v___x_2319_; 
v___x_2319_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2319_;
}
else
{
lean_object* v_val_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v_val_2320_ = lean_ctor_get(v_x_2318_, 0);
lean_inc(v_val_2320_);
lean_dec_ref_known(v_x_2318_, 1);
v___x_2321_ = lean_array_get_size(v_val_2320_);
v___x_2322_ = lean_unsigned_to_nat(0u);
v___x_2323_ = lean_nat_dec_eq(v___x_2321_, v___x_2322_);
if (v___x_2323_ == 0)
{
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v_encodedParams_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2324_ = lean_array_to_list(v_val_2320_);
v___x_2325_ = lean_box(0);
v_encodedParams_2326_ = l_List_mapTR_loop___at___00Std_Http_URI_Query_formatOption_spec__0(v___x_2324_, v___x_2325_);
v___x_2327_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2328_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2329_ = l_String_intercalate(v___x_2328_, v_encodedParams_2326_);
v___x_2330_ = lean_string_append(v___x_2327_, v___x_2329_);
lean_dec_ref(v___x_2329_);
return v___x_2330_;
}
else
{
lean_object* v___x_2331_; 
lean_dec(v_val_2320_);
v___x_2331_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2331_;
}
}
else
{
lean_object* v___x_2332_; 
lean_dec(v_val_2320_);
v___x_2332_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
return v___x_2332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(lean_object* v_x_2333_, lean_object* v_x_2334_){
_start:
{
if (lean_obj_tag(v_x_2333_) == 0)
{
lean_object* v___x_2335_; 
v___x_2335_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2335_;
}
else
{
lean_object* v_val_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v_val_2336_ = lean_ctor_get(v_x_2333_, 0);
lean_inc(v_val_2336_);
lean_dec_ref_known(v_x_2333_, 1);
v___x_2337_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2338_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_val_2336_);
v___x_2339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2337_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
v___x_2340_ = l_Repr_addAppParen(v___x_2339_, v_x_2334_);
return v___x_2340_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(lean_object* v_x_2341_, lean_object* v_x_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_x_2341_, v_x_2342_);
lean_dec(v_x_2342_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object* v_x_2344_, lean_object* v_x_2345_){
_start:
{
if (lean_obj_tag(v_x_2344_) == 0)
{
lean_object* v___x_2346_; 
v___x_2346_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2346_;
}
else
{
lean_object* v_val_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v_val_2347_ = lean_ctor_get(v_x_2344_, 0);
lean_inc(v_val_2347_);
lean_dec_ref_known(v_x_2344_, 1);
v___x_2348_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2349_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_val_2347_);
v___x_2350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = l_Repr_addAppParen(v___x_2350_, v_x_2345_);
return v___x_2351_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1___boxed(lean_object* v_x_2352_, lean_object* v_x_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_x_2352_, v_x_2353_);
lean_dec(v_x_2353_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(lean_object* v_x_2355_, lean_object* v_x_2356_){
_start:
{
if (lean_obj_tag(v_x_2355_) == 0)
{
lean_object* v___x_2357_; 
v___x_2357_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2357_;
}
else
{
lean_object* v_val_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2369_; 
v_val_2358_ = lean_ctor_get(v_x_2355_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v_x_2355_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2360_ = v_x_2355_;
v_isShared_2361_ = v_isSharedCheck_2369_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_val_2358_);
lean_dec(v_x_2355_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2369_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2362_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2363_ = l_String_quote(v_val_2358_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 3);
lean_ctor_set(v___x_2360_, 0, v___x_2363_);
v___x_2365_ = v___x_2360_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2362_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = l_Repr_addAppParen(v___x_2366_, v_x_2356_);
return v___x_2367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2___boxed(lean_object* v_x_2370_, lean_object* v_x_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_x_2370_, v_x_2371_);
lean_dec(v_x_2371_);
return v_res_2372_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = lean_unsigned_to_nat(10u);
v___x_2383_ = lean_nat_to_int(v___x_2382_);
return v___x_2383_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_unsigned_to_nat(13u);
v___x_2388_ = lean_nat_to_int(v___x_2387_);
return v___x_2388_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_unsigned_to_nat(9u);
v___x_2396_ = lean_nat_to_int(v___x_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___redArg(lean_object* v_x_2400_){
_start:
{
lean_object* v_scheme_2401_; lean_object* v_authority_2402_; lean_object* v_path_2403_; lean_object* v_query_2404_; lean_object* v_fragment_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v_scheme_2401_ = lean_ctor_get(v_x_2400_, 0);
lean_inc_ref(v_scheme_2401_);
v_authority_2402_ = lean_ctor_get(v_x_2400_, 1);
lean_inc(v_authority_2402_);
v_path_2403_ = lean_ctor_get(v_x_2400_, 2);
lean_inc_ref(v_path_2403_);
v_query_2404_ = lean_ctor_get(v_x_2400_, 3);
lean_inc(v_query_2404_);
v_fragment_2405_ = lean_ctor_get(v_x_2400_, 4);
lean_inc(v_fragment_2405_);
lean_dec_ref(v_x_2400_);
v___x_2406_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2407_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2408_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2409_ = l_String_quote(v_scheme_2401_);
v___x_2410_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
v___x_2411_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2408_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = 0;
v___x_2413_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set_uint8(v___x_2413_, sizeof(void*)*1, v___x_2412_);
v___x_2414_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2407_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2416_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2414_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
v___x_2417_ = lean_box(1);
v___x_2418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__6));
v___x_2420_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2418_);
lean_ctor_set(v___x_2420_, 1, v___x_2419_);
v___x_2421_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
lean_ctor_set(v___x_2421_, 1, v___x_2406_);
v___x_2422_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_2423_ = lean_unsigned_to_nat(0u);
v___x_2424_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_2402_, v___x_2423_);
v___x_2425_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2422_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___x_2426_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
lean_ctor_set_uint8(v___x_2426_, sizeof(void*)*1, v___x_2412_);
v___x_2427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2421_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
lean_ctor_set(v___x_2428_, 1, v___x_2415_);
v___x_2429_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
lean_ctor_set(v___x_2429_, 1, v___x_2417_);
v___x_2430_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_2431_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
lean_ctor_set(v___x_2432_, 1, v___x_2406_);
v___x_2433_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2434_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_2403_);
v___x_2435_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set_uint8(v___x_2436_, sizeof(void*)*1, v___x_2412_);
v___x_2437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2432_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
lean_ctor_set(v___x_2438_, 1, v___x_2415_);
v___x_2439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
lean_ctor_set(v___x_2439_, 1, v___x_2417_);
v___x_2440_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_2441_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
lean_ctor_set(v___x_2442_, 1, v___x_2406_);
v___x_2443_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_2444_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_2404_, v___x_2423_);
v___x_2445_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2443_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
v___x_2446_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
lean_ctor_set_uint8(v___x_2446_, sizeof(void*)*1, v___x_2412_);
v___x_2447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2442_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
v___x_2448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v___x_2415_);
v___x_2449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
lean_ctor_set(v___x_2449_, 1, v___x_2417_);
v___x_2450_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_2451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
lean_ctor_set(v___x_2452_, 1, v___x_2406_);
v___x_2453_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_2454_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_2405_, v___x_2423_);
v___x_2455_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2453_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
v___x_2456_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
lean_ctor_set_uint8(v___x_2456_, sizeof(void*)*1, v___x_2412_);
v___x_2457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2452_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2459_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2460_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
lean_ctor_set(v___x_2460_, 1, v___x_2457_);
v___x_2461_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2458_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set_uint8(v___x_2464_, sizeof(void*)*1, v___x_2412_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr(lean_object* v_x_2465_, lean_object* v_prec_2466_){
_start:
{
lean_object* v___x_2467_; 
v___x_2467_ = l_Std_Http_instReprURI_repr___redArg(v_x_2465_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___boxed(lean_object* v_x_2468_, lean_object* v_prec_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Std_Http_instReprURI_repr(v_x_2468_, v_prec_2469_);
lean_dec(v_prec_2469_);
return v_res_2470_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object* v_x_2479_, lean_object* v_x_2480_){
_start:
{
if (lean_obj_tag(v_x_2479_) == 0)
{
if (lean_obj_tag(v_x_2480_) == 0)
{
uint8_t v___x_2481_; 
v___x_2481_ = 1;
return v___x_2481_;
}
else
{
uint8_t v___x_2482_; 
v___x_2482_ = 0;
return v___x_2482_;
}
}
else
{
if (lean_obj_tag(v_x_2480_) == 0)
{
uint8_t v___x_2483_; 
v___x_2483_ = 0;
return v___x_2483_;
}
else
{
lean_object* v_val_2484_; lean_object* v_val_2485_; uint8_t v___x_2486_; 
v_val_2484_ = lean_ctor_get(v_x_2479_, 0);
v_val_2485_ = lean_ctor_get(v_x_2480_, 0);
v___x_2486_ = l_Std_Http_URI_instBEqAuthority_beq(v_val_2484_, v_val_2485_);
return v___x_2486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object* v_x_2487_, lean_object* v_x_2488_){
_start:
{
uint8_t v_res_2489_; lean_object* v_r_2490_; 
v_res_2489_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_x_2487_, v_x_2488_);
lean_dec(v_x_2488_);
lean_dec(v_x_2487_);
v_r_2490_ = lean_box(v_res_2489_);
return v_r_2490_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object* v_x_2491_, lean_object* v_x_2492_){
_start:
{
if (lean_obj_tag(v_x_2491_) == 0)
{
if (lean_obj_tag(v_x_2492_) == 0)
{
uint8_t v___x_2493_; 
v___x_2493_ = 1;
return v___x_2493_;
}
else
{
uint8_t v___x_2494_; 
v___x_2494_ = 0;
return v___x_2494_;
}
}
else
{
if (lean_obj_tag(v_x_2492_) == 0)
{
uint8_t v___x_2495_; 
v___x_2495_ = 0;
return v___x_2495_;
}
else
{
lean_object* v_val_2496_; lean_object* v_val_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; 
v_val_2496_ = lean_ctor_get(v_x_2491_, 0);
v_val_2497_ = lean_ctor_get(v_x_2492_, 0);
v___x_2498_ = lean_array_get_size(v_val_2496_);
v___x_2499_ = lean_array_get_size(v_val_2497_);
v___x_2500_ = lean_nat_dec_eq(v___x_2498_, v___x_2499_);
if (v___x_2500_ == 0)
{
return v___x_2500_;
}
else
{
uint8_t v___x_2501_; 
v___x_2501_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_val_2496_, v_val_2497_, v___x_2498_);
return v___x_2501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object* v_x_2502_, lean_object* v_x_2503_){
_start:
{
uint8_t v_res_2504_; lean_object* v_r_2505_; 
v_res_2504_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_x_2502_, v_x_2503_);
lean_dec(v_x_2503_);
lean_dec(v_x_2502_);
v_r_2505_ = lean_box(v_res_2504_);
return v_r_2505_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2(lean_object* v_x_2506_, lean_object* v_x_2507_){
_start:
{
if (lean_obj_tag(v_x_2506_) == 0)
{
if (lean_obj_tag(v_x_2507_) == 0)
{
uint8_t v___x_2508_; 
v___x_2508_ = 1;
return v___x_2508_;
}
else
{
uint8_t v___x_2509_; 
v___x_2509_ = 0;
return v___x_2509_;
}
}
else
{
if (lean_obj_tag(v_x_2507_) == 0)
{
uint8_t v___x_2510_; 
v___x_2510_ = 0;
return v___x_2510_;
}
else
{
lean_object* v_val_2511_; lean_object* v_val_2512_; uint8_t v___x_2513_; 
v_val_2511_ = lean_ctor_get(v_x_2506_, 0);
v_val_2512_ = lean_ctor_get(v_x_2507_, 0);
v___x_2513_ = lean_string_dec_eq(v_val_2511_, v_val_2512_);
return v___x_2513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2___boxed(lean_object* v_x_2514_, lean_object* v_x_2515_){
_start:
{
uint8_t v_res_2516_; lean_object* v_r_2517_; 
v_res_2516_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_x_2514_, v_x_2515_);
lean_dec(v_x_2515_);
lean_dec(v_x_2514_);
v_r_2517_ = lean_box(v_res_2516_);
return v_r_2517_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object* v_x_2518_, lean_object* v_x_2519_){
_start:
{
lean_object* v_scheme_2520_; lean_object* v_authority_2521_; lean_object* v_path_2522_; lean_object* v_query_2523_; lean_object* v_fragment_2524_; lean_object* v_scheme_2525_; lean_object* v_authority_2526_; lean_object* v_path_2527_; lean_object* v_query_2528_; lean_object* v_fragment_2529_; uint8_t v___x_2530_; 
v_scheme_2520_ = lean_ctor_get(v_x_2518_, 0);
v_authority_2521_ = lean_ctor_get(v_x_2518_, 1);
v_path_2522_ = lean_ctor_get(v_x_2518_, 2);
v_query_2523_ = lean_ctor_get(v_x_2518_, 3);
v_fragment_2524_ = lean_ctor_get(v_x_2518_, 4);
v_scheme_2525_ = lean_ctor_get(v_x_2519_, 0);
v_authority_2526_ = lean_ctor_get(v_x_2519_, 1);
v_path_2527_ = lean_ctor_get(v_x_2519_, 2);
v_query_2528_ = lean_ctor_get(v_x_2519_, 3);
v_fragment_2529_ = lean_ctor_get(v_x_2519_, 4);
v___x_2530_ = lean_string_dec_eq(v_scheme_2520_, v_scheme_2525_);
if (v___x_2530_ == 0)
{
return v___x_2530_;
}
else
{
uint8_t v___x_2531_; 
v___x_2531_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_2521_, v_authority_2526_);
if (v___x_2531_ == 0)
{
return v___x_2531_;
}
else
{
uint8_t v___x_2532_; 
v___x_2532_ = l_Std_Http_URI_instBEqPath_beq(v_path_2522_, v_path_2527_);
if (v___x_2532_ == 0)
{
return v___x_2532_;
}
else
{
uint8_t v___x_2533_; 
v___x_2533_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_2523_, v_query_2528_);
if (v___x_2533_ == 0)
{
return v___x_2533_;
}
else
{
uint8_t v___x_2534_; 
v___x_2534_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_2524_, v_fragment_2529_);
return v___x_2534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object* v_x_2535_, lean_object* v_x_2536_){
_start:
{
uint8_t v_res_2537_; lean_object* v_r_2538_; 
v_res_2537_ = l_Std_Http_instBEqURI_beq(v_x_2535_, v_x_2536_);
lean_dec_ref(v_x_2536_);
lean_dec_ref(v_x_2535_);
v_r_2538_ = lean_box(v_res_2537_);
return v_r_2538_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__1(lean_object* v___f_2543_, lean_object* v_uri_2544_){
_start:
{
lean_object* v_scheme_2545_; lean_object* v_authority_2546_; lean_object* v_path_2547_; lean_object* v_query_2548_; lean_object* v_fragment_2549_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2572_; 
v_scheme_2545_ = lean_ctor_get(v_uri_2544_, 0);
lean_inc_ref(v_scheme_2545_);
v_authority_2546_ = lean_ctor_get(v_uri_2544_, 1);
lean_inc(v_authority_2546_);
v_path_2547_ = lean_ctor_get(v_uri_2544_, 2);
lean_inc_ref(v_path_2547_);
v_query_2548_ = lean_ctor_get(v_uri_2544_, 3);
lean_inc(v_query_2548_);
v_fragment_2549_ = lean_ctor_get(v_uri_2544_, 4);
lean_inc(v_fragment_2549_);
lean_dec_ref(v_uri_2544_);
if (lean_obj_tag(v_authority_2546_) == 0)
{
lean_object* v___x_2583_; 
v___x_2583_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2572_ = v___x_2583_;
goto v___jp_2571_;
}
else
{
lean_object* v_val_2584_; lean_object* v_userInfo_2585_; lean_object* v_host_2586_; lean_object* v_port_2587_; lean_object* v___x_2588_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2607_; 
v_val_2584_ = lean_ctor_get(v_authority_2546_, 0);
lean_inc(v_val_2584_);
lean_dec_ref_known(v_authority_2546_, 1);
v_userInfo_2585_ = lean_ctor_get(v_val_2584_, 0);
lean_inc(v_userInfo_2585_);
v_host_2586_ = lean_ctor_get(v_val_2584_, 1);
lean_inc_ref(v_host_2586_);
v_port_2587_ = lean_ctor_get(v_val_2584_, 2);
lean_inc(v_port_2587_);
lean_dec(v_val_2584_);
v___x_2588_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_2585_) == 0)
{
lean_object* v___x_2617_; 
v___x_2617_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2607_ = v___x_2617_;
goto v___jp_2606_;
}
else
{
lean_object* v_val_2618_; lean_object* v_password_2619_; 
v_val_2618_ = lean_ctor_get(v_userInfo_2585_, 0);
lean_inc(v_val_2618_);
lean_dec_ref_known(v_userInfo_2585_, 1);
v_password_2619_ = lean_ctor_get(v_val_2618_, 1);
if (lean_obj_tag(v_password_2619_) == 0)
{
lean_object* v_username_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v_username_2620_ = lean_ctor_get(v_val_2618_, 0);
lean_inc_ref(v_username_2620_);
lean_dec(v_val_2618_);
v___x_2621_ = lean_string_from_utf8_unchecked(v_username_2620_);
v___x_2622_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2623_ = lean_string_append(v___x_2621_, v___x_2622_);
v___y_2607_ = v___x_2623_;
goto v___jp_2606_;
}
else
{
lean_object* v_username_2624_; lean_object* v_val_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_inc_ref(v_password_2619_);
v_username_2624_ = lean_ctor_get(v_val_2618_, 0);
lean_inc_ref(v_username_2624_);
lean_dec(v_val_2618_);
v_val_2625_ = lean_ctor_get(v_password_2619_, 0);
lean_inc(v_val_2625_);
lean_dec_ref_known(v_password_2619_, 1);
v___x_2626_ = lean_string_from_utf8_unchecked(v_username_2624_);
v___x_2627_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2628_ = lean_string_append(v___x_2626_, v___x_2627_);
v___x_2629_ = lean_string_from_utf8_unchecked(v_val_2625_);
v___x_2630_ = lean_string_append(v___x_2628_, v___x_2629_);
lean_dec_ref(v___x_2629_);
v___x_2631_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2632_ = lean_string_append(v___x_2630_, v___x_2631_);
v___y_2607_ = v___x_2632_;
goto v___jp_2606_;
}
}
v___jp_2589_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = lean_string_append(v___y_2590_, v___y_2591_);
lean_dec_ref(v___y_2591_);
v___x_2594_ = lean_string_append(v___x_2593_, v___y_2592_);
lean_dec_ref(v___y_2592_);
v___x_2595_ = lean_string_append(v___x_2588_, v___x_2594_);
lean_dec_ref(v___x_2594_);
v___y_2572_ = v___x_2595_;
goto v___jp_2571_;
}
v___jp_2596_:
{
switch(lean_obj_tag(v_port_2587_))
{
case 0:
{
lean_object* v___x_2599_; 
v___x_2599_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2590_ = v___y_2597_;
v___y_2591_ = v___y_2598_;
v___y_2592_ = v___x_2599_;
goto v___jp_2589_;
}
case 1:
{
lean_object* v___x_2600_; 
v___x_2600_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_2590_ = v___y_2597_;
v___y_2591_ = v___y_2598_;
v___y_2592_ = v___x_2600_;
goto v___jp_2589_;
}
default: 
{
uint16_t v_port_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v_port_2601_ = lean_ctor_get_uint16(v_port_2587_, 0);
lean_dec_ref_known(v_port_2587_, 0);
v___x_2602_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2603_ = lean_uint16_to_nat(v_port_2601_);
v___x_2604_ = l_Nat_reprFast(v___x_2603_);
v___x_2605_ = lean_string_append(v___x_2602_, v___x_2604_);
lean_dec_ref(v___x_2604_);
v___y_2590_ = v___y_2597_;
v___y_2591_ = v___y_2598_;
v___y_2592_ = v___x_2605_;
goto v___jp_2589_;
}
}
}
v___jp_2606_:
{
switch(lean_obj_tag(v_host_2586_))
{
case 0:
{
lean_object* v_name_2608_; 
v_name_2608_ = lean_ctor_get(v_host_2586_, 0);
lean_inc_ref(v_name_2608_);
lean_dec_ref_known(v_host_2586_, 1);
v___y_2597_ = v___y_2607_;
v___y_2598_ = v_name_2608_;
goto v___jp_2596_;
}
case 1:
{
lean_object* v_ipv4_2609_; lean_object* v___x_2610_; 
v_ipv4_2609_ = lean_ctor_get(v_host_2586_, 0);
lean_inc_ref(v_ipv4_2609_);
lean_dec_ref_known(v_host_2586_, 1);
v___x_2610_ = lean_uv_ntop_v4(v_ipv4_2609_);
lean_dec_ref(v_ipv4_2609_);
v___y_2597_ = v___y_2607_;
v___y_2598_ = v___x_2610_;
goto v___jp_2596_;
}
default: 
{
lean_object* v_ipv6_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v_ipv6_2611_ = lean_ctor_get(v_host_2586_, 0);
lean_inc_ref(v_ipv6_2611_);
lean_dec_ref_known(v_host_2586_, 1);
v___x_2612_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_2613_ = lean_uv_ntop_v6(v_ipv6_2611_);
lean_dec_ref(v_ipv6_2611_);
v___x_2614_ = lean_string_append(v___x_2612_, v___x_2613_);
lean_dec_ref(v___x_2613_);
v___x_2615_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_2616_ = lean_string_append(v___x_2614_, v___x_2615_);
v___y_2597_ = v___y_2607_;
v___y_2598_ = v___x_2616_;
goto v___jp_2596_;
}
}
}
}
v___jp_2550_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2555_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2556_ = lean_string_append(v_scheme_2545_, v___x_2555_);
v___x_2557_ = lean_string_append(v___x_2556_, v___y_2552_);
lean_dec_ref(v___y_2552_);
v___x_2558_ = lean_string_append(v___x_2557_, v___y_2551_);
lean_dec_ref(v___y_2551_);
v___x_2559_ = lean_string_append(v___x_2558_, v___y_2553_);
lean_dec_ref(v___y_2553_);
v___x_2560_ = lean_string_append(v___x_2559_, v___y_2554_);
lean_dec_ref(v___y_2554_);
return v___x_2560_;
}
v___jp_2561_:
{
lean_object* v_queryPart_2564_; 
v_queryPart_2564_ = l_Std_Http_URI_Query_formatOption(v_query_2548_);
if (lean_obj_tag(v_fragment_2549_) == 0)
{
lean_object* v___x_2565_; 
v___x_2565_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2551_ = v___y_2563_;
v___y_2552_ = v___y_2562_;
v___y_2553_ = v_queryPart_2564_;
v___y_2554_ = v___x_2565_;
goto v___jp_2550_;
}
else
{
lean_object* v_val_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v_val_2566_ = lean_ctor_get(v_fragment_2549_, 0);
lean_inc(v_val_2566_);
lean_dec_ref_known(v_fragment_2549_, 1);
v___x_2567_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_2568_ = l_Std_Http_URI_EncodedFragment_encode(v_val_2566_);
lean_dec(v_val_2566_);
v___x_2569_ = lean_string_from_utf8_unchecked(v___x_2568_);
v___x_2570_ = lean_string_append(v___x_2567_, v___x_2569_);
lean_dec_ref(v___x_2569_);
v___y_2551_ = v___y_2563_;
v___y_2552_ = v___y_2562_;
v___y_2553_ = v_queryPart_2564_;
v___y_2554_ = v___x_2570_;
goto v___jp_2550_;
}
}
v___jp_2571_:
{
lean_object* v_segments_2573_; uint8_t v_absolute_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; size_t v_sz_2577_; size_t v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v_result_2581_; 
v_segments_2573_ = lean_ctor_get(v_path_2547_, 0);
lean_inc_ref(v_segments_2573_);
v_absolute_2574_ = lean_ctor_get_uint8(v_path_2547_, sizeof(void*)*1);
lean_dec_ref(v_path_2547_);
v___x_2575_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_2576_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_2577_ = lean_array_size(v_segments_2573_);
v___x_2578_ = ((size_t)0ULL);
v___x_2579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2576_, v___f_2543_, v_sz_2577_, v___x_2578_, v_segments_2573_);
v___x_2580_ = lean_array_to_list(v___x_2579_);
v_result_2581_ = l_String_intercalate(v___x_2575_, v___x_2580_);
if (v_absolute_2574_ == 0)
{
v___y_2562_ = v___y_2572_;
v___y_2563_ = v_result_2581_;
goto v___jp_2561_;
}
else
{
lean_object* v___x_2582_; 
v___x_2582_ = lean_string_append(v___x_2575_, v_result_2581_);
lean_dec_ref(v_result_2581_);
v___y_2562_ = v___y_2572_;
v___y_2563_ = v___x_2582_;
goto v___jp_2561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x3f(lean_object* v_b_2645_, lean_object* v_scheme_2646_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Std_Http_URI_Scheme_ofString_x3f(v_scheme_2646_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v___x_2648_; 
lean_dec_ref(v_b_2645_);
v___x_2648_ = lean_box(0);
return v___x_2648_;
}
else
{
lean_object* v_userInfo_2649_; lean_object* v_host_2650_; lean_object* v_port_2651_; lean_object* v_pathSegments_2652_; lean_object* v_query_2653_; lean_object* v_fragment_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2669_; 
v_userInfo_2649_ = lean_ctor_get(v_b_2645_, 1);
v_host_2650_ = lean_ctor_get(v_b_2645_, 2);
v_port_2651_ = lean_ctor_get(v_b_2645_, 3);
v_pathSegments_2652_ = lean_ctor_get(v_b_2645_, 4);
v_query_2653_ = lean_ctor_get(v_b_2645_, 5);
v_fragment_2654_ = lean_ctor_get(v_b_2645_, 6);
v_isSharedCheck_2669_ = !lean_is_exclusive(v_b_2645_);
if (v_isSharedCheck_2669_ == 0)
{
lean_object* v_unused_2670_; 
v_unused_2670_ = lean_ctor_get(v_b_2645_, 0);
lean_dec(v_unused_2670_);
v___x_2656_ = v_b_2645_;
v_isShared_2657_ = v_isSharedCheck_2669_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_fragment_2654_);
lean_inc(v_query_2653_);
lean_inc(v_pathSegments_2652_);
lean_inc(v_port_2651_);
lean_inc(v_host_2650_);
lean_inc(v_userInfo_2649_);
lean_dec(v_b_2645_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2669_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
lean_inc_ref(v___x_2647_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___x_2647_);
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2647_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_userInfo_2649_);
lean_ctor_set(v_reuseFailAlloc_2668_, 2, v_host_2650_);
lean_ctor_set(v_reuseFailAlloc_2668_, 3, v_port_2651_);
lean_ctor_set(v_reuseFailAlloc_2668_, 4, v_pathSegments_2652_);
lean_ctor_set(v_reuseFailAlloc_2668_, 5, v_query_2653_);
lean_ctor_set(v_reuseFailAlloc_2668_, 6, v_fragment_2654_);
v___x_2659_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; 
v_unused_2667_ = lean_ctor_get(v___x_2647_, 0);
lean_dec(v_unused_2667_);
v___x_2661_ = v___x_2647_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_dec(v___x_2647_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2659_);
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(lean_object* v_msg_2671_){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2672_ = ((lean_object*)(l_Std_Http_URI_instInhabitedBuilder_default));
v___x_2673_ = lean_panic_fn_borrowed(v___x_2672_, v_msg_2671_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x21(lean_object* v_b_2675_, lean_object* v_scheme_2676_){
_start:
{
lean_object* v___x_2677_; 
lean_inc_ref(v_scheme_2676_);
v___x_2677_ = l_Std_Http_URI_Builder_setScheme_x3f(v_b_2675_, v_scheme_2676_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2678_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2679_ = ((lean_object*)(l_Std_Http_URI_Builder_setScheme_x21___closed__0));
v___x_2680_ = lean_unsigned_to_nat(687u);
v___x_2681_ = lean_unsigned_to_nat(14u);
v___x_2682_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_2683_ = l_String_quote(v_scheme_2676_);
v___x_2684_ = lean_string_append(v___x_2682_, v___x_2683_);
lean_dec_ref(v___x_2683_);
v___x_2685_ = l_mkPanicMessageWithDecl(v___x_2678_, v___x_2679_, v___x_2680_, v___x_2681_, v___x_2684_);
lean_dec_ref(v___x_2684_);
v___x_2686_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2685_);
return v___x_2686_;
}
else
{
lean_object* v_val_2687_; 
lean_dec_ref(v_scheme_2676_);
v_val_2687_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_val_2687_);
lean_dec_ref_known(v___x_2677_, 1);
return v_val_2687_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo(lean_object* v_b_2688_, lean_object* v_username_2689_, lean_object* v_password_2690_){
_start:
{
lean_object* v_scheme_2691_; lean_object* v_host_2692_; lean_object* v_port_2693_; lean_object* v_pathSegments_2694_; lean_object* v_query_2695_; lean_object* v_fragment_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2719_; 
v_scheme_2691_ = lean_ctor_get(v_b_2688_, 0);
v_host_2692_ = lean_ctor_get(v_b_2688_, 2);
v_port_2693_ = lean_ctor_get(v_b_2688_, 3);
v_pathSegments_2694_ = lean_ctor_get(v_b_2688_, 4);
v_query_2695_ = lean_ctor_get(v_b_2688_, 5);
v_fragment_2696_ = lean_ctor_get(v_b_2688_, 6);
v_isSharedCheck_2719_ = !lean_is_exclusive(v_b_2688_);
if (v_isSharedCheck_2719_ == 0)
{
lean_object* v_unused_2720_; 
v_unused_2720_ = lean_ctor_get(v_b_2688_, 1);
lean_dec(v_unused_2720_);
v___x_2698_ = v_b_2688_;
v_isShared_2699_ = v_isSharedCheck_2719_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_fragment_2696_);
lean_inc(v_query_2695_);
lean_inc(v_pathSegments_2694_);
lean_inc(v_port_2693_);
lean_inc(v_host_2692_);
lean_inc(v_scheme_2691_);
lean_dec(v_b_2688_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2719_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___y_2701_; lean_object* v___x_2706_; 
v___x_2706_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_2689_);
if (lean_obj_tag(v_password_2690_) == 0)
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = lean_box(0);
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___y_2701_ = v___x_2708_;
goto v___jp_2700_;
}
else
{
lean_object* v_val_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2718_; 
v_val_2709_ = lean_ctor_get(v_password_2690_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_password_2690_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2711_ = v_password_2690_;
v_isShared_2712_ = v_isSharedCheck_2718_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_val_2709_);
lean_dec(v_password_2690_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2718_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2713_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_2709_);
lean_dec(v_val_2709_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2713_);
v___x_2715_ = v___x_2711_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
lean_object* v___x_2716_; 
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2706_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___y_2701_ = v___x_2716_;
goto v___jp_2700_;
}
}
}
v___jp_2700_:
{
lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___y_2701_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 1, v___x_2702_);
v___x_2704_ = v___x_2698_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_scheme_2691_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2705_, 2, v_host_2692_);
lean_ctor_set(v_reuseFailAlloc_2705_, 3, v_port_2693_);
lean_ctor_set(v_reuseFailAlloc_2705_, 4, v_pathSegments_2694_);
lean_ctor_set(v_reuseFailAlloc_2705_, 5, v_query_2695_);
lean_ctor_set(v_reuseFailAlloc_2705_, 6, v_fragment_2696_);
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
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo___boxed(lean_object* v_b_2721_, lean_object* v_username_2722_, lean_object* v_password_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_Std_Http_URI_Builder_setUserInfo(v_b_2721_, v_username_2722_, v_password_2723_);
lean_dec_ref(v_username_2722_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x3f(lean_object* v_b_2725_, lean_object* v_name_2726_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Std_Http_URI_DomainName_ofString_x3f(v_name_2726_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v___x_2728_; 
lean_dec_ref(v_b_2725_);
v___x_2728_ = lean_box(0);
return v___x_2728_;
}
else
{
lean_object* v_val_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2752_; 
v_val_2729_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2731_ = v___x_2727_;
v_isShared_2732_ = v_isSharedCheck_2752_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_val_2729_);
lean_dec(v___x_2727_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2752_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v_scheme_2733_; lean_object* v_userInfo_2734_; lean_object* v_port_2735_; lean_object* v_pathSegments_2736_; lean_object* v_query_2737_; lean_object* v_fragment_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2750_; 
v_scheme_2733_ = lean_ctor_get(v_b_2725_, 0);
v_userInfo_2734_ = lean_ctor_get(v_b_2725_, 1);
v_port_2735_ = lean_ctor_get(v_b_2725_, 3);
v_pathSegments_2736_ = lean_ctor_get(v_b_2725_, 4);
v_query_2737_ = lean_ctor_get(v_b_2725_, 5);
v_fragment_2738_ = lean_ctor_get(v_b_2725_, 6);
v_isSharedCheck_2750_ = !lean_is_exclusive(v_b_2725_);
if (v_isSharedCheck_2750_ == 0)
{
lean_object* v_unused_2751_; 
v_unused_2751_ = lean_ctor_get(v_b_2725_, 2);
lean_dec(v_unused_2751_);
v___x_2740_ = v_b_2725_;
v_isShared_2741_ = v_isSharedCheck_2750_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_fragment_2738_);
lean_inc(v_query_2737_);
lean_inc(v_pathSegments_2736_);
lean_inc(v_port_2735_);
lean_inc(v_userInfo_2734_);
lean_inc(v_scheme_2733_);
lean_dec(v_b_2725_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2750_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2742_, 0, v_val_2729_);
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 0, v___x_2742_);
v___x_2744_ = v___x_2731_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2742_);
v___x_2744_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2746_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 2, v___x_2744_);
v___x_2746_ = v___x_2740_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_scheme_2733_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_userInfo_2734_);
lean_ctor_set(v_reuseFailAlloc_2748_, 2, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2748_, 3, v_port_2735_);
lean_ctor_set(v_reuseFailAlloc_2748_, 4, v_pathSegments_2736_);
lean_ctor_set(v_reuseFailAlloc_2748_, 5, v_query_2737_);
lean_ctor_set(v_reuseFailAlloc_2748_, 6, v_fragment_2738_);
v___x_2746_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_object* v___x_2747_; 
v___x_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2746_);
return v___x_2747_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x21(lean_object* v_b_2755_, lean_object* v_name_2756_){
_start:
{
lean_object* v___x_2757_; 
lean_inc_ref(v_name_2756_);
v___x_2757_ = l_Std_Http_URI_Builder_setHost_x3f(v_b_2755_, v_name_2756_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2758_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2759_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__0));
v___x_2760_ = lean_unsigned_to_nat(716u);
v___x_2761_ = lean_unsigned_to_nat(14u);
v___x_2762_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__1));
v___x_2763_ = l_String_quote(v_name_2756_);
v___x_2764_ = lean_string_append(v___x_2762_, v___x_2763_);
lean_dec_ref(v___x_2763_);
v___x_2765_ = l_mkPanicMessageWithDecl(v___x_2758_, v___x_2759_, v___x_2760_, v___x_2761_, v___x_2764_);
lean_dec_ref(v___x_2764_);
v___x_2766_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2765_);
return v___x_2766_;
}
else
{
lean_object* v_val_2767_; 
lean_dec_ref(v_name_2756_);
v_val_2767_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_val_2767_);
lean_dec_ref_known(v___x_2757_, 1);
return v_val_2767_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv4(lean_object* v_b_2768_, lean_object* v_addr_2769_){
_start:
{
lean_object* v_scheme_2770_; lean_object* v_userInfo_2771_; lean_object* v_port_2772_; lean_object* v_pathSegments_2773_; lean_object* v_query_2774_; lean_object* v_fragment_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2784_; 
v_scheme_2770_ = lean_ctor_get(v_b_2768_, 0);
v_userInfo_2771_ = lean_ctor_get(v_b_2768_, 1);
v_port_2772_ = lean_ctor_get(v_b_2768_, 3);
v_pathSegments_2773_ = lean_ctor_get(v_b_2768_, 4);
v_query_2774_ = lean_ctor_get(v_b_2768_, 5);
v_fragment_2775_ = lean_ctor_get(v_b_2768_, 6);
v_isSharedCheck_2784_ = !lean_is_exclusive(v_b_2768_);
if (v_isSharedCheck_2784_ == 0)
{
lean_object* v_unused_2785_; 
v_unused_2785_ = lean_ctor_get(v_b_2768_, 2);
lean_dec(v_unused_2785_);
v___x_2777_ = v_b_2768_;
v_isShared_2778_ = v_isSharedCheck_2784_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_fragment_2775_);
lean_inc(v_query_2774_);
lean_inc(v_pathSegments_2773_);
lean_inc(v_port_2772_);
lean_inc(v_userInfo_2771_);
lean_inc(v_scheme_2770_);
lean_dec(v_b_2768_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2784_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2782_; 
v___x_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2779_, 0, v_addr_2769_);
v___x_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 2, v___x_2780_);
v___x_2782_ = v___x_2777_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_scheme_2770_);
lean_ctor_set(v_reuseFailAlloc_2783_, 1, v_userInfo_2771_);
lean_ctor_set(v_reuseFailAlloc_2783_, 2, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2783_, 3, v_port_2772_);
lean_ctor_set(v_reuseFailAlloc_2783_, 4, v_pathSegments_2773_);
lean_ctor_set(v_reuseFailAlloc_2783_, 5, v_query_2774_);
lean_ctor_set(v_reuseFailAlloc_2783_, 6, v_fragment_2775_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv6(lean_object* v_b_2786_, lean_object* v_addr_2787_){
_start:
{
lean_object* v_scheme_2788_; lean_object* v_userInfo_2789_; lean_object* v_port_2790_; lean_object* v_pathSegments_2791_; lean_object* v_query_2792_; lean_object* v_fragment_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2802_; 
v_scheme_2788_ = lean_ctor_get(v_b_2786_, 0);
v_userInfo_2789_ = lean_ctor_get(v_b_2786_, 1);
v_port_2790_ = lean_ctor_get(v_b_2786_, 3);
v_pathSegments_2791_ = lean_ctor_get(v_b_2786_, 4);
v_query_2792_ = lean_ctor_get(v_b_2786_, 5);
v_fragment_2793_ = lean_ctor_get(v_b_2786_, 6);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_b_2786_);
if (v_isSharedCheck_2802_ == 0)
{
lean_object* v_unused_2803_; 
v_unused_2803_ = lean_ctor_get(v_b_2786_, 2);
lean_dec(v_unused_2803_);
v___x_2795_ = v_b_2786_;
v_isShared_2796_ = v_isSharedCheck_2802_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_fragment_2793_);
lean_inc(v_query_2792_);
lean_inc(v_pathSegments_2791_);
lean_inc(v_port_2790_);
lean_inc(v_userInfo_2789_);
lean_inc(v_scheme_2788_);
lean_dec(v_b_2786_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2802_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2797_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2797_, 0, v_addr_2787_);
v___x_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 2, v___x_2798_);
v___x_2800_ = v___x_2795_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_scheme_2788_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_userInfo_2789_);
lean_ctor_set(v_reuseFailAlloc_2801_, 2, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2801_, 3, v_port_2790_);
lean_ctor_set(v_reuseFailAlloc_2801_, 4, v_pathSegments_2791_);
lean_ctor_set(v_reuseFailAlloc_2801_, 5, v_query_2792_);
lean_ctor_set(v_reuseFailAlloc_2801_, 6, v_fragment_2793_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort(lean_object* v_b_2804_, uint16_t v_port_2805_){
_start:
{
lean_object* v_scheme_2806_; lean_object* v_userInfo_2807_; lean_object* v_host_2808_; lean_object* v_pathSegments_2809_; lean_object* v_query_2810_; lean_object* v_fragment_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2819_; 
v_scheme_2806_ = lean_ctor_get(v_b_2804_, 0);
v_userInfo_2807_ = lean_ctor_get(v_b_2804_, 1);
v_host_2808_ = lean_ctor_get(v_b_2804_, 2);
v_pathSegments_2809_ = lean_ctor_get(v_b_2804_, 4);
v_query_2810_ = lean_ctor_get(v_b_2804_, 5);
v_fragment_2811_ = lean_ctor_get(v_b_2804_, 6);
v_isSharedCheck_2819_ = !lean_is_exclusive(v_b_2804_);
if (v_isSharedCheck_2819_ == 0)
{
lean_object* v_unused_2820_; 
v_unused_2820_ = lean_ctor_get(v_b_2804_, 3);
lean_dec(v_unused_2820_);
v___x_2813_ = v_b_2804_;
v_isShared_2814_ = v_isSharedCheck_2819_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_fragment_2811_);
lean_inc(v_query_2810_);
lean_inc(v_pathSegments_2809_);
lean_inc(v_host_2808_);
lean_inc(v_userInfo_2807_);
lean_inc(v_scheme_2806_);
lean_dec(v_b_2804_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2819_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2815_ = lean_alloc_ctor(2, 0, 2);
lean_ctor_set_uint16(v___x_2815_, 0, v_port_2805_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 3, v___x_2815_);
v___x_2817_ = v___x_2813_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_scheme_2806_);
lean_ctor_set(v_reuseFailAlloc_2818_, 1, v_userInfo_2807_);
lean_ctor_set(v_reuseFailAlloc_2818_, 2, v_host_2808_);
lean_ctor_set(v_reuseFailAlloc_2818_, 3, v___x_2815_);
lean_ctor_set(v_reuseFailAlloc_2818_, 4, v_pathSegments_2809_);
lean_ctor_set(v_reuseFailAlloc_2818_, 5, v_query_2810_);
lean_ctor_set(v_reuseFailAlloc_2818_, 6, v_fragment_2811_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort___boxed(lean_object* v_b_2821_, lean_object* v_port_2822_){
_start:
{
uint16_t v_port_boxed_2823_; lean_object* v_res_2824_; 
v_port_boxed_2823_ = lean_unbox(v_port_2822_);
v_res_2824_ = l_Std_Http_URI_Builder_setPort(v_b_2821_, v_port_boxed_2823_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPath(lean_object* v_b_2825_, lean_object* v_segments_2826_){
_start:
{
lean_object* v_scheme_2827_; lean_object* v_userInfo_2828_; lean_object* v_host_2829_; lean_object* v_port_2830_; lean_object* v_query_2831_; lean_object* v_fragment_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
v_scheme_2827_ = lean_ctor_get(v_b_2825_, 0);
v_userInfo_2828_ = lean_ctor_get(v_b_2825_, 1);
v_host_2829_ = lean_ctor_get(v_b_2825_, 2);
v_port_2830_ = lean_ctor_get(v_b_2825_, 3);
v_query_2831_ = lean_ctor_get(v_b_2825_, 5);
v_fragment_2832_ = lean_ctor_get(v_b_2825_, 6);
v_isSharedCheck_2839_ = !lean_is_exclusive(v_b_2825_);
if (v_isSharedCheck_2839_ == 0)
{
lean_object* v_unused_2840_; 
v_unused_2840_ = lean_ctor_get(v_b_2825_, 4);
lean_dec(v_unused_2840_);
v___x_2834_ = v_b_2825_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_fragment_2832_);
lean_inc(v_query_2831_);
lean_inc(v_port_2830_);
lean_inc(v_host_2829_);
lean_inc(v_userInfo_2828_);
lean_inc(v_scheme_2827_);
lean_dec(v_b_2825_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 4, v_segments_2826_);
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_scheme_2827_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_userInfo_2828_);
lean_ctor_set(v_reuseFailAlloc_2838_, 2, v_host_2829_);
lean_ctor_set(v_reuseFailAlloc_2838_, 3, v_port_2830_);
lean_ctor_set(v_reuseFailAlloc_2838_, 4, v_segments_2826_);
lean_ctor_set(v_reuseFailAlloc_2838_, 5, v_query_2831_);
lean_ctor_set(v_reuseFailAlloc_2838_, 6, v_fragment_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_appendPathSegment(lean_object* v_b_2841_, lean_object* v_segment_2842_){
_start:
{
lean_object* v_scheme_2843_; lean_object* v_userInfo_2844_; lean_object* v_host_2845_; lean_object* v_port_2846_; lean_object* v_pathSegments_2847_; lean_object* v_query_2848_; lean_object* v_fragment_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2857_; 
v_scheme_2843_ = lean_ctor_get(v_b_2841_, 0);
v_userInfo_2844_ = lean_ctor_get(v_b_2841_, 1);
v_host_2845_ = lean_ctor_get(v_b_2841_, 2);
v_port_2846_ = lean_ctor_get(v_b_2841_, 3);
v_pathSegments_2847_ = lean_ctor_get(v_b_2841_, 4);
v_query_2848_ = lean_ctor_get(v_b_2841_, 5);
v_fragment_2849_ = lean_ctor_get(v_b_2841_, 6);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_b_2841_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2851_ = v_b_2841_;
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_fragment_2849_);
lean_inc(v_query_2848_);
lean_inc(v_pathSegments_2847_);
lean_inc(v_port_2846_);
lean_inc(v_host_2845_);
lean_inc(v_userInfo_2844_);
lean_inc(v_scheme_2843_);
lean_dec(v_b_2841_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; lean_object* v___x_2855_; 
v___x_2853_ = lean_array_push(v_pathSegments_2847_, v_segment_2842_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 4, v___x_2853_);
v___x_2855_ = v___x_2851_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_scheme_2843_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_userInfo_2844_);
lean_ctor_set(v_reuseFailAlloc_2856_, 2, v_host_2845_);
lean_ctor_set(v_reuseFailAlloc_2856_, 3, v_port_2846_);
lean_ctor_set(v_reuseFailAlloc_2856_, 4, v___x_2853_);
lean_ctor_set(v_reuseFailAlloc_2856_, 5, v_query_2848_);
lean_ctor_set(v_reuseFailAlloc_2856_, 6, v_fragment_2849_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryParam(lean_object* v_b_2858_, lean_object* v_key_2859_, lean_object* v_value_2860_){
_start:
{
lean_object* v_scheme_2861_; lean_object* v_userInfo_2862_; lean_object* v_host_2863_; lean_object* v_port_2864_; lean_object* v_pathSegments_2865_; lean_object* v_query_2866_; lean_object* v_fragment_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2877_; 
v_scheme_2861_ = lean_ctor_get(v_b_2858_, 0);
v_userInfo_2862_ = lean_ctor_get(v_b_2858_, 1);
v_host_2863_ = lean_ctor_get(v_b_2858_, 2);
v_port_2864_ = lean_ctor_get(v_b_2858_, 3);
v_pathSegments_2865_ = lean_ctor_get(v_b_2858_, 4);
v_query_2866_ = lean_ctor_get(v_b_2858_, 5);
v_fragment_2867_ = lean_ctor_get(v_b_2858_, 6);
v_isSharedCheck_2877_ = !lean_is_exclusive(v_b_2858_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2869_ = v_b_2858_;
v_isShared_2870_ = v_isSharedCheck_2877_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_fragment_2867_);
lean_inc(v_query_2866_);
lean_inc(v_pathSegments_2865_);
lean_inc(v_port_2864_);
lean_inc(v_host_2863_);
lean_inc(v_userInfo_2862_);
lean_inc(v_scheme_2861_);
lean_dec(v_b_2858_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2877_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2875_; 
v___x_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2871_, 0, v_value_2860_);
v___x_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2872_, 0, v_key_2859_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = lean_array_push(v_query_2866_, v___x_2872_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 5, v___x_2873_);
v___x_2875_ = v___x_2869_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_scheme_2861_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_userInfo_2862_);
lean_ctor_set(v_reuseFailAlloc_2876_, 2, v_host_2863_);
lean_ctor_set(v_reuseFailAlloc_2876_, 3, v_port_2864_);
lean_ctor_set(v_reuseFailAlloc_2876_, 4, v_pathSegments_2865_);
lean_ctor_set(v_reuseFailAlloc_2876_, 5, v___x_2873_);
lean_ctor_set(v_reuseFailAlloc_2876_, 6, v_fragment_2867_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryFlag(lean_object* v_b_2878_, lean_object* v_key_2879_){
_start:
{
lean_object* v_scheme_2880_; lean_object* v_userInfo_2881_; lean_object* v_host_2882_; lean_object* v_port_2883_; lean_object* v_pathSegments_2884_; lean_object* v_query_2885_; lean_object* v_fragment_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2896_; 
v_scheme_2880_ = lean_ctor_get(v_b_2878_, 0);
v_userInfo_2881_ = lean_ctor_get(v_b_2878_, 1);
v_host_2882_ = lean_ctor_get(v_b_2878_, 2);
v_port_2883_ = lean_ctor_get(v_b_2878_, 3);
v_pathSegments_2884_ = lean_ctor_get(v_b_2878_, 4);
v_query_2885_ = lean_ctor_get(v_b_2878_, 5);
v_fragment_2886_ = lean_ctor_get(v_b_2878_, 6);
v_isSharedCheck_2896_ = !lean_is_exclusive(v_b_2878_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2888_ = v_b_2878_;
v_isShared_2889_ = v_isSharedCheck_2896_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_fragment_2886_);
lean_inc(v_query_2885_);
lean_inc(v_pathSegments_2884_);
lean_inc(v_port_2883_);
lean_inc(v_host_2882_);
lean_inc(v_userInfo_2881_);
lean_inc(v_scheme_2880_);
lean_dec(v_b_2878_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2896_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2894_; 
v___x_2890_ = lean_box(0);
v___x_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2891_, 0, v_key_2879_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
v___x_2892_ = lean_array_push(v_query_2885_, v___x_2891_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 5, v___x_2892_);
v___x_2894_ = v___x_2888_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_scheme_2880_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_userInfo_2881_);
lean_ctor_set(v_reuseFailAlloc_2895_, 2, v_host_2882_);
lean_ctor_set(v_reuseFailAlloc_2895_, 3, v_port_2883_);
lean_ctor_set(v_reuseFailAlloc_2895_, 4, v_pathSegments_2884_);
lean_ctor_set(v_reuseFailAlloc_2895_, 5, v___x_2892_);
lean_ctor_set(v_reuseFailAlloc_2895_, 6, v_fragment_2886_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setQuery(lean_object* v_b_2897_, lean_object* v_query_2898_){
_start:
{
lean_object* v_scheme_2899_; lean_object* v_userInfo_2900_; lean_object* v_host_2901_; lean_object* v_port_2902_; lean_object* v_pathSegments_2903_; lean_object* v_fragment_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
v_scheme_2899_ = lean_ctor_get(v_b_2897_, 0);
v_userInfo_2900_ = lean_ctor_get(v_b_2897_, 1);
v_host_2901_ = lean_ctor_get(v_b_2897_, 2);
v_port_2902_ = lean_ctor_get(v_b_2897_, 3);
v_pathSegments_2903_ = lean_ctor_get(v_b_2897_, 4);
v_fragment_2904_ = lean_ctor_get(v_b_2897_, 6);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_b_2897_);
if (v_isSharedCheck_2911_ == 0)
{
lean_object* v_unused_2912_; 
v_unused_2912_ = lean_ctor_get(v_b_2897_, 5);
lean_dec(v_unused_2912_);
v___x_2906_ = v_b_2897_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_fragment_2904_);
lean_inc(v_pathSegments_2903_);
lean_inc(v_port_2902_);
lean_inc(v_host_2901_);
lean_inc(v_userInfo_2900_);
lean_inc(v_scheme_2899_);
lean_dec(v_b_2897_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 5, v_query_2898_);
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_scheme_2899_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_userInfo_2900_);
lean_ctor_set(v_reuseFailAlloc_2910_, 2, v_host_2901_);
lean_ctor_set(v_reuseFailAlloc_2910_, 3, v_port_2902_);
lean_ctor_set(v_reuseFailAlloc_2910_, 4, v_pathSegments_2903_);
lean_ctor_set(v_reuseFailAlloc_2910_, 5, v_query_2898_);
lean_ctor_set(v_reuseFailAlloc_2910_, 6, v_fragment_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setFragment(lean_object* v_b_2913_, lean_object* v_fragment_2914_){
_start:
{
lean_object* v_scheme_2915_; lean_object* v_userInfo_2916_; lean_object* v_host_2917_; lean_object* v_port_2918_; lean_object* v_pathSegments_2919_; lean_object* v_query_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2928_; 
v_scheme_2915_ = lean_ctor_get(v_b_2913_, 0);
v_userInfo_2916_ = lean_ctor_get(v_b_2913_, 1);
v_host_2917_ = lean_ctor_get(v_b_2913_, 2);
v_port_2918_ = lean_ctor_get(v_b_2913_, 3);
v_pathSegments_2919_ = lean_ctor_get(v_b_2913_, 4);
v_query_2920_ = lean_ctor_get(v_b_2913_, 5);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_b_2913_);
if (v_isSharedCheck_2928_ == 0)
{
lean_object* v_unused_2929_; 
v_unused_2929_ = lean_ctor_get(v_b_2913_, 6);
lean_dec(v_unused_2929_);
v___x_2922_ = v_b_2913_;
v_isShared_2923_ = v_isSharedCheck_2928_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_query_2920_);
lean_inc(v_pathSegments_2919_);
lean_inc(v_port_2918_);
lean_inc(v_host_2917_);
lean_inc(v_userInfo_2916_);
lean_inc(v_scheme_2915_);
lean_dec(v_b_2913_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2928_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2924_; lean_object* v___x_2926_; 
v___x_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2924_, 0, v_fragment_2914_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 6, v___x_2924_);
v___x_2926_ = v___x_2922_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_scheme_2915_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_userInfo_2916_);
lean_ctor_set(v_reuseFailAlloc_2927_, 2, v_host_2917_);
lean_ctor_set(v_reuseFailAlloc_2927_, 3, v_port_2918_);
lean_ctor_set(v_reuseFailAlloc_2927_, 4, v_pathSegments_2919_);
lean_ctor_set(v_reuseFailAlloc_2927_, 5, v_query_2920_);
lean_ctor_set(v_reuseFailAlloc_2927_, 6, v___x_2924_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(size_t v_sz_2930_, size_t v_i_2931_, lean_object* v_bs_2932_){
_start:
{
uint8_t v___x_2933_; 
v___x_2933_ = lean_usize_dec_lt(v_i_2931_, v_sz_2930_);
if (v___x_2933_ == 0)
{
return v_bs_2932_;
}
else
{
lean_object* v_v_2934_; lean_object* v___x_2935_; lean_object* v_bs_x27_2936_; lean_object* v___x_2937_; size_t v___x_2938_; size_t v___x_2939_; lean_object* v___x_2940_; 
v_v_2934_ = lean_array_uget(v_bs_2932_, v_i_2931_);
v___x_2935_ = lean_unsigned_to_nat(0u);
v_bs_x27_2936_ = lean_array_uset(v_bs_2932_, v_i_2931_, v___x_2935_);
v___x_2937_ = l_Std_Http_URI_EncodedSegment_encode(v_v_2934_);
lean_dec(v_v_2934_);
v___x_2938_ = ((size_t)1ULL);
v___x_2939_ = lean_usize_add(v_i_2931_, v___x_2938_);
v___x_2940_ = lean_array_uset(v_bs_x27_2936_, v_i_2931_, v___x_2937_);
v_i_2931_ = v___x_2939_;
v_bs_2932_ = v___x_2940_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0___boxed(lean_object* v_sz_2942_, lean_object* v_i_2943_, lean_object* v_bs_2944_){
_start:
{
size_t v_sz_boxed_2945_; size_t v_i_boxed_2946_; lean_object* v_res_2947_; 
v_sz_boxed_2945_ = lean_unbox_usize(v_sz_2942_);
lean_dec(v_sz_2942_);
v_i_boxed_2946_ = lean_unbox_usize(v_i_2943_);
lean_dec(v_i_2943_);
v_res_2947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_boxed_2945_, v_i_boxed_2946_, v_bs_2944_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(size_t v_sz_2948_, size_t v_i_2949_, lean_object* v_bs_2950_){
_start:
{
uint8_t v___x_2951_; 
v___x_2951_ = lean_usize_dec_lt(v_i_2949_, v_sz_2948_);
if (v___x_2951_ == 0)
{
return v_bs_2950_;
}
else
{
lean_object* v_v_2952_; lean_object* v_fst_2953_; lean_object* v_snd_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2983_; 
v_v_2952_ = lean_array_uget(v_bs_2950_, v_i_2949_);
v_fst_2953_ = lean_ctor_get(v_v_2952_, 0);
v_snd_2954_ = lean_ctor_get(v_v_2952_, 1);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_v_2952_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2956_ = v_v_2952_;
v_isShared_2957_ = v_isSharedCheck_2983_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_snd_2954_);
lean_inc(v_fst_2953_);
lean_dec(v_v_2952_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2983_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; lean_object* v_bs_x27_2959_; lean_object* v___y_2961_; lean_object* v___x_2966_; 
v___x_2958_ = lean_unsigned_to_nat(0u);
v_bs_x27_2959_ = lean_array_uset(v_bs_2950_, v_i_2949_, v___x_2958_);
v___x_2966_ = l_Std_Http_URI_EncodedQueryParam_encode(v_fst_2953_);
lean_dec(v_fst_2953_);
if (lean_obj_tag(v_snd_2954_) == 0)
{
lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2967_ = lean_box(0);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v___x_2967_);
lean_ctor_set(v___x_2956_, 0, v___x_2966_);
v___x_2969_ = v___x_2956_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
v___y_2961_ = v___x_2969_;
goto v___jp_2960_;
}
}
else
{
lean_object* v_val_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2982_; 
v_val_2971_ = lean_ctor_get(v_snd_2954_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_snd_2954_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2973_ = v_snd_2954_;
v_isShared_2974_ = v_isSharedCheck_2982_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_val_2971_);
lean_dec(v_snd_2954_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2982_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2975_; lean_object* v___x_2977_; 
v___x_2975_ = l_Std_Http_URI_EncodedQueryParam_encode(v_val_2971_);
lean_dec(v_val_2971_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 0, v___x_2975_);
v___x_2977_ = v___x_2973_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2979_; 
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v___x_2977_);
lean_ctor_set(v___x_2956_, 0, v___x_2966_);
v___x_2979_ = v___x_2956_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
v___y_2961_ = v___x_2979_;
goto v___jp_2960_;
}
}
}
}
v___jp_2960_:
{
size_t v___x_2962_; size_t v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = ((size_t)1ULL);
v___x_2963_ = lean_usize_add(v_i_2949_, v___x_2962_);
v___x_2964_ = lean_array_uset(v_bs_x27_2959_, v_i_2949_, v___y_2961_);
v_i_2949_ = v___x_2963_;
v_bs_2950_ = v___x_2964_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1___boxed(lean_object* v_sz_2984_, lean_object* v_i_2985_, lean_object* v_bs_2986_){
_start:
{
size_t v_sz_boxed_2987_; size_t v_i_boxed_2988_; lean_object* v_res_2989_; 
v_sz_boxed_2987_ = lean_unbox_usize(v_sz_2984_);
lean_dec(v_sz_2984_);
v_i_boxed_2988_ = lean_unbox_usize(v_i_2985_);
lean_dec(v_i_2985_);
v_res_2989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_boxed_2987_, v_i_boxed_2988_, v_bs_2986_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_build(lean_object* v_b_2990_){
_start:
{
lean_object* v___y_2992_; lean_object* v___y_2993_; uint8_t v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v_scheme_3013_; lean_object* v_userInfo_3014_; lean_object* v_host_3015_; lean_object* v_port_3016_; lean_object* v_pathSegments_3017_; lean_object* v_query_3018_; lean_object* v_fragment_3019_; lean_object* v___y_3021_; 
v_scheme_3013_ = lean_ctor_get(v_b_2990_, 0);
lean_inc(v_scheme_3013_);
v_userInfo_3014_ = lean_ctor_get(v_b_2990_, 1);
lean_inc(v_userInfo_3014_);
v_host_3015_ = lean_ctor_get(v_b_2990_, 2);
lean_inc(v_host_3015_);
v_port_3016_ = lean_ctor_get(v_b_2990_, 3);
lean_inc(v_port_3016_);
v_pathSegments_3017_ = lean_ctor_get(v_b_2990_, 4);
lean_inc_ref(v_pathSegments_3017_);
v_query_3018_ = lean_ctor_get(v_b_2990_, 5);
lean_inc_ref(v_query_3018_);
v_fragment_3019_ = lean_ctor_get(v_b_2990_, 6);
lean_inc(v_fragment_3019_);
lean_dec_ref(v_b_2990_);
if (lean_obj_tag(v_scheme_3013_) == 0)
{
lean_object* v___x_3034_; 
v___x_3034_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___y_3021_ = v___x_3034_;
goto v___jp_3020_;
}
else
{
lean_object* v_val_3035_; 
v_val_3035_ = lean_ctor_get(v_scheme_3013_, 0);
lean_inc(v_val_3035_);
lean_dec_ref_known(v_scheme_3013_, 1);
v___y_3021_ = v_val_3035_;
goto v___jp_3020_;
}
v___jp_2991_:
{
size_t v_sz_2998_; size_t v___x_2999_; lean_object* v___x_3000_; lean_object* v_path_3001_; size_t v_sz_3002_; lean_object* v_query_3003_; lean_object* v___x_3004_; lean_object* v_query_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v_sz_2998_ = lean_array_size(v___y_2996_);
v___x_2999_ = ((size_t)0ULL);
v___x_3000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_2998_, v___x_2999_, v___y_2996_);
v_path_3001_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_path_3001_, 0, v___x_3000_);
lean_ctor_set_uint8(v_path_3001_, sizeof(void*)*1, v___y_2994_);
v_sz_3002_ = lean_array_size(v___y_2995_);
v_query_3003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_3002_, v___x_2999_, v___y_2995_);
v___x_3004_ = lean_array_to_list(v_query_3003_);
v_query_3005_ = lean_array_mk(v___x_3004_);
v___x_3006_ = lean_array_get_size(v_query_3005_);
v___x_3007_ = lean_unsigned_to_nat(0u);
v___x_3008_ = lean_nat_dec_eq(v___x_3006_, v___x_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3009_, 0, v_query_3005_);
v___x_3010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3010_, 0, v___y_2992_);
lean_ctor_set(v___x_3010_, 1, v___y_2997_);
lean_ctor_set(v___x_3010_, 2, v_path_3001_);
lean_ctor_set(v___x_3010_, 3, v___x_3009_);
lean_ctor_set(v___x_3010_, 4, v___y_2993_);
return v___x_3010_;
}
else
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec_ref(v_query_3005_);
v___x_3011_ = lean_box(0);
v___x_3012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3012_, 0, v___y_2992_);
lean_ctor_set(v___x_3012_, 1, v___y_2997_);
lean_ctor_set(v___x_3012_, 2, v_path_3001_);
lean_ctor_set(v___x_3012_, 3, v___x_3011_);
lean_ctor_set(v___x_3012_, 4, v___y_2993_);
return v___x_3012_;
}
}
v___jp_3020_:
{
if (lean_obj_tag(v_host_3015_) == 0)
{
uint8_t v___x_3022_; lean_object* v___x_3023_; 
lean_dec(v_port_3016_);
lean_dec(v_userInfo_3014_);
v___x_3022_ = 1;
v___x_3023_ = lean_box(0);
v___y_2992_ = v___y_3021_;
v___y_2993_ = v_fragment_3019_;
v___y_2994_ = v___x_3022_;
v___y_2995_ = v_query_3018_;
v___y_2996_ = v_pathSegments_3017_;
v___y_2997_ = v___x_3023_;
goto v___jp_2991_;
}
else
{
lean_object* v_val_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3033_; 
v_val_3024_ = lean_ctor_get(v_host_3015_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v_host_3015_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3026_ = v_host_3015_;
v_isShared_3027_ = v_isSharedCheck_3033_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_val_3024_);
lean_dec(v_host_3015_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3033_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
uint8_t v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3031_; 
v___x_3028_ = 1;
v___x_3029_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3029_, 0, v_userInfo_3014_);
lean_ctor_set(v___x_3029_, 1, v_val_3024_);
lean_ctor_set(v___x_3029_, 2, v_port_3016_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3029_);
v___x_3031_ = v___x_3026_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3029_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
v___y_2992_ = v___y_3021_;
v___y_2993_ = v_fragment_3019_;
v___y_2994_ = v___x_3028_;
v___y_2995_ = v_query_3018_;
v___y_2996_ = v_pathSegments_3017_;
v___y_2997_ = v___x_3031_;
goto v___jp_2991_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withScheme_x21(lean_object* v_uri_3036_, lean_object* v_scheme_3037_){
_start:
{
lean_object* v_authority_3038_; lean_object* v_path_3039_; lean_object* v_query_3040_; lean_object* v_fragment_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3049_; 
v_authority_3038_ = lean_ctor_get(v_uri_3036_, 1);
v_path_3039_ = lean_ctor_get(v_uri_3036_, 2);
v_query_3040_ = lean_ctor_get(v_uri_3036_, 3);
v_fragment_3041_ = lean_ctor_get(v_uri_3036_, 4);
v_isSharedCheck_3049_ = !lean_is_exclusive(v_uri_3036_);
if (v_isSharedCheck_3049_ == 0)
{
lean_object* v_unused_3050_; 
v_unused_3050_ = lean_ctor_get(v_uri_3036_, 0);
lean_dec(v_unused_3050_);
v___x_3043_ = v_uri_3036_;
v_isShared_3044_ = v_isSharedCheck_3049_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_fragment_3041_);
lean_inc(v_query_3040_);
lean_inc(v_path_3039_);
lean_inc(v_authority_3038_);
lean_dec(v_uri_3036_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3049_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3045_; lean_object* v___x_3047_; 
v___x_3045_ = l_Std_Http_URI_Scheme_ofString_x21(v_scheme_3037_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v___x_3045_);
v___x_3047_ = v___x_3043_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_authority_3038_);
lean_ctor_set(v_reuseFailAlloc_3048_, 2, v_path_3039_);
lean_ctor_set(v_reuseFailAlloc_3048_, 3, v_query_3040_);
lean_ctor_set(v_reuseFailAlloc_3048_, 4, v_fragment_3041_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withAuthority(lean_object* v_uri_3051_, lean_object* v_authority_3052_){
_start:
{
lean_object* v_scheme_3053_; lean_object* v_path_3054_; lean_object* v_query_3055_; lean_object* v_fragment_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
v_scheme_3053_ = lean_ctor_get(v_uri_3051_, 0);
v_path_3054_ = lean_ctor_get(v_uri_3051_, 2);
v_query_3055_ = lean_ctor_get(v_uri_3051_, 3);
v_fragment_3056_ = lean_ctor_get(v_uri_3051_, 4);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_uri_3051_);
if (v_isSharedCheck_3063_ == 0)
{
lean_object* v_unused_3064_; 
v_unused_3064_ = lean_ctor_get(v_uri_3051_, 1);
lean_dec(v_unused_3064_);
v___x_3058_ = v_uri_3051_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_fragment_3056_);
lean_inc(v_query_3055_);
lean_inc(v_path_3054_);
lean_inc(v_scheme_3053_);
lean_dec(v_uri_3051_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 1, v_authority_3052_);
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_scheme_3053_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v_authority_3052_);
lean_ctor_set(v_reuseFailAlloc_3062_, 2, v_path_3054_);
lean_ctor_set(v_reuseFailAlloc_3062_, 3, v_query_3055_);
lean_ctor_set(v_reuseFailAlloc_3062_, 4, v_fragment_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withPath(lean_object* v_uri_3065_, lean_object* v_path_3066_){
_start:
{
lean_object* v_scheme_3067_; lean_object* v_authority_3068_; lean_object* v_query_3069_; lean_object* v_fragment_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
v_scheme_3067_ = lean_ctor_get(v_uri_3065_, 0);
v_authority_3068_ = lean_ctor_get(v_uri_3065_, 1);
v_query_3069_ = lean_ctor_get(v_uri_3065_, 3);
v_fragment_3070_ = lean_ctor_get(v_uri_3065_, 4);
v_isSharedCheck_3077_ = !lean_is_exclusive(v_uri_3065_);
if (v_isSharedCheck_3077_ == 0)
{
lean_object* v_unused_3078_; 
v_unused_3078_ = lean_ctor_get(v_uri_3065_, 2);
lean_dec(v_unused_3078_);
v___x_3072_ = v_uri_3065_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_fragment_3070_);
lean_inc(v_query_3069_);
lean_inc(v_authority_3068_);
lean_inc(v_scheme_3067_);
lean_dec(v_uri_3065_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 2, v_path_3066_);
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_scheme_3067_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_authority_3068_);
lean_ctor_set(v_reuseFailAlloc_3076_, 2, v_path_3066_);
lean_ctor_set(v_reuseFailAlloc_3076_, 3, v_query_3069_);
lean_ctor_set(v_reuseFailAlloc_3076_, 4, v_fragment_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withQuery(lean_object* v_uri_3079_, lean_object* v_query_3080_){
_start:
{
lean_object* v_scheme_3081_; lean_object* v_authority_3082_; lean_object* v_path_3083_; lean_object* v_fragment_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3092_; 
v_scheme_3081_ = lean_ctor_get(v_uri_3079_, 0);
v_authority_3082_ = lean_ctor_get(v_uri_3079_, 1);
v_path_3083_ = lean_ctor_get(v_uri_3079_, 2);
v_fragment_3084_ = lean_ctor_get(v_uri_3079_, 4);
v_isSharedCheck_3092_ = !lean_is_exclusive(v_uri_3079_);
if (v_isSharedCheck_3092_ == 0)
{
lean_object* v_unused_3093_; 
v_unused_3093_ = lean_ctor_get(v_uri_3079_, 3);
lean_dec(v_unused_3093_);
v___x_3086_ = v_uri_3079_;
v_isShared_3087_ = v_isSharedCheck_3092_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_fragment_3084_);
lean_inc(v_path_3083_);
lean_inc(v_authority_3082_);
lean_inc(v_scheme_3081_);
lean_dec(v_uri_3079_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3092_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3088_; lean_object* v___x_3090_; 
v___x_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3088_, 0, v_query_3080_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 3, v___x_3088_);
v___x_3090_ = v___x_3086_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_scheme_3081_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_authority_3082_);
lean_ctor_set(v_reuseFailAlloc_3091_, 2, v_path_3083_);
lean_ctor_set(v_reuseFailAlloc_3091_, 3, v___x_3088_);
lean_ctor_set(v_reuseFailAlloc_3091_, 4, v_fragment_3084_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withFragment(lean_object* v_uri_3094_, lean_object* v_fragment_3095_){
_start:
{
lean_object* v_scheme_3096_; lean_object* v_authority_3097_; lean_object* v_path_3098_; lean_object* v_query_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
v_scheme_3096_ = lean_ctor_get(v_uri_3094_, 0);
v_authority_3097_ = lean_ctor_get(v_uri_3094_, 1);
v_path_3098_ = lean_ctor_get(v_uri_3094_, 2);
v_query_3099_ = lean_ctor_get(v_uri_3094_, 3);
v_isSharedCheck_3106_ = !lean_is_exclusive(v_uri_3094_);
if (v_isSharedCheck_3106_ == 0)
{
lean_object* v_unused_3107_; 
v_unused_3107_ = lean_ctor_get(v_uri_3094_, 4);
lean_dec(v_unused_3107_);
v___x_3101_ = v_uri_3094_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_query_3099_);
lean_inc(v_path_3098_);
lean_inc(v_authority_3097_);
lean_inc(v_scheme_3096_);
lean_dec(v_uri_3094_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 4, v_fragment_3095_);
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_scheme_3096_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v_authority_3097_);
lean_ctor_set(v_reuseFailAlloc_3105_, 2, v_path_3098_);
lean_ctor_set(v_reuseFailAlloc_3105_, 3, v_query_3099_);
lean_ctor_set(v_reuseFailAlloc_3105_, 4, v_fragment_3095_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_normalize(lean_object* v_uri_3108_){
_start:
{
lean_object* v_scheme_3109_; lean_object* v_authority_3110_; lean_object* v_path_3111_; lean_object* v_query_3112_; lean_object* v_fragment_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3121_; 
v_scheme_3109_ = lean_ctor_get(v_uri_3108_, 0);
v_authority_3110_ = lean_ctor_get(v_uri_3108_, 1);
v_path_3111_ = lean_ctor_get(v_uri_3108_, 2);
v_query_3112_ = lean_ctor_get(v_uri_3108_, 3);
v_fragment_3113_ = lean_ctor_get(v_uri_3108_, 4);
v_isSharedCheck_3121_ = !lean_is_exclusive(v_uri_3108_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3115_ = v_uri_3108_;
v_isShared_3116_ = v_isSharedCheck_3121_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_fragment_3113_);
lean_inc(v_query_3112_);
lean_inc(v_path_3111_);
lean_inc(v_authority_3110_);
lean_inc(v_scheme_3109_);
lean_dec(v_uri_3108_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3121_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3117_; lean_object* v___x_3119_; 
v___x_3117_ = l_Std_Http_URI_Path_normalize(v_path_3111_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 2, v___x_3117_);
v___x_3119_ = v___x_3115_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_scheme_3109_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v_authority_3110_);
lean_ctor_set(v_reuseFailAlloc_3120_, 2, v___x_3117_);
lean_ctor_set(v_reuseFailAlloc_3120_, 3, v_query_3112_);
lean_ctor_set(v_reuseFailAlloc_3120_, 4, v_fragment_3113_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___redArg(lean_object* v_x_3122_){
_start:
{
lean_object* v_scheme_3123_; lean_object* v_host_3124_; uint16_t v_port_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v_ctr_3146_; lean_object* v_a_3147_; 
v_scheme_3123_ = lean_ctor_get(v_x_3122_, 0);
lean_inc_ref(v_scheme_3123_);
v_host_3124_ = lean_ctor_get(v_x_3122_, 1);
lean_inc_ref(v_host_3124_);
v_port_3125_ = lean_ctor_get_uint16(v_x_3122_, sizeof(void*)*2);
lean_dec_ref(v_x_3122_);
v___x_3126_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_3127_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_3128_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_3129_ = l_String_quote(v_scheme_3123_);
v___x_3130_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
v___x_3131_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3128_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
v___x_3132_ = 0;
v___x_3133_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3133_, 0, v___x_3131_);
lean_ctor_set_uint8(v___x_3133_, sizeof(void*)*1, v___x_3132_);
v___x_3134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3127_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_3136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3134_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = lean_box(1);
v___x_3138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3136_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_3140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3138_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
lean_ctor_set(v___x_3141_, 1, v___x_3126_);
v___x_3142_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_3143_ = lean_unsigned_to_nat(0u);
v___x_3144_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_3124_))
{
case 0:
{
lean_object* v_name_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3186_; 
v_name_3177_ = lean_ctor_get(v_host_3124_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_host_3124_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3179_ = v_host_3124_;
v_isShared_3180_ = v_isSharedCheck_3186_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_name_3177_);
lean_dec(v_host_3124_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3186_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3184_; 
v___x_3181_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_3182_ = l_String_quote(v_name_3177_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set_tag(v___x_3179_, 3);
lean_ctor_set(v___x_3179_, 0, v___x_3182_);
v___x_3184_ = v___x_3179_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3182_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
v_ctr_3146_ = v___x_3181_;
v_a_3147_ = v___x_3184_;
goto v___jp_3145_;
}
}
}
case 1:
{
lean_object* v_ipv4_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3196_; 
v_ipv4_3187_ = lean_ctor_get(v_host_3124_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v_host_3124_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3189_ = v_host_3124_;
v_isShared_3190_ = v_isSharedCheck_3196_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_ipv4_3187_);
lean_dec(v_host_3124_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3196_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3194_; 
v___x_3191_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_3192_ = lean_uv_ntop_v4(v_ipv4_3187_);
lean_dec_ref(v_ipv4_3187_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set_tag(v___x_3189_, 3);
lean_ctor_set(v___x_3189_, 0, v___x_3192_);
v___x_3194_ = v___x_3189_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3192_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
v_ctr_3146_ = v___x_3191_;
v_a_3147_ = v___x_3194_;
goto v___jp_3145_;
}
}
}
default: 
{
lean_object* v_ipv6_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3206_; 
v_ipv6_3197_ = lean_ctor_get(v_host_3124_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v_host_3124_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3199_ = v_host_3124_;
v_isShared_3200_ = v_isSharedCheck_3206_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_ipv6_3197_);
lean_dec(v_host_3124_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3206_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3204_; 
v___x_3201_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_3202_ = lean_uv_ntop_v6(v_ipv6_3197_);
lean_dec_ref(v_ipv6_3197_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set_tag(v___x_3199_, 3);
lean_ctor_set(v___x_3199_, 0, v___x_3202_);
v___x_3204_ = v___x_3199_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
v_ctr_3146_ = v___x_3201_;
v_a_3147_ = v___x_3204_;
goto v___jp_3145_;
}
}
}
}
v___jp_3145_:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3148_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_3149_ = lean_string_append(v___x_3148_, v_ctr_3146_);
v___x_3150_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
v___x_3151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
lean_ctor_set(v___x_3151_, 1, v___x_3137_);
v___x_3152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
lean_ctor_set(v___x_3152_, 1, v_a_3147_);
v___x_3153_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3144_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
v___x_3154_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
lean_ctor_set_uint8(v___x_3154_, sizeof(void*)*1, v___x_3132_);
v___x_3155_ = l_Repr_addAppParen(v___x_3154_, v___x_3143_);
v___x_3156_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3142_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
lean_ctor_set_uint8(v___x_3157_, sizeof(void*)*1, v___x_3132_);
v___x_3158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3141_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
v___x_3159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
lean_ctor_set(v___x_3159_, 1, v___x_3135_);
v___x_3160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
lean_ctor_set(v___x_3160_, 1, v___x_3137_);
v___x_3161_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_3162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3160_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
lean_ctor_set(v___x_3163_, 1, v___x_3126_);
v___x_3164_ = lean_uint16_to_nat(v_port_3125_);
v___x_3165_ = l_Nat_reprFast(v___x_3164_);
v___x_3166_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
v___x_3167_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3142_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
lean_ctor_set_uint8(v___x_3168_, sizeof(void*)*1, v___x_3132_);
v___x_3169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3163_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_3171_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_3172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
lean_ctor_set(v___x_3172_, 1, v___x_3169_);
v___x_3173_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_3174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3172_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
v___x_3175_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3170_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
lean_ctor_set_uint8(v___x_3176_, sizeof(void*)*1, v___x_3132_);
return v___x_3176_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr(lean_object* v_x_3207_, lean_object* v_prec_3208_){
_start:
{
lean_object* v___x_3209_; 
v___x_3209_ = l_Std_Http_URI_instReprOrigin_repr___redArg(v_x_3207_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprOrigin_repr___boxed(lean_object* v_x_3210_, lean_object* v_prec_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Std_Http_URI_instReprOrigin_repr(v_x_3210_, v_prec_3211_);
lean_dec(v_prec_3211_);
return v_res_3212_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqOrigin_beq(lean_object* v_x_3215_, lean_object* v_x_3216_){
_start:
{
lean_object* v_scheme_3217_; lean_object* v_host_3218_; uint16_t v_port_3219_; lean_object* v_scheme_3220_; lean_object* v_host_3221_; uint16_t v_port_3222_; uint8_t v___x_3223_; 
v_scheme_3217_ = lean_ctor_get(v_x_3215_, 0);
v_host_3218_ = lean_ctor_get(v_x_3215_, 1);
v_port_3219_ = lean_ctor_get_uint16(v_x_3215_, sizeof(void*)*2);
v_scheme_3220_ = lean_ctor_get(v_x_3216_, 0);
v_host_3221_ = lean_ctor_get(v_x_3216_, 1);
v_port_3222_ = lean_ctor_get_uint16(v_x_3216_, sizeof(void*)*2);
v___x_3223_ = lean_string_dec_eq(v_scheme_3217_, v_scheme_3220_);
if (v___x_3223_ == 0)
{
return v___x_3223_;
}
else
{
uint8_t v___x_3224_; 
v___x_3224_ = l_Std_Http_URI_instBEqHost_beq(v_host_3218_, v_host_3221_);
if (v___x_3224_ == 0)
{
return v___x_3224_;
}
else
{
uint8_t v___x_3225_; 
v___x_3225_ = lean_uint16_dec_eq(v_port_3219_, v_port_3222_);
return v___x_3225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqOrigin_beq___boxed(lean_object* v_x_3226_, lean_object* v_x_3227_){
_start:
{
uint8_t v_res_3228_; lean_object* v_r_3229_; 
v_res_3228_ = l_Std_Http_URI_instBEqOrigin_beq(v_x_3226_, v_x_3227_);
lean_dec_ref(v_x_3227_);
lean_dec_ref(v_x_3226_);
v_r_3229_ = lean_box(v_res_3228_);
return v_r_3229_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Origin_hostHeader(lean_object* v_o_3232_){
_start:
{
lean_object* v_scheme_3233_; lean_object* v_host_3234_; uint16_t v_port_3235_; lean_object* v___y_3237_; uint16_t v_defaultPort_3243_; uint8_t v___x_3244_; 
v_scheme_3233_ = lean_ctor_get(v_o_3232_, 0);
lean_inc_ref(v_scheme_3233_);
v_host_3234_ = lean_ctor_get(v_o_3232_, 1);
lean_inc_ref(v_host_3234_);
v_port_3235_ = lean_ctor_get_uint16(v_o_3232_, sizeof(void*)*2);
lean_dec_ref(v_o_3232_);
v_defaultPort_3243_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_3233_);
lean_dec_ref(v_scheme_3233_);
v___x_3244_ = lean_uint16_dec_eq(v_port_3235_, v_defaultPort_3243_);
if (v___x_3244_ == 0)
{
switch(lean_obj_tag(v_host_3234_))
{
case 0:
{
lean_object* v_name_3245_; 
v_name_3245_ = lean_ctor_get(v_host_3234_, 0);
lean_inc_ref(v_name_3245_);
lean_dec_ref_known(v_host_3234_, 1);
v___y_3237_ = v_name_3245_;
goto v___jp_3236_;
}
case 1:
{
lean_object* v_ipv4_3246_; lean_object* v___x_3247_; 
v_ipv4_3246_ = lean_ctor_get(v_host_3234_, 0);
lean_inc_ref(v_ipv4_3246_);
lean_dec_ref_known(v_host_3234_, 1);
v___x_3247_ = lean_uv_ntop_v4(v_ipv4_3246_);
lean_dec_ref(v_ipv4_3246_);
v___y_3237_ = v___x_3247_;
goto v___jp_3236_;
}
default: 
{
lean_object* v_ipv6_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v_ipv6_3248_ = lean_ctor_get(v_host_3234_, 0);
lean_inc_ref(v_ipv6_3248_);
lean_dec_ref_known(v_host_3234_, 1);
v___x_3249_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3250_ = lean_uv_ntop_v6(v_ipv6_3248_);
lean_dec_ref(v_ipv6_3248_);
v___x_3251_ = lean_string_append(v___x_3249_, v___x_3250_);
lean_dec_ref(v___x_3250_);
v___x_3252_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3253_ = lean_string_append(v___x_3251_, v___x_3252_);
v___y_3237_ = v___x_3253_;
goto v___jp_3236_;
}
}
}
else
{
switch(lean_obj_tag(v_host_3234_))
{
case 0:
{
lean_object* v_name_3254_; 
v_name_3254_ = lean_ctor_get(v_host_3234_, 0);
lean_inc_ref(v_name_3254_);
lean_dec_ref_known(v_host_3234_, 1);
return v_name_3254_;
}
case 1:
{
lean_object* v_ipv4_3255_; lean_object* v___x_3256_; 
v_ipv4_3255_ = lean_ctor_get(v_host_3234_, 0);
lean_inc_ref(v_ipv4_3255_);
lean_dec_ref_known(v_host_3234_, 1);
v___x_3256_ = lean_uv_ntop_v4(v_ipv4_3255_);
lean_dec_ref(v_ipv4_3255_);
return v___x_3256_;
}
default: 
{
lean_object* v_ipv6_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_ipv6_3257_ = lean_ctor_get(v_host_3234_, 0);
lean_inc_ref(v_ipv6_3257_);
lean_dec_ref_known(v_host_3234_, 1);
v___x_3258_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3259_ = lean_uv_ntop_v6(v_ipv6_3257_);
lean_dec_ref(v_ipv6_3257_);
v___x_3260_ = lean_string_append(v___x_3258_, v___x_3259_);
lean_dec_ref(v___x_3259_);
v___x_3261_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3262_ = lean_string_append(v___x_3260_, v___x_3261_);
return v___x_3262_;
}
}
}
v___jp_3236_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3238_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3239_ = lean_string_append(v___y_3237_, v___x_3238_);
v___x_3240_ = lean_uint16_to_nat(v_port_3235_);
v___x_3241_ = l_Nat_reprFast(v___x_3240_);
v___x_3242_ = lean_string_append(v___x_3239_, v___x_3241_);
lean_dec_ref(v___x_3241_);
return v___x_3242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___redArg(lean_object* v_x_3269_){
_start:
{
lean_object* v_authority_3270_; lean_object* v_path_3271_; lean_object* v_query_3272_; lean_object* v_fragment_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; uint8_t v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v_authority_3270_ = lean_ctor_get(v_x_3269_, 0);
lean_inc(v_authority_3270_);
v_path_3271_ = lean_ctor_get(v_x_3269_, 1);
lean_inc_ref(v_path_3271_);
v_query_3272_ = lean_ctor_get(v_x_3269_, 2);
lean_inc(v_query_3272_);
v_fragment_3273_ = lean_ctor_get(v_x_3269_, 3);
lean_inc(v_fragment_3273_);
lean_dec_ref(v_x_3269_);
v___x_3274_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_3275_ = ((lean_object*)(l_Std_Http_URI_instReprRelativeRef_repr___redArg___closed__1));
v___x_3276_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_3277_ = lean_unsigned_to_nat(0u);
v___x_3278_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_3270_, v___x_3277_);
v___x_3279_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3276_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
v___x_3280_ = 0;
v___x_3281_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set_uint8(v___x_3281_, sizeof(void*)*1, v___x_3280_);
v___x_3282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3275_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
v___x_3283_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_3284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3282_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = lean_box(1);
v___x_3286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3284_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_3288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3286_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
lean_ctor_set(v___x_3289_, 1, v___x_3274_);
v___x_3290_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_3291_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3271_);
v___x_3292_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3290_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*1, v___x_3280_);
v___x_3294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3289_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
lean_ctor_set(v___x_3295_, 1, v___x_3283_);
v___x_3296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3295_);
lean_ctor_set(v___x_3296_, 1, v___x_3285_);
v___x_3297_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_3298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3296_);
lean_ctor_set(v___x_3298_, 1, v___x_3297_);
v___x_3299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
lean_ctor_set(v___x_3299_, 1, v___x_3274_);
v___x_3300_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_3301_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3272_, v___x_3277_);
v___x_3302_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3300_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
lean_ctor_set_uint8(v___x_3303_, sizeof(void*)*1, v___x_3280_);
v___x_3304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3299_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
lean_ctor_set(v___x_3305_, 1, v___x_3283_);
v___x_3306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
lean_ctor_set(v___x_3306_, 1, v___x_3285_);
v___x_3307_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_3308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3306_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
lean_ctor_set(v___x_3309_, 1, v___x_3274_);
v___x_3310_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_3311_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_3273_, v___x_3277_);
v___x_3312_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3310_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
v___x_3313_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
lean_ctor_set_uint8(v___x_3313_, sizeof(void*)*1, v___x_3280_);
v___x_3314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3309_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v___x_3315_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_3316_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_3317_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
lean_ctor_set(v___x_3317_, 1, v___x_3314_);
v___x_3318_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_3319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3317_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
v___x_3320_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3315_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
v___x_3321_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3321_, 0, v___x_3320_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*1, v___x_3280_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr(lean_object* v_x_3322_, lean_object* v_prec_3323_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_x_3322_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprRelativeRef_repr___boxed(lean_object* v_x_3325_, lean_object* v_prec_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l_Std_Http_URI_instReprRelativeRef_repr(v_x_3325_, v_prec_3326_);
lean_dec(v_prec_3326_);
return v_res_3327_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqRelativeRef_beq(lean_object* v_x_3335_, lean_object* v_x_3336_){
_start:
{
lean_object* v_authority_3337_; lean_object* v_path_3338_; lean_object* v_query_3339_; lean_object* v_fragment_3340_; lean_object* v_authority_3341_; lean_object* v_path_3342_; lean_object* v_query_3343_; lean_object* v_fragment_3344_; uint8_t v___x_3345_; 
v_authority_3337_ = lean_ctor_get(v_x_3335_, 0);
v_path_3338_ = lean_ctor_get(v_x_3335_, 1);
v_query_3339_ = lean_ctor_get(v_x_3335_, 2);
v_fragment_3340_ = lean_ctor_get(v_x_3335_, 3);
v_authority_3341_ = lean_ctor_get(v_x_3336_, 0);
v_path_3342_ = lean_ctor_get(v_x_3336_, 1);
v_query_3343_ = lean_ctor_get(v_x_3336_, 2);
v_fragment_3344_ = lean_ctor_get(v_x_3336_, 3);
v___x_3345_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_3337_, v_authority_3341_);
if (v___x_3345_ == 0)
{
return v___x_3345_;
}
else
{
uint8_t v___x_3346_; 
v___x_3346_ = l_Std_Http_URI_instBEqPath_beq(v_path_3338_, v_path_3342_);
if (v___x_3346_ == 0)
{
return v___x_3346_;
}
else
{
uint8_t v___x_3347_; 
v___x_3347_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_query_3339_, v_query_3343_);
if (v___x_3347_ == 0)
{
return v___x_3347_;
}
else
{
uint8_t v___x_3348_; 
v___x_3348_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__2(v_fragment_3340_, v_fragment_3344_);
return v___x_3348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqRelativeRef_beq___boxed(lean_object* v_x_3349_, lean_object* v_x_3350_){
_start:
{
uint8_t v_res_3351_; lean_object* v_r_3352_; 
v_res_3351_ = l_Std_Http_URI_instBEqRelativeRef_beq(v_x_3349_, v_x_3350_);
lean_dec_ref(v_x_3350_);
lean_dec_ref(v_x_3349_);
v_r_3352_ = lean_box(v_res_3351_);
return v_r_3352_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringRelativeRef___lam__1(lean_object* v___f_3355_, lean_object* v_ref_3356_){
_start:
{
lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v_authority_3365_; lean_object* v_path_3366_; lean_object* v_query_3367_; lean_object* v_fragment_3368_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3380_; 
v_authority_3365_ = lean_ctor_get(v_ref_3356_, 0);
lean_inc(v_authority_3365_);
v_path_3366_ = lean_ctor_get(v_ref_3356_, 1);
lean_inc_ref(v_path_3366_);
v_query_3367_ = lean_ctor_get(v_ref_3356_, 2);
lean_inc(v_query_3367_);
v_fragment_3368_ = lean_ctor_get(v_ref_3356_, 3);
lean_inc(v_fragment_3368_);
lean_dec_ref(v_ref_3356_);
if (lean_obj_tag(v_authority_3365_) == 0)
{
lean_object* v___x_3391_; 
v___x_3391_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3380_ = v___x_3391_;
goto v___jp_3379_;
}
else
{
lean_object* v_val_3392_; lean_object* v_userInfo_3393_; lean_object* v_host_3394_; lean_object* v_port_3395_; lean_object* v___x_3396_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3415_; 
v_val_3392_ = lean_ctor_get(v_authority_3365_, 0);
lean_inc(v_val_3392_);
lean_dec_ref_known(v_authority_3365_, 1);
v_userInfo_3393_ = lean_ctor_get(v_val_3392_, 0);
lean_inc(v_userInfo_3393_);
v_host_3394_ = lean_ctor_get(v_val_3392_, 1);
lean_inc_ref(v_host_3394_);
v_port_3395_ = lean_ctor_get(v_val_3392_, 2);
lean_inc(v_port_3395_);
lean_dec(v_val_3392_);
v___x_3396_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3393_) == 0)
{
lean_object* v___x_3425_; 
v___x_3425_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3415_ = v___x_3425_;
goto v___jp_3414_;
}
else
{
lean_object* v_val_3426_; lean_object* v_password_3427_; 
v_val_3426_ = lean_ctor_get(v_userInfo_3393_, 0);
lean_inc(v_val_3426_);
lean_dec_ref_known(v_userInfo_3393_, 1);
v_password_3427_ = lean_ctor_get(v_val_3426_, 1);
if (lean_obj_tag(v_password_3427_) == 0)
{
lean_object* v_username_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v_username_3428_ = lean_ctor_get(v_val_3426_, 0);
lean_inc_ref(v_username_3428_);
lean_dec(v_val_3426_);
v___x_3429_ = lean_string_from_utf8_unchecked(v_username_3428_);
v___x_3430_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3431_ = lean_string_append(v___x_3429_, v___x_3430_);
v___y_3415_ = v___x_3431_;
goto v___jp_3414_;
}
else
{
lean_object* v_username_3432_; lean_object* v_val_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
lean_inc_ref(v_password_3427_);
v_username_3432_ = lean_ctor_get(v_val_3426_, 0);
lean_inc_ref(v_username_3432_);
lean_dec(v_val_3426_);
v_val_3433_ = lean_ctor_get(v_password_3427_, 0);
lean_inc(v_val_3433_);
lean_dec_ref_known(v_password_3427_, 1);
v___x_3434_ = lean_string_from_utf8_unchecked(v_username_3432_);
v___x_3435_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3436_ = lean_string_append(v___x_3434_, v___x_3435_);
v___x_3437_ = lean_string_from_utf8_unchecked(v_val_3433_);
v___x_3438_ = lean_string_append(v___x_3436_, v___x_3437_);
lean_dec_ref(v___x_3437_);
v___x_3439_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3440_ = lean_string_append(v___x_3438_, v___x_3439_);
v___y_3415_ = v___x_3440_;
goto v___jp_3414_;
}
}
v___jp_3397_:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3401_ = lean_string_append(v___y_3398_, v___y_3399_);
lean_dec_ref(v___y_3399_);
v___x_3402_ = lean_string_append(v___x_3401_, v___y_3400_);
lean_dec_ref(v___y_3400_);
v___x_3403_ = lean_string_append(v___x_3396_, v___x_3402_);
lean_dec_ref(v___x_3402_);
v___y_3380_ = v___x_3403_;
goto v___jp_3379_;
}
v___jp_3404_:
{
switch(lean_obj_tag(v_port_3395_))
{
case 0:
{
lean_object* v___x_3407_; 
v___x_3407_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3398_ = v___y_3405_;
v___y_3399_ = v___y_3406_;
v___y_3400_ = v___x_3407_;
goto v___jp_3397_;
}
case 1:
{
lean_object* v___x_3408_; 
v___x_3408_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3398_ = v___y_3405_;
v___y_3399_ = v___y_3406_;
v___y_3400_ = v___x_3408_;
goto v___jp_3397_;
}
default: 
{
uint16_t v_port_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v_port_3409_ = lean_ctor_get_uint16(v_port_3395_, 0);
lean_dec_ref_known(v_port_3395_, 0);
v___x_3410_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3411_ = lean_uint16_to_nat(v_port_3409_);
v___x_3412_ = l_Nat_reprFast(v___x_3411_);
v___x_3413_ = lean_string_append(v___x_3410_, v___x_3412_);
lean_dec_ref(v___x_3412_);
v___y_3398_ = v___y_3405_;
v___y_3399_ = v___y_3406_;
v___y_3400_ = v___x_3413_;
goto v___jp_3397_;
}
}
}
v___jp_3414_:
{
switch(lean_obj_tag(v_host_3394_))
{
case 0:
{
lean_object* v_name_3416_; 
v_name_3416_ = lean_ctor_get(v_host_3394_, 0);
lean_inc_ref(v_name_3416_);
lean_dec_ref_known(v_host_3394_, 1);
v___y_3405_ = v___y_3415_;
v___y_3406_ = v_name_3416_;
goto v___jp_3404_;
}
case 1:
{
lean_object* v_ipv4_3417_; lean_object* v___x_3418_; 
v_ipv4_3417_ = lean_ctor_get(v_host_3394_, 0);
lean_inc_ref(v_ipv4_3417_);
lean_dec_ref_known(v_host_3394_, 1);
v___x_3418_ = lean_uv_ntop_v4(v_ipv4_3417_);
lean_dec_ref(v_ipv4_3417_);
v___y_3405_ = v___y_3415_;
v___y_3406_ = v___x_3418_;
goto v___jp_3404_;
}
default: 
{
lean_object* v_ipv6_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v_ipv6_3419_ = lean_ctor_get(v_host_3394_, 0);
lean_inc_ref(v_ipv6_3419_);
lean_dec_ref_known(v_host_3394_, 1);
v___x_3420_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3421_ = lean_uv_ntop_v6(v_ipv6_3419_);
lean_dec_ref(v_ipv6_3419_);
v___x_3422_ = lean_string_append(v___x_3420_, v___x_3421_);
lean_dec_ref(v___x_3421_);
v___x_3423_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3424_ = lean_string_append(v___x_3422_, v___x_3423_);
v___y_3405_ = v___y_3415_;
v___y_3406_ = v___x_3424_;
goto v___jp_3404_;
}
}
}
}
v___jp_3357_:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3362_ = lean_string_append(v___y_3359_, v___y_3360_);
lean_dec_ref(v___y_3360_);
v___x_3363_ = lean_string_append(v___x_3362_, v___y_3358_);
lean_dec_ref(v___y_3358_);
v___x_3364_ = lean_string_append(v___x_3363_, v___y_3361_);
lean_dec_ref(v___y_3361_);
return v___x_3364_;
}
v___jp_3369_:
{
lean_object* v_queryPart_3372_; 
v_queryPart_3372_ = l_Std_Http_URI_Query_formatOption(v_query_3367_);
if (lean_obj_tag(v_fragment_3368_) == 0)
{
lean_object* v___x_3373_; 
v___x_3373_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3358_ = v_queryPart_3372_;
v___y_3359_ = v___y_3370_;
v___y_3360_ = v___y_3371_;
v___y_3361_ = v___x_3373_;
goto v___jp_3357_;
}
else
{
lean_object* v_val_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_val_3374_ = lean_ctor_get(v_fragment_3368_, 0);
lean_inc(v_val_3374_);
lean_dec_ref_known(v_fragment_3368_, 1);
v___x_3375_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3376_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3374_);
lean_dec(v_val_3374_);
v___x_3377_ = lean_string_from_utf8_unchecked(v___x_3376_);
v___x_3378_ = lean_string_append(v___x_3375_, v___x_3377_);
lean_dec_ref(v___x_3377_);
v___y_3358_ = v_queryPart_3372_;
v___y_3359_ = v___y_3370_;
v___y_3360_ = v___y_3371_;
v___y_3361_ = v___x_3378_;
goto v___jp_3357_;
}
}
v___jp_3379_:
{
lean_object* v_segments_3381_; uint8_t v_absolute_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; size_t v_sz_3385_; size_t v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v_result_3389_; 
v_segments_3381_ = lean_ctor_get(v_path_3366_, 0);
lean_inc_ref(v_segments_3381_);
v_absolute_3382_ = lean_ctor_get_uint8(v_path_3366_, sizeof(void*)*1);
lean_dec_ref(v_path_3366_);
v___x_3383_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3384_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3385_ = lean_array_size(v_segments_3381_);
v___x_3386_ = ((size_t)0ULL);
v___x_3387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3384_, v___f_3355_, v_sz_3385_, v___x_3386_, v_segments_3381_);
v___x_3388_ = lean_array_to_list(v___x_3387_);
v_result_3389_ = l_String_intercalate(v___x_3383_, v___x_3388_);
if (v_absolute_3382_ == 0)
{
v___y_3370_ = v___y_3380_;
v___y_3371_ = v_result_3389_;
goto v___jp_3369_;
}
else
{
lean_object* v___x_3390_; 
v___x_3390_ = lean_string_append(v___x_3383_, v_result_3389_);
lean_dec_ref(v_result_3389_);
v___y_3370_ = v___y_3380_;
v___y_3371_ = v___x_3390_;
goto v___jp_3369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx(lean_object* v_x_3444_){
_start:
{
if (lean_obj_tag(v_x_3444_) == 0)
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_unsigned_to_nat(0u);
return v___x_3445_;
}
else
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_unsigned_to_nat(1u);
return v___x_3446_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorIdx___boxed(lean_object* v_x_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Std_Http_URIReference_ctorIdx(v_x_3447_);
lean_dec_ref(v_x_3447_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___redArg(lean_object* v_t_3449_, lean_object* v_k_3450_){
_start:
{
lean_object* v_uri_3451_; lean_object* v___x_3452_; 
v_uri_3451_ = lean_ctor_get(v_t_3449_, 0);
lean_inc_ref(v_uri_3451_);
lean_dec_ref(v_t_3449_);
v___x_3452_ = lean_apply_1(v_k_3450_, v_uri_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim(lean_object* v_motive_3453_, lean_object* v_ctorIdx_3454_, lean_object* v_t_3455_, lean_object* v_h_3456_, lean_object* v_k_3457_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3455_, v_k_3457_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_ctorElim___boxed(lean_object* v_motive_3459_, lean_object* v_ctorIdx_3460_, lean_object* v_t_3461_, lean_object* v_h_3462_, lean_object* v_k_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Std_Http_URIReference_ctorElim(v_motive_3459_, v_ctorIdx_3460_, v_t_3461_, v_h_3462_, v_k_3463_);
lean_dec(v_ctorIdx_3460_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim___redArg(lean_object* v_t_3465_, lean_object* v_absolute_3466_){
_start:
{
lean_object* v___x_3467_; 
v___x_3467_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3465_, v_absolute_3466_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_absolute_elim(lean_object* v_motive_3468_, lean_object* v_t_3469_, lean_object* v_h_3470_, lean_object* v_absolute_3471_){
_start:
{
lean_object* v___x_3472_; 
v___x_3472_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3469_, v_absolute_3471_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim___redArg(lean_object* v_t_3473_, lean_object* v_relative_3474_){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3473_, v_relative_3474_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_relative_elim(lean_object* v_motive_3476_, lean_object* v_t_3477_, lean_object* v_h_3478_, lean_object* v_relative_3479_){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = l_Std_Http_URIReference_ctorElim___redArg(v_t_3477_, v_relative_3479_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr(lean_object* v_x_3493_, lean_object* v_prec_3494_){
_start:
{
if (lean_obj_tag(v_x_3493_) == 0)
{
lean_object* v_uri_3495_; lean_object* v___y_3497_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v_uri_3495_ = lean_ctor_get(v_x_3493_, 0);
lean_inc_ref(v_uri_3495_);
lean_dec_ref_known(v_x_3493_, 1);
v___x_3505_ = lean_unsigned_to_nat(1024u);
v___x_3506_ = lean_nat_dec_le(v___x_3505_, v_prec_3494_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3507_; 
v___x_3507_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3497_ = v___x_3507_;
goto v___jp_3496_;
}
else
{
lean_object* v___x_3508_; 
v___x_3508_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3497_ = v___x_3508_;
goto v___jp_3496_;
}
v___jp_3496_:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3498_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__2));
v___x_3499_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3495_);
v___x_3500_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3498_);
lean_ctor_set(v___x_3500_, 1, v___x_3499_);
lean_inc(v___y_3497_);
v___x_3501_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___y_3497_);
lean_ctor_set(v___x_3501_, 1, v___x_3500_);
v___x_3502_ = 0;
v___x_3503_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3503_, 0, v___x_3501_);
lean_ctor_set_uint8(v___x_3503_, sizeof(void*)*1, v___x_3502_);
v___x_3504_ = l_Repr_addAppParen(v___x_3503_, v_prec_3494_);
return v___x_3504_;
}
}
else
{
lean_object* v_ref_3509_; lean_object* v___y_3511_; lean_object* v___x_3519_; uint8_t v___x_3520_; 
v_ref_3509_ = lean_ctor_get(v_x_3493_, 0);
lean_inc_ref(v_ref_3509_);
lean_dec_ref_known(v_x_3493_, 1);
v___x_3519_ = lean_unsigned_to_nat(1024u);
v___x_3520_ = lean_nat_dec_le(v___x_3519_, v_prec_3494_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; 
v___x_3521_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3511_ = v___x_3521_;
goto v___jp_3510_;
}
else
{
lean_object* v___x_3522_; 
v___x_3522_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3511_ = v___x_3522_;
goto v___jp_3510_;
}
v___jp_3510_:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3512_ = ((lean_object*)(l_Std_Http_instReprURIReference_repr___closed__5));
v___x_3513_ = l_Std_Http_URI_instReprRelativeRef_repr___redArg(v_ref_3509_);
v___x_3514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3512_);
lean_ctor_set(v___x_3514_, 1, v___x_3513_);
lean_inc(v___y_3511_);
v___x_3515_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3515_, 0, v___y_3511_);
lean_ctor_set(v___x_3515_, 1, v___x_3514_);
v___x_3516_ = 0;
v___x_3517_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3517_, 0, v___x_3515_);
lean_ctor_set_uint8(v___x_3517_, sizeof(void*)*1, v___x_3516_);
v___x_3518_ = l_Repr_addAppParen(v___x_3517_, v_prec_3494_);
return v___x_3518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURIReference_repr___boxed(lean_object* v_x_3523_, lean_object* v_prec_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l_Std_Http_instReprURIReference_repr(v_x_3523_, v_prec_3524_);
lean_dec(v_prec_3524_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURIReference___lam__2(lean_object* v___f_3532_, lean_object* v___f_3533_, lean_object* v_x_3534_){
_start:
{
lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; 
if (lean_obj_tag(v_x_3534_) == 0)
{
lean_object* v_uri_3543_; lean_object* v_scheme_3544_; lean_object* v_authority_3545_; lean_object* v_path_3546_; lean_object* v_query_3547_; lean_object* v_fragment_3548_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3571_; 
lean_dec_ref(v___f_3533_);
v_uri_3543_ = lean_ctor_get(v_x_3534_, 0);
lean_inc_ref(v_uri_3543_);
lean_dec_ref_known(v_x_3534_, 1);
v_scheme_3544_ = lean_ctor_get(v_uri_3543_, 0);
lean_inc_ref(v_scheme_3544_);
v_authority_3545_ = lean_ctor_get(v_uri_3543_, 1);
lean_inc(v_authority_3545_);
v_path_3546_ = lean_ctor_get(v_uri_3543_, 2);
lean_inc_ref(v_path_3546_);
v_query_3547_ = lean_ctor_get(v_uri_3543_, 3);
lean_inc(v_query_3547_);
v_fragment_3548_ = lean_ctor_get(v_uri_3543_, 4);
lean_inc(v_fragment_3548_);
lean_dec_ref(v_uri_3543_);
if (lean_obj_tag(v_authority_3545_) == 0)
{
lean_object* v___x_3582_; 
v___x_3582_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3571_ = v___x_3582_;
goto v___jp_3570_;
}
else
{
lean_object* v_val_3583_; lean_object* v_userInfo_3584_; lean_object* v_host_3585_; lean_object* v_port_3586_; lean_object* v___x_3587_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3606_; 
v_val_3583_ = lean_ctor_get(v_authority_3545_, 0);
lean_inc(v_val_3583_);
lean_dec_ref_known(v_authority_3545_, 1);
v_userInfo_3584_ = lean_ctor_get(v_val_3583_, 0);
lean_inc(v_userInfo_3584_);
v_host_3585_ = lean_ctor_get(v_val_3583_, 1);
lean_inc_ref(v_host_3585_);
v_port_3586_ = lean_ctor_get(v_val_3583_, 2);
lean_inc(v_port_3586_);
lean_dec(v_val_3583_);
v___x_3587_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3584_) == 0)
{
lean_object* v___x_3616_; 
v___x_3616_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3606_ = v___x_3616_;
goto v___jp_3605_;
}
else
{
lean_object* v_val_3617_; lean_object* v_password_3618_; 
v_val_3617_ = lean_ctor_get(v_userInfo_3584_, 0);
lean_inc(v_val_3617_);
lean_dec_ref_known(v_userInfo_3584_, 1);
v_password_3618_ = lean_ctor_get(v_val_3617_, 1);
if (lean_obj_tag(v_password_3618_) == 0)
{
lean_object* v_username_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v_username_3619_ = lean_ctor_get(v_val_3617_, 0);
lean_inc_ref(v_username_3619_);
lean_dec(v_val_3617_);
v___x_3620_ = lean_string_from_utf8_unchecked(v_username_3619_);
v___x_3621_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3622_ = lean_string_append(v___x_3620_, v___x_3621_);
v___y_3606_ = v___x_3622_;
goto v___jp_3605_;
}
else
{
lean_object* v_username_3623_; lean_object* v_val_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
lean_inc_ref(v_password_3618_);
v_username_3623_ = lean_ctor_get(v_val_3617_, 0);
lean_inc_ref(v_username_3623_);
lean_dec(v_val_3617_);
v_val_3624_ = lean_ctor_get(v_password_3618_, 0);
lean_inc(v_val_3624_);
lean_dec_ref_known(v_password_3618_, 1);
v___x_3625_ = lean_string_from_utf8_unchecked(v_username_3623_);
v___x_3626_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3627_ = lean_string_append(v___x_3625_, v___x_3626_);
v___x_3628_ = lean_string_from_utf8_unchecked(v_val_3624_);
v___x_3629_ = lean_string_append(v___x_3627_, v___x_3628_);
lean_dec_ref(v___x_3628_);
v___x_3630_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3631_ = lean_string_append(v___x_3629_, v___x_3630_);
v___y_3606_ = v___x_3631_;
goto v___jp_3605_;
}
}
v___jp_3588_:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3592_ = lean_string_append(v___y_3589_, v___y_3590_);
lean_dec_ref(v___y_3590_);
v___x_3593_ = lean_string_append(v___x_3592_, v___y_3591_);
lean_dec_ref(v___y_3591_);
v___x_3594_ = lean_string_append(v___x_3587_, v___x_3593_);
lean_dec_ref(v___x_3593_);
v___y_3571_ = v___x_3594_;
goto v___jp_3570_;
}
v___jp_3595_:
{
switch(lean_obj_tag(v_port_3586_))
{
case 0:
{
lean_object* v___x_3598_; 
v___x_3598_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3589_ = v___y_3596_;
v___y_3590_ = v___y_3597_;
v___y_3591_ = v___x_3598_;
goto v___jp_3588_;
}
case 1:
{
lean_object* v___x_3599_; 
v___x_3599_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3589_ = v___y_3596_;
v___y_3590_ = v___y_3597_;
v___y_3591_ = v___x_3599_;
goto v___jp_3588_;
}
default: 
{
uint16_t v_port_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v_port_3600_ = lean_ctor_get_uint16(v_port_3586_, 0);
lean_dec_ref_known(v_port_3586_, 0);
v___x_3601_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3602_ = lean_uint16_to_nat(v_port_3600_);
v___x_3603_ = l_Nat_reprFast(v___x_3602_);
v___x_3604_ = lean_string_append(v___x_3601_, v___x_3603_);
lean_dec_ref(v___x_3603_);
v___y_3589_ = v___y_3596_;
v___y_3590_ = v___y_3597_;
v___y_3591_ = v___x_3604_;
goto v___jp_3588_;
}
}
}
v___jp_3605_:
{
switch(lean_obj_tag(v_host_3585_))
{
case 0:
{
lean_object* v_name_3607_; 
v_name_3607_ = lean_ctor_get(v_host_3585_, 0);
lean_inc_ref(v_name_3607_);
lean_dec_ref_known(v_host_3585_, 1);
v___y_3596_ = v___y_3606_;
v___y_3597_ = v_name_3607_;
goto v___jp_3595_;
}
case 1:
{
lean_object* v_ipv4_3608_; lean_object* v___x_3609_; 
v_ipv4_3608_ = lean_ctor_get(v_host_3585_, 0);
lean_inc_ref(v_ipv4_3608_);
lean_dec_ref_known(v_host_3585_, 1);
v___x_3609_ = lean_uv_ntop_v4(v_ipv4_3608_);
lean_dec_ref(v_ipv4_3608_);
v___y_3596_ = v___y_3606_;
v___y_3597_ = v___x_3609_;
goto v___jp_3595_;
}
default: 
{
lean_object* v_ipv6_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v_ipv6_3610_ = lean_ctor_get(v_host_3585_, 0);
lean_inc_ref(v_ipv6_3610_);
lean_dec_ref_known(v_host_3585_, 1);
v___x_3611_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3612_ = lean_uv_ntop_v6(v_ipv6_3610_);
lean_dec_ref(v_ipv6_3610_);
v___x_3613_ = lean_string_append(v___x_3611_, v___x_3612_);
lean_dec_ref(v___x_3612_);
v___x_3614_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3615_ = lean_string_append(v___x_3613_, v___x_3614_);
v___y_3596_ = v___y_3606_;
v___y_3597_ = v___x_3615_;
goto v___jp_3595_;
}
}
}
}
v___jp_3549_:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3554_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3555_ = lean_string_append(v_scheme_3544_, v___x_3554_);
v___x_3556_ = lean_string_append(v___x_3555_, v___y_3551_);
lean_dec_ref(v___y_3551_);
v___x_3557_ = lean_string_append(v___x_3556_, v___y_3550_);
lean_dec_ref(v___y_3550_);
v___x_3558_ = lean_string_append(v___x_3557_, v___y_3552_);
lean_dec_ref(v___y_3552_);
v___x_3559_ = lean_string_append(v___x_3558_, v___y_3553_);
lean_dec_ref(v___y_3553_);
return v___x_3559_;
}
v___jp_3560_:
{
lean_object* v_queryPart_3563_; 
v_queryPart_3563_ = l_Std_Http_URI_Query_formatOption(v_query_3547_);
if (lean_obj_tag(v_fragment_3548_) == 0)
{
lean_object* v___x_3564_; 
v___x_3564_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3550_ = v___y_3562_;
v___y_3551_ = v___y_3561_;
v___y_3552_ = v_queryPart_3563_;
v___y_3553_ = v___x_3564_;
goto v___jp_3549_;
}
else
{
lean_object* v_val_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v_val_3565_ = lean_ctor_get(v_fragment_3548_, 0);
lean_inc(v_val_3565_);
lean_dec_ref_known(v_fragment_3548_, 1);
v___x_3566_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3567_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3565_);
lean_dec(v_val_3565_);
v___x_3568_ = lean_string_from_utf8_unchecked(v___x_3567_);
v___x_3569_ = lean_string_append(v___x_3566_, v___x_3568_);
lean_dec_ref(v___x_3568_);
v___y_3550_ = v___y_3562_;
v___y_3551_ = v___y_3561_;
v___y_3552_ = v_queryPart_3563_;
v___y_3553_ = v___x_3569_;
goto v___jp_3549_;
}
}
v___jp_3570_:
{
lean_object* v_segments_3572_; uint8_t v_absolute_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; size_t v_sz_3576_; size_t v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v_result_3580_; 
v_segments_3572_ = lean_ctor_get(v_path_3546_, 0);
lean_inc_ref(v_segments_3572_);
v_absolute_3573_ = lean_ctor_get_uint8(v_path_3546_, sizeof(void*)*1);
lean_dec_ref(v_path_3546_);
v___x_3574_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3575_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3576_ = lean_array_size(v_segments_3572_);
v___x_3577_ = ((size_t)0ULL);
v___x_3578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3575_, v___f_3532_, v_sz_3576_, v___x_3577_, v_segments_3572_);
v___x_3579_ = lean_array_to_list(v___x_3578_);
v_result_3580_ = l_String_intercalate(v___x_3574_, v___x_3579_);
if (v_absolute_3573_ == 0)
{
v___y_3561_ = v___y_3571_;
v___y_3562_ = v_result_3580_;
goto v___jp_3560_;
}
else
{
lean_object* v___x_3581_; 
v___x_3581_ = lean_string_append(v___x_3574_, v_result_3580_);
lean_dec_ref(v_result_3580_);
v___y_3561_ = v___y_3571_;
v___y_3562_ = v___x_3581_;
goto v___jp_3560_;
}
}
}
else
{
lean_object* v_ref_3632_; lean_object* v_authority_3633_; lean_object* v_path_3634_; lean_object* v_query_3635_; lean_object* v_fragment_3636_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3648_; 
lean_dec_ref(v___f_3532_);
v_ref_3632_ = lean_ctor_get(v_x_3534_, 0);
lean_inc_ref(v_ref_3632_);
lean_dec_ref_known(v_x_3534_, 1);
v_authority_3633_ = lean_ctor_get(v_ref_3632_, 0);
lean_inc(v_authority_3633_);
v_path_3634_ = lean_ctor_get(v_ref_3632_, 1);
lean_inc_ref(v_path_3634_);
v_query_3635_ = lean_ctor_get(v_ref_3632_, 2);
lean_inc(v_query_3635_);
v_fragment_3636_ = lean_ctor_get(v_ref_3632_, 3);
lean_inc(v_fragment_3636_);
lean_dec_ref(v_ref_3632_);
if (lean_obj_tag(v_authority_3633_) == 0)
{
lean_object* v___x_3659_; 
v___x_3659_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3648_ = v___x_3659_;
goto v___jp_3647_;
}
else
{
lean_object* v_val_3660_; lean_object* v_userInfo_3661_; lean_object* v_host_3662_; lean_object* v_port_3663_; lean_object* v___x_3664_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3683_; 
v_val_3660_ = lean_ctor_get(v_authority_3633_, 0);
lean_inc(v_val_3660_);
lean_dec_ref_known(v_authority_3633_, 1);
v_userInfo_3661_ = lean_ctor_get(v_val_3660_, 0);
lean_inc(v_userInfo_3661_);
v_host_3662_ = lean_ctor_get(v_val_3660_, 1);
lean_inc_ref(v_host_3662_);
v_port_3663_ = lean_ctor_get(v_val_3660_, 2);
lean_inc(v_port_3663_);
lean_dec(v_val_3660_);
v___x_3664_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3661_) == 0)
{
lean_object* v___x_3693_; 
v___x_3693_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3683_ = v___x_3693_;
goto v___jp_3682_;
}
else
{
lean_object* v_val_3694_; lean_object* v_password_3695_; 
v_val_3694_ = lean_ctor_get(v_userInfo_3661_, 0);
lean_inc(v_val_3694_);
lean_dec_ref_known(v_userInfo_3661_, 1);
v_password_3695_ = lean_ctor_get(v_val_3694_, 1);
if (lean_obj_tag(v_password_3695_) == 0)
{
lean_object* v_username_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v_username_3696_ = lean_ctor_get(v_val_3694_, 0);
lean_inc_ref(v_username_3696_);
lean_dec(v_val_3694_);
v___x_3697_ = lean_string_from_utf8_unchecked(v_username_3696_);
v___x_3698_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3699_ = lean_string_append(v___x_3697_, v___x_3698_);
v___y_3683_ = v___x_3699_;
goto v___jp_3682_;
}
else
{
lean_object* v_username_3700_; lean_object* v_val_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
lean_inc_ref(v_password_3695_);
v_username_3700_ = lean_ctor_get(v_val_3694_, 0);
lean_inc_ref(v_username_3700_);
lean_dec(v_val_3694_);
v_val_3701_ = lean_ctor_get(v_password_3695_, 0);
lean_inc(v_val_3701_);
lean_dec_ref_known(v_password_3695_, 1);
v___x_3702_ = lean_string_from_utf8_unchecked(v_username_3700_);
v___x_3703_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3704_ = lean_string_append(v___x_3702_, v___x_3703_);
v___x_3705_ = lean_string_from_utf8_unchecked(v_val_3701_);
v___x_3706_ = lean_string_append(v___x_3704_, v___x_3705_);
lean_dec_ref(v___x_3705_);
v___x_3707_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3708_ = lean_string_append(v___x_3706_, v___x_3707_);
v___y_3683_ = v___x_3708_;
goto v___jp_3682_;
}
}
v___jp_3665_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3669_ = lean_string_append(v___y_3667_, v___y_3666_);
lean_dec_ref(v___y_3666_);
v___x_3670_ = lean_string_append(v___x_3669_, v___y_3668_);
lean_dec_ref(v___y_3668_);
v___x_3671_ = lean_string_append(v___x_3664_, v___x_3670_);
lean_dec_ref(v___x_3670_);
v___y_3648_ = v___x_3671_;
goto v___jp_3647_;
}
v___jp_3672_:
{
switch(lean_obj_tag(v_port_3663_))
{
case 0:
{
lean_object* v___x_3675_; 
v___x_3675_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3666_ = v___y_3674_;
v___y_3667_ = v___y_3673_;
v___y_3668_ = v___x_3675_;
goto v___jp_3665_;
}
case 1:
{
lean_object* v___x_3676_; 
v___x_3676_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3666_ = v___y_3674_;
v___y_3667_ = v___y_3673_;
v___y_3668_ = v___x_3676_;
goto v___jp_3665_;
}
default: 
{
uint16_t v_port_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v_port_3677_ = lean_ctor_get_uint16(v_port_3663_, 0);
lean_dec_ref_known(v_port_3663_, 0);
v___x_3678_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3679_ = lean_uint16_to_nat(v_port_3677_);
v___x_3680_ = l_Nat_reprFast(v___x_3679_);
v___x_3681_ = lean_string_append(v___x_3678_, v___x_3680_);
lean_dec_ref(v___x_3680_);
v___y_3666_ = v___y_3674_;
v___y_3667_ = v___y_3673_;
v___y_3668_ = v___x_3681_;
goto v___jp_3665_;
}
}
}
v___jp_3682_:
{
switch(lean_obj_tag(v_host_3662_))
{
case 0:
{
lean_object* v_name_3684_; 
v_name_3684_ = lean_ctor_get(v_host_3662_, 0);
lean_inc_ref(v_name_3684_);
lean_dec_ref_known(v_host_3662_, 1);
v___y_3673_ = v___y_3683_;
v___y_3674_ = v_name_3684_;
goto v___jp_3672_;
}
case 1:
{
lean_object* v_ipv4_3685_; lean_object* v___x_3686_; 
v_ipv4_3685_ = lean_ctor_get(v_host_3662_, 0);
lean_inc_ref(v_ipv4_3685_);
lean_dec_ref_known(v_host_3662_, 1);
v___x_3686_ = lean_uv_ntop_v4(v_ipv4_3685_);
lean_dec_ref(v_ipv4_3685_);
v___y_3673_ = v___y_3683_;
v___y_3674_ = v___x_3686_;
goto v___jp_3672_;
}
default: 
{
lean_object* v_ipv6_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v_ipv6_3687_ = lean_ctor_get(v_host_3662_, 0);
lean_inc_ref(v_ipv6_3687_);
lean_dec_ref_known(v_host_3662_, 1);
v___x_3688_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3689_ = lean_uv_ntop_v6(v_ipv6_3687_);
lean_dec_ref(v_ipv6_3687_);
v___x_3690_ = lean_string_append(v___x_3688_, v___x_3689_);
lean_dec_ref(v___x_3689_);
v___x_3691_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3692_ = lean_string_append(v___x_3690_, v___x_3691_);
v___y_3673_ = v___y_3683_;
v___y_3674_ = v___x_3692_;
goto v___jp_3672_;
}
}
}
}
v___jp_3637_:
{
lean_object* v_queryPart_3640_; 
v_queryPart_3640_ = l_Std_Http_URI_Query_formatOption(v_query_3635_);
if (lean_obj_tag(v_fragment_3636_) == 0)
{
lean_object* v___x_3641_; 
v___x_3641_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3536_ = v___y_3639_;
v___y_3537_ = v___y_3638_;
v___y_3538_ = v_queryPart_3640_;
v___y_3539_ = v___x_3641_;
goto v___jp_3535_;
}
else
{
lean_object* v_val_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v_val_3642_ = lean_ctor_get(v_fragment_3636_, 0);
lean_inc(v_val_3642_);
lean_dec_ref_known(v_fragment_3636_, 1);
v___x_3643_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3644_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3642_);
lean_dec(v_val_3642_);
v___x_3645_ = lean_string_from_utf8_unchecked(v___x_3644_);
v___x_3646_ = lean_string_append(v___x_3643_, v___x_3645_);
lean_dec_ref(v___x_3645_);
v___y_3536_ = v___y_3639_;
v___y_3537_ = v___y_3638_;
v___y_3538_ = v_queryPart_3640_;
v___y_3539_ = v___x_3646_;
goto v___jp_3535_;
}
}
v___jp_3647_:
{
lean_object* v_segments_3649_; uint8_t v_absolute_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; size_t v_sz_3653_; size_t v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v_result_3657_; 
v_segments_3649_ = lean_ctor_get(v_path_3634_, 0);
lean_inc_ref(v_segments_3649_);
v_absolute_3650_ = lean_ctor_get_uint8(v_path_3634_, sizeof(void*)*1);
lean_dec_ref(v_path_3634_);
v___x_3651_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3652_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3653_ = lean_array_size(v_segments_3649_);
v___x_3654_ = ((size_t)0ULL);
v___x_3655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3652_, v___f_3533_, v_sz_3653_, v___x_3654_, v_segments_3649_);
v___x_3656_ = lean_array_to_list(v___x_3655_);
v_result_3657_ = l_String_intercalate(v___x_3651_, v___x_3656_);
if (v_absolute_3650_ == 0)
{
v___y_3638_ = v___y_3648_;
v___y_3639_ = v_result_3657_;
goto v___jp_3637_;
}
else
{
lean_object* v___x_3658_; 
v___x_3658_ = lean_string_append(v___x_3651_, v_result_3657_);
lean_dec_ref(v_result_3657_);
v___y_3638_ = v___y_3648_;
v___y_3639_ = v___x_3658_;
goto v___jp_3637_;
}
}
}
v___jp_3535_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3540_ = lean_string_append(v___y_3537_, v___y_3536_);
lean_dec_ref(v___y_3536_);
v___x_3541_ = lean_string_append(v___x_3540_, v___y_3538_);
lean_dec_ref(v___y_3538_);
v___x_3542_ = lean_string_append(v___x_3541_, v___y_3539_);
lean_dec_ref(v___y_3539_);
return v___x_3542_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx(lean_object* v_x_3712_){
_start:
{
switch(lean_obj_tag(v_x_3712_))
{
case 0:
{
lean_object* v___x_3713_; 
v___x_3713_ = lean_unsigned_to_nat(0u);
return v___x_3713_;
}
case 1:
{
lean_object* v___x_3714_; 
v___x_3714_ = lean_unsigned_to_nat(1u);
return v___x_3714_;
}
case 2:
{
lean_object* v___x_3715_; 
v___x_3715_ = lean_unsigned_to_nat(2u);
return v___x_3715_;
}
default: 
{
lean_object* v___x_3716_; 
v___x_3716_ = lean_unsigned_to_nat(3u);
return v___x_3716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___boxed(lean_object* v_x_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Std_Http_RequestTarget_ctorIdx(v_x_3717_);
lean_dec(v_x_3717_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___redArg(lean_object* v_t_3719_, lean_object* v_k_3720_){
_start:
{
switch(lean_obj_tag(v_t_3719_))
{
case 0:
{
lean_object* v_path_3721_; lean_object* v_query_3722_; lean_object* v___x_3723_; 
v_path_3721_ = lean_ctor_get(v_t_3719_, 0);
lean_inc_ref(v_path_3721_);
v_query_3722_ = lean_ctor_get(v_t_3719_, 1);
lean_inc(v_query_3722_);
lean_dec_ref_known(v_t_3719_, 2);
v___x_3723_ = lean_apply_2(v_k_3720_, v_path_3721_, v_query_3722_);
return v___x_3723_;
}
case 3:
{
return v_k_3720_;
}
default: 
{
lean_object* v_uri_3724_; lean_object* v___x_3725_; 
v_uri_3724_ = lean_ctor_get(v_t_3719_, 0);
lean_inc_ref(v_uri_3724_);
lean_dec(v_t_3719_);
v___x_3725_ = lean_apply_1(v_k_3720_, v_uri_3724_);
return v___x_3725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim(lean_object* v_motive_3726_, lean_object* v_ctorIdx_3727_, lean_object* v_t_3728_, lean_object* v_h_3729_, lean_object* v_k_3730_){
_start:
{
lean_object* v___x_3731_; 
v___x_3731_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3728_, v_k_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___boxed(lean_object* v_motive_3732_, lean_object* v_ctorIdx_3733_, lean_object* v_t_3734_, lean_object* v_h_3735_, lean_object* v_k_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Std_Http_RequestTarget_ctorElim(v_motive_3732_, v_ctorIdx_3733_, v_t_3734_, v_h_3735_, v_k_3736_);
lean_dec(v_ctorIdx_3733_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim___redArg(lean_object* v_t_3738_, lean_object* v_originForm_3739_){
_start:
{
lean_object* v___x_3740_; 
v___x_3740_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3738_, v_originForm_3739_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim(lean_object* v_motive_3741_, lean_object* v_t_3742_, lean_object* v_h_3743_, lean_object* v_originForm_3744_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3742_, v_originForm_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim___redArg(lean_object* v_t_3746_, lean_object* v_absoluteForm_3747_){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3746_, v_absoluteForm_3747_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim(lean_object* v_motive_3749_, lean_object* v_t_3750_, lean_object* v_h_3751_, lean_object* v_absoluteForm_3752_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3750_, v_absoluteForm_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim___redArg(lean_object* v_t_3754_, lean_object* v_authorityForm_3755_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3754_, v_authorityForm_3755_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim(lean_object* v_motive_3757_, lean_object* v_t_3758_, lean_object* v_h_3759_, lean_object* v_authorityForm_3760_){
_start:
{
lean_object* v___x_3761_; 
v___x_3761_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3758_, v_authorityForm_3760_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim___redArg(lean_object* v_t_3762_, lean_object* v_asteriskForm_3763_){
_start:
{
lean_object* v___x_3764_; 
v___x_3764_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3762_, v_asteriskForm_3763_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim(lean_object* v_motive_3765_, lean_object* v_t_3766_, lean_object* v_h_3767_, lean_object* v_asteriskForm_3768_){
_start:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_3766_, v_asteriskForm_3768_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object* v_x_3796_, lean_object* v_prec_3797_){
_start:
{
lean_object* v___y_3799_; 
switch(lean_obj_tag(v_x_3796_))
{
case 0:
{
lean_object* v_path_3805_; lean_object* v_query_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3830_; 
v_path_3805_ = lean_ctor_get(v_x_3796_, 0);
v_query_3806_ = lean_ctor_get(v_x_3796_, 1);
v_isSharedCheck_3830_ = !lean_is_exclusive(v_x_3796_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3808_ = v_x_3796_;
v_isShared_3809_ = v_isSharedCheck_3830_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_query_3806_);
lean_inc(v_path_3805_);
lean_dec(v_x_3796_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3830_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___y_3811_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v___x_3826_ = lean_unsigned_to_nat(1024u);
v___x_3827_ = lean_nat_dec_le(v___x_3826_, v_prec_3797_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3811_ = v___x_3828_;
goto v___jp_3810_;
}
else
{
lean_object* v___x_3829_; 
v___x_3829_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3811_ = v___x_3829_;
goto v___jp_3810_;
}
v___jp_3810_:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3817_; 
v___x_3812_ = lean_box(1);
v___x_3813_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__4));
v___x_3814_ = lean_unsigned_to_nat(1024u);
v___x_3815_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_3805_);
if (v_isShared_3809_ == 0)
{
lean_ctor_set_tag(v___x_3808_, 5);
lean_ctor_set(v___x_3808_, 1, v___x_3815_);
lean_ctor_set(v___x_3808_, 0, v___x_3813_);
v___x_3817_ = v___x_3808_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3813_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v___x_3815_);
v___x_3817_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3817_);
lean_ctor_set(v___x_3818_, 1, v___x_3812_);
v___x_3819_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_3806_, v___x_3814_);
v___x_3820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3818_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
lean_inc(v___y_3811_);
v___x_3821_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___y_3811_);
lean_ctor_set(v___x_3821_, 1, v___x_3820_);
v___x_3822_ = 0;
v___x_3823_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3823_, 0, v___x_3821_);
lean_ctor_set_uint8(v___x_3823_, sizeof(void*)*1, v___x_3822_);
v___x_3824_ = l_Repr_addAppParen(v___x_3823_, v_prec_3797_);
return v___x_3824_;
}
}
}
}
case 1:
{
lean_object* v_uri_3831_; lean_object* v___y_3833_; lean_object* v___x_3841_; uint8_t v___x_3842_; 
v_uri_3831_ = lean_ctor_get(v_x_3796_, 0);
lean_inc_ref(v_uri_3831_);
lean_dec_ref_known(v_x_3796_, 1);
v___x_3841_ = lean_unsigned_to_nat(1024u);
v___x_3842_ = lean_nat_dec_le(v___x_3841_, v_prec_3797_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3843_; 
v___x_3843_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3833_ = v___x_3843_;
goto v___jp_3832_;
}
else
{
lean_object* v___x_3844_; 
v___x_3844_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3833_ = v___x_3844_;
goto v___jp_3832_;
}
v___jp_3832_:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3834_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__7));
v___x_3835_ = l_Std_Http_instReprURI_repr___redArg(v_uri_3831_);
v___x_3836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3834_);
lean_ctor_set(v___x_3836_, 1, v___x_3835_);
lean_inc(v___y_3833_);
v___x_3837_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3837_, 0, v___y_3833_);
lean_ctor_set(v___x_3837_, 1, v___x_3836_);
v___x_3838_ = 0;
v___x_3839_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3839_, 0, v___x_3837_);
lean_ctor_set_uint8(v___x_3839_, sizeof(void*)*1, v___x_3838_);
v___x_3840_ = l_Repr_addAppParen(v___x_3839_, v_prec_3797_);
return v___x_3840_;
}
}
case 2:
{
lean_object* v_authority_3845_; lean_object* v___y_3847_; lean_object* v___x_3855_; uint8_t v___x_3856_; 
v_authority_3845_ = lean_ctor_get(v_x_3796_, 0);
lean_inc_ref(v_authority_3845_);
lean_dec_ref_known(v_x_3796_, 1);
v___x_3855_ = lean_unsigned_to_nat(1024u);
v___x_3856_ = lean_nat_dec_le(v___x_3855_, v_prec_3797_);
if (v___x_3856_ == 0)
{
lean_object* v___x_3857_; 
v___x_3857_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3847_ = v___x_3857_;
goto v___jp_3846_;
}
else
{
lean_object* v___x_3858_; 
v___x_3858_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3847_ = v___x_3858_;
goto v___jp_3846_;
}
v___jp_3846_:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3848_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__10));
v___x_3849_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_authority_3845_);
v___x_3850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3848_);
lean_ctor_set(v___x_3850_, 1, v___x_3849_);
lean_inc(v___y_3847_);
v___x_3851_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___y_3847_);
lean_ctor_set(v___x_3851_, 1, v___x_3850_);
v___x_3852_ = 0;
v___x_3853_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3853_, 0, v___x_3851_);
lean_ctor_set_uint8(v___x_3853_, sizeof(void*)*1, v___x_3852_);
v___x_3854_ = l_Repr_addAppParen(v___x_3853_, v_prec_3797_);
return v___x_3854_;
}
}
default: 
{
lean_object* v___x_3859_; uint8_t v___x_3860_; 
v___x_3859_ = lean_unsigned_to_nat(1024u);
v___x_3860_ = lean_nat_dec_le(v___x_3859_, v_prec_3797_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; 
v___x_3861_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_3799_ = v___x_3861_;
goto v___jp_3798_;
}
else
{
lean_object* v___x_3862_; 
v___x_3862_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_3799_ = v___x_3862_;
goto v___jp_3798_;
}
}
}
v___jp_3798_:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3800_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__1));
lean_inc(v___y_3799_);
v___x_3801_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___y_3799_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = 0;
v___x_3803_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3803_, 0, v___x_3801_);
lean_ctor_set_uint8(v___x_3803_, sizeof(void*)*1, v___x_3802_);
v___x_3804_ = l_Repr_addAppParen(v___x_3803_, v_prec_3797_);
return v___x_3804_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr___boxed(lean_object* v_x_3863_, lean_object* v_prec_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Std_Http_instReprRequestTarget_repr(v_x_3863_, v_prec_3864_);
lean_dec(v_prec_3864_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path(lean_object* v_x_3873_){
_start:
{
switch(lean_obj_tag(v_x_3873_))
{
case 0:
{
lean_object* v_path_3874_; 
v_path_3874_ = lean_ctor_get(v_x_3873_, 0);
lean_inc_ref(v_path_3874_);
return v_path_3874_;
}
case 1:
{
lean_object* v_uri_3875_; lean_object* v_path_3876_; 
v_uri_3875_ = lean_ctor_get(v_x_3873_, 0);
v_path_3876_ = lean_ctor_get(v_uri_3875_, 2);
lean_inc_ref(v_path_3876_);
return v_path_3876_;
}
default: 
{
lean_object* v___x_3877_; 
v___x_3877_ = ((lean_object*)(l_Std_Http_RequestTarget_path___closed__1));
return v___x_3877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path___boxed(lean_object* v_x_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_Std_Http_RequestTarget_path(v_x_3878_);
lean_dec(v_x_3878_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query(lean_object* v_x_3880_){
_start:
{
switch(lean_obj_tag(v_x_3880_))
{
case 0:
{
lean_object* v_query_3881_; 
v_query_3881_ = lean_ctor_get(v_x_3880_, 1);
if (lean_obj_tag(v_query_3881_) == 0)
{
lean_object* v___x_3882_; 
v___x_3882_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3882_;
}
else
{
lean_object* v_val_3883_; 
v_val_3883_ = lean_ctor_get(v_query_3881_, 0);
lean_inc(v_val_3883_);
return v_val_3883_;
}
}
case 1:
{
lean_object* v_uri_3884_; lean_object* v_query_3885_; 
v_uri_3884_ = lean_ctor_get(v_x_3880_, 0);
v_query_3885_ = lean_ctor_get(v_uri_3884_, 3);
if (lean_obj_tag(v_query_3885_) == 0)
{
lean_object* v___x_3886_; 
v___x_3886_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3886_;
}
else
{
lean_object* v_val_3887_; 
v_val_3887_ = lean_ctor_get(v_query_3885_, 0);
lean_inc(v_val_3887_);
return v_val_3887_;
}
}
default: 
{
lean_object* v___x_3888_; 
v___x_3888_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_3888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query___boxed(lean_object* v_x_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Std_Http_RequestTarget_query(v_x_3889_);
lean_dec(v_x_3889_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authority_x3f(lean_object* v_x_3891_){
_start:
{
switch(lean_obj_tag(v_x_3891_))
{
case 2:
{
lean_object* v_authority_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
v_authority_3892_ = lean_ctor_get(v_x_3891_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v_x_3891_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v_x_3891_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_authority_3892_);
lean_dec(v_x_3891_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
lean_ctor_set_tag(v___x_3894_, 1);
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_authority_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
case 1:
{
lean_object* v_uri_3900_; lean_object* v_authority_3901_; 
v_uri_3900_ = lean_ctor_get(v_x_3891_, 0);
lean_inc_ref(v_uri_3900_);
lean_dec_ref_known(v_x_3891_, 1);
v_authority_3901_ = lean_ctor_get(v_uri_3900_, 1);
lean_inc(v_authority_3901_);
lean_dec_ref(v_uri_3900_);
return v_authority_3901_;
}
default: 
{
lean_object* v___x_3902_; 
lean_dec(v_x_3891_);
v___x_3902_ = lean_box(0);
return v___x_3902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__2(lean_object* v___f_3904_, lean_object* v___f_3905_, lean_object* v_x_3906_){
_start:
{
lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; 
switch(lean_obj_tag(v_x_3906_))
{
case 0:
{
lean_object* v_path_3913_; lean_object* v_query_3914_; lean_object* v___y_3916_; lean_object* v_segments_3919_; uint8_t v_absolute_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; size_t v_sz_3923_; size_t v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v_result_3927_; 
lean_dec_ref(v___f_3905_);
v_path_3913_ = lean_ctor_get(v_x_3906_, 0);
lean_inc_ref(v_path_3913_);
v_query_3914_ = lean_ctor_get(v_x_3906_, 1);
lean_inc(v_query_3914_);
lean_dec_ref_known(v_x_3906_, 2);
v_segments_3919_ = lean_ctor_get(v_path_3913_, 0);
lean_inc_ref(v_segments_3919_);
v_absolute_3920_ = lean_ctor_get_uint8(v_path_3913_, sizeof(void*)*1);
lean_dec_ref(v_path_3913_);
v___x_3921_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3922_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3923_ = lean_array_size(v_segments_3919_);
v___x_3924_ = ((size_t)0ULL);
v___x_3925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3922_, v___f_3904_, v_sz_3923_, v___x_3924_, v_segments_3919_);
v___x_3926_ = lean_array_to_list(v___x_3925_);
v_result_3927_ = l_String_intercalate(v___x_3921_, v___x_3926_);
if (v_absolute_3920_ == 0)
{
v___y_3916_ = v_result_3927_;
goto v___jp_3915_;
}
else
{
lean_object* v___x_3928_; 
v___x_3928_ = lean_string_append(v___x_3921_, v_result_3927_);
lean_dec_ref(v_result_3927_);
v___y_3916_ = v___x_3928_;
goto v___jp_3915_;
}
v___jp_3915_:
{
lean_object* v_queryStr_3917_; lean_object* v___x_3918_; 
v_queryStr_3917_ = l_Std_Http_URI_Query_formatOption(v_query_3914_);
v___x_3918_ = lean_string_append(v___y_3916_, v_queryStr_3917_);
lean_dec_ref(v_queryStr_3917_);
return v___x_3918_;
}
}
case 1:
{
lean_object* v_uri_3929_; lean_object* v_scheme_3930_; lean_object* v_authority_3931_; lean_object* v_path_3932_; lean_object* v_query_3933_; lean_object* v_fragment_3934_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3957_; 
lean_dec_ref(v___f_3904_);
v_uri_3929_ = lean_ctor_get(v_x_3906_, 0);
lean_inc_ref(v_uri_3929_);
lean_dec_ref_known(v_x_3906_, 1);
v_scheme_3930_ = lean_ctor_get(v_uri_3929_, 0);
lean_inc_ref(v_scheme_3930_);
v_authority_3931_ = lean_ctor_get(v_uri_3929_, 1);
lean_inc(v_authority_3931_);
v_path_3932_ = lean_ctor_get(v_uri_3929_, 2);
lean_inc_ref(v_path_3932_);
v_query_3933_ = lean_ctor_get(v_uri_3929_, 3);
lean_inc(v_query_3933_);
v_fragment_3934_ = lean_ctor_get(v_uri_3929_, 4);
lean_inc(v_fragment_3934_);
lean_dec_ref(v_uri_3929_);
if (lean_obj_tag(v_authority_3931_) == 0)
{
lean_object* v___x_3968_; 
v___x_3968_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3957_ = v___x_3968_;
goto v___jp_3956_;
}
else
{
lean_object* v_val_3969_; lean_object* v_userInfo_3970_; lean_object* v_host_3971_; lean_object* v_port_3972_; lean_object* v___x_3973_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3992_; 
v_val_3969_ = lean_ctor_get(v_authority_3931_, 0);
lean_inc(v_val_3969_);
lean_dec_ref_known(v_authority_3931_, 1);
v_userInfo_3970_ = lean_ctor_get(v_val_3969_, 0);
lean_inc(v_userInfo_3970_);
v_host_3971_ = lean_ctor_get(v_val_3969_, 1);
lean_inc_ref(v_host_3971_);
v_port_3972_ = lean_ctor_get(v_val_3969_, 2);
lean_inc(v_port_3972_);
lean_dec(v_val_3969_);
v___x_3973_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_3970_) == 0)
{
lean_object* v___x_4002_; 
v___x_4002_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3992_ = v___x_4002_;
goto v___jp_3991_;
}
else
{
lean_object* v_val_4003_; lean_object* v_password_4004_; 
v_val_4003_ = lean_ctor_get(v_userInfo_3970_, 0);
lean_inc(v_val_4003_);
lean_dec_ref_known(v_userInfo_3970_, 1);
v_password_4004_ = lean_ctor_get(v_val_4003_, 1);
if (lean_obj_tag(v_password_4004_) == 0)
{
lean_object* v_username_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v_username_4005_ = lean_ctor_get(v_val_4003_, 0);
lean_inc_ref(v_username_4005_);
lean_dec(v_val_4003_);
v___x_4006_ = lean_string_from_utf8_unchecked(v_username_4005_);
v___x_4007_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4008_ = lean_string_append(v___x_4006_, v___x_4007_);
v___y_3992_ = v___x_4008_;
goto v___jp_3991_;
}
else
{
lean_object* v_username_4009_; lean_object* v_val_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
lean_inc_ref(v_password_4004_);
v_username_4009_ = lean_ctor_get(v_val_4003_, 0);
lean_inc_ref(v_username_4009_);
lean_dec(v_val_4003_);
v_val_4010_ = lean_ctor_get(v_password_4004_, 0);
lean_inc(v_val_4010_);
lean_dec_ref_known(v_password_4004_, 1);
v___x_4011_ = lean_string_from_utf8_unchecked(v_username_4009_);
v___x_4012_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4013_ = lean_string_append(v___x_4011_, v___x_4012_);
v___x_4014_ = lean_string_from_utf8_unchecked(v_val_4010_);
v___x_4015_ = lean_string_append(v___x_4013_, v___x_4014_);
lean_dec_ref(v___x_4014_);
v___x_4016_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4017_ = lean_string_append(v___x_4015_, v___x_4016_);
v___y_3992_ = v___x_4017_;
goto v___jp_3991_;
}
}
v___jp_3974_:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3978_ = lean_string_append(v___y_3975_, v___y_3976_);
lean_dec_ref(v___y_3976_);
v___x_3979_ = lean_string_append(v___x_3978_, v___y_3977_);
lean_dec_ref(v___y_3977_);
v___x_3980_ = lean_string_append(v___x_3973_, v___x_3979_);
lean_dec_ref(v___x_3979_);
v___y_3957_ = v___x_3980_;
goto v___jp_3956_;
}
v___jp_3981_:
{
switch(lean_obj_tag(v_port_3972_))
{
case 0:
{
lean_object* v___x_3984_; 
v___x_3984_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3975_ = v___y_3982_;
v___y_3976_ = v___y_3983_;
v___y_3977_ = v___x_3984_;
goto v___jp_3974_;
}
case 1:
{
lean_object* v___x_3985_; 
v___x_3985_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3975_ = v___y_3982_;
v___y_3976_ = v___y_3983_;
v___y_3977_ = v___x_3985_;
goto v___jp_3974_;
}
default: 
{
uint16_t v_port_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v_port_3986_ = lean_ctor_get_uint16(v_port_3972_, 0);
lean_dec_ref_known(v_port_3972_, 0);
v___x_3987_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3988_ = lean_uint16_to_nat(v_port_3986_);
v___x_3989_ = l_Nat_reprFast(v___x_3988_);
v___x_3990_ = lean_string_append(v___x_3987_, v___x_3989_);
lean_dec_ref(v___x_3989_);
v___y_3975_ = v___y_3982_;
v___y_3976_ = v___y_3983_;
v___y_3977_ = v___x_3990_;
goto v___jp_3974_;
}
}
}
v___jp_3991_:
{
switch(lean_obj_tag(v_host_3971_))
{
case 0:
{
lean_object* v_name_3993_; 
v_name_3993_ = lean_ctor_get(v_host_3971_, 0);
lean_inc_ref(v_name_3993_);
lean_dec_ref_known(v_host_3971_, 1);
v___y_3982_ = v___y_3992_;
v___y_3983_ = v_name_3993_;
goto v___jp_3981_;
}
case 1:
{
lean_object* v_ipv4_3994_; lean_object* v___x_3995_; 
v_ipv4_3994_ = lean_ctor_get(v_host_3971_, 0);
lean_inc_ref(v_ipv4_3994_);
lean_dec_ref_known(v_host_3971_, 1);
v___x_3995_ = lean_uv_ntop_v4(v_ipv4_3994_);
lean_dec_ref(v_ipv4_3994_);
v___y_3982_ = v___y_3992_;
v___y_3983_ = v___x_3995_;
goto v___jp_3981_;
}
default: 
{
lean_object* v_ipv6_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v_ipv6_3996_ = lean_ctor_get(v_host_3971_, 0);
lean_inc_ref(v_ipv6_3996_);
lean_dec_ref_known(v_host_3971_, 1);
v___x_3997_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3998_ = lean_uv_ntop_v6(v_ipv6_3996_);
lean_dec_ref(v_ipv6_3996_);
v___x_3999_ = lean_string_append(v___x_3997_, v___x_3998_);
lean_dec_ref(v___x_3998_);
v___x_4000_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4001_ = lean_string_append(v___x_3999_, v___x_4000_);
v___y_3982_ = v___y_3992_;
v___y_3983_ = v___x_4001_;
goto v___jp_3981_;
}
}
}
}
v___jp_3935_:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3940_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3941_ = lean_string_append(v_scheme_3930_, v___x_3940_);
v___x_3942_ = lean_string_append(v___x_3941_, v___y_3938_);
lean_dec_ref(v___y_3938_);
v___x_3943_ = lean_string_append(v___x_3942_, v___y_3936_);
lean_dec_ref(v___y_3936_);
v___x_3944_ = lean_string_append(v___x_3943_, v___y_3937_);
lean_dec_ref(v___y_3937_);
v___x_3945_ = lean_string_append(v___x_3944_, v___y_3939_);
lean_dec_ref(v___y_3939_);
return v___x_3945_;
}
v___jp_3946_:
{
lean_object* v_queryPart_3949_; 
v_queryPart_3949_ = l_Std_Http_URI_Query_formatOption(v_query_3933_);
if (lean_obj_tag(v_fragment_3934_) == 0)
{
lean_object* v___x_3950_; 
v___x_3950_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3936_ = v___y_3948_;
v___y_3937_ = v_queryPart_3949_;
v___y_3938_ = v___y_3947_;
v___y_3939_ = v___x_3950_;
goto v___jp_3935_;
}
else
{
lean_object* v_val_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v_val_3951_ = lean_ctor_get(v_fragment_3934_, 0);
lean_inc(v_val_3951_);
lean_dec_ref_known(v_fragment_3934_, 1);
v___x_3952_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_3953_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3951_);
lean_dec(v_val_3951_);
v___x_3954_ = lean_string_from_utf8_unchecked(v___x_3953_);
v___x_3955_ = lean_string_append(v___x_3952_, v___x_3954_);
lean_dec_ref(v___x_3954_);
v___y_3936_ = v___y_3948_;
v___y_3937_ = v_queryPart_3949_;
v___y_3938_ = v___y_3947_;
v___y_3939_ = v___x_3955_;
goto v___jp_3935_;
}
}
v___jp_3956_:
{
lean_object* v_segments_3958_; uint8_t v_absolute_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; size_t v_sz_3962_; size_t v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v_result_3966_; 
v_segments_3958_ = lean_ctor_get(v_path_3932_, 0);
lean_inc_ref(v_segments_3958_);
v_absolute_3959_ = lean_ctor_get_uint8(v_path_3932_, sizeof(void*)*1);
lean_dec_ref(v_path_3932_);
v___x_3960_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3961_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3962_ = lean_array_size(v_segments_3958_);
v___x_3963_ = ((size_t)0ULL);
v___x_3964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3961_, v___f_3905_, v_sz_3962_, v___x_3963_, v_segments_3958_);
v___x_3965_ = lean_array_to_list(v___x_3964_);
v_result_3966_ = l_String_intercalate(v___x_3960_, v___x_3965_);
if (v_absolute_3959_ == 0)
{
v___y_3947_ = v___y_3957_;
v___y_3948_ = v_result_3966_;
goto v___jp_3946_;
}
else
{
lean_object* v___x_3967_; 
v___x_3967_ = lean_string_append(v___x_3960_, v_result_3966_);
lean_dec_ref(v_result_3966_);
v___y_3947_ = v___y_3957_;
v___y_3948_ = v___x_3967_;
goto v___jp_3946_;
}
}
}
case 2:
{
lean_object* v_authority_4018_; lean_object* v_userInfo_4019_; lean_object* v_host_4020_; lean_object* v_port_4021_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4033_; 
lean_dec_ref(v___f_3905_);
lean_dec_ref(v___f_3904_);
v_authority_4018_ = lean_ctor_get(v_x_3906_, 0);
lean_inc_ref(v_authority_4018_);
lean_dec_ref_known(v_x_3906_, 1);
v_userInfo_4019_ = lean_ctor_get(v_authority_4018_, 0);
lean_inc(v_userInfo_4019_);
v_host_4020_ = lean_ctor_get(v_authority_4018_, 1);
lean_inc_ref(v_host_4020_);
v_port_4021_ = lean_ctor_get(v_authority_4018_, 2);
lean_inc(v_port_4021_);
lean_dec_ref(v_authority_4018_);
if (lean_obj_tag(v_userInfo_4019_) == 0)
{
lean_object* v___x_4043_; 
v___x_4043_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4033_ = v___x_4043_;
goto v___jp_4032_;
}
else
{
lean_object* v_val_4044_; lean_object* v_password_4045_; 
v_val_4044_ = lean_ctor_get(v_userInfo_4019_, 0);
lean_inc(v_val_4044_);
lean_dec_ref_known(v_userInfo_4019_, 1);
v_password_4045_ = lean_ctor_get(v_val_4044_, 1);
if (lean_obj_tag(v_password_4045_) == 0)
{
lean_object* v_username_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v_username_4046_ = lean_ctor_get(v_val_4044_, 0);
lean_inc_ref(v_username_4046_);
lean_dec(v_val_4044_);
v___x_4047_ = lean_string_from_utf8_unchecked(v_username_4046_);
v___x_4048_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4049_ = lean_string_append(v___x_4047_, v___x_4048_);
v___y_4033_ = v___x_4049_;
goto v___jp_4032_;
}
else
{
lean_object* v_username_4050_; lean_object* v_val_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
lean_inc_ref(v_password_4045_);
v_username_4050_ = lean_ctor_get(v_val_4044_, 0);
lean_inc_ref(v_username_4050_);
lean_dec(v_val_4044_);
v_val_4051_ = lean_ctor_get(v_password_4045_, 0);
lean_inc(v_val_4051_);
lean_dec_ref_known(v_password_4045_, 1);
v___x_4052_ = lean_string_from_utf8_unchecked(v_username_4050_);
v___x_4053_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4054_ = lean_string_append(v___x_4052_, v___x_4053_);
v___x_4055_ = lean_string_from_utf8_unchecked(v_val_4051_);
v___x_4056_ = lean_string_append(v___x_4054_, v___x_4055_);
lean_dec_ref(v___x_4055_);
v___x_4057_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4058_ = lean_string_append(v___x_4056_, v___x_4057_);
v___y_4033_ = v___x_4058_;
goto v___jp_4032_;
}
}
v___jp_4022_:
{
switch(lean_obj_tag(v_port_4021_))
{
case 0:
{
lean_object* v___x_4025_; 
v___x_4025_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3908_ = v___y_4024_;
v___y_3909_ = v___y_4023_;
v___y_3910_ = v___x_4025_;
goto v___jp_3907_;
}
case 1:
{
lean_object* v___x_4026_; 
v___x_4026_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3908_ = v___y_4024_;
v___y_3909_ = v___y_4023_;
v___y_3910_ = v___x_4026_;
goto v___jp_3907_;
}
default: 
{
uint16_t v_port_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v_port_4027_ = lean_ctor_get_uint16(v_port_4021_, 0);
lean_dec_ref_known(v_port_4021_, 0);
v___x_4028_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4029_ = lean_uint16_to_nat(v_port_4027_);
v___x_4030_ = l_Nat_reprFast(v___x_4029_);
v___x_4031_ = lean_string_append(v___x_4028_, v___x_4030_);
lean_dec_ref(v___x_4030_);
v___y_3908_ = v___y_4024_;
v___y_3909_ = v___y_4023_;
v___y_3910_ = v___x_4031_;
goto v___jp_3907_;
}
}
}
v___jp_4032_:
{
switch(lean_obj_tag(v_host_4020_))
{
case 0:
{
lean_object* v_name_4034_; 
v_name_4034_ = lean_ctor_get(v_host_4020_, 0);
lean_inc_ref(v_name_4034_);
lean_dec_ref_known(v_host_4020_, 1);
v___y_4023_ = v___y_4033_;
v___y_4024_ = v_name_4034_;
goto v___jp_4022_;
}
case 1:
{
lean_object* v_ipv4_4035_; lean_object* v___x_4036_; 
v_ipv4_4035_ = lean_ctor_get(v_host_4020_, 0);
lean_inc_ref(v_ipv4_4035_);
lean_dec_ref_known(v_host_4020_, 1);
v___x_4036_ = lean_uv_ntop_v4(v_ipv4_4035_);
lean_dec_ref(v_ipv4_4035_);
v___y_4023_ = v___y_4033_;
v___y_4024_ = v___x_4036_;
goto v___jp_4022_;
}
default: 
{
lean_object* v_ipv6_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v_ipv6_4037_ = lean_ctor_get(v_host_4020_, 0);
lean_inc_ref(v_ipv6_4037_);
lean_dec_ref_known(v_host_4020_, 1);
v___x_4038_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4039_ = lean_uv_ntop_v6(v_ipv6_4037_);
lean_dec_ref(v_ipv6_4037_);
v___x_4040_ = lean_string_append(v___x_4038_, v___x_4039_);
lean_dec_ref(v___x_4039_);
v___x_4041_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4042_ = lean_string_append(v___x_4040_, v___x_4041_);
v___y_4023_ = v___y_4033_;
v___y_4024_ = v___x_4042_;
goto v___jp_4022_;
}
}
}
}
default: 
{
lean_object* v___x_4059_; 
lean_dec_ref(v___f_3905_);
lean_dec_ref(v___f_3904_);
v___x_4059_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__2___closed__0));
return v___x_4059_;
}
}
v___jp_3907_:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = lean_string_append(v___y_3909_, v___y_3908_);
lean_dec_ref(v___y_3908_);
v___x_3912_ = lean_string_append(v___x_3911_, v___y_3910_);
lean_dec_ref(v___y_3910_);
return v___x_3912_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__2(lean_object* v___f_4063_, lean_object* v___f_4064_, lean_object* v_buffer_4065_, lean_object* v_target_4066_){
_start:
{
lean_object* v___y_4068_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; 
switch(lean_obj_tag(v_target_4066_))
{
case 0:
{
lean_object* v_path_4088_; lean_object* v_query_4089_; lean_object* v___y_4091_; lean_object* v_segments_4094_; uint8_t v_absolute_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; size_t v_sz_4098_; size_t v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v_result_4102_; 
lean_dec_ref(v___f_4064_);
v_path_4088_ = lean_ctor_get(v_target_4066_, 0);
lean_inc_ref(v_path_4088_);
v_query_4089_ = lean_ctor_get(v_target_4066_, 1);
lean_inc(v_query_4089_);
lean_dec_ref_known(v_target_4066_, 2);
v_segments_4094_ = lean_ctor_get(v_path_4088_, 0);
lean_inc_ref(v_segments_4094_);
v_absolute_4095_ = lean_ctor_get_uint8(v_path_4088_, sizeof(void*)*1);
lean_dec_ref(v_path_4088_);
v___x_4096_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_4097_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_4098_ = lean_array_size(v_segments_4094_);
v___x_4099_ = ((size_t)0ULL);
v___x_4100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4097_, v___f_4063_, v_sz_4098_, v___x_4099_, v_segments_4094_);
v___x_4101_ = lean_array_to_list(v___x_4100_);
v_result_4102_ = l_String_intercalate(v___x_4096_, v___x_4101_);
if (v_absolute_4095_ == 0)
{
v___y_4091_ = v_result_4102_;
goto v___jp_4090_;
}
else
{
lean_object* v___x_4103_; 
v___x_4103_ = lean_string_append(v___x_4096_, v_result_4102_);
lean_dec_ref(v_result_4102_);
v___y_4091_ = v___x_4103_;
goto v___jp_4090_;
}
v___jp_4090_:
{
lean_object* v_queryStr_4092_; lean_object* v___x_4093_; 
v_queryStr_4092_ = l_Std_Http_URI_Query_formatOption(v_query_4089_);
v___x_4093_ = lean_string_append(v___y_4091_, v_queryStr_4092_);
lean_dec_ref(v_queryStr_4092_);
v___y_4068_ = v___x_4093_;
goto v___jp_4067_;
}
}
case 1:
{
lean_object* v_uri_4104_; lean_object* v_scheme_4105_; lean_object* v_authority_4106_; lean_object* v_path_4107_; lean_object* v_query_4108_; lean_object* v_fragment_4109_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4132_; 
lean_dec_ref(v___f_4063_);
v_uri_4104_ = lean_ctor_get(v_target_4066_, 0);
lean_inc_ref(v_uri_4104_);
lean_dec_ref_known(v_target_4066_, 1);
v_scheme_4105_ = lean_ctor_get(v_uri_4104_, 0);
lean_inc_ref(v_scheme_4105_);
v_authority_4106_ = lean_ctor_get(v_uri_4104_, 1);
lean_inc(v_authority_4106_);
v_path_4107_ = lean_ctor_get(v_uri_4104_, 2);
lean_inc_ref(v_path_4107_);
v_query_4108_ = lean_ctor_get(v_uri_4104_, 3);
lean_inc(v_query_4108_);
v_fragment_4109_ = lean_ctor_get(v_uri_4104_, 4);
lean_inc(v_fragment_4109_);
lean_dec_ref(v_uri_4104_);
if (lean_obj_tag(v_authority_4106_) == 0)
{
lean_object* v___x_4143_; 
v___x_4143_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4132_ = v___x_4143_;
goto v___jp_4131_;
}
else
{
lean_object* v_val_4144_; lean_object* v_userInfo_4145_; lean_object* v_host_4146_; lean_object* v_port_4147_; lean_object* v___x_4148_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4167_; 
v_val_4144_ = lean_ctor_get(v_authority_4106_, 0);
lean_inc(v_val_4144_);
lean_dec_ref_known(v_authority_4106_, 1);
v_userInfo_4145_ = lean_ctor_get(v_val_4144_, 0);
lean_inc(v_userInfo_4145_);
v_host_4146_ = lean_ctor_get(v_val_4144_, 1);
lean_inc_ref(v_host_4146_);
v_port_4147_ = lean_ctor_get(v_val_4144_, 2);
lean_inc(v_port_4147_);
lean_dec(v_val_4144_);
v___x_4148_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__1));
if (lean_obj_tag(v_userInfo_4145_) == 0)
{
lean_object* v___x_4177_; 
v___x_4177_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4167_ = v___x_4177_;
goto v___jp_4166_;
}
else
{
lean_object* v_val_4178_; lean_object* v_password_4179_; 
v_val_4178_ = lean_ctor_get(v_userInfo_4145_, 0);
lean_inc(v_val_4178_);
lean_dec_ref_known(v_userInfo_4145_, 1);
v_password_4179_ = lean_ctor_get(v_val_4178_, 1);
if (lean_obj_tag(v_password_4179_) == 0)
{
lean_object* v_username_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v_username_4180_ = lean_ctor_get(v_val_4178_, 0);
lean_inc_ref(v_username_4180_);
lean_dec(v_val_4178_);
v___x_4181_ = lean_string_from_utf8_unchecked(v_username_4180_);
v___x_4182_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4183_ = lean_string_append(v___x_4181_, v___x_4182_);
v___y_4167_ = v___x_4183_;
goto v___jp_4166_;
}
else
{
lean_object* v_username_4184_; lean_object* v_val_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
lean_inc_ref(v_password_4179_);
v_username_4184_ = lean_ctor_get(v_val_4178_, 0);
lean_inc_ref(v_username_4184_);
lean_dec(v_val_4178_);
v_val_4185_ = lean_ctor_get(v_password_4179_, 0);
lean_inc(v_val_4185_);
lean_dec_ref_known(v_password_4179_, 1);
v___x_4186_ = lean_string_from_utf8_unchecked(v_username_4184_);
v___x_4187_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4188_ = lean_string_append(v___x_4186_, v___x_4187_);
v___x_4189_ = lean_string_from_utf8_unchecked(v_val_4185_);
v___x_4190_ = lean_string_append(v___x_4188_, v___x_4189_);
lean_dec_ref(v___x_4189_);
v___x_4191_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4192_ = lean_string_append(v___x_4190_, v___x_4191_);
v___y_4167_ = v___x_4192_;
goto v___jp_4166_;
}
}
v___jp_4149_:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4153_ = lean_string_append(v___y_4150_, v___y_4151_);
lean_dec_ref(v___y_4151_);
v___x_4154_ = lean_string_append(v___x_4153_, v___y_4152_);
lean_dec_ref(v___y_4152_);
v___x_4155_ = lean_string_append(v___x_4148_, v___x_4154_);
lean_dec_ref(v___x_4154_);
v___y_4132_ = v___x_4155_;
goto v___jp_4131_;
}
v___jp_4156_:
{
switch(lean_obj_tag(v_port_4147_))
{
case 0:
{
lean_object* v___x_4159_; 
v___x_4159_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4150_ = v___y_4157_;
v___y_4151_ = v___y_4158_;
v___y_4152_ = v___x_4159_;
goto v___jp_4149_;
}
case 1:
{
lean_object* v___x_4160_; 
v___x_4160_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_4150_ = v___y_4157_;
v___y_4151_ = v___y_4158_;
v___y_4152_ = v___x_4160_;
goto v___jp_4149_;
}
default: 
{
uint16_t v_port_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v_port_4161_ = lean_ctor_get_uint16(v_port_4147_, 0);
lean_dec_ref_known(v_port_4147_, 0);
v___x_4162_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4163_ = lean_uint16_to_nat(v_port_4161_);
v___x_4164_ = l_Nat_reprFast(v___x_4163_);
v___x_4165_ = lean_string_append(v___x_4162_, v___x_4164_);
lean_dec_ref(v___x_4164_);
v___y_4150_ = v___y_4157_;
v___y_4151_ = v___y_4158_;
v___y_4152_ = v___x_4165_;
goto v___jp_4149_;
}
}
}
v___jp_4166_:
{
switch(lean_obj_tag(v_host_4146_))
{
case 0:
{
lean_object* v_name_4168_; 
v_name_4168_ = lean_ctor_get(v_host_4146_, 0);
lean_inc_ref(v_name_4168_);
lean_dec_ref_known(v_host_4146_, 1);
v___y_4157_ = v___y_4167_;
v___y_4158_ = v_name_4168_;
goto v___jp_4156_;
}
case 1:
{
lean_object* v_ipv4_4169_; lean_object* v___x_4170_; 
v_ipv4_4169_ = lean_ctor_get(v_host_4146_, 0);
lean_inc_ref(v_ipv4_4169_);
lean_dec_ref_known(v_host_4146_, 1);
v___x_4170_ = lean_uv_ntop_v4(v_ipv4_4169_);
lean_dec_ref(v_ipv4_4169_);
v___y_4157_ = v___y_4167_;
v___y_4158_ = v___x_4170_;
goto v___jp_4156_;
}
default: 
{
lean_object* v_ipv6_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v_ipv6_4171_ = lean_ctor_get(v_host_4146_, 0);
lean_inc_ref(v_ipv6_4171_);
lean_dec_ref_known(v_host_4146_, 1);
v___x_4172_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4173_ = lean_uv_ntop_v6(v_ipv6_4171_);
lean_dec_ref(v_ipv6_4171_);
v___x_4174_ = lean_string_append(v___x_4172_, v___x_4173_);
lean_dec_ref(v___x_4173_);
v___x_4175_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4176_ = lean_string_append(v___x_4174_, v___x_4175_);
v___y_4157_ = v___y_4167_;
v___y_4158_ = v___x_4176_;
goto v___jp_4156_;
}
}
}
}
v___jp_4110_:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4115_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4116_ = lean_string_append(v_scheme_4105_, v___x_4115_);
v___x_4117_ = lean_string_append(v___x_4116_, v___y_4112_);
lean_dec_ref(v___y_4112_);
v___x_4118_ = lean_string_append(v___x_4117_, v___y_4111_);
lean_dec_ref(v___y_4111_);
v___x_4119_ = lean_string_append(v___x_4118_, v___y_4113_);
lean_dec_ref(v___y_4113_);
v___x_4120_ = lean_string_append(v___x_4119_, v___y_4114_);
lean_dec_ref(v___y_4114_);
v___y_4068_ = v___x_4120_;
goto v___jp_4067_;
}
v___jp_4121_:
{
lean_object* v_queryPart_4124_; 
v_queryPart_4124_ = l_Std_Http_URI_Query_formatOption(v_query_4108_);
if (lean_obj_tag(v_fragment_4109_) == 0)
{
lean_object* v___x_4125_; 
v___x_4125_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4111_ = v___y_4123_;
v___y_4112_ = v___y_4122_;
v___y_4113_ = v_queryPart_4124_;
v___y_4114_ = v___x_4125_;
goto v___jp_4110_;
}
else
{
lean_object* v_val_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v_val_4126_ = lean_ctor_get(v_fragment_4109_, 0);
lean_inc(v_val_4126_);
lean_dec_ref_known(v_fragment_4109_, 1);
v___x_4127_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__1___closed__0));
v___x_4128_ = l_Std_Http_URI_EncodedFragment_encode(v_val_4126_);
lean_dec(v_val_4126_);
v___x_4129_ = lean_string_from_utf8_unchecked(v___x_4128_);
v___x_4130_ = lean_string_append(v___x_4127_, v___x_4129_);
lean_dec_ref(v___x_4129_);
v___y_4111_ = v___y_4123_;
v___y_4112_ = v___y_4122_;
v___y_4113_ = v_queryPart_4124_;
v___y_4114_ = v___x_4130_;
goto v___jp_4110_;
}
}
v___jp_4131_:
{
lean_object* v_segments_4133_; uint8_t v_absolute_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; size_t v_sz_4137_; size_t v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v_result_4141_; 
v_segments_4133_ = lean_ctor_get(v_path_4107_, 0);
lean_inc_ref(v_segments_4133_);
v_absolute_4134_ = lean_ctor_get_uint8(v_path_4107_, sizeof(void*)*1);
lean_dec_ref(v_path_4107_);
v___x_4135_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_4136_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_4137_ = lean_array_size(v_segments_4133_);
v___x_4138_ = ((size_t)0ULL);
v___x_4139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4136_, v___f_4064_, v_sz_4137_, v___x_4138_, v_segments_4133_);
v___x_4140_ = lean_array_to_list(v___x_4139_);
v_result_4141_ = l_String_intercalate(v___x_4135_, v___x_4140_);
if (v_absolute_4134_ == 0)
{
v___y_4122_ = v___y_4132_;
v___y_4123_ = v_result_4141_;
goto v___jp_4121_;
}
else
{
lean_object* v___x_4142_; 
v___x_4142_ = lean_string_append(v___x_4135_, v_result_4141_);
lean_dec_ref(v_result_4141_);
v___y_4122_ = v___y_4132_;
v___y_4123_ = v___x_4142_;
goto v___jp_4121_;
}
}
}
case 2:
{
lean_object* v_authority_4193_; lean_object* v_userInfo_4194_; lean_object* v_host_4195_; lean_object* v_port_4196_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4208_; 
lean_dec_ref(v___f_4064_);
lean_dec_ref(v___f_4063_);
v_authority_4193_ = lean_ctor_get(v_target_4066_, 0);
lean_inc_ref(v_authority_4193_);
lean_dec_ref_known(v_target_4066_, 1);
v_userInfo_4194_ = lean_ctor_get(v_authority_4193_, 0);
lean_inc(v_userInfo_4194_);
v_host_4195_ = lean_ctor_get(v_authority_4193_, 1);
lean_inc_ref(v_host_4195_);
v_port_4196_ = lean_ctor_get(v_authority_4193_, 2);
lean_inc(v_port_4196_);
lean_dec_ref(v_authority_4193_);
if (lean_obj_tag(v_userInfo_4194_) == 0)
{
lean_object* v___x_4218_; 
v___x_4218_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4208_ = v___x_4218_;
goto v___jp_4207_;
}
else
{
lean_object* v_val_4219_; lean_object* v_password_4220_; 
v_val_4219_ = lean_ctor_get(v_userInfo_4194_, 0);
lean_inc(v_val_4219_);
lean_dec_ref_known(v_userInfo_4194_, 1);
v_password_4220_ = lean_ctor_get(v_val_4219_, 1);
if (lean_obj_tag(v_password_4220_) == 0)
{
lean_object* v_username_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v_username_4221_ = lean_ctor_get(v_val_4219_, 0);
lean_inc_ref(v_username_4221_);
lean_dec(v_val_4219_);
v___x_4222_ = lean_string_from_utf8_unchecked(v_username_4221_);
v___x_4223_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4224_ = lean_string_append(v___x_4222_, v___x_4223_);
v___y_4208_ = v___x_4224_;
goto v___jp_4207_;
}
else
{
lean_object* v_username_4225_; lean_object* v_val_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
lean_inc_ref(v_password_4220_);
v_username_4225_ = lean_ctor_get(v_val_4219_, 0);
lean_inc_ref(v_username_4225_);
lean_dec(v_val_4219_);
v_val_4226_ = lean_ctor_get(v_password_4220_, 0);
lean_inc(v_val_4226_);
lean_dec_ref_known(v_password_4220_, 1);
v___x_4227_ = lean_string_from_utf8_unchecked(v_username_4225_);
v___x_4228_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4229_ = lean_string_append(v___x_4227_, v___x_4228_);
v___x_4230_ = lean_string_from_utf8_unchecked(v_val_4226_);
v___x_4231_ = lean_string_append(v___x_4229_, v___x_4230_);
lean_dec_ref(v___x_4230_);
v___x_4232_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_4233_ = lean_string_append(v___x_4231_, v___x_4232_);
v___y_4208_ = v___x_4233_;
goto v___jp_4207_;
}
}
v___jp_4197_:
{
switch(lean_obj_tag(v_port_4196_))
{
case 0:
{
lean_object* v___x_4200_; 
v___x_4200_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_4083_ = v___y_4199_;
v___y_4084_ = v___y_4198_;
v___y_4085_ = v___x_4200_;
goto v___jp_4082_;
}
case 1:
{
lean_object* v___x_4201_; 
v___x_4201_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_4083_ = v___y_4199_;
v___y_4084_ = v___y_4198_;
v___y_4085_ = v___x_4201_;
goto v___jp_4082_;
}
default: 
{
uint16_t v_port_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v_port_4202_ = lean_ctor_get_uint16(v_port_4196_, 0);
lean_dec_ref_known(v_port_4196_, 0);
v___x_4203_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_4204_ = lean_uint16_to_nat(v_port_4202_);
v___x_4205_ = l_Nat_reprFast(v___x_4204_);
v___x_4206_ = lean_string_append(v___x_4203_, v___x_4205_);
lean_dec_ref(v___x_4205_);
v___y_4083_ = v___y_4199_;
v___y_4084_ = v___y_4198_;
v___y_4085_ = v___x_4206_;
goto v___jp_4082_;
}
}
}
v___jp_4207_:
{
switch(lean_obj_tag(v_host_4195_))
{
case 0:
{
lean_object* v_name_4209_; 
v_name_4209_ = lean_ctor_get(v_host_4195_, 0);
lean_inc_ref(v_name_4209_);
lean_dec_ref_known(v_host_4195_, 1);
v___y_4198_ = v___y_4208_;
v___y_4199_ = v_name_4209_;
goto v___jp_4197_;
}
case 1:
{
lean_object* v_ipv4_4210_; lean_object* v___x_4211_; 
v_ipv4_4210_ = lean_ctor_get(v_host_4195_, 0);
lean_inc_ref(v_ipv4_4210_);
lean_dec_ref_known(v_host_4195_, 1);
v___x_4211_ = lean_uv_ntop_v4(v_ipv4_4210_);
lean_dec_ref(v_ipv4_4210_);
v___y_4198_ = v___y_4208_;
v___y_4199_ = v___x_4211_;
goto v___jp_4197_;
}
default: 
{
lean_object* v_ipv6_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v_ipv6_4212_ = lean_ctor_get(v_host_4195_, 0);
lean_inc_ref(v_ipv6_4212_);
lean_dec_ref_known(v_host_4195_, 1);
v___x_4213_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_4214_ = lean_uv_ntop_v6(v_ipv6_4212_);
lean_dec_ref(v_ipv6_4212_);
v___x_4215_ = lean_string_append(v___x_4213_, v___x_4214_);
lean_dec_ref(v___x_4214_);
v___x_4216_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_4217_ = lean_string_append(v___x_4215_, v___x_4216_);
v___y_4198_ = v___y_4208_;
v___y_4199_ = v___x_4217_;
goto v___jp_4197_;
}
}
}
}
default: 
{
lean_object* v___x_4234_; 
lean_dec_ref(v___f_4064_);
lean_dec_ref(v___f_4063_);
v___x_4234_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__2___closed__0));
v___y_4068_ = v___x_4234_;
goto v___jp_4067_;
}
}
v___jp_4067_:
{
lean_object* v_data_4069_; lean_object* v_size_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4081_; 
v_data_4069_ = lean_ctor_get(v_buffer_4065_, 0);
v_size_4070_ = lean_ctor_get(v_buffer_4065_, 1);
v_isSharedCheck_4081_ = !lean_is_exclusive(v_buffer_4065_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4072_ = v_buffer_4065_;
v_isShared_4073_ = v_isSharedCheck_4081_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_size_4070_);
lean_inc(v_data_4069_);
lean_dec(v_buffer_4065_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4081_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4079_; 
v___x_4074_ = lean_string_to_utf8(v___y_4068_);
lean_dec_ref(v___y_4068_);
lean_inc_ref(v___x_4074_);
v___x_4075_ = lean_array_push(v_data_4069_, v___x_4074_);
v___x_4076_ = lean_byte_array_size(v___x_4074_);
lean_dec_ref(v___x_4074_);
v___x_4077_ = lean_nat_add(v_size_4070_, v___x_4076_);
lean_dec(v_size_4070_);
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 1, v___x_4077_);
lean_ctor_set(v___x_4072_, 0, v___x_4075_);
v___x_4079_ = v___x_4072_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4075_);
lean_ctor_set(v_reuseFailAlloc_4080_, 1, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
v___jp_4082_:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4086_ = lean_string_append(v___y_4084_, v___y_4083_);
lean_dec_ref(v___y_4083_);
v___x_4087_ = lean_string_append(v___x_4086_, v___y_4085_);
lean_dec_ref(v___y_4085_);
v___y_4068_ = v___x_4087_;
goto v___jp_4067_;
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
