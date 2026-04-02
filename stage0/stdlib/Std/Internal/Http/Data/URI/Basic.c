// Lean compiler output
// Module: Std.Internal.Http.Data.URI.Basic
// Imports: import Init.Data.ToString public import Std.Net public import Std.Internal.Http.Internal public import Std.Internal.Http.Data.URI.Encoding
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
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_getLast_x3f___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
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
static const lean_string_object l_Std_Http_URI_DomainName_ofString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Std_Http_URI_DomainName_ofString_x3f___closed__0 = (const lean_object*)&l_Std_Http_URI_DomainName_ofString_x3f___closed__0_value;
static const lean_closure_object l_Std_Http_URI_DomainName_ofString_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_isValidDomainLabel___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_DomainName_ofString_x3f___closed__1 = (const lean_object*)&l_Std_Http_URI_DomainName_ofString_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_DomainName_ofString_x3f(lean_object*);
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
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".."};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0_value;
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
static const lean_array_object l_Std_Http_URI_Builder_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_URI_Builder_empty___closed__0 = (const lean_object*)&l_Std_Http_URI_Builder_empty___closed__0_value;
static const lean_ctor_object l_Std_Http_URI_Builder_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_URI_Builder_empty___closed__0_value),((lean_object*)&l_Std_Http_URI_Builder_empty___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_URI_Builder_empty___closed__1 = (const lean_object*)&l_Std_Http_URI_Builder_empty___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_Builder_empty = (const lean_object*)&l_Std_Http_URI_Builder_empty___closed__1_value;
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
v___x_91_ = lean_unsigned_to_nat(82u);
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
uint32_t v___y_422_; uint8_t v___y_428_; uint32_t v___y_429_; uint8_t v___y_430_; lean_object* v_chars_435_; uint8_t v___y_453_; uint32_t v___y_455_; uint8_t v___y_461_; uint32_t v___y_462_; uint8_t v___y_463_; uint8_t v___y_469_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
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
v___x_432_ = lean_uint32_dec_le(v___x_431_, v___y_429_);
if (v___x_432_ == 0)
{
v___y_422_ = v___y_429_;
goto v___jp_421_;
}
else
{
uint32_t v___x_433_; uint8_t v___x_434_; 
v___x_433_ = 90;
v___x_434_ = lean_uint32_dec_le(v___y_429_, v___x_433_);
if (v___x_434_ == 0)
{
v___y_422_ = v___y_429_;
goto v___jp_421_;
}
else
{
return v___y_428_;
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
v___y_428_ = v___x_443_;
v___y_429_ = v___x_447_;
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
v___y_428_ = v___x_443_;
v___y_429_ = v___x_451_;
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
LEAN_EXPORT lean_object* l_Std_Http_URI_DomainName_ofString_x3f(lean_object* v_s_496_){
_start:
{
lean_object* v___x_497_; lean_object* v_lower_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_497_ = lean_unsigned_to_nat(0u);
v_lower_498_ = l_String_mapAux___at___00Std_Http_URI_Scheme_ofString_x3f_spec__0(v_s_496_, v___x_497_);
v___x_499_ = lean_string_utf8_byte_size(v_lower_498_);
v___x_500_ = lean_nat_dec_eq(v___x_499_, v___x_497_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_501_ = ((lean_object*)(l_Std_Http_URI_DomainName_ofString_x3f___closed__0));
v___x_502_ = lean_box(0);
v___x_503_ = l_String_splitOnAux(v_lower_498_, v___x_501_, v___x_497_, v___x_497_, v___x_497_, v___x_502_);
v___x_504_ = l_List_isEmpty___redArg(v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = ((lean_object*)(l_Std_Http_URI_DomainName_ofString_x3f___closed__1));
v___x_506_ = l_List_all___redArg(v___x_503_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
lean_dec_ref(v_lower_498_);
v___x_507_ = lean_box(0);
return v___x_507_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_508_ = lean_string_length(v_lower_498_);
v___x_509_ = lean_unsigned_to_nat(255u);
v___x_510_ = lean_nat_dec_le(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec_ref(v_lower_498_);
v___x_511_ = lean_box(0);
return v___x_511_;
}
else
{
lean_object* v___x_512_; 
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v_lower_498_);
return v___x_512_;
}
}
}
else
{
lean_object* v___x_513_; 
lean_dec(v___x_503_);
lean_dec_ref(v_lower_498_);
v___x_513_ = lean_box(0);
return v___x_513_;
}
}
else
{
lean_object* v___x_514_; 
lean_dec_ref(v_lower_498_);
v___x_514_ = lean_box(0);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx(lean_object* v_x_515_){
_start:
{
switch(lean_obj_tag(v_x_515_))
{
case 0:
{
lean_object* v___x_516_; 
v___x_516_ = lean_unsigned_to_nat(0u);
return v___x_516_;
}
case 1:
{
lean_object* v___x_517_; 
v___x_517_ = lean_unsigned_to_nat(1u);
return v___x_517_;
}
default: 
{
lean_object* v___x_518_; 
v___x_518_ = lean_unsigned_to_nat(2u);
return v___x_518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorIdx___boxed(lean_object* v_x_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Std_Http_URI_Host_ctorIdx(v_x_519_);
lean_dec_ref(v_x_519_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___redArg(lean_object* v_t_521_, lean_object* v_k_522_){
_start:
{
lean_object* v_name_523_; lean_object* v___x_524_; 
v_name_523_ = lean_ctor_get(v_t_521_, 0);
lean_inc_ref(v_name_523_);
lean_dec_ref(v_t_521_);
v___x_524_ = lean_apply_1(v_k_522_, v_name_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim(lean_object* v_motive_525_, lean_object* v_ctorIdx_526_, lean_object* v_t_527_, lean_object* v_h_528_, lean_object* v_k_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_527_, v_k_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ctorElim___boxed(lean_object* v_motive_531_, lean_object* v_ctorIdx_532_, lean_object* v_t_533_, lean_object* v_h_534_, lean_object* v_k_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_Http_URI_Host_ctorElim(v_motive_531_, v_ctorIdx_532_, v_t_533_, v_h_534_, v_k_535_);
lean_dec(v_ctorIdx_532_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim___redArg(lean_object* v_t_537_, lean_object* v_name_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_537_, v_name_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_name_elim(lean_object* v_motive_540_, lean_object* v_t_541_, lean_object* v_h_542_, lean_object* v_name_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_541_, v_name_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim___redArg(lean_object* v_t_545_, lean_object* v_ipv4_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_545_, v_ipv4_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv4_elim(lean_object* v_motive_548_, lean_object* v_t_549_, lean_object* v_h_550_, lean_object* v_ipv4_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_549_, v_ipv4_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim___redArg(lean_object* v_t_553_, lean_object* v_ipv6_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_553_, v_ipv6_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Host_ipv6_elim(lean_object* v_motive_556_, lean_object* v_t_557_, lean_object* v_h_558_, lean_object* v_ipv6_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Std_Http_URI_Host_ctorElim___redArg(v_t_557_, v_ipv6_559_);
return v___x_560_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default___closed__0(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost_default(void){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = lean_obj_once(&l_Std_Http_URI_instInhabitedHost_default___closed__0, &l_Std_Http_URI_instInhabitedHost_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedHost_default___closed__0);
return v___x_563_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedHost(void){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Std_Http_URI_instInhabitedHost_default;
return v___x_564_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqHost_beq(lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
switch(lean_obj_tag(v_x_565_))
{
case 0:
{
if (lean_obj_tag(v_x_566_) == 0)
{
lean_object* v_name_567_; lean_object* v_name_568_; uint8_t v___x_569_; 
v_name_567_ = lean_ctor_get(v_x_565_, 0);
v_name_568_ = lean_ctor_get(v_x_566_, 0);
v___x_569_ = lean_string_dec_eq(v_name_567_, v_name_568_);
return v___x_569_;
}
else
{
uint8_t v___x_570_; 
v___x_570_ = 0;
return v___x_570_;
}
}
case 1:
{
if (lean_obj_tag(v_x_566_) == 1)
{
lean_object* v_ipv4_571_; lean_object* v_ipv4_572_; uint8_t v___x_573_; 
v_ipv4_571_ = lean_ctor_get(v_x_565_, 0);
v_ipv4_572_ = lean_ctor_get(v_x_566_, 0);
v___x_573_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_ipv4_571_, v_ipv4_572_);
return v___x_573_;
}
else
{
uint8_t v___x_574_; 
v___x_574_ = 0;
return v___x_574_;
}
}
default: 
{
if (lean_obj_tag(v_x_566_) == 2)
{
lean_object* v_ipv6_575_; lean_object* v_ipv6_576_; uint8_t v___x_577_; 
v_ipv6_575_ = lean_ctor_get(v_x_565_, 0);
v_ipv6_576_ = lean_ctor_get(v_x_566_, 0);
v___x_577_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_ipv6_575_, v_ipv6_576_);
return v___x_577_;
}
else
{
uint8_t v___x_578_; 
v___x_578_ = 0;
return v___x_578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqHost_beq___boxed(lean_object* v_x_579_, lean_object* v_x_580_){
_start:
{
uint8_t v_res_581_; lean_object* v_r_582_; 
v_res_581_ = l_Std_Http_URI_instBEqHost_beq(v_x_579_, v_x_580_);
lean_dec_ref(v_x_580_);
lean_dec_ref(v_x_579_);
v_r_582_ = lean_box(v_res_581_);
return v_r_582_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__4(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(2u);
v___x_590_ = lean_nat_to_int(v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprHost___lam__0___closed__5(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = lean_nat_to_int(v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0(lean_object* v_x_593_, lean_object* v_prec_594_){
_start:
{
lean_object* v___y_596_; lean_object* v_ctr_597_; lean_object* v_a_598_; lean_object* v___y_610_; lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_unsigned_to_nat(1024u);
v___x_642_ = lean_nat_dec_le(v___x_641_, v_prec_594_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
v___x_643_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_610_ = v___x_643_;
goto v___jp_609_;
}
else
{
lean_object* v___x_644_; 
v___x_644_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_610_ = v___x_644_;
goto v___jp_609_;
}
v___jp_595_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_599_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_600_ = lean_string_append(v___x_599_, v_ctr_597_);
v___x_601_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v___x_602_ = lean_box(1);
v___x_603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v_a_598_);
lean_inc(v___y_596_);
v___x_605_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_605_, 0, v___y_596_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = 0;
v___x_607_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set_uint8(v___x_607_, sizeof(void*)*1, v___x_606_);
v___x_608_ = l_Repr_addAppParen(v___x_607_, v_prec_594_);
return v___x_608_;
}
v___jp_609_:
{
switch(lean_obj_tag(v_x_593_))
{
case 0:
{
lean_object* v_name_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_620_; 
v_name_611_ = lean_ctor_get(v_x_593_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_620_ == 0)
{
v___x_613_ = v_x_593_;
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_name_611_);
lean_dec(v_x_593_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_615_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_616_ = l_String_quote(v_name_611_);
if (v_isShared_614_ == 0)
{
lean_ctor_set_tag(v___x_613_, 3);
lean_ctor_set(v___x_613_, 0, v___x_616_);
v___x_618_ = v___x_613_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
v___y_596_ = v___y_610_;
v_ctr_597_ = v___x_615_;
v_a_598_ = v___x_618_;
goto v___jp_595_;
}
}
}
case 1:
{
lean_object* v_ipv4_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_630_; 
v_ipv4_621_ = lean_ctor_get(v_x_593_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_630_ == 0)
{
v___x_623_ = v_x_593_;
v_isShared_624_ = v_isSharedCheck_630_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_ipv4_621_);
lean_dec(v_x_593_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_630_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_625_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_626_ = lean_uv_ntop_v4(v_ipv4_621_);
lean_dec_ref(v_ipv4_621_);
if (v_isShared_624_ == 0)
{
lean_ctor_set_tag(v___x_623_, 3);
lean_ctor_set(v___x_623_, 0, v___x_626_);
v___x_628_ = v___x_623_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
v___y_596_ = v___y_610_;
v_ctr_597_ = v___x_625_;
v_a_598_ = v___x_628_;
goto v___jp_595_;
}
}
}
default: 
{
lean_object* v_ipv6_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_640_; 
v_ipv6_631_ = lean_ctor_get(v_x_593_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_640_ == 0)
{
v___x_633_ = v_x_593_;
v_isShared_634_ = v_isSharedCheck_640_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_ipv6_631_);
lean_dec(v_x_593_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_640_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_635_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_636_ = lean_uv_ntop_v6(v_ipv6_631_);
lean_dec_ref(v_ipv6_631_);
if (v_isShared_634_ == 0)
{
lean_ctor_set_tag(v___x_633_, 3);
lean_ctor_set(v___x_633_, 0, v___x_636_);
v___x_638_ = v___x_633_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
v___y_596_ = v___y_610_;
v_ctr_597_ = v___x_635_;
v_a_598_ = v___x_638_;
goto v___jp_595_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprHost___lam__0___boxed(lean_object* v_x_645_, lean_object* v_prec_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Std_Http_URI_instReprHost___lam__0(v_x_645_, v_prec_646_);
lean_dec(v_prec_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0(lean_object* v_x_652_){
_start:
{
switch(lean_obj_tag(v_x_652_))
{
case 0:
{
lean_object* v_name_653_; 
v_name_653_ = lean_ctor_get(v_x_652_, 0);
lean_inc_ref(v_name_653_);
return v_name_653_;
}
case 1:
{
lean_object* v_ipv4_654_; lean_object* v___x_655_; 
v_ipv4_654_ = lean_ctor_get(v_x_652_, 0);
v___x_655_ = lean_uv_ntop_v4(v_ipv4_654_);
return v___x_655_;
}
default: 
{
lean_object* v_ipv6_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_ipv6_656_ = lean_ctor_get(v_x_652_, 0);
v___x_657_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_658_ = lean_uv_ntop_v6(v_ipv6_656_);
v___x_659_ = lean_string_append(v___x_657_, v___x_658_);
lean_dec_ref(v___x_658_);
v___x_660_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_661_ = lean_string_append(v___x_659_, v___x_660_);
return v___x_661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringHost___lam__0___boxed(lean_object* v_x_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Std_Http_URI_instToStringHost___lam__0(v_x_662_);
lean_dec_ref(v_x_662_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx(lean_object* v_x_666_){
_start:
{
switch(lean_obj_tag(v_x_666_))
{
case 0:
{
lean_object* v___x_667_; 
v___x_667_ = lean_unsigned_to_nat(0u);
return v___x_667_;
}
case 1:
{
lean_object* v___x_668_; 
v___x_668_ = lean_unsigned_to_nat(1u);
return v___x_668_;
}
default: 
{
lean_object* v___x_669_; 
v___x_669_ = lean_unsigned_to_nat(2u);
return v___x_669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorIdx___boxed(lean_object* v_x_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Std_Http_URI_Port_ctorIdx(v_x_670_);
lean_dec(v_x_670_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg(lean_object* v_t_672_, lean_object* v_k_673_){
_start:
{
if (lean_obj_tag(v_t_672_) == 2)
{
uint16_t v_port_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_port_674_ = lean_ctor_get_uint16(v_t_672_, 0);
v___x_675_ = lean_box(v_port_674_);
v___x_676_ = lean_apply_1(v_k_673_, v___x_675_);
return v___x_676_;
}
else
{
return v_k_673_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___redArg___boxed(lean_object* v_t_677_, lean_object* v_k_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_677_, v_k_678_);
lean_dec(v_t_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim(lean_object* v_motive_680_, lean_object* v_ctorIdx_681_, lean_object* v_t_682_, lean_object* v_h_683_, lean_object* v_k_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_682_, v_k_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_ctorElim___boxed(lean_object* v_motive_686_, lean_object* v_ctorIdx_687_, lean_object* v_t_688_, lean_object* v_h_689_, lean_object* v_k_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_Http_URI_Port_ctorElim(v_motive_686_, v_ctorIdx_687_, v_t_688_, v_h_689_, v_k_690_);
lean_dec(v_t_688_);
lean_dec(v_ctorIdx_687_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg(lean_object* v_t_692_, lean_object* v_omitted_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_692_, v_omitted_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___redArg___boxed(lean_object* v_t_695_, lean_object* v_omitted_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_Http_URI_Port_omitted_elim___redArg(v_t_695_, v_omitted_696_);
lean_dec(v_t_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim(lean_object* v_motive_698_, lean_object* v_t_699_, lean_object* v_h_700_, lean_object* v_omitted_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_699_, v_omitted_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_omitted_elim___boxed(lean_object* v_motive_703_, lean_object* v_t_704_, lean_object* v_h_705_, lean_object* v_omitted_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Std_Http_URI_Port_omitted_elim(v_motive_703_, v_t_704_, v_h_705_, v_omitted_706_);
lean_dec(v_t_704_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg(lean_object* v_t_708_, lean_object* v_empty_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_708_, v_empty_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___redArg___boxed(lean_object* v_t_711_, lean_object* v_empty_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Std_Http_URI_Port_empty_elim___redArg(v_t_711_, v_empty_712_);
lean_dec(v_t_711_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim(lean_object* v_motive_714_, lean_object* v_t_715_, lean_object* v_h_716_, lean_object* v_empty_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_715_, v_empty_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_empty_elim___boxed(lean_object* v_motive_719_, lean_object* v_t_720_, lean_object* v_h_721_, lean_object* v_empty_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Std_Http_URI_Port_empty_elim(v_motive_719_, v_t_720_, v_h_721_, v_empty_722_);
lean_dec(v_t_720_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg(lean_object* v_t_724_, lean_object* v_value_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_724_, v_value_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___redArg___boxed(lean_object* v_t_727_, lean_object* v_value_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_Http_URI_Port_value_elim___redArg(v_t_727_, v_value_728_);
lean_dec(v_t_727_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim(lean_object* v_motive_730_, lean_object* v_t_731_, lean_object* v_h_732_, lean_object* v_value_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_Http_URI_Port_ctorElim___redArg(v_t_731_, v_value_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Port_value_elim___boxed(lean_object* v_motive_735_, lean_object* v_t_736_, lean_object* v_h_737_, lean_object* v_value_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_Http_URI_Port_value_elim(v_motive_735_, v_t_736_, v_h_737_, v_value_738_);
lean_dec(v_t_736_);
return v_res_739_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort_default(void){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = lean_box(0);
return v___x_740_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedPort(void){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = lean_box(0);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr(lean_object* v_x_754_, lean_object* v_prec_755_){
_start:
{
lean_object* v___y_757_; lean_object* v___y_764_; 
switch(lean_obj_tag(v_x_754_))
{
case 0:
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = lean_unsigned_to_nat(1024u);
v___x_771_ = lean_nat_dec_le(v___x_770_, v_prec_755_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
v___x_772_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_764_ = v___x_772_;
goto v___jp_763_;
}
else
{
lean_object* v___x_773_; 
v___x_773_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_764_ = v___x_773_;
goto v___jp_763_;
}
}
case 1:
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = lean_unsigned_to_nat(1024u);
v___x_775_ = lean_nat_dec_le(v___x_774_, v_prec_755_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
v___x_776_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_757_ = v___x_776_;
goto v___jp_756_;
}
else
{
lean_object* v___x_777_; 
v___x_777_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_757_ = v___x_777_;
goto v___jp_756_;
}
}
default: 
{
uint16_t v_port_778_; lean_object* v___y_780_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_port_778_ = lean_ctor_get_uint16(v_x_754_, 0);
v___x_790_ = lean_unsigned_to_nat(1024u);
v___x_791_ = lean_nat_dec_le(v___x_790_, v_prec_755_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; 
v___x_792_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_780_ = v___x_792_;
goto v___jp_779_;
}
else
{
lean_object* v___x_793_; 
v___x_793_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_780_ = v___x_793_;
goto v___jp_779_;
}
v___jp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_781_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__6));
v___x_782_ = lean_uint16_to_nat(v_port_778_);
v___x_783_ = l_Nat_reprFast(v___x_782_);
v___x_784_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
v___x_785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_781_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
lean_inc(v___y_780_);
v___x_786_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_786_, 0, v___y_780_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = 0;
v___x_788_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_788_, 0, v___x_786_);
lean_ctor_set_uint8(v___x_788_, sizeof(void*)*1, v___x_787_);
v___x_789_ = l_Repr_addAppParen(v___x_788_, v_prec_755_);
return v___x_789_;
}
}
}
v___jp_756_:
{
lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_758_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__1));
lean_inc(v___y_757_);
v___x_759_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_759_, 0, v___y_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = 0;
v___x_761_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_761_, 0, v___x_759_);
lean_ctor_set_uint8(v___x_761_, sizeof(void*)*1, v___x_760_);
v___x_762_ = l_Repr_addAppParen(v___x_761_, v_prec_755_);
return v___x_762_;
}
v___jp_763_:
{
lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_765_ = ((lean_object*)(l_Std_Http_URI_instReprPort_repr___closed__3));
lean_inc(v___y_764_);
v___x_766_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_766_, 0, v___y_764_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = 0;
v___x_768_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*1, v___x_767_);
v___x_769_ = l_Repr_addAppParen(v___x_768_, v_prec_755_);
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPort_repr___boxed(lean_object* v_x_794_, lean_object* v_prec_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Std_Http_URI_instReprPort_repr(v_x_794_, v_prec_795_);
lean_dec(v_prec_795_);
lean_dec(v_x_794_);
return v_res_796_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort_decEq(lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
switch(lean_obj_tag(v_x_799_))
{
case 0:
{
if (lean_obj_tag(v_x_800_) == 0)
{
uint8_t v___x_801_; 
v___x_801_ = 1;
return v___x_801_;
}
else
{
uint8_t v___x_802_; 
v___x_802_ = 0;
return v___x_802_;
}
}
case 1:
{
if (lean_obj_tag(v_x_800_) == 1)
{
uint8_t v___x_803_; 
v___x_803_ = 1;
return v___x_803_;
}
else
{
uint8_t v___x_804_; 
v___x_804_ = 0;
return v___x_804_;
}
}
default: 
{
uint16_t v_port_805_; uint8_t v___x_806_; 
v_port_805_ = lean_ctor_get_uint16(v_x_799_, 0);
v___x_806_ = 0;
if (lean_obj_tag(v_x_800_) == 2)
{
uint16_t v_port_807_; uint8_t v___x_808_; 
v_port_807_ = lean_ctor_get_uint16(v_x_800_, 0);
v___x_808_ = lean_uint16_dec_eq(v_port_805_, v_port_807_);
if (v___x_808_ == 0)
{
return v___x_806_;
}
else
{
return v___x_808_;
}
}
else
{
return v___x_806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort_decEq___boxed(lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
uint8_t v_res_811_; lean_object* v_r_812_; 
v_res_811_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_809_, v_x_810_);
lean_dec(v_x_810_);
lean_dec(v_x_809_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instDecidableEqPort(lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_x_813_, v_x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instDecidableEqPort___boxed(lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
uint8_t v_res_818_; lean_object* v_r_819_; 
v_res_818_ = l_Std_Http_URI_instDecidableEqPort(v_x_816_, v_x_817_);
lean_dec(v_x_817_);
lean_dec(v_x_816_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_820_ = lean_box(0);
v___x_821_ = l_Std_Http_URI_instInhabitedHost_default;
v___x_822_ = lean_box(0);
v___x_823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_821_);
lean_ctor_set(v___x_823_, 2, v___x_820_);
return v___x_823_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority_default(void){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = lean_obj_once(&l_Std_Http_URI_instInhabitedAuthority_default___closed__0, &l_Std_Http_URI_instInhabitedAuthority_default___closed__0_once, _init_l_Std_Http_URI_instInhabitedAuthority_default___closed__0);
return v___x_824_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedAuthority(void){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Std_Http_URI_instInhabitedAuthority_default;
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
if (lean_obj_tag(v_x_826_) == 0)
{
lean_object* v___x_828_; 
v___x_828_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_828_;
}
else
{
lean_object* v_val_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_val_829_ = lean_ctor_get(v_x_826_, 0);
lean_inc(v_val_829_);
lean_dec_ref(v_x_826_);
v___x_830_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_831_ = l_Std_Http_URI_instReprUserInfo_repr___redArg(v_val_829_);
v___x_832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = l_Repr_addAppParen(v___x_832_, v_x_827_);
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0___boxed(lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_x_834_, v_x_835_);
lean_dec(v_x_835_);
return v_res_836_;
}
}
static lean_object* _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_unsigned_to_nat(8u);
v___x_850_ = lean_nat_to_int(v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___redArg(lean_object* v_x_854_){
_start:
{
lean_object* v_userInfo_855_; lean_object* v_host_856_; lean_object* v_port_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v_ctr_877_; lean_object* v_a_878_; 
v_userInfo_855_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_userInfo_855_);
v_host_856_ = lean_ctor_get(v_x_854_, 1);
lean_inc_ref(v_host_856_);
v_port_857_ = lean_ctor_get(v_x_854_, 2);
lean_inc(v_port_857_);
lean_dec_ref(v_x_854_);
v___x_858_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_859_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__3));
v___x_860_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = l_Option_repr___at___00Std_Http_URI_instReprAuthority_repr_spec__0(v_userInfo_855_, v___x_861_);
v___x_863_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_860_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = 0;
v___x_865_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*1, v___x_864_);
v___x_866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_859_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = lean_box(1);
v___x_870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__5));
v___x_872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_870_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v___x_858_);
v___x_874_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_875_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
switch(lean_obj_tag(v_host_856_))
{
case 0:
{
lean_object* v_name_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_915_; 
v_name_906_ = lean_ctor_get(v_host_856_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v_host_856_);
if (v_isSharedCheck_915_ == 0)
{
v___x_908_ = v_host_856_;
v_isShared_909_ = v_isSharedCheck_915_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_name_906_);
lean_dec(v_host_856_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_915_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_910_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__1));
v___x_911_ = l_String_quote(v_name_906_);
if (v_isShared_909_ == 0)
{
lean_ctor_set_tag(v___x_908_, 3);
lean_ctor_set(v___x_908_, 0, v___x_911_);
v___x_913_ = v___x_908_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
v_ctr_877_ = v___x_910_;
v_a_878_ = v___x_913_;
goto v___jp_876_;
}
}
}
case 1:
{
lean_object* v_ipv4_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_925_; 
v_ipv4_916_ = lean_ctor_get(v_host_856_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v_host_856_);
if (v_isSharedCheck_925_ == 0)
{
v___x_918_ = v_host_856_;
v_isShared_919_ = v_isSharedCheck_925_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_ipv4_916_);
lean_dec(v_host_856_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_925_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_920_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__2));
v___x_921_ = lean_uv_ntop_v4(v_ipv4_916_);
lean_dec_ref(v_ipv4_916_);
if (v_isShared_919_ == 0)
{
lean_ctor_set_tag(v___x_918_, 3);
lean_ctor_set(v___x_918_, 0, v___x_921_);
v___x_923_ = v___x_918_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
v_ctr_877_ = v___x_920_;
v_a_878_ = v___x_923_;
goto v___jp_876_;
}
}
}
default: 
{
lean_object* v_ipv6_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_935_; 
v_ipv6_926_ = lean_ctor_get(v_host_856_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v_host_856_);
if (v_isSharedCheck_935_ == 0)
{
v___x_928_ = v_host_856_;
v_isShared_929_ = v_isSharedCheck_935_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_ipv6_926_);
lean_dec(v_host_856_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_935_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_930_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__3));
v___x_931_ = lean_uv_ntop_v6(v_ipv6_926_);
lean_dec_ref(v_ipv6_926_);
if (v_isShared_929_ == 0)
{
lean_ctor_set_tag(v___x_928_, 3);
lean_ctor_set(v___x_928_, 0, v___x_931_);
v___x_933_ = v___x_928_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
v_ctr_877_ = v___x_930_;
v_a_878_ = v___x_933_;
goto v___jp_876_;
}
}
}
}
v___jp_876_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_879_ = ((lean_object*)(l_Std_Http_URI_instReprHost___lam__0___closed__0));
v___x_880_ = lean_string_append(v___x_879_, v_ctr_877_);
v___x_881_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
v___x_882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v___x_869_);
v___x_883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v_a_878_);
v___x_884_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_875_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set_uint8(v___x_885_, sizeof(void*)*1, v___x_864_);
v___x_886_ = l_Repr_addAppParen(v___x_885_, v___x_861_);
v___x_887_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_874_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set_uint8(v___x_888_, sizeof(void*)*1, v___x_864_);
v___x_889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_873_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v___x_867_);
v___x_891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v___x_869_);
v___x_892_ = ((lean_object*)(l_Std_Http_URI_instReprAuthority_repr___redArg___closed__8));
v___x_893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v___x_858_);
v___x_895_ = l_Std_Http_URI_instReprPort_repr(v_port_857_, v___x_861_);
lean_dec(v_port_857_);
v___x_896_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_874_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*1, v___x_864_);
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_894_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_900_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___x_898_);
v___x_902_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_899_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set_uint8(v___x_905_, sizeof(void*)*1, v___x_864_);
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr(lean_object* v_x_936_, lean_object* v_prec_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_x_936_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprAuthority_repr___boxed(lean_object* v_x_939_, lean_object* v_prec_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Std_Http_URI_instReprAuthority_repr(v_x_939_, v_prec_940_);
lean_dec(v_prec_940_);
return v_res_941_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
if (lean_obj_tag(v_x_944_) == 0)
{
if (lean_obj_tag(v_x_945_) == 0)
{
uint8_t v___x_946_; 
v___x_946_ = 1;
return v___x_946_;
}
else
{
uint8_t v___x_947_; 
v___x_947_ = 0;
return v___x_947_;
}
}
else
{
if (lean_obj_tag(v_x_945_) == 0)
{
uint8_t v___x_948_; 
v___x_948_ = 0;
return v___x_948_;
}
else
{
lean_object* v_val_949_; lean_object* v_val_950_; uint8_t v___x_951_; 
v_val_949_ = lean_ctor_get(v_x_944_, 0);
v_val_950_ = lean_ctor_get(v_x_945_, 0);
v___x_951_ = l_Std_Http_URI_instBEqUserInfo_beq(v_val_949_, v_val_950_);
return v___x_951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0___boxed(lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
uint8_t v_res_954_; lean_object* v_r_955_; 
v_res_954_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_x_952_, v_x_953_);
lean_dec(v_x_953_);
lean_dec(v_x_952_);
v_r_955_ = lean_box(v_res_954_);
return v_r_955_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqAuthority_beq(lean_object* v_x_956_, lean_object* v_x_957_){
_start:
{
lean_object* v_userInfo_958_; lean_object* v_host_959_; lean_object* v_port_960_; lean_object* v_userInfo_961_; lean_object* v_host_962_; lean_object* v_port_963_; uint8_t v___x_964_; 
v_userInfo_958_ = lean_ctor_get(v_x_956_, 0);
v_host_959_ = lean_ctor_get(v_x_956_, 1);
v_port_960_ = lean_ctor_get(v_x_956_, 2);
v_userInfo_961_ = lean_ctor_get(v_x_957_, 0);
v_host_962_ = lean_ctor_get(v_x_957_, 1);
v_port_963_ = lean_ctor_get(v_x_957_, 2);
v___x_964_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_userInfo_958_, v_userInfo_961_);
if (v___x_964_ == 0)
{
return v___x_964_;
}
else
{
uint8_t v___x_965_; 
v___x_965_ = l_Std_Http_URI_instBEqHost_beq(v_host_959_, v_host_962_);
if (v___x_965_ == 0)
{
return v___x_965_;
}
else
{
uint8_t v___x_966_; 
v___x_966_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_960_, v_port_963_);
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqAuthority_beq___boxed(lean_object* v_x_967_, lean_object* v_x_968_){
_start:
{
uint8_t v_res_969_; lean_object* v_r_970_; 
v_res_969_ = l_Std_Http_URI_instBEqAuthority_beq(v_x_967_, v_x_968_);
lean_dec_ref(v_x_968_);
lean_dec_ref(v_x_967_);
v_r_970_ = lean_box(v_res_969_);
return v_r_970_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringAuthority___lam__0(lean_object* v_auth_976_){
_start:
{
lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v_userInfo_983_; lean_object* v_host_984_; lean_object* v_port_985_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_997_; 
v_userInfo_983_ = lean_ctor_get(v_auth_976_, 0);
lean_inc(v_userInfo_983_);
v_host_984_ = lean_ctor_get(v_auth_976_, 1);
lean_inc_ref(v_host_984_);
v_port_985_ = lean_ctor_get(v_auth_976_, 2);
lean_inc(v_port_985_);
lean_dec_ref(v_auth_976_);
if (lean_obj_tag(v_userInfo_983_) == 0)
{
lean_object* v___x_1007_; 
v___x_1007_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_997_ = v___x_1007_;
goto v___jp_996_;
}
else
{
lean_object* v_val_1008_; lean_object* v_password_1009_; 
v_val_1008_ = lean_ctor_get(v_userInfo_983_, 0);
lean_inc(v_val_1008_);
lean_dec_ref(v_userInfo_983_);
v_password_1009_ = lean_ctor_get(v_val_1008_, 1);
if (lean_obj_tag(v_password_1009_) == 0)
{
lean_object* v_username_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_username_1010_ = lean_ctor_get(v_val_1008_, 0);
lean_inc_ref(v_username_1010_);
lean_dec(v_val_1008_);
v___x_1011_ = lean_string_from_utf8_unchecked(v_username_1010_);
v___x_1012_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1013_ = lean_string_append(v___x_1011_, v___x_1012_);
v___y_997_ = v___x_1013_;
goto v___jp_996_;
}
else
{
lean_object* v_username_1014_; lean_object* v_val_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_inc_ref(v_password_1009_);
v_username_1014_ = lean_ctor_get(v_val_1008_, 0);
lean_inc_ref(v_username_1014_);
lean_dec(v_val_1008_);
v_val_1015_ = lean_ctor_get(v_password_1009_, 0);
lean_inc(v_val_1015_);
lean_dec_ref(v_password_1009_);
v___x_1016_ = lean_string_from_utf8_unchecked(v_username_1014_);
v___x_1017_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_1018_ = lean_string_append(v___x_1016_, v___x_1017_);
v___x_1019_ = lean_string_from_utf8_unchecked(v_val_1015_);
v___x_1020_ = lean_string_append(v___x_1018_, v___x_1019_);
lean_dec_ref(v___x_1019_);
v___x_1021_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_1022_ = lean_string_append(v___x_1020_, v___x_1021_);
v___y_997_ = v___x_1022_;
goto v___jp_996_;
}
}
v___jp_977_:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_string_append(v___y_978_, v___y_979_);
lean_dec_ref(v___y_979_);
v___x_982_ = lean_string_append(v___x_981_, v___y_980_);
lean_dec_ref(v___y_980_);
return v___x_982_;
}
v___jp_986_:
{
switch(lean_obj_tag(v_port_985_))
{
case 0:
{
lean_object* v___x_989_; 
v___x_989_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_978_ = v___y_987_;
v___y_979_ = v___y_988_;
v___y_980_ = v___x_989_;
goto v___jp_977_;
}
case 1:
{
lean_object* v___x_990_; 
v___x_990_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_978_ = v___y_987_;
v___y_979_ = v___y_988_;
v___y_980_ = v___x_990_;
goto v___jp_977_;
}
default: 
{
uint16_t v_port_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_port_991_ = lean_ctor_get_uint16(v_port_985_, 0);
lean_dec_ref(v_port_985_);
v___x_992_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_993_ = lean_uint16_to_nat(v_port_991_);
v___x_994_ = l_Nat_reprFast(v___x_993_);
v___x_995_ = lean_string_append(v___x_992_, v___x_994_);
lean_dec_ref(v___x_994_);
v___y_978_ = v___y_987_;
v___y_979_ = v___y_988_;
v___y_980_ = v___x_995_;
goto v___jp_977_;
}
}
}
v___jp_996_:
{
switch(lean_obj_tag(v_host_984_))
{
case 0:
{
lean_object* v_name_998_; 
v_name_998_ = lean_ctor_get(v_host_984_, 0);
lean_inc_ref(v_name_998_);
lean_dec_ref(v_host_984_);
v___y_987_ = v___y_997_;
v___y_988_ = v_name_998_;
goto v___jp_986_;
}
case 1:
{
lean_object* v_ipv4_999_; lean_object* v___x_1000_; 
v_ipv4_999_ = lean_ctor_get(v_host_984_, 0);
lean_inc_ref(v_ipv4_999_);
lean_dec_ref(v_host_984_);
v___x_1000_ = lean_uv_ntop_v4(v_ipv4_999_);
lean_dec_ref(v_ipv4_999_);
v___y_987_ = v___y_997_;
v___y_988_ = v___x_1000_;
goto v___jp_986_;
}
default: 
{
lean_object* v_ipv6_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_ipv6_1001_ = lean_ctor_get(v_host_984_, 0);
lean_inc_ref(v_ipv6_1001_);
lean_dec_ref(v_host_984_);
v___x_1002_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_1003_ = lean_uv_ntop_v6(v_ipv6_1001_);
lean_dec_ref(v_ipv6_1001_);
v___x_1004_ = lean_string_append(v___x_1002_, v___x_1003_);
lean_dec_ref(v___x_1003_);
v___x_1005_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_1006_ = lean_string_append(v___x_1004_, v___x_1005_);
v___y_987_ = v___y_997_;
v___y_988_ = v___x_1006_;
goto v___jp_986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1032_, lean_object* v_x_1033_, lean_object* v_x_1034_){
_start:
{
if (lean_obj_tag(v_x_1034_) == 0)
{
lean_dec(v_x_1032_);
return v_x_1033_;
}
else
{
lean_object* v_head_1035_; lean_object* v_tail_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1048_; 
v_head_1035_ = lean_ctor_get(v_x_1034_, 0);
v_tail_1036_ = lean_ctor_get(v_x_1034_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1038_ = v_x_1034_;
v_isShared_1039_ = v_isSharedCheck_1048_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_tail_1036_);
lean_inc(v_head_1035_);
lean_dec(v_x_1034_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1048_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
lean_inc(v_x_1032_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 5);
lean_ctor_set(v___x_1038_, 1, v_x_1032_);
lean_ctor_set(v___x_1038_, 0, v_x_1033_);
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_x_1033_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_x_1032_);
v___x_1041_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1042_ = lean_string_from_utf8_unchecked(v_head_1035_);
v___x_1043_ = l_String_quote(v___x_1042_);
v___x_1044_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
v___x_1045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1041_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v_x_1033_ = v___x_1045_;
v_x_1034_ = v_tail_1036_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_){
_start:
{
if (lean_obj_tag(v_x_1051_) == 0)
{
lean_dec(v_x_1049_);
return v_x_1050_;
}
else
{
lean_object* v_head_1052_; lean_object* v_tail_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1065_; 
v_head_1052_ = lean_ctor_get(v_x_1051_, 0);
v_tail_1053_ = lean_ctor_get(v_x_1051_, 1);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_x_1051_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1055_ = v_x_1051_;
v_isShared_1056_ = v_isSharedCheck_1065_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_tail_1053_);
lean_inc(v_head_1052_);
lean_dec(v_x_1051_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1065_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
lean_inc(v_x_1049_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 5);
lean_ctor_set(v___x_1055_, 1, v_x_1049_);
lean_ctor_set(v___x_1055_, 0, v_x_1050_);
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_x_1050_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_x_1049_);
v___x_1058_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1059_ = lean_string_from_utf8_unchecked(v_head_1052_);
v___x_1060_ = l_String_quote(v___x_1059_);
v___x_1061_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
v___x_1062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1058_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1_spec__2(v_x_1049_, v___x_1062_, v_tail_1053_);
return v___x_1063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_string_from_utf8_unchecked(v___y_1066_);
v___x_1068_ = l_String_quote(v___x_1067_);
v___x_1069_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(lean_object* v_x_1070_, lean_object* v_x_1071_){
_start:
{
if (lean_obj_tag(v_x_1070_) == 0)
{
lean_object* v___x_1072_; 
lean_dec(v_x_1071_);
v___x_1072_ = lean_box(0);
return v___x_1072_;
}
else
{
lean_object* v_tail_1073_; 
v_tail_1073_ = lean_ctor_get(v_x_1070_, 1);
if (lean_obj_tag(v_tail_1073_) == 0)
{
lean_object* v_head_1074_; lean_object* v___x_1075_; 
lean_dec(v_x_1071_);
v_head_1074_ = lean_ctor_get(v_x_1070_, 0);
lean_inc(v_head_1074_);
lean_dec_ref(v_x_1070_);
v___x_1075_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1074_);
return v___x_1075_;
}
else
{
lean_object* v_head_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_inc(v_tail_1073_);
v_head_1076_ = lean_ctor_get(v_x_1070_, 0);
lean_inc(v_head_1076_);
lean_dec_ref(v_x_1070_);
v___x_1077_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0___lam__0(v_head_1076_);
v___x_1078_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0_spec__1(v_x_1071_, v___x_1077_, v_tail_1073_);
return v___x_1078_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__0));
v___x_1084_ = lean_string_length(v___x_1083_);
return v___x_1084_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__2);
v___x_1086_ = lean_nat_to_int(v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(lean_object* v_xs_1094_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1095_ = lean_array_get_size(v_xs_1094_);
v___x_1096_ = lean_unsigned_to_nat(0u);
v___x_1097_ = lean_nat_dec_eq(v___x_1095_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1098_ = lean_array_to_list(v_xs_1094_);
v___x_1099_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1100_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0_spec__0(v___x_1098_, v___x_1099_);
v___x_1101_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1102_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v___x_1100_);
v___x_1104_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1101_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = l_Std_Format_fill(v___x_1106_);
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; 
lean_dec_ref(v_xs_1094_);
v___x_1108_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___redArg(lean_object* v_x_1121_){
_start:
{
lean_object* v_segments_1122_; uint8_t v_absolute_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1155_; 
v_segments_1122_ = lean_ctor_get(v_x_1121_, 0);
v_absolute_1123_ = lean_ctor_get_uint8(v_x_1121_, sizeof(void*)*1);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_x_1121_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1125_ = v_x_1121_;
v_isShared_1126_ = v_isSharedCheck_1155_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_segments_1122_);
lean_dec(v_x_1121_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1155_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; lean_object* v___x_1134_; 
v___x_1127_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1128_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__3));
v___x_1129_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_1130_ = l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0(v_segments_1122_);
v___x_1131_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = 0;
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 6);
lean_ctor_set(v___x_1125_, 0, v___x_1131_);
v___x_1134_ = v___x_1125_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1131_);
v___x_1134_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*1, v___x_1132_);
v___x_1135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1128_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = lean_box(1);
v___x_1139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = ((lean_object*)(l_Std_Http_URI_instReprPath_repr___redArg___closed__5));
v___x_1141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
lean_ctor_set(v___x_1142_, 1, v___x_1127_);
v___x_1143_ = l_Bool_repr___redArg(v_absolute_1123_);
v___x_1144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1129_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*1, v___x_1132_);
v___x_1146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1142_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_1148_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_1149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
lean_ctor_set(v___x_1149_, 1, v___x_1146_);
v___x_1150_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_1151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1147_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set_uint8(v___x_1153_, sizeof(void*)*1, v___x_1132_);
return v___x_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr(lean_object* v_x_1156_, lean_object* v_prec_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Std_Http_URI_instReprPath_repr___redArg(v_x_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprPath_repr___boxed(lean_object* v_x_1159_, lean_object* v_prec_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Std_Http_URI_instReprPath_repr(v_x_1159_, v_prec_1160_);
lean_dec(v_prec_1160_);
return v_res_1161_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(lean_object* v_xs_1164_, lean_object* v_ys_1165_, lean_object* v_x_1166_){
_start:
{
lean_object* v_zero_1167_; uint8_t v_isZero_1168_; 
v_zero_1167_ = lean_unsigned_to_nat(0u);
v_isZero_1168_ = lean_nat_dec_eq(v_x_1166_, v_zero_1167_);
if (v_isZero_1168_ == 1)
{
lean_dec(v_x_1166_);
return v_isZero_1168_;
}
else
{
lean_object* v_one_1169_; lean_object* v_n_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v_one_1169_ = lean_unsigned_to_nat(1u);
v_n_1170_ = lean_nat_sub(v_x_1166_, v_one_1169_);
lean_dec(v_x_1166_);
v___x_1171_ = lean_array_fget_borrowed(v_xs_1164_, v_n_1170_);
v___x_1172_ = lean_array_fget_borrowed(v_ys_1165_, v_n_1170_);
v___x_1173_ = lean_sarray_dec_eq(v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_dec(v_n_1170_);
return v___x_1173_;
}
else
{
v_x_1166_ = v_n_1170_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg___boxed(lean_object* v_xs_1175_, lean_object* v_ys_1176_, lean_object* v_x_1177_){
_start:
{
uint8_t v_res_1178_; lean_object* v_r_1179_; 
v_res_1178_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1175_, v_ys_1176_, v_x_1177_);
lean_dec_ref(v_ys_1176_);
lean_dec_ref(v_xs_1175_);
v_r_1179_ = lean_box(v_res_1178_);
return v_r_1179_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqPath_beq(lean_object* v_x_1180_, lean_object* v_x_1181_){
_start:
{
lean_object* v_segments_1182_; uint8_t v_absolute_1183_; lean_object* v_segments_1184_; uint8_t v_absolute_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v_segments_1182_ = lean_ctor_get(v_x_1180_, 0);
v_absolute_1183_ = lean_ctor_get_uint8(v_x_1180_, sizeof(void*)*1);
v_segments_1184_ = lean_ctor_get(v_x_1181_, 0);
v_absolute_1185_ = lean_ctor_get_uint8(v_x_1181_, sizeof(void*)*1);
v___x_1186_ = lean_array_get_size(v_segments_1182_);
v___x_1187_ = lean_array_get_size(v_segments_1184_);
v___x_1188_ = lean_nat_dec_eq(v___x_1186_, v___x_1187_);
if (v___x_1188_ == 0)
{
return v___x_1188_;
}
else
{
uint8_t v___x_1189_; 
v___x_1189_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_segments_1182_, v_segments_1184_, v___x_1186_);
if (v___x_1189_ == 0)
{
return v___x_1189_;
}
else
{
if (v_absolute_1183_ == 0)
{
if (v_absolute_1185_ == 0)
{
return v___x_1189_;
}
else
{
return v_absolute_1183_;
}
}
else
{
return v_absolute_1185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqPath_beq___boxed(lean_object* v_x_1190_, lean_object* v_x_1191_){
_start:
{
uint8_t v_res_1192_; lean_object* v_r_1193_; 
v_res_1192_ = l_Std_Http_URI_instBEqPath_beq(v_x_1190_, v_x_1191_);
lean_dec_ref(v_x_1191_);
lean_dec_ref(v_x_1190_);
v_r_1193_ = lean_box(v_res_1192_);
return v_r_1193_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(lean_object* v_xs_1194_, lean_object* v_ys_1195_, lean_object* v_hsz_1196_, lean_object* v_x_1197_, lean_object* v_x_1198_){
_start:
{
uint8_t v___x_1199_; 
v___x_1199_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___redArg(v_xs_1194_, v_ys_1195_, v_x_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0___boxed(lean_object* v_xs_1200_, lean_object* v_ys_1201_, lean_object* v_hsz_1202_, lean_object* v_x_1203_, lean_object* v_x_1204_){
_start:
{
uint8_t v_res_1205_; lean_object* v_r_1206_; 
v_res_1205_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqPath_beq_spec__0(v_xs_1200_, v_ys_1201_, v_hsz_1202_, v_x_1203_, v_x_1204_);
lean_dec_ref(v_ys_1201_);
lean_dec_ref(v_xs_1200_);
v_r_1206_ = lean_box(v_res_1205_);
return v_r_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__0(lean_object* v_x_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_string_from_utf8_unchecked(v_x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instToStringPath___lam__1(lean_object* v___f_1231_, lean_object* v_path_1232_){
_start:
{
lean_object* v_segments_1233_; uint8_t v_absolute_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; size_t v_sz_1237_; size_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v_result_1241_; 
v_segments_1233_ = lean_ctor_get(v_path_1232_, 0);
lean_inc_ref(v_segments_1233_);
v_absolute_1234_ = lean_ctor_get_uint8(v_path_1232_, sizeof(void*)*1);
lean_dec_ref(v_path_1232_);
v___x_1235_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_1236_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_1237_ = lean_array_size(v_segments_1233_);
v___x_1238_ = ((size_t)0ULL);
v___x_1239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1236_, v___f_1231_, v_sz_1237_, v___x_1238_, v_segments_1233_);
v___x_1240_ = lean_array_to_list(v___x_1239_);
v_result_1241_ = l_String_intercalate(v___x_1235_, v___x_1240_);
if (v_absolute_1234_ == 0)
{
return v_result_1241_;
}
else
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_string_append(v___x_1235_, v_result_1241_);
lean_dec_ref(v_result_1241_);
return v___x_1242_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Path_isEmpty(lean_object* v_p_1247_){
_start:
{
lean_object* v_segments_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_segments_1248_ = lean_ctor_get(v_p_1247_, 0);
v___x_1249_ = lean_array_get_size(v_segments_1248_);
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = lean_nat_dec_eq(v___x_1249_, v___x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_isEmpty___boxed(lean_object* v_p_1252_){
_start:
{
uint8_t v_res_1253_; lean_object* v_r_1254_; 
v_res_1253_ = l_Std_Http_URI_Path_isEmpty(v_p_1252_);
lean_dec_ref(v_p_1252_);
v_r_1254_ = lean_box(v_res_1253_);
return v_r_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parent(lean_object* v_p_1255_){
_start:
{
lean_object* v_segments_1256_; uint8_t v_absolute_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v_segments_1256_ = lean_ctor_get(v_p_1255_, 0);
v_absolute_1257_ = lean_ctor_get_uint8(v_p_1255_, sizeof(void*)*1);
v___x_1258_ = lean_array_get_size(v_segments_1256_);
v___x_1259_ = lean_unsigned_to_nat(0u);
v___x_1260_ = lean_nat_dec_eq(v___x_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1268_; 
lean_inc_ref(v_segments_1256_);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_p_1255_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; 
v_unused_1269_ = lean_ctor_get(v_p_1255_, 0);
lean_dec(v_unused_1269_);
v___x_1262_ = v_p_1255_;
v_isShared_1263_ = v_isSharedCheck_1268_;
goto v_resetjp_1261_;
}
else
{
lean_dec(v_p_1255_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1268_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1264_ = lean_array_pop(v_segments_1256_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1264_);
v___x_1266_ = v___x_1262_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*1, v_absolute_1257_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
else
{
return v_p_1255_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join(lean_object* v_p1_1270_, lean_object* v_p2_1271_){
_start:
{
uint8_t v_absolute_1272_; 
v_absolute_1272_ = lean_ctor_get_uint8(v_p2_1271_, sizeof(void*)*1);
if (v_absolute_1272_ == 0)
{
lean_object* v_segments_1273_; lean_object* v_segments_1274_; uint8_t v_absolute_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1283_; 
v_segments_1273_ = lean_ctor_get(v_p2_1271_, 0);
v_segments_1274_ = lean_ctor_get(v_p1_1270_, 0);
v_absolute_1275_ = lean_ctor_get_uint8(v_p1_1270_, sizeof(void*)*1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_p1_1270_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1277_ = v_p1_1270_;
v_isShared_1278_ = v_isSharedCheck_1283_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_segments_1274_);
lean_dec(v_p1_1270_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1283_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1279_ = l_Array_append___redArg(v_segments_1274_, v_segments_1273_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1279_);
v___x_1281_ = v___x_1277_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
lean_ctor_set_uint8(v_reuseFailAlloc_1282_, sizeof(void*)*1, v_absolute_1275_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
else
{
lean_dec_ref(v_p1_1270_);
lean_inc_ref(v_p2_1271_);
return v_p2_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_join___boxed(lean_object* v_p1_1284_, lean_object* v_p2_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Std_Http_URI_Path_join(v_p1_1284_, v_p2_1285_);
lean_dec_ref(v_p2_1285_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append(lean_object* v_p_1287_, lean_object* v_segment_1288_){
_start:
{
lean_object* v_segments_1289_; uint8_t v_absolute_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1299_; 
v_segments_1289_ = lean_ctor_get(v_p_1287_, 0);
v_absolute_1290_ = lean_ctor_get_uint8(v_p_1287_, sizeof(void*)*1);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_p_1287_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1292_ = v_p_1287_;
v_isShared_1293_ = v_isSharedCheck_1299_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_segments_1289_);
lean_dec(v_p_1287_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1299_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1294_ = l_Std_Http_URI_EncodedSegment_encode(v_segment_1288_);
v___x_1295_ = lean_array_push(v_segments_1289_, v___x_1294_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1295_);
v___x_1297_ = v___x_1292_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1298_, sizeof(void*)*1, v_absolute_1290_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_append___boxed(lean_object* v_p_1300_, lean_object* v_segment_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Std_Http_URI_Path_append(v_p_1300_, v_segment_1301_);
lean_dec_ref(v_segment_1301_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_appendEncoded(lean_object* v_p_1303_, lean_object* v_segment_1304_){
_start:
{
lean_object* v_segments_1305_; uint8_t v_absolute_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1314_; 
v_segments_1305_ = lean_ctor_get(v_p_1303_, 0);
v_absolute_1306_ = lean_ctor_get_uint8(v_p_1303_, sizeof(void*)*1);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_p_1303_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1308_ = v_p_1303_;
v_isShared_1309_ = v_isSharedCheck_1314_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_segments_1305_);
lean_dec(v_p_1303_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1314_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1310_ = lean_array_push(v_segments_1305_, v_segment_1304_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1310_);
v___x_1312_ = v___x_1308_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
lean_ctor_set_uint8(v_reuseFailAlloc_1313_, sizeof(void*)*1, v_absolute_1306_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(lean_object* v_input_1316_, lean_object* v_output_1317_){
_start:
{
if (lean_obj_tag(v_input_1316_) == 0)
{
lean_object* v___x_1318_; 
v___x_1318_ = l_List_reverse___redArg(v_output_1317_);
return v___x_1318_;
}
else
{
lean_object* v_head_1319_; lean_object* v_tail_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1337_; 
v_head_1319_ = lean_ctor_get(v_input_1316_, 0);
v_tail_1320_ = lean_ctor_get(v_input_1316_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_input_1316_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1322_ = v_input_1316_;
v_isShared_1323_ = v_isSharedCheck_1337_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_tail_1320_);
lean_inc(v_head_1319_);
lean_dec(v_input_1316_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1337_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
lean_inc(v_head_1319_);
v___x_1324_ = lean_string_from_utf8_unchecked(v_head_1319_);
v___x_1325_ = ((lean_object*)(l_Std_Http_URI_DomainName_ofString_x3f___closed__0));
v___x_1326_ = lean_string_dec_eq(v___x_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop___closed__0));
v___x_1328_ = lean_string_dec_eq(v___x_1324_, v___x_1327_);
lean_dec_ref(v___x_1324_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1330_; 
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 1, v_output_1317_);
v___x_1330_ = v___x_1322_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_head_1319_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_output_1317_);
v___x_1330_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
v_input_1316_ = v_tail_1320_;
v_output_1317_ = v___x_1330_;
goto _start;
}
}
else
{
lean_del_object(v___x_1322_);
lean_dec(v_head_1319_);
if (lean_obj_tag(v_output_1317_) == 0)
{
v_input_1316_ = v_tail_1320_;
goto _start;
}
else
{
lean_object* v_tail_1334_; 
v_tail_1334_ = lean_ctor_get(v_output_1317_, 1);
lean_inc(v_tail_1334_);
lean_dec_ref(v_output_1317_);
v_input_1316_ = v_tail_1320_;
v_output_1317_ = v_tail_1334_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_1324_);
lean_del_object(v___x_1322_);
lean_dec(v_head_1319_);
v_input_1316_ = v_tail_1320_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_normalize(lean_object* v_p_1338_){
_start:
{
lean_object* v_segments_1339_; uint8_t v_absolute_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1351_; 
v_segments_1339_ = lean_ctor_get(v_p_1338_, 0);
v_absolute_1340_ = lean_ctor_get_uint8(v_p_1338_, sizeof(void*)*1);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_p_1338_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1342_ = v_p_1338_;
v_isShared_1343_ = v_isSharedCheck_1351_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_segments_1339_);
lean_dec(v_p_1338_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1351_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1344_ = lean_array_to_list(v_segments_1339_);
v___x_1345_ = lean_box(0);
v___x_1346_ = l___private_Std_Internal_Http_Data_URI_Basic_0__Std_Http_URI_Path_normalize_loop(v___x_1344_, v___x_1345_);
v___x_1347_ = lean_array_mk(v___x_1346_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1347_);
v___x_1349_ = v___x_1342_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
lean_ctor_set_uint8(v_reuseFailAlloc_1350_, sizeof(void*)*1, v_absolute_1340_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(size_t v_sz_1352_, size_t v_i_1353_, lean_object* v_bs_1354_){
_start:
{
uint8_t v___x_1355_; 
v___x_1355_ = lean_usize_dec_lt(v_i_1353_, v_sz_1352_);
if (v___x_1355_ == 0)
{
return v_bs_1354_;
}
else
{
lean_object* v_v_1356_; lean_object* v___x_1357_; lean_object* v_bs_x27_1358_; lean_object* v___y_1360_; lean_object* v___x_1365_; 
v_v_1356_ = lean_array_uget(v_bs_1354_, v_i_1353_);
v___x_1357_ = lean_unsigned_to_nat(0u);
v_bs_x27_1358_ = lean_array_uset(v_bs_1354_, v_i_1353_, v___x_1357_);
v___x_1365_ = l_Std_Http_URI_EncodedSegment_decode(v_v_1356_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_string_from_utf8_unchecked(v_v_1356_);
v___y_1360_ = v___x_1366_;
goto v___jp_1359_;
}
else
{
lean_object* v_val_1367_; 
lean_dec(v_v_1356_);
v_val_1367_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_val_1367_);
lean_dec_ref(v___x_1365_);
v___y_1360_ = v_val_1367_;
goto v___jp_1359_;
}
v___jp_1359_:
{
size_t v___x_1361_; size_t v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = ((size_t)1ULL);
v___x_1362_ = lean_usize_add(v_i_1353_, v___x_1361_);
v___x_1363_ = lean_array_uset(v_bs_x27_1358_, v_i_1353_, v___y_1360_);
v_i_1353_ = v___x_1362_;
v_bs_1354_ = v___x_1363_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0___boxed(lean_object* v_sz_1368_, lean_object* v_i_1369_, lean_object* v_bs_1370_){
_start:
{
size_t v_sz_boxed_1371_; size_t v_i_boxed_1372_; lean_object* v_res_1373_; 
v_sz_boxed_1371_ = lean_unbox_usize(v_sz_1368_);
lean_dec(v_sz_1368_);
v_i_boxed_1372_ = lean_unbox_usize(v_i_1369_);
lean_dec(v_i_1369_);
v_res_1373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_boxed_1371_, v_i_boxed_1372_, v_bs_1370_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_toDecodedSegments(lean_object* v_p_1374_){
_start:
{
lean_object* v_segments_1375_; size_t v_sz_1376_; size_t v___x_1377_; lean_object* v___x_1378_; 
v_segments_1375_ = lean_ctor_get(v_p_1374_, 0);
lean_inc_ref(v_segments_1375_);
lean_dec_ref(v_p_1374_);
v_sz_1376_ = lean_array_size(v_segments_1375_);
v___x_1377_ = ((size_t)0ULL);
v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Path_toDecodedSegments_spec__0(v_sz_1376_, v___x_1377_, v_segments_1375_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___redArg(lean_object* v_xs_1387_){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1389_ = l_Array_repr___redArg(v___x_1388_, v_xs_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1(lean_object* v_xs_1390_, lean_object* v_x_1391_){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = ((lean_object*)(l_Std_Http_URI_instReprQuery___aux__1___redArg___closed__3));
v___x_1393_ = l_Array_repr___redArg(v___x_1392_, v_xs_1390_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___aux__1___boxed(lean_object* v_xs_1394_, lean_object* v_x_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Std_Http_URI_instReprQuery___aux__1(v_xs_1394_, v_x_1395_);
lean_dec(v_x_1395_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_){
_start:
{
if (lean_obj_tag(v_x_1399_) == 0)
{
lean_dec(v_x_1397_);
return v_x_1398_;
}
else
{
lean_object* v_head_1400_; lean_object* v_tail_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1410_; 
v_head_1400_ = lean_ctor_get(v_x_1399_, 0);
v_tail_1401_ = lean_ctor_get(v_x_1399_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_x_1399_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1403_ = v_x_1399_;
v_isShared_1404_ = v_isSharedCheck_1410_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_tail_1401_);
lean_inc(v_head_1400_);
lean_dec(v_x_1399_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1410_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
lean_inc(v_x_1397_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set_tag(v___x_1403_, 5);
lean_ctor_set(v___x_1403_, 1, v_x_1397_);
lean_ctor_set(v___x_1403_, 0, v_x_1398_);
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_x_1398_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_x_1397_);
v___x_1406_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
lean_ctor_set(v___x_1407_, 1, v_head_1400_);
v_x_1398_ = v___x_1407_;
v_x_1399_ = v_tail_1401_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(lean_object* v_x_1411_, lean_object* v_x_1412_){
_start:
{
if (lean_obj_tag(v_x_1411_) == 0)
{
lean_object* v___x_1413_; 
lean_dec(v_x_1412_);
v___x_1413_ = lean_box(0);
return v___x_1413_;
}
else
{
lean_object* v_tail_1414_; 
v_tail_1414_ = lean_ctor_get(v_x_1411_, 1);
if (lean_obj_tag(v_tail_1414_) == 0)
{
lean_object* v_head_1415_; 
lean_dec(v_x_1412_);
v_head_1415_ = lean_ctor_get(v_x_1411_, 0);
lean_inc(v_head_1415_);
lean_dec_ref(v_x_1411_);
return v_head_1415_;
}
else
{
lean_object* v_head_1416_; lean_object* v___x_1417_; 
lean_inc(v_tail_1414_);
v_head_1416_ = lean_ctor_get(v_x_1411_, 0);
lean_inc(v_head_1416_);
lean_dec_ref(v_x_1411_);
v___x_1417_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2_spec__3(v_x_1412_, v_head_1416_, v_tail_1414_);
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(lean_object* v_x_1418_, lean_object* v_x_1419_){
_start:
{
if (lean_obj_tag(v_x_1418_) == 0)
{
lean_object* v___x_1420_; 
v___x_1420_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1420_;
}
else
{
lean_object* v_val_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1433_; 
v_val_1421_ = lean_ctor_get(v_x_1418_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_x_1418_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1423_ = v_x_1418_;
v_isShared_1424_ = v_isSharedCheck_1433_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_val_1421_);
lean_dec(v_x_1418_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1433_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1425_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1426_ = lean_string_from_utf8_unchecked(v_val_1421_);
v___x_1427_ = l_String_quote(v___x_1426_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set_tag(v___x_1423_, 3);
lean_ctor_set(v___x_1423_, 0, v___x_1427_);
v___x_1429_ = v___x_1423_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1425_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
v___x_1431_ = l_Repr_addAppParen(v___x_1430_, v_x_1419_);
return v___x_1431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1434_, lean_object* v_x_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_x_1434_, v_x_1435_);
lean_dec(v_x_1435_);
return v_res_1436_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__0));
v___x_1440_ = lean_string_length(v___x_1439_);
return v___x_1440_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__2);
v___x_1442_ = lean_nat_to_int(v___x_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(lean_object* v_x_1447_){
_start:
{
lean_object* v_fst_1448_; lean_object* v_snd_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1474_; 
v_fst_1448_ = lean_ctor_get(v_x_1447_, 0);
v_snd_1449_ = lean_ctor_get(v_x_1447_, 1);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_x_1447_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1451_ = v_x_1447_;
v_isShared_1452_ = v_isSharedCheck_1474_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_snd_1449_);
lean_inc(v_fst_1448_);
lean_dec(v_x_1447_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1474_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1453_ = lean_string_from_utf8_unchecked(v_fst_1448_);
v___x_1454_ = l_String_quote(v___x_1453_);
v___x_1455_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
v___x_1456_ = lean_box(0);
if (v_isShared_1452_ == 0)
{
lean_ctor_set_tag(v___x_1451_, 1);
lean_ctor_set(v___x_1451_, 1, v___x_1456_);
lean_ctor_set(v___x_1451_, 0, v___x_1455_);
v___x_1458_ = v___x_1451_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; lean_object* v___x_1472_; 
v___x_1459_ = lean_unsigned_to_nat(0u);
v___x_1460_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__1(v_snd_1449_, v___x_1459_);
v___x_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
lean_ctor_set(v___x_1461_, 1, v___x_1458_);
v___x_1462_ = l_List_reverse___redArg(v___x_1461_);
v___x_1463_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1464_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0_spec__2(v___x_1462_, v___x_1463_);
v___x_1465_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3, &l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__3);
v___x_1466_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__4));
v___x_1467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v___x_1464_);
v___x_1468_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg___closed__5));
v___x_1469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1467_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v___x_1470_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1465_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = 0;
v___x_1472_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1472_, 0, v___x_1470_);
lean_ctor_set_uint8(v___x_1472_, sizeof(void*)*1, v___x_1471_);
return v___x_1472_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(lean_object* v_x_1475_, lean_object* v_x_1476_, lean_object* v_x_1477_){
_start:
{
if (lean_obj_tag(v_x_1477_) == 0)
{
lean_dec(v_x_1475_);
return v_x_1476_;
}
else
{
lean_object* v_head_1478_; lean_object* v_tail_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1489_; 
v_head_1478_ = lean_ctor_get(v_x_1477_, 0);
v_tail_1479_ = lean_ctor_get(v_x_1477_, 1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_x_1477_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1481_ = v_x_1477_;
v_isShared_1482_ = v_isSharedCheck_1489_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_tail_1479_);
lean_inc(v_head_1478_);
lean_dec(v_x_1477_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1489_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
lean_inc(v_x_1475_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set_tag(v___x_1481_, 5);
lean_ctor_set(v___x_1481_, 1, v_x_1475_);
lean_ctor_set(v___x_1481_, 0, v_x_1476_);
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_x_1476_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_x_1475_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1478_);
v___x_1486_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v_x_1476_ = v___x_1486_;
v_x_1477_ = v_tail_1479_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(lean_object* v_x_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_){
_start:
{
if (lean_obj_tag(v_x_1492_) == 0)
{
lean_dec(v_x_1490_);
return v_x_1491_;
}
else
{
lean_object* v_head_1493_; lean_object* v_tail_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1504_; 
v_head_1493_ = lean_ctor_get(v_x_1492_, 0);
v_tail_1494_ = lean_ctor_get(v_x_1492_, 1);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_x_1492_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1496_ = v_x_1492_;
v_isShared_1497_ = v_isSharedCheck_1504_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_tail_1494_);
lean_inc(v_head_1493_);
lean_dec(v_x_1492_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1504_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
lean_inc(v_x_1490_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set_tag(v___x_1496_, 5);
lean_ctor_set(v___x_1496_, 1, v_x_1490_);
lean_ctor_set(v___x_1496_, 0, v_x_1491_);
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_x_1491_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_x_1490_);
v___x_1499_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1500_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1493_);
v___x_1501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1499_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
v___x_1502_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4_spec__6(v_x_1490_, v___x_1501_, v_tail_1494_);
return v___x_1502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(lean_object* v_x_1505_, lean_object* v_x_1506_){
_start:
{
if (lean_obj_tag(v_x_1505_) == 0)
{
lean_object* v___x_1507_; 
lean_dec(v_x_1506_);
v___x_1507_ = lean_box(0);
return v___x_1507_;
}
else
{
lean_object* v_tail_1508_; 
v_tail_1508_ = lean_ctor_get(v_x_1505_, 1);
if (lean_obj_tag(v_tail_1508_) == 0)
{
lean_object* v_head_1509_; lean_object* v___x_1510_; 
lean_dec(v_x_1506_);
v_head_1509_ = lean_ctor_get(v_x_1505_, 0);
lean_inc(v_head_1509_);
lean_dec_ref(v_x_1505_);
v___x_1510_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1509_);
return v___x_1510_;
}
else
{
lean_object* v_head_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_inc(v_tail_1508_);
v_head_1511_ = lean_ctor_get(v_x_1505_, 0);
lean_inc(v_head_1511_);
lean_dec_ref(v_x_1505_);
v___x_1512_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_head_1511_);
v___x_1513_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1_spec__4(v_x_1506_, v___x_1512_, v_tail_1508_);
return v___x_1513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(lean_object* v_xs_1514_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; 
v___x_1515_ = lean_array_get_size(v_xs_1514_);
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = lean_nat_dec_eq(v___x_1515_, v___x_1516_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1518_ = lean_array_to_list(v_xs_1514_);
v___x_1519_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1520_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__1(v___x_1518_, v___x_1519_);
v___x_1521_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1522_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
lean_ctor_set(v___x_1523_, 1, v___x_1520_);
v___x_1524_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1523_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1521_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = l_Std_Format_fill(v___x_1526_);
return v___x_1527_;
}
else
{
lean_object* v___x_1528_; 
lean_dec_ref(v_xs_1514_);
v___x_1528_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1528_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0(lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v___y_1529_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instReprQuery___lam__0___boxed(lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Std_Http_URI_instReprQuery___lam__0(v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(lean_object* v_x_1537_, lean_object* v_x_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___redArg(v_x_1537_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0___boxed(lean_object* v_x_1540_, lean_object* v_x_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_URI_instReprQuery_spec__0_spec__0(v_x_1540_, v_x_1541_);
lean_dec(v_x_1541_);
return v_res_1542_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1___lam__0(lean_object* v___f_1547_, lean_object* v_x_1548_, lean_object* v_x_1549_){
_start:
{
lean_object* v_fst_1550_; lean_object* v_snd_1551_; lean_object* v_fst_1552_; lean_object* v_snd_1553_; uint8_t v___x_1554_; 
v_fst_1550_ = lean_ctor_get(v_x_1548_, 0);
lean_inc(v_fst_1550_);
v_snd_1551_ = lean_ctor_get(v_x_1548_, 1);
lean_inc(v_snd_1551_);
lean_dec_ref(v_x_1548_);
v_fst_1552_ = lean_ctor_get(v_x_1549_, 0);
lean_inc(v_fst_1552_);
v_snd_1553_ = lean_ctor_get(v_x_1549_, 1);
lean_inc(v_snd_1553_);
lean_dec_ref(v_x_1549_);
v___x_1554_ = lean_sarray_dec_eq(v_fst_1550_, v_fst_1552_);
lean_dec(v_fst_1552_);
lean_dec(v_fst_1550_);
if (v___x_1554_ == 0)
{
lean_dec(v_snd_1553_);
lean_dec(v_snd_1551_);
lean_dec_ref(v___f_1547_);
return v___x_1554_;
}
else
{
uint8_t v___x_1555_; 
v___x_1555_ = l_Option_instBEq_beq___redArg(v___f_1547_, v_snd_1551_, v_snd_1553_);
return v___x_1555_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___lam__0___boxed(lean_object* v___f_1556_, lean_object* v_x_1557_, lean_object* v_x_1558_){
_start:
{
uint8_t v_res_1559_; lean_object* v_r_1560_; 
v_res_1559_ = l_Std_Http_URI_instBEqQuery___aux__1___lam__0(v___f_1556_, v_x_1557_, v_x_1558_);
v_r_1560_ = lean_box(v_res_1559_);
return v_r_1560_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1(lean_object* v_xs_1564_, lean_object* v_ys_1565_){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1566_ = lean_array_get_size(v_xs_1564_);
v___x_1567_ = lean_array_get_size(v_ys_1565_);
v___x_1568_ = lean_nat_dec_eq(v___x_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
return v___x_1568_;
}
else
{
lean_object* v___f_1569_; uint8_t v___x_1570_; 
v___f_1569_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__1));
v___x_1570_ = l_Array_isEqvAux___redArg(v_xs_1564_, v_ys_1565_, v___f_1569_, v___x_1566_);
return v___x_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___boxed(lean_object* v_xs_1571_, lean_object* v_ys_1572_){
_start:
{
uint8_t v_res_1573_; lean_object* v_r_1574_; 
v_res_1573_ = l_Std_Http_URI_instBEqQuery___aux__1(v_xs_1571_, v_ys_1572_);
lean_dec_ref(v_ys_1572_);
lean_dec_ref(v_xs_1571_);
v_r_1574_ = lean_box(v_res_1573_);
return v_r_1574_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(lean_object* v_x_1575_, lean_object* v_x_1576_){
_start:
{
if (lean_obj_tag(v_x_1575_) == 0)
{
if (lean_obj_tag(v_x_1576_) == 0)
{
uint8_t v___x_1577_; 
v___x_1577_ = 1;
return v___x_1577_;
}
else
{
uint8_t v___x_1578_; 
v___x_1578_ = 0;
return v___x_1578_;
}
}
else
{
if (lean_obj_tag(v_x_1576_) == 0)
{
uint8_t v___x_1579_; 
v___x_1579_ = 0;
return v___x_1579_;
}
else
{
lean_object* v_val_1580_; lean_object* v_val_1581_; uint8_t v___x_1582_; 
v_val_1580_ = lean_ctor_get(v_x_1575_, 0);
v_val_1581_ = lean_ctor_get(v_x_1576_, 0);
v___x_1582_ = lean_sarray_dec_eq(v_val_1580_, v_val_1581_);
return v___x_1582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0___boxed(lean_object* v_x_1583_, lean_object* v_x_1584_){
_start:
{
uint8_t v_res_1585_; lean_object* v_r_1586_; 
v_res_1585_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_x_1583_, v_x_1584_);
lean_dec(v_x_1584_);
lean_dec(v_x_1583_);
v_r_1586_ = lean_box(v_res_1585_);
return v_r_1586_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(lean_object* v_xs_1587_, lean_object* v_ys_1588_, lean_object* v_x_1589_){
_start:
{
lean_object* v_zero_1590_; uint8_t v_isZero_1591_; 
v_zero_1590_ = lean_unsigned_to_nat(0u);
v_isZero_1591_ = lean_nat_dec_eq(v_x_1589_, v_zero_1590_);
if (v_isZero_1591_ == 1)
{
lean_dec(v_x_1589_);
return v_isZero_1591_;
}
else
{
lean_object* v_one_1592_; lean_object* v_n_1593_; uint8_t v___y_1595_; lean_object* v___x_1597_; lean_object* v_fst_1598_; lean_object* v_snd_1599_; lean_object* v___x_1600_; lean_object* v_fst_1601_; lean_object* v_snd_1602_; uint8_t v___x_1603_; 
v_one_1592_ = lean_unsigned_to_nat(1u);
v_n_1593_ = lean_nat_sub(v_x_1589_, v_one_1592_);
lean_dec(v_x_1589_);
v___x_1597_ = lean_array_fget_borrowed(v_xs_1587_, v_n_1593_);
v_fst_1598_ = lean_ctor_get(v___x_1597_, 0);
v_snd_1599_ = lean_ctor_get(v___x_1597_, 1);
v___x_1600_ = lean_array_fget_borrowed(v_ys_1588_, v_n_1593_);
v_fst_1601_ = lean_ctor_get(v___x_1600_, 0);
v_snd_1602_ = lean_ctor_get(v___x_1600_, 1);
v___x_1603_ = lean_sarray_dec_eq(v_fst_1598_, v_fst_1601_);
if (v___x_1603_ == 0)
{
v___y_1595_ = v___x_1603_;
goto v___jp_1594_;
}
else
{
uint8_t v___x_1604_; 
v___x_1604_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_snd_1599_, v_snd_1602_);
v___y_1595_ = v___x_1604_;
goto v___jp_1594_;
}
v___jp_1594_:
{
if (v___y_1595_ == 0)
{
lean_dec(v_n_1593_);
return v___y_1595_;
}
else
{
v_x_1589_ = v_n_1593_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg___boxed(lean_object* v_xs_1605_, lean_object* v_ys_1606_, lean_object* v_x_1607_){
_start:
{
uint8_t v_res_1608_; lean_object* v_r_1609_; 
v_res_1608_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1605_, v_ys_1606_, v_x_1607_);
lean_dec_ref(v_ys_1606_);
lean_dec_ref(v_xs_1605_);
v_r_1609_ = lean_box(v_res_1608_);
return v_r_1609_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___lam__0(lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1612_ = lean_array_get_size(v___y_1610_);
v___x_1613_ = lean_array_get_size(v___y_1611_);
v___x_1614_ = lean_nat_dec_eq(v___x_1612_, v___x_1613_);
if (v___x_1614_ == 0)
{
return v___x_1614_;
}
else
{
uint8_t v___x_1615_; 
v___x_1615_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v___y_1610_, v___y_1611_, v___x_1612_);
return v___x_1615_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___lam__0___boxed(lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
uint8_t v_res_1618_; lean_object* v_r_1619_; 
v_res_1618_ = l_Std_Http_URI_instBEqQuery___lam__0(v___y_1616_, v___y_1617_);
lean_dec_ref(v___y_1617_);
lean_dec_ref(v___y_1616_);
v_r_1619_ = lean_box(v_res_1618_);
return v_r_1619_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(lean_object* v_xs_1622_, lean_object* v_ys_1623_, lean_object* v_hsz_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_){
_start:
{
uint8_t v___x_1627_; 
v___x_1627_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1622_, v_ys_1623_, v_x_1625_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___boxed(lean_object* v_xs_1628_, lean_object* v_ys_1629_, lean_object* v_hsz_1630_, lean_object* v_x_1631_, lean_object* v_x_1632_){
_start:
{
uint8_t v_res_1633_; lean_object* v_r_1634_; 
v_res_1633_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(v_xs_1628_, v_ys_1629_, v_hsz_1630_, v_x_1631_, v_x_1632_);
lean_dec_ref(v_ys_1629_);
lean_dec_ref(v_xs_1628_);
v_r_1634_ = lean_box(v_res_1633_);
return v_r_1634_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(lean_object* v_as_1635_){
_start:
{
lean_object* v___f_1636_; lean_object* v___x_1637_; 
v___f_1636_ = ((lean_object*)(l_Std_Http_URI_instBEqQuery___aux__1___closed__0));
v___x_1637_ = l_List_eraseDupsBy___redArg(v___f_1636_, v_as_1635_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(size_t v_sz_1638_, size_t v_i_1639_, lean_object* v_bs_1640_){
_start:
{
uint8_t v___x_1641_; 
v___x_1641_ = lean_usize_dec_lt(v_i_1639_, v_sz_1638_);
if (v___x_1641_ == 0)
{
return v_bs_1640_;
}
else
{
lean_object* v_v_1642_; lean_object* v_fst_1643_; lean_object* v___x_1644_; lean_object* v_bs_x27_1645_; size_t v___x_1646_; size_t v___x_1647_; lean_object* v___x_1648_; 
v_v_1642_ = lean_array_uget_borrowed(v_bs_1640_, v_i_1639_);
v_fst_1643_ = lean_ctor_get(v_v_1642_, 0);
lean_inc(v_fst_1643_);
v___x_1644_ = lean_unsigned_to_nat(0u);
v_bs_x27_1645_ = lean_array_uset(v_bs_1640_, v_i_1639_, v___x_1644_);
v___x_1646_ = ((size_t)1ULL);
v___x_1647_ = lean_usize_add(v_i_1639_, v___x_1646_);
v___x_1648_ = lean_array_uset(v_bs_x27_1645_, v_i_1639_, v_fst_1643_);
v_i_1639_ = v___x_1647_;
v_bs_1640_ = v___x_1648_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0___boxed(lean_object* v_sz_1650_, lean_object* v_i_1651_, lean_object* v_bs_1652_){
_start:
{
size_t v_sz_boxed_1653_; size_t v_i_boxed_1654_; lean_object* v_res_1655_; 
v_sz_boxed_1653_ = lean_unbox_usize(v_sz_1650_);
lean_dec(v_sz_1650_);
v_i_boxed_1654_ = lean_unbox_usize(v_i_1651_);
lean_dec(v_i_1651_);
v_res_1655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_boxed_1653_, v_i_boxed_1654_, v_bs_1652_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names(lean_object* v_query_1656_){
_start:
{
size_t v_sz_1657_; size_t v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_sz_1657_ = lean_array_size(v_query_1656_);
v___x_1658_ = ((size_t)0ULL);
v___x_1659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_1657_, v___x_1658_, v_query_1656_);
v___x_1660_ = lean_array_to_list(v___x_1659_);
v___x_1661_ = l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(v___x_1660_);
v___x_1662_ = lean_array_mk(v___x_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(size_t v_sz_1663_, size_t v_i_1664_, lean_object* v_bs_1665_){
_start:
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_usize_dec_lt(v_i_1664_, v_sz_1663_);
if (v___x_1666_ == 0)
{
return v_bs_1665_;
}
else
{
lean_object* v_v_1667_; lean_object* v_snd_1668_; lean_object* v___x_1669_; lean_object* v_bs_x27_1670_; size_t v___x_1671_; size_t v___x_1672_; lean_object* v___x_1673_; 
v_v_1667_ = lean_array_uget_borrowed(v_bs_1665_, v_i_1664_);
v_snd_1668_ = lean_ctor_get(v_v_1667_, 1);
lean_inc(v_snd_1668_);
v___x_1669_ = lean_unsigned_to_nat(0u);
v_bs_x27_1670_ = lean_array_uset(v_bs_1665_, v_i_1664_, v___x_1669_);
v___x_1671_ = ((size_t)1ULL);
v___x_1672_ = lean_usize_add(v_i_1664_, v___x_1671_);
v___x_1673_ = lean_array_uset(v_bs_x27_1670_, v_i_1664_, v_snd_1668_);
v_i_1664_ = v___x_1672_;
v_bs_1665_ = v___x_1673_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0___boxed(lean_object* v_sz_1675_, lean_object* v_i_1676_, lean_object* v_bs_1677_){
_start:
{
size_t v_sz_boxed_1678_; size_t v_i_boxed_1679_; lean_object* v_res_1680_; 
v_sz_boxed_1678_ = lean_unbox_usize(v_sz_1675_);
lean_dec(v_sz_1675_);
v_i_boxed_1679_ = lean_unbox_usize(v_i_1676_);
lean_dec(v_i_1676_);
v_res_1680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_boxed_1678_, v_i_boxed_1679_, v_bs_1677_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_values(lean_object* v_query_1681_){
_start:
{
size_t v_sz_1682_; size_t v___x_1683_; lean_object* v___x_1684_; 
v_sz_1682_ = lean_array_size(v_query_1681_);
v___x_1683_ = ((size_t)0ULL);
v___x_1684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_1682_, v___x_1683_, v_query_1681_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray(lean_object* v_query_1685_){
_start:
{
lean_inc_ref(v_query_1685_);
return v_query_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray___boxed(lean_object* v_query_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Std_Http_URI_Query_toArray(v_query_1686_);
lean_dec_ref(v_query_1686_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object* v_key_1689_, lean_object* v_value_1690_){
_start:
{
if (lean_obj_tag(v_value_1690_) == 0)
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_string_from_utf8_unchecked(v_key_1689_);
return v___x_1691_;
}
else
{
lean_object* v_val_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v_val_1692_ = lean_ctor_get(v_value_1690_, 0);
lean_inc(v_val_1692_);
lean_dec_ref(v_value_1690_);
v___x_1693_ = lean_string_from_utf8_unchecked(v_key_1689_);
v___x_1694_ = ((lean_object*)(l_Std_Http_URI_Query_formatQueryParam___closed__0));
v___x_1695_ = lean_string_append(v___x_1693_, v___x_1694_);
v___x_1696_ = lean_string_from_utf8_unchecked(v_val_1692_);
v___x_1697_ = lean_string_append(v___x_1695_, v___x_1696_);
lean_dec_ref(v___x_1696_);
return v___x_1697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(lean_object* v_key_1701_, lean_object* v_as_1702_, size_t v_sz_1703_, size_t v_i_1704_, lean_object* v_b_1705_){
_start:
{
uint8_t v___x_1706_; 
v___x_1706_ = lean_usize_dec_lt(v_i_1704_, v_sz_1703_);
if (v___x_1706_ == 0)
{
lean_inc_ref(v_b_1705_);
return v_b_1705_;
}
else
{
lean_object* v_a_1707_; lean_object* v_fst_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v_a_1707_ = lean_array_uget_borrowed(v_as_1702_, v_i_1704_);
v_fst_1708_ = lean_ctor_get(v_a_1707_, 0);
v___x_1709_ = lean_box(0);
v___x_1710_ = lean_sarray_dec_eq(v_fst_1708_, v_key_1701_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; size_t v___x_1712_; size_t v___x_1713_; 
v___x_1711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v___x_1712_ = ((size_t)1ULL);
v___x_1713_ = lean_usize_add(v_i_1704_, v___x_1712_);
v_i_1704_ = v___x_1713_;
v_b_1705_ = v___x_1711_;
goto _start;
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_inc(v_a_1707_);
v___x_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1715_, 0, v_a_1707_);
v___x_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
lean_ctor_set(v___x_1717_, 1, v___x_1709_);
return v___x_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___boxed(lean_object* v_key_1718_, lean_object* v_as_1719_, lean_object* v_sz_1720_, lean_object* v_i_1721_, lean_object* v_b_1722_){
_start:
{
size_t v_sz_boxed_1723_; size_t v_i_boxed_1724_; lean_object* v_res_1725_; 
v_sz_boxed_1723_ = lean_unbox_usize(v_sz_1720_);
lean_dec(v_sz_1720_);
v_i_boxed_1724_ = lean_unbox_usize(v_i_1721_);
lean_dec(v_i_1721_);
v_res_1725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1718_, v_as_1719_, v_sz_boxed_1723_, v_i_boxed_1724_, v_b_1722_);
lean_dec_ref(v_b_1722_);
lean_dec_ref(v_as_1719_);
lean_dec_ref(v_key_1718_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f(lean_object* v_query_1726_, lean_object* v_key_1727_){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; size_t v_sz_1730_; size_t v___x_1731_; lean_object* v___x_1732_; lean_object* v_fst_1733_; 
v___x_1728_ = lean_box(0);
v___x_1729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v_sz_1730_ = lean_array_size(v_query_1726_);
v___x_1731_ = ((size_t)0ULL);
v___x_1732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1727_, v_query_1726_, v_sz_1730_, v___x_1731_, v___x_1729_);
v_fst_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_fst_1733_);
lean_dec_ref(v___x_1732_);
if (lean_obj_tag(v_fst_1733_) == 0)
{
return v___x_1728_;
}
else
{
lean_object* v_val_1734_; 
v_val_1734_ = lean_ctor_get(v_fst_1733_, 0);
lean_inc(v_val_1734_);
lean_dec_ref(v_fst_1733_);
if (lean_obj_tag(v_val_1734_) == 0)
{
return v___x_1728_;
}
else
{
lean_object* v_val_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1743_; 
v_val_1735_ = lean_ctor_get(v_val_1734_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_val_1734_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1737_ = v_val_1734_;
v_isShared_1738_ = v_isSharedCheck_1743_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_val_1735_);
lean_dec(v_val_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1743_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v_snd_1739_; lean_object* v___x_1741_; 
v_snd_1739_ = lean_ctor_get(v_val_1735_, 1);
lean_inc(v_snd_1739_);
lean_dec(v_val_1735_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v_snd_1739_);
v___x_1741_ = v___x_1737_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_snd_1739_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f___boxed(lean_object* v_query_1744_, lean_object* v_key_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1744_, v_key_1745_);
lean_dec_ref(v_key_1745_);
lean_dec_ref(v_query_1744_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f(lean_object* v_query_1747_, lean_object* v_key_1748_){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1748_);
v___x_1750_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1747_, v___x_1749_);
lean_dec_ref(v___x_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f___boxed(lean_object* v_query_1751_, lean_object* v_key_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Std_Http_URI_Query_find_x3f(v_query_1751_, v_key_1752_);
lean_dec_ref(v_key_1752_);
lean_dec_ref(v_query_1751_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(lean_object* v_key_1754_, lean_object* v_as_1755_, size_t v_i_1756_, size_t v_stop_1757_, lean_object* v_b_1758_){
_start:
{
lean_object* v___y_1760_; uint8_t v___x_1764_; 
v___x_1764_ = lean_usize_dec_eq(v_i_1756_, v_stop_1757_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; lean_object* v_fst_1766_; lean_object* v_snd_1767_; uint8_t v___x_1768_; 
v___x_1765_ = lean_array_uget_borrowed(v_as_1755_, v_i_1756_);
v_fst_1766_ = lean_ctor_get(v___x_1765_, 0);
v_snd_1767_ = lean_ctor_get(v___x_1765_, 1);
v___x_1768_ = lean_sarray_dec_eq(v_fst_1766_, v_key_1754_);
if (v___x_1768_ == 0)
{
v___y_1760_ = v_b_1758_;
goto v___jp_1759_;
}
else
{
lean_object* v___x_1769_; 
lean_inc(v_snd_1767_);
v___x_1769_ = lean_array_push(v_b_1758_, v_snd_1767_);
v___y_1760_ = v___x_1769_;
goto v___jp_1759_;
}
}
else
{
return v_b_1758_;
}
v___jp_1759_:
{
size_t v___x_1761_; size_t v___x_1762_; 
v___x_1761_ = ((size_t)1ULL);
v___x_1762_ = lean_usize_add(v_i_1756_, v___x_1761_);
v_i_1756_ = v___x_1762_;
v_b_1758_ = v___y_1760_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0___boxed(lean_object* v_key_1770_, lean_object* v_as_1771_, lean_object* v_i_1772_, lean_object* v_stop_1773_, lean_object* v_b_1774_){
_start:
{
size_t v_i_boxed_1775_; size_t v_stop_boxed_1776_; lean_object* v_res_1777_; 
v_i_boxed_1775_ = lean_unbox_usize(v_i_1772_);
lean_dec(v_i_1772_);
v_stop_boxed_1776_ = lean_unbox_usize(v_stop_1773_);
lean_dec(v_stop_1773_);
v_res_1777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1770_, v_as_1771_, v_i_boxed_1775_, v_stop_boxed_1776_, v_b_1774_);
lean_dec_ref(v_as_1771_);
lean_dec_ref(v_key_1770_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(lean_object* v_key_1780_, lean_object* v_as_1781_, lean_object* v_start_1782_, lean_object* v_stop_1783_){
_start:
{
lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1784_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_1785_ = lean_nat_dec_lt(v_start_1782_, v_stop_1783_);
if (v___x_1785_ == 0)
{
return v___x_1784_;
}
else
{
lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1786_ = lean_array_get_size(v_as_1781_);
v___x_1787_ = lean_nat_dec_le(v_stop_1783_, v___x_1786_);
if (v___x_1787_ == 0)
{
uint8_t v___x_1788_; 
v___x_1788_ = lean_nat_dec_lt(v_start_1782_, v___x_1786_);
if (v___x_1788_ == 0)
{
return v___x_1784_;
}
else
{
size_t v___x_1789_; size_t v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = lean_usize_of_nat(v_start_1782_);
v___x_1790_ = lean_usize_of_nat(v___x_1786_);
v___x_1791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1780_, v_as_1781_, v___x_1789_, v___x_1790_, v___x_1784_);
return v___x_1791_;
}
}
else
{
size_t v___x_1792_; size_t v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = lean_usize_of_nat(v_start_1782_);
v___x_1793_ = lean_usize_of_nat(v_stop_1783_);
v___x_1794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1780_, v_as_1781_, v___x_1792_, v___x_1793_, v___x_1784_);
return v___x_1794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___boxed(lean_object* v_key_1795_, lean_object* v_as_1796_, lean_object* v_start_1797_, lean_object* v_stop_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1795_, v_as_1796_, v_start_1797_, v_stop_1798_);
lean_dec(v_stop_1798_);
lean_dec(v_start_1797_);
lean_dec_ref(v_as_1796_);
lean_dec_ref(v_key_1795_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded(lean_object* v_query_1800_, lean_object* v_key_1801_){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = lean_array_get_size(v_query_1800_);
v___x_1804_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1801_, v_query_1800_, v___x_1802_, v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded___boxed(lean_object* v_query_1805_, lean_object* v_key_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1805_, v_key_1806_);
lean_dec_ref(v_key_1806_);
lean_dec_ref(v_query_1805_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll(lean_object* v_query_1808_, lean_object* v_key_1809_){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1809_);
v___x_1811_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1808_, v___x_1810_);
lean_dec_ref(v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll___boxed(lean_object* v_query_1812_, lean_object* v_key_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Std_Http_URI_Query_findAll(v_query_1812_, v_key_1813_);
lean_dec_ref(v_key_1813_);
lean_dec_ref(v_query_1812_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert(lean_object* v_query_1815_, lean_object* v_key_1816_, lean_object* v_value_1817_){
_start:
{
lean_object* v_encodedKey_1818_; lean_object* v_encodedValue_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v_encodedKey_1818_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1816_);
v_encodedValue_1819_ = l_Std_Http_URI_EncodedQueryParam_encode(v_value_1817_);
v___x_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1820_, 0, v_encodedValue_1819_);
v___x_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1821_, 0, v_encodedKey_1818_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = lean_array_push(v_query_1815_, v___x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert___boxed(lean_object* v_query_1823_, lean_object* v_key_1824_, lean_object* v_value_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Std_Http_URI_Query_insert(v_query_1823_, v_key_1824_, v_value_1825_);
lean_dec_ref(v_value_1825_);
lean_dec_ref(v_key_1824_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object* v_query_1827_, lean_object* v_key_1828_, lean_object* v_value_1829_){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v_key_1828_);
lean_ctor_set(v___x_1830_, 1, v_value_1829_);
v___x_1831_ = lean_array_push(v_query_1827_, v___x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_ofList(lean_object* v_pairs_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_array_mk(v_pairs_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(lean_object* v_key_1837_, lean_object* v_as_1838_, size_t v_i_1839_, size_t v_stop_1840_){
_start:
{
uint8_t v___x_1841_; 
v___x_1841_ = lean_usize_dec_eq(v_i_1839_, v_stop_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v_fst_1843_; uint8_t v___x_1844_; 
v___x_1842_ = lean_array_uget_borrowed(v_as_1838_, v_i_1839_);
v_fst_1843_ = lean_ctor_get(v___x_1842_, 0);
v___x_1844_ = lean_sarray_dec_eq(v_fst_1843_, v_key_1837_);
if (v___x_1844_ == 0)
{
size_t v___x_1845_; size_t v___x_1846_; 
v___x_1845_ = ((size_t)1ULL);
v___x_1846_ = lean_usize_add(v_i_1839_, v___x_1845_);
v_i_1839_ = v___x_1846_;
goto _start;
}
else
{
return v___x_1844_;
}
}
else
{
uint8_t v___x_1848_; 
v___x_1848_ = 0;
return v___x_1848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(lean_object* v_key_1849_, lean_object* v_as_1850_, lean_object* v_i_1851_, lean_object* v_stop_1852_){
_start:
{
size_t v_i_boxed_1853_; size_t v_stop_boxed_1854_; uint8_t v_res_1855_; lean_object* v_r_1856_; 
v_i_boxed_1853_ = lean_unbox_usize(v_i_1851_);
lean_dec(v_i_1851_);
v_stop_boxed_1854_ = lean_unbox_usize(v_stop_1852_);
lean_dec(v_stop_1852_);
v_res_1855_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1849_, v_as_1850_, v_i_boxed_1853_, v_stop_boxed_1854_);
lean_dec_ref(v_as_1850_);
lean_dec_ref(v_key_1849_);
v_r_1856_ = lean_box(v_res_1855_);
return v_r_1856_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_containsEncoded(lean_object* v_query_1857_, lean_object* v_key_1858_){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1859_ = lean_unsigned_to_nat(0u);
v___x_1860_ = lean_array_get_size(v_query_1857_);
v___x_1861_ = lean_nat_dec_lt(v___x_1859_, v___x_1860_);
if (v___x_1861_ == 0)
{
return v___x_1861_;
}
else
{
if (v___x_1861_ == 0)
{
return v___x_1861_;
}
else
{
size_t v___x_1862_; size_t v___x_1863_; uint8_t v___x_1864_; 
v___x_1862_ = ((size_t)0ULL);
v___x_1863_ = lean_usize_of_nat(v___x_1860_);
v___x_1864_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1858_, v_query_1857_, v___x_1862_, v___x_1863_);
return v___x_1864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_containsEncoded___boxed(lean_object* v_query_1865_, lean_object* v_key_1866_){
_start:
{
uint8_t v_res_1867_; lean_object* v_r_1868_; 
v_res_1867_ = l_Std_Http_URI_Query_containsEncoded(v_query_1865_, v_key_1866_);
lean_dec_ref(v_key_1866_);
lean_dec_ref(v_query_1865_);
v_r_1868_ = lean_box(v_res_1867_);
return v_r_1868_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_contains(lean_object* v_query_1869_, lean_object* v_key_1870_){
_start:
{
lean_object* v___x_1871_; uint8_t v___x_1872_; 
v___x_1871_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1870_);
v___x_1872_ = l_Std_Http_URI_Query_containsEncoded(v_query_1869_, v___x_1871_);
lean_dec_ref(v___x_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_contains___boxed(lean_object* v_query_1873_, lean_object* v_key_1874_){
_start:
{
uint8_t v_res_1875_; lean_object* v_r_1876_; 
v_res_1875_ = l_Std_Http_URI_Query_contains(v_query_1873_, v_key_1874_);
lean_dec_ref(v_key_1874_);
lean_dec_ref(v_query_1873_);
v_r_1876_ = lean_box(v_res_1875_);
return v_r_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(lean_object* v_key_1877_, lean_object* v_as_1878_, size_t v_i_1879_, size_t v_stop_1880_, lean_object* v_b_1881_){
_start:
{
lean_object* v___y_1883_; uint8_t v___x_1887_; 
v___x_1887_ = lean_usize_dec_eq(v_i_1879_, v_stop_1880_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v_fst_1891_; uint8_t v___x_1892_; 
v___x_1888_ = lean_array_uget_borrowed(v_as_1878_, v_i_1879_);
v_fst_1891_ = lean_ctor_get(v___x_1888_, 0);
v___x_1892_ = lean_sarray_dec_eq(v_fst_1891_, v_key_1877_);
if (v___x_1892_ == 0)
{
goto v___jp_1889_;
}
else
{
if (v___x_1887_ == 0)
{
v___y_1883_ = v_b_1881_;
goto v___jp_1882_;
}
else
{
goto v___jp_1889_;
}
}
v___jp_1889_:
{
lean_object* v___x_1890_; 
lean_inc(v___x_1888_);
v___x_1890_ = lean_array_push(v_b_1881_, v___x_1888_);
v___y_1883_ = v___x_1890_;
goto v___jp_1882_;
}
}
else
{
return v_b_1881_;
}
v___jp_1882_:
{
size_t v___x_1884_; size_t v___x_1885_; 
v___x_1884_ = ((size_t)1ULL);
v___x_1885_ = lean_usize_add(v_i_1879_, v___x_1884_);
v_i_1879_ = v___x_1885_;
v_b_1881_ = v___y_1883_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(lean_object* v_key_1893_, lean_object* v_as_1894_, lean_object* v_i_1895_, lean_object* v_stop_1896_, lean_object* v_b_1897_){
_start:
{
size_t v_i_boxed_1898_; size_t v_stop_boxed_1899_; lean_object* v_res_1900_; 
v_i_boxed_1898_ = lean_unbox_usize(v_i_1895_);
lean_dec(v_i_1895_);
v_stop_boxed_1899_ = lean_unbox_usize(v_stop_1896_);
lean_dec(v_stop_1896_);
v_res_1900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1893_, v_as_1894_, v_i_boxed_1898_, v_stop_boxed_1899_, v_b_1897_);
lean_dec_ref(v_as_1894_);
lean_dec_ref(v_key_1893_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded(lean_object* v_query_1901_, lean_object* v_key_1902_){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1903_ = lean_unsigned_to_nat(0u);
v___x_1904_ = lean_array_get_size(v_query_1901_);
v___x_1905_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_1906_ = lean_nat_dec_lt(v___x_1903_, v___x_1904_);
if (v___x_1906_ == 0)
{
return v___x_1905_;
}
else
{
uint8_t v___x_1907_; 
v___x_1907_ = lean_nat_dec_le(v___x_1904_, v___x_1904_);
if (v___x_1907_ == 0)
{
if (v___x_1906_ == 0)
{
return v___x_1905_;
}
else
{
size_t v___x_1908_; size_t v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = ((size_t)0ULL);
v___x_1909_ = lean_usize_of_nat(v___x_1904_);
v___x_1910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1902_, v_query_1901_, v___x_1908_, v___x_1909_, v___x_1905_);
return v___x_1910_;
}
}
else
{
size_t v___x_1911_; size_t v___x_1912_; lean_object* v___x_1913_; 
v___x_1911_ = ((size_t)0ULL);
v___x_1912_ = lean_usize_of_nat(v___x_1904_);
v___x_1913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1902_, v_query_1901_, v___x_1911_, v___x_1912_, v___x_1905_);
return v___x_1913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded___boxed(lean_object* v_query_1914_, lean_object* v_key_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Std_Http_URI_Query_eraseEncoded(v_query_1914_, v_key_1915_);
lean_dec_ref(v_key_1915_);
lean_dec_ref(v_query_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase(lean_object* v_query_1917_, lean_object* v_key_1918_){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1918_);
v___x_1920_ = l_Std_Http_URI_Query_eraseEncoded(v_query_1917_, v___x_1919_);
lean_dec_ref(v___x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase___boxed(lean_object* v_query_1921_, lean_object* v_key_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Std_Http_URI_Query_erase(v_query_1921_, v_key_1922_);
lean_dec_ref(v_key_1922_);
lean_dec_ref(v_query_1921_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get(lean_object* v_query_1926_, lean_object* v_key_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Std_Http_URI_Query_find_x3f(v_query_1926_, v_key_1927_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v___x_1929_; 
v___x_1929_ = lean_box(0);
return v___x_1929_;
}
else
{
lean_object* v_val_1930_; 
v_val_1930_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_val_1930_);
lean_dec_ref(v___x_1928_);
if (lean_obj_tag(v_val_1930_) == 0)
{
lean_object* v___x_1931_; 
v___x_1931_ = ((lean_object*)(l_Std_Http_URI_Query_get___closed__0));
return v___x_1931_;
}
else
{
lean_object* v_val_1932_; lean_object* v___x_1933_; 
v_val_1932_ = lean_ctor_get(v_val_1930_, 0);
lean_inc(v_val_1932_);
lean_dec_ref(v_val_1930_);
v___x_1933_ = l_Std_Http_URI_EncodedQueryParam_decode(v_val_1932_);
lean_dec(v_val_1932_);
return v___x_1933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get___boxed(lean_object* v_query_1934_, lean_object* v_key_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Std_Http_URI_Query_get(v_query_1934_, v_key_1935_);
lean_dec_ref(v_key_1935_);
lean_dec_ref(v_query_1934_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD(lean_object* v_query_1937_, lean_object* v_key_1938_, lean_object* v_default_1939_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Std_Http_URI_Query_get(v_query_1937_, v_key_1938_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_inc_ref(v_default_1939_);
return v_default_1939_;
}
else
{
lean_object* v_val_1941_; 
v_val_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_val_1941_);
lean_dec_ref(v___x_1940_);
return v_val_1941_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD___boxed(lean_object* v_query_1942_, lean_object* v_key_1943_, lean_object* v_default_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Std_Http_URI_Query_getD(v_query_1942_, v_key_1943_, v_default_1944_);
lean_dec_ref(v_default_1944_);
lean_dec_ref(v_key_1943_);
lean_dec_ref(v_query_1942_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set(lean_object* v_query_1946_, lean_object* v_key_1947_, lean_object* v_value_1948_){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = l_Std_Http_URI_Query_erase(v_query_1946_, v_key_1947_);
v___x_1950_ = l_Std_Http_URI_Query_insert(v___x_1949_, v_key_1947_, v_value_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set___boxed(lean_object* v_query_1951_, lean_object* v_key_1952_, lean_object* v_value_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Std_Http_URI_Query_set(v_query_1951_, v_key_1952_, v_value_1953_);
lean_dec_ref(v_value_1953_);
lean_dec_ref(v_key_1952_);
lean_dec_ref(v_query_1951_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(size_t v_sz_1955_, size_t v_i_1956_, lean_object* v_bs_1957_){
_start:
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_usize_dec_lt(v_i_1956_, v_sz_1955_);
if (v___x_1958_ == 0)
{
return v_bs_1957_;
}
else
{
lean_object* v_v_1959_; lean_object* v_fst_1960_; lean_object* v_snd_1961_; lean_object* v___x_1962_; lean_object* v_bs_x27_1963_; lean_object* v___x_1964_; size_t v___x_1965_; size_t v___x_1966_; lean_object* v___x_1967_; 
v_v_1959_ = lean_array_uget_borrowed(v_bs_1957_, v_i_1956_);
v_fst_1960_ = lean_ctor_get(v_v_1959_, 0);
lean_inc(v_fst_1960_);
v_snd_1961_ = lean_ctor_get(v_v_1959_, 1);
lean_inc(v_snd_1961_);
v___x_1962_ = lean_unsigned_to_nat(0u);
v_bs_x27_1963_ = lean_array_uset(v_bs_1957_, v_i_1956_, v___x_1962_);
v___x_1964_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_1960_, v_snd_1961_);
v___x_1965_ = ((size_t)1ULL);
v___x_1966_ = lean_usize_add(v_i_1956_, v___x_1965_);
v___x_1967_ = lean_array_uset(v_bs_x27_1963_, v_i_1956_, v___x_1964_);
v_i_1956_ = v___x_1966_;
v_bs_1957_ = v___x_1967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0___boxed(lean_object* v_sz_1969_, lean_object* v_i_1970_, lean_object* v_bs_1971_){
_start:
{
size_t v_sz_boxed_1972_; size_t v_i_boxed_1973_; lean_object* v_res_1974_; 
v_sz_boxed_1972_ = lean_unbox_usize(v_sz_1969_);
lean_dec(v_sz_1969_);
v_i_boxed_1973_ = lean_unbox_usize(v_i_1970_);
lean_dec(v_i_1970_);
v_res_1974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_boxed_1972_, v_i_boxed_1973_, v_bs_1971_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toRawString(lean_object* v_query_1976_){
_start:
{
size_t v_sz_1977_; size_t v___x_1978_; lean_object* v_params_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v_sz_1977_ = lean_array_size(v_query_1976_);
v___x_1978_ = ((size_t)0ULL);
v_params_1979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_1977_, v___x_1978_, v_query_1976_);
v___x_1980_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_1981_ = lean_array_to_list(v_params_1979_);
v___x_1982_ = l_String_intercalate(v___x_1980_, v___x_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0(lean_object* v_x_1984_){
_start:
{
lean_object* v_fst_1985_; lean_object* v_snd_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v_fst_1985_ = lean_ctor_get(v_x_1984_, 0);
v_snd_1986_ = lean_ctor_get(v_x_1984_, 1);
v___x_1987_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
v___x_1988_ = l_Std_Http_URI_Query_insert(v___x_1987_, v_fst_1985_, v_snd_1986_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0___boxed(lean_object* v_x_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Std_Http_URI_Query_instSingletonProdString___lam__0(v_x_1989_);
lean_dec_ref(v_x_1989_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0(lean_object* v_x_1993_, lean_object* v_q_1994_){
_start:
{
lean_object* v_fst_1995_; lean_object* v_snd_1996_; lean_object* v___x_1997_; 
v_fst_1995_ = lean_ctor_get(v_x_1993_, 0);
v_snd_1996_ = lean_ctor_get(v_x_1993_, 1);
v___x_1997_ = l_Std_Http_URI_Query_insert(v_q_1994_, v_fst_1995_, v_snd_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0___boxed(lean_object* v_x_1998_, lean_object* v_q_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Std_Http_URI_Query_instInsertProdString___lam__0(v_x_1998_, v_q_1999_);
lean_dec_ref(v_x_1998_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__0(lean_object* v_x_2003_){
_start:
{
lean_object* v_fst_2004_; lean_object* v_snd_2005_; lean_object* v___x_2006_; 
v_fst_2004_ = lean_ctor_get(v_x_2003_, 0);
lean_inc(v_fst_2004_);
v_snd_2005_ = lean_ctor_get(v_x_2003_, 1);
lean_inc(v_snd_2005_);
lean_dec_ref(v_x_2003_);
v___x_2006_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2004_, v_snd_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__1(lean_object* v___f_2008_, lean_object* v_q_2009_){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2010_ = lean_array_get_size(v_q_2009_);
v___x_2011_ = lean_unsigned_to_nat(0u);
v___x_2012_ = lean_nat_dec_eq(v___x_2010_, v___x_2011_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v_encodedParams_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2013_ = lean_array_to_list(v_q_2009_);
v___x_2014_ = lean_box(0);
v_encodedParams_2015_ = l_List_mapTR_loop___redArg(v___f_2008_, v___x_2013_, v___x_2014_);
v___x_2016_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2017_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2018_ = l_String_intercalate(v___x_2017_, v_encodedParams_2015_);
v___x_2019_ = lean_string_append(v___x_2016_, v___x_2018_);
lean_dec_ref(v___x_2018_);
return v___x_2019_;
}
else
{
lean_object* v___x_2020_; 
lean_dec_ref(v_q_2009_);
lean_dec_ref(v___f_2008_);
v___x_2020_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2020_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(lean_object* v_x_2025_, lean_object* v_x_2026_){
_start:
{
if (lean_obj_tag(v_x_2025_) == 0)
{
lean_object* v___x_2027_; 
v___x_2027_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2027_;
}
else
{
lean_object* v_val_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v_val_2028_ = lean_ctor_get(v_x_2025_, 0);
lean_inc(v_val_2028_);
lean_dec_ref(v_x_2025_);
v___x_2029_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2030_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_val_2028_);
v___x_2031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2029_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
v___x_2032_ = l_Repr_addAppParen(v___x_2031_, v_x_2026_);
return v___x_2032_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(lean_object* v_x_2033_, lean_object* v_x_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_x_2033_, v_x_2034_);
lean_dec(v_x_2034_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object* v_x_2036_, lean_object* v_x_2037_){
_start:
{
if (lean_obj_tag(v_x_2036_) == 0)
{
lean_object* v___x_2038_; 
v___x_2038_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2038_;
}
else
{
lean_object* v_val_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2050_; 
v_val_2039_ = lean_ctor_get(v_x_2036_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_x_2036_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2041_ = v_x_2036_;
v_isShared_2042_ = v_isSharedCheck_2050_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_val_2039_);
lean_dec(v_x_2036_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2050_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2043_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2044_ = l_String_quote(v_val_2039_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set_tag(v___x_2041_, 3);
lean_ctor_set(v___x_2041_, 0, v___x_2044_);
v___x_2046_ = v___x_2041_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2043_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
v___x_2048_ = l_Repr_addAppParen(v___x_2047_, v_x_2037_);
return v___x_2048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1___boxed(lean_object* v_x_2051_, lean_object* v_x_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_x_2051_, v_x_2052_);
lean_dec(v_x_2052_);
return v_res_2053_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = lean_unsigned_to_nat(10u);
v___x_2064_ = lean_nat_to_int(v___x_2063_);
return v___x_2064_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_unsigned_to_nat(13u);
v___x_2069_ = lean_nat_to_int(v___x_2068_);
return v___x_2069_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_unsigned_to_nat(9u);
v___x_2077_ = lean_nat_to_int(v___x_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___redArg(lean_object* v_x_2081_){
_start:
{
lean_object* v_scheme_2082_; lean_object* v_authority_2083_; lean_object* v_path_2084_; lean_object* v_query_2085_; lean_object* v_fragment_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v_scheme_2082_ = lean_ctor_get(v_x_2081_, 0);
lean_inc_ref(v_scheme_2082_);
v_authority_2083_ = lean_ctor_get(v_x_2081_, 1);
lean_inc(v_authority_2083_);
v_path_2084_ = lean_ctor_get(v_x_2081_, 2);
lean_inc_ref(v_path_2084_);
v_query_2085_ = lean_ctor_get(v_x_2081_, 3);
lean_inc_ref(v_query_2085_);
v_fragment_2086_ = lean_ctor_get(v_x_2081_, 4);
lean_inc(v_fragment_2086_);
lean_dec_ref(v_x_2081_);
v___x_2087_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2088_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2089_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2090_ = l_String_quote(v_scheme_2082_);
v___x_2091_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
v___x_2092_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2089_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = 0;
v___x_2094_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2094_, 0, v___x_2092_);
lean_ctor_set_uint8(v___x_2094_, sizeof(void*)*1, v___x_2093_);
v___x_2095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2088_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
v___x_2096_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2095_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = lean_box(1);
v___x_2099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2097_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
v___x_2100_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__6));
v___x_2101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2099_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
lean_ctor_set(v___x_2102_, 1, v___x_2087_);
v___x_2103_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_2104_ = lean_unsigned_to_nat(0u);
v___x_2105_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_2083_, v___x_2104_);
v___x_2106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2103_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
v___x_2107_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set_uint8(v___x_2107_, sizeof(void*)*1, v___x_2093_);
v___x_2108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2102_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set(v___x_2109_, 1, v___x_2096_);
v___x_2110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
lean_ctor_set(v___x_2110_, 1, v___x_2098_);
v___x_2111_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_2112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v___x_2087_);
v___x_2114_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2115_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_2084_);
v___x_2116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
lean_ctor_set_uint8(v___x_2117_, sizeof(void*)*1, v___x_2093_);
v___x_2118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2113_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
lean_ctor_set(v___x_2119_, 1, v___x_2096_);
v___x_2120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v___x_2098_);
v___x_2121_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_2122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2120_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set(v___x_2123_, 1, v___x_2087_);
v___x_2124_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_2125_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_query_2085_);
v___x_2126_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2124_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set_uint8(v___x_2127_, sizeof(void*)*1, v___x_2093_);
v___x_2128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2123_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
lean_ctor_set(v___x_2129_, 1, v___x_2096_);
v___x_2130_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
lean_ctor_set(v___x_2130_, 1, v___x_2098_);
v___x_2131_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_2132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v___x_2087_);
v___x_2134_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_2135_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_fragment_2086_, v___x_2104_);
v___x_2136_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2134_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
lean_ctor_set_uint8(v___x_2137_, sizeof(void*)*1, v___x_2093_);
v___x_2138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2133_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2140_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2140_);
lean_ctor_set(v___x_2141_, 1, v___x_2138_);
v___x_2142_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2139_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
lean_ctor_set_uint8(v___x_2145_, sizeof(void*)*1, v___x_2093_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr(lean_object* v_x_2146_, lean_object* v_prec_2147_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Std_Http_instReprURI_repr___redArg(v_x_2146_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___boxed(lean_object* v_x_2149_, lean_object* v_prec_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Std_Http_instReprURI_repr(v_x_2149_, v_prec_2150_);
lean_dec(v_prec_2150_);
return v_res_2151_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object* v_x_2161_, lean_object* v_x_2162_){
_start:
{
if (lean_obj_tag(v_x_2161_) == 0)
{
if (lean_obj_tag(v_x_2162_) == 0)
{
uint8_t v___x_2163_; 
v___x_2163_ = 1;
return v___x_2163_;
}
else
{
uint8_t v___x_2164_; 
v___x_2164_ = 0;
return v___x_2164_;
}
}
else
{
if (lean_obj_tag(v_x_2162_) == 0)
{
uint8_t v___x_2165_; 
v___x_2165_ = 0;
return v___x_2165_;
}
else
{
lean_object* v_val_2166_; lean_object* v_val_2167_; uint8_t v___x_2168_; 
v_val_2166_ = lean_ctor_get(v_x_2161_, 0);
v_val_2167_ = lean_ctor_get(v_x_2162_, 0);
v___x_2168_ = l_Std_Http_URI_instBEqAuthority_beq(v_val_2166_, v_val_2167_);
return v___x_2168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object* v_x_2169_, lean_object* v_x_2170_){
_start:
{
uint8_t v_res_2171_; lean_object* v_r_2172_; 
v_res_2171_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_x_2169_, v_x_2170_);
lean_dec(v_x_2170_);
lean_dec(v_x_2169_);
v_r_2172_ = lean_box(v_res_2171_);
return v_r_2172_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object* v_x_2173_, lean_object* v_x_2174_){
_start:
{
if (lean_obj_tag(v_x_2173_) == 0)
{
if (lean_obj_tag(v_x_2174_) == 0)
{
uint8_t v___x_2175_; 
v___x_2175_ = 1;
return v___x_2175_;
}
else
{
uint8_t v___x_2176_; 
v___x_2176_ = 0;
return v___x_2176_;
}
}
else
{
if (lean_obj_tag(v_x_2174_) == 0)
{
uint8_t v___x_2177_; 
v___x_2177_ = 0;
return v___x_2177_;
}
else
{
lean_object* v_val_2178_; lean_object* v_val_2179_; uint8_t v___x_2180_; 
v_val_2178_ = lean_ctor_get(v_x_2173_, 0);
v_val_2179_ = lean_ctor_get(v_x_2174_, 0);
v___x_2180_ = lean_string_dec_eq(v_val_2178_, v_val_2179_);
return v___x_2180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object* v_x_2181_, lean_object* v_x_2182_){
_start:
{
uint8_t v_res_2183_; lean_object* v_r_2184_; 
v_res_2183_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_x_2181_, v_x_2182_);
lean_dec(v_x_2182_);
lean_dec(v_x_2181_);
v_r_2184_ = lean_box(v_res_2183_);
return v_r_2184_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object* v_x_2185_, lean_object* v_x_2186_){
_start:
{
lean_object* v_scheme_2187_; lean_object* v_authority_2188_; lean_object* v_path_2189_; lean_object* v_query_2190_; lean_object* v_fragment_2191_; lean_object* v_scheme_2192_; lean_object* v_authority_2193_; lean_object* v_path_2194_; lean_object* v_query_2195_; lean_object* v_fragment_2196_; uint8_t v___x_2197_; 
v_scheme_2187_ = lean_ctor_get(v_x_2185_, 0);
v_authority_2188_ = lean_ctor_get(v_x_2185_, 1);
v_path_2189_ = lean_ctor_get(v_x_2185_, 2);
v_query_2190_ = lean_ctor_get(v_x_2185_, 3);
v_fragment_2191_ = lean_ctor_get(v_x_2185_, 4);
v_scheme_2192_ = lean_ctor_get(v_x_2186_, 0);
v_authority_2193_ = lean_ctor_get(v_x_2186_, 1);
v_path_2194_ = lean_ctor_get(v_x_2186_, 2);
v_query_2195_ = lean_ctor_get(v_x_2186_, 3);
v_fragment_2196_ = lean_ctor_get(v_x_2186_, 4);
v___x_2197_ = lean_string_dec_eq(v_scheme_2187_, v_scheme_2192_);
if (v___x_2197_ == 0)
{
return v___x_2197_;
}
else
{
uint8_t v___x_2198_; 
v___x_2198_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_2188_, v_authority_2193_);
if (v___x_2198_ == 0)
{
return v___x_2198_;
}
else
{
uint8_t v___x_2199_; 
v___x_2199_ = l_Std_Http_URI_instBEqPath_beq(v_path_2189_, v_path_2194_);
if (v___x_2199_ == 0)
{
return v___x_2199_;
}
else
{
lean_object* v___x_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; 
v___x_2200_ = lean_array_get_size(v_query_2190_);
v___x_2201_ = lean_array_get_size(v_query_2195_);
v___x_2202_ = lean_nat_dec_eq(v___x_2200_, v___x_2201_);
if (v___x_2202_ == 0)
{
return v___x_2202_;
}
else
{
uint8_t v___x_2203_; 
v___x_2203_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_query_2190_, v_query_2195_, v___x_2200_);
if (v___x_2203_ == 0)
{
return v___x_2203_;
}
else
{
uint8_t v___x_2204_; 
v___x_2204_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_fragment_2191_, v_fragment_2196_);
return v___x_2204_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object* v_x_2205_, lean_object* v_x_2206_){
_start:
{
uint8_t v_res_2207_; lean_object* v_r_2208_; 
v_res_2207_ = l_Std_Http_instBEqURI_beq(v_x_2205_, v_x_2206_);
lean_dec_ref(v_x_2206_);
lean_dec_ref(v_x_2205_);
v_r_2208_ = lean_box(v_res_2207_);
return v_r_2208_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__2(lean_object* v___f_2213_, lean_object* v___f_2214_, lean_object* v_uri_2215_){
_start:
{
lean_object* v_scheme_2216_; lean_object* v_authority_2217_; lean_object* v_path_2218_; lean_object* v_query_2219_; lean_object* v_fragment_2220_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2257_; 
v_scheme_2216_ = lean_ctor_get(v_uri_2215_, 0);
lean_inc_ref(v_scheme_2216_);
v_authority_2217_ = lean_ctor_get(v_uri_2215_, 1);
lean_inc(v_authority_2217_);
v_path_2218_ = lean_ctor_get(v_uri_2215_, 2);
lean_inc_ref(v_path_2218_);
v_query_2219_ = lean_ctor_get(v_uri_2215_, 3);
lean_inc_ref(v_query_2219_);
v_fragment_2220_ = lean_ctor_get(v_uri_2215_, 4);
lean_inc(v_fragment_2220_);
lean_dec_ref(v_uri_2215_);
if (lean_obj_tag(v_authority_2217_) == 0)
{
lean_object* v___x_2268_; 
v___x_2268_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2257_ = v___x_2268_;
goto v___jp_2256_;
}
else
{
lean_object* v_val_2269_; lean_object* v_userInfo_2270_; lean_object* v_host_2271_; lean_object* v_port_2272_; lean_object* v___x_2273_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2292_; 
v_val_2269_ = lean_ctor_get(v_authority_2217_, 0);
lean_inc(v_val_2269_);
lean_dec_ref(v_authority_2217_);
v_userInfo_2270_ = lean_ctor_get(v_val_2269_, 0);
lean_inc(v_userInfo_2270_);
v_host_2271_ = lean_ctor_get(v_val_2269_, 1);
lean_inc_ref(v_host_2271_);
v_port_2272_ = lean_ctor_get(v_val_2269_, 2);
lean_inc(v_port_2272_);
lean_dec(v_val_2269_);
v___x_2273_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__1));
if (lean_obj_tag(v_userInfo_2270_) == 0)
{
lean_object* v___x_2302_; 
v___x_2302_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2292_ = v___x_2302_;
goto v___jp_2291_;
}
else
{
lean_object* v_val_2303_; lean_object* v_password_2304_; 
v_val_2303_ = lean_ctor_get(v_userInfo_2270_, 0);
lean_inc(v_val_2303_);
lean_dec_ref(v_userInfo_2270_);
v_password_2304_ = lean_ctor_get(v_val_2303_, 1);
if (lean_obj_tag(v_password_2304_) == 0)
{
lean_object* v_username_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_username_2305_ = lean_ctor_get(v_val_2303_, 0);
lean_inc_ref(v_username_2305_);
lean_dec(v_val_2303_);
v___x_2306_ = lean_string_from_utf8_unchecked(v_username_2305_);
v___x_2307_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2308_ = lean_string_append(v___x_2306_, v___x_2307_);
v___y_2292_ = v___x_2308_;
goto v___jp_2291_;
}
else
{
lean_object* v_username_2309_; lean_object* v_val_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
lean_inc_ref(v_password_2304_);
v_username_2309_ = lean_ctor_get(v_val_2303_, 0);
lean_inc_ref(v_username_2309_);
lean_dec(v_val_2303_);
v_val_2310_ = lean_ctor_get(v_password_2304_, 0);
lean_inc(v_val_2310_);
lean_dec_ref(v_password_2304_);
v___x_2311_ = lean_string_from_utf8_unchecked(v_username_2309_);
v___x_2312_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2313_ = lean_string_append(v___x_2311_, v___x_2312_);
v___x_2314_ = lean_string_from_utf8_unchecked(v_val_2310_);
v___x_2315_ = lean_string_append(v___x_2313_, v___x_2314_);
lean_dec_ref(v___x_2314_);
v___x_2316_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2317_ = lean_string_append(v___x_2315_, v___x_2316_);
v___y_2292_ = v___x_2317_;
goto v___jp_2291_;
}
}
v___jp_2274_:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2278_ = lean_string_append(v___y_2275_, v___y_2276_);
lean_dec_ref(v___y_2276_);
v___x_2279_ = lean_string_append(v___x_2278_, v___y_2277_);
lean_dec_ref(v___y_2277_);
v___x_2280_ = lean_string_append(v___x_2273_, v___x_2279_);
lean_dec_ref(v___x_2279_);
v___y_2257_ = v___x_2280_;
goto v___jp_2256_;
}
v___jp_2281_:
{
switch(lean_obj_tag(v_port_2272_))
{
case 0:
{
lean_object* v___x_2284_; 
v___x_2284_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2275_ = v___y_2282_;
v___y_2276_ = v___y_2283_;
v___y_2277_ = v___x_2284_;
goto v___jp_2274_;
}
case 1:
{
lean_object* v___x_2285_; 
v___x_2285_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_2275_ = v___y_2282_;
v___y_2276_ = v___y_2283_;
v___y_2277_ = v___x_2285_;
goto v___jp_2274_;
}
default: 
{
uint16_t v_port_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v_port_2286_ = lean_ctor_get_uint16(v_port_2272_, 0);
lean_dec_ref(v_port_2272_);
v___x_2287_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2288_ = lean_uint16_to_nat(v_port_2286_);
v___x_2289_ = l_Nat_reprFast(v___x_2288_);
v___x_2290_ = lean_string_append(v___x_2287_, v___x_2289_);
lean_dec_ref(v___x_2289_);
v___y_2275_ = v___y_2282_;
v___y_2276_ = v___y_2283_;
v___y_2277_ = v___x_2290_;
goto v___jp_2274_;
}
}
}
v___jp_2291_:
{
switch(lean_obj_tag(v_host_2271_))
{
case 0:
{
lean_object* v_name_2293_; 
v_name_2293_ = lean_ctor_get(v_host_2271_, 0);
lean_inc_ref(v_name_2293_);
lean_dec_ref(v_host_2271_);
v___y_2282_ = v___y_2292_;
v___y_2283_ = v_name_2293_;
goto v___jp_2281_;
}
case 1:
{
lean_object* v_ipv4_2294_; lean_object* v___x_2295_; 
v_ipv4_2294_ = lean_ctor_get(v_host_2271_, 0);
lean_inc_ref(v_ipv4_2294_);
lean_dec_ref(v_host_2271_);
v___x_2295_ = lean_uv_ntop_v4(v_ipv4_2294_);
lean_dec_ref(v_ipv4_2294_);
v___y_2282_ = v___y_2292_;
v___y_2283_ = v___x_2295_;
goto v___jp_2281_;
}
default: 
{
lean_object* v_ipv6_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v_ipv6_2296_ = lean_ctor_get(v_host_2271_, 0);
lean_inc_ref(v_ipv6_2296_);
lean_dec_ref(v_host_2271_);
v___x_2297_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_2298_ = lean_uv_ntop_v6(v_ipv6_2296_);
lean_dec_ref(v_ipv6_2296_);
v___x_2299_ = lean_string_append(v___x_2297_, v___x_2298_);
lean_dec_ref(v___x_2298_);
v___x_2300_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_2301_ = lean_string_append(v___x_2299_, v___x_2300_);
v___y_2282_ = v___y_2292_;
v___y_2283_ = v___x_2301_;
goto v___jp_2281_;
}
}
}
}
v___jp_2221_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2226_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2227_ = lean_string_append(v_scheme_2216_, v___x_2226_);
v___x_2228_ = lean_string_append(v___x_2227_, v___y_2222_);
lean_dec_ref(v___y_2222_);
v___x_2229_ = lean_string_append(v___x_2228_, v___y_2224_);
lean_dec_ref(v___y_2224_);
v___x_2230_ = lean_string_append(v___x_2229_, v___y_2223_);
lean_dec_ref(v___y_2223_);
v___x_2231_ = lean_string_append(v___x_2230_, v___y_2225_);
lean_dec_ref(v___y_2225_);
return v___x_2231_;
}
v___jp_2232_:
{
if (lean_obj_tag(v_fragment_2220_) == 0)
{
lean_object* v___x_2236_; 
v___x_2236_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2222_ = v___y_2233_;
v___y_2223_ = v___y_2235_;
v___y_2224_ = v___y_2234_;
v___y_2225_ = v___x_2236_;
goto v___jp_2221_;
}
else
{
lean_object* v_val_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v_val_2237_ = lean_ctor_get(v_fragment_2220_, 0);
lean_inc(v_val_2237_);
lean_dec_ref(v_fragment_2220_);
v___x_2238_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__0));
v___x_2239_ = l_Std_Http_URI_EncodedFragment_encode(v_val_2237_);
lean_dec(v_val_2237_);
v___x_2240_ = lean_string_from_utf8_unchecked(v___x_2239_);
v___x_2241_ = lean_string_append(v___x_2238_, v___x_2240_);
lean_dec_ref(v___x_2240_);
v___y_2222_ = v___y_2233_;
v___y_2223_ = v___y_2235_;
v___y_2224_ = v___y_2234_;
v___y_2225_ = v___x_2241_;
goto v___jp_2221_;
}
}
v___jp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; 
v___x_2245_ = lean_array_get_size(v_query_2219_);
v___x_2246_ = lean_unsigned_to_nat(0u);
v___x_2247_ = lean_nat_dec_eq(v___x_2245_, v___x_2246_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v_encodedParams_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2248_ = lean_array_to_list(v_query_2219_);
v___x_2249_ = lean_box(0);
v_encodedParams_2250_ = l_List_mapTR_loop___redArg(v___f_2213_, v___x_2248_, v___x_2249_);
v___x_2251_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2252_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2253_ = l_String_intercalate(v___x_2252_, v_encodedParams_2250_);
v___x_2254_ = lean_string_append(v___x_2251_, v___x_2253_);
lean_dec_ref(v___x_2253_);
v___y_2233_ = v___y_2243_;
v___y_2234_ = v___y_2244_;
v___y_2235_ = v___x_2254_;
goto v___jp_2232_;
}
else
{
lean_object* v___x_2255_; 
lean_dec_ref(v_query_2219_);
lean_dec_ref(v___f_2213_);
v___x_2255_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2233_ = v___y_2243_;
v___y_2234_ = v___y_2244_;
v___y_2235_ = v___x_2255_;
goto v___jp_2232_;
}
}
v___jp_2256_:
{
lean_object* v_segments_2258_; uint8_t v_absolute_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; size_t v_sz_2262_; size_t v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v_result_2266_; 
v_segments_2258_ = lean_ctor_get(v_path_2218_, 0);
lean_inc_ref(v_segments_2258_);
v_absolute_2259_ = lean_ctor_get_uint8(v_path_2218_, sizeof(void*)*1);
lean_dec_ref(v_path_2218_);
v___x_2260_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_2261_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_2262_ = lean_array_size(v_segments_2258_);
v___x_2263_ = ((size_t)0ULL);
v___x_2264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2261_, v___f_2214_, v_sz_2262_, v___x_2263_, v_segments_2258_);
v___x_2265_ = lean_array_to_list(v___x_2264_);
v_result_2266_ = l_String_intercalate(v___x_2260_, v___x_2265_);
if (v_absolute_2259_ == 0)
{
v___y_2243_ = v___y_2257_;
v___y_2244_ = v_result_2266_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2267_; 
v___x_2267_ = lean_string_append(v___x_2260_, v_result_2266_);
lean_dec_ref(v_result_2266_);
v___y_2243_ = v___y_2257_;
v___y_2244_ = v___x_2267_;
goto v___jp_2242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x3f(lean_object* v_b_2337_, lean_object* v_scheme_2338_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Std_Http_URI_Scheme_ofString_x3f(v_scheme_2338_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v___x_2340_; 
lean_dec_ref(v_b_2337_);
v___x_2340_ = lean_box(0);
return v___x_2340_;
}
else
{
lean_object* v_userInfo_2341_; lean_object* v_host_2342_; lean_object* v_port_2343_; lean_object* v_pathSegments_2344_; lean_object* v_query_2345_; lean_object* v_fragment_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2361_; 
v_userInfo_2341_ = lean_ctor_get(v_b_2337_, 1);
v_host_2342_ = lean_ctor_get(v_b_2337_, 2);
v_port_2343_ = lean_ctor_get(v_b_2337_, 3);
v_pathSegments_2344_ = lean_ctor_get(v_b_2337_, 4);
v_query_2345_ = lean_ctor_get(v_b_2337_, 5);
v_fragment_2346_ = lean_ctor_get(v_b_2337_, 6);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_b_2337_);
if (v_isSharedCheck_2361_ == 0)
{
lean_object* v_unused_2362_; 
v_unused_2362_ = lean_ctor_get(v_b_2337_, 0);
lean_dec(v_unused_2362_);
v___x_2348_ = v_b_2337_;
v_isShared_2349_ = v_isSharedCheck_2361_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_fragment_2346_);
lean_inc(v_query_2345_);
lean_inc(v_pathSegments_2344_);
lean_inc(v_port_2343_);
lean_inc(v_host_2342_);
lean_inc(v_userInfo_2341_);
lean_dec(v_b_2337_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2361_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
lean_inc_ref(v___x_2339_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2339_);
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2339_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_userInfo_2341_);
lean_ctor_set(v_reuseFailAlloc_2360_, 2, v_host_2342_);
lean_ctor_set(v_reuseFailAlloc_2360_, 3, v_port_2343_);
lean_ctor_set(v_reuseFailAlloc_2360_, 4, v_pathSegments_2344_);
lean_ctor_set(v_reuseFailAlloc_2360_, 5, v_query_2345_);
lean_ctor_set(v_reuseFailAlloc_2360_, 6, v_fragment_2346_);
v___x_2351_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2358_ == 0)
{
lean_object* v_unused_2359_; 
v_unused_2359_ = lean_ctor_get(v___x_2339_, 0);
lean_dec(v_unused_2359_);
v___x_2353_ = v___x_2339_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_dec(v___x_2339_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2351_);
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(lean_object* v_msg_2363_){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = ((lean_object*)(l_Std_Http_URI_instInhabitedBuilder_default));
v___x_2365_ = lean_panic_fn_borrowed(v___x_2364_, v_msg_2363_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x21(lean_object* v_b_2367_, lean_object* v_scheme_2368_){
_start:
{
lean_object* v___x_2369_; 
lean_inc_ref(v_scheme_2368_);
v___x_2369_ = l_Std_Http_URI_Builder_setScheme_x3f(v_b_2367_, v_scheme_2368_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2370_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2371_ = ((lean_object*)(l_Std_Http_URI_Builder_setScheme_x21___closed__0));
v___x_2372_ = lean_unsigned_to_nat(677u);
v___x_2373_ = lean_unsigned_to_nat(14u);
v___x_2374_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_2375_ = l_String_quote(v_scheme_2368_);
v___x_2376_ = lean_string_append(v___x_2374_, v___x_2375_);
lean_dec_ref(v___x_2375_);
v___x_2377_ = l_mkPanicMessageWithDecl(v___x_2370_, v___x_2371_, v___x_2372_, v___x_2373_, v___x_2376_);
lean_dec_ref(v___x_2376_);
v___x_2378_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2377_);
return v___x_2378_;
}
else
{
lean_object* v_val_2379_; 
lean_dec_ref(v_scheme_2368_);
v_val_2379_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_val_2379_);
lean_dec_ref(v___x_2369_);
return v_val_2379_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo(lean_object* v_b_2380_, lean_object* v_username_2381_, lean_object* v_password_2382_){
_start:
{
lean_object* v_scheme_2383_; lean_object* v_host_2384_; lean_object* v_port_2385_; lean_object* v_pathSegments_2386_; lean_object* v_query_2387_; lean_object* v_fragment_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2411_; 
v_scheme_2383_ = lean_ctor_get(v_b_2380_, 0);
v_host_2384_ = lean_ctor_get(v_b_2380_, 2);
v_port_2385_ = lean_ctor_get(v_b_2380_, 3);
v_pathSegments_2386_ = lean_ctor_get(v_b_2380_, 4);
v_query_2387_ = lean_ctor_get(v_b_2380_, 5);
v_fragment_2388_ = lean_ctor_get(v_b_2380_, 6);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_b_2380_);
if (v_isSharedCheck_2411_ == 0)
{
lean_object* v_unused_2412_; 
v_unused_2412_ = lean_ctor_get(v_b_2380_, 1);
lean_dec(v_unused_2412_);
v___x_2390_ = v_b_2380_;
v_isShared_2391_ = v_isSharedCheck_2411_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_fragment_2388_);
lean_inc(v_query_2387_);
lean_inc(v_pathSegments_2386_);
lean_inc(v_port_2385_);
lean_inc(v_host_2384_);
lean_inc(v_scheme_2383_);
lean_dec(v_b_2380_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2411_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___y_2393_; lean_object* v___x_2398_; 
v___x_2398_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_2381_);
if (lean_obj_tag(v_password_2382_) == 0)
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = lean_box(0);
v___x_2400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___y_2393_ = v___x_2400_;
goto v___jp_2392_;
}
else
{
lean_object* v_val_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2410_; 
v_val_2401_ = lean_ctor_get(v_password_2382_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_password_2382_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2403_ = v_password_2382_;
v_isShared_2404_ = v_isSharedCheck_2410_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_val_2401_);
lean_dec(v_password_2382_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2410_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2405_; lean_object* v___x_2407_; 
v___x_2405_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_2401_);
lean_dec(v_val_2401_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v___x_2405_);
v___x_2407_ = v___x_2403_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2398_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
v___y_2393_ = v___x_2408_;
goto v___jp_2392_;
}
}
}
v___jp_2392_:
{
lean_object* v___x_2394_; lean_object* v___x_2396_; 
v___x_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___y_2393_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 1, v___x_2394_);
v___x_2396_ = v___x_2390_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_scheme_2383_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_host_2384_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_port_2385_);
lean_ctor_set(v_reuseFailAlloc_2397_, 4, v_pathSegments_2386_);
lean_ctor_set(v_reuseFailAlloc_2397_, 5, v_query_2387_);
lean_ctor_set(v_reuseFailAlloc_2397_, 6, v_fragment_2388_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo___boxed(lean_object* v_b_2413_, lean_object* v_username_2414_, lean_object* v_password_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Std_Http_URI_Builder_setUserInfo(v_b_2413_, v_username_2414_, v_password_2415_);
lean_dec_ref(v_username_2414_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x3f(lean_object* v_b_2417_, lean_object* v_name_2418_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Std_Http_URI_DomainName_ofString_x3f(v_name_2418_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v___x_2420_; 
lean_dec_ref(v_b_2417_);
v___x_2420_ = lean_box(0);
return v___x_2420_;
}
else
{
lean_object* v_val_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2444_; 
v_val_2421_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2423_ = v___x_2419_;
v_isShared_2424_ = v_isSharedCheck_2444_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_val_2421_);
lean_dec(v___x_2419_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2444_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v_scheme_2425_; lean_object* v_userInfo_2426_; lean_object* v_port_2427_; lean_object* v_pathSegments_2428_; lean_object* v_query_2429_; lean_object* v_fragment_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2442_; 
v_scheme_2425_ = lean_ctor_get(v_b_2417_, 0);
v_userInfo_2426_ = lean_ctor_get(v_b_2417_, 1);
v_port_2427_ = lean_ctor_get(v_b_2417_, 3);
v_pathSegments_2428_ = lean_ctor_get(v_b_2417_, 4);
v_query_2429_ = lean_ctor_get(v_b_2417_, 5);
v_fragment_2430_ = lean_ctor_get(v_b_2417_, 6);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_b_2417_);
if (v_isSharedCheck_2442_ == 0)
{
lean_object* v_unused_2443_; 
v_unused_2443_ = lean_ctor_get(v_b_2417_, 2);
lean_dec(v_unused_2443_);
v___x_2432_ = v_b_2417_;
v_isShared_2433_ = v_isSharedCheck_2442_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_fragment_2430_);
lean_inc(v_query_2429_);
lean_inc(v_pathSegments_2428_);
lean_inc(v_port_2427_);
lean_inc(v_userInfo_2426_);
lean_inc(v_scheme_2425_);
lean_dec(v_b_2417_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2442_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v_val_2421_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2434_);
v___x_2436_ = v___x_2423_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2438_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 2, v___x_2436_);
v___x_2438_ = v___x_2432_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_scheme_2425_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_userInfo_2426_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v___x_2436_);
lean_ctor_set(v_reuseFailAlloc_2440_, 3, v_port_2427_);
lean_ctor_set(v_reuseFailAlloc_2440_, 4, v_pathSegments_2428_);
lean_ctor_set(v_reuseFailAlloc_2440_, 5, v_query_2429_);
lean_ctor_set(v_reuseFailAlloc_2440_, 6, v_fragment_2430_);
v___x_2438_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v___x_2439_; 
v___x_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
return v___x_2439_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x21(lean_object* v_b_2447_, lean_object* v_name_2448_){
_start:
{
lean_object* v___x_2449_; 
lean_inc_ref(v_name_2448_);
v___x_2449_ = l_Std_Http_URI_Builder_setHost_x3f(v_b_2447_, v_name_2448_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2450_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2451_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__0));
v___x_2452_ = lean_unsigned_to_nat(706u);
v___x_2453_ = lean_unsigned_to_nat(14u);
v___x_2454_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__1));
v___x_2455_ = l_String_quote(v_name_2448_);
v___x_2456_ = lean_string_append(v___x_2454_, v___x_2455_);
lean_dec_ref(v___x_2455_);
v___x_2457_ = l_mkPanicMessageWithDecl(v___x_2450_, v___x_2451_, v___x_2452_, v___x_2453_, v___x_2456_);
lean_dec_ref(v___x_2456_);
v___x_2458_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2457_);
return v___x_2458_;
}
else
{
lean_object* v_val_2459_; 
lean_dec_ref(v_name_2448_);
v_val_2459_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_val_2459_);
lean_dec_ref(v___x_2449_);
return v_val_2459_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv4(lean_object* v_b_2460_, lean_object* v_addr_2461_){
_start:
{
lean_object* v_scheme_2462_; lean_object* v_userInfo_2463_; lean_object* v_port_2464_; lean_object* v_pathSegments_2465_; lean_object* v_query_2466_; lean_object* v_fragment_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2476_; 
v_scheme_2462_ = lean_ctor_get(v_b_2460_, 0);
v_userInfo_2463_ = lean_ctor_get(v_b_2460_, 1);
v_port_2464_ = lean_ctor_get(v_b_2460_, 3);
v_pathSegments_2465_ = lean_ctor_get(v_b_2460_, 4);
v_query_2466_ = lean_ctor_get(v_b_2460_, 5);
v_fragment_2467_ = lean_ctor_get(v_b_2460_, 6);
v_isSharedCheck_2476_ = !lean_is_exclusive(v_b_2460_);
if (v_isSharedCheck_2476_ == 0)
{
lean_object* v_unused_2477_; 
v_unused_2477_ = lean_ctor_get(v_b_2460_, 2);
lean_dec(v_unused_2477_);
v___x_2469_ = v_b_2460_;
v_isShared_2470_ = v_isSharedCheck_2476_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_fragment_2467_);
lean_inc(v_query_2466_);
lean_inc(v_pathSegments_2465_);
lean_inc(v_port_2464_);
lean_inc(v_userInfo_2463_);
lean_inc(v_scheme_2462_);
lean_dec(v_b_2460_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2476_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2471_, 0, v_addr_2461_);
v___x_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 2, v___x_2472_);
v___x_2474_ = v___x_2469_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_scheme_2462_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_userInfo_2463_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_port_2464_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v_pathSegments_2465_);
lean_ctor_set(v_reuseFailAlloc_2475_, 5, v_query_2466_);
lean_ctor_set(v_reuseFailAlloc_2475_, 6, v_fragment_2467_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv6(lean_object* v_b_2478_, lean_object* v_addr_2479_){
_start:
{
lean_object* v_scheme_2480_; lean_object* v_userInfo_2481_; lean_object* v_port_2482_; lean_object* v_pathSegments_2483_; lean_object* v_query_2484_; lean_object* v_fragment_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2494_; 
v_scheme_2480_ = lean_ctor_get(v_b_2478_, 0);
v_userInfo_2481_ = lean_ctor_get(v_b_2478_, 1);
v_port_2482_ = lean_ctor_get(v_b_2478_, 3);
v_pathSegments_2483_ = lean_ctor_get(v_b_2478_, 4);
v_query_2484_ = lean_ctor_get(v_b_2478_, 5);
v_fragment_2485_ = lean_ctor_get(v_b_2478_, 6);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_b_2478_);
if (v_isSharedCheck_2494_ == 0)
{
lean_object* v_unused_2495_; 
v_unused_2495_ = lean_ctor_get(v_b_2478_, 2);
lean_dec(v_unused_2495_);
v___x_2487_ = v_b_2478_;
v_isShared_2488_ = v_isSharedCheck_2494_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_fragment_2485_);
lean_inc(v_query_2484_);
lean_inc(v_pathSegments_2483_);
lean_inc(v_port_2482_);
lean_inc(v_userInfo_2481_);
lean_inc(v_scheme_2480_);
lean_dec(v_b_2478_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2494_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2489_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2489_, 0, v_addr_2479_);
v___x_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 2, v___x_2490_);
v___x_2492_ = v___x_2487_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_scheme_2480_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_userInfo_2481_);
lean_ctor_set(v_reuseFailAlloc_2493_, 2, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2493_, 3, v_port_2482_);
lean_ctor_set(v_reuseFailAlloc_2493_, 4, v_pathSegments_2483_);
lean_ctor_set(v_reuseFailAlloc_2493_, 5, v_query_2484_);
lean_ctor_set(v_reuseFailAlloc_2493_, 6, v_fragment_2485_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort(lean_object* v_b_2496_, uint16_t v_port_2497_){
_start:
{
lean_object* v_scheme_2498_; lean_object* v_userInfo_2499_; lean_object* v_host_2500_; lean_object* v_pathSegments_2501_; lean_object* v_query_2502_; lean_object* v_fragment_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2511_; 
v_scheme_2498_ = lean_ctor_get(v_b_2496_, 0);
v_userInfo_2499_ = lean_ctor_get(v_b_2496_, 1);
v_host_2500_ = lean_ctor_get(v_b_2496_, 2);
v_pathSegments_2501_ = lean_ctor_get(v_b_2496_, 4);
v_query_2502_ = lean_ctor_get(v_b_2496_, 5);
v_fragment_2503_ = lean_ctor_get(v_b_2496_, 6);
v_isSharedCheck_2511_ = !lean_is_exclusive(v_b_2496_);
if (v_isSharedCheck_2511_ == 0)
{
lean_object* v_unused_2512_; 
v_unused_2512_ = lean_ctor_get(v_b_2496_, 3);
lean_dec(v_unused_2512_);
v___x_2505_ = v_b_2496_;
v_isShared_2506_ = v_isSharedCheck_2511_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_fragment_2503_);
lean_inc(v_query_2502_);
lean_inc(v_pathSegments_2501_);
lean_inc(v_host_2500_);
lean_inc(v_userInfo_2499_);
lean_inc(v_scheme_2498_);
lean_dec(v_b_2496_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2511_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2507_ = lean_alloc_ctor(2, 0, 2);
lean_ctor_set_uint16(v___x_2507_, 0, v_port_2497_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 3, v___x_2507_);
v___x_2509_ = v___x_2505_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_scheme_2498_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_userInfo_2499_);
lean_ctor_set(v_reuseFailAlloc_2510_, 2, v_host_2500_);
lean_ctor_set(v_reuseFailAlloc_2510_, 3, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2510_, 4, v_pathSegments_2501_);
lean_ctor_set(v_reuseFailAlloc_2510_, 5, v_query_2502_);
lean_ctor_set(v_reuseFailAlloc_2510_, 6, v_fragment_2503_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort___boxed(lean_object* v_b_2513_, lean_object* v_port_2514_){
_start:
{
uint16_t v_port_boxed_2515_; lean_object* v_res_2516_; 
v_port_boxed_2515_ = lean_unbox(v_port_2514_);
v_res_2516_ = l_Std_Http_URI_Builder_setPort(v_b_2513_, v_port_boxed_2515_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPath(lean_object* v_b_2517_, lean_object* v_segments_2518_){
_start:
{
lean_object* v_scheme_2519_; lean_object* v_userInfo_2520_; lean_object* v_host_2521_; lean_object* v_port_2522_; lean_object* v_query_2523_; lean_object* v_fragment_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
v_scheme_2519_ = lean_ctor_get(v_b_2517_, 0);
v_userInfo_2520_ = lean_ctor_get(v_b_2517_, 1);
v_host_2521_ = lean_ctor_get(v_b_2517_, 2);
v_port_2522_ = lean_ctor_get(v_b_2517_, 3);
v_query_2523_ = lean_ctor_get(v_b_2517_, 5);
v_fragment_2524_ = lean_ctor_get(v_b_2517_, 6);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_b_2517_);
if (v_isSharedCheck_2531_ == 0)
{
lean_object* v_unused_2532_; 
v_unused_2532_ = lean_ctor_get(v_b_2517_, 4);
lean_dec(v_unused_2532_);
v___x_2526_ = v_b_2517_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_fragment_2524_);
lean_inc(v_query_2523_);
lean_inc(v_port_2522_);
lean_inc(v_host_2521_);
lean_inc(v_userInfo_2520_);
lean_inc(v_scheme_2519_);
lean_dec(v_b_2517_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 4, v_segments_2518_);
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_scheme_2519_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_userInfo_2520_);
lean_ctor_set(v_reuseFailAlloc_2530_, 2, v_host_2521_);
lean_ctor_set(v_reuseFailAlloc_2530_, 3, v_port_2522_);
lean_ctor_set(v_reuseFailAlloc_2530_, 4, v_segments_2518_);
lean_ctor_set(v_reuseFailAlloc_2530_, 5, v_query_2523_);
lean_ctor_set(v_reuseFailAlloc_2530_, 6, v_fragment_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_appendPathSegment(lean_object* v_b_2533_, lean_object* v_segment_2534_){
_start:
{
lean_object* v_scheme_2535_; lean_object* v_userInfo_2536_; lean_object* v_host_2537_; lean_object* v_port_2538_; lean_object* v_pathSegments_2539_; lean_object* v_query_2540_; lean_object* v_fragment_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2549_; 
v_scheme_2535_ = lean_ctor_get(v_b_2533_, 0);
v_userInfo_2536_ = lean_ctor_get(v_b_2533_, 1);
v_host_2537_ = lean_ctor_get(v_b_2533_, 2);
v_port_2538_ = lean_ctor_get(v_b_2533_, 3);
v_pathSegments_2539_ = lean_ctor_get(v_b_2533_, 4);
v_query_2540_ = lean_ctor_get(v_b_2533_, 5);
v_fragment_2541_ = lean_ctor_get(v_b_2533_, 6);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_b_2533_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2543_ = v_b_2533_;
v_isShared_2544_ = v_isSharedCheck_2549_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_fragment_2541_);
lean_inc(v_query_2540_);
lean_inc(v_pathSegments_2539_);
lean_inc(v_port_2538_);
lean_inc(v_host_2537_);
lean_inc(v_userInfo_2536_);
lean_inc(v_scheme_2535_);
lean_dec(v_b_2533_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2549_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2545_ = lean_array_push(v_pathSegments_2539_, v_segment_2534_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 4, v___x_2545_);
v___x_2547_ = v___x_2543_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_scheme_2535_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_userInfo_2536_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v_host_2537_);
lean_ctor_set(v_reuseFailAlloc_2548_, 3, v_port_2538_);
lean_ctor_set(v_reuseFailAlloc_2548_, 4, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2548_, 5, v_query_2540_);
lean_ctor_set(v_reuseFailAlloc_2548_, 6, v_fragment_2541_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryParam(lean_object* v_b_2550_, lean_object* v_key_2551_, lean_object* v_value_2552_){
_start:
{
lean_object* v_scheme_2553_; lean_object* v_userInfo_2554_; lean_object* v_host_2555_; lean_object* v_port_2556_; lean_object* v_pathSegments_2557_; lean_object* v_query_2558_; lean_object* v_fragment_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2569_; 
v_scheme_2553_ = lean_ctor_get(v_b_2550_, 0);
v_userInfo_2554_ = lean_ctor_get(v_b_2550_, 1);
v_host_2555_ = lean_ctor_get(v_b_2550_, 2);
v_port_2556_ = lean_ctor_get(v_b_2550_, 3);
v_pathSegments_2557_ = lean_ctor_get(v_b_2550_, 4);
v_query_2558_ = lean_ctor_get(v_b_2550_, 5);
v_fragment_2559_ = lean_ctor_get(v_b_2550_, 6);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_b_2550_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2561_ = v_b_2550_;
v_isShared_2562_ = v_isSharedCheck_2569_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_fragment_2559_);
lean_inc(v_query_2558_);
lean_inc(v_pathSegments_2557_);
lean_inc(v_port_2556_);
lean_inc(v_host_2555_);
lean_inc(v_userInfo_2554_);
lean_inc(v_scheme_2553_);
lean_dec(v_b_2550_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2569_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2563_, 0, v_value_2552_);
v___x_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2564_, 0, v_key_2551_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = lean_array_push(v_query_2558_, v___x_2564_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 5, v___x_2565_);
v___x_2567_ = v___x_2561_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_scheme_2553_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_userInfo_2554_);
lean_ctor_set(v_reuseFailAlloc_2568_, 2, v_host_2555_);
lean_ctor_set(v_reuseFailAlloc_2568_, 3, v_port_2556_);
lean_ctor_set(v_reuseFailAlloc_2568_, 4, v_pathSegments_2557_);
lean_ctor_set(v_reuseFailAlloc_2568_, 5, v___x_2565_);
lean_ctor_set(v_reuseFailAlloc_2568_, 6, v_fragment_2559_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryFlag(lean_object* v_b_2570_, lean_object* v_key_2571_){
_start:
{
lean_object* v_scheme_2572_; lean_object* v_userInfo_2573_; lean_object* v_host_2574_; lean_object* v_port_2575_; lean_object* v_pathSegments_2576_; lean_object* v_query_2577_; lean_object* v_fragment_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2588_; 
v_scheme_2572_ = lean_ctor_get(v_b_2570_, 0);
v_userInfo_2573_ = lean_ctor_get(v_b_2570_, 1);
v_host_2574_ = lean_ctor_get(v_b_2570_, 2);
v_port_2575_ = lean_ctor_get(v_b_2570_, 3);
v_pathSegments_2576_ = lean_ctor_get(v_b_2570_, 4);
v_query_2577_ = lean_ctor_get(v_b_2570_, 5);
v_fragment_2578_ = lean_ctor_get(v_b_2570_, 6);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_b_2570_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2580_ = v_b_2570_;
v_isShared_2581_ = v_isSharedCheck_2588_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_fragment_2578_);
lean_inc(v_query_2577_);
lean_inc(v_pathSegments_2576_);
lean_inc(v_port_2575_);
lean_inc(v_host_2574_);
lean_inc(v_userInfo_2573_);
lean_inc(v_scheme_2572_);
lean_dec(v_b_2570_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2588_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2582_ = lean_box(0);
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v_key_2571_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = lean_array_push(v_query_2577_, v___x_2583_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 5, v___x_2584_);
v___x_2586_ = v___x_2580_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_scheme_2572_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_userInfo_2573_);
lean_ctor_set(v_reuseFailAlloc_2587_, 2, v_host_2574_);
lean_ctor_set(v_reuseFailAlloc_2587_, 3, v_port_2575_);
lean_ctor_set(v_reuseFailAlloc_2587_, 4, v_pathSegments_2576_);
lean_ctor_set(v_reuseFailAlloc_2587_, 5, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2587_, 6, v_fragment_2578_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setQuery(lean_object* v_b_2589_, lean_object* v_query_2590_){
_start:
{
lean_object* v_scheme_2591_; lean_object* v_userInfo_2592_; lean_object* v_host_2593_; lean_object* v_port_2594_; lean_object* v_pathSegments_2595_; lean_object* v_fragment_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
v_scheme_2591_ = lean_ctor_get(v_b_2589_, 0);
v_userInfo_2592_ = lean_ctor_get(v_b_2589_, 1);
v_host_2593_ = lean_ctor_get(v_b_2589_, 2);
v_port_2594_ = lean_ctor_get(v_b_2589_, 3);
v_pathSegments_2595_ = lean_ctor_get(v_b_2589_, 4);
v_fragment_2596_ = lean_ctor_get(v_b_2589_, 6);
v_isSharedCheck_2603_ = !lean_is_exclusive(v_b_2589_);
if (v_isSharedCheck_2603_ == 0)
{
lean_object* v_unused_2604_; 
v_unused_2604_ = lean_ctor_get(v_b_2589_, 5);
lean_dec(v_unused_2604_);
v___x_2598_ = v_b_2589_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_fragment_2596_);
lean_inc(v_pathSegments_2595_);
lean_inc(v_port_2594_);
lean_inc(v_host_2593_);
lean_inc(v_userInfo_2592_);
lean_inc(v_scheme_2591_);
lean_dec(v_b_2589_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 5, v_query_2590_);
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_scheme_2591_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_userInfo_2592_);
lean_ctor_set(v_reuseFailAlloc_2602_, 2, v_host_2593_);
lean_ctor_set(v_reuseFailAlloc_2602_, 3, v_port_2594_);
lean_ctor_set(v_reuseFailAlloc_2602_, 4, v_pathSegments_2595_);
lean_ctor_set(v_reuseFailAlloc_2602_, 5, v_query_2590_);
lean_ctor_set(v_reuseFailAlloc_2602_, 6, v_fragment_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setFragment(lean_object* v_b_2605_, lean_object* v_fragment_2606_){
_start:
{
lean_object* v_scheme_2607_; lean_object* v_userInfo_2608_; lean_object* v_host_2609_; lean_object* v_port_2610_; lean_object* v_pathSegments_2611_; lean_object* v_query_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2620_; 
v_scheme_2607_ = lean_ctor_get(v_b_2605_, 0);
v_userInfo_2608_ = lean_ctor_get(v_b_2605_, 1);
v_host_2609_ = lean_ctor_get(v_b_2605_, 2);
v_port_2610_ = lean_ctor_get(v_b_2605_, 3);
v_pathSegments_2611_ = lean_ctor_get(v_b_2605_, 4);
v_query_2612_ = lean_ctor_get(v_b_2605_, 5);
v_isSharedCheck_2620_ = !lean_is_exclusive(v_b_2605_);
if (v_isSharedCheck_2620_ == 0)
{
lean_object* v_unused_2621_; 
v_unused_2621_ = lean_ctor_get(v_b_2605_, 6);
lean_dec(v_unused_2621_);
v___x_2614_ = v_b_2605_;
v_isShared_2615_ = v_isSharedCheck_2620_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_query_2612_);
lean_inc(v_pathSegments_2611_);
lean_inc(v_port_2610_);
lean_inc(v_host_2609_);
lean_inc(v_userInfo_2608_);
lean_inc(v_scheme_2607_);
lean_dec(v_b_2605_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2620_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2616_; lean_object* v___x_2618_; 
v___x_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2616_, 0, v_fragment_2606_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 6, v___x_2616_);
v___x_2618_ = v___x_2614_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_scheme_2607_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_userInfo_2608_);
lean_ctor_set(v_reuseFailAlloc_2619_, 2, v_host_2609_);
lean_ctor_set(v_reuseFailAlloc_2619_, 3, v_port_2610_);
lean_ctor_set(v_reuseFailAlloc_2619_, 4, v_pathSegments_2611_);
lean_ctor_set(v_reuseFailAlloc_2619_, 5, v_query_2612_);
lean_ctor_set(v_reuseFailAlloc_2619_, 6, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(size_t v_sz_2622_, size_t v_i_2623_, lean_object* v_bs_2624_){
_start:
{
uint8_t v___x_2625_; 
v___x_2625_ = lean_usize_dec_lt(v_i_2623_, v_sz_2622_);
if (v___x_2625_ == 0)
{
return v_bs_2624_;
}
else
{
lean_object* v_v_2626_; lean_object* v___x_2627_; lean_object* v_bs_x27_2628_; lean_object* v___x_2629_; size_t v___x_2630_; size_t v___x_2631_; lean_object* v___x_2632_; 
v_v_2626_ = lean_array_uget(v_bs_2624_, v_i_2623_);
v___x_2627_ = lean_unsigned_to_nat(0u);
v_bs_x27_2628_ = lean_array_uset(v_bs_2624_, v_i_2623_, v___x_2627_);
v___x_2629_ = l_Std_Http_URI_EncodedSegment_encode(v_v_2626_);
lean_dec(v_v_2626_);
v___x_2630_ = ((size_t)1ULL);
v___x_2631_ = lean_usize_add(v_i_2623_, v___x_2630_);
v___x_2632_ = lean_array_uset(v_bs_x27_2628_, v_i_2623_, v___x_2629_);
v_i_2623_ = v___x_2631_;
v_bs_2624_ = v___x_2632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0___boxed(lean_object* v_sz_2634_, lean_object* v_i_2635_, lean_object* v_bs_2636_){
_start:
{
size_t v_sz_boxed_2637_; size_t v_i_boxed_2638_; lean_object* v_res_2639_; 
v_sz_boxed_2637_ = lean_unbox_usize(v_sz_2634_);
lean_dec(v_sz_2634_);
v_i_boxed_2638_ = lean_unbox_usize(v_i_2635_);
lean_dec(v_i_2635_);
v_res_2639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_boxed_2637_, v_i_boxed_2638_, v_bs_2636_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(size_t v_sz_2640_, size_t v_i_2641_, lean_object* v_bs_2642_){
_start:
{
uint8_t v___x_2643_; 
v___x_2643_ = lean_usize_dec_lt(v_i_2641_, v_sz_2640_);
if (v___x_2643_ == 0)
{
return v_bs_2642_;
}
else
{
lean_object* v_v_2644_; lean_object* v_fst_2645_; lean_object* v_snd_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2675_; 
v_v_2644_ = lean_array_uget(v_bs_2642_, v_i_2641_);
v_fst_2645_ = lean_ctor_get(v_v_2644_, 0);
v_snd_2646_ = lean_ctor_get(v_v_2644_, 1);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_v_2644_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2648_ = v_v_2644_;
v_isShared_2649_ = v_isSharedCheck_2675_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_snd_2646_);
lean_inc(v_fst_2645_);
lean_dec(v_v_2644_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2675_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; lean_object* v_bs_x27_2651_; lean_object* v___y_2653_; lean_object* v___x_2658_; 
v___x_2650_ = lean_unsigned_to_nat(0u);
v_bs_x27_2651_ = lean_array_uset(v_bs_2642_, v_i_2641_, v___x_2650_);
v___x_2658_ = l_Std_Http_URI_EncodedQueryParam_encode(v_fst_2645_);
lean_dec(v_fst_2645_);
if (lean_obj_tag(v_snd_2646_) == 0)
{
lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2659_ = lean_box(0);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 1, v___x_2659_);
lean_ctor_set(v___x_2648_, 0, v___x_2658_);
v___x_2661_ = v___x_2648_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
v___y_2653_ = v___x_2661_;
goto v___jp_2652_;
}
}
else
{
lean_object* v_val_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2674_; 
v_val_2663_ = lean_ctor_get(v_snd_2646_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_snd_2646_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2665_ = v_snd_2646_;
v_isShared_2666_ = v_isSharedCheck_2674_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_val_2663_);
lean_dec(v_snd_2646_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2674_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2667_ = l_Std_Http_URI_EncodedQueryParam_encode(v_val_2663_);
lean_dec(v_val_2663_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2667_);
v___x_2669_ = v___x_2665_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2671_; 
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 1, v___x_2669_);
lean_ctor_set(v___x_2648_, 0, v___x_2658_);
v___x_2671_ = v___x_2648_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
v___y_2653_ = v___x_2671_;
goto v___jp_2652_;
}
}
}
}
v___jp_2652_:
{
size_t v___x_2654_; size_t v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = ((size_t)1ULL);
v___x_2655_ = lean_usize_add(v_i_2641_, v___x_2654_);
v___x_2656_ = lean_array_uset(v_bs_x27_2651_, v_i_2641_, v___y_2653_);
v_i_2641_ = v___x_2655_;
v_bs_2642_ = v___x_2656_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1___boxed(lean_object* v_sz_2676_, lean_object* v_i_2677_, lean_object* v_bs_2678_){
_start:
{
size_t v_sz_boxed_2679_; size_t v_i_boxed_2680_; lean_object* v_res_2681_; 
v_sz_boxed_2679_ = lean_unbox_usize(v_sz_2676_);
lean_dec(v_sz_2676_);
v_i_boxed_2680_ = lean_unbox_usize(v_i_2677_);
lean_dec(v_i_2677_);
v_res_2681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_boxed_2679_, v_i_boxed_2680_, v_bs_2678_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_build(lean_object* v_b_2682_){
_start:
{
lean_object* v___y_2684_; lean_object* v___y_2685_; uint8_t v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v_scheme_2699_; lean_object* v_userInfo_2700_; lean_object* v_host_2701_; lean_object* v_port_2702_; lean_object* v_pathSegments_2703_; lean_object* v_query_2704_; lean_object* v_fragment_2705_; lean_object* v___y_2707_; 
v_scheme_2699_ = lean_ctor_get(v_b_2682_, 0);
lean_inc(v_scheme_2699_);
v_userInfo_2700_ = lean_ctor_get(v_b_2682_, 1);
lean_inc(v_userInfo_2700_);
v_host_2701_ = lean_ctor_get(v_b_2682_, 2);
lean_inc(v_host_2701_);
v_port_2702_ = lean_ctor_get(v_b_2682_, 3);
lean_inc(v_port_2702_);
v_pathSegments_2703_ = lean_ctor_get(v_b_2682_, 4);
lean_inc_ref(v_pathSegments_2703_);
v_query_2704_ = lean_ctor_get(v_b_2682_, 5);
lean_inc_ref(v_query_2704_);
v_fragment_2705_ = lean_ctor_get(v_b_2682_, 6);
lean_inc(v_fragment_2705_);
lean_dec_ref(v_b_2682_);
if (lean_obj_tag(v_scheme_2699_) == 0)
{
lean_object* v___x_2720_; 
v___x_2720_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___y_2707_ = v___x_2720_;
goto v___jp_2706_;
}
else
{
lean_object* v_val_2721_; 
v_val_2721_ = lean_ctor_get(v_scheme_2699_, 0);
lean_inc(v_val_2721_);
lean_dec_ref(v_scheme_2699_);
v___y_2707_ = v_val_2721_;
goto v___jp_2706_;
}
v___jp_2683_:
{
size_t v_sz_2690_; size_t v___x_2691_; lean_object* v___x_2692_; lean_object* v_path_2693_; size_t v_sz_2694_; lean_object* v_query_2695_; lean_object* v___x_2696_; lean_object* v_query_2697_; lean_object* v___x_2698_; 
v_sz_2690_ = lean_array_size(v___y_2684_);
v___x_2691_ = ((size_t)0ULL);
v___x_2692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_2690_, v___x_2691_, v___y_2684_);
v_path_2693_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_path_2693_, 0, v___x_2692_);
lean_ctor_set_uint8(v_path_2693_, sizeof(void*)*1, v___y_2686_);
v_sz_2694_ = lean_array_size(v___y_2688_);
v_query_2695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_2694_, v___x_2691_, v___y_2688_);
v___x_2696_ = lean_array_to_list(v_query_2695_);
v_query_2697_ = lean_array_mk(v___x_2696_);
v___x_2698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2698_, 0, v___y_2687_);
lean_ctor_set(v___x_2698_, 1, v___y_2689_);
lean_ctor_set(v___x_2698_, 2, v_path_2693_);
lean_ctor_set(v___x_2698_, 3, v_query_2697_);
lean_ctor_set(v___x_2698_, 4, v___y_2685_);
return v___x_2698_;
}
v___jp_2706_:
{
if (lean_obj_tag(v_host_2701_) == 0)
{
uint8_t v___x_2708_; lean_object* v___x_2709_; 
lean_dec(v_port_2702_);
lean_dec(v_userInfo_2700_);
v___x_2708_ = 1;
v___x_2709_ = lean_box(0);
v___y_2684_ = v_pathSegments_2703_;
v___y_2685_ = v_fragment_2705_;
v___y_2686_ = v___x_2708_;
v___y_2687_ = v___y_2707_;
v___y_2688_ = v_query_2704_;
v___y_2689_ = v___x_2709_;
goto v___jp_2683_;
}
else
{
lean_object* v_val_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2719_; 
v_val_2710_ = lean_ctor_get(v_host_2701_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v_host_2701_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2712_ = v_host_2701_;
v_isShared_2713_ = v_isSharedCheck_2719_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_val_2710_);
lean_dec(v_host_2701_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2719_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
uint8_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2714_ = 1;
v___x_2715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2715_, 0, v_userInfo_2700_);
lean_ctor_set(v___x_2715_, 1, v_val_2710_);
lean_ctor_set(v___x_2715_, 2, v_port_2702_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v___x_2715_);
v___x_2717_ = v___x_2712_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
v___y_2684_ = v_pathSegments_2703_;
v___y_2685_ = v_fragment_2705_;
v___y_2686_ = v___x_2714_;
v___y_2687_ = v___y_2707_;
v___y_2688_ = v_query_2704_;
v___y_2689_ = v___x_2717_;
goto v___jp_2683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withScheme_x21(lean_object* v_uri_2722_, lean_object* v_scheme_2723_){
_start:
{
lean_object* v_authority_2724_; lean_object* v_path_2725_; lean_object* v_query_2726_; lean_object* v_fragment_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2735_; 
v_authority_2724_ = lean_ctor_get(v_uri_2722_, 1);
v_path_2725_ = lean_ctor_get(v_uri_2722_, 2);
v_query_2726_ = lean_ctor_get(v_uri_2722_, 3);
v_fragment_2727_ = lean_ctor_get(v_uri_2722_, 4);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_uri_2722_);
if (v_isSharedCheck_2735_ == 0)
{
lean_object* v_unused_2736_; 
v_unused_2736_ = lean_ctor_get(v_uri_2722_, 0);
lean_dec(v_unused_2736_);
v___x_2729_ = v_uri_2722_;
v_isShared_2730_ = v_isSharedCheck_2735_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_fragment_2727_);
lean_inc(v_query_2726_);
lean_inc(v_path_2725_);
lean_inc(v_authority_2724_);
lean_dec(v_uri_2722_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2735_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2731_ = l_Std_Http_URI_Scheme_ofString_x21(v_scheme_2723_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v___x_2731_);
v___x_2733_ = v___x_2729_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_authority_2724_);
lean_ctor_set(v_reuseFailAlloc_2734_, 2, v_path_2725_);
lean_ctor_set(v_reuseFailAlloc_2734_, 3, v_query_2726_);
lean_ctor_set(v_reuseFailAlloc_2734_, 4, v_fragment_2727_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withAuthority(lean_object* v_uri_2737_, lean_object* v_authority_2738_){
_start:
{
lean_object* v_scheme_2739_; lean_object* v_path_2740_; lean_object* v_query_2741_; lean_object* v_fragment_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
v_scheme_2739_ = lean_ctor_get(v_uri_2737_, 0);
v_path_2740_ = lean_ctor_get(v_uri_2737_, 2);
v_query_2741_ = lean_ctor_get(v_uri_2737_, 3);
v_fragment_2742_ = lean_ctor_get(v_uri_2737_, 4);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_uri_2737_);
if (v_isSharedCheck_2749_ == 0)
{
lean_object* v_unused_2750_; 
v_unused_2750_ = lean_ctor_get(v_uri_2737_, 1);
lean_dec(v_unused_2750_);
v___x_2744_ = v_uri_2737_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_fragment_2742_);
lean_inc(v_query_2741_);
lean_inc(v_path_2740_);
lean_inc(v_scheme_2739_);
lean_dec(v_uri_2737_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 1, v_authority_2738_);
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_scheme_2739_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_authority_2738_);
lean_ctor_set(v_reuseFailAlloc_2748_, 2, v_path_2740_);
lean_ctor_set(v_reuseFailAlloc_2748_, 3, v_query_2741_);
lean_ctor_set(v_reuseFailAlloc_2748_, 4, v_fragment_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withPath(lean_object* v_uri_2751_, lean_object* v_path_2752_){
_start:
{
lean_object* v_scheme_2753_; lean_object* v_authority_2754_; lean_object* v_query_2755_; lean_object* v_fragment_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
v_scheme_2753_ = lean_ctor_get(v_uri_2751_, 0);
v_authority_2754_ = lean_ctor_get(v_uri_2751_, 1);
v_query_2755_ = lean_ctor_get(v_uri_2751_, 3);
v_fragment_2756_ = lean_ctor_get(v_uri_2751_, 4);
v_isSharedCheck_2763_ = !lean_is_exclusive(v_uri_2751_);
if (v_isSharedCheck_2763_ == 0)
{
lean_object* v_unused_2764_; 
v_unused_2764_ = lean_ctor_get(v_uri_2751_, 2);
lean_dec(v_unused_2764_);
v___x_2758_ = v_uri_2751_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_fragment_2756_);
lean_inc(v_query_2755_);
lean_inc(v_authority_2754_);
lean_inc(v_scheme_2753_);
lean_dec(v_uri_2751_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 2, v_path_2752_);
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_scheme_2753_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v_authority_2754_);
lean_ctor_set(v_reuseFailAlloc_2762_, 2, v_path_2752_);
lean_ctor_set(v_reuseFailAlloc_2762_, 3, v_query_2755_);
lean_ctor_set(v_reuseFailAlloc_2762_, 4, v_fragment_2756_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_withQuery(lean_object* v_uri_2765_, lean_object* v_query_2766_){
_start:
{
lean_object* v_scheme_2767_; lean_object* v_authority_2768_; lean_object* v_path_2769_; lean_object* v_fragment_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
v_scheme_2767_ = lean_ctor_get(v_uri_2765_, 0);
v_authority_2768_ = lean_ctor_get(v_uri_2765_, 1);
v_path_2769_ = lean_ctor_get(v_uri_2765_, 2);
v_fragment_2770_ = lean_ctor_get(v_uri_2765_, 4);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_uri_2765_);
if (v_isSharedCheck_2777_ == 0)
{
lean_object* v_unused_2778_; 
v_unused_2778_ = lean_ctor_get(v_uri_2765_, 3);
lean_dec(v_unused_2778_);
v___x_2772_ = v_uri_2765_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_fragment_2770_);
lean_inc(v_path_2769_);
lean_inc(v_authority_2768_);
lean_inc(v_scheme_2767_);
lean_dec(v_uri_2765_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 3, v_query_2766_);
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_scheme_2767_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_authority_2768_);
lean_ctor_set(v_reuseFailAlloc_2776_, 2, v_path_2769_);
lean_ctor_set(v_reuseFailAlloc_2776_, 3, v_query_2766_);
lean_ctor_set(v_reuseFailAlloc_2776_, 4, v_fragment_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withFragment(lean_object* v_uri_2779_, lean_object* v_fragment_2780_){
_start:
{
lean_object* v_scheme_2781_; lean_object* v_authority_2782_; lean_object* v_path_2783_; lean_object* v_query_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
v_scheme_2781_ = lean_ctor_get(v_uri_2779_, 0);
v_authority_2782_ = lean_ctor_get(v_uri_2779_, 1);
v_path_2783_ = lean_ctor_get(v_uri_2779_, 2);
v_query_2784_ = lean_ctor_get(v_uri_2779_, 3);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_uri_2779_);
if (v_isSharedCheck_2791_ == 0)
{
lean_object* v_unused_2792_; 
v_unused_2792_ = lean_ctor_get(v_uri_2779_, 4);
lean_dec(v_unused_2792_);
v___x_2786_ = v_uri_2779_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_query_2784_);
lean_inc(v_path_2783_);
lean_inc(v_authority_2782_);
lean_inc(v_scheme_2781_);
lean_dec(v_uri_2779_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 4, v_fragment_2780_);
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_scheme_2781_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_authority_2782_);
lean_ctor_set(v_reuseFailAlloc_2790_, 2, v_path_2783_);
lean_ctor_set(v_reuseFailAlloc_2790_, 3, v_query_2784_);
lean_ctor_set(v_reuseFailAlloc_2790_, 4, v_fragment_2780_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_normalize(lean_object* v_uri_2793_){
_start:
{
lean_object* v_scheme_2794_; lean_object* v_authority_2795_; lean_object* v_path_2796_; lean_object* v_query_2797_; lean_object* v_fragment_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2806_; 
v_scheme_2794_ = lean_ctor_get(v_uri_2793_, 0);
v_authority_2795_ = lean_ctor_get(v_uri_2793_, 1);
v_path_2796_ = lean_ctor_get(v_uri_2793_, 2);
v_query_2797_ = lean_ctor_get(v_uri_2793_, 3);
v_fragment_2798_ = lean_ctor_get(v_uri_2793_, 4);
v_isSharedCheck_2806_ = !lean_is_exclusive(v_uri_2793_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2800_ = v_uri_2793_;
v_isShared_2801_ = v_isSharedCheck_2806_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_fragment_2798_);
lean_inc(v_query_2797_);
lean_inc(v_path_2796_);
lean_inc(v_authority_2795_);
lean_inc(v_scheme_2794_);
lean_dec(v_uri_2793_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2806_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2802_ = l_Std_Http_URI_Path_normalize(v_path_2796_);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 2, v___x_2802_);
v___x_2804_ = v___x_2800_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_scheme_2794_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_authority_2795_);
lean_ctor_set(v_reuseFailAlloc_2805_, 2, v___x_2802_);
lean_ctor_set(v_reuseFailAlloc_2805_, 3, v_query_2797_);
lean_ctor_set(v_reuseFailAlloc_2805_, 4, v_fragment_2798_);
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
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx(lean_object* v_x_2807_){
_start:
{
switch(lean_obj_tag(v_x_2807_))
{
case 0:
{
lean_object* v___x_2808_; 
v___x_2808_ = lean_unsigned_to_nat(0u);
return v___x_2808_;
}
case 1:
{
lean_object* v___x_2809_; 
v___x_2809_ = lean_unsigned_to_nat(1u);
return v___x_2809_;
}
case 2:
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_unsigned_to_nat(2u);
return v___x_2810_;
}
default: 
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_unsigned_to_nat(3u);
return v___x_2811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___boxed(lean_object* v_x_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Std_Http_RequestTarget_ctorIdx(v_x_2812_);
lean_dec(v_x_2812_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___redArg(lean_object* v_t_2814_, lean_object* v_k_2815_){
_start:
{
switch(lean_obj_tag(v_t_2814_))
{
case 0:
{
lean_object* v_path_2816_; lean_object* v_query_2817_; lean_object* v___x_2818_; 
v_path_2816_ = lean_ctor_get(v_t_2814_, 0);
lean_inc_ref(v_path_2816_);
v_query_2817_ = lean_ctor_get(v_t_2814_, 1);
lean_inc(v_query_2817_);
lean_dec_ref(v_t_2814_);
v___x_2818_ = lean_apply_2(v_k_2815_, v_path_2816_, v_query_2817_);
return v___x_2818_;
}
case 3:
{
return v_k_2815_;
}
default: 
{
lean_object* v_uri_2819_; lean_object* v___x_2820_; 
v_uri_2819_ = lean_ctor_get(v_t_2814_, 0);
lean_inc_ref(v_uri_2819_);
lean_dec(v_t_2814_);
v___x_2820_ = lean_apply_1(v_k_2815_, v_uri_2819_);
return v___x_2820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim(lean_object* v_motive_2821_, lean_object* v_ctorIdx_2822_, lean_object* v_t_2823_, lean_object* v_h_2824_, lean_object* v_k_2825_){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2823_, v_k_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___boxed(lean_object* v_motive_2827_, lean_object* v_ctorIdx_2828_, lean_object* v_t_2829_, lean_object* v_h_2830_, lean_object* v_k_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Std_Http_RequestTarget_ctorElim(v_motive_2827_, v_ctorIdx_2828_, v_t_2829_, v_h_2830_, v_k_2831_);
lean_dec(v_ctorIdx_2828_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim___redArg(lean_object* v_t_2833_, lean_object* v_originForm_2834_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2833_, v_originForm_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim(lean_object* v_motive_2836_, lean_object* v_t_2837_, lean_object* v_h_2838_, lean_object* v_originForm_2839_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2837_, v_originForm_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim___redArg(lean_object* v_t_2841_, lean_object* v_absoluteForm_2842_){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2841_, v_absoluteForm_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim(lean_object* v_motive_2844_, lean_object* v_t_2845_, lean_object* v_h_2846_, lean_object* v_absoluteForm_2847_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2845_, v_absoluteForm_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim___redArg(lean_object* v_t_2849_, lean_object* v_authorityForm_2850_){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2849_, v_authorityForm_2850_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim(lean_object* v_motive_2852_, lean_object* v_t_2853_, lean_object* v_h_2854_, lean_object* v_authorityForm_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2853_, v_authorityForm_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim___redArg(lean_object* v_t_2857_, lean_object* v_asteriskForm_2858_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2857_, v_asteriskForm_2858_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim(lean_object* v_motive_2860_, lean_object* v_t_2861_, lean_object* v_h_2862_, lean_object* v_asteriskForm_2863_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2861_, v_asteriskForm_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0(lean_object* v_x_2870_, lean_object* v_x_2871_){
_start:
{
if (lean_obj_tag(v_x_2870_) == 0)
{
lean_object* v___x_2872_; 
v___x_2872_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2872_;
}
else
{
lean_object* v_val_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v_val_2873_ = lean_ctor_get(v_x_2870_, 0);
lean_inc(v_val_2873_);
lean_dec_ref(v_x_2870_);
v___x_2874_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2875_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_val_2873_);
v___x_2876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2874_);
lean_ctor_set(v___x_2876_, 1, v___x_2875_);
v___x_2877_ = l_Repr_addAppParen(v___x_2876_, v_x_2871_);
return v___x_2877_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0___boxed(lean_object* v_x_2878_, lean_object* v_x_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0(v_x_2878_, v_x_2879_);
lean_dec(v_x_2879_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object* v_x_2902_, lean_object* v_prec_2903_){
_start:
{
lean_object* v___y_2905_; 
switch(lean_obj_tag(v_x_2902_))
{
case 0:
{
lean_object* v_path_2911_; lean_object* v_query_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2936_; 
v_path_2911_ = lean_ctor_get(v_x_2902_, 0);
v_query_2912_ = lean_ctor_get(v_x_2902_, 1);
v_isSharedCheck_2936_ = !lean_is_exclusive(v_x_2902_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2914_ = v_x_2902_;
v_isShared_2915_ = v_isSharedCheck_2936_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_query_2912_);
lean_inc(v_path_2911_);
lean_dec(v_x_2902_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2936_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___y_2917_; lean_object* v___x_2932_; uint8_t v___x_2933_; 
v___x_2932_ = lean_unsigned_to_nat(1024u);
v___x_2933_ = lean_nat_dec_le(v___x_2932_, v_prec_2903_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; 
v___x_2934_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_2917_ = v___x_2934_;
goto v___jp_2916_;
}
else
{
lean_object* v___x_2935_; 
v___x_2935_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_2917_ = v___x_2935_;
goto v___jp_2916_;
}
v___jp_2916_:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2923_; 
v___x_2918_ = lean_box(1);
v___x_2919_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__4));
v___x_2920_ = lean_unsigned_to_nat(1024u);
v___x_2921_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_2911_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set_tag(v___x_2914_, 5);
lean_ctor_set(v___x_2914_, 1, v___x_2921_);
lean_ctor_set(v___x_2914_, 0, v___x_2919_);
v___x_2923_ = v___x_2914_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2919_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v___x_2921_);
v___x_2923_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
lean_ctor_set(v___x_2924_, 1, v___x_2918_);
v___x_2925_ = l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0(v_query_2912_, v___x_2920_);
v___x_2926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2924_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
lean_inc(v___y_2917_);
v___x_2927_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___y_2917_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
v___x_2928_ = 0;
v___x_2929_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2929_, 0, v___x_2927_);
lean_ctor_set_uint8(v___x_2929_, sizeof(void*)*1, v___x_2928_);
v___x_2930_ = l_Repr_addAppParen(v___x_2929_, v_prec_2903_);
return v___x_2930_;
}
}
}
}
case 1:
{
lean_object* v_uri_2937_; lean_object* v___y_2939_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v_uri_2937_ = lean_ctor_get(v_x_2902_, 0);
lean_inc_ref(v_uri_2937_);
lean_dec_ref(v_x_2902_);
v___x_2947_ = lean_unsigned_to_nat(1024u);
v___x_2948_ = lean_nat_dec_le(v___x_2947_, v_prec_2903_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_2939_ = v___x_2949_;
goto v___jp_2938_;
}
else
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_2939_ = v___x_2950_;
goto v___jp_2938_;
}
v___jp_2938_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2940_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__7));
v___x_2941_ = l_Std_Http_instReprURI_repr___redArg(v_uri_2937_);
v___x_2942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2940_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
lean_inc(v___y_2939_);
v___x_2943_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___y_2939_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
v___x_2944_ = 0;
v___x_2945_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2945_, 0, v___x_2943_);
lean_ctor_set_uint8(v___x_2945_, sizeof(void*)*1, v___x_2944_);
v___x_2946_ = l_Repr_addAppParen(v___x_2945_, v_prec_2903_);
return v___x_2946_;
}
}
case 2:
{
lean_object* v_authority_2951_; lean_object* v___y_2953_; lean_object* v___x_2961_; uint8_t v___x_2962_; 
v_authority_2951_ = lean_ctor_get(v_x_2902_, 0);
lean_inc_ref(v_authority_2951_);
lean_dec_ref(v_x_2902_);
v___x_2961_ = lean_unsigned_to_nat(1024u);
v___x_2962_ = lean_nat_dec_le(v___x_2961_, v_prec_2903_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_2953_ = v___x_2963_;
goto v___jp_2952_;
}
else
{
lean_object* v___x_2964_; 
v___x_2964_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_2953_ = v___x_2964_;
goto v___jp_2952_;
}
v___jp_2952_:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2954_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__10));
v___x_2955_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_authority_2951_);
v___x_2956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2954_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
lean_inc(v___y_2953_);
v___x_2957_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___y_2953_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v___x_2958_ = 0;
v___x_2959_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set_uint8(v___x_2959_, sizeof(void*)*1, v___x_2958_);
v___x_2960_ = l_Repr_addAppParen(v___x_2959_, v_prec_2903_);
return v___x_2960_;
}
}
default: 
{
lean_object* v___x_2965_; uint8_t v___x_2966_; 
v___x_2965_ = lean_unsigned_to_nat(1024u);
v___x_2966_ = lean_nat_dec_le(v___x_2965_, v_prec_2903_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_2905_ = v___x_2967_;
goto v___jp_2904_;
}
else
{
lean_object* v___x_2968_; 
v___x_2968_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_2905_ = v___x_2968_;
goto v___jp_2904_;
}
}
}
v___jp_2904_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2906_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__1));
lean_inc(v___y_2905_);
v___x_2907_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___y_2905_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = 0;
v___x_2909_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2909_, 0, v___x_2907_);
lean_ctor_set_uint8(v___x_2909_, sizeof(void*)*1, v___x_2908_);
v___x_2910_ = l_Repr_addAppParen(v___x_2909_, v_prec_2903_);
return v___x_2910_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr___boxed(lean_object* v_x_2969_, lean_object* v_prec_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Std_Http_instReprRequestTarget_repr(v_x_2969_, v_prec_2970_);
lean_dec(v_prec_2970_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path(lean_object* v_x_2979_){
_start:
{
switch(lean_obj_tag(v_x_2979_))
{
case 0:
{
lean_object* v_path_2980_; 
v_path_2980_ = lean_ctor_get(v_x_2979_, 0);
lean_inc_ref(v_path_2980_);
return v_path_2980_;
}
case 1:
{
lean_object* v_uri_2981_; lean_object* v_path_2982_; 
v_uri_2981_ = lean_ctor_get(v_x_2979_, 0);
v_path_2982_ = lean_ctor_get(v_uri_2981_, 2);
lean_inc_ref(v_path_2982_);
return v_path_2982_;
}
default: 
{
lean_object* v___x_2983_; 
v___x_2983_ = ((lean_object*)(l_Std_Http_RequestTarget_path___closed__1));
return v___x_2983_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path___boxed(lean_object* v_x_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l_Std_Http_RequestTarget_path(v_x_2984_);
lean_dec(v_x_2984_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query(lean_object* v_x_2986_){
_start:
{
switch(lean_obj_tag(v_x_2986_))
{
case 0:
{
lean_object* v_query_2987_; 
v_query_2987_ = lean_ctor_get(v_x_2986_, 1);
if (lean_obj_tag(v_query_2987_) == 0)
{
lean_object* v___x_2988_; 
v___x_2988_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_2988_;
}
else
{
lean_object* v_val_2989_; 
v_val_2989_ = lean_ctor_get(v_query_2987_, 0);
lean_inc(v_val_2989_);
return v_val_2989_;
}
}
case 1:
{
lean_object* v_uri_2990_; lean_object* v_query_2991_; 
v_uri_2990_ = lean_ctor_get(v_x_2986_, 0);
v_query_2991_ = lean_ctor_get(v_uri_2990_, 3);
lean_inc_ref(v_query_2991_);
return v_query_2991_;
}
default: 
{
lean_object* v___x_2992_; 
v___x_2992_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_2992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query___boxed(lean_object* v_x_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Std_Http_RequestTarget_query(v_x_2993_);
lean_dec(v_x_2993_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authority_x3f(lean_object* v_x_2995_){
_start:
{
switch(lean_obj_tag(v_x_2995_))
{
case 2:
{
lean_object* v_authority_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
v_authority_2996_ = lean_ctor_get(v_x_2995_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v_x_2995_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v_x_2995_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_authority_2996_);
lean_dec(v_x_2995_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
lean_ctor_set_tag(v___x_2998_, 1);
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_authority_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
case 1:
{
lean_object* v_uri_3004_; lean_object* v_authority_3005_; 
v_uri_3004_ = lean_ctor_get(v_x_2995_, 0);
lean_inc_ref(v_uri_3004_);
lean_dec_ref(v_x_2995_);
v_authority_3005_ = lean_ctor_get(v_uri_3004_, 1);
lean_inc(v_authority_3005_);
lean_dec_ref(v_uri_3004_);
return v_authority_3005_;
}
default: 
{
lean_object* v___x_3006_; 
lean_dec(v_x_2995_);
v___x_3006_ = lean_box(0);
return v___x_3006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__4(lean_object* v___f_3008_, lean_object* v___f_3009_, lean_object* v___f_3010_, lean_object* v___f_3011_, lean_object* v_x_3012_){
_start:
{
lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; 
switch(lean_obj_tag(v_x_3012_))
{
case 0:
{
lean_object* v_path_3019_; lean_object* v_query_3020_; lean_object* v___y_3022_; lean_object* v_segments_3035_; uint8_t v_absolute_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; size_t v_sz_3039_; size_t v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v_result_3043_; 
lean_dec_ref(v___f_3011_);
lean_dec_ref(v___f_3010_);
v_path_3019_ = lean_ctor_get(v_x_3012_, 0);
lean_inc_ref(v_path_3019_);
v_query_3020_ = lean_ctor_get(v_x_3012_, 1);
lean_inc(v_query_3020_);
lean_dec_ref(v_x_3012_);
v_segments_3035_ = lean_ctor_get(v_path_3019_, 0);
lean_inc_ref(v_segments_3035_);
v_absolute_3036_ = lean_ctor_get_uint8(v_path_3019_, sizeof(void*)*1);
lean_dec_ref(v_path_3019_);
v___x_3037_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3038_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3039_ = lean_array_size(v_segments_3035_);
v___x_3040_ = ((size_t)0ULL);
v___x_3041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3038_, v___f_3009_, v_sz_3039_, v___x_3040_, v_segments_3035_);
v___x_3042_ = lean_array_to_list(v___x_3041_);
v_result_3043_ = l_String_intercalate(v___x_3037_, v___x_3042_);
if (v_absolute_3036_ == 0)
{
v___y_3022_ = v_result_3043_;
goto v___jp_3021_;
}
else
{
lean_object* v___x_3044_; 
v___x_3044_ = lean_string_append(v___x_3037_, v_result_3043_);
lean_dec_ref(v_result_3043_);
v___y_3022_ = v___x_3044_;
goto v___jp_3021_;
}
v___jp_3021_:
{
if (lean_obj_tag(v_query_3020_) == 0)
{
lean_dec_ref(v___f_3008_);
return v___y_3022_;
}
else
{
lean_object* v_val_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; uint8_t v___x_3026_; 
v_val_3023_ = lean_ctor_get(v_query_3020_, 0);
lean_inc(v_val_3023_);
lean_dec_ref(v_query_3020_);
v___x_3024_ = lean_array_get_size(v_val_3023_);
v___x_3025_ = lean_unsigned_to_nat(0u);
v___x_3026_ = lean_nat_dec_eq(v___x_3024_, v___x_3025_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v_encodedParams_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3027_ = lean_array_to_list(v_val_3023_);
v___x_3028_ = lean_box(0);
v_encodedParams_3029_ = l_List_mapTR_loop___redArg(v___f_3008_, v___x_3027_, v___x_3028_);
v___x_3030_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_3031_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_3032_ = l_String_intercalate(v___x_3031_, v_encodedParams_3029_);
v___x_3033_ = lean_string_append(v___x_3030_, v___x_3032_);
lean_dec_ref(v___x_3032_);
v___x_3034_ = lean_string_append(v___y_3022_, v___x_3033_);
lean_dec_ref(v___x_3033_);
return v___x_3034_;
}
else
{
lean_dec(v_val_3023_);
lean_dec_ref(v___f_3008_);
return v___y_3022_;
}
}
}
}
case 1:
{
lean_object* v_uri_3045_; lean_object* v_scheme_3046_; lean_object* v_authority_3047_; lean_object* v_path_3048_; lean_object* v_query_3049_; lean_object* v_fragment_3050_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3087_; 
lean_dec_ref(v___f_3009_);
lean_dec_ref(v___f_3008_);
v_uri_3045_ = lean_ctor_get(v_x_3012_, 0);
lean_inc_ref(v_uri_3045_);
lean_dec_ref(v_x_3012_);
v_scheme_3046_ = lean_ctor_get(v_uri_3045_, 0);
lean_inc_ref(v_scheme_3046_);
v_authority_3047_ = lean_ctor_get(v_uri_3045_, 1);
lean_inc(v_authority_3047_);
v_path_3048_ = lean_ctor_get(v_uri_3045_, 2);
lean_inc_ref(v_path_3048_);
v_query_3049_ = lean_ctor_get(v_uri_3045_, 3);
lean_inc_ref(v_query_3049_);
v_fragment_3050_ = lean_ctor_get(v_uri_3045_, 4);
lean_inc(v_fragment_3050_);
lean_dec_ref(v_uri_3045_);
if (lean_obj_tag(v_authority_3047_) == 0)
{
lean_object* v___x_3098_; 
v___x_3098_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3087_ = v___x_3098_;
goto v___jp_3086_;
}
else
{
lean_object* v_val_3099_; lean_object* v_userInfo_3100_; lean_object* v_host_3101_; lean_object* v_port_3102_; lean_object* v___x_3103_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3122_; 
v_val_3099_ = lean_ctor_get(v_authority_3047_, 0);
lean_inc(v_val_3099_);
lean_dec_ref(v_authority_3047_);
v_userInfo_3100_ = lean_ctor_get(v_val_3099_, 0);
lean_inc(v_userInfo_3100_);
v_host_3101_ = lean_ctor_get(v_val_3099_, 1);
lean_inc_ref(v_host_3101_);
v_port_3102_ = lean_ctor_get(v_val_3099_, 2);
lean_inc(v_port_3102_);
lean_dec(v_val_3099_);
v___x_3103_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__1));
if (lean_obj_tag(v_userInfo_3100_) == 0)
{
lean_object* v___x_3132_; 
v___x_3132_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3122_ = v___x_3132_;
goto v___jp_3121_;
}
else
{
lean_object* v_val_3133_; lean_object* v_password_3134_; 
v_val_3133_ = lean_ctor_get(v_userInfo_3100_, 0);
lean_inc(v_val_3133_);
lean_dec_ref(v_userInfo_3100_);
v_password_3134_ = lean_ctor_get(v_val_3133_, 1);
if (lean_obj_tag(v_password_3134_) == 0)
{
lean_object* v_username_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v_username_3135_ = lean_ctor_get(v_val_3133_, 0);
lean_inc_ref(v_username_3135_);
lean_dec(v_val_3133_);
v___x_3136_ = lean_string_from_utf8_unchecked(v_username_3135_);
v___x_3137_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3138_ = lean_string_append(v___x_3136_, v___x_3137_);
v___y_3122_ = v___x_3138_;
goto v___jp_3121_;
}
else
{
lean_object* v_username_3139_; lean_object* v_val_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
lean_inc_ref(v_password_3134_);
v_username_3139_ = lean_ctor_get(v_val_3133_, 0);
lean_inc_ref(v_username_3139_);
lean_dec(v_val_3133_);
v_val_3140_ = lean_ctor_get(v_password_3134_, 0);
lean_inc(v_val_3140_);
lean_dec_ref(v_password_3134_);
v___x_3141_ = lean_string_from_utf8_unchecked(v_username_3139_);
v___x_3142_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3143_ = lean_string_append(v___x_3141_, v___x_3142_);
v___x_3144_ = lean_string_from_utf8_unchecked(v_val_3140_);
v___x_3145_ = lean_string_append(v___x_3143_, v___x_3144_);
lean_dec_ref(v___x_3144_);
v___x_3146_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3147_ = lean_string_append(v___x_3145_, v___x_3146_);
v___y_3122_ = v___x_3147_;
goto v___jp_3121_;
}
}
v___jp_3104_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3108_ = lean_string_append(v___y_3105_, v___y_3106_);
lean_dec_ref(v___y_3106_);
v___x_3109_ = lean_string_append(v___x_3108_, v___y_3107_);
lean_dec_ref(v___y_3107_);
v___x_3110_ = lean_string_append(v___x_3103_, v___x_3109_);
lean_dec_ref(v___x_3109_);
v___y_3087_ = v___x_3110_;
goto v___jp_3086_;
}
v___jp_3111_:
{
switch(lean_obj_tag(v_port_3102_))
{
case 0:
{
lean_object* v___x_3114_; 
v___x_3114_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3105_ = v___y_3112_;
v___y_3106_ = v___y_3113_;
v___y_3107_ = v___x_3114_;
goto v___jp_3104_;
}
case 1:
{
lean_object* v___x_3115_; 
v___x_3115_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3105_ = v___y_3112_;
v___y_3106_ = v___y_3113_;
v___y_3107_ = v___x_3115_;
goto v___jp_3104_;
}
default: 
{
uint16_t v_port_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v_port_3116_ = lean_ctor_get_uint16(v_port_3102_, 0);
lean_dec_ref(v_port_3102_);
v___x_3117_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3118_ = lean_uint16_to_nat(v_port_3116_);
v___x_3119_ = l_Nat_reprFast(v___x_3118_);
v___x_3120_ = lean_string_append(v___x_3117_, v___x_3119_);
lean_dec_ref(v___x_3119_);
v___y_3105_ = v___y_3112_;
v___y_3106_ = v___y_3113_;
v___y_3107_ = v___x_3120_;
goto v___jp_3104_;
}
}
}
v___jp_3121_:
{
switch(lean_obj_tag(v_host_3101_))
{
case 0:
{
lean_object* v_name_3123_; 
v_name_3123_ = lean_ctor_get(v_host_3101_, 0);
lean_inc_ref(v_name_3123_);
lean_dec_ref(v_host_3101_);
v___y_3112_ = v___y_3122_;
v___y_3113_ = v_name_3123_;
goto v___jp_3111_;
}
case 1:
{
lean_object* v_ipv4_3124_; lean_object* v___x_3125_; 
v_ipv4_3124_ = lean_ctor_get(v_host_3101_, 0);
lean_inc_ref(v_ipv4_3124_);
lean_dec_ref(v_host_3101_);
v___x_3125_ = lean_uv_ntop_v4(v_ipv4_3124_);
lean_dec_ref(v_ipv4_3124_);
v___y_3112_ = v___y_3122_;
v___y_3113_ = v___x_3125_;
goto v___jp_3111_;
}
default: 
{
lean_object* v_ipv6_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v_ipv6_3126_ = lean_ctor_get(v_host_3101_, 0);
lean_inc_ref(v_ipv6_3126_);
lean_dec_ref(v_host_3101_);
v___x_3127_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3128_ = lean_uv_ntop_v6(v_ipv6_3126_);
lean_dec_ref(v_ipv6_3126_);
v___x_3129_ = lean_string_append(v___x_3127_, v___x_3128_);
lean_dec_ref(v___x_3128_);
v___x_3130_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3131_ = lean_string_append(v___x_3129_, v___x_3130_);
v___y_3112_ = v___y_3122_;
v___y_3113_ = v___x_3131_;
goto v___jp_3111_;
}
}
}
}
v___jp_3051_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3056_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3057_ = lean_string_append(v_scheme_3046_, v___x_3056_);
v___x_3058_ = lean_string_append(v___x_3057_, v___y_3052_);
lean_dec_ref(v___y_3052_);
v___x_3059_ = lean_string_append(v___x_3058_, v___y_3053_);
lean_dec_ref(v___y_3053_);
v___x_3060_ = lean_string_append(v___x_3059_, v___y_3054_);
lean_dec_ref(v___y_3054_);
v___x_3061_ = lean_string_append(v___x_3060_, v___y_3055_);
lean_dec_ref(v___y_3055_);
return v___x_3061_;
}
v___jp_3062_:
{
if (lean_obj_tag(v_fragment_3050_) == 0)
{
lean_object* v___x_3066_; 
v___x_3066_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3052_ = v___y_3063_;
v___y_3053_ = v___y_3064_;
v___y_3054_ = v___y_3065_;
v___y_3055_ = v___x_3066_;
goto v___jp_3051_;
}
else
{
lean_object* v_val_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_val_3067_ = lean_ctor_get(v_fragment_3050_, 0);
lean_inc(v_val_3067_);
lean_dec_ref(v_fragment_3050_);
v___x_3068_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__0));
v___x_3069_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3067_);
lean_dec(v_val_3067_);
v___x_3070_ = lean_string_from_utf8_unchecked(v___x_3069_);
v___x_3071_ = lean_string_append(v___x_3068_, v___x_3070_);
lean_dec_ref(v___x_3070_);
v___y_3052_ = v___y_3063_;
v___y_3053_ = v___y_3064_;
v___y_3054_ = v___y_3065_;
v___y_3055_ = v___x_3071_;
goto v___jp_3051_;
}
}
v___jp_3072_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; 
v___x_3075_ = lean_array_get_size(v_query_3049_);
v___x_3076_ = lean_unsigned_to_nat(0u);
v___x_3077_ = lean_nat_dec_eq(v___x_3075_, v___x_3076_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v_encodedParams_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3078_ = lean_array_to_list(v_query_3049_);
v___x_3079_ = lean_box(0);
v_encodedParams_3080_ = l_List_mapTR_loop___redArg(v___f_3010_, v___x_3078_, v___x_3079_);
v___x_3081_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_3082_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_3083_ = l_String_intercalate(v___x_3082_, v_encodedParams_3080_);
v___x_3084_ = lean_string_append(v___x_3081_, v___x_3083_);
lean_dec_ref(v___x_3083_);
v___y_3063_ = v___y_3073_;
v___y_3064_ = v___y_3074_;
v___y_3065_ = v___x_3084_;
goto v___jp_3062_;
}
else
{
lean_object* v___x_3085_; 
lean_dec_ref(v_query_3049_);
lean_dec_ref(v___f_3010_);
v___x_3085_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3063_ = v___y_3073_;
v___y_3064_ = v___y_3074_;
v___y_3065_ = v___x_3085_;
goto v___jp_3062_;
}
}
v___jp_3086_:
{
lean_object* v_segments_3088_; uint8_t v_absolute_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; size_t v_sz_3092_; size_t v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v_result_3096_; 
v_segments_3088_ = lean_ctor_get(v_path_3048_, 0);
lean_inc_ref(v_segments_3088_);
v_absolute_3089_ = lean_ctor_get_uint8(v_path_3048_, sizeof(void*)*1);
lean_dec_ref(v_path_3048_);
v___x_3090_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3091_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3092_ = lean_array_size(v_segments_3088_);
v___x_3093_ = ((size_t)0ULL);
v___x_3094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3091_, v___f_3011_, v_sz_3092_, v___x_3093_, v_segments_3088_);
v___x_3095_ = lean_array_to_list(v___x_3094_);
v_result_3096_ = l_String_intercalate(v___x_3090_, v___x_3095_);
if (v_absolute_3089_ == 0)
{
v___y_3073_ = v___y_3087_;
v___y_3074_ = v_result_3096_;
goto v___jp_3072_;
}
else
{
lean_object* v___x_3097_; 
v___x_3097_ = lean_string_append(v___x_3090_, v_result_3096_);
lean_dec_ref(v_result_3096_);
v___y_3073_ = v___y_3087_;
v___y_3074_ = v___x_3097_;
goto v___jp_3072_;
}
}
}
case 2:
{
lean_object* v_authority_3148_; lean_object* v_userInfo_3149_; lean_object* v_host_3150_; lean_object* v_port_3151_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3163_; 
lean_dec_ref(v___f_3011_);
lean_dec_ref(v___f_3010_);
lean_dec_ref(v___f_3009_);
lean_dec_ref(v___f_3008_);
v_authority_3148_ = lean_ctor_get(v_x_3012_, 0);
lean_inc_ref(v_authority_3148_);
lean_dec_ref(v_x_3012_);
v_userInfo_3149_ = lean_ctor_get(v_authority_3148_, 0);
lean_inc(v_userInfo_3149_);
v_host_3150_ = lean_ctor_get(v_authority_3148_, 1);
lean_inc_ref(v_host_3150_);
v_port_3151_ = lean_ctor_get(v_authority_3148_, 2);
lean_inc(v_port_3151_);
lean_dec_ref(v_authority_3148_);
if (lean_obj_tag(v_userInfo_3149_) == 0)
{
lean_object* v___x_3173_; 
v___x_3173_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3163_ = v___x_3173_;
goto v___jp_3162_;
}
else
{
lean_object* v_val_3174_; lean_object* v_password_3175_; 
v_val_3174_ = lean_ctor_get(v_userInfo_3149_, 0);
lean_inc(v_val_3174_);
lean_dec_ref(v_userInfo_3149_);
v_password_3175_ = lean_ctor_get(v_val_3174_, 1);
if (lean_obj_tag(v_password_3175_) == 0)
{
lean_object* v_username_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v_username_3176_ = lean_ctor_get(v_val_3174_, 0);
lean_inc_ref(v_username_3176_);
lean_dec(v_val_3174_);
v___x_3177_ = lean_string_from_utf8_unchecked(v_username_3176_);
v___x_3178_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3179_ = lean_string_append(v___x_3177_, v___x_3178_);
v___y_3163_ = v___x_3179_;
goto v___jp_3162_;
}
else
{
lean_object* v_username_3180_; lean_object* v_val_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
lean_inc_ref(v_password_3175_);
v_username_3180_ = lean_ctor_get(v_val_3174_, 0);
lean_inc_ref(v_username_3180_);
lean_dec(v_val_3174_);
v_val_3181_ = lean_ctor_get(v_password_3175_, 0);
lean_inc(v_val_3181_);
lean_dec_ref(v_password_3175_);
v___x_3182_ = lean_string_from_utf8_unchecked(v_username_3180_);
v___x_3183_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3184_ = lean_string_append(v___x_3182_, v___x_3183_);
v___x_3185_ = lean_string_from_utf8_unchecked(v_val_3181_);
v___x_3186_ = lean_string_append(v___x_3184_, v___x_3185_);
lean_dec_ref(v___x_3185_);
v___x_3187_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3188_ = lean_string_append(v___x_3186_, v___x_3187_);
v___y_3163_ = v___x_3188_;
goto v___jp_3162_;
}
}
v___jp_3152_:
{
switch(lean_obj_tag(v_port_3151_))
{
case 0:
{
lean_object* v___x_3155_; 
v___x_3155_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3014_ = v___y_3153_;
v___y_3015_ = v___y_3154_;
v___y_3016_ = v___x_3155_;
goto v___jp_3013_;
}
case 1:
{
lean_object* v___x_3156_; 
v___x_3156_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3014_ = v___y_3153_;
v___y_3015_ = v___y_3154_;
v___y_3016_ = v___x_3156_;
goto v___jp_3013_;
}
default: 
{
uint16_t v_port_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v_port_3157_ = lean_ctor_get_uint16(v_port_3151_, 0);
lean_dec_ref(v_port_3151_);
v___x_3158_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3159_ = lean_uint16_to_nat(v_port_3157_);
v___x_3160_ = l_Nat_reprFast(v___x_3159_);
v___x_3161_ = lean_string_append(v___x_3158_, v___x_3160_);
lean_dec_ref(v___x_3160_);
v___y_3014_ = v___y_3153_;
v___y_3015_ = v___y_3154_;
v___y_3016_ = v___x_3161_;
goto v___jp_3013_;
}
}
}
v___jp_3162_:
{
switch(lean_obj_tag(v_host_3150_))
{
case 0:
{
lean_object* v_name_3164_; 
v_name_3164_ = lean_ctor_get(v_host_3150_, 0);
lean_inc_ref(v_name_3164_);
lean_dec_ref(v_host_3150_);
v___y_3153_ = v___y_3163_;
v___y_3154_ = v_name_3164_;
goto v___jp_3152_;
}
case 1:
{
lean_object* v_ipv4_3165_; lean_object* v___x_3166_; 
v_ipv4_3165_ = lean_ctor_get(v_host_3150_, 0);
lean_inc_ref(v_ipv4_3165_);
lean_dec_ref(v_host_3150_);
v___x_3166_ = lean_uv_ntop_v4(v_ipv4_3165_);
lean_dec_ref(v_ipv4_3165_);
v___y_3153_ = v___y_3163_;
v___y_3154_ = v___x_3166_;
goto v___jp_3152_;
}
default: 
{
lean_object* v_ipv6_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v_ipv6_3167_ = lean_ctor_get(v_host_3150_, 0);
lean_inc_ref(v_ipv6_3167_);
lean_dec_ref(v_host_3150_);
v___x_3168_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3169_ = lean_uv_ntop_v6(v_ipv6_3167_);
lean_dec_ref(v_ipv6_3167_);
v___x_3170_ = lean_string_append(v___x_3168_, v___x_3169_);
lean_dec_ref(v___x_3169_);
v___x_3171_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3172_ = lean_string_append(v___x_3170_, v___x_3171_);
v___y_3153_ = v___y_3163_;
v___y_3154_ = v___x_3172_;
goto v___jp_3152_;
}
}
}
}
default: 
{
lean_object* v___x_3189_; 
lean_dec_ref(v___f_3011_);
lean_dec_ref(v___f_3010_);
lean_dec_ref(v___f_3009_);
lean_dec_ref(v___f_3008_);
v___x_3189_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__4___closed__0));
return v___x_3189_;
}
}
v___jp_3013_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = lean_string_append(v___y_3014_, v___y_3015_);
lean_dec_ref(v___y_3015_);
v___x_3018_ = lean_string_append(v___x_3017_, v___y_3016_);
lean_dec_ref(v___y_3016_);
return v___x_3018_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__4(lean_object* v___f_3194_, lean_object* v___f_3195_, lean_object* v___f_3196_, lean_object* v___f_3197_, lean_object* v_buffer_3198_, lean_object* v_target_3199_){
_start:
{
lean_object* v___y_3201_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; 
switch(lean_obj_tag(v_target_3199_))
{
case 0:
{
lean_object* v_path_3221_; lean_object* v_query_3222_; lean_object* v___y_3224_; lean_object* v_segments_3237_; uint8_t v_absolute_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; size_t v_sz_3241_; size_t v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v_result_3245_; 
lean_dec_ref(v___f_3197_);
lean_dec_ref(v___f_3196_);
v_path_3221_ = lean_ctor_get(v_target_3199_, 0);
lean_inc_ref(v_path_3221_);
v_query_3222_ = lean_ctor_get(v_target_3199_, 1);
lean_inc(v_query_3222_);
lean_dec_ref(v_target_3199_);
v_segments_3237_ = lean_ctor_get(v_path_3221_, 0);
lean_inc_ref(v_segments_3237_);
v_absolute_3238_ = lean_ctor_get_uint8(v_path_3221_, sizeof(void*)*1);
lean_dec_ref(v_path_3221_);
v___x_3239_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3240_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3241_ = lean_array_size(v_segments_3237_);
v___x_3242_ = ((size_t)0ULL);
v___x_3243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3240_, v___f_3195_, v_sz_3241_, v___x_3242_, v_segments_3237_);
v___x_3244_ = lean_array_to_list(v___x_3243_);
v_result_3245_ = l_String_intercalate(v___x_3239_, v___x_3244_);
if (v_absolute_3238_ == 0)
{
v___y_3224_ = v_result_3245_;
goto v___jp_3223_;
}
else
{
lean_object* v___x_3246_; 
v___x_3246_ = lean_string_append(v___x_3239_, v_result_3245_);
lean_dec_ref(v_result_3245_);
v___y_3224_ = v___x_3246_;
goto v___jp_3223_;
}
v___jp_3223_:
{
if (lean_obj_tag(v_query_3222_) == 0)
{
lean_dec_ref(v___f_3194_);
v___y_3201_ = v___y_3224_;
goto v___jp_3200_;
}
else
{
lean_object* v_val_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; uint8_t v___x_3228_; 
v_val_3225_ = lean_ctor_get(v_query_3222_, 0);
lean_inc(v_val_3225_);
lean_dec_ref(v_query_3222_);
v___x_3226_ = lean_array_get_size(v_val_3225_);
v___x_3227_ = lean_unsigned_to_nat(0u);
v___x_3228_ = lean_nat_dec_eq(v___x_3226_, v___x_3227_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v_encodedParams_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3229_ = lean_array_to_list(v_val_3225_);
v___x_3230_ = lean_box(0);
v_encodedParams_3231_ = l_List_mapTR_loop___redArg(v___f_3194_, v___x_3229_, v___x_3230_);
v___x_3232_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_3233_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_3234_ = l_String_intercalate(v___x_3233_, v_encodedParams_3231_);
v___x_3235_ = lean_string_append(v___x_3232_, v___x_3234_);
lean_dec_ref(v___x_3234_);
v___x_3236_ = lean_string_append(v___y_3224_, v___x_3235_);
lean_dec_ref(v___x_3235_);
v___y_3201_ = v___x_3236_;
goto v___jp_3200_;
}
else
{
lean_dec(v_val_3225_);
lean_dec_ref(v___f_3194_);
v___y_3201_ = v___y_3224_;
goto v___jp_3200_;
}
}
}
}
case 1:
{
lean_object* v_uri_3247_; lean_object* v_scheme_3248_; lean_object* v_authority_3249_; lean_object* v_path_3250_; lean_object* v_query_3251_; lean_object* v_fragment_3252_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3289_; 
lean_dec_ref(v___f_3195_);
lean_dec_ref(v___f_3194_);
v_uri_3247_ = lean_ctor_get(v_target_3199_, 0);
lean_inc_ref(v_uri_3247_);
lean_dec_ref(v_target_3199_);
v_scheme_3248_ = lean_ctor_get(v_uri_3247_, 0);
lean_inc_ref(v_scheme_3248_);
v_authority_3249_ = lean_ctor_get(v_uri_3247_, 1);
lean_inc(v_authority_3249_);
v_path_3250_ = lean_ctor_get(v_uri_3247_, 2);
lean_inc_ref(v_path_3250_);
v_query_3251_ = lean_ctor_get(v_uri_3247_, 3);
lean_inc_ref(v_query_3251_);
v_fragment_3252_ = lean_ctor_get(v_uri_3247_, 4);
lean_inc(v_fragment_3252_);
lean_dec_ref(v_uri_3247_);
if (lean_obj_tag(v_authority_3249_) == 0)
{
lean_object* v___x_3300_; 
v___x_3300_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3289_ = v___x_3300_;
goto v___jp_3288_;
}
else
{
lean_object* v_val_3301_; lean_object* v_userInfo_3302_; lean_object* v_host_3303_; lean_object* v_port_3304_; lean_object* v___x_3305_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3324_; 
v_val_3301_ = lean_ctor_get(v_authority_3249_, 0);
lean_inc(v_val_3301_);
lean_dec_ref(v_authority_3249_);
v_userInfo_3302_ = lean_ctor_get(v_val_3301_, 0);
lean_inc(v_userInfo_3302_);
v_host_3303_ = lean_ctor_get(v_val_3301_, 1);
lean_inc_ref(v_host_3303_);
v_port_3304_ = lean_ctor_get(v_val_3301_, 2);
lean_inc(v_port_3304_);
lean_dec(v_val_3301_);
v___x_3305_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__1));
if (lean_obj_tag(v_userInfo_3302_) == 0)
{
lean_object* v___x_3334_; 
v___x_3334_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3324_ = v___x_3334_;
goto v___jp_3323_;
}
else
{
lean_object* v_val_3335_; lean_object* v_password_3336_; 
v_val_3335_ = lean_ctor_get(v_userInfo_3302_, 0);
lean_inc(v_val_3335_);
lean_dec_ref(v_userInfo_3302_);
v_password_3336_ = lean_ctor_get(v_val_3335_, 1);
if (lean_obj_tag(v_password_3336_) == 0)
{
lean_object* v_username_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v_username_3337_ = lean_ctor_get(v_val_3335_, 0);
lean_inc_ref(v_username_3337_);
lean_dec(v_val_3335_);
v___x_3338_ = lean_string_from_utf8_unchecked(v_username_3337_);
v___x_3339_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3340_ = lean_string_append(v___x_3338_, v___x_3339_);
v___y_3324_ = v___x_3340_;
goto v___jp_3323_;
}
else
{
lean_object* v_username_3341_; lean_object* v_val_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
lean_inc_ref(v_password_3336_);
v_username_3341_ = lean_ctor_get(v_val_3335_, 0);
lean_inc_ref(v_username_3341_);
lean_dec(v_val_3335_);
v_val_3342_ = lean_ctor_get(v_password_3336_, 0);
lean_inc(v_val_3342_);
lean_dec_ref(v_password_3336_);
v___x_3343_ = lean_string_from_utf8_unchecked(v_username_3341_);
v___x_3344_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3345_ = lean_string_append(v___x_3343_, v___x_3344_);
v___x_3346_ = lean_string_from_utf8_unchecked(v_val_3342_);
v___x_3347_ = lean_string_append(v___x_3345_, v___x_3346_);
lean_dec_ref(v___x_3346_);
v___x_3348_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3349_ = lean_string_append(v___x_3347_, v___x_3348_);
v___y_3324_ = v___x_3349_;
goto v___jp_3323_;
}
}
v___jp_3306_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3310_ = lean_string_append(v___y_3308_, v___y_3307_);
lean_dec_ref(v___y_3307_);
v___x_3311_ = lean_string_append(v___x_3310_, v___y_3309_);
lean_dec_ref(v___y_3309_);
v___x_3312_ = lean_string_append(v___x_3305_, v___x_3311_);
lean_dec_ref(v___x_3311_);
v___y_3289_ = v___x_3312_;
goto v___jp_3288_;
}
v___jp_3313_:
{
switch(lean_obj_tag(v_port_3304_))
{
case 0:
{
lean_object* v___x_3316_; 
v___x_3316_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3307_ = v___y_3315_;
v___y_3308_ = v___y_3314_;
v___y_3309_ = v___x_3316_;
goto v___jp_3306_;
}
case 1:
{
lean_object* v___x_3317_; 
v___x_3317_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3307_ = v___y_3315_;
v___y_3308_ = v___y_3314_;
v___y_3309_ = v___x_3317_;
goto v___jp_3306_;
}
default: 
{
uint16_t v_port_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v_port_3318_ = lean_ctor_get_uint16(v_port_3304_, 0);
lean_dec_ref(v_port_3304_);
v___x_3319_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3320_ = lean_uint16_to_nat(v_port_3318_);
v___x_3321_ = l_Nat_reprFast(v___x_3320_);
v___x_3322_ = lean_string_append(v___x_3319_, v___x_3321_);
lean_dec_ref(v___x_3321_);
v___y_3307_ = v___y_3315_;
v___y_3308_ = v___y_3314_;
v___y_3309_ = v___x_3322_;
goto v___jp_3306_;
}
}
}
v___jp_3323_:
{
switch(lean_obj_tag(v_host_3303_))
{
case 0:
{
lean_object* v_name_3325_; 
v_name_3325_ = lean_ctor_get(v_host_3303_, 0);
lean_inc_ref(v_name_3325_);
lean_dec_ref(v_host_3303_);
v___y_3314_ = v___y_3324_;
v___y_3315_ = v_name_3325_;
goto v___jp_3313_;
}
case 1:
{
lean_object* v_ipv4_3326_; lean_object* v___x_3327_; 
v_ipv4_3326_ = lean_ctor_get(v_host_3303_, 0);
lean_inc_ref(v_ipv4_3326_);
lean_dec_ref(v_host_3303_);
v___x_3327_ = lean_uv_ntop_v4(v_ipv4_3326_);
lean_dec_ref(v_ipv4_3326_);
v___y_3314_ = v___y_3324_;
v___y_3315_ = v___x_3327_;
goto v___jp_3313_;
}
default: 
{
lean_object* v_ipv6_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_ipv6_3328_ = lean_ctor_get(v_host_3303_, 0);
lean_inc_ref(v_ipv6_3328_);
lean_dec_ref(v_host_3303_);
v___x_3329_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3330_ = lean_uv_ntop_v6(v_ipv6_3328_);
lean_dec_ref(v_ipv6_3328_);
v___x_3331_ = lean_string_append(v___x_3329_, v___x_3330_);
lean_dec_ref(v___x_3330_);
v___x_3332_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3333_ = lean_string_append(v___x_3331_, v___x_3332_);
v___y_3314_ = v___y_3324_;
v___y_3315_ = v___x_3333_;
goto v___jp_3313_;
}
}
}
}
v___jp_3253_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3258_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3259_ = lean_string_append(v_scheme_3248_, v___x_3258_);
v___x_3260_ = lean_string_append(v___x_3259_, v___y_3254_);
lean_dec_ref(v___y_3254_);
v___x_3261_ = lean_string_append(v___x_3260_, v___y_3256_);
lean_dec_ref(v___y_3256_);
v___x_3262_ = lean_string_append(v___x_3261_, v___y_3255_);
lean_dec_ref(v___y_3255_);
v___x_3263_ = lean_string_append(v___x_3262_, v___y_3257_);
lean_dec_ref(v___y_3257_);
v___y_3201_ = v___x_3263_;
goto v___jp_3200_;
}
v___jp_3264_:
{
if (lean_obj_tag(v_fragment_3252_) == 0)
{
lean_object* v___x_3268_; 
v___x_3268_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3254_ = v___y_3265_;
v___y_3255_ = v___y_3267_;
v___y_3256_ = v___y_3266_;
v___y_3257_ = v___x_3268_;
goto v___jp_3253_;
}
else
{
lean_object* v_val_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v_val_3269_ = lean_ctor_get(v_fragment_3252_, 0);
lean_inc(v_val_3269_);
lean_dec_ref(v_fragment_3252_);
v___x_3270_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__0));
v___x_3271_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3269_);
lean_dec(v_val_3269_);
v___x_3272_ = lean_string_from_utf8_unchecked(v___x_3271_);
v___x_3273_ = lean_string_append(v___x_3270_, v___x_3272_);
lean_dec_ref(v___x_3272_);
v___y_3254_ = v___y_3265_;
v___y_3255_ = v___y_3267_;
v___y_3256_ = v___y_3266_;
v___y_3257_ = v___x_3273_;
goto v___jp_3253_;
}
}
v___jp_3274_:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; uint8_t v___x_3279_; 
v___x_3277_ = lean_array_get_size(v_query_3251_);
v___x_3278_ = lean_unsigned_to_nat(0u);
v___x_3279_ = lean_nat_dec_eq(v___x_3277_, v___x_3278_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v_encodedParams_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3280_ = lean_array_to_list(v_query_3251_);
v___x_3281_ = lean_box(0);
v_encodedParams_3282_ = l_List_mapTR_loop___redArg(v___f_3196_, v___x_3280_, v___x_3281_);
v___x_3283_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_3284_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_3285_ = l_String_intercalate(v___x_3284_, v_encodedParams_3282_);
v___x_3286_ = lean_string_append(v___x_3283_, v___x_3285_);
lean_dec_ref(v___x_3285_);
v___y_3265_ = v___y_3275_;
v___y_3266_ = v___y_3276_;
v___y_3267_ = v___x_3286_;
goto v___jp_3264_;
}
else
{
lean_object* v___x_3287_; 
lean_dec_ref(v_query_3251_);
lean_dec_ref(v___f_3196_);
v___x_3287_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3265_ = v___y_3275_;
v___y_3266_ = v___y_3276_;
v___y_3267_ = v___x_3287_;
goto v___jp_3264_;
}
}
v___jp_3288_:
{
lean_object* v_segments_3290_; uint8_t v_absolute_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; size_t v_sz_3294_; size_t v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v_result_3298_; 
v_segments_3290_ = lean_ctor_get(v_path_3250_, 0);
lean_inc_ref(v_segments_3290_);
v_absolute_3291_ = lean_ctor_get_uint8(v_path_3250_, sizeof(void*)*1);
lean_dec_ref(v_path_3250_);
v___x_3292_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3293_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3294_ = lean_array_size(v_segments_3290_);
v___x_3295_ = ((size_t)0ULL);
v___x_3296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3293_, v___f_3197_, v_sz_3294_, v___x_3295_, v_segments_3290_);
v___x_3297_ = lean_array_to_list(v___x_3296_);
v_result_3298_ = l_String_intercalate(v___x_3292_, v___x_3297_);
if (v_absolute_3291_ == 0)
{
v___y_3275_ = v___y_3289_;
v___y_3276_ = v_result_3298_;
goto v___jp_3274_;
}
else
{
lean_object* v___x_3299_; 
v___x_3299_ = lean_string_append(v___x_3292_, v_result_3298_);
lean_dec_ref(v_result_3298_);
v___y_3275_ = v___y_3289_;
v___y_3276_ = v___x_3299_;
goto v___jp_3274_;
}
}
}
case 2:
{
lean_object* v_authority_3350_; lean_object* v_userInfo_3351_; lean_object* v_host_3352_; lean_object* v_port_3353_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3365_; 
lean_dec_ref(v___f_3197_);
lean_dec_ref(v___f_3196_);
lean_dec_ref(v___f_3195_);
lean_dec_ref(v___f_3194_);
v_authority_3350_ = lean_ctor_get(v_target_3199_, 0);
lean_inc_ref(v_authority_3350_);
lean_dec_ref(v_target_3199_);
v_userInfo_3351_ = lean_ctor_get(v_authority_3350_, 0);
lean_inc(v_userInfo_3351_);
v_host_3352_ = lean_ctor_get(v_authority_3350_, 1);
lean_inc_ref(v_host_3352_);
v_port_3353_ = lean_ctor_get(v_authority_3350_, 2);
lean_inc(v_port_3353_);
lean_dec_ref(v_authority_3350_);
if (lean_obj_tag(v_userInfo_3351_) == 0)
{
lean_object* v___x_3375_; 
v___x_3375_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3365_ = v___x_3375_;
goto v___jp_3364_;
}
else
{
lean_object* v_val_3376_; lean_object* v_password_3377_; 
v_val_3376_ = lean_ctor_get(v_userInfo_3351_, 0);
lean_inc(v_val_3376_);
lean_dec_ref(v_userInfo_3351_);
v_password_3377_ = lean_ctor_get(v_val_3376_, 1);
if (lean_obj_tag(v_password_3377_) == 0)
{
lean_object* v_username_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v_username_3378_ = lean_ctor_get(v_val_3376_, 0);
lean_inc_ref(v_username_3378_);
lean_dec(v_val_3376_);
v___x_3379_ = lean_string_from_utf8_unchecked(v_username_3378_);
v___x_3380_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3381_ = lean_string_append(v___x_3379_, v___x_3380_);
v___y_3365_ = v___x_3381_;
goto v___jp_3364_;
}
else
{
lean_object* v_username_3382_; lean_object* v_val_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
lean_inc_ref(v_password_3377_);
v_username_3382_ = lean_ctor_get(v_val_3376_, 0);
lean_inc_ref(v_username_3382_);
lean_dec(v_val_3376_);
v_val_3383_ = lean_ctor_get(v_password_3377_, 0);
lean_inc(v_val_3383_);
lean_dec_ref(v_password_3377_);
v___x_3384_ = lean_string_from_utf8_unchecked(v_username_3382_);
v___x_3385_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3386_ = lean_string_append(v___x_3384_, v___x_3385_);
v___x_3387_ = lean_string_from_utf8_unchecked(v_val_3383_);
v___x_3388_ = lean_string_append(v___x_3386_, v___x_3387_);
lean_dec_ref(v___x_3387_);
v___x_3389_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3390_ = lean_string_append(v___x_3388_, v___x_3389_);
v___y_3365_ = v___x_3390_;
goto v___jp_3364_;
}
}
v___jp_3354_:
{
switch(lean_obj_tag(v_port_3353_))
{
case 0:
{
lean_object* v___x_3357_; 
v___x_3357_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3216_ = v___y_3356_;
v___y_3217_ = v___y_3355_;
v___y_3218_ = v___x_3357_;
goto v___jp_3215_;
}
case 1:
{
lean_object* v___x_3358_; 
v___x_3358_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3216_ = v___y_3356_;
v___y_3217_ = v___y_3355_;
v___y_3218_ = v___x_3358_;
goto v___jp_3215_;
}
default: 
{
uint16_t v_port_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v_port_3359_ = lean_ctor_get_uint16(v_port_3353_, 0);
lean_dec_ref(v_port_3353_);
v___x_3360_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3361_ = lean_uint16_to_nat(v_port_3359_);
v___x_3362_ = l_Nat_reprFast(v___x_3361_);
v___x_3363_ = lean_string_append(v___x_3360_, v___x_3362_);
lean_dec_ref(v___x_3362_);
v___y_3216_ = v___y_3356_;
v___y_3217_ = v___y_3355_;
v___y_3218_ = v___x_3363_;
goto v___jp_3215_;
}
}
}
v___jp_3364_:
{
switch(lean_obj_tag(v_host_3352_))
{
case 0:
{
lean_object* v_name_3366_; 
v_name_3366_ = lean_ctor_get(v_host_3352_, 0);
lean_inc_ref(v_name_3366_);
lean_dec_ref(v_host_3352_);
v___y_3355_ = v___y_3365_;
v___y_3356_ = v_name_3366_;
goto v___jp_3354_;
}
case 1:
{
lean_object* v_ipv4_3367_; lean_object* v___x_3368_; 
v_ipv4_3367_ = lean_ctor_get(v_host_3352_, 0);
lean_inc_ref(v_ipv4_3367_);
lean_dec_ref(v_host_3352_);
v___x_3368_ = lean_uv_ntop_v4(v_ipv4_3367_);
lean_dec_ref(v_ipv4_3367_);
v___y_3355_ = v___y_3365_;
v___y_3356_ = v___x_3368_;
goto v___jp_3354_;
}
default: 
{
lean_object* v_ipv6_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_ipv6_3369_ = lean_ctor_get(v_host_3352_, 0);
lean_inc_ref(v_ipv6_3369_);
lean_dec_ref(v_host_3352_);
v___x_3370_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3371_ = lean_uv_ntop_v6(v_ipv6_3369_);
lean_dec_ref(v_ipv6_3369_);
v___x_3372_ = lean_string_append(v___x_3370_, v___x_3371_);
lean_dec_ref(v___x_3371_);
v___x_3373_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3374_ = lean_string_append(v___x_3372_, v___x_3373_);
v___y_3355_ = v___y_3365_;
v___y_3356_ = v___x_3374_;
goto v___jp_3354_;
}
}
}
}
default: 
{
lean_object* v___x_3391_; 
lean_dec_ref(v___f_3197_);
lean_dec_ref(v___f_3196_);
lean_dec_ref(v___f_3195_);
lean_dec_ref(v___f_3194_);
v___x_3391_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__4___closed__0));
v___y_3201_ = v___x_3391_;
goto v___jp_3200_;
}
}
v___jp_3200_:
{
lean_object* v_data_3202_; lean_object* v_size_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3214_; 
v_data_3202_ = lean_ctor_get(v_buffer_3198_, 0);
v_size_3203_ = lean_ctor_get(v_buffer_3198_, 1);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_buffer_3198_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3205_ = v_buffer_3198_;
v_isShared_3206_ = v_isSharedCheck_3214_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_size_3203_);
lean_inc(v_data_3202_);
lean_dec(v_buffer_3198_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3214_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3212_; 
v___x_3207_ = lean_string_to_utf8(v___y_3201_);
lean_dec_ref(v___y_3201_);
lean_inc_ref(v___x_3207_);
v___x_3208_ = lean_array_push(v_data_3202_, v___x_3207_);
v___x_3209_ = lean_byte_array_size(v___x_3207_);
lean_dec_ref(v___x_3207_);
v___x_3210_ = lean_nat_add(v_size_3203_, v___x_3209_);
lean_dec(v_size_3203_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 1, v___x_3210_);
lean_ctor_set(v___x_3205_, 0, v___x_3208_);
v___x_3212_ = v___x_3205_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3208_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
v___jp_3215_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = lean_string_append(v___y_3217_, v___y_3216_);
lean_dec_ref(v___y_3216_);
v___x_3220_ = lean_string_append(v___x_3219_, v___y_3218_);
lean_dec_ref(v___y_3218_);
v___y_3201_ = v___x_3220_;
goto v___jp_3200_;
}
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Std_Net(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Internal(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_URI_Encoding(uint8_t builtin);
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
