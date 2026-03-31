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
uint8_t l_ByteArray_instDecidableEq(lean_object*, lean_object*);
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
lean_object* l_ByteArray_instDecidableEq___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Http_URI_instBEqQuery___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instBEqQuery___aux__1___closed__0;
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
lean_dec_ref(v_x_335_);
v___x_337_ = 0;
return v___x_337_;
}
}
else
{
if (lean_obj_tag(v_x_335_) == 0)
{
uint8_t v___x_338_; 
lean_dec_ref(v_x_334_);
v___x_338_ = 0;
return v___x_338_;
}
else
{
lean_object* v_val_339_; lean_object* v_val_340_; uint8_t v___x_341_; 
v_val_339_ = lean_ctor_get(v_x_334_, 0);
lean_inc(v_val_339_);
lean_dec_ref(v_x_334_);
v_val_340_ = lean_ctor_get(v_x_335_, 0);
lean_inc(v_val_340_);
lean_dec_ref(v_x_335_);
v___x_341_ = l_ByteArray_instDecidableEq(v_val_339_, v_val_340_);
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
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqUserInfo_beq(lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
lean_object* v_username_348_; lean_object* v_password_349_; lean_object* v_username_350_; lean_object* v_password_351_; uint8_t v___x_352_; 
v_username_348_ = lean_ctor_get(v_x_346_, 0);
lean_inc_ref(v_username_348_);
v_password_349_ = lean_ctor_get(v_x_346_, 1);
lean_inc(v_password_349_);
lean_dec_ref(v_x_346_);
v_username_350_ = lean_ctor_get(v_x_347_, 0);
lean_inc_ref(v_username_350_);
v_password_351_ = lean_ctor_get(v_x_347_, 1);
lean_inc(v_password_351_);
lean_dec_ref(v_x_347_);
v___x_352_ = l_ByteArray_instDecidableEq(v_username_348_, v_username_350_);
if (v___x_352_ == 0)
{
lean_dec(v_password_351_);
lean_dec(v_password_349_);
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
lean_dec_ref(v_x_945_);
v___x_947_ = 0;
return v___x_947_;
}
}
else
{
if (lean_obj_tag(v_x_945_) == 0)
{
uint8_t v___x_948_; 
lean_dec_ref(v_x_944_);
v___x_948_ = 0;
return v___x_948_;
}
else
{
lean_object* v_val_949_; lean_object* v_val_950_; uint8_t v___x_951_; 
v_val_949_ = lean_ctor_get(v_x_944_, 0);
lean_inc(v_val_949_);
lean_dec_ref(v_x_944_);
v_val_950_ = lean_ctor_get(v_x_945_, 0);
lean_inc(v_val_950_);
lean_dec_ref(v_x_945_);
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
v_r_955_ = lean_box(v_res_954_);
return v_r_955_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqAuthority_beq(lean_object* v_x_956_, lean_object* v_x_957_){
_start:
{
lean_object* v_userInfo_958_; lean_object* v_host_959_; lean_object* v_port_960_; lean_object* v_userInfo_961_; lean_object* v_host_962_; lean_object* v_port_963_; uint8_t v___x_964_; 
v_userInfo_958_ = lean_ctor_get(v_x_956_, 0);
lean_inc(v_userInfo_958_);
v_host_959_ = lean_ctor_get(v_x_956_, 1);
lean_inc_ref(v_host_959_);
v_port_960_ = lean_ctor_get(v_x_956_, 2);
lean_inc(v_port_960_);
lean_dec_ref(v_x_956_);
v_userInfo_961_ = lean_ctor_get(v_x_957_, 0);
lean_inc(v_userInfo_961_);
v_host_962_ = lean_ctor_get(v_x_957_, 1);
lean_inc_ref(v_host_962_);
v_port_963_ = lean_ctor_get(v_x_957_, 2);
lean_inc(v_port_963_);
lean_dec_ref(v_x_957_);
v___x_964_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqAuthority_beq_spec__0(v_userInfo_958_, v_userInfo_961_);
if (v___x_964_ == 0)
{
lean_dec(v_port_963_);
lean_dec_ref(v_host_962_);
lean_dec(v_port_960_);
lean_dec_ref(v_host_959_);
return v___x_964_;
}
else
{
uint8_t v___x_965_; 
v___x_965_ = l_Std_Http_URI_instBEqHost_beq(v_host_959_, v_host_962_);
lean_dec_ref(v_host_962_);
lean_dec_ref(v_host_959_);
if (v___x_965_ == 0)
{
lean_dec(v_port_963_);
lean_dec(v_port_960_);
return v___x_965_;
}
else
{
uint8_t v___x_966_; 
v___x_966_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_960_, v_port_963_);
lean_dec(v_port_963_);
lean_dec(v_port_960_);
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
lean_inc(v___x_1172_);
lean_inc(v___x_1171_);
v___x_1173_ = l_ByteArray_instDecidableEq(v___x_1171_, v___x_1172_);
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
v___x_1554_ = l_ByteArray_instDecidableEq(v_fst_1550_, v_fst_1552_);
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
static lean_object* _init_l_Std_Http_URI_instBEqQuery___aux__1___closed__0(void){
_start:
{
lean_object* v___f_1561_; lean_object* v___f_1562_; 
v___f_1561_ = lean_alloc_closure((void*)(l_ByteArray_instDecidableEq___boxed), 2, 0);
v___f_1562_ = lean_alloc_closure((void*)(l_Std_Http_URI_instBEqQuery___aux__1___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1562_, 0, v___f_1561_);
return v___f_1562_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___aux__1(lean_object* v_xs_1563_, lean_object* v_ys_1564_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1565_ = lean_array_get_size(v_xs_1563_);
v___x_1566_ = lean_array_get_size(v_ys_1564_);
v___x_1567_ = lean_nat_dec_eq(v___x_1565_, v___x_1566_);
if (v___x_1567_ == 0)
{
return v___x_1567_;
}
else
{
lean_object* v___f_1568_; uint8_t v___x_1569_; 
v___f_1568_ = lean_obj_once(&l_Std_Http_URI_instBEqQuery___aux__1___closed__0, &l_Std_Http_URI_instBEqQuery___aux__1___closed__0_once, _init_l_Std_Http_URI_instBEqQuery___aux__1___closed__0);
v___x_1569_ = l_Array_isEqvAux___redArg(v_xs_1563_, v_ys_1564_, v___f_1568_, v___x_1565_);
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___aux__1___boxed(lean_object* v_xs_1570_, lean_object* v_ys_1571_){
_start:
{
uint8_t v_res_1572_; lean_object* v_r_1573_; 
v_res_1572_ = l_Std_Http_URI_instBEqQuery___aux__1(v_xs_1570_, v_ys_1571_);
lean_dec_ref(v_ys_1571_);
lean_dec_ref(v_xs_1570_);
v_r_1573_ = lean_box(v_res_1572_);
return v_r_1573_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(lean_object* v_x_1574_, lean_object* v_x_1575_){
_start:
{
if (lean_obj_tag(v_x_1574_) == 0)
{
if (lean_obj_tag(v_x_1575_) == 0)
{
uint8_t v___x_1576_; 
v___x_1576_ = 1;
return v___x_1576_;
}
else
{
uint8_t v___x_1577_; 
lean_dec_ref(v_x_1575_);
v___x_1577_ = 0;
return v___x_1577_;
}
}
else
{
if (lean_obj_tag(v_x_1575_) == 0)
{
uint8_t v___x_1578_; 
lean_dec_ref(v_x_1574_);
v___x_1578_ = 0;
return v___x_1578_;
}
else
{
lean_object* v_val_1579_; lean_object* v_val_1580_; uint8_t v___x_1581_; 
v_val_1579_ = lean_ctor_get(v_x_1574_, 0);
lean_inc(v_val_1579_);
lean_dec_ref(v_x_1574_);
v_val_1580_ = lean_ctor_get(v_x_1575_, 0);
lean_inc(v_val_1580_);
lean_dec_ref(v_x_1575_);
v___x_1581_ = l_ByteArray_instDecidableEq(v_val_1579_, v_val_1580_);
return v___x_1581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0___boxed(lean_object* v_x_1582_, lean_object* v_x_1583_){
_start:
{
uint8_t v_res_1584_; lean_object* v_r_1585_; 
v_res_1584_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_x_1582_, v_x_1583_);
v_r_1585_ = lean_box(v_res_1584_);
return v_r_1585_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(lean_object* v_xs_1586_, lean_object* v_ys_1587_, lean_object* v_x_1588_){
_start:
{
lean_object* v_zero_1589_; uint8_t v_isZero_1590_; 
v_zero_1589_ = lean_unsigned_to_nat(0u);
v_isZero_1590_ = lean_nat_dec_eq(v_x_1588_, v_zero_1589_);
if (v_isZero_1590_ == 1)
{
lean_dec(v_x_1588_);
return v_isZero_1590_;
}
else
{
lean_object* v_one_1591_; lean_object* v_n_1592_; uint8_t v___y_1594_; lean_object* v___x_1596_; lean_object* v_fst_1597_; lean_object* v_snd_1598_; lean_object* v___x_1599_; lean_object* v_fst_1600_; lean_object* v_snd_1601_; uint8_t v___x_1602_; 
v_one_1591_ = lean_unsigned_to_nat(1u);
v_n_1592_ = lean_nat_sub(v_x_1588_, v_one_1591_);
lean_dec(v_x_1588_);
v___x_1596_ = lean_array_fget_borrowed(v_xs_1586_, v_n_1592_);
v_fst_1597_ = lean_ctor_get(v___x_1596_, 0);
v_snd_1598_ = lean_ctor_get(v___x_1596_, 1);
v___x_1599_ = lean_array_fget_borrowed(v_ys_1587_, v_n_1592_);
v_fst_1600_ = lean_ctor_get(v___x_1599_, 0);
v_snd_1601_ = lean_ctor_get(v___x_1599_, 1);
lean_inc(v_fst_1600_);
lean_inc(v_fst_1597_);
v___x_1602_ = l_ByteArray_instDecidableEq(v_fst_1597_, v_fst_1600_);
if (v___x_1602_ == 0)
{
v___y_1594_ = v___x_1602_;
goto v___jp_1593_;
}
else
{
uint8_t v___x_1603_; 
lean_inc(v_snd_1601_);
lean_inc(v_snd_1598_);
v___x_1603_ = l_Option_instBEq_beq___at___00Std_Http_URI_instBEqQuery_spec__0(v_snd_1598_, v_snd_1601_);
v___y_1594_ = v___x_1603_;
goto v___jp_1593_;
}
v___jp_1593_:
{
if (v___y_1594_ == 0)
{
lean_dec(v_n_1592_);
return v___y_1594_;
}
else
{
v_x_1588_ = v_n_1592_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg___boxed(lean_object* v_xs_1604_, lean_object* v_ys_1605_, lean_object* v_x_1606_){
_start:
{
uint8_t v_res_1607_; lean_object* v_r_1608_; 
v_res_1607_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1604_, v_ys_1605_, v_x_1606_);
lean_dec_ref(v_ys_1605_);
lean_dec_ref(v_xs_1604_);
v_r_1608_ = lean_box(v_res_1607_);
return v_r_1608_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_instBEqQuery___lam__0(lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1611_ = lean_array_get_size(v___y_1609_);
v___x_1612_ = lean_array_get_size(v___y_1610_);
v___x_1613_ = lean_nat_dec_eq(v___x_1611_, v___x_1612_);
if (v___x_1613_ == 0)
{
return v___x_1613_;
}
else
{
uint8_t v___x_1614_; 
v___x_1614_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v___y_1609_, v___y_1610_, v___x_1611_);
return v___x_1614_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery___lam__0___boxed(lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
uint8_t v_res_1617_; lean_object* v_r_1618_; 
v_res_1617_ = l_Std_Http_URI_instBEqQuery___lam__0(v___y_1615_, v___y_1616_);
lean_dec_ref(v___y_1616_);
lean_dec_ref(v___y_1615_);
v_r_1618_ = lean_box(v_res_1617_);
return v_r_1618_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(lean_object* v_xs_1621_, lean_object* v_ys_1622_, lean_object* v_hsz_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_){
_start:
{
uint8_t v___x_1626_; 
v___x_1626_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_xs_1621_, v_ys_1622_, v_x_1624_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___boxed(lean_object* v_xs_1627_, lean_object* v_ys_1628_, lean_object* v_hsz_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_){
_start:
{
uint8_t v_res_1632_; lean_object* v_r_1633_; 
v_res_1632_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1(v_xs_1627_, v_ys_1628_, v_hsz_1629_, v_x_1630_, v_x_1631_);
lean_dec_ref(v_ys_1628_);
lean_dec_ref(v_xs_1627_);
v_r_1633_ = lean_box(v_res_1632_);
return v_r_1633_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(lean_object* v_as_1634_){
_start:
{
lean_object* v___f_1635_; lean_object* v___x_1636_; 
v___f_1635_ = lean_alloc_closure((void*)(l_ByteArray_instDecidableEq___boxed), 2, 0);
v___x_1636_ = l_List_eraseDupsBy___redArg(v___f_1635_, v_as_1634_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(size_t v_sz_1637_, size_t v_i_1638_, lean_object* v_bs_1639_){
_start:
{
uint8_t v___x_1640_; 
v___x_1640_ = lean_usize_dec_lt(v_i_1638_, v_sz_1637_);
if (v___x_1640_ == 0)
{
return v_bs_1639_;
}
else
{
lean_object* v_v_1641_; lean_object* v_fst_1642_; lean_object* v___x_1643_; lean_object* v_bs_x27_1644_; size_t v___x_1645_; size_t v___x_1646_; lean_object* v___x_1647_; 
v_v_1641_ = lean_array_uget_borrowed(v_bs_1639_, v_i_1638_);
v_fst_1642_ = lean_ctor_get(v_v_1641_, 0);
lean_inc(v_fst_1642_);
v___x_1643_ = lean_unsigned_to_nat(0u);
v_bs_x27_1644_ = lean_array_uset(v_bs_1639_, v_i_1638_, v___x_1643_);
v___x_1645_ = ((size_t)1ULL);
v___x_1646_ = lean_usize_add(v_i_1638_, v___x_1645_);
v___x_1647_ = lean_array_uset(v_bs_x27_1644_, v_i_1638_, v_fst_1642_);
v_i_1638_ = v___x_1646_;
v_bs_1639_ = v___x_1647_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0___boxed(lean_object* v_sz_1649_, lean_object* v_i_1650_, lean_object* v_bs_1651_){
_start:
{
size_t v_sz_boxed_1652_; size_t v_i_boxed_1653_; lean_object* v_res_1654_; 
v_sz_boxed_1652_ = lean_unbox_usize(v_sz_1649_);
lean_dec(v_sz_1649_);
v_i_boxed_1653_ = lean_unbox_usize(v_i_1650_);
lean_dec(v_i_1650_);
v_res_1654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_boxed_1652_, v_i_boxed_1653_, v_bs_1651_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names(lean_object* v_query_1655_){
_start:
{
size_t v_sz_1656_; size_t v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_sz_1656_ = lean_array_size(v_query_1655_);
v___x_1657_ = ((size_t)0ULL);
v___x_1658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_1656_, v___x_1657_, v_query_1655_);
v___x_1659_ = lean_array_to_list(v___x_1658_);
v___x_1660_ = l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(v___x_1659_);
v___x_1661_ = lean_array_mk(v___x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(size_t v_sz_1662_, size_t v_i_1663_, lean_object* v_bs_1664_){
_start:
{
uint8_t v___x_1665_; 
v___x_1665_ = lean_usize_dec_lt(v_i_1663_, v_sz_1662_);
if (v___x_1665_ == 0)
{
return v_bs_1664_;
}
else
{
lean_object* v_v_1666_; lean_object* v_snd_1667_; lean_object* v___x_1668_; lean_object* v_bs_x27_1669_; size_t v___x_1670_; size_t v___x_1671_; lean_object* v___x_1672_; 
v_v_1666_ = lean_array_uget_borrowed(v_bs_1664_, v_i_1663_);
v_snd_1667_ = lean_ctor_get(v_v_1666_, 1);
lean_inc(v_snd_1667_);
v___x_1668_ = lean_unsigned_to_nat(0u);
v_bs_x27_1669_ = lean_array_uset(v_bs_1664_, v_i_1663_, v___x_1668_);
v___x_1670_ = ((size_t)1ULL);
v___x_1671_ = lean_usize_add(v_i_1663_, v___x_1670_);
v___x_1672_ = lean_array_uset(v_bs_x27_1669_, v_i_1663_, v_snd_1667_);
v_i_1663_ = v___x_1671_;
v_bs_1664_ = v___x_1672_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0___boxed(lean_object* v_sz_1674_, lean_object* v_i_1675_, lean_object* v_bs_1676_){
_start:
{
size_t v_sz_boxed_1677_; size_t v_i_boxed_1678_; lean_object* v_res_1679_; 
v_sz_boxed_1677_ = lean_unbox_usize(v_sz_1674_);
lean_dec(v_sz_1674_);
v_i_boxed_1678_ = lean_unbox_usize(v_i_1675_);
lean_dec(v_i_1675_);
v_res_1679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_boxed_1677_, v_i_boxed_1678_, v_bs_1676_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_values(lean_object* v_query_1680_){
_start:
{
size_t v_sz_1681_; size_t v___x_1682_; lean_object* v___x_1683_; 
v_sz_1681_ = lean_array_size(v_query_1680_);
v___x_1682_ = ((size_t)0ULL);
v___x_1683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_1681_, v___x_1682_, v_query_1680_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray(lean_object* v_query_1684_){
_start:
{
lean_inc_ref(v_query_1684_);
return v_query_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray___boxed(lean_object* v_query_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Std_Http_URI_Query_toArray(v_query_1685_);
lean_dec_ref(v_query_1685_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object* v_key_1688_, lean_object* v_value_1689_){
_start:
{
if (lean_obj_tag(v_value_1689_) == 0)
{
lean_object* v___x_1690_; 
v___x_1690_ = lean_string_from_utf8_unchecked(v_key_1688_);
return v___x_1690_;
}
else
{
lean_object* v_val_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_val_1691_ = lean_ctor_get(v_value_1689_, 0);
lean_inc(v_val_1691_);
lean_dec_ref(v_value_1689_);
v___x_1692_ = lean_string_from_utf8_unchecked(v_key_1688_);
v___x_1693_ = ((lean_object*)(l_Std_Http_URI_Query_formatQueryParam___closed__0));
v___x_1694_ = lean_string_append(v___x_1692_, v___x_1693_);
v___x_1695_ = lean_string_from_utf8_unchecked(v_val_1691_);
v___x_1696_ = lean_string_append(v___x_1694_, v___x_1695_);
lean_dec_ref(v___x_1695_);
return v___x_1696_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(lean_object* v_key_1700_, lean_object* v_as_1701_, size_t v_sz_1702_, size_t v_i_1703_, lean_object* v_b_1704_){
_start:
{
uint8_t v___x_1705_; 
v___x_1705_ = lean_usize_dec_lt(v_i_1703_, v_sz_1702_);
if (v___x_1705_ == 0)
{
lean_dec_ref(v_key_1700_);
lean_inc_ref(v_b_1704_);
return v_b_1704_;
}
else
{
lean_object* v_a_1706_; lean_object* v_fst_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v_a_1706_ = lean_array_uget_borrowed(v_as_1701_, v_i_1703_);
v_fst_1707_ = lean_ctor_get(v_a_1706_, 0);
v___x_1708_ = lean_box(0);
lean_inc_ref(v_key_1700_);
lean_inc(v_fst_1707_);
v___x_1709_ = l_ByteArray_instDecidableEq(v_fst_1707_, v_key_1700_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; size_t v___x_1711_; size_t v___x_1712_; 
v___x_1710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v___x_1711_ = ((size_t)1ULL);
v___x_1712_ = lean_usize_add(v_i_1703_, v___x_1711_);
v_i_1703_ = v___x_1712_;
v_b_1704_ = v___x_1710_;
goto _start;
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_dec_ref(v_key_1700_);
lean_inc(v_a_1706_);
v___x_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1714_, 0, v_a_1706_);
v___x_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
lean_ctor_set(v___x_1716_, 1, v___x_1708_);
return v___x_1716_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___boxed(lean_object* v_key_1717_, lean_object* v_as_1718_, lean_object* v_sz_1719_, lean_object* v_i_1720_, lean_object* v_b_1721_){
_start:
{
size_t v_sz_boxed_1722_; size_t v_i_boxed_1723_; lean_object* v_res_1724_; 
v_sz_boxed_1722_ = lean_unbox_usize(v_sz_1719_);
lean_dec(v_sz_1719_);
v_i_boxed_1723_ = lean_unbox_usize(v_i_1720_);
lean_dec(v_i_1720_);
v_res_1724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1717_, v_as_1718_, v_sz_boxed_1722_, v_i_boxed_1723_, v_b_1721_);
lean_dec_ref(v_b_1721_);
lean_dec_ref(v_as_1718_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f(lean_object* v_query_1725_, lean_object* v_key_1726_){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; size_t v_sz_1729_; size_t v___x_1730_; lean_object* v___x_1731_; lean_object* v_fst_1732_; 
v___x_1727_ = lean_box(0);
v___x_1728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v_sz_1729_ = lean_array_size(v_query_1725_);
v___x_1730_ = ((size_t)0ULL);
v___x_1731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1726_, v_query_1725_, v_sz_1729_, v___x_1730_, v___x_1728_);
v_fst_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_fst_1732_);
lean_dec_ref(v___x_1731_);
if (lean_obj_tag(v_fst_1732_) == 0)
{
return v___x_1727_;
}
else
{
lean_object* v_val_1733_; 
v_val_1733_ = lean_ctor_get(v_fst_1732_, 0);
lean_inc(v_val_1733_);
lean_dec_ref(v_fst_1732_);
if (lean_obj_tag(v_val_1733_) == 0)
{
return v___x_1727_;
}
else
{
lean_object* v_val_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1742_; 
v_val_1734_ = lean_ctor_get(v_val_1733_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_val_1733_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1736_ = v_val_1733_;
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_val_1734_);
lean_dec(v_val_1733_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v_snd_1738_; lean_object* v___x_1740_; 
v_snd_1738_ = lean_ctor_get(v_val_1734_, 1);
lean_inc(v_snd_1738_);
lean_dec(v_val_1734_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v_snd_1738_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_snd_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f___boxed(lean_object* v_query_1743_, lean_object* v_key_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1743_, v_key_1744_);
lean_dec_ref(v_query_1743_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f(lean_object* v_query_1746_, lean_object* v_key_1747_){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1747_);
v___x_1749_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1746_, v___x_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f___boxed(lean_object* v_query_1750_, lean_object* v_key_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Std_Http_URI_Query_find_x3f(v_query_1750_, v_key_1751_);
lean_dec_ref(v_key_1751_);
lean_dec_ref(v_query_1750_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(lean_object* v_key_1753_, lean_object* v_as_1754_, size_t v_i_1755_, size_t v_stop_1756_, lean_object* v_b_1757_){
_start:
{
lean_object* v___y_1759_; uint8_t v___x_1763_; 
v___x_1763_ = lean_usize_dec_eq(v_i_1755_, v_stop_1756_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v_fst_1765_; lean_object* v_snd_1766_; uint8_t v___x_1767_; 
v___x_1764_ = lean_array_uget_borrowed(v_as_1754_, v_i_1755_);
v_fst_1765_ = lean_ctor_get(v___x_1764_, 0);
v_snd_1766_ = lean_ctor_get(v___x_1764_, 1);
lean_inc_ref(v_key_1753_);
lean_inc(v_fst_1765_);
v___x_1767_ = l_ByteArray_instDecidableEq(v_fst_1765_, v_key_1753_);
if (v___x_1767_ == 0)
{
v___y_1759_ = v_b_1757_;
goto v___jp_1758_;
}
else
{
lean_object* v___x_1768_; 
lean_inc(v_snd_1766_);
v___x_1768_ = lean_array_push(v_b_1757_, v_snd_1766_);
v___y_1759_ = v___x_1768_;
goto v___jp_1758_;
}
}
else
{
lean_dec_ref(v_key_1753_);
return v_b_1757_;
}
v___jp_1758_:
{
size_t v___x_1760_; size_t v___x_1761_; 
v___x_1760_ = ((size_t)1ULL);
v___x_1761_ = lean_usize_add(v_i_1755_, v___x_1760_);
v_i_1755_ = v___x_1761_;
v_b_1757_ = v___y_1759_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0___boxed(lean_object* v_key_1769_, lean_object* v_as_1770_, lean_object* v_i_1771_, lean_object* v_stop_1772_, lean_object* v_b_1773_){
_start:
{
size_t v_i_boxed_1774_; size_t v_stop_boxed_1775_; lean_object* v_res_1776_; 
v_i_boxed_1774_ = lean_unbox_usize(v_i_1771_);
lean_dec(v_i_1771_);
v_stop_boxed_1775_ = lean_unbox_usize(v_stop_1772_);
lean_dec(v_stop_1772_);
v_res_1776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1769_, v_as_1770_, v_i_boxed_1774_, v_stop_boxed_1775_, v_b_1773_);
lean_dec_ref(v_as_1770_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(lean_object* v_key_1779_, lean_object* v_as_1780_, lean_object* v_start_1781_, lean_object* v_stop_1782_){
_start:
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_1784_ = lean_nat_dec_lt(v_start_1781_, v_stop_1782_);
if (v___x_1784_ == 0)
{
lean_dec_ref(v_key_1779_);
return v___x_1783_;
}
else
{
lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = lean_array_get_size(v_as_1780_);
v___x_1786_ = lean_nat_dec_le(v_stop_1782_, v___x_1785_);
if (v___x_1786_ == 0)
{
uint8_t v___x_1787_; 
v___x_1787_ = lean_nat_dec_lt(v_start_1781_, v___x_1785_);
if (v___x_1787_ == 0)
{
lean_dec_ref(v_key_1779_);
return v___x_1783_;
}
else
{
size_t v___x_1788_; size_t v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = lean_usize_of_nat(v_start_1781_);
v___x_1789_ = lean_usize_of_nat(v___x_1785_);
v___x_1790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1779_, v_as_1780_, v___x_1788_, v___x_1789_, v___x_1783_);
return v___x_1790_;
}
}
else
{
size_t v___x_1791_; size_t v___x_1792_; lean_object* v___x_1793_; 
v___x_1791_ = lean_usize_of_nat(v_start_1781_);
v___x_1792_ = lean_usize_of_nat(v_stop_1782_);
v___x_1793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1779_, v_as_1780_, v___x_1791_, v___x_1792_, v___x_1783_);
return v___x_1793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___boxed(lean_object* v_key_1794_, lean_object* v_as_1795_, lean_object* v_start_1796_, lean_object* v_stop_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1794_, v_as_1795_, v_start_1796_, v_stop_1797_);
lean_dec(v_stop_1797_);
lean_dec(v_start_1796_);
lean_dec_ref(v_as_1795_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded(lean_object* v_query_1799_, lean_object* v_key_1800_){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = lean_array_get_size(v_query_1799_);
v___x_1803_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1800_, v_query_1799_, v___x_1801_, v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded___boxed(lean_object* v_query_1804_, lean_object* v_key_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1804_, v_key_1805_);
lean_dec_ref(v_query_1804_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll(lean_object* v_query_1807_, lean_object* v_key_1808_){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1808_);
v___x_1810_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1807_, v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll___boxed(lean_object* v_query_1811_, lean_object* v_key_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Std_Http_URI_Query_findAll(v_query_1811_, v_key_1812_);
lean_dec_ref(v_key_1812_);
lean_dec_ref(v_query_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert(lean_object* v_query_1814_, lean_object* v_key_1815_, lean_object* v_value_1816_){
_start:
{
lean_object* v_encodedKey_1817_; lean_object* v_encodedValue_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v_encodedKey_1817_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1815_);
v_encodedValue_1818_ = l_Std_Http_URI_EncodedQueryParam_encode(v_value_1816_);
v___x_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1819_, 0, v_encodedValue_1818_);
v___x_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1820_, 0, v_encodedKey_1817_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = lean_array_push(v_query_1814_, v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert___boxed(lean_object* v_query_1822_, lean_object* v_key_1823_, lean_object* v_value_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Std_Http_URI_Query_insert(v_query_1822_, v_key_1823_, v_value_1824_);
lean_dec_ref(v_value_1824_);
lean_dec_ref(v_key_1823_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object* v_query_1826_, lean_object* v_key_1827_, lean_object* v_value_1828_){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v_key_1827_);
lean_ctor_set(v___x_1829_, 1, v_value_1828_);
v___x_1830_ = lean_array_push(v_query_1826_, v___x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_ofList(lean_object* v_pairs_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_array_mk(v_pairs_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(lean_object* v_key_1836_, lean_object* v_as_1837_, size_t v_i_1838_, size_t v_stop_1839_){
_start:
{
uint8_t v___x_1840_; 
v___x_1840_ = lean_usize_dec_eq(v_i_1838_, v_stop_1839_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v_fst_1842_; uint8_t v___x_1843_; 
v___x_1841_ = lean_array_uget_borrowed(v_as_1837_, v_i_1838_);
v_fst_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc_ref(v_key_1836_);
lean_inc(v_fst_1842_);
v___x_1843_ = l_ByteArray_instDecidableEq(v_fst_1842_, v_key_1836_);
if (v___x_1843_ == 0)
{
size_t v___x_1844_; size_t v___x_1845_; 
v___x_1844_ = ((size_t)1ULL);
v___x_1845_ = lean_usize_add(v_i_1838_, v___x_1844_);
v_i_1838_ = v___x_1845_;
goto _start;
}
else
{
lean_dec_ref(v_key_1836_);
return v___x_1843_;
}
}
else
{
uint8_t v___x_1847_; 
lean_dec_ref(v_key_1836_);
v___x_1847_ = 0;
return v___x_1847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(lean_object* v_key_1848_, lean_object* v_as_1849_, lean_object* v_i_1850_, lean_object* v_stop_1851_){
_start:
{
size_t v_i_boxed_1852_; size_t v_stop_boxed_1853_; uint8_t v_res_1854_; lean_object* v_r_1855_; 
v_i_boxed_1852_ = lean_unbox_usize(v_i_1850_);
lean_dec(v_i_1850_);
v_stop_boxed_1853_ = lean_unbox_usize(v_stop_1851_);
lean_dec(v_stop_1851_);
v_res_1854_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1848_, v_as_1849_, v_i_boxed_1852_, v_stop_boxed_1853_);
lean_dec_ref(v_as_1849_);
v_r_1855_ = lean_box(v_res_1854_);
return v_r_1855_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_containsEncoded(lean_object* v_query_1856_, lean_object* v_key_1857_){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1858_ = lean_unsigned_to_nat(0u);
v___x_1859_ = lean_array_get_size(v_query_1856_);
v___x_1860_ = lean_nat_dec_lt(v___x_1858_, v___x_1859_);
if (v___x_1860_ == 0)
{
lean_dec_ref(v_key_1857_);
return v___x_1860_;
}
else
{
if (v___x_1860_ == 0)
{
lean_dec_ref(v_key_1857_);
return v___x_1860_;
}
else
{
size_t v___x_1861_; size_t v___x_1862_; uint8_t v___x_1863_; 
v___x_1861_ = ((size_t)0ULL);
v___x_1862_ = lean_usize_of_nat(v___x_1859_);
v___x_1863_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1857_, v_query_1856_, v___x_1861_, v___x_1862_);
return v___x_1863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_containsEncoded___boxed(lean_object* v_query_1864_, lean_object* v_key_1865_){
_start:
{
uint8_t v_res_1866_; lean_object* v_r_1867_; 
v_res_1866_ = l_Std_Http_URI_Query_containsEncoded(v_query_1864_, v_key_1865_);
lean_dec_ref(v_query_1864_);
v_r_1867_ = lean_box(v_res_1866_);
return v_r_1867_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_contains(lean_object* v_query_1868_, lean_object* v_key_1869_){
_start:
{
lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1870_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1869_);
v___x_1871_ = l_Std_Http_URI_Query_containsEncoded(v_query_1868_, v___x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_contains___boxed(lean_object* v_query_1872_, lean_object* v_key_1873_){
_start:
{
uint8_t v_res_1874_; lean_object* v_r_1875_; 
v_res_1874_ = l_Std_Http_URI_Query_contains(v_query_1872_, v_key_1873_);
lean_dec_ref(v_key_1873_);
lean_dec_ref(v_query_1872_);
v_r_1875_ = lean_box(v_res_1874_);
return v_r_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(lean_object* v_key_1876_, lean_object* v_as_1877_, size_t v_i_1878_, size_t v_stop_1879_, lean_object* v_b_1880_){
_start:
{
lean_object* v___y_1882_; uint8_t v___x_1886_; 
v___x_1886_ = lean_usize_dec_eq(v_i_1878_, v_stop_1879_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v_fst_1890_; uint8_t v___x_1891_; 
v___x_1887_ = lean_array_uget_borrowed(v_as_1877_, v_i_1878_);
v_fst_1890_ = lean_ctor_get(v___x_1887_, 0);
lean_inc_ref(v_key_1876_);
lean_inc(v_fst_1890_);
v___x_1891_ = l_ByteArray_instDecidableEq(v_fst_1890_, v_key_1876_);
if (v___x_1891_ == 0)
{
goto v___jp_1888_;
}
else
{
if (v___x_1886_ == 0)
{
v___y_1882_ = v_b_1880_;
goto v___jp_1881_;
}
else
{
goto v___jp_1888_;
}
}
v___jp_1888_:
{
lean_object* v___x_1889_; 
lean_inc(v___x_1887_);
v___x_1889_ = lean_array_push(v_b_1880_, v___x_1887_);
v___y_1882_ = v___x_1889_;
goto v___jp_1881_;
}
}
else
{
lean_dec_ref(v_key_1876_);
return v_b_1880_;
}
v___jp_1881_:
{
size_t v___x_1883_; size_t v___x_1884_; 
v___x_1883_ = ((size_t)1ULL);
v___x_1884_ = lean_usize_add(v_i_1878_, v___x_1883_);
v_i_1878_ = v___x_1884_;
v_b_1880_ = v___y_1882_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(lean_object* v_key_1892_, lean_object* v_as_1893_, lean_object* v_i_1894_, lean_object* v_stop_1895_, lean_object* v_b_1896_){
_start:
{
size_t v_i_boxed_1897_; size_t v_stop_boxed_1898_; lean_object* v_res_1899_; 
v_i_boxed_1897_ = lean_unbox_usize(v_i_1894_);
lean_dec(v_i_1894_);
v_stop_boxed_1898_ = lean_unbox_usize(v_stop_1895_);
lean_dec(v_stop_1895_);
v_res_1899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1892_, v_as_1893_, v_i_boxed_1897_, v_stop_boxed_1898_, v_b_1896_);
lean_dec_ref(v_as_1893_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded(lean_object* v_query_1900_, lean_object* v_key_1901_){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1902_ = lean_unsigned_to_nat(0u);
v___x_1903_ = lean_array_get_size(v_query_1900_);
v___x_1904_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_1905_ = lean_nat_dec_lt(v___x_1902_, v___x_1903_);
if (v___x_1905_ == 0)
{
lean_dec_ref(v_key_1901_);
return v___x_1904_;
}
else
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_nat_dec_le(v___x_1903_, v___x_1903_);
if (v___x_1906_ == 0)
{
if (v___x_1905_ == 0)
{
lean_dec_ref(v_key_1901_);
return v___x_1904_;
}
else
{
size_t v___x_1907_; size_t v___x_1908_; lean_object* v___x_1909_; 
v___x_1907_ = ((size_t)0ULL);
v___x_1908_ = lean_usize_of_nat(v___x_1903_);
v___x_1909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1901_, v_query_1900_, v___x_1907_, v___x_1908_, v___x_1904_);
return v___x_1909_;
}
}
else
{
size_t v___x_1910_; size_t v___x_1911_; lean_object* v___x_1912_; 
v___x_1910_ = ((size_t)0ULL);
v___x_1911_ = lean_usize_of_nat(v___x_1903_);
v___x_1912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1901_, v_query_1900_, v___x_1910_, v___x_1911_, v___x_1904_);
return v___x_1912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded___boxed(lean_object* v_query_1913_, lean_object* v_key_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Std_Http_URI_Query_eraseEncoded(v_query_1913_, v_key_1914_);
lean_dec_ref(v_query_1913_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase(lean_object* v_query_1916_, lean_object* v_key_1917_){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1917_);
v___x_1919_ = l_Std_Http_URI_Query_eraseEncoded(v_query_1916_, v___x_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase___boxed(lean_object* v_query_1920_, lean_object* v_key_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Std_Http_URI_Query_erase(v_query_1920_, v_key_1921_);
lean_dec_ref(v_key_1921_);
lean_dec_ref(v_query_1920_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get(lean_object* v_query_1925_, lean_object* v_key_1926_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Std_Http_URI_Query_find_x3f(v_query_1925_, v_key_1926_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_box(0);
return v___x_1928_;
}
else
{
lean_object* v_val_1929_; 
v_val_1929_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_val_1929_);
lean_dec_ref(v___x_1927_);
if (lean_obj_tag(v_val_1929_) == 0)
{
lean_object* v___x_1930_; 
v___x_1930_ = ((lean_object*)(l_Std_Http_URI_Query_get___closed__0));
return v___x_1930_;
}
else
{
lean_object* v_val_1931_; lean_object* v___x_1932_; 
v_val_1931_ = lean_ctor_get(v_val_1929_, 0);
lean_inc(v_val_1931_);
lean_dec_ref(v_val_1929_);
v___x_1932_ = l_Std_Http_URI_EncodedQueryParam_decode(v_val_1931_);
lean_dec(v_val_1931_);
return v___x_1932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get___boxed(lean_object* v_query_1933_, lean_object* v_key_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Std_Http_URI_Query_get(v_query_1933_, v_key_1934_);
lean_dec_ref(v_key_1934_);
lean_dec_ref(v_query_1933_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD(lean_object* v_query_1936_, lean_object* v_key_1937_, lean_object* v_default_1938_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Std_Http_URI_Query_get(v_query_1936_, v_key_1937_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_inc_ref(v_default_1938_);
return v_default_1938_;
}
else
{
lean_object* v_val_1940_; 
v_val_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_val_1940_);
lean_dec_ref(v___x_1939_);
return v_val_1940_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD___boxed(lean_object* v_query_1941_, lean_object* v_key_1942_, lean_object* v_default_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Std_Http_URI_Query_getD(v_query_1941_, v_key_1942_, v_default_1943_);
lean_dec_ref(v_default_1943_);
lean_dec_ref(v_key_1942_);
lean_dec_ref(v_query_1941_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set(lean_object* v_query_1945_, lean_object* v_key_1946_, lean_object* v_value_1947_){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = l_Std_Http_URI_Query_erase(v_query_1945_, v_key_1946_);
v___x_1949_ = l_Std_Http_URI_Query_insert(v___x_1948_, v_key_1946_, v_value_1947_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set___boxed(lean_object* v_query_1950_, lean_object* v_key_1951_, lean_object* v_value_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Std_Http_URI_Query_set(v_query_1950_, v_key_1951_, v_value_1952_);
lean_dec_ref(v_value_1952_);
lean_dec_ref(v_key_1951_);
lean_dec_ref(v_query_1950_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(size_t v_sz_1954_, size_t v_i_1955_, lean_object* v_bs_1956_){
_start:
{
uint8_t v___x_1957_; 
v___x_1957_ = lean_usize_dec_lt(v_i_1955_, v_sz_1954_);
if (v___x_1957_ == 0)
{
return v_bs_1956_;
}
else
{
lean_object* v_v_1958_; lean_object* v_fst_1959_; lean_object* v_snd_1960_; lean_object* v___x_1961_; lean_object* v_bs_x27_1962_; lean_object* v___x_1963_; size_t v___x_1964_; size_t v___x_1965_; lean_object* v___x_1966_; 
v_v_1958_ = lean_array_uget_borrowed(v_bs_1956_, v_i_1955_);
v_fst_1959_ = lean_ctor_get(v_v_1958_, 0);
lean_inc(v_fst_1959_);
v_snd_1960_ = lean_ctor_get(v_v_1958_, 1);
lean_inc(v_snd_1960_);
v___x_1961_ = lean_unsigned_to_nat(0u);
v_bs_x27_1962_ = lean_array_uset(v_bs_1956_, v_i_1955_, v___x_1961_);
v___x_1963_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_1959_, v_snd_1960_);
v___x_1964_ = ((size_t)1ULL);
v___x_1965_ = lean_usize_add(v_i_1955_, v___x_1964_);
v___x_1966_ = lean_array_uset(v_bs_x27_1962_, v_i_1955_, v___x_1963_);
v_i_1955_ = v___x_1965_;
v_bs_1956_ = v___x_1966_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0___boxed(lean_object* v_sz_1968_, lean_object* v_i_1969_, lean_object* v_bs_1970_){
_start:
{
size_t v_sz_boxed_1971_; size_t v_i_boxed_1972_; lean_object* v_res_1973_; 
v_sz_boxed_1971_ = lean_unbox_usize(v_sz_1968_);
lean_dec(v_sz_1968_);
v_i_boxed_1972_ = lean_unbox_usize(v_i_1969_);
lean_dec(v_i_1969_);
v_res_1973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_boxed_1971_, v_i_boxed_1972_, v_bs_1970_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toRawString(lean_object* v_query_1975_){
_start:
{
size_t v_sz_1976_; size_t v___x_1977_; lean_object* v_params_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_sz_1976_ = lean_array_size(v_query_1975_);
v___x_1977_ = ((size_t)0ULL);
v_params_1978_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_1976_, v___x_1977_, v_query_1975_);
v___x_1979_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_1980_ = lean_array_to_list(v_params_1978_);
v___x_1981_ = l_String_intercalate(v___x_1979_, v___x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0(lean_object* v_x_1983_){
_start:
{
lean_object* v_fst_1984_; lean_object* v_snd_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v_fst_1984_ = lean_ctor_get(v_x_1983_, 0);
v_snd_1985_ = lean_ctor_get(v_x_1983_, 1);
v___x_1986_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
v___x_1987_ = l_Std_Http_URI_Query_insert(v___x_1986_, v_fst_1984_, v_snd_1985_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0___boxed(lean_object* v_x_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Std_Http_URI_Query_instSingletonProdString___lam__0(v_x_1988_);
lean_dec_ref(v_x_1988_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0(lean_object* v_x_1992_, lean_object* v_q_1993_){
_start:
{
lean_object* v_fst_1994_; lean_object* v_snd_1995_; lean_object* v___x_1996_; 
v_fst_1994_ = lean_ctor_get(v_x_1992_, 0);
v_snd_1995_ = lean_ctor_get(v_x_1992_, 1);
v___x_1996_ = l_Std_Http_URI_Query_insert(v_q_1993_, v_fst_1994_, v_snd_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0___boxed(lean_object* v_x_1997_, lean_object* v_q_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Std_Http_URI_Query_instInsertProdString___lam__0(v_x_1997_, v_q_1998_);
lean_dec_ref(v_x_1997_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__0(lean_object* v_x_2002_){
_start:
{
lean_object* v_fst_2003_; lean_object* v_snd_2004_; lean_object* v___x_2005_; 
v_fst_2003_ = lean_ctor_get(v_x_2002_, 0);
lean_inc(v_fst_2003_);
v_snd_2004_ = lean_ctor_get(v_x_2002_, 1);
lean_inc(v_snd_2004_);
lean_dec_ref(v_x_2002_);
v___x_2005_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_2003_, v_snd_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__1(lean_object* v___f_2007_, lean_object* v_q_2008_){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2009_ = lean_array_get_size(v_q_2008_);
v___x_2010_ = lean_unsigned_to_nat(0u);
v___x_2011_ = lean_nat_dec_eq(v___x_2009_, v___x_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v_encodedParams_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2012_ = lean_array_to_list(v_q_2008_);
v___x_2013_ = lean_box(0);
v_encodedParams_2014_ = l_List_mapTR_loop___redArg(v___f_2007_, v___x_2012_, v___x_2013_);
v___x_2015_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2016_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2017_ = l_String_intercalate(v___x_2016_, v_encodedParams_2014_);
v___x_2018_ = lean_string_append(v___x_2015_, v___x_2017_);
lean_dec_ref(v___x_2017_);
return v___x_2018_;
}
else
{
lean_object* v___x_2019_; 
lean_dec_ref(v_q_2008_);
lean_dec_ref(v___f_2007_);
v___x_2019_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_2019_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(lean_object* v_x_2024_, lean_object* v_x_2025_){
_start:
{
if (lean_obj_tag(v_x_2024_) == 0)
{
lean_object* v___x_2026_; 
v___x_2026_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2026_;
}
else
{
lean_object* v_val_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v_val_2027_ = lean_ctor_get(v_x_2024_, 0);
lean_inc(v_val_2027_);
lean_dec_ref(v_x_2024_);
v___x_2028_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2029_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_val_2027_);
v___x_2030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2028_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = l_Repr_addAppParen(v___x_2030_, v_x_2025_);
return v___x_2031_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(lean_object* v_x_2032_, lean_object* v_x_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_x_2032_, v_x_2033_);
lean_dec(v_x_2033_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object* v_x_2035_, lean_object* v_x_2036_){
_start:
{
if (lean_obj_tag(v_x_2035_) == 0)
{
lean_object* v___x_2037_; 
v___x_2037_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2037_;
}
else
{
lean_object* v_val_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2049_; 
v_val_2038_ = lean_ctor_get(v_x_2035_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_x_2035_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2040_ = v_x_2035_;
v_isShared_2041_ = v_isSharedCheck_2049_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_val_2038_);
lean_dec(v_x_2035_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2049_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2042_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2043_ = l_String_quote(v_val_2038_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set_tag(v___x_2040_, 3);
lean_ctor_set(v___x_2040_, 0, v___x_2043_);
v___x_2045_ = v___x_2040_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2042_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = l_Repr_addAppParen(v___x_2046_, v_x_2036_);
return v___x_2047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1___boxed(lean_object* v_x_2050_, lean_object* v_x_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_x_2050_, v_x_2051_);
lean_dec(v_x_2051_);
return v_res_2052_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = lean_unsigned_to_nat(10u);
v___x_2063_ = lean_nat_to_int(v___x_2062_);
return v___x_2063_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_unsigned_to_nat(13u);
v___x_2068_ = lean_nat_to_int(v___x_2067_);
return v___x_2068_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_unsigned_to_nat(9u);
v___x_2076_ = lean_nat_to_int(v___x_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___redArg(lean_object* v_x_2080_){
_start:
{
lean_object* v_scheme_2081_; lean_object* v_authority_2082_; lean_object* v_path_2083_; lean_object* v_query_2084_; lean_object* v_fragment_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v_scheme_2081_ = lean_ctor_get(v_x_2080_, 0);
lean_inc_ref(v_scheme_2081_);
v_authority_2082_ = lean_ctor_get(v_x_2080_, 1);
lean_inc(v_authority_2082_);
v_path_2083_ = lean_ctor_get(v_x_2080_, 2);
lean_inc_ref(v_path_2083_);
v_query_2084_ = lean_ctor_get(v_x_2080_, 3);
lean_inc_ref(v_query_2084_);
v_fragment_2085_ = lean_ctor_get(v_x_2080_, 4);
lean_inc(v_fragment_2085_);
lean_dec_ref(v_x_2080_);
v___x_2086_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_2087_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_2088_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_2089_ = l_String_quote(v_scheme_2081_);
v___x_2090_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
v___x_2091_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2088_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
v___x_2092_ = 0;
v___x_2093_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2093_, 0, v___x_2091_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*1, v___x_2092_);
v___x_2094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2087_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_2096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = lean_box(1);
v___x_2098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2096_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__6));
v___x_2100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2098_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___x_2101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v___x_2086_);
v___x_2102_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_2103_ = lean_unsigned_to_nat(0u);
v___x_2104_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_2082_, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2102_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set_uint8(v___x_2106_, sizeof(void*)*1, v___x_2092_);
v___x_2107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2101_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
v___x_2108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
lean_ctor_set(v___x_2108_, 1, v___x_2095_);
v___x_2109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set(v___x_2109_, 1, v___x_2097_);
v___x_2110_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_2111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2109_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
lean_ctor_set(v___x_2112_, 1, v___x_2086_);
v___x_2113_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2114_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_2083_);
v___x_2115_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2113_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set_uint8(v___x_2116_, sizeof(void*)*1, v___x_2092_);
v___x_2117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2112_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v___x_2095_);
v___x_2119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
lean_ctor_set(v___x_2119_, 1, v___x_2097_);
v___x_2120_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_2121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v___x_2086_);
v___x_2123_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_2124_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_query_2084_);
v___x_2125_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
lean_ctor_set_uint8(v___x_2126_, sizeof(void*)*1, v___x_2092_);
v___x_2127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2122_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_ctor_set(v___x_2128_, 1, v___x_2095_);
v___x_2129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
lean_ctor_set(v___x_2129_, 1, v___x_2097_);
v___x_2130_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_2131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2129_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
v___x_2132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v___x_2086_);
v___x_2133_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_2134_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__1(v_fragment_2085_, v___x_2103_);
v___x_2135_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2133_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set_uint8(v___x_2136_, sizeof(void*)*1, v___x_2092_);
v___x_2137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2132_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2139_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
lean_ctor_set(v___x_2140_, 1, v___x_2137_);
v___x_2141_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2140_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
v___x_2143_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2138_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
lean_ctor_set_uint8(v___x_2144_, sizeof(void*)*1, v___x_2092_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr(lean_object* v_x_2145_, lean_object* v_prec_2146_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Std_Http_instReprURI_repr___redArg(v_x_2145_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___boxed(lean_object* v_x_2148_, lean_object* v_prec_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Std_Http_instReprURI_repr(v_x_2148_, v_prec_2149_);
lean_dec(v_prec_2149_);
return v_res_2150_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object* v_x_2160_, lean_object* v_x_2161_){
_start:
{
if (lean_obj_tag(v_x_2160_) == 0)
{
if (lean_obj_tag(v_x_2161_) == 0)
{
uint8_t v___x_2162_; 
v___x_2162_ = 1;
return v___x_2162_;
}
else
{
uint8_t v___x_2163_; 
lean_dec_ref(v_x_2161_);
v___x_2163_ = 0;
return v___x_2163_;
}
}
else
{
if (lean_obj_tag(v_x_2161_) == 0)
{
uint8_t v___x_2164_; 
lean_dec_ref(v_x_2160_);
v___x_2164_ = 0;
return v___x_2164_;
}
else
{
lean_object* v_val_2165_; lean_object* v_val_2166_; uint8_t v___x_2167_; 
v_val_2165_ = lean_ctor_get(v_x_2160_, 0);
lean_inc(v_val_2165_);
lean_dec_ref(v_x_2160_);
v_val_2166_ = lean_ctor_get(v_x_2161_, 0);
lean_inc(v_val_2166_);
lean_dec_ref(v_x_2161_);
v___x_2167_ = l_Std_Http_URI_instBEqAuthority_beq(v_val_2165_, v_val_2166_);
return v___x_2167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object* v_x_2168_, lean_object* v_x_2169_){
_start:
{
uint8_t v_res_2170_; lean_object* v_r_2171_; 
v_res_2170_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_x_2168_, v_x_2169_);
v_r_2171_ = lean_box(v_res_2170_);
return v_r_2171_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object* v_x_2172_, lean_object* v_x_2173_){
_start:
{
if (lean_obj_tag(v_x_2172_) == 0)
{
if (lean_obj_tag(v_x_2173_) == 0)
{
uint8_t v___x_2174_; 
v___x_2174_ = 1;
return v___x_2174_;
}
else
{
uint8_t v___x_2175_; 
v___x_2175_ = 0;
return v___x_2175_;
}
}
else
{
if (lean_obj_tag(v_x_2173_) == 0)
{
uint8_t v___x_2176_; 
v___x_2176_ = 0;
return v___x_2176_;
}
else
{
lean_object* v_val_2177_; lean_object* v_val_2178_; uint8_t v___x_2179_; 
v_val_2177_ = lean_ctor_get(v_x_2172_, 0);
v_val_2178_ = lean_ctor_get(v_x_2173_, 0);
v___x_2179_ = lean_string_dec_eq(v_val_2177_, v_val_2178_);
return v___x_2179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object* v_x_2180_, lean_object* v_x_2181_){
_start:
{
uint8_t v_res_2182_; lean_object* v_r_2183_; 
v_res_2182_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_x_2180_, v_x_2181_);
lean_dec(v_x_2181_);
lean_dec(v_x_2180_);
v_r_2183_ = lean_box(v_res_2182_);
return v_r_2183_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object* v_x_2184_, lean_object* v_x_2185_){
_start:
{
lean_object* v_scheme_2186_; lean_object* v_authority_2187_; lean_object* v_path_2188_; lean_object* v_query_2189_; lean_object* v_fragment_2190_; lean_object* v_scheme_2191_; lean_object* v_authority_2192_; lean_object* v_path_2193_; lean_object* v_query_2194_; lean_object* v_fragment_2195_; uint8_t v___x_2196_; 
v_scheme_2186_ = lean_ctor_get(v_x_2184_, 0);
lean_inc_ref(v_scheme_2186_);
v_authority_2187_ = lean_ctor_get(v_x_2184_, 1);
lean_inc(v_authority_2187_);
v_path_2188_ = lean_ctor_get(v_x_2184_, 2);
lean_inc_ref(v_path_2188_);
v_query_2189_ = lean_ctor_get(v_x_2184_, 3);
lean_inc_ref(v_query_2189_);
v_fragment_2190_ = lean_ctor_get(v_x_2184_, 4);
lean_inc(v_fragment_2190_);
lean_dec_ref(v_x_2184_);
v_scheme_2191_ = lean_ctor_get(v_x_2185_, 0);
lean_inc_ref(v_scheme_2191_);
v_authority_2192_ = lean_ctor_get(v_x_2185_, 1);
lean_inc(v_authority_2192_);
v_path_2193_ = lean_ctor_get(v_x_2185_, 2);
lean_inc_ref(v_path_2193_);
v_query_2194_ = lean_ctor_get(v_x_2185_, 3);
lean_inc_ref(v_query_2194_);
v_fragment_2195_ = lean_ctor_get(v_x_2185_, 4);
lean_inc(v_fragment_2195_);
lean_dec_ref(v_x_2185_);
v___x_2196_ = lean_string_dec_eq(v_scheme_2186_, v_scheme_2191_);
lean_dec_ref(v_scheme_2191_);
lean_dec_ref(v_scheme_2186_);
if (v___x_2196_ == 0)
{
lean_dec(v_fragment_2195_);
lean_dec_ref(v_query_2194_);
lean_dec_ref(v_path_2193_);
lean_dec(v_authority_2192_);
lean_dec(v_fragment_2190_);
lean_dec_ref(v_query_2189_);
lean_dec_ref(v_path_2188_);
lean_dec(v_authority_2187_);
return v___x_2196_;
}
else
{
uint8_t v___x_2197_; 
v___x_2197_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_2187_, v_authority_2192_);
if (v___x_2197_ == 0)
{
lean_dec(v_fragment_2195_);
lean_dec_ref(v_query_2194_);
lean_dec_ref(v_path_2193_);
lean_dec(v_fragment_2190_);
lean_dec_ref(v_query_2189_);
lean_dec_ref(v_path_2188_);
return v___x_2197_;
}
else
{
uint8_t v___x_2198_; 
v___x_2198_ = l_Std_Http_URI_instBEqPath_beq(v_path_2188_, v_path_2193_);
lean_dec_ref(v_path_2193_);
lean_dec_ref(v_path_2188_);
if (v___x_2198_ == 0)
{
lean_dec(v_fragment_2195_);
lean_dec_ref(v_query_2194_);
lean_dec(v_fragment_2190_);
lean_dec_ref(v_query_2189_);
return v___x_2198_;
}
else
{
lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2199_ = lean_array_get_size(v_query_2189_);
v___x_2200_ = lean_array_get_size(v_query_2194_);
v___x_2201_ = lean_nat_dec_eq(v___x_2199_, v___x_2200_);
if (v___x_2201_ == 0)
{
lean_dec(v_fragment_2195_);
lean_dec_ref(v_query_2194_);
lean_dec(v_fragment_2190_);
lean_dec_ref(v_query_2189_);
return v___x_2201_;
}
else
{
uint8_t v___x_2202_; 
v___x_2202_ = l_Array_isEqvAux___at___00Std_Http_URI_instBEqQuery_spec__1___redArg(v_query_2189_, v_query_2194_, v___x_2199_);
lean_dec_ref(v_query_2194_);
lean_dec_ref(v_query_2189_);
if (v___x_2202_ == 0)
{
lean_dec(v_fragment_2195_);
lean_dec(v_fragment_2190_);
return v___x_2202_;
}
else
{
uint8_t v___x_2203_; 
v___x_2203_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_fragment_2190_, v_fragment_2195_);
lean_dec(v_fragment_2195_);
lean_dec(v_fragment_2190_);
return v___x_2203_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object* v_x_2204_, lean_object* v_x_2205_){
_start:
{
uint8_t v_res_2206_; lean_object* v_r_2207_; 
v_res_2206_ = l_Std_Http_instBEqURI_beq(v_x_2204_, v_x_2205_);
v_r_2207_ = lean_box(v_res_2206_);
return v_r_2207_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__2(lean_object* v___f_2212_, lean_object* v___f_2213_, lean_object* v_uri_2214_){
_start:
{
lean_object* v_scheme_2215_; lean_object* v_authority_2216_; lean_object* v_path_2217_; lean_object* v_query_2218_; lean_object* v_fragment_2219_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2256_; 
v_scheme_2215_ = lean_ctor_get(v_uri_2214_, 0);
lean_inc_ref(v_scheme_2215_);
v_authority_2216_ = lean_ctor_get(v_uri_2214_, 1);
lean_inc(v_authority_2216_);
v_path_2217_ = lean_ctor_get(v_uri_2214_, 2);
lean_inc_ref(v_path_2217_);
v_query_2218_ = lean_ctor_get(v_uri_2214_, 3);
lean_inc_ref(v_query_2218_);
v_fragment_2219_ = lean_ctor_get(v_uri_2214_, 4);
lean_inc(v_fragment_2219_);
lean_dec_ref(v_uri_2214_);
if (lean_obj_tag(v_authority_2216_) == 0)
{
lean_object* v___x_2267_; 
v___x_2267_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2256_ = v___x_2267_;
goto v___jp_2255_;
}
else
{
lean_object* v_val_2268_; lean_object* v_userInfo_2269_; lean_object* v_host_2270_; lean_object* v_port_2271_; lean_object* v___x_2272_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2291_; 
v_val_2268_ = lean_ctor_get(v_authority_2216_, 0);
lean_inc(v_val_2268_);
lean_dec_ref(v_authority_2216_);
v_userInfo_2269_ = lean_ctor_get(v_val_2268_, 0);
lean_inc(v_userInfo_2269_);
v_host_2270_ = lean_ctor_get(v_val_2268_, 1);
lean_inc_ref(v_host_2270_);
v_port_2271_ = lean_ctor_get(v_val_2268_, 2);
lean_inc(v_port_2271_);
lean_dec(v_val_2268_);
v___x_2272_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__1));
if (lean_obj_tag(v_userInfo_2269_) == 0)
{
lean_object* v___x_2301_; 
v___x_2301_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2291_ = v___x_2301_;
goto v___jp_2290_;
}
else
{
lean_object* v_val_2302_; lean_object* v_password_2303_; 
v_val_2302_ = lean_ctor_get(v_userInfo_2269_, 0);
lean_inc(v_val_2302_);
lean_dec_ref(v_userInfo_2269_);
v_password_2303_ = lean_ctor_get(v_val_2302_, 1);
if (lean_obj_tag(v_password_2303_) == 0)
{
lean_object* v_username_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v_username_2304_ = lean_ctor_get(v_val_2302_, 0);
lean_inc_ref(v_username_2304_);
lean_dec(v_val_2302_);
v___x_2305_ = lean_string_from_utf8_unchecked(v_username_2304_);
v___x_2306_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2307_ = lean_string_append(v___x_2305_, v___x_2306_);
v___y_2291_ = v___x_2307_;
goto v___jp_2290_;
}
else
{
lean_object* v_username_2308_; lean_object* v_val_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
lean_inc_ref(v_password_2303_);
v_username_2308_ = lean_ctor_get(v_val_2302_, 0);
lean_inc_ref(v_username_2308_);
lean_dec(v_val_2302_);
v_val_2309_ = lean_ctor_get(v_password_2303_, 0);
lean_inc(v_val_2309_);
lean_dec_ref(v_password_2303_);
v___x_2310_ = lean_string_from_utf8_unchecked(v_username_2308_);
v___x_2311_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2312_ = lean_string_append(v___x_2310_, v___x_2311_);
v___x_2313_ = lean_string_from_utf8_unchecked(v_val_2309_);
v___x_2314_ = lean_string_append(v___x_2312_, v___x_2313_);
lean_dec_ref(v___x_2313_);
v___x_2315_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2316_ = lean_string_append(v___x_2314_, v___x_2315_);
v___y_2291_ = v___x_2316_;
goto v___jp_2290_;
}
}
v___jp_2273_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = lean_string_append(v___y_2274_, v___y_2275_);
lean_dec_ref(v___y_2275_);
v___x_2278_ = lean_string_append(v___x_2277_, v___y_2276_);
lean_dec_ref(v___y_2276_);
v___x_2279_ = lean_string_append(v___x_2272_, v___x_2278_);
lean_dec_ref(v___x_2278_);
v___y_2256_ = v___x_2279_;
goto v___jp_2255_;
}
v___jp_2280_:
{
switch(lean_obj_tag(v_port_2271_))
{
case 0:
{
lean_object* v___x_2283_; 
v___x_2283_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2274_ = v___y_2281_;
v___y_2275_ = v___y_2282_;
v___y_2276_ = v___x_2283_;
goto v___jp_2273_;
}
case 1:
{
lean_object* v___x_2284_; 
v___x_2284_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_2274_ = v___y_2281_;
v___y_2275_ = v___y_2282_;
v___y_2276_ = v___x_2284_;
goto v___jp_2273_;
}
default: 
{
uint16_t v_port_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v_port_2285_ = lean_ctor_get_uint16(v_port_2271_, 0);
lean_dec_ref(v_port_2271_);
v___x_2286_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2287_ = lean_uint16_to_nat(v_port_2285_);
v___x_2288_ = l_Nat_reprFast(v___x_2287_);
v___x_2289_ = lean_string_append(v___x_2286_, v___x_2288_);
lean_dec_ref(v___x_2288_);
v___y_2274_ = v___y_2281_;
v___y_2275_ = v___y_2282_;
v___y_2276_ = v___x_2289_;
goto v___jp_2273_;
}
}
}
v___jp_2290_:
{
switch(lean_obj_tag(v_host_2270_))
{
case 0:
{
lean_object* v_name_2292_; 
v_name_2292_ = lean_ctor_get(v_host_2270_, 0);
lean_inc_ref(v_name_2292_);
lean_dec_ref(v_host_2270_);
v___y_2281_ = v___y_2291_;
v___y_2282_ = v_name_2292_;
goto v___jp_2280_;
}
case 1:
{
lean_object* v_ipv4_2293_; lean_object* v___x_2294_; 
v_ipv4_2293_ = lean_ctor_get(v_host_2270_, 0);
lean_inc_ref(v_ipv4_2293_);
lean_dec_ref(v_host_2270_);
v___x_2294_ = lean_uv_ntop_v4(v_ipv4_2293_);
lean_dec_ref(v_ipv4_2293_);
v___y_2281_ = v___y_2291_;
v___y_2282_ = v___x_2294_;
goto v___jp_2280_;
}
default: 
{
lean_object* v_ipv6_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v_ipv6_2295_ = lean_ctor_get(v_host_2270_, 0);
lean_inc_ref(v_ipv6_2295_);
lean_dec_ref(v_host_2270_);
v___x_2296_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_2297_ = lean_uv_ntop_v6(v_ipv6_2295_);
lean_dec_ref(v_ipv6_2295_);
v___x_2298_ = lean_string_append(v___x_2296_, v___x_2297_);
lean_dec_ref(v___x_2297_);
v___x_2299_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_2300_ = lean_string_append(v___x_2298_, v___x_2299_);
v___y_2281_ = v___y_2291_;
v___y_2282_ = v___x_2300_;
goto v___jp_2280_;
}
}
}
}
v___jp_2220_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2225_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2226_ = lean_string_append(v_scheme_2215_, v___x_2225_);
v___x_2227_ = lean_string_append(v___x_2226_, v___y_2221_);
lean_dec_ref(v___y_2221_);
v___x_2228_ = lean_string_append(v___x_2227_, v___y_2223_);
lean_dec_ref(v___y_2223_);
v___x_2229_ = lean_string_append(v___x_2228_, v___y_2222_);
lean_dec_ref(v___y_2222_);
v___x_2230_ = lean_string_append(v___x_2229_, v___y_2224_);
lean_dec_ref(v___y_2224_);
return v___x_2230_;
}
v___jp_2231_:
{
if (lean_obj_tag(v_fragment_2219_) == 0)
{
lean_object* v___x_2235_; 
v___x_2235_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2221_ = v___y_2232_;
v___y_2222_ = v___y_2234_;
v___y_2223_ = v___y_2233_;
v___y_2224_ = v___x_2235_;
goto v___jp_2220_;
}
else
{
lean_object* v_val_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v_val_2236_ = lean_ctor_get(v_fragment_2219_, 0);
lean_inc(v_val_2236_);
lean_dec_ref(v_fragment_2219_);
v___x_2237_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__0));
v___x_2238_ = l_Std_Http_URI_EncodedFragment_encode(v_val_2236_);
lean_dec(v_val_2236_);
v___x_2239_ = lean_string_from_utf8_unchecked(v___x_2238_);
v___x_2240_ = lean_string_append(v___x_2237_, v___x_2239_);
lean_dec_ref(v___x_2239_);
v___y_2221_ = v___y_2232_;
v___y_2222_ = v___y_2234_;
v___y_2223_ = v___y_2233_;
v___y_2224_ = v___x_2240_;
goto v___jp_2220_;
}
}
v___jp_2241_:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v___x_2244_ = lean_array_get_size(v_query_2218_);
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = lean_nat_dec_eq(v___x_2244_, v___x_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v_encodedParams_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2247_ = lean_array_to_list(v_query_2218_);
v___x_2248_ = lean_box(0);
v_encodedParams_2249_ = l_List_mapTR_loop___redArg(v___f_2212_, v___x_2247_, v___x_2248_);
v___x_2250_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2251_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2252_ = l_String_intercalate(v___x_2251_, v_encodedParams_2249_);
v___x_2253_ = lean_string_append(v___x_2250_, v___x_2252_);
lean_dec_ref(v___x_2252_);
v___y_2232_ = v___y_2242_;
v___y_2233_ = v___y_2243_;
v___y_2234_ = v___x_2253_;
goto v___jp_2231_;
}
else
{
lean_object* v___x_2254_; 
lean_dec_ref(v_query_2218_);
lean_dec_ref(v___f_2212_);
v___x_2254_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2232_ = v___y_2242_;
v___y_2233_ = v___y_2243_;
v___y_2234_ = v___x_2254_;
goto v___jp_2231_;
}
}
v___jp_2255_:
{
lean_object* v_segments_2257_; uint8_t v_absolute_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; size_t v_sz_2261_; size_t v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v_result_2265_; 
v_segments_2257_ = lean_ctor_get(v_path_2217_, 0);
lean_inc_ref(v_segments_2257_);
v_absolute_2258_ = lean_ctor_get_uint8(v_path_2217_, sizeof(void*)*1);
lean_dec_ref(v_path_2217_);
v___x_2259_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_2260_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_2261_ = lean_array_size(v_segments_2257_);
v___x_2262_ = ((size_t)0ULL);
v___x_2263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2260_, v___f_2213_, v_sz_2261_, v___x_2262_, v_segments_2257_);
v___x_2264_ = lean_array_to_list(v___x_2263_);
v_result_2265_ = l_String_intercalate(v___x_2259_, v___x_2264_);
if (v_absolute_2258_ == 0)
{
v___y_2242_ = v___y_2256_;
v___y_2243_ = v_result_2265_;
goto v___jp_2241_;
}
else
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_string_append(v___x_2259_, v_result_2265_);
lean_dec_ref(v_result_2265_);
v___y_2242_ = v___y_2256_;
v___y_2243_ = v___x_2266_;
goto v___jp_2241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x3f(lean_object* v_b_2336_, lean_object* v_scheme_2337_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Std_Http_URI_Scheme_ofString_x3f(v_scheme_2337_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v___x_2339_; 
lean_dec_ref(v_b_2336_);
v___x_2339_ = lean_box(0);
return v___x_2339_;
}
else
{
lean_object* v_userInfo_2340_; lean_object* v_host_2341_; lean_object* v_port_2342_; lean_object* v_pathSegments_2343_; lean_object* v_query_2344_; lean_object* v_fragment_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2360_; 
v_userInfo_2340_ = lean_ctor_get(v_b_2336_, 1);
v_host_2341_ = lean_ctor_get(v_b_2336_, 2);
v_port_2342_ = lean_ctor_get(v_b_2336_, 3);
v_pathSegments_2343_ = lean_ctor_get(v_b_2336_, 4);
v_query_2344_ = lean_ctor_get(v_b_2336_, 5);
v_fragment_2345_ = lean_ctor_get(v_b_2336_, 6);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_b_2336_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; 
v_unused_2361_ = lean_ctor_get(v_b_2336_, 0);
lean_dec(v_unused_2361_);
v___x_2347_ = v_b_2336_;
v_isShared_2348_ = v_isSharedCheck_2360_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_fragment_2345_);
lean_inc(v_query_2344_);
lean_inc(v_pathSegments_2343_);
lean_inc(v_port_2342_);
lean_inc(v_host_2341_);
lean_inc(v_userInfo_2340_);
lean_dec(v_b_2336_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2360_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
lean_inc_ref(v___x_2338_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 0, v___x_2338_);
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2338_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_userInfo_2340_);
lean_ctor_set(v_reuseFailAlloc_2359_, 2, v_host_2341_);
lean_ctor_set(v_reuseFailAlloc_2359_, 3, v_port_2342_);
lean_ctor_set(v_reuseFailAlloc_2359_, 4, v_pathSegments_2343_);
lean_ctor_set(v_reuseFailAlloc_2359_, 5, v_query_2344_);
lean_ctor_set(v_reuseFailAlloc_2359_, 6, v_fragment_2345_);
v___x_2350_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2357_ == 0)
{
lean_object* v_unused_2358_; 
v_unused_2358_ = lean_ctor_get(v___x_2338_, 0);
lean_dec(v_unused_2358_);
v___x_2352_ = v___x_2338_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_dec(v___x_2338_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2350_);
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(lean_object* v_msg_2362_){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = ((lean_object*)(l_Std_Http_URI_instInhabitedBuilder_default));
v___x_2364_ = lean_panic_fn_borrowed(v___x_2363_, v_msg_2362_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x21(lean_object* v_b_2366_, lean_object* v_scheme_2367_){
_start:
{
lean_object* v___x_2368_; 
lean_inc_ref(v_scheme_2367_);
v___x_2368_ = l_Std_Http_URI_Builder_setScheme_x3f(v_b_2366_, v_scheme_2367_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2369_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2370_ = ((lean_object*)(l_Std_Http_URI_Builder_setScheme_x21___closed__0));
v___x_2371_ = lean_unsigned_to_nat(677u);
v___x_2372_ = lean_unsigned_to_nat(14u);
v___x_2373_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_2374_ = l_String_quote(v_scheme_2367_);
v___x_2375_ = lean_string_append(v___x_2373_, v___x_2374_);
lean_dec_ref(v___x_2374_);
v___x_2376_ = l_mkPanicMessageWithDecl(v___x_2369_, v___x_2370_, v___x_2371_, v___x_2372_, v___x_2375_);
lean_dec_ref(v___x_2375_);
v___x_2377_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2376_);
return v___x_2377_;
}
else
{
lean_object* v_val_2378_; 
lean_dec_ref(v_scheme_2367_);
v_val_2378_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_val_2378_);
lean_dec_ref(v___x_2368_);
return v_val_2378_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo(lean_object* v_b_2379_, lean_object* v_username_2380_, lean_object* v_password_2381_){
_start:
{
lean_object* v_scheme_2382_; lean_object* v_host_2383_; lean_object* v_port_2384_; lean_object* v_pathSegments_2385_; lean_object* v_query_2386_; lean_object* v_fragment_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2410_; 
v_scheme_2382_ = lean_ctor_get(v_b_2379_, 0);
v_host_2383_ = lean_ctor_get(v_b_2379_, 2);
v_port_2384_ = lean_ctor_get(v_b_2379_, 3);
v_pathSegments_2385_ = lean_ctor_get(v_b_2379_, 4);
v_query_2386_ = lean_ctor_get(v_b_2379_, 5);
v_fragment_2387_ = lean_ctor_get(v_b_2379_, 6);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_b_2379_);
if (v_isSharedCheck_2410_ == 0)
{
lean_object* v_unused_2411_; 
v_unused_2411_ = lean_ctor_get(v_b_2379_, 1);
lean_dec(v_unused_2411_);
v___x_2389_ = v_b_2379_;
v_isShared_2390_ = v_isSharedCheck_2410_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_fragment_2387_);
lean_inc(v_query_2386_);
lean_inc(v_pathSegments_2385_);
lean_inc(v_port_2384_);
lean_inc(v_host_2383_);
lean_inc(v_scheme_2382_);
lean_dec(v_b_2379_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2410_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___y_2392_; lean_object* v___x_2397_; 
v___x_2397_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_2380_);
if (lean_obj_tag(v_password_2381_) == 0)
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = lean_box(0);
v___x_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___y_2392_ = v___x_2399_;
goto v___jp_2391_;
}
else
{
lean_object* v_val_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2409_; 
v_val_2400_ = lean_ctor_get(v_password_2381_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_password_2381_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2402_ = v_password_2381_;
v_isShared_2403_ = v_isSharedCheck_2409_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_val_2400_);
lean_dec(v_password_2381_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2409_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2406_; 
v___x_2404_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_2400_);
lean_dec(v_val_2400_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2404_);
v___x_2406_ = v___x_2402_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
lean_object* v___x_2407_; 
v___x_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2397_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___y_2392_ = v___x_2407_;
goto v___jp_2391_;
}
}
}
v___jp_2391_:
{
lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___y_2392_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 1, v___x_2393_);
v___x_2395_ = v___x_2389_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_scheme_2382_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v___x_2393_);
lean_ctor_set(v_reuseFailAlloc_2396_, 2, v_host_2383_);
lean_ctor_set(v_reuseFailAlloc_2396_, 3, v_port_2384_);
lean_ctor_set(v_reuseFailAlloc_2396_, 4, v_pathSegments_2385_);
lean_ctor_set(v_reuseFailAlloc_2396_, 5, v_query_2386_);
lean_ctor_set(v_reuseFailAlloc_2396_, 6, v_fragment_2387_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo___boxed(lean_object* v_b_2412_, lean_object* v_username_2413_, lean_object* v_password_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Std_Http_URI_Builder_setUserInfo(v_b_2412_, v_username_2413_, v_password_2414_);
lean_dec_ref(v_username_2413_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x3f(lean_object* v_b_2416_, lean_object* v_name_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Std_Http_URI_DomainName_ofString_x3f(v_name_2417_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v___x_2419_; 
lean_dec_ref(v_b_2416_);
v___x_2419_ = lean_box(0);
return v___x_2419_;
}
else
{
lean_object* v_val_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2443_; 
v_val_2420_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2422_ = v___x_2418_;
v_isShared_2423_ = v_isSharedCheck_2443_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_val_2420_);
lean_dec(v___x_2418_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2443_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v_scheme_2424_; lean_object* v_userInfo_2425_; lean_object* v_port_2426_; lean_object* v_pathSegments_2427_; lean_object* v_query_2428_; lean_object* v_fragment_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2441_; 
v_scheme_2424_ = lean_ctor_get(v_b_2416_, 0);
v_userInfo_2425_ = lean_ctor_get(v_b_2416_, 1);
v_port_2426_ = lean_ctor_get(v_b_2416_, 3);
v_pathSegments_2427_ = lean_ctor_get(v_b_2416_, 4);
v_query_2428_ = lean_ctor_get(v_b_2416_, 5);
v_fragment_2429_ = lean_ctor_get(v_b_2416_, 6);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_b_2416_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; 
v_unused_2442_ = lean_ctor_get(v_b_2416_, 2);
lean_dec(v_unused_2442_);
v___x_2431_ = v_b_2416_;
v_isShared_2432_ = v_isSharedCheck_2441_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_fragment_2429_);
lean_inc(v_query_2428_);
lean_inc(v_pathSegments_2427_);
lean_inc(v_port_2426_);
lean_inc(v_userInfo_2425_);
lean_inc(v_scheme_2424_);
lean_dec(v_b_2416_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2441_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2435_; 
v___x_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2433_, 0, v_val_2420_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2433_);
v___x_2435_ = v___x_2422_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
lean_object* v___x_2437_; 
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 2, v___x_2435_);
v___x_2437_ = v___x_2431_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_scheme_2424_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v_userInfo_2425_);
lean_ctor_set(v_reuseFailAlloc_2439_, 2, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2439_, 3, v_port_2426_);
lean_ctor_set(v_reuseFailAlloc_2439_, 4, v_pathSegments_2427_);
lean_ctor_set(v_reuseFailAlloc_2439_, 5, v_query_2428_);
lean_ctor_set(v_reuseFailAlloc_2439_, 6, v_fragment_2429_);
v___x_2437_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2438_; 
v___x_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
return v___x_2438_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x21(lean_object* v_b_2446_, lean_object* v_name_2447_){
_start:
{
lean_object* v___x_2448_; 
lean_inc_ref(v_name_2447_);
v___x_2448_ = l_Std_Http_URI_Builder_setHost_x3f(v_b_2446_, v_name_2447_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2449_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2450_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__0));
v___x_2451_ = lean_unsigned_to_nat(706u);
v___x_2452_ = lean_unsigned_to_nat(14u);
v___x_2453_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__1));
v___x_2454_ = l_String_quote(v_name_2447_);
v___x_2455_ = lean_string_append(v___x_2453_, v___x_2454_);
lean_dec_ref(v___x_2454_);
v___x_2456_ = l_mkPanicMessageWithDecl(v___x_2449_, v___x_2450_, v___x_2451_, v___x_2452_, v___x_2455_);
lean_dec_ref(v___x_2455_);
v___x_2457_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2456_);
return v___x_2457_;
}
else
{
lean_object* v_val_2458_; 
lean_dec_ref(v_name_2447_);
v_val_2458_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_val_2458_);
lean_dec_ref(v___x_2448_);
return v_val_2458_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv4(lean_object* v_b_2459_, lean_object* v_addr_2460_){
_start:
{
lean_object* v_scheme_2461_; lean_object* v_userInfo_2462_; lean_object* v_port_2463_; lean_object* v_pathSegments_2464_; lean_object* v_query_2465_; lean_object* v_fragment_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2475_; 
v_scheme_2461_ = lean_ctor_get(v_b_2459_, 0);
v_userInfo_2462_ = lean_ctor_get(v_b_2459_, 1);
v_port_2463_ = lean_ctor_get(v_b_2459_, 3);
v_pathSegments_2464_ = lean_ctor_get(v_b_2459_, 4);
v_query_2465_ = lean_ctor_get(v_b_2459_, 5);
v_fragment_2466_ = lean_ctor_get(v_b_2459_, 6);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_b_2459_);
if (v_isSharedCheck_2475_ == 0)
{
lean_object* v_unused_2476_; 
v_unused_2476_ = lean_ctor_get(v_b_2459_, 2);
lean_dec(v_unused_2476_);
v___x_2468_ = v_b_2459_;
v_isShared_2469_ = v_isSharedCheck_2475_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_fragment_2466_);
lean_inc(v_query_2465_);
lean_inc(v_pathSegments_2464_);
lean_inc(v_port_2463_);
lean_inc(v_userInfo_2462_);
lean_inc(v_scheme_2461_);
lean_dec(v_b_2459_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2475_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2470_, 0, v_addr_2460_);
v___x_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 2, v___x_2471_);
v___x_2473_ = v___x_2468_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_scheme_2461_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_userInfo_2462_);
lean_ctor_set(v_reuseFailAlloc_2474_, 2, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2474_, 3, v_port_2463_);
lean_ctor_set(v_reuseFailAlloc_2474_, 4, v_pathSegments_2464_);
lean_ctor_set(v_reuseFailAlloc_2474_, 5, v_query_2465_);
lean_ctor_set(v_reuseFailAlloc_2474_, 6, v_fragment_2466_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv6(lean_object* v_b_2477_, lean_object* v_addr_2478_){
_start:
{
lean_object* v_scheme_2479_; lean_object* v_userInfo_2480_; lean_object* v_port_2481_; lean_object* v_pathSegments_2482_; lean_object* v_query_2483_; lean_object* v_fragment_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2493_; 
v_scheme_2479_ = lean_ctor_get(v_b_2477_, 0);
v_userInfo_2480_ = lean_ctor_get(v_b_2477_, 1);
v_port_2481_ = lean_ctor_get(v_b_2477_, 3);
v_pathSegments_2482_ = lean_ctor_get(v_b_2477_, 4);
v_query_2483_ = lean_ctor_get(v_b_2477_, 5);
v_fragment_2484_ = lean_ctor_get(v_b_2477_, 6);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_b_2477_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; 
v_unused_2494_ = lean_ctor_get(v_b_2477_, 2);
lean_dec(v_unused_2494_);
v___x_2486_ = v_b_2477_;
v_isShared_2487_ = v_isSharedCheck_2493_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_fragment_2484_);
lean_inc(v_query_2483_);
lean_inc(v_pathSegments_2482_);
lean_inc(v_port_2481_);
lean_inc(v_userInfo_2480_);
lean_inc(v_scheme_2479_);
lean_dec(v_b_2477_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2493_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2488_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_addr_2478_);
v___x_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 2, v___x_2489_);
v___x_2491_ = v___x_2486_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_scheme_2479_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_userInfo_2480_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v_port_2481_);
lean_ctor_set(v_reuseFailAlloc_2492_, 4, v_pathSegments_2482_);
lean_ctor_set(v_reuseFailAlloc_2492_, 5, v_query_2483_);
lean_ctor_set(v_reuseFailAlloc_2492_, 6, v_fragment_2484_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort(lean_object* v_b_2495_, uint16_t v_port_2496_){
_start:
{
lean_object* v_scheme_2497_; lean_object* v_userInfo_2498_; lean_object* v_host_2499_; lean_object* v_pathSegments_2500_; lean_object* v_query_2501_; lean_object* v_fragment_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2510_; 
v_scheme_2497_ = lean_ctor_get(v_b_2495_, 0);
v_userInfo_2498_ = lean_ctor_get(v_b_2495_, 1);
v_host_2499_ = lean_ctor_get(v_b_2495_, 2);
v_pathSegments_2500_ = lean_ctor_get(v_b_2495_, 4);
v_query_2501_ = lean_ctor_get(v_b_2495_, 5);
v_fragment_2502_ = lean_ctor_get(v_b_2495_, 6);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_b_2495_);
if (v_isSharedCheck_2510_ == 0)
{
lean_object* v_unused_2511_; 
v_unused_2511_ = lean_ctor_get(v_b_2495_, 3);
lean_dec(v_unused_2511_);
v___x_2504_ = v_b_2495_;
v_isShared_2505_ = v_isSharedCheck_2510_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_fragment_2502_);
lean_inc(v_query_2501_);
lean_inc(v_pathSegments_2500_);
lean_inc(v_host_2499_);
lean_inc(v_userInfo_2498_);
lean_inc(v_scheme_2497_);
lean_dec(v_b_2495_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2510_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2506_ = lean_alloc_ctor(2, 0, 2);
lean_ctor_set_uint16(v___x_2506_, 0, v_port_2496_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 3, v___x_2506_);
v___x_2508_ = v___x_2504_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_scheme_2497_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_userInfo_2498_);
lean_ctor_set(v_reuseFailAlloc_2509_, 2, v_host_2499_);
lean_ctor_set(v_reuseFailAlloc_2509_, 3, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2509_, 4, v_pathSegments_2500_);
lean_ctor_set(v_reuseFailAlloc_2509_, 5, v_query_2501_);
lean_ctor_set(v_reuseFailAlloc_2509_, 6, v_fragment_2502_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort___boxed(lean_object* v_b_2512_, lean_object* v_port_2513_){
_start:
{
uint16_t v_port_boxed_2514_; lean_object* v_res_2515_; 
v_port_boxed_2514_ = lean_unbox(v_port_2513_);
v_res_2515_ = l_Std_Http_URI_Builder_setPort(v_b_2512_, v_port_boxed_2514_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPath(lean_object* v_b_2516_, lean_object* v_segments_2517_){
_start:
{
lean_object* v_scheme_2518_; lean_object* v_userInfo_2519_; lean_object* v_host_2520_; lean_object* v_port_2521_; lean_object* v_query_2522_; lean_object* v_fragment_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
v_scheme_2518_ = lean_ctor_get(v_b_2516_, 0);
v_userInfo_2519_ = lean_ctor_get(v_b_2516_, 1);
v_host_2520_ = lean_ctor_get(v_b_2516_, 2);
v_port_2521_ = lean_ctor_get(v_b_2516_, 3);
v_query_2522_ = lean_ctor_get(v_b_2516_, 5);
v_fragment_2523_ = lean_ctor_get(v_b_2516_, 6);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_b_2516_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v_b_2516_, 4);
lean_dec(v_unused_2531_);
v___x_2525_ = v_b_2516_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_fragment_2523_);
lean_inc(v_query_2522_);
lean_inc(v_port_2521_);
lean_inc(v_host_2520_);
lean_inc(v_userInfo_2519_);
lean_inc(v_scheme_2518_);
lean_dec(v_b_2516_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 4, v_segments_2517_);
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_scheme_2518_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_userInfo_2519_);
lean_ctor_set(v_reuseFailAlloc_2529_, 2, v_host_2520_);
lean_ctor_set(v_reuseFailAlloc_2529_, 3, v_port_2521_);
lean_ctor_set(v_reuseFailAlloc_2529_, 4, v_segments_2517_);
lean_ctor_set(v_reuseFailAlloc_2529_, 5, v_query_2522_);
lean_ctor_set(v_reuseFailAlloc_2529_, 6, v_fragment_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_appendPathSegment(lean_object* v_b_2532_, lean_object* v_segment_2533_){
_start:
{
lean_object* v_scheme_2534_; lean_object* v_userInfo_2535_; lean_object* v_host_2536_; lean_object* v_port_2537_; lean_object* v_pathSegments_2538_; lean_object* v_query_2539_; lean_object* v_fragment_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2548_; 
v_scheme_2534_ = lean_ctor_get(v_b_2532_, 0);
v_userInfo_2535_ = lean_ctor_get(v_b_2532_, 1);
v_host_2536_ = lean_ctor_get(v_b_2532_, 2);
v_port_2537_ = lean_ctor_get(v_b_2532_, 3);
v_pathSegments_2538_ = lean_ctor_get(v_b_2532_, 4);
v_query_2539_ = lean_ctor_get(v_b_2532_, 5);
v_fragment_2540_ = lean_ctor_get(v_b_2532_, 6);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_b_2532_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2542_ = v_b_2532_;
v_isShared_2543_ = v_isSharedCheck_2548_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_fragment_2540_);
lean_inc(v_query_2539_);
lean_inc(v_pathSegments_2538_);
lean_inc(v_port_2537_);
lean_inc(v_host_2536_);
lean_inc(v_userInfo_2535_);
lean_inc(v_scheme_2534_);
lean_dec(v_b_2532_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2548_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2544_; lean_object* v___x_2546_; 
v___x_2544_ = lean_array_push(v_pathSegments_2538_, v_segment_2533_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 4, v___x_2544_);
v___x_2546_ = v___x_2542_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_scheme_2534_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_userInfo_2535_);
lean_ctor_set(v_reuseFailAlloc_2547_, 2, v_host_2536_);
lean_ctor_set(v_reuseFailAlloc_2547_, 3, v_port_2537_);
lean_ctor_set(v_reuseFailAlloc_2547_, 4, v___x_2544_);
lean_ctor_set(v_reuseFailAlloc_2547_, 5, v_query_2539_);
lean_ctor_set(v_reuseFailAlloc_2547_, 6, v_fragment_2540_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryParam(lean_object* v_b_2549_, lean_object* v_key_2550_, lean_object* v_value_2551_){
_start:
{
lean_object* v_scheme_2552_; lean_object* v_userInfo_2553_; lean_object* v_host_2554_; lean_object* v_port_2555_; lean_object* v_pathSegments_2556_; lean_object* v_query_2557_; lean_object* v_fragment_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2568_; 
v_scheme_2552_ = lean_ctor_get(v_b_2549_, 0);
v_userInfo_2553_ = lean_ctor_get(v_b_2549_, 1);
v_host_2554_ = lean_ctor_get(v_b_2549_, 2);
v_port_2555_ = lean_ctor_get(v_b_2549_, 3);
v_pathSegments_2556_ = lean_ctor_get(v_b_2549_, 4);
v_query_2557_ = lean_ctor_get(v_b_2549_, 5);
v_fragment_2558_ = lean_ctor_get(v_b_2549_, 6);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_b_2549_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2560_ = v_b_2549_;
v_isShared_2561_ = v_isSharedCheck_2568_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_fragment_2558_);
lean_inc(v_query_2557_);
lean_inc(v_pathSegments_2556_);
lean_inc(v_port_2555_);
lean_inc(v_host_2554_);
lean_inc(v_userInfo_2553_);
lean_inc(v_scheme_2552_);
lean_dec(v_b_2549_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2568_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2566_; 
v___x_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2562_, 0, v_value_2551_);
v___x_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2563_, 0, v_key_2550_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = lean_array_push(v_query_2557_, v___x_2563_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 5, v___x_2564_);
v___x_2566_ = v___x_2560_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_scheme_2552_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_userInfo_2553_);
lean_ctor_set(v_reuseFailAlloc_2567_, 2, v_host_2554_);
lean_ctor_set(v_reuseFailAlloc_2567_, 3, v_port_2555_);
lean_ctor_set(v_reuseFailAlloc_2567_, 4, v_pathSegments_2556_);
lean_ctor_set(v_reuseFailAlloc_2567_, 5, v___x_2564_);
lean_ctor_set(v_reuseFailAlloc_2567_, 6, v_fragment_2558_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryFlag(lean_object* v_b_2569_, lean_object* v_key_2570_){
_start:
{
lean_object* v_scheme_2571_; lean_object* v_userInfo_2572_; lean_object* v_host_2573_; lean_object* v_port_2574_; lean_object* v_pathSegments_2575_; lean_object* v_query_2576_; lean_object* v_fragment_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2587_; 
v_scheme_2571_ = lean_ctor_get(v_b_2569_, 0);
v_userInfo_2572_ = lean_ctor_get(v_b_2569_, 1);
v_host_2573_ = lean_ctor_get(v_b_2569_, 2);
v_port_2574_ = lean_ctor_get(v_b_2569_, 3);
v_pathSegments_2575_ = lean_ctor_get(v_b_2569_, 4);
v_query_2576_ = lean_ctor_get(v_b_2569_, 5);
v_fragment_2577_ = lean_ctor_get(v_b_2569_, 6);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_b_2569_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2579_ = v_b_2569_;
v_isShared_2580_ = v_isSharedCheck_2587_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_fragment_2577_);
lean_inc(v_query_2576_);
lean_inc(v_pathSegments_2575_);
lean_inc(v_port_2574_);
lean_inc(v_host_2573_);
lean_inc(v_userInfo_2572_);
lean_inc(v_scheme_2571_);
lean_dec(v_b_2569_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2587_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2585_; 
v___x_2581_ = lean_box(0);
v___x_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2582_, 0, v_key_2570_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = lean_array_push(v_query_2576_, v___x_2582_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 5, v___x_2583_);
v___x_2585_ = v___x_2579_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_scheme_2571_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_userInfo_2572_);
lean_ctor_set(v_reuseFailAlloc_2586_, 2, v_host_2573_);
lean_ctor_set(v_reuseFailAlloc_2586_, 3, v_port_2574_);
lean_ctor_set(v_reuseFailAlloc_2586_, 4, v_pathSegments_2575_);
lean_ctor_set(v_reuseFailAlloc_2586_, 5, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2586_, 6, v_fragment_2577_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setQuery(lean_object* v_b_2588_, lean_object* v_query_2589_){
_start:
{
lean_object* v_scheme_2590_; lean_object* v_userInfo_2591_; lean_object* v_host_2592_; lean_object* v_port_2593_; lean_object* v_pathSegments_2594_; lean_object* v_fragment_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
v_scheme_2590_ = lean_ctor_get(v_b_2588_, 0);
v_userInfo_2591_ = lean_ctor_get(v_b_2588_, 1);
v_host_2592_ = lean_ctor_get(v_b_2588_, 2);
v_port_2593_ = lean_ctor_get(v_b_2588_, 3);
v_pathSegments_2594_ = lean_ctor_get(v_b_2588_, 4);
v_fragment_2595_ = lean_ctor_get(v_b_2588_, 6);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_b_2588_);
if (v_isSharedCheck_2602_ == 0)
{
lean_object* v_unused_2603_; 
v_unused_2603_ = lean_ctor_get(v_b_2588_, 5);
lean_dec(v_unused_2603_);
v___x_2597_ = v_b_2588_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_fragment_2595_);
lean_inc(v_pathSegments_2594_);
lean_inc(v_port_2593_);
lean_inc(v_host_2592_);
lean_inc(v_userInfo_2591_);
lean_inc(v_scheme_2590_);
lean_dec(v_b_2588_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 5, v_query_2589_);
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_scheme_2590_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_userInfo_2591_);
lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_host_2592_);
lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_port_2593_);
lean_ctor_set(v_reuseFailAlloc_2601_, 4, v_pathSegments_2594_);
lean_ctor_set(v_reuseFailAlloc_2601_, 5, v_query_2589_);
lean_ctor_set(v_reuseFailAlloc_2601_, 6, v_fragment_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setFragment(lean_object* v_b_2604_, lean_object* v_fragment_2605_){
_start:
{
lean_object* v_scheme_2606_; lean_object* v_userInfo_2607_; lean_object* v_host_2608_; lean_object* v_port_2609_; lean_object* v_pathSegments_2610_; lean_object* v_query_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2619_; 
v_scheme_2606_ = lean_ctor_get(v_b_2604_, 0);
v_userInfo_2607_ = lean_ctor_get(v_b_2604_, 1);
v_host_2608_ = lean_ctor_get(v_b_2604_, 2);
v_port_2609_ = lean_ctor_get(v_b_2604_, 3);
v_pathSegments_2610_ = lean_ctor_get(v_b_2604_, 4);
v_query_2611_ = lean_ctor_get(v_b_2604_, 5);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_b_2604_);
if (v_isSharedCheck_2619_ == 0)
{
lean_object* v_unused_2620_; 
v_unused_2620_ = lean_ctor_get(v_b_2604_, 6);
lean_dec(v_unused_2620_);
v___x_2613_ = v_b_2604_;
v_isShared_2614_ = v_isSharedCheck_2619_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_query_2611_);
lean_inc(v_pathSegments_2610_);
lean_inc(v_port_2609_);
lean_inc(v_host_2608_);
lean_inc(v_userInfo_2607_);
lean_inc(v_scheme_2606_);
lean_dec(v_b_2604_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2619_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2615_; lean_object* v___x_2617_; 
v___x_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2615_, 0, v_fragment_2605_);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 6, v___x_2615_);
v___x_2617_ = v___x_2613_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_scheme_2606_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_userInfo_2607_);
lean_ctor_set(v_reuseFailAlloc_2618_, 2, v_host_2608_);
lean_ctor_set(v_reuseFailAlloc_2618_, 3, v_port_2609_);
lean_ctor_set(v_reuseFailAlloc_2618_, 4, v_pathSegments_2610_);
lean_ctor_set(v_reuseFailAlloc_2618_, 5, v_query_2611_);
lean_ctor_set(v_reuseFailAlloc_2618_, 6, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(size_t v_sz_2621_, size_t v_i_2622_, lean_object* v_bs_2623_){
_start:
{
uint8_t v___x_2624_; 
v___x_2624_ = lean_usize_dec_lt(v_i_2622_, v_sz_2621_);
if (v___x_2624_ == 0)
{
return v_bs_2623_;
}
else
{
lean_object* v_v_2625_; lean_object* v___x_2626_; lean_object* v_bs_x27_2627_; lean_object* v___x_2628_; size_t v___x_2629_; size_t v___x_2630_; lean_object* v___x_2631_; 
v_v_2625_ = lean_array_uget(v_bs_2623_, v_i_2622_);
v___x_2626_ = lean_unsigned_to_nat(0u);
v_bs_x27_2627_ = lean_array_uset(v_bs_2623_, v_i_2622_, v___x_2626_);
v___x_2628_ = l_Std_Http_URI_EncodedSegment_encode(v_v_2625_);
lean_dec(v_v_2625_);
v___x_2629_ = ((size_t)1ULL);
v___x_2630_ = lean_usize_add(v_i_2622_, v___x_2629_);
v___x_2631_ = lean_array_uset(v_bs_x27_2627_, v_i_2622_, v___x_2628_);
v_i_2622_ = v___x_2630_;
v_bs_2623_ = v___x_2631_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0___boxed(lean_object* v_sz_2633_, lean_object* v_i_2634_, lean_object* v_bs_2635_){
_start:
{
size_t v_sz_boxed_2636_; size_t v_i_boxed_2637_; lean_object* v_res_2638_; 
v_sz_boxed_2636_ = lean_unbox_usize(v_sz_2633_);
lean_dec(v_sz_2633_);
v_i_boxed_2637_ = lean_unbox_usize(v_i_2634_);
lean_dec(v_i_2634_);
v_res_2638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_boxed_2636_, v_i_boxed_2637_, v_bs_2635_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(size_t v_sz_2639_, size_t v_i_2640_, lean_object* v_bs_2641_){
_start:
{
uint8_t v___x_2642_; 
v___x_2642_ = lean_usize_dec_lt(v_i_2640_, v_sz_2639_);
if (v___x_2642_ == 0)
{
return v_bs_2641_;
}
else
{
lean_object* v_v_2643_; lean_object* v_fst_2644_; lean_object* v_snd_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2674_; 
v_v_2643_ = lean_array_uget(v_bs_2641_, v_i_2640_);
v_fst_2644_ = lean_ctor_get(v_v_2643_, 0);
v_snd_2645_ = lean_ctor_get(v_v_2643_, 1);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_v_2643_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2647_ = v_v_2643_;
v_isShared_2648_ = v_isSharedCheck_2674_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_snd_2645_);
lean_inc(v_fst_2644_);
lean_dec(v_v_2643_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2674_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v_bs_x27_2650_; lean_object* v___y_2652_; lean_object* v___x_2657_; 
v___x_2649_ = lean_unsigned_to_nat(0u);
v_bs_x27_2650_ = lean_array_uset(v_bs_2641_, v_i_2640_, v___x_2649_);
v___x_2657_ = l_Std_Http_URI_EncodedQueryParam_encode(v_fst_2644_);
lean_dec(v_fst_2644_);
if (lean_obj_tag(v_snd_2645_) == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2658_ = lean_box(0);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 1, v___x_2658_);
lean_ctor_set(v___x_2647_, 0, v___x_2657_);
v___x_2660_ = v___x_2647_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2661_, 1, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
v___y_2652_ = v___x_2660_;
goto v___jp_2651_;
}
}
else
{
lean_object* v_val_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2673_; 
v_val_2662_ = lean_ctor_get(v_snd_2645_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_snd_2645_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2664_ = v_snd_2645_;
v_isShared_2665_ = v_isSharedCheck_2673_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_val_2662_);
lean_dec(v_snd_2645_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2673_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2666_; lean_object* v___x_2668_; 
v___x_2666_ = l_Std_Http_URI_EncodedQueryParam_encode(v_val_2662_);
lean_dec(v_val_2662_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v___x_2666_);
v___x_2668_ = v___x_2664_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2666_);
v___x_2668_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2670_; 
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 1, v___x_2668_);
lean_ctor_set(v___x_2647_, 0, v___x_2657_);
v___x_2670_ = v___x_2647_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
v___y_2652_ = v___x_2670_;
goto v___jp_2651_;
}
}
}
}
v___jp_2651_:
{
size_t v___x_2653_; size_t v___x_2654_; lean_object* v___x_2655_; 
v___x_2653_ = ((size_t)1ULL);
v___x_2654_ = lean_usize_add(v_i_2640_, v___x_2653_);
v___x_2655_ = lean_array_uset(v_bs_x27_2650_, v_i_2640_, v___y_2652_);
v_i_2640_ = v___x_2654_;
v_bs_2641_ = v___x_2655_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1___boxed(lean_object* v_sz_2675_, lean_object* v_i_2676_, lean_object* v_bs_2677_){
_start:
{
size_t v_sz_boxed_2678_; size_t v_i_boxed_2679_; lean_object* v_res_2680_; 
v_sz_boxed_2678_ = lean_unbox_usize(v_sz_2675_);
lean_dec(v_sz_2675_);
v_i_boxed_2679_ = lean_unbox_usize(v_i_2676_);
lean_dec(v_i_2676_);
v_res_2680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_boxed_2678_, v_i_boxed_2679_, v_bs_2677_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_build(lean_object* v_b_2681_){
_start:
{
lean_object* v___y_2683_; lean_object* v___y_2684_; uint8_t v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v_scheme_2698_; lean_object* v_userInfo_2699_; lean_object* v_host_2700_; lean_object* v_port_2701_; lean_object* v_pathSegments_2702_; lean_object* v_query_2703_; lean_object* v_fragment_2704_; lean_object* v___y_2706_; 
v_scheme_2698_ = lean_ctor_get(v_b_2681_, 0);
lean_inc(v_scheme_2698_);
v_userInfo_2699_ = lean_ctor_get(v_b_2681_, 1);
lean_inc(v_userInfo_2699_);
v_host_2700_ = lean_ctor_get(v_b_2681_, 2);
lean_inc(v_host_2700_);
v_port_2701_ = lean_ctor_get(v_b_2681_, 3);
lean_inc(v_port_2701_);
v_pathSegments_2702_ = lean_ctor_get(v_b_2681_, 4);
lean_inc_ref(v_pathSegments_2702_);
v_query_2703_ = lean_ctor_get(v_b_2681_, 5);
lean_inc_ref(v_query_2703_);
v_fragment_2704_ = lean_ctor_get(v_b_2681_, 6);
lean_inc(v_fragment_2704_);
lean_dec_ref(v_b_2681_);
if (lean_obj_tag(v_scheme_2698_) == 0)
{
lean_object* v___x_2719_; 
v___x_2719_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___y_2706_ = v___x_2719_;
goto v___jp_2705_;
}
else
{
lean_object* v_val_2720_; 
v_val_2720_ = lean_ctor_get(v_scheme_2698_, 0);
lean_inc(v_val_2720_);
lean_dec_ref(v_scheme_2698_);
v___y_2706_ = v_val_2720_;
goto v___jp_2705_;
}
v___jp_2682_:
{
size_t v_sz_2689_; size_t v___x_2690_; lean_object* v___x_2691_; lean_object* v_path_2692_; size_t v_sz_2693_; lean_object* v_query_2694_; lean_object* v___x_2695_; lean_object* v_query_2696_; lean_object* v___x_2697_; 
v_sz_2689_ = lean_array_size(v___y_2683_);
v___x_2690_ = ((size_t)0ULL);
v___x_2691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_2689_, v___x_2690_, v___y_2683_);
v_path_2692_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_path_2692_, 0, v___x_2691_);
lean_ctor_set_uint8(v_path_2692_, sizeof(void*)*1, v___y_2685_);
v_sz_2693_ = lean_array_size(v___y_2687_);
v_query_2694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_2693_, v___x_2690_, v___y_2687_);
v___x_2695_ = lean_array_to_list(v_query_2694_);
v_query_2696_ = lean_array_mk(v___x_2695_);
v___x_2697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2697_, 0, v___y_2686_);
lean_ctor_set(v___x_2697_, 1, v___y_2688_);
lean_ctor_set(v___x_2697_, 2, v_path_2692_);
lean_ctor_set(v___x_2697_, 3, v_query_2696_);
lean_ctor_set(v___x_2697_, 4, v___y_2684_);
return v___x_2697_;
}
v___jp_2705_:
{
if (lean_obj_tag(v_host_2700_) == 0)
{
uint8_t v___x_2707_; lean_object* v___x_2708_; 
lean_dec(v_port_2701_);
lean_dec(v_userInfo_2699_);
v___x_2707_ = 1;
v___x_2708_ = lean_box(0);
v___y_2683_ = v_pathSegments_2702_;
v___y_2684_ = v_fragment_2704_;
v___y_2685_ = v___x_2707_;
v___y_2686_ = v___y_2706_;
v___y_2687_ = v_query_2703_;
v___y_2688_ = v___x_2708_;
goto v___jp_2682_;
}
else
{
lean_object* v_val_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2718_; 
v_val_2709_ = lean_ctor_get(v_host_2700_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_host_2700_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2711_ = v_host_2700_;
v_isShared_2712_ = v_isSharedCheck_2718_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_val_2709_);
lean_dec(v_host_2700_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2718_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
uint8_t v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
v___x_2713_ = 1;
v___x_2714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2714_, 0, v_userInfo_2699_);
lean_ctor_set(v___x_2714_, 1, v_val_2709_);
lean_ctor_set(v___x_2714_, 2, v_port_2701_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2714_);
v___x_2716_ = v___x_2711_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
v___y_2683_ = v_pathSegments_2702_;
v___y_2684_ = v_fragment_2704_;
v___y_2685_ = v___x_2713_;
v___y_2686_ = v___y_2706_;
v___y_2687_ = v_query_2703_;
v___y_2688_ = v___x_2716_;
goto v___jp_2682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withScheme_x21(lean_object* v_uri_2721_, lean_object* v_scheme_2722_){
_start:
{
lean_object* v_authority_2723_; lean_object* v_path_2724_; lean_object* v_query_2725_; lean_object* v_fragment_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2734_; 
v_authority_2723_ = lean_ctor_get(v_uri_2721_, 1);
v_path_2724_ = lean_ctor_get(v_uri_2721_, 2);
v_query_2725_ = lean_ctor_get(v_uri_2721_, 3);
v_fragment_2726_ = lean_ctor_get(v_uri_2721_, 4);
v_isSharedCheck_2734_ = !lean_is_exclusive(v_uri_2721_);
if (v_isSharedCheck_2734_ == 0)
{
lean_object* v_unused_2735_; 
v_unused_2735_ = lean_ctor_get(v_uri_2721_, 0);
lean_dec(v_unused_2735_);
v___x_2728_ = v_uri_2721_;
v_isShared_2729_ = v_isSharedCheck_2734_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_fragment_2726_);
lean_inc(v_query_2725_);
lean_inc(v_path_2724_);
lean_inc(v_authority_2723_);
lean_dec(v_uri_2721_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2734_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2730_ = l_Std_Http_URI_Scheme_ofString_x21(v_scheme_2722_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2730_);
v___x_2732_ = v___x_2728_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v___x_2730_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_authority_2723_);
lean_ctor_set(v_reuseFailAlloc_2733_, 2, v_path_2724_);
lean_ctor_set(v_reuseFailAlloc_2733_, 3, v_query_2725_);
lean_ctor_set(v_reuseFailAlloc_2733_, 4, v_fragment_2726_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_withAuthority(lean_object* v_uri_2736_, lean_object* v_authority_2737_){
_start:
{
lean_object* v_scheme_2738_; lean_object* v_path_2739_; lean_object* v_query_2740_; lean_object* v_fragment_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
v_scheme_2738_ = lean_ctor_get(v_uri_2736_, 0);
v_path_2739_ = lean_ctor_get(v_uri_2736_, 2);
v_query_2740_ = lean_ctor_get(v_uri_2736_, 3);
v_fragment_2741_ = lean_ctor_get(v_uri_2736_, 4);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_uri_2736_);
if (v_isSharedCheck_2748_ == 0)
{
lean_object* v_unused_2749_; 
v_unused_2749_ = lean_ctor_get(v_uri_2736_, 1);
lean_dec(v_unused_2749_);
v___x_2743_ = v_uri_2736_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_fragment_2741_);
lean_inc(v_query_2740_);
lean_inc(v_path_2739_);
lean_inc(v_scheme_2738_);
lean_dec(v_uri_2736_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 1, v_authority_2737_);
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_scheme_2738_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_authority_2737_);
lean_ctor_set(v_reuseFailAlloc_2747_, 2, v_path_2739_);
lean_ctor_set(v_reuseFailAlloc_2747_, 3, v_query_2740_);
lean_ctor_set(v_reuseFailAlloc_2747_, 4, v_fragment_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withPath(lean_object* v_uri_2750_, lean_object* v_path_2751_){
_start:
{
lean_object* v_scheme_2752_; lean_object* v_authority_2753_; lean_object* v_query_2754_; lean_object* v_fragment_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
v_scheme_2752_ = lean_ctor_get(v_uri_2750_, 0);
v_authority_2753_ = lean_ctor_get(v_uri_2750_, 1);
v_query_2754_ = lean_ctor_get(v_uri_2750_, 3);
v_fragment_2755_ = lean_ctor_get(v_uri_2750_, 4);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_uri_2750_);
if (v_isSharedCheck_2762_ == 0)
{
lean_object* v_unused_2763_; 
v_unused_2763_ = lean_ctor_get(v_uri_2750_, 2);
lean_dec(v_unused_2763_);
v___x_2757_ = v_uri_2750_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_fragment_2755_);
lean_inc(v_query_2754_);
lean_inc(v_authority_2753_);
lean_inc(v_scheme_2752_);
lean_dec(v_uri_2750_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 2, v_path_2751_);
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_scheme_2752_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_authority_2753_);
lean_ctor_set(v_reuseFailAlloc_2761_, 2, v_path_2751_);
lean_ctor_set(v_reuseFailAlloc_2761_, 3, v_query_2754_);
lean_ctor_set(v_reuseFailAlloc_2761_, 4, v_fragment_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withQuery(lean_object* v_uri_2764_, lean_object* v_query_2765_){
_start:
{
lean_object* v_scheme_2766_; lean_object* v_authority_2767_; lean_object* v_path_2768_; lean_object* v_fragment_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
v_scheme_2766_ = lean_ctor_get(v_uri_2764_, 0);
v_authority_2767_ = lean_ctor_get(v_uri_2764_, 1);
v_path_2768_ = lean_ctor_get(v_uri_2764_, 2);
v_fragment_2769_ = lean_ctor_get(v_uri_2764_, 4);
v_isSharedCheck_2776_ = !lean_is_exclusive(v_uri_2764_);
if (v_isSharedCheck_2776_ == 0)
{
lean_object* v_unused_2777_; 
v_unused_2777_ = lean_ctor_get(v_uri_2764_, 3);
lean_dec(v_unused_2777_);
v___x_2771_ = v_uri_2764_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_fragment_2769_);
lean_inc(v_path_2768_);
lean_inc(v_authority_2767_);
lean_inc(v_scheme_2766_);
lean_dec(v_uri_2764_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 3, v_query_2765_);
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_scheme_2766_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_authority_2767_);
lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_path_2768_);
lean_ctor_set(v_reuseFailAlloc_2775_, 3, v_query_2765_);
lean_ctor_set(v_reuseFailAlloc_2775_, 4, v_fragment_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withFragment(lean_object* v_uri_2778_, lean_object* v_fragment_2779_){
_start:
{
lean_object* v_scheme_2780_; lean_object* v_authority_2781_; lean_object* v_path_2782_; lean_object* v_query_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
v_scheme_2780_ = lean_ctor_get(v_uri_2778_, 0);
v_authority_2781_ = lean_ctor_get(v_uri_2778_, 1);
v_path_2782_ = lean_ctor_get(v_uri_2778_, 2);
v_query_2783_ = lean_ctor_get(v_uri_2778_, 3);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_uri_2778_);
if (v_isSharedCheck_2790_ == 0)
{
lean_object* v_unused_2791_; 
v_unused_2791_ = lean_ctor_get(v_uri_2778_, 4);
lean_dec(v_unused_2791_);
v___x_2785_ = v_uri_2778_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_query_2783_);
lean_inc(v_path_2782_);
lean_inc(v_authority_2781_);
lean_inc(v_scheme_2780_);
lean_dec(v_uri_2778_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 4, v_fragment_2779_);
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_scheme_2780_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_authority_2781_);
lean_ctor_set(v_reuseFailAlloc_2789_, 2, v_path_2782_);
lean_ctor_set(v_reuseFailAlloc_2789_, 3, v_query_2783_);
lean_ctor_set(v_reuseFailAlloc_2789_, 4, v_fragment_2779_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_normalize(lean_object* v_uri_2792_){
_start:
{
lean_object* v_scheme_2793_; lean_object* v_authority_2794_; lean_object* v_path_2795_; lean_object* v_query_2796_; lean_object* v_fragment_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2805_; 
v_scheme_2793_ = lean_ctor_get(v_uri_2792_, 0);
v_authority_2794_ = lean_ctor_get(v_uri_2792_, 1);
v_path_2795_ = lean_ctor_get(v_uri_2792_, 2);
v_query_2796_ = lean_ctor_get(v_uri_2792_, 3);
v_fragment_2797_ = lean_ctor_get(v_uri_2792_, 4);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_uri_2792_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2799_ = v_uri_2792_;
v_isShared_2800_ = v_isSharedCheck_2805_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_fragment_2797_);
lean_inc(v_query_2796_);
lean_inc(v_path_2795_);
lean_inc(v_authority_2794_);
lean_inc(v_scheme_2793_);
lean_dec(v_uri_2792_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2805_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2803_; 
v___x_2801_ = l_Std_Http_URI_Path_normalize(v_path_2795_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 2, v___x_2801_);
v___x_2803_ = v___x_2799_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_scheme_2793_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v_authority_2794_);
lean_ctor_set(v_reuseFailAlloc_2804_, 2, v___x_2801_);
lean_ctor_set(v_reuseFailAlloc_2804_, 3, v_query_2796_);
lean_ctor_set(v_reuseFailAlloc_2804_, 4, v_fragment_2797_);
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
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx(lean_object* v_x_2806_){
_start:
{
switch(lean_obj_tag(v_x_2806_))
{
case 0:
{
lean_object* v___x_2807_; 
v___x_2807_ = lean_unsigned_to_nat(0u);
return v___x_2807_;
}
case 1:
{
lean_object* v___x_2808_; 
v___x_2808_ = lean_unsigned_to_nat(1u);
return v___x_2808_;
}
case 2:
{
lean_object* v___x_2809_; 
v___x_2809_ = lean_unsigned_to_nat(2u);
return v___x_2809_;
}
default: 
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_unsigned_to_nat(3u);
return v___x_2810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___boxed(lean_object* v_x_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Std_Http_RequestTarget_ctorIdx(v_x_2811_);
lean_dec(v_x_2811_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___redArg(lean_object* v_t_2813_, lean_object* v_k_2814_){
_start:
{
switch(lean_obj_tag(v_t_2813_))
{
case 0:
{
lean_object* v_path_2815_; lean_object* v_query_2816_; lean_object* v___x_2817_; 
v_path_2815_ = lean_ctor_get(v_t_2813_, 0);
lean_inc_ref(v_path_2815_);
v_query_2816_ = lean_ctor_get(v_t_2813_, 1);
lean_inc(v_query_2816_);
lean_dec_ref(v_t_2813_);
v___x_2817_ = lean_apply_2(v_k_2814_, v_path_2815_, v_query_2816_);
return v___x_2817_;
}
case 3:
{
return v_k_2814_;
}
default: 
{
lean_object* v_uri_2818_; lean_object* v___x_2819_; 
v_uri_2818_ = lean_ctor_get(v_t_2813_, 0);
lean_inc_ref(v_uri_2818_);
lean_dec(v_t_2813_);
v___x_2819_ = lean_apply_1(v_k_2814_, v_uri_2818_);
return v___x_2819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim(lean_object* v_motive_2820_, lean_object* v_ctorIdx_2821_, lean_object* v_t_2822_, lean_object* v_h_2823_, lean_object* v_k_2824_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2822_, v_k_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___boxed(lean_object* v_motive_2826_, lean_object* v_ctorIdx_2827_, lean_object* v_t_2828_, lean_object* v_h_2829_, lean_object* v_k_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Std_Http_RequestTarget_ctorElim(v_motive_2826_, v_ctorIdx_2827_, v_t_2828_, v_h_2829_, v_k_2830_);
lean_dec(v_ctorIdx_2827_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim___redArg(lean_object* v_t_2832_, lean_object* v_originForm_2833_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2832_, v_originForm_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim(lean_object* v_motive_2835_, lean_object* v_t_2836_, lean_object* v_h_2837_, lean_object* v_originForm_2838_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2836_, v_originForm_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim___redArg(lean_object* v_t_2840_, lean_object* v_absoluteForm_2841_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2840_, v_absoluteForm_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim(lean_object* v_motive_2843_, lean_object* v_t_2844_, lean_object* v_h_2845_, lean_object* v_absoluteForm_2846_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2844_, v_absoluteForm_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim___redArg(lean_object* v_t_2848_, lean_object* v_authorityForm_2849_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2848_, v_authorityForm_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim(lean_object* v_motive_2851_, lean_object* v_t_2852_, lean_object* v_h_2853_, lean_object* v_authorityForm_2854_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2852_, v_authorityForm_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim___redArg(lean_object* v_t_2856_, lean_object* v_asteriskForm_2857_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2856_, v_asteriskForm_2857_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim(lean_object* v_motive_2859_, lean_object* v_t_2860_, lean_object* v_h_2861_, lean_object* v_asteriskForm_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2860_, v_asteriskForm_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0(lean_object* v_x_2869_, lean_object* v_x_2870_){
_start:
{
if (lean_obj_tag(v_x_2869_) == 0)
{
lean_object* v___x_2871_; 
v___x_2871_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2871_;
}
else
{
lean_object* v_val_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v_val_2872_ = lean_ctor_get(v_x_2869_, 0);
lean_inc(v_val_2872_);
lean_dec_ref(v_x_2869_);
v___x_2873_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2874_ = l_Array_repr___at___00Std_Http_URI_instReprQuery_spec__0(v_val_2872_);
v___x_2875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2873_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
v___x_2876_ = l_Repr_addAppParen(v___x_2875_, v_x_2870_);
return v___x_2876_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0___boxed(lean_object* v_x_2877_, lean_object* v_x_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0(v_x_2877_, v_x_2878_);
lean_dec(v_x_2878_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object* v_x_2901_, lean_object* v_prec_2902_){
_start:
{
lean_object* v___y_2904_; 
switch(lean_obj_tag(v_x_2901_))
{
case 0:
{
lean_object* v_path_2910_; lean_object* v_query_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2935_; 
v_path_2910_ = lean_ctor_get(v_x_2901_, 0);
v_query_2911_ = lean_ctor_get(v_x_2901_, 1);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_x_2901_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2913_ = v_x_2901_;
v_isShared_2914_ = v_isSharedCheck_2935_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_query_2911_);
lean_inc(v_path_2910_);
lean_dec(v_x_2901_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2935_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___y_2916_; lean_object* v___x_2931_; uint8_t v___x_2932_; 
v___x_2931_ = lean_unsigned_to_nat(1024u);
v___x_2932_ = lean_nat_dec_le(v___x_2931_, v_prec_2902_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; 
v___x_2933_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_2916_ = v___x_2933_;
goto v___jp_2915_;
}
else
{
lean_object* v___x_2934_; 
v___x_2934_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_2916_ = v___x_2934_;
goto v___jp_2915_;
}
v___jp_2915_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2917_ = lean_box(1);
v___x_2918_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__4));
v___x_2919_ = lean_unsigned_to_nat(1024u);
v___x_2920_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_2910_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set_tag(v___x_2913_, 5);
lean_ctor_set(v___x_2913_, 1, v___x_2920_);
lean_ctor_set(v___x_2913_, 0, v___x_2918_);
v___x_2922_ = v___x_2913_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
lean_ctor_set(v___x_2923_, 1, v___x_2917_);
v___x_2924_ = l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0(v_query_2911_, v___x_2919_);
v___x_2925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2923_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
lean_inc(v___y_2916_);
v___x_2926_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___y_2916_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
v___x_2927_ = 0;
v___x_2928_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2928_, 0, v___x_2926_);
lean_ctor_set_uint8(v___x_2928_, sizeof(void*)*1, v___x_2927_);
v___x_2929_ = l_Repr_addAppParen(v___x_2928_, v_prec_2902_);
return v___x_2929_;
}
}
}
}
case 1:
{
lean_object* v_uri_2936_; lean_object* v___y_2938_; lean_object* v___x_2946_; uint8_t v___x_2947_; 
v_uri_2936_ = lean_ctor_get(v_x_2901_, 0);
lean_inc_ref(v_uri_2936_);
lean_dec_ref(v_x_2901_);
v___x_2946_ = lean_unsigned_to_nat(1024u);
v___x_2947_ = lean_nat_dec_le(v___x_2946_, v_prec_2902_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; 
v___x_2948_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_2938_ = v___x_2948_;
goto v___jp_2937_;
}
else
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_2938_ = v___x_2949_;
goto v___jp_2937_;
}
v___jp_2937_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; uint8_t v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2939_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__7));
v___x_2940_ = l_Std_Http_instReprURI_repr___redArg(v_uri_2936_);
v___x_2941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2939_);
lean_ctor_set(v___x_2941_, 1, v___x_2940_);
lean_inc(v___y_2938_);
v___x_2942_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___y_2938_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___x_2943_ = 0;
v___x_2944_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2944_, 0, v___x_2942_);
lean_ctor_set_uint8(v___x_2944_, sizeof(void*)*1, v___x_2943_);
v___x_2945_ = l_Repr_addAppParen(v___x_2944_, v_prec_2902_);
return v___x_2945_;
}
}
case 2:
{
lean_object* v_authority_2950_; lean_object* v___y_2952_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v_authority_2950_ = lean_ctor_get(v_x_2901_, 0);
lean_inc_ref(v_authority_2950_);
lean_dec_ref(v_x_2901_);
v___x_2960_ = lean_unsigned_to_nat(1024u);
v___x_2961_ = lean_nat_dec_le(v___x_2960_, v_prec_2902_);
if (v___x_2961_ == 0)
{
lean_object* v___x_2962_; 
v___x_2962_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_2952_ = v___x_2962_;
goto v___jp_2951_;
}
else
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_2952_ = v___x_2963_;
goto v___jp_2951_;
}
v___jp_2951_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; uint8_t v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2953_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__10));
v___x_2954_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_authority_2950_);
v___x_2955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2953_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
lean_inc(v___y_2952_);
v___x_2956_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___y_2952_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
v___x_2957_ = 0;
v___x_2958_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2958_, 0, v___x_2956_);
lean_ctor_set_uint8(v___x_2958_, sizeof(void*)*1, v___x_2957_);
v___x_2959_ = l_Repr_addAppParen(v___x_2958_, v_prec_2902_);
return v___x_2959_;
}
}
default: 
{
lean_object* v___x_2964_; uint8_t v___x_2965_; 
v___x_2964_ = lean_unsigned_to_nat(1024u);
v___x_2965_ = lean_nat_dec_le(v___x_2964_, v_prec_2902_);
if (v___x_2965_ == 0)
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_2904_ = v___x_2966_;
goto v___jp_2903_;
}
else
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_2904_ = v___x_2967_;
goto v___jp_2903_;
}
}
}
v___jp_2903_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2905_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__1));
lean_inc(v___y_2904_);
v___x_2906_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___y_2904_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = 0;
v___x_2908_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2908_, 0, v___x_2906_);
lean_ctor_set_uint8(v___x_2908_, sizeof(void*)*1, v___x_2907_);
v___x_2909_ = l_Repr_addAppParen(v___x_2908_, v_prec_2902_);
return v___x_2909_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr___boxed(lean_object* v_x_2968_, lean_object* v_prec_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Std_Http_instReprRequestTarget_repr(v_x_2968_, v_prec_2969_);
lean_dec(v_prec_2969_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path(lean_object* v_x_2978_){
_start:
{
switch(lean_obj_tag(v_x_2978_))
{
case 0:
{
lean_object* v_path_2979_; 
v_path_2979_ = lean_ctor_get(v_x_2978_, 0);
lean_inc_ref(v_path_2979_);
return v_path_2979_;
}
case 1:
{
lean_object* v_uri_2980_; lean_object* v_path_2981_; 
v_uri_2980_ = lean_ctor_get(v_x_2978_, 0);
v_path_2981_ = lean_ctor_get(v_uri_2980_, 2);
lean_inc_ref(v_path_2981_);
return v_path_2981_;
}
default: 
{
lean_object* v___x_2982_; 
v___x_2982_ = ((lean_object*)(l_Std_Http_RequestTarget_path___closed__1));
return v___x_2982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path___boxed(lean_object* v_x_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Std_Http_RequestTarget_path(v_x_2983_);
lean_dec(v_x_2983_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query(lean_object* v_x_2985_){
_start:
{
switch(lean_obj_tag(v_x_2985_))
{
case 0:
{
lean_object* v_query_2986_; 
v_query_2986_ = lean_ctor_get(v_x_2985_, 1);
if (lean_obj_tag(v_query_2986_) == 0)
{
lean_object* v___x_2987_; 
v___x_2987_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_2987_;
}
else
{
lean_object* v_val_2988_; 
v_val_2988_ = lean_ctor_get(v_query_2986_, 0);
lean_inc(v_val_2988_);
return v_val_2988_;
}
}
case 1:
{
lean_object* v_uri_2989_; lean_object* v_query_2990_; 
v_uri_2989_ = lean_ctor_get(v_x_2985_, 0);
v_query_2990_ = lean_ctor_get(v_uri_2989_, 3);
lean_inc_ref(v_query_2990_);
return v_query_2990_;
}
default: 
{
lean_object* v___x_2991_; 
v___x_2991_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_2991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query___boxed(lean_object* v_x_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Std_Http_RequestTarget_query(v_x_2992_);
lean_dec(v_x_2992_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authority_x3f(lean_object* v_x_2994_){
_start:
{
switch(lean_obj_tag(v_x_2994_))
{
case 2:
{
lean_object* v_authority_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
v_authority_2995_ = lean_ctor_get(v_x_2994_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v_x_2994_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v_x_2994_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_authority_2995_);
lean_dec(v_x_2994_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
lean_ctor_set_tag(v___x_2997_, 1);
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_authority_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
case 1:
{
lean_object* v_uri_3003_; lean_object* v_authority_3004_; 
v_uri_3003_ = lean_ctor_get(v_x_2994_, 0);
lean_inc_ref(v_uri_3003_);
lean_dec_ref(v_x_2994_);
v_authority_3004_ = lean_ctor_get(v_uri_3003_, 1);
lean_inc(v_authority_3004_);
lean_dec_ref(v_uri_3003_);
return v_authority_3004_;
}
default: 
{
lean_object* v___x_3005_; 
lean_dec(v_x_2994_);
v___x_3005_ = lean_box(0);
return v___x_3005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__4(lean_object* v___f_3007_, lean_object* v___f_3008_, lean_object* v___f_3009_, lean_object* v___f_3010_, lean_object* v_x_3011_){
_start:
{
lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; 
switch(lean_obj_tag(v_x_3011_))
{
case 0:
{
lean_object* v_path_3018_; lean_object* v_query_3019_; lean_object* v___y_3021_; lean_object* v_segments_3034_; uint8_t v_absolute_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; size_t v_sz_3038_; size_t v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v_result_3042_; 
lean_dec_ref(v___f_3010_);
lean_dec_ref(v___f_3009_);
v_path_3018_ = lean_ctor_get(v_x_3011_, 0);
lean_inc_ref(v_path_3018_);
v_query_3019_ = lean_ctor_get(v_x_3011_, 1);
lean_inc(v_query_3019_);
lean_dec_ref(v_x_3011_);
v_segments_3034_ = lean_ctor_get(v_path_3018_, 0);
lean_inc_ref(v_segments_3034_);
v_absolute_3035_ = lean_ctor_get_uint8(v_path_3018_, sizeof(void*)*1);
lean_dec_ref(v_path_3018_);
v___x_3036_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3037_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3038_ = lean_array_size(v_segments_3034_);
v___x_3039_ = ((size_t)0ULL);
v___x_3040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3037_, v___f_3008_, v_sz_3038_, v___x_3039_, v_segments_3034_);
v___x_3041_ = lean_array_to_list(v___x_3040_);
v_result_3042_ = l_String_intercalate(v___x_3036_, v___x_3041_);
if (v_absolute_3035_ == 0)
{
v___y_3021_ = v_result_3042_;
goto v___jp_3020_;
}
else
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_string_append(v___x_3036_, v_result_3042_);
lean_dec_ref(v_result_3042_);
v___y_3021_ = v___x_3043_;
goto v___jp_3020_;
}
v___jp_3020_:
{
if (lean_obj_tag(v_query_3019_) == 0)
{
lean_dec_ref(v___f_3007_);
return v___y_3021_;
}
else
{
lean_object* v_val_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; 
v_val_3022_ = lean_ctor_get(v_query_3019_, 0);
lean_inc(v_val_3022_);
lean_dec_ref(v_query_3019_);
v___x_3023_ = lean_array_get_size(v_val_3022_);
v___x_3024_ = lean_unsigned_to_nat(0u);
v___x_3025_ = lean_nat_dec_eq(v___x_3023_, v___x_3024_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v_encodedParams_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3026_ = lean_array_to_list(v_val_3022_);
v___x_3027_ = lean_box(0);
v_encodedParams_3028_ = l_List_mapTR_loop___redArg(v___f_3007_, v___x_3026_, v___x_3027_);
v___x_3029_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_3030_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_3031_ = l_String_intercalate(v___x_3030_, v_encodedParams_3028_);
v___x_3032_ = lean_string_append(v___x_3029_, v___x_3031_);
lean_dec_ref(v___x_3031_);
v___x_3033_ = lean_string_append(v___y_3021_, v___x_3032_);
lean_dec_ref(v___x_3032_);
return v___x_3033_;
}
else
{
lean_dec(v_val_3022_);
lean_dec_ref(v___f_3007_);
return v___y_3021_;
}
}
}
}
case 1:
{
lean_object* v_uri_3044_; lean_object* v_scheme_3045_; lean_object* v_authority_3046_; lean_object* v_path_3047_; lean_object* v_query_3048_; lean_object* v_fragment_3049_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3086_; 
lean_dec_ref(v___f_3008_);
lean_dec_ref(v___f_3007_);
v_uri_3044_ = lean_ctor_get(v_x_3011_, 0);
lean_inc_ref(v_uri_3044_);
lean_dec_ref(v_x_3011_);
v_scheme_3045_ = lean_ctor_get(v_uri_3044_, 0);
lean_inc_ref(v_scheme_3045_);
v_authority_3046_ = lean_ctor_get(v_uri_3044_, 1);
lean_inc(v_authority_3046_);
v_path_3047_ = lean_ctor_get(v_uri_3044_, 2);
lean_inc_ref(v_path_3047_);
v_query_3048_ = lean_ctor_get(v_uri_3044_, 3);
lean_inc_ref(v_query_3048_);
v_fragment_3049_ = lean_ctor_get(v_uri_3044_, 4);
lean_inc(v_fragment_3049_);
lean_dec_ref(v_uri_3044_);
if (lean_obj_tag(v_authority_3046_) == 0)
{
lean_object* v___x_3097_; 
v___x_3097_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3086_ = v___x_3097_;
goto v___jp_3085_;
}
else
{
lean_object* v_val_3098_; lean_object* v_userInfo_3099_; lean_object* v_host_3100_; lean_object* v_port_3101_; lean_object* v___x_3102_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3121_; 
v_val_3098_ = lean_ctor_get(v_authority_3046_, 0);
lean_inc(v_val_3098_);
lean_dec_ref(v_authority_3046_);
v_userInfo_3099_ = lean_ctor_get(v_val_3098_, 0);
lean_inc(v_userInfo_3099_);
v_host_3100_ = lean_ctor_get(v_val_3098_, 1);
lean_inc_ref(v_host_3100_);
v_port_3101_ = lean_ctor_get(v_val_3098_, 2);
lean_inc(v_port_3101_);
lean_dec(v_val_3098_);
v___x_3102_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__1));
if (lean_obj_tag(v_userInfo_3099_) == 0)
{
lean_object* v___x_3131_; 
v___x_3131_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3121_ = v___x_3131_;
goto v___jp_3120_;
}
else
{
lean_object* v_val_3132_; lean_object* v_password_3133_; 
v_val_3132_ = lean_ctor_get(v_userInfo_3099_, 0);
lean_inc(v_val_3132_);
lean_dec_ref(v_userInfo_3099_);
v_password_3133_ = lean_ctor_get(v_val_3132_, 1);
if (lean_obj_tag(v_password_3133_) == 0)
{
lean_object* v_username_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v_username_3134_ = lean_ctor_get(v_val_3132_, 0);
lean_inc_ref(v_username_3134_);
lean_dec(v_val_3132_);
v___x_3135_ = lean_string_from_utf8_unchecked(v_username_3134_);
v___x_3136_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3137_ = lean_string_append(v___x_3135_, v___x_3136_);
v___y_3121_ = v___x_3137_;
goto v___jp_3120_;
}
else
{
lean_object* v_username_3138_; lean_object* v_val_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
lean_inc_ref(v_password_3133_);
v_username_3138_ = lean_ctor_get(v_val_3132_, 0);
lean_inc_ref(v_username_3138_);
lean_dec(v_val_3132_);
v_val_3139_ = lean_ctor_get(v_password_3133_, 0);
lean_inc(v_val_3139_);
lean_dec_ref(v_password_3133_);
v___x_3140_ = lean_string_from_utf8_unchecked(v_username_3138_);
v___x_3141_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3142_ = lean_string_append(v___x_3140_, v___x_3141_);
v___x_3143_ = lean_string_from_utf8_unchecked(v_val_3139_);
v___x_3144_ = lean_string_append(v___x_3142_, v___x_3143_);
lean_dec_ref(v___x_3143_);
v___x_3145_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3146_ = lean_string_append(v___x_3144_, v___x_3145_);
v___y_3121_ = v___x_3146_;
goto v___jp_3120_;
}
}
v___jp_3103_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3107_ = lean_string_append(v___y_3104_, v___y_3105_);
lean_dec_ref(v___y_3105_);
v___x_3108_ = lean_string_append(v___x_3107_, v___y_3106_);
lean_dec_ref(v___y_3106_);
v___x_3109_ = lean_string_append(v___x_3102_, v___x_3108_);
lean_dec_ref(v___x_3108_);
v___y_3086_ = v___x_3109_;
goto v___jp_3085_;
}
v___jp_3110_:
{
switch(lean_obj_tag(v_port_3101_))
{
case 0:
{
lean_object* v___x_3113_; 
v___x_3113_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3104_ = v___y_3111_;
v___y_3105_ = v___y_3112_;
v___y_3106_ = v___x_3113_;
goto v___jp_3103_;
}
case 1:
{
lean_object* v___x_3114_; 
v___x_3114_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3104_ = v___y_3111_;
v___y_3105_ = v___y_3112_;
v___y_3106_ = v___x_3114_;
goto v___jp_3103_;
}
default: 
{
uint16_t v_port_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v_port_3115_ = lean_ctor_get_uint16(v_port_3101_, 0);
lean_dec_ref(v_port_3101_);
v___x_3116_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3117_ = lean_uint16_to_nat(v_port_3115_);
v___x_3118_ = l_Nat_reprFast(v___x_3117_);
v___x_3119_ = lean_string_append(v___x_3116_, v___x_3118_);
lean_dec_ref(v___x_3118_);
v___y_3104_ = v___y_3111_;
v___y_3105_ = v___y_3112_;
v___y_3106_ = v___x_3119_;
goto v___jp_3103_;
}
}
}
v___jp_3120_:
{
switch(lean_obj_tag(v_host_3100_))
{
case 0:
{
lean_object* v_name_3122_; 
v_name_3122_ = lean_ctor_get(v_host_3100_, 0);
lean_inc_ref(v_name_3122_);
lean_dec_ref(v_host_3100_);
v___y_3111_ = v___y_3121_;
v___y_3112_ = v_name_3122_;
goto v___jp_3110_;
}
case 1:
{
lean_object* v_ipv4_3123_; lean_object* v___x_3124_; 
v_ipv4_3123_ = lean_ctor_get(v_host_3100_, 0);
lean_inc_ref(v_ipv4_3123_);
lean_dec_ref(v_host_3100_);
v___x_3124_ = lean_uv_ntop_v4(v_ipv4_3123_);
lean_dec_ref(v_ipv4_3123_);
v___y_3111_ = v___y_3121_;
v___y_3112_ = v___x_3124_;
goto v___jp_3110_;
}
default: 
{
lean_object* v_ipv6_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v_ipv6_3125_ = lean_ctor_get(v_host_3100_, 0);
lean_inc_ref(v_ipv6_3125_);
lean_dec_ref(v_host_3100_);
v___x_3126_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3127_ = lean_uv_ntop_v6(v_ipv6_3125_);
lean_dec_ref(v_ipv6_3125_);
v___x_3128_ = lean_string_append(v___x_3126_, v___x_3127_);
lean_dec_ref(v___x_3127_);
v___x_3129_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3130_ = lean_string_append(v___x_3128_, v___x_3129_);
v___y_3111_ = v___y_3121_;
v___y_3112_ = v___x_3130_;
goto v___jp_3110_;
}
}
}
}
v___jp_3050_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3055_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3056_ = lean_string_append(v_scheme_3045_, v___x_3055_);
v___x_3057_ = lean_string_append(v___x_3056_, v___y_3051_);
lean_dec_ref(v___y_3051_);
v___x_3058_ = lean_string_append(v___x_3057_, v___y_3052_);
lean_dec_ref(v___y_3052_);
v___x_3059_ = lean_string_append(v___x_3058_, v___y_3053_);
lean_dec_ref(v___y_3053_);
v___x_3060_ = lean_string_append(v___x_3059_, v___y_3054_);
lean_dec_ref(v___y_3054_);
return v___x_3060_;
}
v___jp_3061_:
{
if (lean_obj_tag(v_fragment_3049_) == 0)
{
lean_object* v___x_3065_; 
v___x_3065_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3051_ = v___y_3062_;
v___y_3052_ = v___y_3063_;
v___y_3053_ = v___y_3064_;
v___y_3054_ = v___x_3065_;
goto v___jp_3050_;
}
else
{
lean_object* v_val_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v_val_3066_ = lean_ctor_get(v_fragment_3049_, 0);
lean_inc(v_val_3066_);
lean_dec_ref(v_fragment_3049_);
v___x_3067_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__0));
v___x_3068_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3066_);
lean_dec(v_val_3066_);
v___x_3069_ = lean_string_from_utf8_unchecked(v___x_3068_);
v___x_3070_ = lean_string_append(v___x_3067_, v___x_3069_);
lean_dec_ref(v___x_3069_);
v___y_3051_ = v___y_3062_;
v___y_3052_ = v___y_3063_;
v___y_3053_ = v___y_3064_;
v___y_3054_ = v___x_3070_;
goto v___jp_3050_;
}
}
v___jp_3071_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; uint8_t v___x_3076_; 
v___x_3074_ = lean_array_get_size(v_query_3048_);
v___x_3075_ = lean_unsigned_to_nat(0u);
v___x_3076_ = lean_nat_dec_eq(v___x_3074_, v___x_3075_);
if (v___x_3076_ == 0)
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v_encodedParams_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3077_ = lean_array_to_list(v_query_3048_);
v___x_3078_ = lean_box(0);
v_encodedParams_3079_ = l_List_mapTR_loop___redArg(v___f_3009_, v___x_3077_, v___x_3078_);
v___x_3080_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_3081_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_3082_ = l_String_intercalate(v___x_3081_, v_encodedParams_3079_);
v___x_3083_ = lean_string_append(v___x_3080_, v___x_3082_);
lean_dec_ref(v___x_3082_);
v___y_3062_ = v___y_3072_;
v___y_3063_ = v___y_3073_;
v___y_3064_ = v___x_3083_;
goto v___jp_3061_;
}
else
{
lean_object* v___x_3084_; 
lean_dec_ref(v_query_3048_);
lean_dec_ref(v___f_3009_);
v___x_3084_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3062_ = v___y_3072_;
v___y_3063_ = v___y_3073_;
v___y_3064_ = v___x_3084_;
goto v___jp_3061_;
}
}
v___jp_3085_:
{
lean_object* v_segments_3087_; uint8_t v_absolute_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; size_t v_sz_3091_; size_t v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v_result_3095_; 
v_segments_3087_ = lean_ctor_get(v_path_3047_, 0);
lean_inc_ref(v_segments_3087_);
v_absolute_3088_ = lean_ctor_get_uint8(v_path_3047_, sizeof(void*)*1);
lean_dec_ref(v_path_3047_);
v___x_3089_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3090_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3091_ = lean_array_size(v_segments_3087_);
v___x_3092_ = ((size_t)0ULL);
v___x_3093_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3090_, v___f_3010_, v_sz_3091_, v___x_3092_, v_segments_3087_);
v___x_3094_ = lean_array_to_list(v___x_3093_);
v_result_3095_ = l_String_intercalate(v___x_3089_, v___x_3094_);
if (v_absolute_3088_ == 0)
{
v___y_3072_ = v___y_3086_;
v___y_3073_ = v_result_3095_;
goto v___jp_3071_;
}
else
{
lean_object* v___x_3096_; 
v___x_3096_ = lean_string_append(v___x_3089_, v_result_3095_);
lean_dec_ref(v_result_3095_);
v___y_3072_ = v___y_3086_;
v___y_3073_ = v___x_3096_;
goto v___jp_3071_;
}
}
}
case 2:
{
lean_object* v_authority_3147_; lean_object* v_userInfo_3148_; lean_object* v_host_3149_; lean_object* v_port_3150_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3162_; 
lean_dec_ref(v___f_3010_);
lean_dec_ref(v___f_3009_);
lean_dec_ref(v___f_3008_);
lean_dec_ref(v___f_3007_);
v_authority_3147_ = lean_ctor_get(v_x_3011_, 0);
lean_inc_ref(v_authority_3147_);
lean_dec_ref(v_x_3011_);
v_userInfo_3148_ = lean_ctor_get(v_authority_3147_, 0);
lean_inc(v_userInfo_3148_);
v_host_3149_ = lean_ctor_get(v_authority_3147_, 1);
lean_inc_ref(v_host_3149_);
v_port_3150_ = lean_ctor_get(v_authority_3147_, 2);
lean_inc(v_port_3150_);
lean_dec_ref(v_authority_3147_);
if (lean_obj_tag(v_userInfo_3148_) == 0)
{
lean_object* v___x_3172_; 
v___x_3172_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3162_ = v___x_3172_;
goto v___jp_3161_;
}
else
{
lean_object* v_val_3173_; lean_object* v_password_3174_; 
v_val_3173_ = lean_ctor_get(v_userInfo_3148_, 0);
lean_inc(v_val_3173_);
lean_dec_ref(v_userInfo_3148_);
v_password_3174_ = lean_ctor_get(v_val_3173_, 1);
if (lean_obj_tag(v_password_3174_) == 0)
{
lean_object* v_username_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v_username_3175_ = lean_ctor_get(v_val_3173_, 0);
lean_inc_ref(v_username_3175_);
lean_dec(v_val_3173_);
v___x_3176_ = lean_string_from_utf8_unchecked(v_username_3175_);
v___x_3177_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3178_ = lean_string_append(v___x_3176_, v___x_3177_);
v___y_3162_ = v___x_3178_;
goto v___jp_3161_;
}
else
{
lean_object* v_username_3179_; lean_object* v_val_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_inc_ref(v_password_3174_);
v_username_3179_ = lean_ctor_get(v_val_3173_, 0);
lean_inc_ref(v_username_3179_);
lean_dec(v_val_3173_);
v_val_3180_ = lean_ctor_get(v_password_3174_, 0);
lean_inc(v_val_3180_);
lean_dec_ref(v_password_3174_);
v___x_3181_ = lean_string_from_utf8_unchecked(v_username_3179_);
v___x_3182_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3183_ = lean_string_append(v___x_3181_, v___x_3182_);
v___x_3184_ = lean_string_from_utf8_unchecked(v_val_3180_);
v___x_3185_ = lean_string_append(v___x_3183_, v___x_3184_);
lean_dec_ref(v___x_3184_);
v___x_3186_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3187_ = lean_string_append(v___x_3185_, v___x_3186_);
v___y_3162_ = v___x_3187_;
goto v___jp_3161_;
}
}
v___jp_3151_:
{
switch(lean_obj_tag(v_port_3150_))
{
case 0:
{
lean_object* v___x_3154_; 
v___x_3154_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3013_ = v___y_3152_;
v___y_3014_ = v___y_3153_;
v___y_3015_ = v___x_3154_;
goto v___jp_3012_;
}
case 1:
{
lean_object* v___x_3155_; 
v___x_3155_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3013_ = v___y_3152_;
v___y_3014_ = v___y_3153_;
v___y_3015_ = v___x_3155_;
goto v___jp_3012_;
}
default: 
{
uint16_t v_port_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v_port_3156_ = lean_ctor_get_uint16(v_port_3150_, 0);
lean_dec_ref(v_port_3150_);
v___x_3157_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3158_ = lean_uint16_to_nat(v_port_3156_);
v___x_3159_ = l_Nat_reprFast(v___x_3158_);
v___x_3160_ = lean_string_append(v___x_3157_, v___x_3159_);
lean_dec_ref(v___x_3159_);
v___y_3013_ = v___y_3152_;
v___y_3014_ = v___y_3153_;
v___y_3015_ = v___x_3160_;
goto v___jp_3012_;
}
}
}
v___jp_3161_:
{
switch(lean_obj_tag(v_host_3149_))
{
case 0:
{
lean_object* v_name_3163_; 
v_name_3163_ = lean_ctor_get(v_host_3149_, 0);
lean_inc_ref(v_name_3163_);
lean_dec_ref(v_host_3149_);
v___y_3152_ = v___y_3162_;
v___y_3153_ = v_name_3163_;
goto v___jp_3151_;
}
case 1:
{
lean_object* v_ipv4_3164_; lean_object* v___x_3165_; 
v_ipv4_3164_ = lean_ctor_get(v_host_3149_, 0);
lean_inc_ref(v_ipv4_3164_);
lean_dec_ref(v_host_3149_);
v___x_3165_ = lean_uv_ntop_v4(v_ipv4_3164_);
lean_dec_ref(v_ipv4_3164_);
v___y_3152_ = v___y_3162_;
v___y_3153_ = v___x_3165_;
goto v___jp_3151_;
}
default: 
{
lean_object* v_ipv6_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v_ipv6_3166_ = lean_ctor_get(v_host_3149_, 0);
lean_inc_ref(v_ipv6_3166_);
lean_dec_ref(v_host_3149_);
v___x_3167_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3168_ = lean_uv_ntop_v6(v_ipv6_3166_);
lean_dec_ref(v_ipv6_3166_);
v___x_3169_ = lean_string_append(v___x_3167_, v___x_3168_);
lean_dec_ref(v___x_3168_);
v___x_3170_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3171_ = lean_string_append(v___x_3169_, v___x_3170_);
v___y_3152_ = v___y_3162_;
v___y_3153_ = v___x_3171_;
goto v___jp_3151_;
}
}
}
}
default: 
{
lean_object* v___x_3188_; 
lean_dec_ref(v___f_3010_);
lean_dec_ref(v___f_3009_);
lean_dec_ref(v___f_3008_);
lean_dec_ref(v___f_3007_);
v___x_3188_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__4___closed__0));
return v___x_3188_;
}
}
v___jp_3012_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = lean_string_append(v___y_3013_, v___y_3014_);
lean_dec_ref(v___y_3014_);
v___x_3017_ = lean_string_append(v___x_3016_, v___y_3015_);
lean_dec_ref(v___y_3015_);
return v___x_3017_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__4(lean_object* v___f_3193_, lean_object* v___f_3194_, lean_object* v___f_3195_, lean_object* v___f_3196_, lean_object* v_buffer_3197_, lean_object* v_target_3198_){
_start:
{
lean_object* v___y_3200_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; 
switch(lean_obj_tag(v_target_3198_))
{
case 0:
{
lean_object* v_path_3220_; lean_object* v_query_3221_; lean_object* v___y_3223_; lean_object* v_segments_3236_; uint8_t v_absolute_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; size_t v_sz_3240_; size_t v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v_result_3244_; 
lean_dec_ref(v___f_3196_);
lean_dec_ref(v___f_3195_);
v_path_3220_ = lean_ctor_get(v_target_3198_, 0);
lean_inc_ref(v_path_3220_);
v_query_3221_ = lean_ctor_get(v_target_3198_, 1);
lean_inc(v_query_3221_);
lean_dec_ref(v_target_3198_);
v_segments_3236_ = lean_ctor_get(v_path_3220_, 0);
lean_inc_ref(v_segments_3236_);
v_absolute_3237_ = lean_ctor_get_uint8(v_path_3220_, sizeof(void*)*1);
lean_dec_ref(v_path_3220_);
v___x_3238_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3239_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3240_ = lean_array_size(v_segments_3236_);
v___x_3241_ = ((size_t)0ULL);
v___x_3242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3239_, v___f_3194_, v_sz_3240_, v___x_3241_, v_segments_3236_);
v___x_3243_ = lean_array_to_list(v___x_3242_);
v_result_3244_ = l_String_intercalate(v___x_3238_, v___x_3243_);
if (v_absolute_3237_ == 0)
{
v___y_3223_ = v_result_3244_;
goto v___jp_3222_;
}
else
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_string_append(v___x_3238_, v_result_3244_);
lean_dec_ref(v_result_3244_);
v___y_3223_ = v___x_3245_;
goto v___jp_3222_;
}
v___jp_3222_:
{
if (lean_obj_tag(v_query_3221_) == 0)
{
lean_dec_ref(v___f_3193_);
v___y_3200_ = v___y_3223_;
goto v___jp_3199_;
}
else
{
lean_object* v_val_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; uint8_t v___x_3227_; 
v_val_3224_ = lean_ctor_get(v_query_3221_, 0);
lean_inc(v_val_3224_);
lean_dec_ref(v_query_3221_);
v___x_3225_ = lean_array_get_size(v_val_3224_);
v___x_3226_ = lean_unsigned_to_nat(0u);
v___x_3227_ = lean_nat_dec_eq(v___x_3225_, v___x_3226_);
if (v___x_3227_ == 0)
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v_encodedParams_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3228_ = lean_array_to_list(v_val_3224_);
v___x_3229_ = lean_box(0);
v_encodedParams_3230_ = l_List_mapTR_loop___redArg(v___f_3193_, v___x_3228_, v___x_3229_);
v___x_3231_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_3232_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_3233_ = l_String_intercalate(v___x_3232_, v_encodedParams_3230_);
v___x_3234_ = lean_string_append(v___x_3231_, v___x_3233_);
lean_dec_ref(v___x_3233_);
v___x_3235_ = lean_string_append(v___y_3223_, v___x_3234_);
lean_dec_ref(v___x_3234_);
v___y_3200_ = v___x_3235_;
goto v___jp_3199_;
}
else
{
lean_dec(v_val_3224_);
lean_dec_ref(v___f_3193_);
v___y_3200_ = v___y_3223_;
goto v___jp_3199_;
}
}
}
}
case 1:
{
lean_object* v_uri_3246_; lean_object* v_scheme_3247_; lean_object* v_authority_3248_; lean_object* v_path_3249_; lean_object* v_query_3250_; lean_object* v_fragment_3251_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3288_; 
lean_dec_ref(v___f_3194_);
lean_dec_ref(v___f_3193_);
v_uri_3246_ = lean_ctor_get(v_target_3198_, 0);
lean_inc_ref(v_uri_3246_);
lean_dec_ref(v_target_3198_);
v_scheme_3247_ = lean_ctor_get(v_uri_3246_, 0);
lean_inc_ref(v_scheme_3247_);
v_authority_3248_ = lean_ctor_get(v_uri_3246_, 1);
lean_inc(v_authority_3248_);
v_path_3249_ = lean_ctor_get(v_uri_3246_, 2);
lean_inc_ref(v_path_3249_);
v_query_3250_ = lean_ctor_get(v_uri_3246_, 3);
lean_inc_ref(v_query_3250_);
v_fragment_3251_ = lean_ctor_get(v_uri_3246_, 4);
lean_inc(v_fragment_3251_);
lean_dec_ref(v_uri_3246_);
if (lean_obj_tag(v_authority_3248_) == 0)
{
lean_object* v___x_3299_; 
v___x_3299_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3288_ = v___x_3299_;
goto v___jp_3287_;
}
else
{
lean_object* v_val_3300_; lean_object* v_userInfo_3301_; lean_object* v_host_3302_; lean_object* v_port_3303_; lean_object* v___x_3304_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3323_; 
v_val_3300_ = lean_ctor_get(v_authority_3248_, 0);
lean_inc(v_val_3300_);
lean_dec_ref(v_authority_3248_);
v_userInfo_3301_ = lean_ctor_get(v_val_3300_, 0);
lean_inc(v_userInfo_3301_);
v_host_3302_ = lean_ctor_get(v_val_3300_, 1);
lean_inc_ref(v_host_3302_);
v_port_3303_ = lean_ctor_get(v_val_3300_, 2);
lean_inc(v_port_3303_);
lean_dec(v_val_3300_);
v___x_3304_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__1));
if (lean_obj_tag(v_userInfo_3301_) == 0)
{
lean_object* v___x_3333_; 
v___x_3333_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3323_ = v___x_3333_;
goto v___jp_3322_;
}
else
{
lean_object* v_val_3334_; lean_object* v_password_3335_; 
v_val_3334_ = lean_ctor_get(v_userInfo_3301_, 0);
lean_inc(v_val_3334_);
lean_dec_ref(v_userInfo_3301_);
v_password_3335_ = lean_ctor_get(v_val_3334_, 1);
if (lean_obj_tag(v_password_3335_) == 0)
{
lean_object* v_username_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v_username_3336_ = lean_ctor_get(v_val_3334_, 0);
lean_inc_ref(v_username_3336_);
lean_dec(v_val_3334_);
v___x_3337_ = lean_string_from_utf8_unchecked(v_username_3336_);
v___x_3338_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3339_ = lean_string_append(v___x_3337_, v___x_3338_);
v___y_3323_ = v___x_3339_;
goto v___jp_3322_;
}
else
{
lean_object* v_username_3340_; lean_object* v_val_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
lean_inc_ref(v_password_3335_);
v_username_3340_ = lean_ctor_get(v_val_3334_, 0);
lean_inc_ref(v_username_3340_);
lean_dec(v_val_3334_);
v_val_3341_ = lean_ctor_get(v_password_3335_, 0);
lean_inc(v_val_3341_);
lean_dec_ref(v_password_3335_);
v___x_3342_ = lean_string_from_utf8_unchecked(v_username_3340_);
v___x_3343_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3344_ = lean_string_append(v___x_3342_, v___x_3343_);
v___x_3345_ = lean_string_from_utf8_unchecked(v_val_3341_);
v___x_3346_ = lean_string_append(v___x_3344_, v___x_3345_);
lean_dec_ref(v___x_3345_);
v___x_3347_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3348_ = lean_string_append(v___x_3346_, v___x_3347_);
v___y_3323_ = v___x_3348_;
goto v___jp_3322_;
}
}
v___jp_3305_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3309_ = lean_string_append(v___y_3307_, v___y_3306_);
lean_dec_ref(v___y_3306_);
v___x_3310_ = lean_string_append(v___x_3309_, v___y_3308_);
lean_dec_ref(v___y_3308_);
v___x_3311_ = lean_string_append(v___x_3304_, v___x_3310_);
lean_dec_ref(v___x_3310_);
v___y_3288_ = v___x_3311_;
goto v___jp_3287_;
}
v___jp_3312_:
{
switch(lean_obj_tag(v_port_3303_))
{
case 0:
{
lean_object* v___x_3315_; 
v___x_3315_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3306_ = v___y_3314_;
v___y_3307_ = v___y_3313_;
v___y_3308_ = v___x_3315_;
goto v___jp_3305_;
}
case 1:
{
lean_object* v___x_3316_; 
v___x_3316_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3306_ = v___y_3314_;
v___y_3307_ = v___y_3313_;
v___y_3308_ = v___x_3316_;
goto v___jp_3305_;
}
default: 
{
uint16_t v_port_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v_port_3317_ = lean_ctor_get_uint16(v_port_3303_, 0);
lean_dec_ref(v_port_3303_);
v___x_3318_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3319_ = lean_uint16_to_nat(v_port_3317_);
v___x_3320_ = l_Nat_reprFast(v___x_3319_);
v___x_3321_ = lean_string_append(v___x_3318_, v___x_3320_);
lean_dec_ref(v___x_3320_);
v___y_3306_ = v___y_3314_;
v___y_3307_ = v___y_3313_;
v___y_3308_ = v___x_3321_;
goto v___jp_3305_;
}
}
}
v___jp_3322_:
{
switch(lean_obj_tag(v_host_3302_))
{
case 0:
{
lean_object* v_name_3324_; 
v_name_3324_ = lean_ctor_get(v_host_3302_, 0);
lean_inc_ref(v_name_3324_);
lean_dec_ref(v_host_3302_);
v___y_3313_ = v___y_3323_;
v___y_3314_ = v_name_3324_;
goto v___jp_3312_;
}
case 1:
{
lean_object* v_ipv4_3325_; lean_object* v___x_3326_; 
v_ipv4_3325_ = lean_ctor_get(v_host_3302_, 0);
lean_inc_ref(v_ipv4_3325_);
lean_dec_ref(v_host_3302_);
v___x_3326_ = lean_uv_ntop_v4(v_ipv4_3325_);
lean_dec_ref(v_ipv4_3325_);
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___x_3326_;
goto v___jp_3312_;
}
default: 
{
lean_object* v_ipv6_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v_ipv6_3327_ = lean_ctor_get(v_host_3302_, 0);
lean_inc_ref(v_ipv6_3327_);
lean_dec_ref(v_host_3302_);
v___x_3328_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3329_ = lean_uv_ntop_v6(v_ipv6_3327_);
lean_dec_ref(v_ipv6_3327_);
v___x_3330_ = lean_string_append(v___x_3328_, v___x_3329_);
lean_dec_ref(v___x_3329_);
v___x_3331_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3332_ = lean_string_append(v___x_3330_, v___x_3331_);
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___x_3332_;
goto v___jp_3312_;
}
}
}
}
v___jp_3252_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3257_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3258_ = lean_string_append(v_scheme_3247_, v___x_3257_);
v___x_3259_ = lean_string_append(v___x_3258_, v___y_3253_);
lean_dec_ref(v___y_3253_);
v___x_3260_ = lean_string_append(v___x_3259_, v___y_3255_);
lean_dec_ref(v___y_3255_);
v___x_3261_ = lean_string_append(v___x_3260_, v___y_3254_);
lean_dec_ref(v___y_3254_);
v___x_3262_ = lean_string_append(v___x_3261_, v___y_3256_);
lean_dec_ref(v___y_3256_);
v___y_3200_ = v___x_3262_;
goto v___jp_3199_;
}
v___jp_3263_:
{
if (lean_obj_tag(v_fragment_3251_) == 0)
{
lean_object* v___x_3267_; 
v___x_3267_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3253_ = v___y_3264_;
v___y_3254_ = v___y_3266_;
v___y_3255_ = v___y_3265_;
v___y_3256_ = v___x_3267_;
goto v___jp_3252_;
}
else
{
lean_object* v_val_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v_val_3268_ = lean_ctor_get(v_fragment_3251_, 0);
lean_inc(v_val_3268_);
lean_dec_ref(v_fragment_3251_);
v___x_3269_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__0));
v___x_3270_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3268_);
lean_dec(v_val_3268_);
v___x_3271_ = lean_string_from_utf8_unchecked(v___x_3270_);
v___x_3272_ = lean_string_append(v___x_3269_, v___x_3271_);
lean_dec_ref(v___x_3271_);
v___y_3253_ = v___y_3264_;
v___y_3254_ = v___y_3266_;
v___y_3255_ = v___y_3265_;
v___y_3256_ = v___x_3272_;
goto v___jp_3252_;
}
}
v___jp_3273_:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; uint8_t v___x_3278_; 
v___x_3276_ = lean_array_get_size(v_query_3250_);
v___x_3277_ = lean_unsigned_to_nat(0u);
v___x_3278_ = lean_nat_dec_eq(v___x_3276_, v___x_3277_);
if (v___x_3278_ == 0)
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v_encodedParams_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3279_ = lean_array_to_list(v_query_3250_);
v___x_3280_ = lean_box(0);
v_encodedParams_3281_ = l_List_mapTR_loop___redArg(v___f_3195_, v___x_3279_, v___x_3280_);
v___x_3282_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_3283_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_3284_ = l_String_intercalate(v___x_3283_, v_encodedParams_3281_);
v___x_3285_ = lean_string_append(v___x_3282_, v___x_3284_);
lean_dec_ref(v___x_3284_);
v___y_3264_ = v___y_3274_;
v___y_3265_ = v___y_3275_;
v___y_3266_ = v___x_3285_;
goto v___jp_3263_;
}
else
{
lean_object* v___x_3286_; 
lean_dec_ref(v_query_3250_);
lean_dec_ref(v___f_3195_);
v___x_3286_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3264_ = v___y_3274_;
v___y_3265_ = v___y_3275_;
v___y_3266_ = v___x_3286_;
goto v___jp_3263_;
}
}
v___jp_3287_:
{
lean_object* v_segments_3289_; uint8_t v_absolute_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; size_t v_sz_3293_; size_t v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v_result_3297_; 
v_segments_3289_ = lean_ctor_get(v_path_3249_, 0);
lean_inc_ref(v_segments_3289_);
v_absolute_3290_ = lean_ctor_get_uint8(v_path_3249_, sizeof(void*)*1);
lean_dec_ref(v_path_3249_);
v___x_3291_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3292_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3293_ = lean_array_size(v_segments_3289_);
v___x_3294_ = ((size_t)0ULL);
v___x_3295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3292_, v___f_3196_, v_sz_3293_, v___x_3294_, v_segments_3289_);
v___x_3296_ = lean_array_to_list(v___x_3295_);
v_result_3297_ = l_String_intercalate(v___x_3291_, v___x_3296_);
if (v_absolute_3290_ == 0)
{
v___y_3274_ = v___y_3288_;
v___y_3275_ = v_result_3297_;
goto v___jp_3273_;
}
else
{
lean_object* v___x_3298_; 
v___x_3298_ = lean_string_append(v___x_3291_, v_result_3297_);
lean_dec_ref(v_result_3297_);
v___y_3274_ = v___y_3288_;
v___y_3275_ = v___x_3298_;
goto v___jp_3273_;
}
}
}
case 2:
{
lean_object* v_authority_3349_; lean_object* v_userInfo_3350_; lean_object* v_host_3351_; lean_object* v_port_3352_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3364_; 
lean_dec_ref(v___f_3196_);
lean_dec_ref(v___f_3195_);
lean_dec_ref(v___f_3194_);
lean_dec_ref(v___f_3193_);
v_authority_3349_ = lean_ctor_get(v_target_3198_, 0);
lean_inc_ref(v_authority_3349_);
lean_dec_ref(v_target_3198_);
v_userInfo_3350_ = lean_ctor_get(v_authority_3349_, 0);
lean_inc(v_userInfo_3350_);
v_host_3351_ = lean_ctor_get(v_authority_3349_, 1);
lean_inc_ref(v_host_3351_);
v_port_3352_ = lean_ctor_get(v_authority_3349_, 2);
lean_inc(v_port_3352_);
lean_dec_ref(v_authority_3349_);
if (lean_obj_tag(v_userInfo_3350_) == 0)
{
lean_object* v___x_3374_; 
v___x_3374_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3364_ = v___x_3374_;
goto v___jp_3363_;
}
else
{
lean_object* v_val_3375_; lean_object* v_password_3376_; 
v_val_3375_ = lean_ctor_get(v_userInfo_3350_, 0);
lean_inc(v_val_3375_);
lean_dec_ref(v_userInfo_3350_);
v_password_3376_ = lean_ctor_get(v_val_3375_, 1);
if (lean_obj_tag(v_password_3376_) == 0)
{
lean_object* v_username_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v_username_3377_ = lean_ctor_get(v_val_3375_, 0);
lean_inc_ref(v_username_3377_);
lean_dec(v_val_3375_);
v___x_3378_ = lean_string_from_utf8_unchecked(v_username_3377_);
v___x_3379_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3380_ = lean_string_append(v___x_3378_, v___x_3379_);
v___y_3364_ = v___x_3380_;
goto v___jp_3363_;
}
else
{
lean_object* v_username_3381_; lean_object* v_val_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
lean_inc_ref(v_password_3376_);
v_username_3381_ = lean_ctor_get(v_val_3375_, 0);
lean_inc_ref(v_username_3381_);
lean_dec(v_val_3375_);
v_val_3382_ = lean_ctor_get(v_password_3376_, 0);
lean_inc(v_val_3382_);
lean_dec_ref(v_password_3376_);
v___x_3383_ = lean_string_from_utf8_unchecked(v_username_3381_);
v___x_3384_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3385_ = lean_string_append(v___x_3383_, v___x_3384_);
v___x_3386_ = lean_string_from_utf8_unchecked(v_val_3382_);
v___x_3387_ = lean_string_append(v___x_3385_, v___x_3386_);
lean_dec_ref(v___x_3386_);
v___x_3388_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3389_ = lean_string_append(v___x_3387_, v___x_3388_);
v___y_3364_ = v___x_3389_;
goto v___jp_3363_;
}
}
v___jp_3353_:
{
switch(lean_obj_tag(v_port_3352_))
{
case 0:
{
lean_object* v___x_3356_; 
v___x_3356_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3215_ = v___y_3355_;
v___y_3216_ = v___y_3354_;
v___y_3217_ = v___x_3356_;
goto v___jp_3214_;
}
case 1:
{
lean_object* v___x_3357_; 
v___x_3357_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3215_ = v___y_3355_;
v___y_3216_ = v___y_3354_;
v___y_3217_ = v___x_3357_;
goto v___jp_3214_;
}
default: 
{
uint16_t v_port_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v_port_3358_ = lean_ctor_get_uint16(v_port_3352_, 0);
lean_dec_ref(v_port_3352_);
v___x_3359_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3360_ = lean_uint16_to_nat(v_port_3358_);
v___x_3361_ = l_Nat_reprFast(v___x_3360_);
v___x_3362_ = lean_string_append(v___x_3359_, v___x_3361_);
lean_dec_ref(v___x_3361_);
v___y_3215_ = v___y_3355_;
v___y_3216_ = v___y_3354_;
v___y_3217_ = v___x_3362_;
goto v___jp_3214_;
}
}
}
v___jp_3363_:
{
switch(lean_obj_tag(v_host_3351_))
{
case 0:
{
lean_object* v_name_3365_; 
v_name_3365_ = lean_ctor_get(v_host_3351_, 0);
lean_inc_ref(v_name_3365_);
lean_dec_ref(v_host_3351_);
v___y_3354_ = v___y_3364_;
v___y_3355_ = v_name_3365_;
goto v___jp_3353_;
}
case 1:
{
lean_object* v_ipv4_3366_; lean_object* v___x_3367_; 
v_ipv4_3366_ = lean_ctor_get(v_host_3351_, 0);
lean_inc_ref(v_ipv4_3366_);
lean_dec_ref(v_host_3351_);
v___x_3367_ = lean_uv_ntop_v4(v_ipv4_3366_);
lean_dec_ref(v_ipv4_3366_);
v___y_3354_ = v___y_3364_;
v___y_3355_ = v___x_3367_;
goto v___jp_3353_;
}
default: 
{
lean_object* v_ipv6_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v_ipv6_3368_ = lean_ctor_get(v_host_3351_, 0);
lean_inc_ref(v_ipv6_3368_);
lean_dec_ref(v_host_3351_);
v___x_3369_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3370_ = lean_uv_ntop_v6(v_ipv6_3368_);
lean_dec_ref(v_ipv6_3368_);
v___x_3371_ = lean_string_append(v___x_3369_, v___x_3370_);
lean_dec_ref(v___x_3370_);
v___x_3372_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3373_ = lean_string_append(v___x_3371_, v___x_3372_);
v___y_3354_ = v___y_3364_;
v___y_3355_ = v___x_3373_;
goto v___jp_3353_;
}
}
}
}
default: 
{
lean_object* v___x_3390_; 
lean_dec_ref(v___f_3196_);
lean_dec_ref(v___f_3195_);
lean_dec_ref(v___f_3194_);
lean_dec_ref(v___f_3193_);
v___x_3390_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__4___closed__0));
v___y_3200_ = v___x_3390_;
goto v___jp_3199_;
}
}
v___jp_3199_:
{
lean_object* v_data_3201_; lean_object* v_size_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3213_; 
v_data_3201_ = lean_ctor_get(v_buffer_3197_, 0);
v_size_3202_ = lean_ctor_get(v_buffer_3197_, 1);
v_isSharedCheck_3213_ = !lean_is_exclusive(v_buffer_3197_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3204_ = v_buffer_3197_;
v_isShared_3205_ = v_isSharedCheck_3213_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_size_3202_);
lean_inc(v_data_3201_);
lean_dec(v_buffer_3197_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3213_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3211_; 
v___x_3206_ = lean_string_to_utf8(v___y_3200_);
lean_dec_ref(v___y_3200_);
lean_inc_ref(v___x_3206_);
v___x_3207_ = lean_array_push(v_data_3201_, v___x_3206_);
v___x_3208_ = lean_byte_array_size(v___x_3206_);
lean_dec_ref(v___x_3206_);
v___x_3209_ = lean_nat_add(v_size_3202_, v___x_3208_);
lean_dec(v_size_3202_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 1, v___x_3209_);
lean_ctor_set(v___x_3204_, 0, v___x_3207_);
v___x_3211_ = v___x_3204_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3207_);
lean_ctor_set(v_reuseFailAlloc_3212_, 1, v___x_3209_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
v___jp_3214_:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = lean_string_append(v___y_3216_, v___y_3215_);
lean_dec_ref(v___y_3215_);
v___x_3219_ = lean_string_append(v___x_3218_, v___y_3217_);
lean_dec_ref(v___y_3217_);
v___y_3200_ = v___x_3219_;
goto v___jp_3199_;
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
