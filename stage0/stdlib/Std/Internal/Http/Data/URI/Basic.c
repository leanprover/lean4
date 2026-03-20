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
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_ByteArray_instDecidableEq(lean_object*, lean_object*);
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
lean_object* l_ByteArray_instDecidableEq___boxed(lean_object*, lean_object*);
lean_object* l_Option_instBEq_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instBEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_getLast_x3f___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Option_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_URI_EncodedSegment_decode(lean_object*);
extern lean_object* l_Std_Net_instInhabitedIPv4Addr_default;
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_EncodedUserInfo_decode(lean_object*);
lean_object* l_Std_Http_URI_EncodedUserInfo_encode(lean_object*);
lean_object* l_Std_Http_URI_EncodedQueryParam_decode(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_List_eraseDupsBy___redArg(lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Http_URI_instReprQuery___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_EncodedString_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_URI_instReprQuery___closed__0 = (const lean_object*)&l_Std_Http_URI_instReprQuery___closed__0_value;
static const lean_closure_object l_Std_Http_URI_instReprQuery___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_repr___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_URI_instReprQuery___closed__0_value)} };
static const lean_object* l_Std_Http_URI_instReprQuery___closed__1 = (const lean_object*)&l_Std_Http_URI_instReprQuery___closed__1_value;
static const lean_closure_object l_Std_Http_URI_instReprQuery___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprTupleOfRepr___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprQuery___closed__1_value)} };
static const lean_object* l_Std_Http_URI_instReprQuery___closed__2 = (const lean_object*)&l_Std_Http_URI_instReprQuery___closed__2_value;
static const lean_closure_object l_Std_Http_URI_instReprQuery___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Prod_repr___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_URI_instReprQuery___closed__0_value),((lean_object*)&l_Std_Http_URI_instReprQuery___closed__2_value)} };
static const lean_object* l_Std_Http_URI_instReprQuery___closed__3 = (const lean_object*)&l_Std_Http_URI_instReprQuery___closed__3_value;
static const lean_closure_object l_Std_Http_URI_instReprQuery___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instRepr___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_URI_instReprQuery___closed__3_value)} };
static const lean_object* l_Std_Http_URI_instReprQuery___closed__4 = (const lean_object*)&l_Std_Http_URI_instReprQuery___closed__4_value;
LEAN_EXPORT const lean_object* l_Std_Http_URI_instReprQuery = (const lean_object*)&l_Std_Http_URI_instReprQuery___closed__4_value;
static lean_once_cell_t l_Std_Http_URI_instInhabitedQuery___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instInhabitedQuery___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_URI_instInhabitedQuery;
static lean_once_cell_t l_Std_Http_URI_instBEqQuery___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instBEqQuery___closed__0;
static lean_once_cell_t l_Std_Http_URI_instBEqQuery___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instBEqQuery___closed__1;
static lean_once_cell_t l_Std_Http_URI_instBEqQuery___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instBEqQuery___closed__2;
LEAN_EXPORT lean_object* l_Std_Http_URI_instBEqQuery;
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
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__2;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__3;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__4_value;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__2_spec__6_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instReprURI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instReprURI_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instReprURI___closed__0 = (const lean_object*)&l_Std_Http_instReprURI___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instReprURI = (const lean_object*)&l_Std_Http_instReprURI___closed__0_value;
static const lean_array_object l_Std_Http_instInhabitedURI_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_instInhabitedURI_default___closed__0 = (const lean_object*)&l_Std_Http_instInhabitedURI_default___closed__0_value;
static const lean_ctor_object l_Std_Http_instInhabitedURI_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_URI_instInhabitedScheme___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_URI_instInhabitedPath_default___closed__1_value),((lean_object*)&l_Std_Http_instInhabitedURI_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_instInhabitedURI_default___closed__1 = (const lean_object*)&l_Std_Http_instInhabitedURI_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_instInhabitedURI_default = (const lean_object*)&l_Std_Http_instInhabitedURI_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_instInhabitedURI = (const lean_object*)&l_Std_Http_instInhabitedURI_default___closed__1_value;
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_instBEqURI_beq_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_instBEqURI_beq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_instBEqURI_beq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_instBEqURI_beq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Http_URI_instInhabitedBuilder_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_instInhabitedBuilder_default___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_URI_instInhabitedBuilder_default;
LEAN_EXPORT lean_object* l_Std_Http_URI_instInhabitedBuilder;
static const lean_array_object l_Std_Http_URI_Builder_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_URI_Builder_empty___closed__0 = (const lean_object*)&l_Std_Http_URI_Builder_empty___closed__0_value;
static lean_once_cell_t l_Std_Http_URI_Builder_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Builder_empty___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_empty;
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
static lean_once_cell_t l_Std_Http_RequestTarget_instToString___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_RequestTarget_instToString___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_RequestTarget_instEncodeV11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_RequestTarget_instEncodeV11___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11;
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
v___x_83_ = lean_panic_fn(v___x_82_, v_msg_81_);
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
lean_dec_ref(v_ctr_597_);
v___x_601_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v___x_602_ = lean_box(1);
v___x_603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v_a_598_);
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
lean_dec_ref(v_ctr_877_);
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
static lean_object* _init_l_Std_Http_URI_instInhabitedQuery___closed__0(void){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Array_instInhabited(lean_box(0));
return v___x_1390_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedQuery(void){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_obj_once(&l_Std_Http_URI_instInhabitedQuery___closed__0, &l_Std_Http_URI_instInhabitedQuery___closed__0_once, _init_l_Std_Http_URI_instInhabitedQuery___closed__0);
return v___x_1391_;
}
}
static lean_object* _init_l_Std_Http_URI_instBEqQuery___closed__0(void){
_start:
{
lean_object* v___f_1392_; lean_object* v___x_1393_; 
v___f_1392_ = lean_alloc_closure((void*)(l_ByteArray_instDecidableEq___boxed), 2, 0);
v___x_1393_ = lean_alloc_closure((void*)(l_Option_instBEq_beq___boxed), 4, 2);
lean_closure_set(v___x_1393_, 0, lean_box(0));
lean_closure_set(v___x_1393_, 1, v___f_1392_);
return v___x_1393_;
}
}
static lean_object* _init_l_Std_Http_URI_instBEqQuery___closed__1(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___f_1395_; lean_object* v___f_1396_; 
v___x_1394_ = lean_obj_once(&l_Std_Http_URI_instBEqQuery___closed__0, &l_Std_Http_URI_instBEqQuery___closed__0_once, _init_l_Std_Http_URI_instBEqQuery___closed__0);
v___f_1395_ = lean_alloc_closure((void*)(l_ByteArray_instDecidableEq___boxed), 2, 0);
v___f_1396_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1396_, 0, v___f_1395_);
lean_closure_set(v___f_1396_, 1, v___x_1394_);
return v___f_1396_;
}
}
static lean_object* _init_l_Std_Http_URI_instBEqQuery___closed__2(void){
_start:
{
lean_object* v___f_1397_; lean_object* v___f_1398_; 
v___f_1397_ = lean_obj_once(&l_Std_Http_URI_instBEqQuery___closed__1, &l_Std_Http_URI_instBEqQuery___closed__1_once, _init_l_Std_Http_URI_instBEqQuery___closed__1);
v___f_1398_ = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1398_, 0, v___f_1397_);
return v___f_1398_;
}
}
static lean_object* _init_l_Std_Http_URI_instBEqQuery(void){
_start:
{
lean_object* v___f_1399_; 
v___f_1399_ = lean_obj_once(&l_Std_Http_URI_instBEqQuery___closed__2, &l_Std_Http_URI_instBEqQuery___closed__2_once, _init_l_Std_Http_URI_instBEqQuery___closed__2);
return v___f_1399_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(lean_object* v_as_1400_){
_start:
{
lean_object* v___f_1401_; lean_object* v___x_1402_; 
v___f_1401_ = lean_alloc_closure((void*)(l_ByteArray_instDecidableEq___boxed), 2, 0);
v___x_1402_ = l_List_eraseDupsBy___redArg(v___f_1401_, v_as_1400_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(size_t v_sz_1403_, size_t v_i_1404_, lean_object* v_bs_1405_){
_start:
{
uint8_t v___x_1406_; 
v___x_1406_ = lean_usize_dec_lt(v_i_1404_, v_sz_1403_);
if (v___x_1406_ == 0)
{
return v_bs_1405_;
}
else
{
lean_object* v_v_1407_; lean_object* v_fst_1408_; lean_object* v___x_1409_; lean_object* v_bs_x27_1410_; size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
v_v_1407_ = lean_array_uget_borrowed(v_bs_1405_, v_i_1404_);
v_fst_1408_ = lean_ctor_get(v_v_1407_, 0);
lean_inc(v_fst_1408_);
v___x_1409_ = lean_unsigned_to_nat(0u);
v_bs_x27_1410_ = lean_array_uset(v_bs_1405_, v_i_1404_, v___x_1409_);
v___x_1411_ = ((size_t)1ULL);
v___x_1412_ = lean_usize_add(v_i_1404_, v___x_1411_);
v___x_1413_ = lean_array_uset(v_bs_x27_1410_, v_i_1404_, v_fst_1408_);
v_i_1404_ = v___x_1412_;
v_bs_1405_ = v___x_1413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0___boxed(lean_object* v_sz_1415_, lean_object* v_i_1416_, lean_object* v_bs_1417_){
_start:
{
size_t v_sz_boxed_1418_; size_t v_i_boxed_1419_; lean_object* v_res_1420_; 
v_sz_boxed_1418_ = lean_unbox_usize(v_sz_1415_);
lean_dec(v_sz_1415_);
v_i_boxed_1419_ = lean_unbox_usize(v_i_1416_);
lean_dec(v_i_1416_);
v_res_1420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_boxed_1418_, v_i_boxed_1419_, v_bs_1417_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_names(lean_object* v_query_1421_){
_start:
{
size_t v_sz_1422_; size_t v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_sz_1422_ = lean_array_size(v_query_1421_);
v___x_1423_ = ((size_t)0ULL);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_names_spec__0(v_sz_1422_, v___x_1423_, v_query_1421_);
v___x_1425_ = lean_array_to_list(v___x_1424_);
v___x_1426_ = l_List_eraseDups___at___00Std_Http_URI_Query_names_spec__1(v___x_1425_);
v___x_1427_ = lean_array_mk(v___x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(size_t v_sz_1428_, size_t v_i_1429_, lean_object* v_bs_1430_){
_start:
{
uint8_t v___x_1431_; 
v___x_1431_ = lean_usize_dec_lt(v_i_1429_, v_sz_1428_);
if (v___x_1431_ == 0)
{
return v_bs_1430_;
}
else
{
lean_object* v_v_1432_; lean_object* v_snd_1433_; lean_object* v___x_1434_; lean_object* v_bs_x27_1435_; size_t v___x_1436_; size_t v___x_1437_; lean_object* v___x_1438_; 
v_v_1432_ = lean_array_uget_borrowed(v_bs_1430_, v_i_1429_);
v_snd_1433_ = lean_ctor_get(v_v_1432_, 1);
lean_inc(v_snd_1433_);
v___x_1434_ = lean_unsigned_to_nat(0u);
v_bs_x27_1435_ = lean_array_uset(v_bs_1430_, v_i_1429_, v___x_1434_);
v___x_1436_ = ((size_t)1ULL);
v___x_1437_ = lean_usize_add(v_i_1429_, v___x_1436_);
v___x_1438_ = lean_array_uset(v_bs_x27_1435_, v_i_1429_, v_snd_1433_);
v_i_1429_ = v___x_1437_;
v_bs_1430_ = v___x_1438_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0___boxed(lean_object* v_sz_1440_, lean_object* v_i_1441_, lean_object* v_bs_1442_){
_start:
{
size_t v_sz_boxed_1443_; size_t v_i_boxed_1444_; lean_object* v_res_1445_; 
v_sz_boxed_1443_ = lean_unbox_usize(v_sz_1440_);
lean_dec(v_sz_1440_);
v_i_boxed_1444_ = lean_unbox_usize(v_i_1441_);
lean_dec(v_i_1441_);
v_res_1445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_boxed_1443_, v_i_boxed_1444_, v_bs_1442_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_values(lean_object* v_query_1446_){
_start:
{
size_t v_sz_1447_; size_t v___x_1448_; lean_object* v___x_1449_; 
v_sz_1447_ = lean_array_size(v_query_1446_);
v___x_1448_ = ((size_t)0ULL);
v___x_1449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_values_spec__0(v_sz_1447_, v___x_1448_, v_query_1446_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray(lean_object* v_query_1450_){
_start:
{
lean_inc_ref(v_query_1450_);
return v_query_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toArray___boxed(lean_object* v_query_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Std_Http_URI_Query_toArray(v_query_1451_);
lean_dec_ref(v_query_1451_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object* v_key_1454_, lean_object* v_value_1455_){
_start:
{
if (lean_obj_tag(v_value_1455_) == 0)
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_string_from_utf8_unchecked(v_key_1454_);
return v___x_1456_;
}
else
{
lean_object* v_val_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_val_1457_ = lean_ctor_get(v_value_1455_, 0);
lean_inc(v_val_1457_);
lean_dec_ref(v_value_1455_);
v___x_1458_ = lean_string_from_utf8_unchecked(v_key_1454_);
v___x_1459_ = ((lean_object*)(l_Std_Http_URI_Query_formatQueryParam___closed__0));
v___x_1460_ = lean_string_append(v___x_1458_, v___x_1459_);
v___x_1461_ = lean_string_from_utf8_unchecked(v_val_1457_);
v___x_1462_ = lean_string_append(v___x_1460_, v___x_1461_);
lean_dec_ref(v___x_1461_);
return v___x_1462_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(lean_object* v_key_1466_, lean_object* v_as_1467_, size_t v_sz_1468_, size_t v_i_1469_, lean_object* v_b_1470_){
_start:
{
uint8_t v___x_1471_; 
v___x_1471_ = lean_usize_dec_lt(v_i_1469_, v_sz_1468_);
if (v___x_1471_ == 0)
{
lean_dec_ref(v_key_1466_);
return v_b_1470_;
}
else
{
lean_object* v_a_1472_; lean_object* v_fst_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
lean_dec_ref(v_b_1470_);
v_a_1472_ = lean_array_uget_borrowed(v_as_1467_, v_i_1469_);
v_fst_1473_ = lean_ctor_get(v_a_1472_, 0);
v___x_1474_ = lean_box(0);
lean_inc_ref(v_key_1466_);
lean_inc(v_fst_1473_);
v___x_1475_ = l_ByteArray_instDecidableEq(v_fst_1473_, v_key_1466_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; 
v___x_1476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v___x_1477_ = ((size_t)1ULL);
v___x_1478_ = lean_usize_add(v_i_1469_, v___x_1477_);
v_i_1469_ = v___x_1478_;
v_b_1470_ = v___x_1476_;
goto _start;
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_dec_ref(v_key_1466_);
lean_inc(v_a_1472_);
v___x_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1480_, 0, v_a_1472_);
v___x_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v___x_1474_);
return v___x_1482_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___boxed(lean_object* v_key_1483_, lean_object* v_as_1484_, lean_object* v_sz_1485_, lean_object* v_i_1486_, lean_object* v_b_1487_){
_start:
{
size_t v_sz_boxed_1488_; size_t v_i_boxed_1489_; lean_object* v_res_1490_; 
v_sz_boxed_1488_ = lean_unbox_usize(v_sz_1485_);
lean_dec(v_sz_1485_);
v_i_boxed_1489_ = lean_unbox_usize(v_i_1486_);
lean_dec(v_i_1486_);
v_res_1490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1483_, v_as_1484_, v_sz_boxed_1488_, v_i_boxed_1489_, v_b_1487_);
lean_dec_ref(v_as_1484_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f(lean_object* v_query_1491_, lean_object* v_key_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; size_t v_sz_1495_; size_t v___x_1496_; lean_object* v___x_1497_; lean_object* v_fst_1498_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0___closed__0));
v_sz_1495_ = lean_array_size(v_query_1491_);
v___x_1496_ = ((size_t)0ULL);
v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_URI_Query_findEncoded_x3f_spec__0(v_key_1492_, v_query_1491_, v_sz_1495_, v___x_1496_, v___x_1494_);
v_fst_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_fst_1498_);
lean_dec_ref(v___x_1497_);
if (lean_obj_tag(v_fst_1498_) == 0)
{
return v___x_1493_;
}
else
{
lean_object* v_val_1499_; 
v_val_1499_ = lean_ctor_get(v_fst_1498_, 0);
lean_inc(v_val_1499_);
lean_dec_ref(v_fst_1498_);
if (lean_obj_tag(v_val_1499_) == 0)
{
return v___x_1493_;
}
else
{
lean_object* v_val_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1508_; 
v_val_1500_ = lean_ctor_get(v_val_1499_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_val_1499_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1502_ = v_val_1499_;
v_isShared_1503_ = v_isSharedCheck_1508_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_val_1500_);
lean_dec(v_val_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1508_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v_snd_1504_; lean_object* v___x_1506_; 
v_snd_1504_ = lean_ctor_get(v_val_1500_, 1);
lean_inc(v_snd_1504_);
lean_dec(v_val_1500_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v_snd_1504_);
v___x_1506_ = v___x_1502_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_snd_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findEncoded_x3f___boxed(lean_object* v_query_1509_, lean_object* v_key_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1509_, v_key_1510_);
lean_dec_ref(v_query_1509_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f(lean_object* v_query_1512_, lean_object* v_key_1513_){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1513_);
v___x_1515_ = l_Std_Http_URI_Query_findEncoded_x3f(v_query_1512_, v___x_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_find_x3f___boxed(lean_object* v_query_1516_, lean_object* v_key_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Std_Http_URI_Query_find_x3f(v_query_1516_, v_key_1517_);
lean_dec_ref(v_key_1517_);
lean_dec_ref(v_query_1516_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(lean_object* v_key_1519_, lean_object* v_as_1520_, size_t v_i_1521_, size_t v_stop_1522_, lean_object* v_b_1523_){
_start:
{
lean_object* v___y_1525_; uint8_t v___x_1529_; 
v___x_1529_ = lean_usize_dec_eq(v_i_1521_, v_stop_1522_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v_fst_1531_; lean_object* v_snd_1532_; uint8_t v___x_1533_; 
v___x_1530_ = lean_array_uget_borrowed(v_as_1520_, v_i_1521_);
v_fst_1531_ = lean_ctor_get(v___x_1530_, 0);
v_snd_1532_ = lean_ctor_get(v___x_1530_, 1);
lean_inc_ref(v_key_1519_);
lean_inc(v_fst_1531_);
v___x_1533_ = l_ByteArray_instDecidableEq(v_fst_1531_, v_key_1519_);
if (v___x_1533_ == 0)
{
v___y_1525_ = v_b_1523_;
goto v___jp_1524_;
}
else
{
lean_object* v___x_1534_; 
lean_inc(v_snd_1532_);
v___x_1534_ = lean_array_push(v_b_1523_, v_snd_1532_);
v___y_1525_ = v___x_1534_;
goto v___jp_1524_;
}
}
else
{
lean_dec_ref(v_key_1519_);
return v_b_1523_;
}
v___jp_1524_:
{
size_t v___x_1526_; size_t v___x_1527_; 
v___x_1526_ = ((size_t)1ULL);
v___x_1527_ = lean_usize_add(v_i_1521_, v___x_1526_);
v_i_1521_ = v___x_1527_;
v_b_1523_ = v___y_1525_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0___boxed(lean_object* v_key_1535_, lean_object* v_as_1536_, lean_object* v_i_1537_, lean_object* v_stop_1538_, lean_object* v_b_1539_){
_start:
{
size_t v_i_boxed_1540_; size_t v_stop_boxed_1541_; lean_object* v_res_1542_; 
v_i_boxed_1540_ = lean_unbox_usize(v_i_1537_);
lean_dec(v_i_1537_);
v_stop_boxed_1541_ = lean_unbox_usize(v_stop_1538_);
lean_dec(v_stop_1538_);
v_res_1542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1535_, v_as_1536_, v_i_boxed_1540_, v_stop_boxed_1541_, v_b_1539_);
lean_dec_ref(v_as_1536_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(lean_object* v_key_1545_, lean_object* v_as_1546_, lean_object* v_start_1547_, lean_object* v_stop_1548_){
_start:
{
lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___closed__0));
v___x_1550_ = lean_nat_dec_lt(v_start_1547_, v_stop_1548_);
if (v___x_1550_ == 0)
{
lean_dec_ref(v_key_1545_);
return v___x_1549_;
}
else
{
lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = lean_array_get_size(v_as_1546_);
v___x_1552_ = lean_nat_dec_le(v_stop_1548_, v___x_1551_);
if (v___x_1552_ == 0)
{
uint8_t v___x_1553_; 
v___x_1553_ = lean_nat_dec_lt(v_start_1547_, v___x_1551_);
if (v___x_1553_ == 0)
{
lean_dec_ref(v_key_1545_);
return v___x_1549_;
}
else
{
size_t v___x_1554_; size_t v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = lean_usize_of_nat(v_start_1547_);
v___x_1555_ = lean_usize_of_nat(v___x_1551_);
v___x_1556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1545_, v_as_1546_, v___x_1554_, v___x_1555_, v___x_1549_);
return v___x_1556_;
}
}
else
{
size_t v___x_1557_; size_t v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = lean_usize_of_nat(v_start_1547_);
v___x_1558_ = lean_usize_of_nat(v_stop_1548_);
v___x_1559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0_spec__0(v_key_1545_, v_as_1546_, v___x_1557_, v___x_1558_, v___x_1549_);
return v___x_1559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0___boxed(lean_object* v_key_1560_, lean_object* v_as_1561_, lean_object* v_start_1562_, lean_object* v_stop_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1560_, v_as_1561_, v_start_1562_, v_stop_1563_);
lean_dec(v_stop_1563_);
lean_dec(v_start_1562_);
lean_dec_ref(v_as_1561_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded(lean_object* v_query_1565_, lean_object* v_key_1566_){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = lean_unsigned_to_nat(0u);
v___x_1568_ = lean_array_get_size(v_query_1565_);
v___x_1569_ = l_Array_filterMapM___at___00Std_Http_URI_Query_findAllEncoded_spec__0(v_key_1566_, v_query_1565_, v___x_1567_, v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAllEncoded___boxed(lean_object* v_query_1570_, lean_object* v_key_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1570_, v_key_1571_);
lean_dec_ref(v_query_1570_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll(lean_object* v_query_1573_, lean_object* v_key_1574_){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1574_);
v___x_1576_ = l_Std_Http_URI_Query_findAllEncoded(v_query_1573_, v___x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_findAll___boxed(lean_object* v_query_1577_, lean_object* v_key_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Std_Http_URI_Query_findAll(v_query_1577_, v_key_1578_);
lean_dec_ref(v_key_1578_);
lean_dec_ref(v_query_1577_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert(lean_object* v_query_1580_, lean_object* v_key_1581_, lean_object* v_value_1582_){
_start:
{
lean_object* v_encodedKey_1583_; lean_object* v_encodedValue_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_encodedKey_1583_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1581_);
v_encodedValue_1584_ = l_Std_Http_URI_EncodedQueryParam_encode(v_value_1582_);
v___x_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1585_, 0, v_encodedValue_1584_);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_encodedKey_1583_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = lean_array_push(v_query_1580_, v___x_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insert___boxed(lean_object* v_query_1588_, lean_object* v_key_1589_, lean_object* v_value_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Std_Http_URI_Query_insert(v_query_1588_, v_key_1589_, v_value_1590_);
lean_dec_ref(v_value_1590_);
lean_dec_ref(v_key_1589_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object* v_query_1592_, lean_object* v_key_1593_, lean_object* v_value_1594_){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v_key_1593_);
lean_ctor_set(v___x_1595_, 1, v_value_1594_);
v___x_1596_ = lean_array_push(v_query_1592_, v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_ofList(lean_object* v_pairs_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_array_mk(v_pairs_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(lean_object* v_key_1602_, lean_object* v_as_1603_, size_t v_i_1604_, size_t v_stop_1605_){
_start:
{
uint8_t v___x_1606_; 
v___x_1606_ = lean_usize_dec_eq(v_i_1604_, v_stop_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v_fst_1608_; uint8_t v___x_1609_; 
v___x_1607_ = lean_array_uget_borrowed(v_as_1603_, v_i_1604_);
v_fst_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc_ref(v_key_1602_);
lean_inc(v_fst_1608_);
v___x_1609_ = l_ByteArray_instDecidableEq(v_fst_1608_, v_key_1602_);
if (v___x_1609_ == 0)
{
size_t v___x_1610_; size_t v___x_1611_; 
v___x_1610_ = ((size_t)1ULL);
v___x_1611_ = lean_usize_add(v_i_1604_, v___x_1610_);
v_i_1604_ = v___x_1611_;
goto _start;
}
else
{
lean_dec_ref(v_key_1602_);
return v___x_1609_;
}
}
else
{
uint8_t v___x_1613_; 
lean_dec_ref(v_key_1602_);
v___x_1613_ = 0;
return v___x_1613_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0___boxed(lean_object* v_key_1614_, lean_object* v_as_1615_, lean_object* v_i_1616_, lean_object* v_stop_1617_){
_start:
{
size_t v_i_boxed_1618_; size_t v_stop_boxed_1619_; uint8_t v_res_1620_; lean_object* v_r_1621_; 
v_i_boxed_1618_ = lean_unbox_usize(v_i_1616_);
lean_dec(v_i_1616_);
v_stop_boxed_1619_ = lean_unbox_usize(v_stop_1617_);
lean_dec(v_stop_1617_);
v_res_1620_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1614_, v_as_1615_, v_i_boxed_1618_, v_stop_boxed_1619_);
lean_dec_ref(v_as_1615_);
v_r_1621_ = lean_box(v_res_1620_);
return v_r_1621_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_containsEncoded(lean_object* v_query_1622_, lean_object* v_key_1623_){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1624_ = lean_unsigned_to_nat(0u);
v___x_1625_ = lean_array_get_size(v_query_1622_);
v___x_1626_ = lean_nat_dec_lt(v___x_1624_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_dec_ref(v_key_1623_);
return v___x_1626_;
}
else
{
if (v___x_1626_ == 0)
{
lean_dec_ref(v_key_1623_);
return v___x_1626_;
}
else
{
size_t v___x_1627_; size_t v___x_1628_; uint8_t v___x_1629_; 
v___x_1627_ = ((size_t)0ULL);
v___x_1628_ = lean_usize_of_nat(v___x_1625_);
v___x_1629_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_URI_Query_containsEncoded_spec__0(v_key_1623_, v_query_1622_, v___x_1627_, v___x_1628_);
return v___x_1629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_containsEncoded___boxed(lean_object* v_query_1630_, lean_object* v_key_1631_){
_start:
{
uint8_t v_res_1632_; lean_object* v_r_1633_; 
v_res_1632_ = l_Std_Http_URI_Query_containsEncoded(v_query_1630_, v_key_1631_);
lean_dec_ref(v_query_1630_);
v_r_1633_ = lean_box(v_res_1632_);
return v_r_1633_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_URI_Query_contains(lean_object* v_query_1634_, lean_object* v_key_1635_){
_start:
{
lean_object* v___x_1636_; uint8_t v___x_1637_; 
v___x_1636_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1635_);
v___x_1637_ = l_Std_Http_URI_Query_containsEncoded(v_query_1634_, v___x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_contains___boxed(lean_object* v_query_1638_, lean_object* v_key_1639_){
_start:
{
uint8_t v_res_1640_; lean_object* v_r_1641_; 
v_res_1640_ = l_Std_Http_URI_Query_contains(v_query_1638_, v_key_1639_);
lean_dec_ref(v_key_1639_);
lean_dec_ref(v_query_1638_);
v_r_1641_ = lean_box(v_res_1640_);
return v_r_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(lean_object* v_key_1642_, lean_object* v_as_1643_, size_t v_i_1644_, size_t v_stop_1645_, lean_object* v_b_1646_){
_start:
{
lean_object* v___y_1648_; uint8_t v___x_1652_; 
v___x_1652_ = lean_usize_dec_eq(v_i_1644_, v_stop_1645_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; lean_object* v_fst_1656_; uint8_t v___x_1657_; 
v___x_1653_ = lean_array_uget_borrowed(v_as_1643_, v_i_1644_);
v_fst_1656_ = lean_ctor_get(v___x_1653_, 0);
lean_inc_ref(v_key_1642_);
lean_inc(v_fst_1656_);
v___x_1657_ = l_ByteArray_instDecidableEq(v_fst_1656_, v_key_1642_);
if (v___x_1657_ == 0)
{
goto v___jp_1654_;
}
else
{
if (v___x_1652_ == 0)
{
v___y_1648_ = v_b_1646_;
goto v___jp_1647_;
}
else
{
goto v___jp_1654_;
}
}
v___jp_1654_:
{
lean_object* v___x_1655_; 
lean_inc(v___x_1653_);
v___x_1655_ = lean_array_push(v_b_1646_, v___x_1653_);
v___y_1648_ = v___x_1655_;
goto v___jp_1647_;
}
}
else
{
lean_dec_ref(v_key_1642_);
return v_b_1646_;
}
v___jp_1647_:
{
size_t v___x_1649_; size_t v___x_1650_; 
v___x_1649_ = ((size_t)1ULL);
v___x_1650_ = lean_usize_add(v_i_1644_, v___x_1649_);
v_i_1644_ = v___x_1650_;
v_b_1646_ = v___y_1648_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0___boxed(lean_object* v_key_1658_, lean_object* v_as_1659_, lean_object* v_i_1660_, lean_object* v_stop_1661_, lean_object* v_b_1662_){
_start:
{
size_t v_i_boxed_1663_; size_t v_stop_boxed_1664_; lean_object* v_res_1665_; 
v_i_boxed_1663_ = lean_unbox_usize(v_i_1660_);
lean_dec(v_i_1660_);
v_stop_boxed_1664_ = lean_unbox_usize(v_stop_1661_);
lean_dec(v_stop_1661_);
v_res_1665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1658_, v_as_1659_, v_i_boxed_1663_, v_stop_boxed_1664_, v_b_1662_);
lean_dec_ref(v_as_1659_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded(lean_object* v_query_1666_, lean_object* v_key_1667_){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1668_ = lean_unsigned_to_nat(0u);
v___x_1669_ = lean_array_get_size(v_query_1666_);
v___x_1670_ = ((lean_object*)(l_Std_Http_URI_Query_empty___closed__0));
v___x_1671_ = lean_nat_dec_lt(v___x_1668_, v___x_1669_);
if (v___x_1671_ == 0)
{
lean_dec_ref(v_key_1667_);
return v___x_1670_;
}
else
{
uint8_t v___x_1672_; 
v___x_1672_ = lean_nat_dec_le(v___x_1669_, v___x_1669_);
if (v___x_1672_ == 0)
{
if (v___x_1671_ == 0)
{
lean_dec_ref(v_key_1667_);
return v___x_1670_;
}
else
{
size_t v___x_1673_; size_t v___x_1674_; lean_object* v___x_1675_; 
v___x_1673_ = ((size_t)0ULL);
v___x_1674_ = lean_usize_of_nat(v___x_1669_);
v___x_1675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1667_, v_query_1666_, v___x_1673_, v___x_1674_, v___x_1670_);
return v___x_1675_;
}
}
else
{
size_t v___x_1676_; size_t v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = ((size_t)0ULL);
v___x_1677_ = lean_usize_of_nat(v___x_1669_);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_URI_Query_eraseEncoded_spec__0(v_key_1667_, v_query_1666_, v___x_1676_, v___x_1677_, v___x_1670_);
return v___x_1678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_eraseEncoded___boxed(lean_object* v_query_1679_, lean_object* v_key_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Std_Http_URI_Query_eraseEncoded(v_query_1679_, v_key_1680_);
lean_dec_ref(v_query_1679_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase(lean_object* v_query_1682_, lean_object* v_key_1683_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = l_Std_Http_URI_EncodedQueryParam_encode(v_key_1683_);
v___x_1685_ = l_Std_Http_URI_Query_eraseEncoded(v_query_1682_, v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_erase___boxed(lean_object* v_query_1686_, lean_object* v_key_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Std_Http_URI_Query_erase(v_query_1686_, v_key_1687_);
lean_dec_ref(v_key_1687_);
lean_dec_ref(v_query_1686_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get(lean_object* v_query_1691_, lean_object* v_key_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Std_Http_URI_Query_find_x3f(v_query_1691_, v_key_1692_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_box(0);
return v___x_1694_;
}
else
{
lean_object* v_val_1695_; 
v_val_1695_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_val_1695_);
lean_dec_ref(v___x_1693_);
if (lean_obj_tag(v_val_1695_) == 0)
{
lean_object* v___x_1696_; 
v___x_1696_ = ((lean_object*)(l_Std_Http_URI_Query_get___closed__0));
return v___x_1696_;
}
else
{
lean_object* v_val_1697_; lean_object* v___x_1698_; 
v_val_1697_ = lean_ctor_get(v_val_1695_, 0);
lean_inc(v_val_1697_);
lean_dec_ref(v_val_1695_);
v___x_1698_ = l_Std_Http_URI_EncodedQueryParam_decode(v_val_1697_);
lean_dec(v_val_1697_);
return v___x_1698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_get___boxed(lean_object* v_query_1699_, lean_object* v_key_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Std_Http_URI_Query_get(v_query_1699_, v_key_1700_);
lean_dec_ref(v_key_1700_);
lean_dec_ref(v_query_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD(lean_object* v_query_1702_, lean_object* v_key_1703_, lean_object* v_default_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Std_Http_URI_Query_get(v_query_1702_, v_key_1703_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_inc_ref(v_default_1704_);
return v_default_1704_;
}
else
{
lean_object* v_val_1706_; 
v_val_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_val_1706_);
lean_dec_ref(v___x_1705_);
return v_val_1706_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_getD___boxed(lean_object* v_query_1707_, lean_object* v_key_1708_, lean_object* v_default_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Std_Http_URI_Query_getD(v_query_1707_, v_key_1708_, v_default_1709_);
lean_dec_ref(v_default_1709_);
lean_dec_ref(v_key_1708_);
lean_dec_ref(v_query_1707_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set(lean_object* v_query_1711_, lean_object* v_key_1712_, lean_object* v_value_1713_){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = l_Std_Http_URI_Query_erase(v_query_1711_, v_key_1712_);
v___x_1715_ = l_Std_Http_URI_Query_insert(v___x_1714_, v_key_1712_, v_value_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_set___boxed(lean_object* v_query_1716_, lean_object* v_key_1717_, lean_object* v_value_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Std_Http_URI_Query_set(v_query_1716_, v_key_1717_, v_value_1718_);
lean_dec_ref(v_value_1718_);
lean_dec_ref(v_key_1717_);
lean_dec_ref(v_query_1716_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(size_t v_sz_1720_, size_t v_i_1721_, lean_object* v_bs_1722_){
_start:
{
uint8_t v___x_1723_; 
v___x_1723_ = lean_usize_dec_lt(v_i_1721_, v_sz_1720_);
if (v___x_1723_ == 0)
{
return v_bs_1722_;
}
else
{
lean_object* v_v_1724_; lean_object* v_fst_1725_; lean_object* v_snd_1726_; lean_object* v___x_1727_; lean_object* v_bs_x27_1728_; lean_object* v___x_1729_; size_t v___x_1730_; size_t v___x_1731_; lean_object* v___x_1732_; 
v_v_1724_ = lean_array_uget_borrowed(v_bs_1722_, v_i_1721_);
v_fst_1725_ = lean_ctor_get(v_v_1724_, 0);
lean_inc(v_fst_1725_);
v_snd_1726_ = lean_ctor_get(v_v_1724_, 1);
lean_inc(v_snd_1726_);
v___x_1727_ = lean_unsigned_to_nat(0u);
v_bs_x27_1728_ = lean_array_uset(v_bs_1722_, v_i_1721_, v___x_1727_);
v___x_1729_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_1725_, v_snd_1726_);
v___x_1730_ = ((size_t)1ULL);
v___x_1731_ = lean_usize_add(v_i_1721_, v___x_1730_);
v___x_1732_ = lean_array_uset(v_bs_x27_1728_, v_i_1721_, v___x_1729_);
v_i_1721_ = v___x_1731_;
v_bs_1722_ = v___x_1732_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0___boxed(lean_object* v_sz_1734_, lean_object* v_i_1735_, lean_object* v_bs_1736_){
_start:
{
size_t v_sz_boxed_1737_; size_t v_i_boxed_1738_; lean_object* v_res_1739_; 
v_sz_boxed_1737_ = lean_unbox_usize(v_sz_1734_);
lean_dec(v_sz_1734_);
v_i_boxed_1738_ = lean_unbox_usize(v_i_1735_);
lean_dec(v_i_1735_);
v_res_1739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_boxed_1737_, v_i_boxed_1738_, v_bs_1736_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_toRawString(lean_object* v_query_1741_){
_start:
{
size_t v_sz_1742_; size_t v___x_1743_; lean_object* v_params_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_sz_1742_ = lean_array_size(v_query_1741_);
v___x_1743_ = ((size_t)0ULL);
v_params_1744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Query_toRawString_spec__0(v_sz_1742_, v___x_1743_, v_query_1741_);
v___x_1745_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_1746_ = lean_array_to_list(v_params_1744_);
v___x_1747_ = l_String_intercalate(v___x_1745_, v___x_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0(lean_object* v_x_1749_){
_start:
{
lean_object* v_fst_1750_; lean_object* v_snd_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v_fst_1750_ = lean_ctor_get(v_x_1749_, 0);
v_snd_1751_ = lean_ctor_get(v_x_1749_, 1);
v___x_1752_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
v___x_1753_ = l_Std_Http_URI_Query_insert(v___x_1752_, v_fst_1750_, v_snd_1751_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instSingletonProdString___lam__0___boxed(lean_object* v_x_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Std_Http_URI_Query_instSingletonProdString___lam__0(v_x_1754_);
lean_dec_ref(v_x_1754_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0(lean_object* v_x_1758_, lean_object* v_q_1759_){
_start:
{
lean_object* v_fst_1760_; lean_object* v_snd_1761_; lean_object* v___x_1762_; 
v_fst_1760_ = lean_ctor_get(v_x_1758_, 0);
v_snd_1761_ = lean_ctor_get(v_x_1758_, 1);
v___x_1762_ = l_Std_Http_URI_Query_insert(v_q_1759_, v_fst_1760_, v_snd_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instInsertProdString___lam__0___boxed(lean_object* v_x_1763_, lean_object* v_q_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Std_Http_URI_Query_instInsertProdString___lam__0(v_x_1763_, v_q_1764_);
lean_dec_ref(v_x_1763_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__0(lean_object* v_x_1768_){
_start:
{
lean_object* v_fst_1769_; lean_object* v_snd_1770_; lean_object* v___x_1771_; 
v_fst_1769_ = lean_ctor_get(v_x_1768_, 0);
lean_inc(v_fst_1769_);
v_snd_1770_ = lean_ctor_get(v_x_1768_, 1);
lean_inc(v_snd_1770_);
lean_dec_ref(v_x_1768_);
v___x_1771_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_1769_, v_snd_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Query_instToString___lam__1(lean_object* v___f_1773_, lean_object* v_q_1774_){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1775_ = lean_array_get_size(v_q_1774_);
v___x_1776_ = lean_unsigned_to_nat(0u);
v___x_1777_ = lean_nat_dec_eq(v___x_1775_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v_encodedParams_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1778_ = lean_array_to_list(v_q_1774_);
v___x_1779_ = lean_box(0);
v_encodedParams_1780_ = l_List_mapTR_loop___redArg(v___f_1773_, v___x_1778_, v___x_1779_);
v___x_1781_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_1782_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_1783_ = l_String_intercalate(v___x_1782_, v_encodedParams_1780_);
v___x_1784_ = lean_string_append(v___x_1781_, v___x_1783_);
lean_dec_ref(v___x_1783_);
return v___x_1784_;
}
else
{
lean_object* v___x_1785_; 
lean_dec_ref(v_q_1774_);
lean_dec_ref(v___f_1773_);
v___x_1785_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
return v___x_1785_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(lean_object* v_x_1790_, lean_object* v_x_1791_){
_start:
{
if (lean_obj_tag(v_x_1790_) == 0)
{
lean_object* v___x_1792_; 
v___x_1792_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1792_;
}
else
{
lean_object* v_val_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v_val_1793_ = lean_ctor_get(v_x_1790_, 0);
lean_inc(v_val_1793_);
lean_dec_ref(v_x_1790_);
v___x_1794_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1795_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_val_1793_);
v___x_1796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1794_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = l_Repr_addAppParen(v___x_1796_, v_x_1791_);
return v___x_1797_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0___boxed(lean_object* v_x_1798_, lean_object* v_x_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_x_1798_, v_x_1799_);
lean_dec(v_x_1799_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(lean_object* v_x_1801_, lean_object* v_x_1802_){
_start:
{
if (lean_obj_tag(v_x_1801_) == 0)
{
lean_object* v___x_1803_; 
v___x_1803_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1803_;
}
else
{
lean_object* v_val_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1815_; 
v_val_1804_ = lean_ctor_get(v_x_1801_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_x_1801_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1806_ = v_x_1801_;
v_isShared_1807_ = v_isSharedCheck_1815_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_val_1804_);
lean_dec(v_x_1801_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1815_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1808_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1809_ = l_String_quote(v_val_1804_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set_tag(v___x_1806_, 3);
lean_ctor_set(v___x_1806_, 0, v___x_1809_);
v___x_1811_ = v___x_1806_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1808_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = l_Repr_addAppParen(v___x_1812_, v_x_1802_);
return v___x_1813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2___boxed(lean_object* v_x_1816_, lean_object* v_x_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_x_1816_, v_x_1817_);
lean_dec(v_x_1817_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1_spec__4_spec__5(lean_object* v_x_1819_, lean_object* v_x_1820_, lean_object* v_x_1821_){
_start:
{
if (lean_obj_tag(v_x_1821_) == 0)
{
lean_dec(v_x_1819_);
return v_x_1820_;
}
else
{
lean_object* v_head_1822_; lean_object* v_tail_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1832_; 
v_head_1822_ = lean_ctor_get(v_x_1821_, 0);
v_tail_1823_ = lean_ctor_get(v_x_1821_, 1);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_x_1821_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1825_ = v_x_1821_;
v_isShared_1826_ = v_isSharedCheck_1832_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_tail_1823_);
lean_inc(v_head_1822_);
lean_dec(v_x_1821_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1832_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
lean_inc(v_x_1819_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set_tag(v___x_1825_, 5);
lean_ctor_set(v___x_1825_, 1, v_x_1819_);
lean_ctor_set(v___x_1825_, 0, v_x_1820_);
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_x_1820_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_x_1819_);
v___x_1828_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; 
v___x_1829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
lean_ctor_set(v___x_1829_, 1, v_head_1822_);
v_x_1820_ = v___x_1829_;
v_x_1821_ = v_tail_1823_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1_spec__4(lean_object* v_x_1833_, lean_object* v_x_1834_){
_start:
{
if (lean_obj_tag(v_x_1833_) == 0)
{
lean_object* v___x_1835_; 
lean_dec(v_x_1834_);
v___x_1835_ = lean_box(0);
return v___x_1835_;
}
else
{
lean_object* v_tail_1836_; 
v_tail_1836_ = lean_ctor_get(v_x_1833_, 1);
if (lean_obj_tag(v_tail_1836_) == 0)
{
lean_object* v_head_1837_; 
lean_dec(v_x_1834_);
v_head_1837_ = lean_ctor_get(v_x_1833_, 0);
lean_inc(v_head_1837_);
lean_dec_ref(v_x_1833_);
return v_head_1837_;
}
else
{
lean_object* v_head_1838_; lean_object* v___x_1839_; 
lean_inc(v_tail_1836_);
v_head_1838_ = lean_ctor_get(v_x_1833_, 0);
lean_inc(v_head_1838_);
lean_dec_ref(v_x_1833_);
v___x_1839_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1_spec__4_spec__5(v_x_1834_, v_head_1838_, v_tail_1836_);
return v___x_1839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1_spec__3(lean_object* v_x_1840_, lean_object* v_x_1841_){
_start:
{
if (lean_obj_tag(v_x_1840_) == 0)
{
lean_object* v___x_1842_; 
v___x_1842_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_1842_;
}
else
{
lean_object* v_val_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1855_; 
v_val_1843_ = lean_ctor_get(v_x_1840_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_x_1840_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1845_ = v_x_1840_;
v_isShared_1846_ = v_isSharedCheck_1855_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_val_1843_);
lean_dec(v_x_1840_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1855_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1847_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_1848_ = lean_string_from_utf8_unchecked(v_val_1843_);
v___x_1849_ = l_String_quote(v___x_1848_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set_tag(v___x_1845_, 3);
lean_ctor_set(v___x_1845_, 0, v___x_1849_);
v___x_1851_ = v___x_1845_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1847_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = l_Repr_addAppParen(v___x_1852_, v_x_1841_);
return v___x_1853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1_spec__3___boxed(lean_object* v_x_1856_, lean_object* v_x_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1_spec__3(v_x_1856_, v_x_1857_);
lean_dec(v_x_1857_);
return v_res_1858_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__0));
v___x_1862_ = lean_string_length(v___x_1861_);
return v___x_1862_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__2);
v___x_1864_ = lean_nat_to_int(v___x_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg(lean_object* v_x_1869_){
_start:
{
lean_object* v_fst_1870_; lean_object* v_snd_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1896_; 
v_fst_1870_ = lean_ctor_get(v_x_1869_, 0);
v_snd_1871_ = lean_ctor_get(v_x_1869_, 1);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_x_1869_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1873_ = v_x_1869_;
v_isShared_1874_ = v_isSharedCheck_1896_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_snd_1871_);
lean_inc(v_fst_1870_);
lean_dec(v_x_1869_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1896_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1875_ = lean_string_from_utf8_unchecked(v_fst_1870_);
v___x_1876_ = l_String_quote(v___x_1875_);
v___x_1877_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
v___x_1878_ = lean_box(0);
if (v_isShared_1874_ == 0)
{
lean_ctor_set_tag(v___x_1873_, 1);
lean_ctor_set(v___x_1873_, 1, v___x_1878_);
lean_ctor_set(v___x_1873_, 0, v___x_1877_);
v___x_1880_ = v___x_1873_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; lean_object* v___x_1894_; 
v___x_1881_ = lean_unsigned_to_nat(0u);
v___x_1882_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1_spec__3(v_snd_1871_, v___x_1881_);
v___x_1883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v___x_1880_);
v___x_1884_ = l_List_reverse___redArg(v___x_1883_);
v___x_1885_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1886_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1_spec__4(v___x_1884_, v___x_1885_);
v___x_1887_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__3, &l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__3_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__3);
v___x_1888_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__4));
v___x_1889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set(v___x_1889_, 1, v___x_1886_);
v___x_1890_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg___closed__5));
v___x_1891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1889_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1887_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = 0;
v___x_1894_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set_uint8(v___x_1894_, sizeof(void*)*1, v___x_1893_);
return v___x_1894_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__2_spec__6_spec__8(lean_object* v_x_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
if (lean_obj_tag(v_x_1899_) == 0)
{
lean_dec(v_x_1897_);
return v_x_1898_;
}
else
{
lean_object* v_head_1900_; lean_object* v_tail_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1911_; 
v_head_1900_ = lean_ctor_get(v_x_1899_, 0);
v_tail_1901_ = lean_ctor_get(v_x_1899_, 1);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_x_1899_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1903_ = v_x_1899_;
v_isShared_1904_ = v_isSharedCheck_1911_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_tail_1901_);
lean_inc(v_head_1900_);
lean_dec(v_x_1899_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1911_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
lean_inc(v_x_1897_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set_tag(v___x_1903_, 5);
lean_ctor_set(v___x_1903_, 1, v_x_1897_);
lean_ctor_set(v___x_1903_, 0, v_x_1898_);
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_x_1898_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_x_1897_);
v___x_1906_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg(v_head_1900_);
v___x_1908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v_x_1898_ = v___x_1908_;
v_x_1899_ = v_tail_1901_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__2_spec__6(lean_object* v_x_1912_, lean_object* v_x_1913_, lean_object* v_x_1914_){
_start:
{
if (lean_obj_tag(v_x_1914_) == 0)
{
lean_dec(v_x_1912_);
return v_x_1913_;
}
else
{
lean_object* v_head_1915_; lean_object* v_tail_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1926_; 
v_head_1915_ = lean_ctor_get(v_x_1914_, 0);
v_tail_1916_ = lean_ctor_get(v_x_1914_, 1);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_x_1914_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1918_ = v_x_1914_;
v_isShared_1919_ = v_isSharedCheck_1926_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_tail_1916_);
lean_inc(v_head_1915_);
lean_dec(v_x_1914_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1926_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
lean_inc(v_x_1912_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set_tag(v___x_1918_, 5);
lean_ctor_set(v___x_1918_, 1, v_x_1912_);
lean_ctor_set(v___x_1918_, 0, v_x_1913_);
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_x_1913_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_x_1912_);
v___x_1921_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg(v_head_1915_);
v___x_1923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__2_spec__6_spec__8(v_x_1912_, v___x_1923_, v_tail_1916_);
return v___x_1924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__2(lean_object* v_x_1927_, lean_object* v_x_1928_){
_start:
{
if (lean_obj_tag(v_x_1927_) == 0)
{
lean_object* v___x_1929_; 
lean_dec(v_x_1928_);
v___x_1929_ = lean_box(0);
return v___x_1929_;
}
else
{
lean_object* v_tail_1930_; 
v_tail_1930_ = lean_ctor_get(v_x_1927_, 1);
if (lean_obj_tag(v_tail_1930_) == 0)
{
lean_object* v_head_1931_; lean_object* v___x_1932_; 
lean_dec(v_x_1928_);
v_head_1931_ = lean_ctor_get(v_x_1927_, 0);
lean_inc(v_head_1931_);
lean_dec_ref(v_x_1927_);
v___x_1932_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg(v_head_1931_);
return v___x_1932_;
}
else
{
lean_object* v_head_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
lean_inc(v_tail_1930_);
v_head_1933_ = lean_ctor_get(v_x_1927_, 0);
lean_inc(v_head_1933_);
lean_dec_ref(v_x_1927_);
v___x_1934_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg(v_head_1933_);
v___x_1935_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__2_spec__6(v_x_1928_, v___x_1934_, v_tail_1930_);
return v___x_1935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_instReprURI_repr_spec__1(lean_object* v_xs_1936_){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1937_ = lean_array_get_size(v_xs_1936_);
v___x_1938_ = lean_unsigned_to_nat(0u);
v___x_1939_ = lean_nat_dec_eq(v___x_1937_, v___x_1938_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1940_ = lean_array_to_list(v_xs_1936_);
v___x_1941_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__1));
v___x_1942_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__2(v___x_1940_, v___x_1941_);
v___x_1943_ = lean_obj_once(&l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__3);
v___x_1944_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__4));
v___x_1945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
lean_ctor_set(v___x_1945_, 1, v___x_1942_);
v___x_1946_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__5));
v___x_1947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1943_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = l_Std_Format_fill(v___x_1948_);
return v___x_1949_;
}
else
{
lean_object* v___x_1950_; 
lean_dec_ref(v_xs_1936_);
v___x_1950_ = ((lean_object*)(l_Array_repr___at___00Std_Http_URI_instReprPath_repr_spec__0___closed__7));
return v___x_1950_;
}
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = lean_unsigned_to_nat(10u);
v___x_1961_ = lean_nat_to_int(v___x_1960_);
return v___x_1961_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_unsigned_to_nat(13u);
v___x_1966_ = lean_nat_to_int(v___x_1965_);
return v___x_1966_;
}
}
static lean_object* _init_l_Std_Http_instReprURI_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = lean_unsigned_to_nat(9u);
v___x_1974_ = lean_nat_to_int(v___x_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___redArg(lean_object* v_x_1978_){
_start:
{
lean_object* v_scheme_1979_; lean_object* v_authority_1980_; lean_object* v_path_1981_; lean_object* v_query_1982_; lean_object* v_fragment_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v_scheme_1979_ = lean_ctor_get(v_x_1978_, 0);
lean_inc_ref(v_scheme_1979_);
v_authority_1980_ = lean_ctor_get(v_x_1978_, 1);
lean_inc(v_authority_1980_);
v_path_1981_ = lean_ctor_get(v_x_1978_, 2);
lean_inc_ref(v_path_1981_);
v_query_1982_ = lean_ctor_get(v_x_1978_, 3);
lean_inc_ref(v_query_1982_);
v_fragment_1983_ = lean_ctor_get(v_x_1978_, 4);
lean_inc(v_fragment_1983_);
lean_dec_ref(v_x_1978_);
v___x_1984_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__5));
v___x_1985_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__3));
v___x_1986_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__4, &l_Std_Http_instReprURI_repr___redArg___closed__4_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__4);
v___x_1987_ = l_String_quote(v_scheme_1979_);
v___x_1988_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
v___x_1989_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1986_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = 0;
v___x_1991_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set_uint8(v___x_1991_, sizeof(void*)*1, v___x_1990_);
v___x_1992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1985_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__9));
v___x_1994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = lean_box(1);
v___x_1996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1994_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__6));
v___x_1998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1996_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
v___x_1999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
lean_ctor_set(v___x_1999_, 1, v___x_1984_);
v___x_2000_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__7, &l_Std_Http_instReprURI_repr___redArg___closed__7_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__7);
v___x_2001_ = lean_unsigned_to_nat(0u);
v___x_2002_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__0(v_authority_1980_, v___x_2001_);
v___x_2003_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2000_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
lean_ctor_set_uint8(v___x_2004_, sizeof(void*)*1, v___x_1990_);
v___x_2005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_1999_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
lean_ctor_set(v___x_2006_, 1, v___x_1993_);
v___x_2007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
lean_ctor_set(v___x_2007_, 1, v___x_1995_);
v___x_2008_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__9));
v___x_2009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2007_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
lean_ctor_set(v___x_2010_, 1, v___x_1984_);
v___x_2011_ = lean_obj_once(&l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6, &l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6_once, _init_l_Std_Http_URI_instReprAuthority_repr___redArg___closed__6);
v___x_2012_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_1981_);
v___x_2013_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set_uint8(v___x_2014_, sizeof(void*)*1, v___x_1990_);
v___x_2015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2010_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
v___x_2016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
lean_ctor_set(v___x_2016_, 1, v___x_1993_);
v___x_2017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
lean_ctor_set(v___x_2017_, 1, v___x_1995_);
v___x_2018_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__11));
v___x_2019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2017_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
v___x_2020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
lean_ctor_set(v___x_2020_, 1, v___x_1984_);
v___x_2021_ = lean_obj_once(&l_Std_Http_instReprURI_repr___redArg___closed__12, &l_Std_Http_instReprURI_repr___redArg___closed__12_once, _init_l_Std_Http_instReprURI_repr___redArg___closed__12);
v___x_2022_ = l_Array_repr___at___00Std_Http_instReprURI_repr_spec__1(v_query_1982_);
v___x_2023_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2021_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
lean_ctor_set_uint8(v___x_2024_, sizeof(void*)*1, v___x_1990_);
v___x_2025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2020_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
lean_ctor_set(v___x_2026_, 1, v___x_1993_);
v___x_2027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
lean_ctor_set(v___x_2027_, 1, v___x_1995_);
v___x_2028_ = ((lean_object*)(l_Std_Http_instReprURI_repr___redArg___closed__14));
v___x_2029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2027_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
lean_ctor_set(v___x_2030_, 1, v___x_1984_);
v___x_2031_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__7);
v___x_2032_ = l_Option_repr___at___00Std_Http_instReprURI_repr_spec__2(v_fragment_1983_, v___x_2001_);
v___x_2033_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2031_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*1, v___x_1990_);
v___x_2035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2030_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v___x_2036_ = lean_obj_once(&l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14, &l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14_once, _init_l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__14);
v___x_2037_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__15));
v___x_2038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
lean_ctor_set(v___x_2038_, 1, v___x_2035_);
v___x_2039_ = ((lean_object*)(l_Std_Http_URI_instReprUserInfo_repr___redArg___closed__16));
v___x_2040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2038_);
lean_ctor_set(v___x_2040_, 1, v___x_2039_);
v___x_2041_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2036_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*1, v___x_1990_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr(lean_object* v_x_2043_, lean_object* v_prec_2044_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Std_Http_instReprURI_repr___redArg(v_x_2043_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprURI_repr___boxed(lean_object* v_x_2046_, lean_object* v_prec_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Std_Http_instReprURI_repr(v_x_2046_, v_prec_2047_);
lean_dec(v_prec_2047_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1(lean_object* v_x_2049_, lean_object* v_x_2050_){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___redArg(v_x_2049_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1___boxed(lean_object* v_x_2052_, lean_object* v_x_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_instReprURI_repr_spec__1_spec__1(v_x_2052_, v_x_2053_);
lean_dec(v_x_2053_);
return v_res_2054_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(lean_object* v_x_2066_, lean_object* v_x_2067_){
_start:
{
if (lean_obj_tag(v_x_2066_) == 0)
{
if (lean_obj_tag(v_x_2067_) == 0)
{
uint8_t v___x_2068_; 
v___x_2068_ = 1;
return v___x_2068_;
}
else
{
uint8_t v___x_2069_; 
lean_dec_ref(v_x_2067_);
v___x_2069_ = 0;
return v___x_2069_;
}
}
else
{
if (lean_obj_tag(v_x_2067_) == 0)
{
uint8_t v___x_2070_; 
lean_dec_ref(v_x_2066_);
v___x_2070_ = 0;
return v___x_2070_;
}
else
{
lean_object* v_val_2071_; lean_object* v_val_2072_; uint8_t v___x_2073_; 
v_val_2071_ = lean_ctor_get(v_x_2066_, 0);
lean_inc(v_val_2071_);
lean_dec_ref(v_x_2066_);
v_val_2072_ = lean_ctor_get(v_x_2067_, 0);
lean_inc(v_val_2072_);
lean_dec_ref(v_x_2067_);
v___x_2073_ = l_Std_Http_URI_instBEqAuthority_beq(v_val_2071_, v_val_2072_);
return v___x_2073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0___boxed(lean_object* v_x_2074_, lean_object* v_x_2075_){
_start:
{
uint8_t v_res_2076_; lean_object* v_r_2077_; 
v_res_2076_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_x_2074_, v_x_2075_);
v_r_2077_ = lean_box(v_res_2076_);
return v_r_2077_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(lean_object* v_x_2078_, lean_object* v_x_2079_){
_start:
{
if (lean_obj_tag(v_x_2078_) == 0)
{
if (lean_obj_tag(v_x_2079_) == 0)
{
uint8_t v___x_2080_; 
v___x_2080_ = 1;
return v___x_2080_;
}
else
{
uint8_t v___x_2081_; 
lean_dec_ref(v_x_2079_);
v___x_2081_ = 0;
return v___x_2081_;
}
}
else
{
if (lean_obj_tag(v_x_2079_) == 0)
{
uint8_t v___x_2082_; 
lean_dec_ref(v_x_2078_);
v___x_2082_ = 0;
return v___x_2082_;
}
else
{
lean_object* v_val_2083_; lean_object* v_val_2084_; uint8_t v___x_2085_; 
v_val_2083_ = lean_ctor_get(v_x_2078_, 0);
lean_inc(v_val_2083_);
lean_dec_ref(v_x_2078_);
v_val_2084_ = lean_ctor_get(v_x_2079_, 0);
lean_inc(v_val_2084_);
lean_dec_ref(v_x_2079_);
v___x_2085_ = l_ByteArray_instDecidableEq(v_val_2083_, v_val_2084_);
return v___x_2085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1___boxed(lean_object* v_x_2086_, lean_object* v_x_2087_){
_start:
{
uint8_t v_res_2088_; lean_object* v_r_2089_; 
v_res_2088_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_x_2086_, v_x_2087_);
v_r_2089_ = lean_box(v_res_2088_);
return v_r_2089_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__3(lean_object* v_x_2090_, lean_object* v_x_2091_){
_start:
{
if (lean_obj_tag(v_x_2090_) == 0)
{
if (lean_obj_tag(v_x_2091_) == 0)
{
uint8_t v___x_2092_; 
v___x_2092_ = 1;
return v___x_2092_;
}
else
{
uint8_t v___x_2093_; 
v___x_2093_ = 0;
return v___x_2093_;
}
}
else
{
if (lean_obj_tag(v_x_2091_) == 0)
{
uint8_t v___x_2094_; 
v___x_2094_ = 0;
return v___x_2094_;
}
else
{
lean_object* v_val_2095_; lean_object* v_val_2096_; uint8_t v___x_2097_; 
v_val_2095_ = lean_ctor_get(v_x_2090_, 0);
v_val_2096_ = lean_ctor_get(v_x_2091_, 0);
v___x_2097_ = lean_string_dec_eq(v_val_2095_, v_val_2096_);
return v___x_2097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__3___boxed(lean_object* v_x_2098_, lean_object* v_x_2099_){
_start:
{
uint8_t v_res_2100_; lean_object* v_r_2101_; 
v_res_2100_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__3(v_x_2098_, v_x_2099_);
lean_dec(v_x_2099_);
lean_dec(v_x_2098_);
v_r_2101_ = lean_box(v_res_2100_);
return v_r_2101_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_instBEqURI_beq_spec__2___redArg(lean_object* v_xs_2102_, lean_object* v_ys_2103_, lean_object* v_x_2104_){
_start:
{
lean_object* v_zero_2105_; uint8_t v_isZero_2106_; 
v_zero_2105_ = lean_unsigned_to_nat(0u);
v_isZero_2106_ = lean_nat_dec_eq(v_x_2104_, v_zero_2105_);
if (v_isZero_2106_ == 1)
{
lean_dec(v_x_2104_);
return v_isZero_2106_;
}
else
{
lean_object* v_one_2107_; lean_object* v_n_2108_; uint8_t v___y_2110_; lean_object* v___x_2112_; lean_object* v_fst_2113_; lean_object* v_snd_2114_; lean_object* v___x_2115_; lean_object* v_fst_2116_; lean_object* v_snd_2117_; uint8_t v___x_2118_; 
v_one_2107_ = lean_unsigned_to_nat(1u);
v_n_2108_ = lean_nat_sub(v_x_2104_, v_one_2107_);
lean_dec(v_x_2104_);
v___x_2112_ = lean_array_fget_borrowed(v_xs_2102_, v_n_2108_);
v_fst_2113_ = lean_ctor_get(v___x_2112_, 0);
v_snd_2114_ = lean_ctor_get(v___x_2112_, 1);
v___x_2115_ = lean_array_fget_borrowed(v_ys_2103_, v_n_2108_);
v_fst_2116_ = lean_ctor_get(v___x_2115_, 0);
v_snd_2117_ = lean_ctor_get(v___x_2115_, 1);
lean_inc(v_fst_2116_);
lean_inc(v_fst_2113_);
v___x_2118_ = l_ByteArray_instDecidableEq(v_fst_2113_, v_fst_2116_);
if (v___x_2118_ == 0)
{
v___y_2110_ = v___x_2118_;
goto v___jp_2109_;
}
else
{
uint8_t v___x_2119_; 
lean_inc(v_snd_2117_);
lean_inc(v_snd_2114_);
v___x_2119_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__1(v_snd_2114_, v_snd_2117_);
v___y_2110_ = v___x_2119_;
goto v___jp_2109_;
}
v___jp_2109_:
{
if (v___y_2110_ == 0)
{
lean_dec(v_n_2108_);
return v___y_2110_;
}
else
{
v_x_2104_ = v_n_2108_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_instBEqURI_beq_spec__2___redArg___boxed(lean_object* v_xs_2120_, lean_object* v_ys_2121_, lean_object* v_x_2122_){
_start:
{
uint8_t v_res_2123_; lean_object* v_r_2124_; 
v_res_2123_ = l_Array_isEqvAux___at___00Std_Http_instBEqURI_beq_spec__2___redArg(v_xs_2120_, v_ys_2121_, v_x_2122_);
lean_dec_ref(v_ys_2121_);
lean_dec_ref(v_xs_2120_);
v_r_2124_ = lean_box(v_res_2123_);
return v_r_2124_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instBEqURI_beq(lean_object* v_x_2125_, lean_object* v_x_2126_){
_start:
{
lean_object* v_scheme_2127_; lean_object* v_authority_2128_; lean_object* v_path_2129_; lean_object* v_query_2130_; lean_object* v_fragment_2131_; lean_object* v_scheme_2132_; lean_object* v_authority_2133_; lean_object* v_path_2134_; lean_object* v_query_2135_; lean_object* v_fragment_2136_; uint8_t v___x_2137_; 
v_scheme_2127_ = lean_ctor_get(v_x_2125_, 0);
lean_inc_ref(v_scheme_2127_);
v_authority_2128_ = lean_ctor_get(v_x_2125_, 1);
lean_inc(v_authority_2128_);
v_path_2129_ = lean_ctor_get(v_x_2125_, 2);
lean_inc_ref(v_path_2129_);
v_query_2130_ = lean_ctor_get(v_x_2125_, 3);
lean_inc_ref(v_query_2130_);
v_fragment_2131_ = lean_ctor_get(v_x_2125_, 4);
lean_inc(v_fragment_2131_);
lean_dec_ref(v_x_2125_);
v_scheme_2132_ = lean_ctor_get(v_x_2126_, 0);
lean_inc_ref(v_scheme_2132_);
v_authority_2133_ = lean_ctor_get(v_x_2126_, 1);
lean_inc(v_authority_2133_);
v_path_2134_ = lean_ctor_get(v_x_2126_, 2);
lean_inc_ref(v_path_2134_);
v_query_2135_ = lean_ctor_get(v_x_2126_, 3);
lean_inc_ref(v_query_2135_);
v_fragment_2136_ = lean_ctor_get(v_x_2126_, 4);
lean_inc(v_fragment_2136_);
lean_dec_ref(v_x_2126_);
v___x_2137_ = lean_string_dec_eq(v_scheme_2127_, v_scheme_2132_);
lean_dec_ref(v_scheme_2132_);
lean_dec_ref(v_scheme_2127_);
if (v___x_2137_ == 0)
{
lean_dec(v_fragment_2136_);
lean_dec_ref(v_query_2135_);
lean_dec_ref(v_path_2134_);
lean_dec(v_authority_2133_);
lean_dec(v_fragment_2131_);
lean_dec_ref(v_query_2130_);
lean_dec_ref(v_path_2129_);
lean_dec(v_authority_2128_);
return v___x_2137_;
}
else
{
uint8_t v___x_2138_; 
v___x_2138_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__0(v_authority_2128_, v_authority_2133_);
if (v___x_2138_ == 0)
{
lean_dec(v_fragment_2136_);
lean_dec_ref(v_query_2135_);
lean_dec_ref(v_path_2134_);
lean_dec(v_fragment_2131_);
lean_dec_ref(v_query_2130_);
lean_dec_ref(v_path_2129_);
return v___x_2138_;
}
else
{
uint8_t v___x_2139_; 
v___x_2139_ = l_Std_Http_URI_instBEqPath_beq(v_path_2129_, v_path_2134_);
lean_dec_ref(v_path_2134_);
lean_dec_ref(v_path_2129_);
if (v___x_2139_ == 0)
{
lean_dec(v_fragment_2136_);
lean_dec_ref(v_query_2135_);
lean_dec(v_fragment_2131_);
lean_dec_ref(v_query_2130_);
return v___x_2139_;
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2140_ = lean_array_get_size(v_query_2130_);
v___x_2141_ = lean_array_get_size(v_query_2135_);
v___x_2142_ = lean_nat_dec_eq(v___x_2140_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_dec(v_fragment_2136_);
lean_dec_ref(v_query_2135_);
lean_dec(v_fragment_2131_);
lean_dec_ref(v_query_2130_);
return v___x_2142_;
}
else
{
uint8_t v___x_2143_; 
v___x_2143_ = l_Array_isEqvAux___at___00Std_Http_instBEqURI_beq_spec__2___redArg(v_query_2130_, v_query_2135_, v___x_2140_);
lean_dec_ref(v_query_2135_);
lean_dec_ref(v_query_2130_);
if (v___x_2143_ == 0)
{
lean_dec(v_fragment_2136_);
lean_dec(v_fragment_2131_);
return v___x_2143_;
}
else
{
uint8_t v___x_2144_; 
v___x_2144_ = l_Option_instBEq_beq___at___00Std_Http_instBEqURI_beq_spec__3(v_fragment_2131_, v_fragment_2136_);
lean_dec(v_fragment_2136_);
lean_dec(v_fragment_2131_);
return v___x_2144_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqURI_beq___boxed(lean_object* v_x_2145_, lean_object* v_x_2146_){
_start:
{
uint8_t v_res_2147_; lean_object* v_r_2148_; 
v_res_2147_ = l_Std_Http_instBEqURI_beq(v_x_2145_, v_x_2146_);
v_r_2148_ = lean_box(v_res_2147_);
return v_r_2148_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_instBEqURI_beq_spec__2(lean_object* v_xs_2149_, lean_object* v_ys_2150_, lean_object* v_hsz_2151_, lean_object* v_x_2152_, lean_object* v_x_2153_){
_start:
{
uint8_t v___x_2154_; 
v___x_2154_ = l_Array_isEqvAux___at___00Std_Http_instBEqURI_beq_spec__2___redArg(v_xs_2149_, v_ys_2150_, v_x_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_instBEqURI_beq_spec__2___boxed(lean_object* v_xs_2155_, lean_object* v_ys_2156_, lean_object* v_hsz_2157_, lean_object* v_x_2158_, lean_object* v_x_2159_){
_start:
{
uint8_t v_res_2160_; lean_object* v_r_2161_; 
v_res_2160_ = l_Array_isEqvAux___at___00Std_Http_instBEqURI_beq_spec__2(v_xs_2155_, v_ys_2156_, v_hsz_2157_, v_x_2158_, v_x_2159_);
lean_dec_ref(v_ys_2156_);
lean_dec_ref(v_xs_2155_);
v_r_2161_ = lean_box(v_res_2160_);
return v_r_2161_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instToStringURI___lam__2(lean_object* v___f_2166_, lean_object* v___f_2167_, lean_object* v_uri_2168_){
_start:
{
lean_object* v_scheme_2169_; lean_object* v_authority_2170_; lean_object* v_path_2171_; lean_object* v_query_2172_; lean_object* v_fragment_2173_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2210_; 
v_scheme_2169_ = lean_ctor_get(v_uri_2168_, 0);
lean_inc_ref(v_scheme_2169_);
v_authority_2170_ = lean_ctor_get(v_uri_2168_, 1);
lean_inc(v_authority_2170_);
v_path_2171_ = lean_ctor_get(v_uri_2168_, 2);
lean_inc_ref(v_path_2171_);
v_query_2172_ = lean_ctor_get(v_uri_2168_, 3);
lean_inc_ref(v_query_2172_);
v_fragment_2173_ = lean_ctor_get(v_uri_2168_, 4);
lean_inc(v_fragment_2173_);
lean_dec_ref(v_uri_2168_);
if (lean_obj_tag(v_authority_2170_) == 0)
{
lean_object* v___x_2221_; 
v___x_2221_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2210_ = v___x_2221_;
goto v___jp_2209_;
}
else
{
lean_object* v_val_2222_; lean_object* v_userInfo_2223_; lean_object* v_host_2224_; lean_object* v_port_2225_; lean_object* v___x_2226_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2245_; 
v_val_2222_ = lean_ctor_get(v_authority_2170_, 0);
lean_inc(v_val_2222_);
lean_dec_ref(v_authority_2170_);
v_userInfo_2223_ = lean_ctor_get(v_val_2222_, 0);
lean_inc(v_userInfo_2223_);
v_host_2224_ = lean_ctor_get(v_val_2222_, 1);
lean_inc_ref(v_host_2224_);
v_port_2225_ = lean_ctor_get(v_val_2222_, 2);
lean_inc(v_port_2225_);
lean_dec(v_val_2222_);
v___x_2226_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__1));
if (lean_obj_tag(v_userInfo_2223_) == 0)
{
lean_object* v___x_2255_; 
v___x_2255_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2245_ = v___x_2255_;
goto v___jp_2244_;
}
else
{
lean_object* v_val_2256_; lean_object* v_password_2257_; 
v_val_2256_ = lean_ctor_get(v_userInfo_2223_, 0);
lean_inc(v_val_2256_);
lean_dec_ref(v_userInfo_2223_);
v_password_2257_ = lean_ctor_get(v_val_2256_, 1);
if (lean_obj_tag(v_password_2257_) == 0)
{
lean_object* v_username_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v_username_2258_ = lean_ctor_get(v_val_2256_, 0);
lean_inc_ref(v_username_2258_);
lean_dec(v_val_2256_);
v___x_2259_ = lean_string_from_utf8_unchecked(v_username_2258_);
v___x_2260_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2261_ = lean_string_append(v___x_2259_, v___x_2260_);
v___y_2245_ = v___x_2261_;
goto v___jp_2244_;
}
else
{
lean_object* v_username_2262_; lean_object* v_val_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_inc_ref(v_password_2257_);
v_username_2262_ = lean_ctor_get(v_val_2256_, 0);
lean_inc_ref(v_username_2262_);
lean_dec(v_val_2256_);
v_val_2263_ = lean_ctor_get(v_password_2257_, 0);
lean_inc(v_val_2263_);
lean_dec_ref(v_password_2257_);
v___x_2264_ = lean_string_from_utf8_unchecked(v_username_2262_);
v___x_2265_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2266_ = lean_string_append(v___x_2264_, v___x_2265_);
v___x_2267_ = lean_string_from_utf8_unchecked(v_val_2263_);
v___x_2268_ = lean_string_append(v___x_2266_, v___x_2267_);
lean_dec_ref(v___x_2267_);
v___x_2269_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_2270_ = lean_string_append(v___x_2268_, v___x_2269_);
v___y_2245_ = v___x_2270_;
goto v___jp_2244_;
}
}
v___jp_2227_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = lean_string_append(v___y_2228_, v___y_2229_);
lean_dec_ref(v___y_2229_);
v___x_2232_ = lean_string_append(v___x_2231_, v___y_2230_);
lean_dec_ref(v___y_2230_);
v___x_2233_ = lean_string_append(v___x_2226_, v___x_2232_);
lean_dec_ref(v___x_2232_);
v___y_2210_ = v___x_2233_;
goto v___jp_2209_;
}
v___jp_2234_:
{
switch(lean_obj_tag(v_port_2225_))
{
case 0:
{
lean_object* v___x_2237_; 
v___x_2237_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2228_ = v___y_2235_;
v___y_2229_ = v___y_2236_;
v___y_2230_ = v___x_2237_;
goto v___jp_2227_;
}
case 1:
{
lean_object* v___x_2238_; 
v___x_2238_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_2228_ = v___y_2235_;
v___y_2229_ = v___y_2236_;
v___y_2230_ = v___x_2238_;
goto v___jp_2227_;
}
default: 
{
uint16_t v_port_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v_port_2239_ = lean_ctor_get_uint16(v_port_2225_, 0);
lean_dec_ref(v_port_2225_);
v___x_2240_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2241_ = lean_uint16_to_nat(v_port_2239_);
v___x_2242_ = l_Nat_reprFast(v___x_2241_);
v___x_2243_ = lean_string_append(v___x_2240_, v___x_2242_);
lean_dec_ref(v___x_2242_);
v___y_2228_ = v___y_2235_;
v___y_2229_ = v___y_2236_;
v___y_2230_ = v___x_2243_;
goto v___jp_2227_;
}
}
}
v___jp_2244_:
{
switch(lean_obj_tag(v_host_2224_))
{
case 0:
{
lean_object* v_name_2246_; 
v_name_2246_ = lean_ctor_get(v_host_2224_, 0);
lean_inc_ref(v_name_2246_);
lean_dec_ref(v_host_2224_);
v___y_2235_ = v___y_2245_;
v___y_2236_ = v_name_2246_;
goto v___jp_2234_;
}
case 1:
{
lean_object* v_ipv4_2247_; lean_object* v___x_2248_; 
v_ipv4_2247_ = lean_ctor_get(v_host_2224_, 0);
lean_inc_ref(v_ipv4_2247_);
lean_dec_ref(v_host_2224_);
v___x_2248_ = lean_uv_ntop_v4(v_ipv4_2247_);
lean_dec_ref(v_ipv4_2247_);
v___y_2235_ = v___y_2245_;
v___y_2236_ = v___x_2248_;
goto v___jp_2234_;
}
default: 
{
lean_object* v_ipv6_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v_ipv6_2249_ = lean_ctor_get(v_host_2224_, 0);
lean_inc_ref(v_ipv6_2249_);
lean_dec_ref(v_host_2224_);
v___x_2250_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_2251_ = lean_uv_ntop_v6(v_ipv6_2249_);
lean_dec_ref(v_ipv6_2249_);
v___x_2252_ = lean_string_append(v___x_2250_, v___x_2251_);
lean_dec_ref(v___x_2251_);
v___x_2253_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_2254_ = lean_string_append(v___x_2252_, v___x_2253_);
v___y_2235_ = v___y_2245_;
v___y_2236_ = v___x_2254_;
goto v___jp_2234_;
}
}
}
}
v___jp_2174_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2179_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_2180_ = lean_string_append(v_scheme_2169_, v___x_2179_);
v___x_2181_ = lean_string_append(v___x_2180_, v___y_2175_);
lean_dec_ref(v___y_2175_);
v___x_2182_ = lean_string_append(v___x_2181_, v___y_2176_);
lean_dec_ref(v___y_2176_);
v___x_2183_ = lean_string_append(v___x_2182_, v___y_2177_);
lean_dec_ref(v___y_2177_);
v___x_2184_ = lean_string_append(v___x_2183_, v___y_2178_);
lean_dec_ref(v___y_2178_);
return v___x_2184_;
}
v___jp_2185_:
{
if (lean_obj_tag(v_fragment_2173_) == 0)
{
lean_object* v___x_2189_; 
v___x_2189_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2175_ = v___y_2186_;
v___y_2176_ = v___y_2187_;
v___y_2177_ = v___y_2188_;
v___y_2178_ = v___x_2189_;
goto v___jp_2174_;
}
else
{
lean_object* v_val_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v_val_2190_ = lean_ctor_get(v_fragment_2173_, 0);
lean_inc(v_val_2190_);
lean_dec_ref(v_fragment_2173_);
v___x_2191_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__0));
v___x_2192_ = l_Std_Http_URI_EncodedFragment_encode(v_val_2190_);
lean_dec(v_val_2190_);
v___x_2193_ = lean_string_from_utf8_unchecked(v___x_2192_);
v___x_2194_ = lean_string_append(v___x_2191_, v___x_2193_);
lean_dec_ref(v___x_2193_);
v___y_2175_ = v___y_2186_;
v___y_2176_ = v___y_2187_;
v___y_2177_ = v___y_2188_;
v___y_2178_ = v___x_2194_;
goto v___jp_2174_;
}
}
v___jp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2198_ = lean_array_get_size(v_query_2172_);
v___x_2199_ = lean_unsigned_to_nat(0u);
v___x_2200_ = lean_nat_dec_eq(v___x_2198_, v___x_2199_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v_encodedParams_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2201_ = lean_array_to_list(v_query_2172_);
v___x_2202_ = lean_box(0);
v_encodedParams_2203_ = l_List_mapTR_loop___redArg(v___f_2166_, v___x_2201_, v___x_2202_);
v___x_2204_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2205_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2206_ = l_String_intercalate(v___x_2205_, v_encodedParams_2203_);
v___x_2207_ = lean_string_append(v___x_2204_, v___x_2206_);
lean_dec_ref(v___x_2206_);
v___y_2186_ = v___y_2196_;
v___y_2187_ = v___y_2197_;
v___y_2188_ = v___x_2207_;
goto v___jp_2185_;
}
else
{
lean_object* v___x_2208_; 
lean_dec_ref(v_query_2172_);
lean_dec_ref(v___f_2166_);
v___x_2208_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2186_ = v___y_2196_;
v___y_2187_ = v___y_2197_;
v___y_2188_ = v___x_2208_;
goto v___jp_2185_;
}
}
v___jp_2209_:
{
lean_object* v_segments_2211_; uint8_t v_absolute_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; size_t v_sz_2215_; size_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v_result_2219_; 
v_segments_2211_ = lean_ctor_get(v_path_2171_, 0);
lean_inc_ref(v_segments_2211_);
v_absolute_2212_ = lean_ctor_get_uint8(v_path_2171_, sizeof(void*)*1);
lean_dec_ref(v_path_2171_);
v___x_2213_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_2214_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_2215_ = lean_array_size(v_segments_2211_);
v___x_2216_ = ((size_t)0ULL);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2214_, v___f_2167_, v_sz_2215_, v___x_2216_, v_segments_2211_);
v___x_2218_ = lean_array_to_list(v___x_2217_);
v_result_2219_ = l_String_intercalate(v___x_2213_, v___x_2218_);
if (v_absolute_2212_ == 0)
{
v___y_2196_ = v___y_2210_;
v___y_2197_ = v_result_2219_;
goto v___jp_2195_;
}
else
{
lean_object* v___x_2220_; 
v___x_2220_ = lean_string_append(v___x_2213_, v_result_2219_);
lean_dec_ref(v_result_2219_);
v___y_2196_ = v___y_2210_;
v___y_2197_ = v___x_2220_;
goto v___jp_2195_;
}
}
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedBuilder_default___closed__1(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2277_ = ((lean_object*)(l_Std_Http_URI_instInhabitedBuilder_default___closed__0));
v___x_2278_ = lean_box(0);
v___x_2279_ = lean_box(0);
v___x_2280_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
lean_ctor_set(v___x_2280_, 2, v___x_2279_);
lean_ctor_set(v___x_2280_, 3, v___x_2278_);
lean_ctor_set(v___x_2280_, 4, v___x_2277_);
lean_ctor_set(v___x_2280_, 5, v___x_2277_);
lean_ctor_set(v___x_2280_, 6, v___x_2279_);
return v___x_2280_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedBuilder_default(void){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = lean_obj_once(&l_Std_Http_URI_instInhabitedBuilder_default___closed__1, &l_Std_Http_URI_instInhabitedBuilder_default___closed__1_once, _init_l_Std_Http_URI_instInhabitedBuilder_default___closed__1);
return v___x_2281_;
}
}
static lean_object* _init_l_Std_Http_URI_instInhabitedBuilder(void){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Std_Http_URI_instInhabitedBuilder_default;
return v___x_2282_;
}
}
static lean_object* _init_l_Std_Http_URI_Builder_empty___closed__1(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2285_ = ((lean_object*)(l_Std_Http_URI_Builder_empty___closed__0));
v___x_2286_ = lean_box(0);
v___x_2287_ = lean_box(0);
v___x_2288_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
lean_ctor_set(v___x_2288_, 2, v___x_2287_);
lean_ctor_set(v___x_2288_, 3, v___x_2286_);
lean_ctor_set(v___x_2288_, 4, v___x_2285_);
lean_ctor_set(v___x_2288_, 5, v___x_2285_);
lean_ctor_set(v___x_2288_, 6, v___x_2287_);
return v___x_2288_;
}
}
static lean_object* _init_l_Std_Http_URI_Builder_empty(void){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_obj_once(&l_Std_Http_URI_Builder_empty___closed__1, &l_Std_Http_URI_Builder_empty___closed__1_once, _init_l_Std_Http_URI_Builder_empty___closed__1);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x3f(lean_object* v_b_2290_, lean_object* v_scheme_2291_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Std_Http_URI_Scheme_ofString_x3f(v_scheme_2291_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v___x_2293_; 
lean_dec_ref(v_b_2290_);
v___x_2293_ = lean_box(0);
return v___x_2293_;
}
else
{
lean_object* v_userInfo_2294_; lean_object* v_host_2295_; lean_object* v_port_2296_; lean_object* v_pathSegments_2297_; lean_object* v_query_2298_; lean_object* v_fragment_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2314_; 
v_userInfo_2294_ = lean_ctor_get(v_b_2290_, 1);
v_host_2295_ = lean_ctor_get(v_b_2290_, 2);
v_port_2296_ = lean_ctor_get(v_b_2290_, 3);
v_pathSegments_2297_ = lean_ctor_get(v_b_2290_, 4);
v_query_2298_ = lean_ctor_get(v_b_2290_, 5);
v_fragment_2299_ = lean_ctor_get(v_b_2290_, 6);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_b_2290_);
if (v_isSharedCheck_2314_ == 0)
{
lean_object* v_unused_2315_; 
v_unused_2315_ = lean_ctor_get(v_b_2290_, 0);
lean_dec(v_unused_2315_);
v___x_2301_ = v_b_2290_;
v_isShared_2302_ = v_isSharedCheck_2314_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_fragment_2299_);
lean_inc(v_query_2298_);
lean_inc(v_pathSegments_2297_);
lean_inc(v_port_2296_);
lean_inc(v_host_2295_);
lean_inc(v_userInfo_2294_);
lean_dec(v_b_2290_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2314_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
lean_inc_ref(v___x_2292_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2292_);
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2292_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_userInfo_2294_);
lean_ctor_set(v_reuseFailAlloc_2313_, 2, v_host_2295_);
lean_ctor_set(v_reuseFailAlloc_2313_, 3, v_port_2296_);
lean_ctor_set(v_reuseFailAlloc_2313_, 4, v_pathSegments_2297_);
lean_ctor_set(v_reuseFailAlloc_2313_, 5, v_query_2298_);
lean_ctor_set(v_reuseFailAlloc_2313_, 6, v_fragment_2299_);
v___x_2304_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2311_ == 0)
{
lean_object* v_unused_2312_; 
v_unused_2312_ = lean_ctor_get(v___x_2292_, 0);
lean_dec(v_unused_2312_);
v___x_2306_ = v___x_2292_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_dec(v___x_2292_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(lean_object* v_msg_2316_){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = l_Std_Http_URI_instInhabitedBuilder_default;
v___x_2318_ = lean_panic_fn(v___x_2317_, v_msg_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setScheme_x21(lean_object* v_b_2320_, lean_object* v_scheme_2321_){
_start:
{
lean_object* v___x_2322_; 
lean_inc_ref(v_scheme_2321_);
v___x_2322_ = l_Std_Http_URI_Builder_setScheme_x3f(v_b_2320_, v_scheme_2321_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2323_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2324_ = ((lean_object*)(l_Std_Http_URI_Builder_setScheme_x21___closed__0));
v___x_2325_ = lean_unsigned_to_nat(677u);
v___x_2326_ = lean_unsigned_to_nat(14u);
v___x_2327_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__2));
v___x_2328_ = l_String_quote(v_scheme_2321_);
v___x_2329_ = lean_string_append(v___x_2327_, v___x_2328_);
lean_dec_ref(v___x_2328_);
v___x_2330_ = l_mkPanicMessageWithDecl(v___x_2323_, v___x_2324_, v___x_2325_, v___x_2326_, v___x_2329_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2330_);
return v___x_2331_;
}
else
{
lean_object* v_val_2332_; 
lean_dec_ref(v_scheme_2321_);
v_val_2332_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_val_2332_);
lean_dec_ref(v___x_2322_);
return v_val_2332_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo(lean_object* v_b_2333_, lean_object* v_username_2334_, lean_object* v_password_2335_){
_start:
{
lean_object* v_scheme_2336_; lean_object* v_host_2337_; lean_object* v_port_2338_; lean_object* v_pathSegments_2339_; lean_object* v_query_2340_; lean_object* v_fragment_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2364_; 
v_scheme_2336_ = lean_ctor_get(v_b_2333_, 0);
v_host_2337_ = lean_ctor_get(v_b_2333_, 2);
v_port_2338_ = lean_ctor_get(v_b_2333_, 3);
v_pathSegments_2339_ = lean_ctor_get(v_b_2333_, 4);
v_query_2340_ = lean_ctor_get(v_b_2333_, 5);
v_fragment_2341_ = lean_ctor_get(v_b_2333_, 6);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_b_2333_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; 
v_unused_2365_ = lean_ctor_get(v_b_2333_, 1);
lean_dec(v_unused_2365_);
v___x_2343_ = v_b_2333_;
v_isShared_2344_ = v_isSharedCheck_2364_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_fragment_2341_);
lean_inc(v_query_2340_);
lean_inc(v_pathSegments_2339_);
lean_inc(v_port_2338_);
lean_inc(v_host_2337_);
lean_inc(v_scheme_2336_);
lean_dec(v_b_2333_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2364_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___y_2346_; lean_object* v___x_2351_; 
v___x_2351_ = l_Std_Http_URI_EncodedUserInfo_encode(v_username_2334_);
if (lean_obj_tag(v_password_2335_) == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2351_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
v___y_2346_ = v___x_2353_;
goto v___jp_2345_;
}
else
{
lean_object* v_val_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2363_; 
v_val_2354_ = lean_ctor_get(v_password_2335_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_password_2335_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2356_ = v_password_2335_;
v_isShared_2357_ = v_isSharedCheck_2363_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_val_2354_);
lean_dec(v_password_2335_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2363_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2358_ = l_Std_Http_URI_EncodedUserInfo_encode(v_val_2354_);
lean_dec(v_val_2354_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v___x_2358_);
v___x_2360_ = v___x_2356_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2361_; 
v___x_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2351_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___y_2346_ = v___x_2361_;
goto v___jp_2345_;
}
}
}
v___jp_2345_:
{
lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___y_2346_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 1, v___x_2347_);
v___x_2349_ = v___x_2343_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_scheme_2336_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2350_, 2, v_host_2337_);
lean_ctor_set(v_reuseFailAlloc_2350_, 3, v_port_2338_);
lean_ctor_set(v_reuseFailAlloc_2350_, 4, v_pathSegments_2339_);
lean_ctor_set(v_reuseFailAlloc_2350_, 5, v_query_2340_);
lean_ctor_set(v_reuseFailAlloc_2350_, 6, v_fragment_2341_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setUserInfo___boxed(lean_object* v_b_2366_, lean_object* v_username_2367_, lean_object* v_password_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Std_Http_URI_Builder_setUserInfo(v_b_2366_, v_username_2367_, v_password_2368_);
lean_dec_ref(v_username_2367_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x3f(lean_object* v_b_2370_, lean_object* v_name_2371_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Std_Http_URI_DomainName_ofString_x3f(v_name_2371_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v___x_2373_; 
lean_dec_ref(v_b_2370_);
v___x_2373_ = lean_box(0);
return v___x_2373_;
}
else
{
lean_object* v_val_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2397_; 
v_val_2374_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2376_ = v___x_2372_;
v_isShared_2377_ = v_isSharedCheck_2397_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_val_2374_);
lean_dec(v___x_2372_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2397_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v_scheme_2378_; lean_object* v_userInfo_2379_; lean_object* v_port_2380_; lean_object* v_pathSegments_2381_; lean_object* v_query_2382_; lean_object* v_fragment_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2395_; 
v_scheme_2378_ = lean_ctor_get(v_b_2370_, 0);
v_userInfo_2379_ = lean_ctor_get(v_b_2370_, 1);
v_port_2380_ = lean_ctor_get(v_b_2370_, 3);
v_pathSegments_2381_ = lean_ctor_get(v_b_2370_, 4);
v_query_2382_ = lean_ctor_get(v_b_2370_, 5);
v_fragment_2383_ = lean_ctor_get(v_b_2370_, 6);
v_isSharedCheck_2395_ = !lean_is_exclusive(v_b_2370_);
if (v_isSharedCheck_2395_ == 0)
{
lean_object* v_unused_2396_; 
v_unused_2396_ = lean_ctor_get(v_b_2370_, 2);
lean_dec(v_unused_2396_);
v___x_2385_ = v_b_2370_;
v_isShared_2386_ = v_isSharedCheck_2395_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_fragment_2383_);
lean_inc(v_query_2382_);
lean_inc(v_pathSegments_2381_);
lean_inc(v_port_2380_);
lean_inc(v_userInfo_2379_);
lean_inc(v_scheme_2378_);
lean_dec(v_b_2370_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2395_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2387_; lean_object* v___x_2389_; 
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v_val_2374_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 0, v___x_2387_);
v___x_2389_ = v___x_2376_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2391_; 
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 2, v___x_2389_);
v___x_2391_ = v___x_2385_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_scheme_2378_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_userInfo_2379_);
lean_ctor_set(v_reuseFailAlloc_2393_, 2, v___x_2389_);
lean_ctor_set(v_reuseFailAlloc_2393_, 3, v_port_2380_);
lean_ctor_set(v_reuseFailAlloc_2393_, 4, v_pathSegments_2381_);
lean_ctor_set(v_reuseFailAlloc_2393_, 5, v_query_2382_);
lean_ctor_set(v_reuseFailAlloc_2393_, 6, v_fragment_2383_);
v___x_2391_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
return v___x_2392_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHost_x21(lean_object* v_b_2400_, lean_object* v_name_2401_){
_start:
{
lean_object* v___x_2402_; 
lean_inc_ref(v_name_2401_);
v___x_2402_ = l_Std_Http_URI_Builder_setHost_x3f(v_b_2400_, v_name_2401_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2403_ = ((lean_object*)(l_Std_Http_URI_Scheme_ofString_x21___closed__0));
v___x_2404_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__0));
v___x_2405_ = lean_unsigned_to_nat(706u);
v___x_2406_ = lean_unsigned_to_nat(14u);
v___x_2407_ = ((lean_object*)(l_Std_Http_URI_Builder_setHost_x21___closed__1));
v___x_2408_ = l_String_quote(v_name_2401_);
v___x_2409_ = lean_string_append(v___x_2407_, v___x_2408_);
lean_dec_ref(v___x_2408_);
v___x_2410_ = l_mkPanicMessageWithDecl(v___x_2403_, v___x_2404_, v___x_2405_, v___x_2406_, v___x_2409_);
lean_dec_ref(v___x_2409_);
v___x_2411_ = l_panic___at___00Std_Http_URI_Builder_setScheme_x21_spec__0(v___x_2410_);
return v___x_2411_;
}
else
{
lean_object* v_val_2412_; 
lean_dec_ref(v_name_2401_);
v_val_2412_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_val_2412_);
lean_dec_ref(v___x_2402_);
return v_val_2412_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv4(lean_object* v_b_2413_, lean_object* v_addr_2414_){
_start:
{
lean_object* v_scheme_2415_; lean_object* v_userInfo_2416_; lean_object* v_port_2417_; lean_object* v_pathSegments_2418_; lean_object* v_query_2419_; lean_object* v_fragment_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2429_; 
v_scheme_2415_ = lean_ctor_get(v_b_2413_, 0);
v_userInfo_2416_ = lean_ctor_get(v_b_2413_, 1);
v_port_2417_ = lean_ctor_get(v_b_2413_, 3);
v_pathSegments_2418_ = lean_ctor_get(v_b_2413_, 4);
v_query_2419_ = lean_ctor_get(v_b_2413_, 5);
v_fragment_2420_ = lean_ctor_get(v_b_2413_, 6);
v_isSharedCheck_2429_ = !lean_is_exclusive(v_b_2413_);
if (v_isSharedCheck_2429_ == 0)
{
lean_object* v_unused_2430_; 
v_unused_2430_ = lean_ctor_get(v_b_2413_, 2);
lean_dec(v_unused_2430_);
v___x_2422_ = v_b_2413_;
v_isShared_2423_ = v_isSharedCheck_2429_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_fragment_2420_);
lean_inc(v_query_2419_);
lean_inc(v_pathSegments_2418_);
lean_inc(v_port_2417_);
lean_inc(v_userInfo_2416_);
lean_inc(v_scheme_2415_);
lean_dec(v_b_2413_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2429_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2427_; 
v___x_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2424_, 0, v_addr_2414_);
v___x_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 2, v___x_2425_);
v___x_2427_ = v___x_2422_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_scheme_2415_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_userInfo_2416_);
lean_ctor_set(v_reuseFailAlloc_2428_, 2, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2428_, 3, v_port_2417_);
lean_ctor_set(v_reuseFailAlloc_2428_, 4, v_pathSegments_2418_);
lean_ctor_set(v_reuseFailAlloc_2428_, 5, v_query_2419_);
lean_ctor_set(v_reuseFailAlloc_2428_, 6, v_fragment_2420_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setHostIPv6(lean_object* v_b_2431_, lean_object* v_addr_2432_){
_start:
{
lean_object* v_scheme_2433_; lean_object* v_userInfo_2434_; lean_object* v_port_2435_; lean_object* v_pathSegments_2436_; lean_object* v_query_2437_; lean_object* v_fragment_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2447_; 
v_scheme_2433_ = lean_ctor_get(v_b_2431_, 0);
v_userInfo_2434_ = lean_ctor_get(v_b_2431_, 1);
v_port_2435_ = lean_ctor_get(v_b_2431_, 3);
v_pathSegments_2436_ = lean_ctor_get(v_b_2431_, 4);
v_query_2437_ = lean_ctor_get(v_b_2431_, 5);
v_fragment_2438_ = lean_ctor_get(v_b_2431_, 6);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_b_2431_);
if (v_isSharedCheck_2447_ == 0)
{
lean_object* v_unused_2448_; 
v_unused_2448_ = lean_ctor_get(v_b_2431_, 2);
lean_dec(v_unused_2448_);
v___x_2440_ = v_b_2431_;
v_isShared_2441_ = v_isSharedCheck_2447_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_fragment_2438_);
lean_inc(v_query_2437_);
lean_inc(v_pathSegments_2436_);
lean_inc(v_port_2435_);
lean_inc(v_userInfo_2434_);
lean_inc(v_scheme_2433_);
lean_dec(v_b_2431_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2447_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2445_; 
v___x_2442_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2442_, 0, v_addr_2432_);
v___x_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 2, v___x_2443_);
v___x_2445_ = v___x_2440_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_scheme_2433_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_userInfo_2434_);
lean_ctor_set(v_reuseFailAlloc_2446_, 2, v___x_2443_);
lean_ctor_set(v_reuseFailAlloc_2446_, 3, v_port_2435_);
lean_ctor_set(v_reuseFailAlloc_2446_, 4, v_pathSegments_2436_);
lean_ctor_set(v_reuseFailAlloc_2446_, 5, v_query_2437_);
lean_ctor_set(v_reuseFailAlloc_2446_, 6, v_fragment_2438_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort(lean_object* v_b_2449_, uint16_t v_port_2450_){
_start:
{
lean_object* v_scheme_2451_; lean_object* v_userInfo_2452_; lean_object* v_host_2453_; lean_object* v_pathSegments_2454_; lean_object* v_query_2455_; lean_object* v_fragment_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2464_; 
v_scheme_2451_ = lean_ctor_get(v_b_2449_, 0);
v_userInfo_2452_ = lean_ctor_get(v_b_2449_, 1);
v_host_2453_ = lean_ctor_get(v_b_2449_, 2);
v_pathSegments_2454_ = lean_ctor_get(v_b_2449_, 4);
v_query_2455_ = lean_ctor_get(v_b_2449_, 5);
v_fragment_2456_ = lean_ctor_get(v_b_2449_, 6);
v_isSharedCheck_2464_ = !lean_is_exclusive(v_b_2449_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; 
v_unused_2465_ = lean_ctor_get(v_b_2449_, 3);
lean_dec(v_unused_2465_);
v___x_2458_ = v_b_2449_;
v_isShared_2459_ = v_isSharedCheck_2464_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_fragment_2456_);
lean_inc(v_query_2455_);
lean_inc(v_pathSegments_2454_);
lean_inc(v_host_2453_);
lean_inc(v_userInfo_2452_);
lean_inc(v_scheme_2451_);
lean_dec(v_b_2449_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2464_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2460_; lean_object* v___x_2462_; 
v___x_2460_ = lean_alloc_ctor(2, 0, 2);
lean_ctor_set_uint16(v___x_2460_, 0, v_port_2450_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 3, v___x_2460_);
v___x_2462_ = v___x_2458_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_scheme_2451_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v_userInfo_2452_);
lean_ctor_set(v_reuseFailAlloc_2463_, 2, v_host_2453_);
lean_ctor_set(v_reuseFailAlloc_2463_, 3, v___x_2460_);
lean_ctor_set(v_reuseFailAlloc_2463_, 4, v_pathSegments_2454_);
lean_ctor_set(v_reuseFailAlloc_2463_, 5, v_query_2455_);
lean_ctor_set(v_reuseFailAlloc_2463_, 6, v_fragment_2456_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPort___boxed(lean_object* v_b_2466_, lean_object* v_port_2467_){
_start:
{
uint16_t v_port_boxed_2468_; lean_object* v_res_2469_; 
v_port_boxed_2468_ = lean_unbox(v_port_2467_);
v_res_2469_ = l_Std_Http_URI_Builder_setPort(v_b_2466_, v_port_boxed_2468_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setPath(lean_object* v_b_2470_, lean_object* v_segments_2471_){
_start:
{
lean_object* v_scheme_2472_; lean_object* v_userInfo_2473_; lean_object* v_host_2474_; lean_object* v_port_2475_; lean_object* v_query_2476_; lean_object* v_fragment_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
v_scheme_2472_ = lean_ctor_get(v_b_2470_, 0);
v_userInfo_2473_ = lean_ctor_get(v_b_2470_, 1);
v_host_2474_ = lean_ctor_get(v_b_2470_, 2);
v_port_2475_ = lean_ctor_get(v_b_2470_, 3);
v_query_2476_ = lean_ctor_get(v_b_2470_, 5);
v_fragment_2477_ = lean_ctor_get(v_b_2470_, 6);
v_isSharedCheck_2484_ = !lean_is_exclusive(v_b_2470_);
if (v_isSharedCheck_2484_ == 0)
{
lean_object* v_unused_2485_; 
v_unused_2485_ = lean_ctor_get(v_b_2470_, 4);
lean_dec(v_unused_2485_);
v___x_2479_ = v_b_2470_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_fragment_2477_);
lean_inc(v_query_2476_);
lean_inc(v_port_2475_);
lean_inc(v_host_2474_);
lean_inc(v_userInfo_2473_);
lean_inc(v_scheme_2472_);
lean_dec(v_b_2470_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 4, v_segments_2471_);
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_scheme_2472_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_userInfo_2473_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_host_2474_);
lean_ctor_set(v_reuseFailAlloc_2483_, 3, v_port_2475_);
lean_ctor_set(v_reuseFailAlloc_2483_, 4, v_segments_2471_);
lean_ctor_set(v_reuseFailAlloc_2483_, 5, v_query_2476_);
lean_ctor_set(v_reuseFailAlloc_2483_, 6, v_fragment_2477_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_appendPathSegment(lean_object* v_b_2486_, lean_object* v_segment_2487_){
_start:
{
lean_object* v_scheme_2488_; lean_object* v_userInfo_2489_; lean_object* v_host_2490_; lean_object* v_port_2491_; lean_object* v_pathSegments_2492_; lean_object* v_query_2493_; lean_object* v_fragment_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2502_; 
v_scheme_2488_ = lean_ctor_get(v_b_2486_, 0);
v_userInfo_2489_ = lean_ctor_get(v_b_2486_, 1);
v_host_2490_ = lean_ctor_get(v_b_2486_, 2);
v_port_2491_ = lean_ctor_get(v_b_2486_, 3);
v_pathSegments_2492_ = lean_ctor_get(v_b_2486_, 4);
v_query_2493_ = lean_ctor_get(v_b_2486_, 5);
v_fragment_2494_ = lean_ctor_get(v_b_2486_, 6);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_b_2486_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2496_ = v_b_2486_;
v_isShared_2497_ = v_isSharedCheck_2502_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_fragment_2494_);
lean_inc(v_query_2493_);
lean_inc(v_pathSegments_2492_);
lean_inc(v_port_2491_);
lean_inc(v_host_2490_);
lean_inc(v_userInfo_2489_);
lean_inc(v_scheme_2488_);
lean_dec(v_b_2486_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2502_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2498_; lean_object* v___x_2500_; 
v___x_2498_ = lean_array_push(v_pathSegments_2492_, v_segment_2487_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 4, v___x_2498_);
v___x_2500_ = v___x_2496_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_scheme_2488_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_userInfo_2489_);
lean_ctor_set(v_reuseFailAlloc_2501_, 2, v_host_2490_);
lean_ctor_set(v_reuseFailAlloc_2501_, 3, v_port_2491_);
lean_ctor_set(v_reuseFailAlloc_2501_, 4, v___x_2498_);
lean_ctor_set(v_reuseFailAlloc_2501_, 5, v_query_2493_);
lean_ctor_set(v_reuseFailAlloc_2501_, 6, v_fragment_2494_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryParam(lean_object* v_b_2503_, lean_object* v_key_2504_, lean_object* v_value_2505_){
_start:
{
lean_object* v_scheme_2506_; lean_object* v_userInfo_2507_; lean_object* v_host_2508_; lean_object* v_port_2509_; lean_object* v_pathSegments_2510_; lean_object* v_query_2511_; lean_object* v_fragment_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2522_; 
v_scheme_2506_ = lean_ctor_get(v_b_2503_, 0);
v_userInfo_2507_ = lean_ctor_get(v_b_2503_, 1);
v_host_2508_ = lean_ctor_get(v_b_2503_, 2);
v_port_2509_ = lean_ctor_get(v_b_2503_, 3);
v_pathSegments_2510_ = lean_ctor_get(v_b_2503_, 4);
v_query_2511_ = lean_ctor_get(v_b_2503_, 5);
v_fragment_2512_ = lean_ctor_get(v_b_2503_, 6);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_b_2503_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2514_ = v_b_2503_;
v_isShared_2515_ = v_isSharedCheck_2522_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_fragment_2512_);
lean_inc(v_query_2511_);
lean_inc(v_pathSegments_2510_);
lean_inc(v_port_2509_);
lean_inc(v_host_2508_);
lean_inc(v_userInfo_2507_);
lean_inc(v_scheme_2506_);
lean_dec(v_b_2503_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2522_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2516_, 0, v_value_2505_);
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v_key_2504_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = lean_array_push(v_query_2511_, v___x_2517_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 5, v___x_2518_);
v___x_2520_ = v___x_2514_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_scheme_2506_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_userInfo_2507_);
lean_ctor_set(v_reuseFailAlloc_2521_, 2, v_host_2508_);
lean_ctor_set(v_reuseFailAlloc_2521_, 3, v_port_2509_);
lean_ctor_set(v_reuseFailAlloc_2521_, 4, v_pathSegments_2510_);
lean_ctor_set(v_reuseFailAlloc_2521_, 5, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2521_, 6, v_fragment_2512_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_addQueryFlag(lean_object* v_b_2523_, lean_object* v_key_2524_){
_start:
{
lean_object* v_scheme_2525_; lean_object* v_userInfo_2526_; lean_object* v_host_2527_; lean_object* v_port_2528_; lean_object* v_pathSegments_2529_; lean_object* v_query_2530_; lean_object* v_fragment_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2541_; 
v_scheme_2525_ = lean_ctor_get(v_b_2523_, 0);
v_userInfo_2526_ = lean_ctor_get(v_b_2523_, 1);
v_host_2527_ = lean_ctor_get(v_b_2523_, 2);
v_port_2528_ = lean_ctor_get(v_b_2523_, 3);
v_pathSegments_2529_ = lean_ctor_get(v_b_2523_, 4);
v_query_2530_ = lean_ctor_get(v_b_2523_, 5);
v_fragment_2531_ = lean_ctor_get(v_b_2523_, 6);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_b_2523_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2533_ = v_b_2523_;
v_isShared_2534_ = v_isSharedCheck_2541_;
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
lean_inc(v_scheme_2525_);
lean_dec(v_b_2523_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2541_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2539_; 
v___x_2535_ = lean_box(0);
v___x_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2536_, 0, v_key_2524_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_2537_ = lean_array_push(v_query_2530_, v___x_2536_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 5, v___x_2537_);
v___x_2539_ = v___x_2533_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_scheme_2525_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_userInfo_2526_);
lean_ctor_set(v_reuseFailAlloc_2540_, 2, v_host_2527_);
lean_ctor_set(v_reuseFailAlloc_2540_, 3, v_port_2528_);
lean_ctor_set(v_reuseFailAlloc_2540_, 4, v_pathSegments_2529_);
lean_ctor_set(v_reuseFailAlloc_2540_, 5, v___x_2537_);
lean_ctor_set(v_reuseFailAlloc_2540_, 6, v_fragment_2531_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setQuery(lean_object* v_b_2542_, lean_object* v_query_2543_){
_start:
{
lean_object* v_scheme_2544_; lean_object* v_userInfo_2545_; lean_object* v_host_2546_; lean_object* v_port_2547_; lean_object* v_pathSegments_2548_; lean_object* v_fragment_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
v_scheme_2544_ = lean_ctor_get(v_b_2542_, 0);
v_userInfo_2545_ = lean_ctor_get(v_b_2542_, 1);
v_host_2546_ = lean_ctor_get(v_b_2542_, 2);
v_port_2547_ = lean_ctor_get(v_b_2542_, 3);
v_pathSegments_2548_ = lean_ctor_get(v_b_2542_, 4);
v_fragment_2549_ = lean_ctor_get(v_b_2542_, 6);
v_isSharedCheck_2556_ = !lean_is_exclusive(v_b_2542_);
if (v_isSharedCheck_2556_ == 0)
{
lean_object* v_unused_2557_; 
v_unused_2557_ = lean_ctor_get(v_b_2542_, 5);
lean_dec(v_unused_2557_);
v___x_2551_ = v_b_2542_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_fragment_2549_);
lean_inc(v_pathSegments_2548_);
lean_inc(v_port_2547_);
lean_inc(v_host_2546_);
lean_inc(v_userInfo_2545_);
lean_inc(v_scheme_2544_);
lean_dec(v_b_2542_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 5, v_query_2543_);
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_scheme_2544_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_userInfo_2545_);
lean_ctor_set(v_reuseFailAlloc_2555_, 2, v_host_2546_);
lean_ctor_set(v_reuseFailAlloc_2555_, 3, v_port_2547_);
lean_ctor_set(v_reuseFailAlloc_2555_, 4, v_pathSegments_2548_);
lean_ctor_set(v_reuseFailAlloc_2555_, 5, v_query_2543_);
lean_ctor_set(v_reuseFailAlloc_2555_, 6, v_fragment_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_setFragment(lean_object* v_b_2558_, lean_object* v_fragment_2559_){
_start:
{
lean_object* v_scheme_2560_; lean_object* v_userInfo_2561_; lean_object* v_host_2562_; lean_object* v_port_2563_; lean_object* v_pathSegments_2564_; lean_object* v_query_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2573_; 
v_scheme_2560_ = lean_ctor_get(v_b_2558_, 0);
v_userInfo_2561_ = lean_ctor_get(v_b_2558_, 1);
v_host_2562_ = lean_ctor_get(v_b_2558_, 2);
v_port_2563_ = lean_ctor_get(v_b_2558_, 3);
v_pathSegments_2564_ = lean_ctor_get(v_b_2558_, 4);
v_query_2565_ = lean_ctor_get(v_b_2558_, 5);
v_isSharedCheck_2573_ = !lean_is_exclusive(v_b_2558_);
if (v_isSharedCheck_2573_ == 0)
{
lean_object* v_unused_2574_; 
v_unused_2574_ = lean_ctor_get(v_b_2558_, 6);
lean_dec(v_unused_2574_);
v___x_2567_ = v_b_2558_;
v_isShared_2568_ = v_isSharedCheck_2573_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_query_2565_);
lean_inc(v_pathSegments_2564_);
lean_inc(v_port_2563_);
lean_inc(v_host_2562_);
lean_inc(v_userInfo_2561_);
lean_inc(v_scheme_2560_);
lean_dec(v_b_2558_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2573_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2569_, 0, v_fragment_2559_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 6, v___x_2569_);
v___x_2571_ = v___x_2567_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_scheme_2560_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_userInfo_2561_);
lean_ctor_set(v_reuseFailAlloc_2572_, 2, v_host_2562_);
lean_ctor_set(v_reuseFailAlloc_2572_, 3, v_port_2563_);
lean_ctor_set(v_reuseFailAlloc_2572_, 4, v_pathSegments_2564_);
lean_ctor_set(v_reuseFailAlloc_2572_, 5, v_query_2565_);
lean_ctor_set(v_reuseFailAlloc_2572_, 6, v___x_2569_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(size_t v_sz_2575_, size_t v_i_2576_, lean_object* v_bs_2577_){
_start:
{
uint8_t v___x_2578_; 
v___x_2578_ = lean_usize_dec_lt(v_i_2576_, v_sz_2575_);
if (v___x_2578_ == 0)
{
return v_bs_2577_;
}
else
{
lean_object* v_v_2579_; lean_object* v___x_2580_; lean_object* v_bs_x27_2581_; lean_object* v___x_2582_; size_t v___x_2583_; size_t v___x_2584_; lean_object* v___x_2585_; 
v_v_2579_ = lean_array_uget(v_bs_2577_, v_i_2576_);
v___x_2580_ = lean_unsigned_to_nat(0u);
v_bs_x27_2581_ = lean_array_uset(v_bs_2577_, v_i_2576_, v___x_2580_);
v___x_2582_ = l_Std_Http_URI_EncodedSegment_encode(v_v_2579_);
lean_dec(v_v_2579_);
v___x_2583_ = ((size_t)1ULL);
v___x_2584_ = lean_usize_add(v_i_2576_, v___x_2583_);
v___x_2585_ = lean_array_uset(v_bs_x27_2581_, v_i_2576_, v___x_2582_);
v_i_2576_ = v___x_2584_;
v_bs_2577_ = v___x_2585_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0___boxed(lean_object* v_sz_2587_, lean_object* v_i_2588_, lean_object* v_bs_2589_){
_start:
{
size_t v_sz_boxed_2590_; size_t v_i_boxed_2591_; lean_object* v_res_2592_; 
v_sz_boxed_2590_ = lean_unbox_usize(v_sz_2587_);
lean_dec(v_sz_2587_);
v_i_boxed_2591_ = lean_unbox_usize(v_i_2588_);
lean_dec(v_i_2588_);
v_res_2592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_boxed_2590_, v_i_boxed_2591_, v_bs_2589_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(size_t v_sz_2593_, size_t v_i_2594_, lean_object* v_bs_2595_){
_start:
{
uint8_t v___x_2596_; 
v___x_2596_ = lean_usize_dec_lt(v_i_2594_, v_sz_2593_);
if (v___x_2596_ == 0)
{
return v_bs_2595_;
}
else
{
lean_object* v_v_2597_; lean_object* v_fst_2598_; lean_object* v_snd_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2628_; 
v_v_2597_ = lean_array_uget(v_bs_2595_, v_i_2594_);
v_fst_2598_ = lean_ctor_get(v_v_2597_, 0);
v_snd_2599_ = lean_ctor_get(v_v_2597_, 1);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_v_2597_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2601_ = v_v_2597_;
v_isShared_2602_ = v_isSharedCheck_2628_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_snd_2599_);
lean_inc(v_fst_2598_);
lean_dec(v_v_2597_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2628_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2603_; lean_object* v_bs_x27_2604_; lean_object* v___y_2606_; lean_object* v___x_2611_; 
v___x_2603_ = lean_unsigned_to_nat(0u);
v_bs_x27_2604_ = lean_array_uset(v_bs_2595_, v_i_2594_, v___x_2603_);
v___x_2611_ = l_Std_Http_URI_EncodedQueryParam_encode(v_fst_2598_);
lean_dec(v_fst_2598_);
if (lean_obj_tag(v_snd_2599_) == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2612_ = lean_box(0);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 1, v___x_2612_);
lean_ctor_set(v___x_2601_, 0, v___x_2611_);
v___x_2614_ = v___x_2601_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
v___y_2606_ = v___x_2614_;
goto v___jp_2605_;
}
}
else
{
lean_object* v_val_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2627_; 
v_val_2616_ = lean_ctor_get(v_snd_2599_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_snd_2599_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2618_ = v_snd_2599_;
v_isShared_2619_ = v_isSharedCheck_2627_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_val_2616_);
lean_dec(v_snd_2599_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2627_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2620_; lean_object* v___x_2622_; 
v___x_2620_ = l_Std_Http_URI_EncodedQueryParam_encode(v_val_2616_);
lean_dec(v_val_2616_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v___x_2620_);
v___x_2622_ = v___x_2618_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2624_; 
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 1, v___x_2622_);
lean_ctor_set(v___x_2601_, 0, v___x_2611_);
v___x_2624_ = v___x_2601_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
v___y_2606_ = v___x_2624_;
goto v___jp_2605_;
}
}
}
}
v___jp_2605_:
{
size_t v___x_2607_; size_t v___x_2608_; lean_object* v___x_2609_; 
v___x_2607_ = ((size_t)1ULL);
v___x_2608_ = lean_usize_add(v_i_2594_, v___x_2607_);
v___x_2609_ = lean_array_uset(v_bs_x27_2604_, v_i_2594_, v___y_2606_);
v_i_2594_ = v___x_2608_;
v_bs_2595_ = v___x_2609_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1___boxed(lean_object* v_sz_2629_, lean_object* v_i_2630_, lean_object* v_bs_2631_){
_start:
{
size_t v_sz_boxed_2632_; size_t v_i_boxed_2633_; lean_object* v_res_2634_; 
v_sz_boxed_2632_ = lean_unbox_usize(v_sz_2629_);
lean_dec(v_sz_2629_);
v_i_boxed_2633_ = lean_unbox_usize(v_i_2630_);
lean_dec(v_i_2630_);
v_res_2634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_boxed_2632_, v_i_boxed_2633_, v_bs_2631_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Builder_build(lean_object* v_b_2635_){
_start:
{
lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; uint8_t v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v_scheme_2652_; lean_object* v_userInfo_2653_; lean_object* v_host_2654_; lean_object* v_port_2655_; lean_object* v_pathSegments_2656_; lean_object* v_query_2657_; lean_object* v_fragment_2658_; lean_object* v___y_2660_; 
v_scheme_2652_ = lean_ctor_get(v_b_2635_, 0);
lean_inc(v_scheme_2652_);
v_userInfo_2653_ = lean_ctor_get(v_b_2635_, 1);
lean_inc(v_userInfo_2653_);
v_host_2654_ = lean_ctor_get(v_b_2635_, 2);
lean_inc(v_host_2654_);
v_port_2655_ = lean_ctor_get(v_b_2635_, 3);
lean_inc(v_port_2655_);
v_pathSegments_2656_ = lean_ctor_get(v_b_2635_, 4);
lean_inc_ref(v_pathSegments_2656_);
v_query_2657_ = lean_ctor_get(v_b_2635_, 5);
lean_inc_ref(v_query_2657_);
v_fragment_2658_ = lean_ctor_get(v_b_2635_, 6);
lean_inc(v_fragment_2658_);
lean_dec_ref(v_b_2635_);
if (lean_obj_tag(v_scheme_2652_) == 0)
{
lean_object* v___x_2673_; 
v___x_2673_ = ((lean_object*)(l_Std_Http_URI_Scheme_defaultPort___closed__0));
v___y_2660_ = v___x_2673_;
goto v___jp_2659_;
}
else
{
lean_object* v_val_2674_; 
v_val_2674_ = lean_ctor_get(v_scheme_2652_, 0);
lean_inc(v_val_2674_);
lean_dec_ref(v_scheme_2652_);
v___y_2660_ = v_val_2674_;
goto v___jp_2659_;
}
v___jp_2636_:
{
size_t v_sz_2643_; size_t v___x_2644_; lean_object* v___x_2645_; lean_object* v_path_2646_; size_t v_sz_2647_; lean_object* v_query_2648_; lean_object* v___x_2649_; lean_object* v_query_2650_; lean_object* v___x_2651_; 
v_sz_2643_ = lean_array_size(v___y_2641_);
v___x_2644_ = ((size_t)0ULL);
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__0(v_sz_2643_, v___x_2644_, v___y_2641_);
v_path_2646_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_path_2646_, 0, v___x_2645_);
lean_ctor_set_uint8(v_path_2646_, sizeof(void*)*1, v___y_2640_);
v_sz_2647_ = lean_array_size(v___y_2638_);
v_query_2648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_URI_Builder_build_spec__1(v_sz_2647_, v___x_2644_, v___y_2638_);
v___x_2649_ = lean_array_to_list(v_query_2648_);
v_query_2650_ = lean_array_mk(v___x_2649_);
v___x_2651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2651_, 0, v___y_2637_);
lean_ctor_set(v___x_2651_, 1, v___y_2642_);
lean_ctor_set(v___x_2651_, 2, v_path_2646_);
lean_ctor_set(v___x_2651_, 3, v_query_2650_);
lean_ctor_set(v___x_2651_, 4, v___y_2639_);
return v___x_2651_;
}
v___jp_2659_:
{
if (lean_obj_tag(v_host_2654_) == 0)
{
uint8_t v___x_2661_; lean_object* v___x_2662_; 
lean_dec(v_port_2655_);
lean_dec(v_userInfo_2653_);
v___x_2661_ = 1;
v___x_2662_ = lean_box(0);
v___y_2637_ = v___y_2660_;
v___y_2638_ = v_query_2657_;
v___y_2639_ = v_fragment_2658_;
v___y_2640_ = v___x_2661_;
v___y_2641_ = v_pathSegments_2656_;
v___y_2642_ = v___x_2662_;
goto v___jp_2636_;
}
else
{
lean_object* v_val_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2672_; 
v_val_2663_ = lean_ctor_get(v_host_2654_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v_host_2654_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2665_ = v_host_2654_;
v_isShared_2666_ = v_isSharedCheck_2672_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_val_2663_);
lean_dec(v_host_2654_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2672_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
uint8_t v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2667_ = 1;
v___x_2668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2668_, 0, v_userInfo_2653_);
lean_ctor_set(v___x_2668_, 1, v_val_2663_);
lean_ctor_set(v___x_2668_, 2, v_port_2655_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2668_);
v___x_2670_ = v___x_2665_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
v___y_2637_ = v___y_2660_;
v___y_2638_ = v_query_2657_;
v___y_2639_ = v_fragment_2658_;
v___y_2640_ = v___x_2667_;
v___y_2641_ = v_pathSegments_2656_;
v___y_2642_ = v___x_2670_;
goto v___jp_2636_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withScheme_x21(lean_object* v_uri_2675_, lean_object* v_scheme_2676_){
_start:
{
lean_object* v_authority_2677_; lean_object* v_path_2678_; lean_object* v_query_2679_; lean_object* v_fragment_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2688_; 
v_authority_2677_ = lean_ctor_get(v_uri_2675_, 1);
v_path_2678_ = lean_ctor_get(v_uri_2675_, 2);
v_query_2679_ = lean_ctor_get(v_uri_2675_, 3);
v_fragment_2680_ = lean_ctor_get(v_uri_2675_, 4);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_uri_2675_);
if (v_isSharedCheck_2688_ == 0)
{
lean_object* v_unused_2689_; 
v_unused_2689_ = lean_ctor_get(v_uri_2675_, 0);
lean_dec(v_unused_2689_);
v___x_2682_ = v_uri_2675_;
v_isShared_2683_ = v_isSharedCheck_2688_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_fragment_2680_);
lean_inc(v_query_2679_);
lean_inc(v_path_2678_);
lean_inc(v_authority_2677_);
lean_dec(v_uri_2675_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2688_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2684_; lean_object* v___x_2686_; 
v___x_2684_ = l_Std_Http_URI_Scheme_ofString_x21(v_scheme_2676_);
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 0, v___x_2684_);
v___x_2686_ = v___x_2682_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2684_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_authority_2677_);
lean_ctor_set(v_reuseFailAlloc_2687_, 2, v_path_2678_);
lean_ctor_set(v_reuseFailAlloc_2687_, 3, v_query_2679_);
lean_ctor_set(v_reuseFailAlloc_2687_, 4, v_fragment_2680_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withAuthority(lean_object* v_uri_2690_, lean_object* v_authority_2691_){
_start:
{
lean_object* v_scheme_2692_; lean_object* v_path_2693_; lean_object* v_query_2694_; lean_object* v_fragment_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
v_scheme_2692_ = lean_ctor_get(v_uri_2690_, 0);
v_path_2693_ = lean_ctor_get(v_uri_2690_, 2);
v_query_2694_ = lean_ctor_get(v_uri_2690_, 3);
v_fragment_2695_ = lean_ctor_get(v_uri_2690_, 4);
v_isSharedCheck_2702_ = !lean_is_exclusive(v_uri_2690_);
if (v_isSharedCheck_2702_ == 0)
{
lean_object* v_unused_2703_; 
v_unused_2703_ = lean_ctor_get(v_uri_2690_, 1);
lean_dec(v_unused_2703_);
v___x_2697_ = v_uri_2690_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_fragment_2695_);
lean_inc(v_query_2694_);
lean_inc(v_path_2693_);
lean_inc(v_scheme_2692_);
lean_dec(v_uri_2690_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v_authority_2691_);
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_scheme_2692_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_authority_2691_);
lean_ctor_set(v_reuseFailAlloc_2701_, 2, v_path_2693_);
lean_ctor_set(v_reuseFailAlloc_2701_, 3, v_query_2694_);
lean_ctor_set(v_reuseFailAlloc_2701_, 4, v_fragment_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withPath(lean_object* v_uri_2704_, lean_object* v_path_2705_){
_start:
{
lean_object* v_scheme_2706_; lean_object* v_authority_2707_; lean_object* v_query_2708_; lean_object* v_fragment_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
v_scheme_2706_ = lean_ctor_get(v_uri_2704_, 0);
v_authority_2707_ = lean_ctor_get(v_uri_2704_, 1);
v_query_2708_ = lean_ctor_get(v_uri_2704_, 3);
v_fragment_2709_ = lean_ctor_get(v_uri_2704_, 4);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_uri_2704_);
if (v_isSharedCheck_2716_ == 0)
{
lean_object* v_unused_2717_; 
v_unused_2717_ = lean_ctor_get(v_uri_2704_, 2);
lean_dec(v_unused_2717_);
v___x_2711_ = v_uri_2704_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_fragment_2709_);
lean_inc(v_query_2708_);
lean_inc(v_authority_2707_);
lean_inc(v_scheme_2706_);
lean_dec(v_uri_2704_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 2, v_path_2705_);
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_scheme_2706_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v_authority_2707_);
lean_ctor_set(v_reuseFailAlloc_2715_, 2, v_path_2705_);
lean_ctor_set(v_reuseFailAlloc_2715_, 3, v_query_2708_);
lean_ctor_set(v_reuseFailAlloc_2715_, 4, v_fragment_2709_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_withQuery(lean_object* v_uri_2718_, lean_object* v_query_2719_){
_start:
{
lean_object* v_scheme_2720_; lean_object* v_authority_2721_; lean_object* v_path_2722_; lean_object* v_fragment_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
v_scheme_2720_ = lean_ctor_get(v_uri_2718_, 0);
v_authority_2721_ = lean_ctor_get(v_uri_2718_, 1);
v_path_2722_ = lean_ctor_get(v_uri_2718_, 2);
v_fragment_2723_ = lean_ctor_get(v_uri_2718_, 4);
v_isSharedCheck_2730_ = !lean_is_exclusive(v_uri_2718_);
if (v_isSharedCheck_2730_ == 0)
{
lean_object* v_unused_2731_; 
v_unused_2731_ = lean_ctor_get(v_uri_2718_, 3);
lean_dec(v_unused_2731_);
v___x_2725_ = v_uri_2718_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_fragment_2723_);
lean_inc(v_path_2722_);
lean_inc(v_authority_2721_);
lean_inc(v_scheme_2720_);
lean_dec(v_uri_2718_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 3, v_query_2719_);
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_scheme_2720_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v_authority_2721_);
lean_ctor_set(v_reuseFailAlloc_2729_, 2, v_path_2722_);
lean_ctor_set(v_reuseFailAlloc_2729_, 3, v_query_2719_);
lean_ctor_set(v_reuseFailAlloc_2729_, 4, v_fragment_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_withFragment(lean_object* v_uri_2732_, lean_object* v_fragment_2733_){
_start:
{
lean_object* v_scheme_2734_; lean_object* v_authority_2735_; lean_object* v_path_2736_; lean_object* v_query_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
v_scheme_2734_ = lean_ctor_get(v_uri_2732_, 0);
v_authority_2735_ = lean_ctor_get(v_uri_2732_, 1);
v_path_2736_ = lean_ctor_get(v_uri_2732_, 2);
v_query_2737_ = lean_ctor_get(v_uri_2732_, 3);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_uri_2732_);
if (v_isSharedCheck_2744_ == 0)
{
lean_object* v_unused_2745_; 
v_unused_2745_ = lean_ctor_get(v_uri_2732_, 4);
lean_dec(v_unused_2745_);
v___x_2739_ = v_uri_2732_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_query_2737_);
lean_inc(v_path_2736_);
lean_inc(v_authority_2735_);
lean_inc(v_scheme_2734_);
lean_dec(v_uri_2732_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 4, v_fragment_2733_);
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_scheme_2734_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_authority_2735_);
lean_ctor_set(v_reuseFailAlloc_2743_, 2, v_path_2736_);
lean_ctor_set(v_reuseFailAlloc_2743_, 3, v_query_2737_);
lean_ctor_set(v_reuseFailAlloc_2743_, 4, v_fragment_2733_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_normalize(lean_object* v_uri_2746_){
_start:
{
lean_object* v_scheme_2747_; lean_object* v_authority_2748_; lean_object* v_path_2749_; lean_object* v_query_2750_; lean_object* v_fragment_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2759_; 
v_scheme_2747_ = lean_ctor_get(v_uri_2746_, 0);
v_authority_2748_ = lean_ctor_get(v_uri_2746_, 1);
v_path_2749_ = lean_ctor_get(v_uri_2746_, 2);
v_query_2750_ = lean_ctor_get(v_uri_2746_, 3);
v_fragment_2751_ = lean_ctor_get(v_uri_2746_, 4);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_uri_2746_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2753_ = v_uri_2746_;
v_isShared_2754_ = v_isSharedCheck_2759_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_fragment_2751_);
lean_inc(v_query_2750_);
lean_inc(v_path_2749_);
lean_inc(v_authority_2748_);
lean_inc(v_scheme_2747_);
lean_dec(v_uri_2746_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2759_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2755_ = l_Std_Http_URI_Path_normalize(v_path_2749_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 2, v___x_2755_);
v___x_2757_ = v___x_2753_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_scheme_2747_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_authority_2748_);
lean_ctor_set(v_reuseFailAlloc_2758_, 2, v___x_2755_);
lean_ctor_set(v_reuseFailAlloc_2758_, 3, v_query_2750_);
lean_ctor_set(v_reuseFailAlloc_2758_, 4, v_fragment_2751_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx(lean_object* v_x_2760_){
_start:
{
switch(lean_obj_tag(v_x_2760_))
{
case 0:
{
lean_object* v___x_2761_; 
v___x_2761_ = lean_unsigned_to_nat(0u);
return v___x_2761_;
}
case 1:
{
lean_object* v___x_2762_; 
v___x_2762_ = lean_unsigned_to_nat(1u);
return v___x_2762_;
}
case 2:
{
lean_object* v___x_2763_; 
v___x_2763_ = lean_unsigned_to_nat(2u);
return v___x_2763_;
}
default: 
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_unsigned_to_nat(3u);
return v___x_2764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorIdx___boxed(lean_object* v_x_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Std_Http_RequestTarget_ctorIdx(v_x_2765_);
lean_dec(v_x_2765_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___redArg(lean_object* v_t_2767_, lean_object* v_k_2768_){
_start:
{
switch(lean_obj_tag(v_t_2767_))
{
case 0:
{
lean_object* v_path_2769_; lean_object* v_query_2770_; lean_object* v___x_2771_; 
v_path_2769_ = lean_ctor_get(v_t_2767_, 0);
lean_inc_ref(v_path_2769_);
v_query_2770_ = lean_ctor_get(v_t_2767_, 1);
lean_inc(v_query_2770_);
lean_dec_ref(v_t_2767_);
v___x_2771_ = lean_apply_2(v_k_2768_, v_path_2769_, v_query_2770_);
return v___x_2771_;
}
case 3:
{
return v_k_2768_;
}
default: 
{
lean_object* v_uri_2772_; lean_object* v___x_2773_; 
v_uri_2772_ = lean_ctor_get(v_t_2767_, 0);
lean_inc_ref(v_uri_2772_);
lean_dec(v_t_2767_);
v___x_2773_ = lean_apply_1(v_k_2768_, v_uri_2772_);
return v___x_2773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim(lean_object* v_motive_2774_, lean_object* v_ctorIdx_2775_, lean_object* v_t_2776_, lean_object* v_h_2777_, lean_object* v_k_2778_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2776_, v_k_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_ctorElim___boxed(lean_object* v_motive_2780_, lean_object* v_ctorIdx_2781_, lean_object* v_t_2782_, lean_object* v_h_2783_, lean_object* v_k_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Std_Http_RequestTarget_ctorElim(v_motive_2780_, v_ctorIdx_2781_, v_t_2782_, v_h_2783_, v_k_2784_);
lean_dec(v_ctorIdx_2781_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim___redArg(lean_object* v_t_2786_, lean_object* v_originForm_2787_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2786_, v_originForm_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_elim(lean_object* v_motive_2789_, lean_object* v_t_2790_, lean_object* v_h_2791_, lean_object* v_originForm_2792_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2790_, v_originForm_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim___redArg(lean_object* v_t_2794_, lean_object* v_absoluteForm_2795_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2794_, v_absoluteForm_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_absoluteForm_elim(lean_object* v_motive_2797_, lean_object* v_t_2798_, lean_object* v_h_2799_, lean_object* v_absoluteForm_2800_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2798_, v_absoluteForm_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim___redArg(lean_object* v_t_2802_, lean_object* v_authorityForm_2803_){
_start:
{
lean_object* v___x_2804_; 
v___x_2804_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2802_, v_authorityForm_2803_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authorityForm_elim(lean_object* v_motive_2805_, lean_object* v_t_2806_, lean_object* v_h_2807_, lean_object* v_authorityForm_2808_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2806_, v_authorityForm_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim___redArg(lean_object* v_t_2810_, lean_object* v_asteriskForm_2811_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2810_, v_asteriskForm_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_asteriskForm_elim(lean_object* v_motive_2813_, lean_object* v_t_2814_, lean_object* v_h_2815_, lean_object* v_asteriskForm_2816_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Std_Http_RequestTarget_ctorElim___redArg(v_t_2814_, v_asteriskForm_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0(lean_object* v_x_2823_, lean_object* v_x_2824_){
_start:
{
if (lean_obj_tag(v_x_2823_) == 0)
{
lean_object* v___x_2825_; 
v___x_2825_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__1));
return v___x_2825_;
}
else
{
lean_object* v_val_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v_val_2826_ = lean_ctor_get(v_x_2823_, 0);
lean_inc(v_val_2826_);
lean_dec_ref(v_x_2823_);
v___x_2827_ = ((lean_object*)(l_Option_repr___at___00Std_Http_URI_instReprUserInfo_repr_spec__0___closed__3));
v___x_2828_ = l_Array_repr___at___00Std_Http_instReprURI_repr_spec__1(v_val_2826_);
v___x_2829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2827_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = l_Repr_addAppParen(v___x_2829_, v_x_2824_);
return v___x_2830_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0___boxed(lean_object* v_x_2831_, lean_object* v_x_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0(v_x_2831_, v_x_2832_);
lean_dec(v_x_2832_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object* v_x_2855_, lean_object* v_prec_2856_){
_start:
{
lean_object* v___y_2858_; 
switch(lean_obj_tag(v_x_2855_))
{
case 0:
{
lean_object* v_path_2864_; lean_object* v_query_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2889_; 
v_path_2864_ = lean_ctor_get(v_x_2855_, 0);
v_query_2865_ = lean_ctor_get(v_x_2855_, 1);
v_isSharedCheck_2889_ = !lean_is_exclusive(v_x_2855_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2867_ = v_x_2855_;
v_isShared_2868_ = v_isSharedCheck_2889_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_query_2865_);
lean_inc(v_path_2864_);
lean_dec(v_x_2855_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2889_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___y_2870_; lean_object* v___x_2885_; uint8_t v___x_2886_; 
v___x_2885_ = lean_unsigned_to_nat(1024u);
v___x_2886_ = lean_nat_dec_le(v___x_2885_, v_prec_2856_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2887_; 
v___x_2887_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_2870_ = v___x_2887_;
goto v___jp_2869_;
}
else
{
lean_object* v___x_2888_; 
v___x_2888_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_2870_ = v___x_2888_;
goto v___jp_2869_;
}
v___jp_2869_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2876_; 
v___x_2871_ = lean_box(1);
v___x_2872_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__4));
v___x_2873_ = lean_unsigned_to_nat(1024u);
v___x_2874_ = l_Std_Http_URI_instReprPath_repr___redArg(v_path_2864_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set_tag(v___x_2867_, 5);
lean_ctor_set(v___x_2867_, 1, v___x_2874_);
lean_ctor_set(v___x_2867_, 0, v___x_2872_);
v___x_2876_ = v___x_2867_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2872_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
lean_ctor_set(v___x_2877_, 1, v___x_2871_);
v___x_2878_ = l_Option_repr___at___00Std_Http_instReprRequestTarget_repr_spec__0(v_query_2865_, v___x_2873_);
v___x_2879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
v___x_2880_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___y_2870_);
lean_ctor_set(v___x_2880_, 1, v___x_2879_);
v___x_2881_ = 0;
v___x_2882_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2882_, 0, v___x_2880_);
lean_ctor_set_uint8(v___x_2882_, sizeof(void*)*1, v___x_2881_);
v___x_2883_ = l_Repr_addAppParen(v___x_2882_, v_prec_2856_);
return v___x_2883_;
}
}
}
}
case 1:
{
lean_object* v_uri_2890_; lean_object* v___y_2892_; lean_object* v___x_2900_; uint8_t v___x_2901_; 
v_uri_2890_ = lean_ctor_get(v_x_2855_, 0);
lean_inc_ref(v_uri_2890_);
lean_dec_ref(v_x_2855_);
v___x_2900_ = lean_unsigned_to_nat(1024u);
v___x_2901_ = lean_nat_dec_le(v___x_2900_, v_prec_2856_);
if (v___x_2901_ == 0)
{
lean_object* v___x_2902_; 
v___x_2902_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_2892_ = v___x_2902_;
goto v___jp_2891_;
}
else
{
lean_object* v___x_2903_; 
v___x_2903_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_2892_ = v___x_2903_;
goto v___jp_2891_;
}
v___jp_2891_:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; uint8_t v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2893_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__7));
v___x_2894_ = l_Std_Http_instReprURI_repr___redArg(v_uri_2890_);
v___x_2895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2893_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v___x_2896_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___y_2892_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
v___x_2897_ = 0;
v___x_2898_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2898_, 0, v___x_2896_);
lean_ctor_set_uint8(v___x_2898_, sizeof(void*)*1, v___x_2897_);
v___x_2899_ = l_Repr_addAppParen(v___x_2898_, v_prec_2856_);
return v___x_2899_;
}
}
case 2:
{
lean_object* v_authority_2904_; lean_object* v___y_2906_; lean_object* v___x_2914_; uint8_t v___x_2915_; 
v_authority_2904_ = lean_ctor_get(v_x_2855_, 0);
lean_inc_ref(v_authority_2904_);
lean_dec_ref(v_x_2855_);
v___x_2914_ = lean_unsigned_to_nat(1024u);
v___x_2915_ = lean_nat_dec_le(v___x_2914_, v_prec_2856_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; 
v___x_2916_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_2906_ = v___x_2916_;
goto v___jp_2905_;
}
else
{
lean_object* v___x_2917_; 
v___x_2917_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_2906_ = v___x_2917_;
goto v___jp_2905_;
}
v___jp_2905_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2907_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__10));
v___x_2908_ = l_Std_Http_URI_instReprAuthority_repr___redArg(v_authority_2904_);
v___x_2909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2907_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___y_2906_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = 0;
v___x_2912_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2912_, 0, v___x_2910_);
lean_ctor_set_uint8(v___x_2912_, sizeof(void*)*1, v___x_2911_);
v___x_2913_ = l_Repr_addAppParen(v___x_2912_, v_prec_2856_);
return v___x_2913_;
}
}
default: 
{
lean_object* v___x_2918_; uint8_t v___x_2919_; 
v___x_2918_ = lean_unsigned_to_nat(1024u);
v___x_2919_ = lean_nat_dec_le(v___x_2918_, v_prec_2856_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; 
v___x_2920_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__4, &l_Std_Http_URI_instReprHost___lam__0___closed__4_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__4);
v___y_2858_ = v___x_2920_;
goto v___jp_2857_;
}
else
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_obj_once(&l_Std_Http_URI_instReprHost___lam__0___closed__5, &l_Std_Http_URI_instReprHost___lam__0___closed__5_once, _init_l_Std_Http_URI_instReprHost___lam__0___closed__5);
v___y_2858_ = v___x_2921_;
goto v___jp_2857_;
}
}
}
v___jp_2857_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2859_ = ((lean_object*)(l_Std_Http_instReprRequestTarget_repr___closed__1));
v___x_2860_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___y_2858_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = 0;
v___x_2862_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set_uint8(v___x_2862_, sizeof(void*)*1, v___x_2861_);
v___x_2863_ = l_Repr_addAppParen(v___x_2862_, v_prec_2856_);
return v___x_2863_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprRequestTarget_repr___boxed(lean_object* v_x_2922_, lean_object* v_prec_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Std_Http_instReprRequestTarget_repr(v_x_2922_, v_prec_2923_);
lean_dec(v_prec_2923_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path(lean_object* v_x_2932_){
_start:
{
switch(lean_obj_tag(v_x_2932_))
{
case 0:
{
lean_object* v_path_2933_; 
v_path_2933_ = lean_ctor_get(v_x_2932_, 0);
lean_inc_ref(v_path_2933_);
return v_path_2933_;
}
case 1:
{
lean_object* v_uri_2934_; lean_object* v_path_2935_; 
v_uri_2934_ = lean_ctor_get(v_x_2932_, 0);
v_path_2935_ = lean_ctor_get(v_uri_2934_, 2);
lean_inc_ref(v_path_2935_);
return v_path_2935_;
}
default: 
{
lean_object* v___x_2936_; 
v___x_2936_ = ((lean_object*)(l_Std_Http_RequestTarget_path___closed__1));
return v___x_2936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_path___boxed(lean_object* v_x_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Std_Http_RequestTarget_path(v_x_2937_);
lean_dec(v_x_2937_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query(lean_object* v_x_2939_){
_start:
{
switch(lean_obj_tag(v_x_2939_))
{
case 0:
{
lean_object* v_query_2940_; 
v_query_2940_ = lean_ctor_get(v_x_2939_, 1);
if (lean_obj_tag(v_query_2940_) == 0)
{
lean_object* v___x_2941_; 
v___x_2941_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_2941_;
}
else
{
lean_object* v_val_2942_; 
v_val_2942_ = lean_ctor_get(v_query_2940_, 0);
lean_inc(v_val_2942_);
return v_val_2942_;
}
}
case 1:
{
lean_object* v_uri_2943_; lean_object* v_query_2944_; 
v_uri_2943_ = lean_ctor_get(v_x_2939_, 0);
v_query_2944_ = lean_ctor_get(v_uri_2943_, 3);
lean_inc_ref(v_query_2944_);
return v_query_2944_;
}
default: 
{
lean_object* v___x_2945_; 
v___x_2945_ = ((lean_object*)(l_Std_Http_URI_Query_empty));
return v___x_2945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_query___boxed(lean_object* v_x_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Std_Http_RequestTarget_query(v_x_2946_);
lean_dec(v_x_2946_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_authority_x3f(lean_object* v_x_2948_){
_start:
{
switch(lean_obj_tag(v_x_2948_))
{
case 2:
{
lean_object* v_authority_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
v_authority_2949_ = lean_ctor_get(v_x_2948_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_x_2948_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v_x_2948_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_authority_2949_);
lean_dec(v_x_2948_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set_tag(v___x_2951_, 1);
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_authority_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
case 1:
{
lean_object* v_uri_2957_; lean_object* v_authority_2958_; 
v_uri_2957_ = lean_ctor_get(v_x_2948_, 0);
lean_inc_ref(v_uri_2957_);
lean_dec_ref(v_x_2948_);
v_authority_2958_ = lean_ctor_get(v_uri_2957_, 1);
lean_inc(v_authority_2958_);
lean_dec_ref(v_uri_2957_);
return v_authority_2958_;
}
default: 
{
lean_object* v___x_2959_; 
lean_dec(v_x_2948_);
v___x_2959_ = lean_box(0);
return v___x_2959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instToString___lam__4(lean_object* v___f_2961_, lean_object* v___f_2962_, lean_object* v___f_2963_, lean_object* v___f_2964_, lean_object* v_x_2965_){
_start:
{
lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; 
switch(lean_obj_tag(v_x_2965_))
{
case 0:
{
lean_object* v_path_2972_; lean_object* v_query_2973_; lean_object* v___y_2975_; lean_object* v_segments_2988_; uint8_t v_absolute_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; size_t v_sz_2992_; size_t v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v_result_2996_; 
lean_dec_ref(v___f_2964_);
lean_dec_ref(v___f_2963_);
v_path_2972_ = lean_ctor_get(v_x_2965_, 0);
lean_inc_ref(v_path_2972_);
v_query_2973_ = lean_ctor_get(v_x_2965_, 1);
lean_inc(v_query_2973_);
lean_dec_ref(v_x_2965_);
v_segments_2988_ = lean_ctor_get(v_path_2972_, 0);
lean_inc_ref(v_segments_2988_);
v_absolute_2989_ = lean_ctor_get_uint8(v_path_2972_, sizeof(void*)*1);
lean_dec_ref(v_path_2972_);
v___x_2990_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_2991_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_2992_ = lean_array_size(v_segments_2988_);
v___x_2993_ = ((size_t)0ULL);
v___x_2994_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2991_, v___f_2962_, v_sz_2992_, v___x_2993_, v_segments_2988_);
v___x_2995_ = lean_array_to_list(v___x_2994_);
v_result_2996_ = l_String_intercalate(v___x_2990_, v___x_2995_);
if (v_absolute_2989_ == 0)
{
v___y_2975_ = v_result_2996_;
goto v___jp_2974_;
}
else
{
lean_object* v___x_2997_; 
v___x_2997_ = lean_string_append(v___x_2990_, v_result_2996_);
lean_dec_ref(v_result_2996_);
v___y_2975_ = v___x_2997_;
goto v___jp_2974_;
}
v___jp_2974_:
{
if (lean_obj_tag(v_query_2973_) == 0)
{
lean_dec_ref(v___f_2961_);
return v___y_2975_;
}
else
{
lean_object* v_val_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; 
v_val_2976_ = lean_ctor_get(v_query_2973_, 0);
lean_inc(v_val_2976_);
lean_dec_ref(v_query_2973_);
v___x_2977_ = lean_array_get_size(v_val_2976_);
v___x_2978_ = lean_unsigned_to_nat(0u);
v___x_2979_ = lean_nat_dec_eq(v___x_2977_, v___x_2978_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v_encodedParams_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2980_ = lean_array_to_list(v_val_2976_);
v___x_2981_ = lean_box(0);
v_encodedParams_2982_ = l_List_mapTR_loop___redArg(v___f_2961_, v___x_2980_, v___x_2981_);
v___x_2983_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_2984_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_2985_ = l_String_intercalate(v___x_2984_, v_encodedParams_2982_);
v___x_2986_ = lean_string_append(v___x_2983_, v___x_2985_);
lean_dec_ref(v___x_2985_);
v___x_2987_ = lean_string_append(v___y_2975_, v___x_2986_);
lean_dec_ref(v___x_2986_);
return v___x_2987_;
}
else
{
lean_dec(v_val_2976_);
lean_dec_ref(v___f_2961_);
return v___y_2975_;
}
}
}
}
case 1:
{
lean_object* v_uri_2998_; lean_object* v_scheme_2999_; lean_object* v_authority_3000_; lean_object* v_path_3001_; lean_object* v_query_3002_; lean_object* v_fragment_3003_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3040_; 
lean_dec_ref(v___f_2962_);
lean_dec_ref(v___f_2961_);
v_uri_2998_ = lean_ctor_get(v_x_2965_, 0);
lean_inc_ref(v_uri_2998_);
lean_dec_ref(v_x_2965_);
v_scheme_2999_ = lean_ctor_get(v_uri_2998_, 0);
lean_inc_ref(v_scheme_2999_);
v_authority_3000_ = lean_ctor_get(v_uri_2998_, 1);
lean_inc(v_authority_3000_);
v_path_3001_ = lean_ctor_get(v_uri_2998_, 2);
lean_inc_ref(v_path_3001_);
v_query_3002_ = lean_ctor_get(v_uri_2998_, 3);
lean_inc_ref(v_query_3002_);
v_fragment_3003_ = lean_ctor_get(v_uri_2998_, 4);
lean_inc(v_fragment_3003_);
lean_dec_ref(v_uri_2998_);
if (lean_obj_tag(v_authority_3000_) == 0)
{
lean_object* v___x_3051_; 
v___x_3051_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3040_ = v___x_3051_;
goto v___jp_3039_;
}
else
{
lean_object* v_val_3052_; lean_object* v_userInfo_3053_; lean_object* v_host_3054_; lean_object* v_port_3055_; lean_object* v___x_3056_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3075_; 
v_val_3052_ = lean_ctor_get(v_authority_3000_, 0);
lean_inc(v_val_3052_);
lean_dec_ref(v_authority_3000_);
v_userInfo_3053_ = lean_ctor_get(v_val_3052_, 0);
lean_inc(v_userInfo_3053_);
v_host_3054_ = lean_ctor_get(v_val_3052_, 1);
lean_inc_ref(v_host_3054_);
v_port_3055_ = lean_ctor_get(v_val_3052_, 2);
lean_inc(v_port_3055_);
lean_dec(v_val_3052_);
v___x_3056_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__1));
if (lean_obj_tag(v_userInfo_3053_) == 0)
{
lean_object* v___x_3085_; 
v___x_3085_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3075_ = v___x_3085_;
goto v___jp_3074_;
}
else
{
lean_object* v_val_3086_; lean_object* v_password_3087_; 
v_val_3086_ = lean_ctor_get(v_userInfo_3053_, 0);
lean_inc(v_val_3086_);
lean_dec_ref(v_userInfo_3053_);
v_password_3087_ = lean_ctor_get(v_val_3086_, 1);
if (lean_obj_tag(v_password_3087_) == 0)
{
lean_object* v_username_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v_username_3088_ = lean_ctor_get(v_val_3086_, 0);
lean_inc_ref(v_username_3088_);
lean_dec(v_val_3086_);
v___x_3089_ = lean_string_from_utf8_unchecked(v_username_3088_);
v___x_3090_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3091_ = lean_string_append(v___x_3089_, v___x_3090_);
v___y_3075_ = v___x_3091_;
goto v___jp_3074_;
}
else
{
lean_object* v_username_3092_; lean_object* v_val_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
lean_inc_ref(v_password_3087_);
v_username_3092_ = lean_ctor_get(v_val_3086_, 0);
lean_inc_ref(v_username_3092_);
lean_dec(v_val_3086_);
v_val_3093_ = lean_ctor_get(v_password_3087_, 0);
lean_inc(v_val_3093_);
lean_dec_ref(v_password_3087_);
v___x_3094_ = lean_string_from_utf8_unchecked(v_username_3092_);
v___x_3095_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3096_ = lean_string_append(v___x_3094_, v___x_3095_);
v___x_3097_ = lean_string_from_utf8_unchecked(v_val_3093_);
v___x_3098_ = lean_string_append(v___x_3096_, v___x_3097_);
lean_dec_ref(v___x_3097_);
v___x_3099_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3100_ = lean_string_append(v___x_3098_, v___x_3099_);
v___y_3075_ = v___x_3100_;
goto v___jp_3074_;
}
}
v___jp_3057_:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = lean_string_append(v___y_3059_, v___y_3058_);
lean_dec_ref(v___y_3058_);
v___x_3062_ = lean_string_append(v___x_3061_, v___y_3060_);
lean_dec_ref(v___y_3060_);
v___x_3063_ = lean_string_append(v___x_3056_, v___x_3062_);
lean_dec_ref(v___x_3062_);
v___y_3040_ = v___x_3063_;
goto v___jp_3039_;
}
v___jp_3064_:
{
switch(lean_obj_tag(v_port_3055_))
{
case 0:
{
lean_object* v___x_3067_; 
v___x_3067_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3058_ = v___y_3066_;
v___y_3059_ = v___y_3065_;
v___y_3060_ = v___x_3067_;
goto v___jp_3057_;
}
case 1:
{
lean_object* v___x_3068_; 
v___x_3068_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3058_ = v___y_3066_;
v___y_3059_ = v___y_3065_;
v___y_3060_ = v___x_3068_;
goto v___jp_3057_;
}
default: 
{
uint16_t v_port_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v_port_3069_ = lean_ctor_get_uint16(v_port_3055_, 0);
lean_dec_ref(v_port_3055_);
v___x_3070_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3071_ = lean_uint16_to_nat(v_port_3069_);
v___x_3072_ = l_Nat_reprFast(v___x_3071_);
v___x_3073_ = lean_string_append(v___x_3070_, v___x_3072_);
lean_dec_ref(v___x_3072_);
v___y_3058_ = v___y_3066_;
v___y_3059_ = v___y_3065_;
v___y_3060_ = v___x_3073_;
goto v___jp_3057_;
}
}
}
v___jp_3074_:
{
switch(lean_obj_tag(v_host_3054_))
{
case 0:
{
lean_object* v_name_3076_; 
v_name_3076_ = lean_ctor_get(v_host_3054_, 0);
lean_inc_ref(v_name_3076_);
lean_dec_ref(v_host_3054_);
v___y_3065_ = v___y_3075_;
v___y_3066_ = v_name_3076_;
goto v___jp_3064_;
}
case 1:
{
lean_object* v_ipv4_3077_; lean_object* v___x_3078_; 
v_ipv4_3077_ = lean_ctor_get(v_host_3054_, 0);
lean_inc_ref(v_ipv4_3077_);
lean_dec_ref(v_host_3054_);
v___x_3078_ = lean_uv_ntop_v4(v_ipv4_3077_);
lean_dec_ref(v_ipv4_3077_);
v___y_3065_ = v___y_3075_;
v___y_3066_ = v___x_3078_;
goto v___jp_3064_;
}
default: 
{
lean_object* v_ipv6_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v_ipv6_3079_ = lean_ctor_get(v_host_3054_, 0);
lean_inc_ref(v_ipv6_3079_);
lean_dec_ref(v_host_3054_);
v___x_3080_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3081_ = lean_uv_ntop_v6(v_ipv6_3079_);
lean_dec_ref(v_ipv6_3079_);
v___x_3082_ = lean_string_append(v___x_3080_, v___x_3081_);
lean_dec_ref(v___x_3081_);
v___x_3083_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3084_ = lean_string_append(v___x_3082_, v___x_3083_);
v___y_3065_ = v___y_3075_;
v___y_3066_ = v___x_3084_;
goto v___jp_3064_;
}
}
}
}
v___jp_3004_:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3009_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3010_ = lean_string_append(v_scheme_2999_, v___x_3009_);
v___x_3011_ = lean_string_append(v___x_3010_, v___y_3007_);
lean_dec_ref(v___y_3007_);
v___x_3012_ = lean_string_append(v___x_3011_, v___y_3006_);
lean_dec_ref(v___y_3006_);
v___x_3013_ = lean_string_append(v___x_3012_, v___y_3005_);
lean_dec_ref(v___y_3005_);
v___x_3014_ = lean_string_append(v___x_3013_, v___y_3008_);
lean_dec_ref(v___y_3008_);
return v___x_3014_;
}
v___jp_3015_:
{
if (lean_obj_tag(v_fragment_3003_) == 0)
{
lean_object* v___x_3019_; 
v___x_3019_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3005_ = v___y_3018_;
v___y_3006_ = v___y_3016_;
v___y_3007_ = v___y_3017_;
v___y_3008_ = v___x_3019_;
goto v___jp_3004_;
}
else
{
lean_object* v_val_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_val_3020_ = lean_ctor_get(v_fragment_3003_, 0);
lean_inc(v_val_3020_);
lean_dec_ref(v_fragment_3003_);
v___x_3021_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__0));
v___x_3022_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3020_);
lean_dec(v_val_3020_);
v___x_3023_ = lean_string_from_utf8_unchecked(v___x_3022_);
v___x_3024_ = lean_string_append(v___x_3021_, v___x_3023_);
lean_dec_ref(v___x_3023_);
v___y_3005_ = v___y_3018_;
v___y_3006_ = v___y_3016_;
v___y_3007_ = v___y_3017_;
v___y_3008_ = v___x_3024_;
goto v___jp_3004_;
}
}
v___jp_3025_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; uint8_t v___x_3030_; 
v___x_3028_ = lean_array_get_size(v_query_3002_);
v___x_3029_ = lean_unsigned_to_nat(0u);
v___x_3030_ = lean_nat_dec_eq(v___x_3028_, v___x_3029_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v_encodedParams_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3031_ = lean_array_to_list(v_query_3002_);
v___x_3032_ = lean_box(0);
v_encodedParams_3033_ = l_List_mapTR_loop___redArg(v___f_2963_, v___x_3031_, v___x_3032_);
v___x_3034_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_3035_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_3036_ = l_String_intercalate(v___x_3035_, v_encodedParams_3033_);
v___x_3037_ = lean_string_append(v___x_3034_, v___x_3036_);
lean_dec_ref(v___x_3036_);
v___y_3016_ = v___y_3027_;
v___y_3017_ = v___y_3026_;
v___y_3018_ = v___x_3037_;
goto v___jp_3015_;
}
else
{
lean_object* v___x_3038_; 
lean_dec_ref(v_query_3002_);
lean_dec_ref(v___f_2963_);
v___x_3038_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3016_ = v___y_3027_;
v___y_3017_ = v___y_3026_;
v___y_3018_ = v___x_3038_;
goto v___jp_3015_;
}
}
v___jp_3039_:
{
lean_object* v_segments_3041_; uint8_t v_absolute_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; size_t v_sz_3045_; size_t v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v_result_3049_; 
v_segments_3041_ = lean_ctor_get(v_path_3001_, 0);
lean_inc_ref(v_segments_3041_);
v_absolute_3042_ = lean_ctor_get_uint8(v_path_3001_, sizeof(void*)*1);
lean_dec_ref(v_path_3001_);
v___x_3043_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3044_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3045_ = lean_array_size(v_segments_3041_);
v___x_3046_ = ((size_t)0ULL);
v___x_3047_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3044_, v___f_2964_, v_sz_3045_, v___x_3046_, v_segments_3041_);
v___x_3048_ = lean_array_to_list(v___x_3047_);
v_result_3049_ = l_String_intercalate(v___x_3043_, v___x_3048_);
if (v_absolute_3042_ == 0)
{
v___y_3026_ = v___y_3040_;
v___y_3027_ = v_result_3049_;
goto v___jp_3025_;
}
else
{
lean_object* v___x_3050_; 
v___x_3050_ = lean_string_append(v___x_3043_, v_result_3049_);
lean_dec_ref(v_result_3049_);
v___y_3026_ = v___y_3040_;
v___y_3027_ = v___x_3050_;
goto v___jp_3025_;
}
}
}
case 2:
{
lean_object* v_authority_3101_; lean_object* v_userInfo_3102_; lean_object* v_host_3103_; lean_object* v_port_3104_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3116_; 
lean_dec_ref(v___f_2964_);
lean_dec_ref(v___f_2963_);
lean_dec_ref(v___f_2962_);
lean_dec_ref(v___f_2961_);
v_authority_3101_ = lean_ctor_get(v_x_2965_, 0);
lean_inc_ref(v_authority_3101_);
lean_dec_ref(v_x_2965_);
v_userInfo_3102_ = lean_ctor_get(v_authority_3101_, 0);
lean_inc(v_userInfo_3102_);
v_host_3103_ = lean_ctor_get(v_authority_3101_, 1);
lean_inc_ref(v_host_3103_);
v_port_3104_ = lean_ctor_get(v_authority_3101_, 2);
lean_inc(v_port_3104_);
lean_dec_ref(v_authority_3101_);
if (lean_obj_tag(v_userInfo_3102_) == 0)
{
lean_object* v___x_3126_; 
v___x_3126_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3116_ = v___x_3126_;
goto v___jp_3115_;
}
else
{
lean_object* v_val_3127_; lean_object* v_password_3128_; 
v_val_3127_ = lean_ctor_get(v_userInfo_3102_, 0);
lean_inc(v_val_3127_);
lean_dec_ref(v_userInfo_3102_);
v_password_3128_ = lean_ctor_get(v_val_3127_, 1);
if (lean_obj_tag(v_password_3128_) == 0)
{
lean_object* v_username_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v_username_3129_ = lean_ctor_get(v_val_3127_, 0);
lean_inc_ref(v_username_3129_);
lean_dec(v_val_3127_);
v___x_3130_ = lean_string_from_utf8_unchecked(v_username_3129_);
v___x_3131_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3132_ = lean_string_append(v___x_3130_, v___x_3131_);
v___y_3116_ = v___x_3132_;
goto v___jp_3115_;
}
else
{
lean_object* v_username_3133_; lean_object* v_val_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
lean_inc_ref(v_password_3128_);
v_username_3133_ = lean_ctor_get(v_val_3127_, 0);
lean_inc_ref(v_username_3133_);
lean_dec(v_val_3127_);
v_val_3134_ = lean_ctor_get(v_password_3128_, 0);
lean_inc(v_val_3134_);
lean_dec_ref(v_password_3128_);
v___x_3135_ = lean_string_from_utf8_unchecked(v_username_3133_);
v___x_3136_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3137_ = lean_string_append(v___x_3135_, v___x_3136_);
v___x_3138_ = lean_string_from_utf8_unchecked(v_val_3134_);
v___x_3139_ = lean_string_append(v___x_3137_, v___x_3138_);
lean_dec_ref(v___x_3138_);
v___x_3140_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3141_ = lean_string_append(v___x_3139_, v___x_3140_);
v___y_3116_ = v___x_3141_;
goto v___jp_3115_;
}
}
v___jp_3105_:
{
switch(lean_obj_tag(v_port_3104_))
{
case 0:
{
lean_object* v___x_3108_; 
v___x_3108_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_2967_ = v___y_3106_;
v___y_2968_ = v___y_3107_;
v___y_2969_ = v___x_3108_;
goto v___jp_2966_;
}
case 1:
{
lean_object* v___x_3109_; 
v___x_3109_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_2967_ = v___y_3106_;
v___y_2968_ = v___y_3107_;
v___y_2969_ = v___x_3109_;
goto v___jp_2966_;
}
default: 
{
uint16_t v_port_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v_port_3110_ = lean_ctor_get_uint16(v_port_3104_, 0);
lean_dec_ref(v_port_3104_);
v___x_3111_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3112_ = lean_uint16_to_nat(v_port_3110_);
v___x_3113_ = l_Nat_reprFast(v___x_3112_);
v___x_3114_ = lean_string_append(v___x_3111_, v___x_3113_);
lean_dec_ref(v___x_3113_);
v___y_2967_ = v___y_3106_;
v___y_2968_ = v___y_3107_;
v___y_2969_ = v___x_3114_;
goto v___jp_2966_;
}
}
}
v___jp_3115_:
{
switch(lean_obj_tag(v_host_3103_))
{
case 0:
{
lean_object* v_name_3117_; 
v_name_3117_ = lean_ctor_get(v_host_3103_, 0);
lean_inc_ref(v_name_3117_);
lean_dec_ref(v_host_3103_);
v___y_3106_ = v___y_3116_;
v___y_3107_ = v_name_3117_;
goto v___jp_3105_;
}
case 1:
{
lean_object* v_ipv4_3118_; lean_object* v___x_3119_; 
v_ipv4_3118_ = lean_ctor_get(v_host_3103_, 0);
lean_inc_ref(v_ipv4_3118_);
lean_dec_ref(v_host_3103_);
v___x_3119_ = lean_uv_ntop_v4(v_ipv4_3118_);
lean_dec_ref(v_ipv4_3118_);
v___y_3106_ = v___y_3116_;
v___y_3107_ = v___x_3119_;
goto v___jp_3105_;
}
default: 
{
lean_object* v_ipv6_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v_ipv6_3120_ = lean_ctor_get(v_host_3103_, 0);
lean_inc_ref(v_ipv6_3120_);
lean_dec_ref(v_host_3103_);
v___x_3121_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3122_ = lean_uv_ntop_v6(v_ipv6_3120_);
lean_dec_ref(v_ipv6_3120_);
v___x_3123_ = lean_string_append(v___x_3121_, v___x_3122_);
lean_dec_ref(v___x_3122_);
v___x_3124_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3125_ = lean_string_append(v___x_3123_, v___x_3124_);
v___y_3106_ = v___y_3116_;
v___y_3107_ = v___x_3125_;
goto v___jp_3105_;
}
}
}
}
default: 
{
lean_object* v___x_3142_; 
lean_dec_ref(v___f_2964_);
lean_dec_ref(v___f_2963_);
lean_dec_ref(v___f_2962_);
lean_dec_ref(v___f_2961_);
v___x_3142_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__4___closed__0));
return v___x_3142_;
}
}
v___jp_2966_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = lean_string_append(v___y_2967_, v___y_2968_);
lean_dec_ref(v___y_2968_);
v___x_2971_ = lean_string_append(v___x_2970_, v___y_2969_);
lean_dec_ref(v___y_2969_);
return v___x_2971_;
}
}
}
static lean_object* _init_l_Std_Http_RequestTarget_instToString___closed__0(void){
_start:
{
lean_object* v___f_3143_; lean_object* v___f_3144_; lean_object* v___f_3145_; 
v___f_3143_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___closed__0));
v___f_3144_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___closed__0));
v___f_3145_ = lean_alloc_closure((void*)(l_Std_Http_RequestTarget_instToString___lam__4), 5, 4);
lean_closure_set(v___f_3145_, 0, v___f_3144_);
lean_closure_set(v___f_3145_, 1, v___f_3143_);
lean_closure_set(v___f_3145_, 2, v___f_3144_);
lean_closure_set(v___f_3145_, 3, v___f_3143_);
return v___f_3145_;
}
}
static lean_object* _init_l_Std_Http_RequestTarget_instToString(void){
_start:
{
lean_object* v___f_3146_; 
v___f_3146_ = lean_obj_once(&l_Std_Http_RequestTarget_instToString___closed__0, &l_Std_Http_RequestTarget_instToString___closed__0_once, _init_l_Std_Http_RequestTarget_instToString___closed__0);
return v___f_3146_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_instEncodeV11___lam__4(lean_object* v___f_3147_, lean_object* v___f_3148_, lean_object* v___f_3149_, lean_object* v___f_3150_, lean_object* v_buffer_3151_, lean_object* v_target_3152_){
_start:
{
lean_object* v___y_3154_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; 
switch(lean_obj_tag(v_target_3152_))
{
case 0:
{
lean_object* v_path_3174_; lean_object* v_query_3175_; lean_object* v___y_3177_; lean_object* v_segments_3190_; uint8_t v_absolute_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; size_t v_sz_3194_; size_t v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v_result_3198_; 
lean_dec_ref(v___f_3150_);
lean_dec_ref(v___f_3149_);
v_path_3174_ = lean_ctor_get(v_target_3152_, 0);
lean_inc_ref(v_path_3174_);
v_query_3175_ = lean_ctor_get(v_target_3152_, 1);
lean_inc(v_query_3175_);
lean_dec_ref(v_target_3152_);
v_segments_3190_ = lean_ctor_get(v_path_3174_, 0);
lean_inc_ref(v_segments_3190_);
v_absolute_3191_ = lean_ctor_get_uint8(v_path_3174_, sizeof(void*)*1);
lean_dec_ref(v_path_3174_);
v___x_3192_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3193_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3194_ = lean_array_size(v_segments_3190_);
v___x_3195_ = ((size_t)0ULL);
v___x_3196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3193_, v___f_3148_, v_sz_3194_, v___x_3195_, v_segments_3190_);
v___x_3197_ = lean_array_to_list(v___x_3196_);
v_result_3198_ = l_String_intercalate(v___x_3192_, v___x_3197_);
if (v_absolute_3191_ == 0)
{
v___y_3177_ = v_result_3198_;
goto v___jp_3176_;
}
else
{
lean_object* v___x_3199_; 
v___x_3199_ = lean_string_append(v___x_3192_, v_result_3198_);
lean_dec_ref(v_result_3198_);
v___y_3177_ = v___x_3199_;
goto v___jp_3176_;
}
v___jp_3176_:
{
if (lean_obj_tag(v_query_3175_) == 0)
{
lean_dec_ref(v___f_3147_);
v___y_3154_ = v___y_3177_;
goto v___jp_3153_;
}
else
{
lean_object* v_val_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; uint8_t v___x_3181_; 
v_val_3178_ = lean_ctor_get(v_query_3175_, 0);
lean_inc(v_val_3178_);
lean_dec_ref(v_query_3175_);
v___x_3179_ = lean_array_get_size(v_val_3178_);
v___x_3180_ = lean_unsigned_to_nat(0u);
v___x_3181_ = lean_nat_dec_eq(v___x_3179_, v___x_3180_);
if (v___x_3181_ == 0)
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v_encodedParams_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3182_ = lean_array_to_list(v_val_3178_);
v___x_3183_ = lean_box(0);
v_encodedParams_3184_ = l_List_mapTR_loop___redArg(v___f_3147_, v___x_3182_, v___x_3183_);
v___x_3185_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_3186_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_3187_ = l_String_intercalate(v___x_3186_, v_encodedParams_3184_);
v___x_3188_ = lean_string_append(v___x_3185_, v___x_3187_);
lean_dec_ref(v___x_3187_);
v___x_3189_ = lean_string_append(v___y_3177_, v___x_3188_);
lean_dec_ref(v___x_3188_);
v___y_3154_ = v___x_3189_;
goto v___jp_3153_;
}
else
{
lean_dec(v_val_3178_);
lean_dec_ref(v___f_3147_);
v___y_3154_ = v___y_3177_;
goto v___jp_3153_;
}
}
}
}
case 1:
{
lean_object* v_uri_3200_; lean_object* v_scheme_3201_; lean_object* v_authority_3202_; lean_object* v_path_3203_; lean_object* v_query_3204_; lean_object* v_fragment_3205_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3242_; 
lean_dec_ref(v___f_3148_);
lean_dec_ref(v___f_3147_);
v_uri_3200_ = lean_ctor_get(v_target_3152_, 0);
lean_inc_ref(v_uri_3200_);
lean_dec_ref(v_target_3152_);
v_scheme_3201_ = lean_ctor_get(v_uri_3200_, 0);
lean_inc_ref(v_scheme_3201_);
v_authority_3202_ = lean_ctor_get(v_uri_3200_, 1);
lean_inc(v_authority_3202_);
v_path_3203_ = lean_ctor_get(v_uri_3200_, 2);
lean_inc_ref(v_path_3203_);
v_query_3204_ = lean_ctor_get(v_uri_3200_, 3);
lean_inc_ref(v_query_3204_);
v_fragment_3205_ = lean_ctor_get(v_uri_3200_, 4);
lean_inc(v_fragment_3205_);
lean_dec_ref(v_uri_3200_);
if (lean_obj_tag(v_authority_3202_) == 0)
{
lean_object* v___x_3253_; 
v___x_3253_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3242_ = v___x_3253_;
goto v___jp_3241_;
}
else
{
lean_object* v_val_3254_; lean_object* v_userInfo_3255_; lean_object* v_host_3256_; lean_object* v_port_3257_; lean_object* v___x_3258_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3277_; 
v_val_3254_ = lean_ctor_get(v_authority_3202_, 0);
lean_inc(v_val_3254_);
lean_dec_ref(v_authority_3202_);
v_userInfo_3255_ = lean_ctor_get(v_val_3254_, 0);
lean_inc(v_userInfo_3255_);
v_host_3256_ = lean_ctor_get(v_val_3254_, 1);
lean_inc_ref(v_host_3256_);
v_port_3257_ = lean_ctor_get(v_val_3254_, 2);
lean_inc(v_port_3257_);
lean_dec(v_val_3254_);
v___x_3258_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__1));
if (lean_obj_tag(v_userInfo_3255_) == 0)
{
lean_object* v___x_3287_; 
v___x_3287_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3277_ = v___x_3287_;
goto v___jp_3276_;
}
else
{
lean_object* v_val_3288_; lean_object* v_password_3289_; 
v_val_3288_ = lean_ctor_get(v_userInfo_3255_, 0);
lean_inc(v_val_3288_);
lean_dec_ref(v_userInfo_3255_);
v_password_3289_ = lean_ctor_get(v_val_3288_, 1);
if (lean_obj_tag(v_password_3289_) == 0)
{
lean_object* v_username_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v_username_3290_ = lean_ctor_get(v_val_3288_, 0);
lean_inc_ref(v_username_3290_);
lean_dec(v_val_3288_);
v___x_3291_ = lean_string_from_utf8_unchecked(v_username_3290_);
v___x_3292_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3293_ = lean_string_append(v___x_3291_, v___x_3292_);
v___y_3277_ = v___x_3293_;
goto v___jp_3276_;
}
else
{
lean_object* v_username_3294_; lean_object* v_val_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
lean_inc_ref(v_password_3289_);
v_username_3294_ = lean_ctor_get(v_val_3288_, 0);
lean_inc_ref(v_username_3294_);
lean_dec(v_val_3288_);
v_val_3295_ = lean_ctor_get(v_password_3289_, 0);
lean_inc(v_val_3295_);
lean_dec_ref(v_password_3289_);
v___x_3296_ = lean_string_from_utf8_unchecked(v_username_3294_);
v___x_3297_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3298_ = lean_string_append(v___x_3296_, v___x_3297_);
v___x_3299_ = lean_string_from_utf8_unchecked(v_val_3295_);
v___x_3300_ = lean_string_append(v___x_3298_, v___x_3299_);
lean_dec_ref(v___x_3299_);
v___x_3301_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3302_ = lean_string_append(v___x_3300_, v___x_3301_);
v___y_3277_ = v___x_3302_;
goto v___jp_3276_;
}
}
v___jp_3259_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3263_ = lean_string_append(v___y_3261_, v___y_3260_);
lean_dec_ref(v___y_3260_);
v___x_3264_ = lean_string_append(v___x_3263_, v___y_3262_);
lean_dec_ref(v___y_3262_);
v___x_3265_ = lean_string_append(v___x_3258_, v___x_3264_);
lean_dec_ref(v___x_3264_);
v___y_3242_ = v___x_3265_;
goto v___jp_3241_;
}
v___jp_3266_:
{
switch(lean_obj_tag(v_port_3257_))
{
case 0:
{
lean_object* v___x_3269_; 
v___x_3269_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3260_ = v___y_3268_;
v___y_3261_ = v___y_3267_;
v___y_3262_ = v___x_3269_;
goto v___jp_3259_;
}
case 1:
{
lean_object* v___x_3270_; 
v___x_3270_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3260_ = v___y_3268_;
v___y_3261_ = v___y_3267_;
v___y_3262_ = v___x_3270_;
goto v___jp_3259_;
}
default: 
{
uint16_t v_port_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v_port_3271_ = lean_ctor_get_uint16(v_port_3257_, 0);
lean_dec_ref(v_port_3257_);
v___x_3272_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3273_ = lean_uint16_to_nat(v_port_3271_);
v___x_3274_ = l_Nat_reprFast(v___x_3273_);
v___x_3275_ = lean_string_append(v___x_3272_, v___x_3274_);
lean_dec_ref(v___x_3274_);
v___y_3260_ = v___y_3268_;
v___y_3261_ = v___y_3267_;
v___y_3262_ = v___x_3275_;
goto v___jp_3259_;
}
}
}
v___jp_3276_:
{
switch(lean_obj_tag(v_host_3256_))
{
case 0:
{
lean_object* v_name_3278_; 
v_name_3278_ = lean_ctor_get(v_host_3256_, 0);
lean_inc_ref(v_name_3278_);
lean_dec_ref(v_host_3256_);
v___y_3267_ = v___y_3277_;
v___y_3268_ = v_name_3278_;
goto v___jp_3266_;
}
case 1:
{
lean_object* v_ipv4_3279_; lean_object* v___x_3280_; 
v_ipv4_3279_ = lean_ctor_get(v_host_3256_, 0);
lean_inc_ref(v_ipv4_3279_);
lean_dec_ref(v_host_3256_);
v___x_3280_ = lean_uv_ntop_v4(v_ipv4_3279_);
lean_dec_ref(v_ipv4_3279_);
v___y_3267_ = v___y_3277_;
v___y_3268_ = v___x_3280_;
goto v___jp_3266_;
}
default: 
{
lean_object* v_ipv6_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v_ipv6_3281_ = lean_ctor_get(v_host_3256_, 0);
lean_inc_ref(v_ipv6_3281_);
lean_dec_ref(v_host_3256_);
v___x_3282_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3283_ = lean_uv_ntop_v6(v_ipv6_3281_);
lean_dec_ref(v_ipv6_3281_);
v___x_3284_ = lean_string_append(v___x_3282_, v___x_3283_);
lean_dec_ref(v___x_3283_);
v___x_3285_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3286_ = lean_string_append(v___x_3284_, v___x_3285_);
v___y_3267_ = v___y_3277_;
v___y_3268_ = v___x_3286_;
goto v___jp_3266_;
}
}
}
}
v___jp_3206_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3211_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3212_ = lean_string_append(v_scheme_3201_, v___x_3211_);
v___x_3213_ = lean_string_append(v___x_3212_, v___y_3208_);
lean_dec_ref(v___y_3208_);
v___x_3214_ = lean_string_append(v___x_3213_, v___y_3209_);
lean_dec_ref(v___y_3209_);
v___x_3215_ = lean_string_append(v___x_3214_, v___y_3207_);
lean_dec_ref(v___y_3207_);
v___x_3216_ = lean_string_append(v___x_3215_, v___y_3210_);
lean_dec_ref(v___y_3210_);
v___y_3154_ = v___x_3216_;
goto v___jp_3153_;
}
v___jp_3217_:
{
if (lean_obj_tag(v_fragment_3205_) == 0)
{
lean_object* v___x_3221_; 
v___x_3221_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3207_ = v___y_3220_;
v___y_3208_ = v___y_3218_;
v___y_3209_ = v___y_3219_;
v___y_3210_ = v___x_3221_;
goto v___jp_3206_;
}
else
{
lean_object* v_val_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v_val_3222_ = lean_ctor_get(v_fragment_3205_, 0);
lean_inc(v_val_3222_);
lean_dec_ref(v_fragment_3205_);
v___x_3223_ = ((lean_object*)(l_Std_Http_instToStringURI___lam__2___closed__0));
v___x_3224_ = l_Std_Http_URI_EncodedFragment_encode(v_val_3222_);
lean_dec(v_val_3222_);
v___x_3225_ = lean_string_from_utf8_unchecked(v___x_3224_);
v___x_3226_ = lean_string_append(v___x_3223_, v___x_3225_);
lean_dec_ref(v___x_3225_);
v___y_3207_ = v___y_3220_;
v___y_3208_ = v___y_3218_;
v___y_3209_ = v___y_3219_;
v___y_3210_ = v___x_3226_;
goto v___jp_3206_;
}
}
v___jp_3227_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___x_3230_ = lean_array_get_size(v_query_3204_);
v___x_3231_ = lean_unsigned_to_nat(0u);
v___x_3232_ = lean_nat_dec_eq(v___x_3230_, v___x_3231_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v_encodedParams_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3233_ = lean_array_to_list(v_query_3204_);
v___x_3234_ = lean_box(0);
v_encodedParams_3235_ = l_List_mapTR_loop___redArg(v___f_3149_, v___x_3233_, v___x_3234_);
v___x_3236_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___lam__1___closed__0));
v___x_3237_ = ((lean_object*)(l_Std_Http_URI_Query_toRawString___closed__0));
v___x_3238_ = l_String_intercalate(v___x_3237_, v_encodedParams_3235_);
v___x_3239_ = lean_string_append(v___x_3236_, v___x_3238_);
lean_dec_ref(v___x_3238_);
v___y_3218_ = v___y_3228_;
v___y_3219_ = v___y_3229_;
v___y_3220_ = v___x_3239_;
goto v___jp_3217_;
}
else
{
lean_object* v___x_3240_; 
lean_dec_ref(v_query_3204_);
lean_dec_ref(v___f_3149_);
v___x_3240_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3218_ = v___y_3228_;
v___y_3219_ = v___y_3229_;
v___y_3220_ = v___x_3240_;
goto v___jp_3217_;
}
}
v___jp_3241_:
{
lean_object* v_segments_3243_; uint8_t v_absolute_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; size_t v_sz_3247_; size_t v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v_result_3251_; 
v_segments_3243_ = lean_ctor_get(v_path_3203_, 0);
lean_inc_ref(v_segments_3243_);
v_absolute_3244_ = lean_ctor_get_uint8(v_path_3203_, sizeof(void*)*1);
lean_dec_ref(v_path_3203_);
v___x_3245_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__0));
v___x_3246_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___lam__1___closed__10));
v_sz_3247_ = lean_array_size(v_segments_3243_);
v___x_3248_ = ((size_t)0ULL);
v___x_3249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3246_, v___f_3150_, v_sz_3247_, v___x_3248_, v_segments_3243_);
v___x_3250_ = lean_array_to_list(v___x_3249_);
v_result_3251_ = l_String_intercalate(v___x_3245_, v___x_3250_);
if (v_absolute_3244_ == 0)
{
v___y_3228_ = v___y_3242_;
v___y_3229_ = v_result_3251_;
goto v___jp_3227_;
}
else
{
lean_object* v___x_3252_; 
v___x_3252_ = lean_string_append(v___x_3245_, v_result_3251_);
lean_dec_ref(v_result_3251_);
v___y_3228_ = v___y_3242_;
v___y_3229_ = v___x_3252_;
goto v___jp_3227_;
}
}
}
case 2:
{
lean_object* v_authority_3303_; lean_object* v_userInfo_3304_; lean_object* v_host_3305_; lean_object* v_port_3306_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3318_; 
lean_dec_ref(v___f_3150_);
lean_dec_ref(v___f_3149_);
lean_dec_ref(v___f_3148_);
lean_dec_ref(v___f_3147_);
v_authority_3303_ = lean_ctor_get(v_target_3152_, 0);
lean_inc_ref(v_authority_3303_);
lean_dec_ref(v_target_3152_);
v_userInfo_3304_ = lean_ctor_get(v_authority_3303_, 0);
lean_inc(v_userInfo_3304_);
v_host_3305_ = lean_ctor_get(v_authority_3303_, 1);
lean_inc_ref(v_host_3305_);
v_port_3306_ = lean_ctor_get(v_authority_3303_, 2);
lean_inc(v_port_3306_);
lean_dec_ref(v_authority_3303_);
if (lean_obj_tag(v_userInfo_3304_) == 0)
{
lean_object* v___x_3328_; 
v___x_3328_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3318_ = v___x_3328_;
goto v___jp_3317_;
}
else
{
lean_object* v_val_3329_; lean_object* v_password_3330_; 
v_val_3329_ = lean_ctor_get(v_userInfo_3304_, 0);
lean_inc(v_val_3329_);
lean_dec_ref(v_userInfo_3304_);
v_password_3330_ = lean_ctor_get(v_val_3329_, 1);
if (lean_obj_tag(v_password_3330_) == 0)
{
lean_object* v_username_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v_username_3331_ = lean_ctor_get(v_val_3329_, 0);
lean_inc_ref(v_username_3331_);
lean_dec(v_val_3329_);
v___x_3332_ = lean_string_from_utf8_unchecked(v_username_3331_);
v___x_3333_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3334_ = lean_string_append(v___x_3332_, v___x_3333_);
v___y_3318_ = v___x_3334_;
goto v___jp_3317_;
}
else
{
lean_object* v_username_3335_; lean_object* v_val_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
lean_inc_ref(v_password_3330_);
v_username_3335_ = lean_ctor_get(v_val_3329_, 0);
lean_inc_ref(v_username_3335_);
lean_dec(v_val_3329_);
v_val_3336_ = lean_ctor_get(v_password_3330_, 0);
lean_inc(v_val_3336_);
lean_dec_ref(v_password_3330_);
v___x_3337_ = lean_string_from_utf8_unchecked(v_username_3335_);
v___x_3338_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3339_ = lean_string_append(v___x_3337_, v___x_3338_);
v___x_3340_ = lean_string_from_utf8_unchecked(v_val_3336_);
v___x_3341_ = lean_string_append(v___x_3339_, v___x_3340_);
lean_dec_ref(v___x_3340_);
v___x_3342_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__2));
v___x_3343_ = lean_string_append(v___x_3341_, v___x_3342_);
v___y_3318_ = v___x_3343_;
goto v___jp_3317_;
}
}
v___jp_3307_:
{
switch(lean_obj_tag(v_port_3306_))
{
case 0:
{
lean_object* v___x_3310_; 
v___x_3310_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__0));
v___y_3169_ = v___y_3308_;
v___y_3170_ = v___y_3309_;
v___y_3171_ = v___x_3310_;
goto v___jp_3168_;
}
case 1:
{
lean_object* v___x_3311_; 
v___x_3311_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___y_3169_ = v___y_3308_;
v___y_3170_ = v___y_3309_;
v___y_3171_ = v___x_3311_;
goto v___jp_3168_;
}
default: 
{
uint16_t v_port_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_port_3312_ = lean_ctor_get_uint16(v_port_3306_, 0);
lean_dec_ref(v_port_3306_);
v___x_3313_ = ((lean_object*)(l_Std_Http_URI_instToStringAuthority___lam__0___closed__1));
v___x_3314_ = lean_uint16_to_nat(v_port_3312_);
v___x_3315_ = l_Nat_reprFast(v___x_3314_);
v___x_3316_ = lean_string_append(v___x_3313_, v___x_3315_);
lean_dec_ref(v___x_3315_);
v___y_3169_ = v___y_3308_;
v___y_3170_ = v___y_3309_;
v___y_3171_ = v___x_3316_;
goto v___jp_3168_;
}
}
}
v___jp_3317_:
{
switch(lean_obj_tag(v_host_3305_))
{
case 0:
{
lean_object* v_name_3319_; 
v_name_3319_ = lean_ctor_get(v_host_3305_, 0);
lean_inc_ref(v_name_3319_);
lean_dec_ref(v_host_3305_);
v___y_3308_ = v___y_3318_;
v___y_3309_ = v_name_3319_;
goto v___jp_3307_;
}
case 1:
{
lean_object* v_ipv4_3320_; lean_object* v___x_3321_; 
v_ipv4_3320_ = lean_ctor_get(v_host_3305_, 0);
lean_inc_ref(v_ipv4_3320_);
lean_dec_ref(v_host_3305_);
v___x_3321_ = lean_uv_ntop_v4(v_ipv4_3320_);
lean_dec_ref(v_ipv4_3320_);
v___y_3308_ = v___y_3318_;
v___y_3309_ = v___x_3321_;
goto v___jp_3307_;
}
default: 
{
lean_object* v_ipv6_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v_ipv6_3322_ = lean_ctor_get(v_host_3305_, 0);
lean_inc_ref(v_ipv6_3322_);
lean_dec_ref(v_host_3305_);
v___x_3323_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__0));
v___x_3324_ = lean_uv_ntop_v6(v_ipv6_3322_);
lean_dec_ref(v_ipv6_3322_);
v___x_3325_ = lean_string_append(v___x_3323_, v___x_3324_);
lean_dec_ref(v___x_3324_);
v___x_3326_ = ((lean_object*)(l_Std_Http_URI_instToStringHost___lam__0___closed__1));
v___x_3327_ = lean_string_append(v___x_3325_, v___x_3326_);
v___y_3308_ = v___y_3318_;
v___y_3309_ = v___x_3327_;
goto v___jp_3307_;
}
}
}
}
default: 
{
lean_object* v___x_3344_; 
lean_dec_ref(v___f_3150_);
lean_dec_ref(v___f_3149_);
lean_dec_ref(v___f_3148_);
lean_dec_ref(v___f_3147_);
v___x_3344_ = ((lean_object*)(l_Std_Http_RequestTarget_instToString___lam__4___closed__0));
v___y_3154_ = v___x_3344_;
goto v___jp_3153_;
}
}
v___jp_3153_:
{
lean_object* v_data_3155_; lean_object* v_size_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3167_; 
v_data_3155_ = lean_ctor_get(v_buffer_3151_, 0);
v_size_3156_ = lean_ctor_get(v_buffer_3151_, 1);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_buffer_3151_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3158_ = v_buffer_3151_;
v_isShared_3159_ = v_isSharedCheck_3167_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_size_3156_);
lean_inc(v_data_3155_);
lean_dec(v_buffer_3151_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3167_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3165_; 
v___x_3160_ = lean_string_to_utf8(v___y_3154_);
lean_dec_ref(v___y_3154_);
lean_inc_ref(v___x_3160_);
v___x_3161_ = lean_array_push(v_data_3155_, v___x_3160_);
v___x_3162_ = lean_byte_array_size(v___x_3160_);
lean_dec_ref(v___x_3160_);
v___x_3163_ = lean_nat_add(v_size_3156_, v___x_3162_);
lean_dec(v_size_3156_);
if (v_isShared_3159_ == 0)
{
lean_ctor_set(v___x_3158_, 1, v___x_3163_);
lean_ctor_set(v___x_3158_, 0, v___x_3161_);
v___x_3165_ = v___x_3158_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3161_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v___x_3163_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
v___jp_3168_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = lean_string_append(v___y_3169_, v___y_3170_);
lean_dec_ref(v___y_3170_);
v___x_3173_ = lean_string_append(v___x_3172_, v___y_3171_);
lean_dec_ref(v___y_3171_);
v___y_3154_ = v___x_3173_;
goto v___jp_3153_;
}
}
}
static lean_object* _init_l_Std_Http_RequestTarget_instEncodeV11___closed__0(void){
_start:
{
lean_object* v___f_3345_; lean_object* v___f_3346_; lean_object* v___f_3347_; 
v___f_3345_ = ((lean_object*)(l_Std_Http_URI_instToStringPath___closed__0));
v___f_3346_ = ((lean_object*)(l_Std_Http_URI_Query_instToString___closed__0));
v___f_3347_ = lean_alloc_closure((void*)(l_Std_Http_RequestTarget_instEncodeV11___lam__4), 6, 4);
lean_closure_set(v___f_3347_, 0, v___f_3346_);
lean_closure_set(v___f_3347_, 1, v___f_3345_);
lean_closure_set(v___f_3347_, 2, v___f_3346_);
lean_closure_set(v___f_3347_, 3, v___f_3345_);
return v___f_3347_;
}
}
static lean_object* _init_l_Std_Http_RequestTarget_instEncodeV11(void){
_start:
{
lean_object* v___f_3348_; 
v___f_3348_ = lean_obj_once(&l_Std_Http_RequestTarget_instEncodeV11___closed__0, &l_Std_Http_RequestTarget_instEncodeV11___closed__0_once, _init_l_Std_Http_RequestTarget_instEncodeV11___closed__0);
return v___f_3348_;
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
l_Std_Http_URI_instInhabitedQuery = _init_l_Std_Http_URI_instInhabitedQuery();
lean_mark_persistent(l_Std_Http_URI_instInhabitedQuery);
l_Std_Http_URI_instBEqQuery = _init_l_Std_Http_URI_instBEqQuery();
lean_mark_persistent(l_Std_Http_URI_instBEqQuery);
l_Std_Http_URI_instInhabitedBuilder_default = _init_l_Std_Http_URI_instInhabitedBuilder_default();
lean_mark_persistent(l_Std_Http_URI_instInhabitedBuilder_default);
l_Std_Http_URI_instInhabitedBuilder = _init_l_Std_Http_URI_instInhabitedBuilder();
lean_mark_persistent(l_Std_Http_URI_instInhabitedBuilder);
l_Std_Http_URI_Builder_empty = _init_l_Std_Http_URI_Builder_empty();
lean_mark_persistent(l_Std_Http_URI_Builder_empty);
l_Std_Http_RequestTarget_instToString = _init_l_Std_Http_RequestTarget_instToString();
lean_mark_persistent(l_Std_Http_RequestTarget_instToString);
l_Std_Http_RequestTarget_instEncodeV11 = _init_l_Std_Http_RequestTarget_instEncodeV11();
lean_mark_persistent(l_Std_Http_RequestTarget_instEncodeV11);
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
