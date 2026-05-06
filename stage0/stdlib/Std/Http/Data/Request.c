// Lean compiler output
// Module: Std.Http.Data.Request
// Imports: public import Std.Http.Data.Extensions public import Std.Http.Data.Method public import Std.Http.Data.Version public import Std.Http.Data.Headers public import Std.Http.Data.URI
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
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* l_Std_Http_URI_Query_formatQueryParam(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Headers_fold___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_uv_ntop_v4(lean_object*);
lean_object* lean_uv_ntop_v6(lean_object*);
lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_Extensions_empty;
extern lean_object* l_Std_Http_Headers_empty;
lean_object* l_Std_Http_instReprMethod_repr(uint8_t, lean_object*);
lean_object* l_Std_Http_instReprVersion_repr(uint8_t, lean_object*);
lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object*, lean_object*);
lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_instInhabitedRequestTarget_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Std_Http_Header_Name_ofString_x21(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* l_Std_Http_Extensions_compareName___boxed(lean_object*, lean_object*);
lean_object* l_Std_Http_Header_Name_ofString_x3f(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x3f(lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Request_instInhabitedHead_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instInhabitedHead_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Request_instInhabitedHead_default;
LEAN_EXPORT lean_object* l_Std_Http_Request_instInhabitedHead;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Request_instReprHead_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Request_instReprHead_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Http_Request_instReprHead_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "method"};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_Request_instReprHead_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_Request_instReprHead_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Http_Request_instReprHead_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__4 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Http_Request_instReprHead_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Http_Request_instReprHead_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__3_value),((lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__6 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Http_Request_instReprHead_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__7;
static const lean_string_object l_Std_Http_Request_instReprHead_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__8 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Http_Request_instReprHead_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__9 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Http_Request_instReprHead_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__10 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Http_Request_instReprHead_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__11 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__11_value;
static lean_once_cell_t l_Std_Http_Request_instReprHead_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__12;
static const lean_string_object l_Std_Http_Request_instReprHead_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "uri"};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__13 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__13_value;
static const lean_ctor_object l_Std_Http_Request_instReprHead_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__13_value)}};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__14 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__14_value;
static lean_once_cell_t l_Std_Http_Request_instReprHead_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__15;
static const lean_string_object l_Std_Http_Request_instReprHead_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "headers"};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__16 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__16_value;
static const lean_ctor_object l_Std_Http_Request_instReprHead_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__16_value)}};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__17 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__17_value;
static const lean_string_object l_Std_Http_Request_instReprHead_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__18 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__18_value;
static lean_once_cell_t l_Std_Http_Request_instReprHead_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__19;
static lean_once_cell_t l_Std_Http_Request_instReprHead_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__20;
static const lean_ctor_object l_Std_Http_Request_instReprHead_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__21 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__21_value;
static const lean_ctor_object l_Std_Http_Request_instReprHead_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__18_value)}};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__22 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__22_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_instReprHead_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instReprHead_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instReprHead_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Request_instReprHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instReprHead_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instReprHead___closed__0 = (const lean_object*)&l_Std_Http_Request_instReprHead___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Request_instReprHead = (const lean_object*)&l_Std_Http_Request_instReprHead___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__3___closed__0 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__3___closed__0_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__3___closed__1 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__3___closed__1_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__3___closed__2 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__3___closed__2_value;
static lean_once_cell_t l_Std_Http_Request_instToStringHead___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instToStringHead___lam__3___closed__3;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__3___closed__4 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__3___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__3___boxed__const__1;
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__3(lean_object*);
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__0 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__0_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__1 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__1_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__2 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__2_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__3 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__3_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__4 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__4_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__5 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__5_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__6 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__6_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__7 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__7_value;
static const lean_ctor_object l_Std_Http_Request_instToStringHead___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__1_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__2_value)}};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__8 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__8_value;
static const lean_ctor_object l_Std_Http_Request_instToStringHead___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__8_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__3_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__4_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__5_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__6_value)}};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__9 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__9_value;
static const lean_ctor_object l_Std_Http_Request_instToStringHead___lam__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__9_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__7_value)}};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__10 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__10_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.0"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__11 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__11_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.1"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__12 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__12_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/2.0"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__13 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__13_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/3.0"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__14 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__14_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__15 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__15_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "&"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__16 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__16_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__17 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__17_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__18 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__18_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__19 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__19_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__20 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__20_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__21 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__21_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__22 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__22_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "//"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__23 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__23_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__24 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__24_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__25 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__25_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ACL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__26 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__26_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BASELINE-CONTROL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__27 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__27_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "BIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__28 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__28_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CHECKIN"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__29 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__29_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CHECKOUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__30 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__30_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CONNECT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__31 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__31_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COPY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__32 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__32_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DELETE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__33 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__33_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__34 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__34_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__35 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__35_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "LABEL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__36 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__36_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LINK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__37 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__37_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LOCK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__38 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__38_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MERGE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__39 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__39_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKACTIVITY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__40 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__40_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKCALENDAR"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__41 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__41_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MKCOL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__42 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__42_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MKREDIRECTREF"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__43 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__43_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MKWORKSPACE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__44 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__44_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MOVE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__45 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__45_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__46 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__46_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ORDERPATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__47 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__47_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__48 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__48_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__49 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__49_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRI"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__50 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__50_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PROPFIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__51 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__51_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PROPPATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__52 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__52_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__53 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__53_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "QUERY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__54 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__54_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REBIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__55 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__55_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REPORT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__56 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__56_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SEARCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__57 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__57_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TRACE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__58 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__58_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNBIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__59 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__59_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UNCHECKOUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__60 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__60_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLINK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__61 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__61_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLOCK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__62 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__62_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UPDATE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__63 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__63_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UPDATEREDIRECTREF"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__64 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__64_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "VERSION-CONTROL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__65 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__65_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__0 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__1 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__1_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__2 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__2_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__6, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___closed__2_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__1_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__1_value)} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__3 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__3_value;
LEAN_EXPORT const lean_object* l_Std_Http_Request_instToStringHead = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__4___closed__1;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Request_instEncodeV11Head___lam__4___closed__2;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__4___closed__4;
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Request_instEncodeV11Head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instEncodeV11Head___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instEncodeV11Head___closed__0 = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__0_value;
static const lean_closure_object l_Std_Http_Request_instEncodeV11Head___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instEncodeV11Head___lam__4, .m_arity = 7, .m_num_fixed = 5, .m_objs = {((lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__0_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__1_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__1_value)} };
static const lean_object* l_Std_Http_Request_instEncodeV11Head___closed__1 = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Request_instEncodeV11Head = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__1_value;
static lean_once_cell_t l_Std_Http_Request_new___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_new___closed__0;
static lean_once_cell_t l_Std_Http_Request_new___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_new___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_Request_new;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Request_Builder_uri_x21___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l_Std_Http_Request_Builder_uri_x21___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Request_Builder_uri_x21___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Request_Builder_uri_x21___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Request_Builder_uri_x21___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Request_Builder_uri_x21___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Request_Builder_uri_x21___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Request_Builder_uri_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*9 + 0, .m_other = 9, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(253) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(256) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(128) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(100) << 1) | 1))}};
static const lean_object* l_Std_Http_Request_Builder_uri_x21___closed__0 = (const lean_object*)&l_Std_Http_Request_Builder_uri_x21___closed__0_value;
static const lean_closure_object l_Std_Http_Request_Builder_uri_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_Builder_uri_x21___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Request_Builder_uri_x21___closed__0_value)} };
static const lean_object* l_Std_Http_Request_Builder_uri_x21___closed__1 = (const lean_object*)&l_Std_Http_Request_Builder_uri_x21___closed__1_value;
static const lean_string_object l_Std_Http_Request_Builder_uri_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Std.Http.Data.URI"};
static const lean_object* l_Std_Http_Request_Builder_uri_x21___closed__2 = (const lean_object*)&l_Std_Http_Request_Builder_uri_x21___closed__2_value;
static const lean_string_object l_Std_Http_Request_Builder_uri_x21___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Std.Http.RequestTarget.parse!"};
static const lean_object* l_Std_Http_Request_Builder_uri_x21___closed__3 = (const lean_object*)&l_Std_Http_Request_Builder_uri_x21___closed__3_value;
static const lean_string_object l_Std_Http_Request_Builder_uri_x21___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid request target"};
static const lean_object* l_Std_Http_Request_Builder_uri_x21___closed__4 = (const lean_object*)&l_Std_Http_Request_Builder_uri_x21___closed__4_value;
static lean_once_cell_t l_Std_Http_Request_Builder_uri_x21___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_Builder_uri_x21___closed__5;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headers(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headerOpt(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Request_Builder_extension___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Extensions_compareName___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_Builder_extension___redArg___closed__0 = (const lean_object*)&l_Std_Http_Request_Builder_extension___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Request_get___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_get___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Request_get(lean_object*);
static lean_once_cell_t l_Std_Http_Request_post___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_post___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Request_post(lean_object*);
static lean_once_cell_t l_Std_Http_Request_put___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_put___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Request_put(lean_object*);
static lean_once_cell_t l_Std_Http_Request_delete___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_delete___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Request_delete(lean_object*);
static lean_once_cell_t l_Std_Http_Request_patch___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_patch___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Request_patch(lean_object*);
static lean_once_cell_t l_Std_Http_Request_head___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_head___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Request_head(lean_object*);
static lean_once_cell_t l_Std_Http_Request_options___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_options___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Request_options(lean_object*);
static lean_once_cell_t l_Std_Http_Request_connect___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_connect___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Request_connect(lean_object*);
static lean_once_cell_t l_Std_Http_Request_trace___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_trace___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Request_trace(lean_object*);
static lean_object* _init_l_Std_Http_Request_instInhabitedHead_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; uint8_t v___x_3_; uint8_t v___x_4_; lean_object* v___x_5_; 
v___x_1_ = l_Std_Http_Headers_empty;
v___x_2_ = lean_box(3);
v___x_3_ = 0;
v___x_4_ = 0;
v___x_5_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_5_, 0, v___x_2_);
lean_ctor_set(v___x_5_, 1, v___x_1_);
lean_ctor_set_uint8(v___x_5_, sizeof(void*)*2, v___x_4_);
lean_ctor_set_uint8(v___x_5_, sizeof(void*)*2 + 1, v___x_3_);
return v___x_5_;
}
}
static lean_object* _init_l_Std_Http_Request_instInhabitedHead_default(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_obj_once(&l_Std_Http_Request_instInhabitedHead_default___closed__0, &l_Std_Http_Request_instInhabitedHead_default___closed__0_once, _init_l_Std_Http_Request_instInhabitedHead_default___closed__0);
return v___x_6_;
}
}
static lean_object* _init_l_Std_Http_Request_instInhabitedHead(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Std_Http_Request_instInhabitedHead_default;
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Request_instReprHead_repr_spec__0(lean_object* v_a_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_nat_to_int(v_a_8_);
return v___x_9_;
}
}
static lean_object* _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_unsigned_to_nat(10u);
v___x_24_ = lean_nat_to_int(v___x_23_);
return v___x_24_;
}
}
static lean_object* _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_unsigned_to_nat(11u);
v___x_32_ = lean_nat_to_int(v___x_31_);
return v___x_32_;
}
}
static lean_object* _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(7u);
v___x_37_ = lean_nat_to_int(v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__0));
v___x_43_ = lean_string_length(v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_obj_once(&l_Std_Http_Request_instReprHead_repr___redArg___closed__19, &l_Std_Http_Request_instReprHead_repr___redArg___closed__19_once, _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__19);
v___x_45_ = lean_nat_to_int(v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instReprHead_repr___redArg(lean_object* v_x_50_){
_start:
{
uint8_t v_method_51_; uint8_t v_version_52_; lean_object* v_uri_53_; lean_object* v_headers_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_method_51_ = lean_ctor_get_uint8(v_x_50_, sizeof(void*)*2);
v_version_52_ = lean_ctor_get_uint8(v_x_50_, sizeof(void*)*2 + 1);
v_uri_53_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_uri_53_);
v_headers_54_ = lean_ctor_get(v_x_50_, 1);
lean_inc_ref(v_headers_54_);
lean_dec_ref(v_x_50_);
v___x_55_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__5));
v___x_56_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__6));
v___x_57_ = lean_obj_once(&l_Std_Http_Request_instReprHead_repr___redArg___closed__7, &l_Std_Http_Request_instReprHead_repr___redArg___closed__7_once, _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__7);
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = l_Std_Http_instReprMethod_repr(v_method_51_, v___x_58_);
v___x_60_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_57_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = 0;
v___x_62_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_62_, 0, v___x_60_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*1, v___x_61_);
v___x_63_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_56_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__9));
v___x_65_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
v___x_66_ = lean_box(1);
v___x_67_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_65_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__11));
v___x_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___x_55_);
v___x_71_ = lean_obj_once(&l_Std_Http_Request_instReprHead_repr___redArg___closed__12, &l_Std_Http_Request_instReprHead_repr___redArg___closed__12_once, _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__12);
v___x_72_ = l_Std_Http_instReprVersion_repr(v_version_52_, v___x_58_);
v___x_73_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set_uint8(v___x_74_, sizeof(void*)*1, v___x_61_);
v___x_75_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_70_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_64_);
v___x_77_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___x_66_);
v___x_78_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__14));
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_55_);
v___x_81_ = lean_obj_once(&l_Std_Http_Request_instReprHead_repr___redArg___closed__15, &l_Std_Http_Request_instReprHead_repr___redArg___closed__15_once, _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__15);
v___x_82_ = l_Std_Http_instReprRequestTarget_repr(v_uri_53_, v___x_58_);
v___x_83_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___x_61_);
v___x_85_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_80_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_64_);
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_66_);
v___x_88_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__17));
v___x_89_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_55_);
v___x_91_ = l_Std_Http_instReprHeaders_repr___redArg(v_headers_54_);
v___x_92_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_71_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*1, v___x_61_);
v___x_94_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_90_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = lean_obj_once(&l_Std_Http_Request_instReprHead_repr___redArg___closed__20, &l_Std_Http_Request_instReprHead_repr___redArg___closed__20_once, _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__20);
v___x_96_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__21));
v___x_97_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_94_);
v___x_98_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__22));
v___x_99_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_97_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_95_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*1, v___x_61_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instReprHead_repr(lean_object* v_x_102_, lean_object* v_prec_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instReprHead_repr___boxed(lean_object* v_x_105_, lean_object* v_prec_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_Http_Request_instReprHead_repr(v_x_105_, v_prec_106_);
lean_dec(v_prec_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest_default___redArg(lean_object* v_inst_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = l_Std_Http_Request_instInhabitedHead_default;
v___x_112_ = l_Std_Http_Extensions_empty;
v___x_113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set(v___x_113_, 1, v_inst_110_);
lean_ctor_set(v___x_113_, 2, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest_default(lean_object* v_t_114_, lean_object* v_inst_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Std_Http_instInhabitedRequest_default___redArg(v_inst_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest___redArg(lean_object* v_inst_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Std_Http_instInhabitedRequest_default___redArg(v_inst_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest(lean_object* v_a_119_, lean_object* v_inst_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Std_Http_instInhabitedRequest_default___redArg(v_inst_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__0(lean_object* v_x_122_){
_start:
{
lean_object* v_fst_123_; lean_object* v_snd_124_; lean_object* v___x_125_; 
v_fst_123_ = lean_ctor_get(v_x_122_, 0);
lean_inc(v_fst_123_);
v_snd_124_ = lean_ctor_get(v_x_122_, 1);
lean_inc(v_snd_124_);
lean_dec_ref(v_x_122_);
v___x_125_ = l_Std_Http_URI_Query_formatQueryParam(v_fst_123_, v_snd_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__1(lean_object* v_x_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_string_from_utf8_unchecked(v_x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2(lean_object* v___x_128_, lean_object* v___x_129_, lean_object* v___x_130_, lean_object* v_fst_131_, lean_object* v___x_132_, uint32_t v___x_133_, lean_object* v___x_134_, lean_object* v_it_135_, lean_object* v_acc_136_, lean_object* v_hP_137_, lean_object* v_recur_138_){
_start:
{
lean_object* v_it_140_; lean_object* v_out_141_; lean_object* v_it_157_; lean_object* v_startInclusive_158_; lean_object* v_endExclusive_159_; 
if (lean_obj_tag(v_it_135_) == 0)
{
lean_object* v_currPos_171_; lean_object* v_searcher_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_194_; 
v_currPos_171_ = lean_ctor_get(v_it_135_, 0);
v_searcher_172_ = lean_ctor_get(v_it_135_, 1);
v_isSharedCheck_194_ = !lean_is_exclusive(v_it_135_);
if (v_isSharedCheck_194_ == 0)
{
v___x_174_ = v_it_135_;
v_isShared_175_ = v_isSharedCheck_194_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_searcher_172_);
lean_inc(v_currPos_171_);
lean_dec(v_it_135_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_194_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
uint8_t v___x_176_; 
v___x_176_ = lean_nat_dec_eq(v_searcher_172_, v___x_132_);
if (v___x_176_ == 0)
{
uint32_t v___x_177_; uint8_t v___x_178_; 
lean_dec(v___x_132_);
v___x_177_ = lean_string_utf8_get_fast(v_fst_131_, v_searcher_172_);
v___x_178_ = lean_uint32_dec_eq(v___x_177_, v___x_133_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_string_utf8_next_fast(v_fst_131_, v_searcher_172_);
lean_dec(v_searcher_172_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v___x_179_);
v___x_181_ = v___x_174_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_currPos_171_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_179_);
v___x_181_ = v_reuseFailAlloc_183_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; 
v___x_182_ = lean_apply_4(v_recur_138_, v___x_181_, v_acc_136_, lean_box(0), lean_box(0));
return v___x_182_;
}
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_slice_187_; lean_object* v_nextIt_189_; 
v___x_184_ = lean_string_utf8_next_fast(v_fst_131_, v_searcher_172_);
v___x_185_ = lean_nat_sub(v___x_184_, v_searcher_172_);
v___x_186_ = lean_nat_add(v_searcher_172_, v___x_185_);
lean_dec(v___x_185_);
v_slice_187_ = l_String_Slice_subslice_x21(v___x_134_, v_currPos_171_, v_searcher_172_);
lean_inc(v___x_186_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v___x_186_);
lean_ctor_set(v___x_174_, 0, v___x_186_);
v_nextIt_189_ = v___x_174_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___x_186_);
v_nextIt_189_ = v_reuseFailAlloc_192_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v_startInclusive_190_; lean_object* v_endExclusive_191_; 
v_startInclusive_190_ = lean_ctor_get(v_slice_187_, 0);
lean_inc(v_startInclusive_190_);
v_endExclusive_191_ = lean_ctor_get(v_slice_187_, 1);
lean_inc(v_endExclusive_191_);
lean_dec_ref(v_slice_187_);
v_it_157_ = v_nextIt_189_;
v_startInclusive_158_ = v_startInclusive_190_;
v_endExclusive_159_ = v_endExclusive_191_;
goto v___jp_156_;
}
}
}
else
{
lean_object* v___x_193_; 
lean_del_object(v___x_174_);
lean_dec(v_searcher_172_);
v___x_193_ = lean_box(1);
v_it_157_ = v___x_193_;
v_startInclusive_158_ = v_currPos_171_;
v_endExclusive_159_ = v___x_132_;
goto v___jp_156_;
}
}
}
else
{
lean_dec_ref(v_recur_138_);
lean_dec(v___x_132_);
return v_acc_136_;
}
v___jp_139_:
{
if (lean_obj_tag(v_acc_136_) == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_142_, 0, v_out_141_);
v___x_143_ = lean_apply_4(v_recur_138_, v_it_140_, v___x_142_, lean_box(0), lean_box(0));
return v___x_143_;
}
else
{
lean_object* v_val_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_155_; 
v_val_144_ = lean_ctor_get(v_acc_136_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v_acc_136_);
if (v_isSharedCheck_155_ == 0)
{
v___x_146_ = v_acc_136_;
v_isShared_147_ = v_isSharedCheck_155_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_val_144_);
lean_dec(v_acc_136_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_155_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_148_ = lean_string_utf8_extract(v___x_128_, v___x_129_, v___x_130_);
v___x_149_ = lean_string_append(v_val_144_, v___x_148_);
lean_dec_ref(v___x_148_);
v___x_150_ = lean_string_append(v___x_149_, v_out_141_);
lean_dec_ref(v_out_141_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_150_);
v___x_152_ = v___x_146_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_154_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; 
v___x_153_ = lean_apply_4(v_recur_138_, v_it_140_, v___x_152_, lean_box(0), lean_box(0));
return v___x_153_;
}
}
}
}
v___jp_156_:
{
lean_object* v___x_160_; uint32_t v___x_161_; uint32_t v___x_162_; uint8_t v___x_163_; 
v___x_160_ = lean_string_utf8_extract(v_fst_131_, v_startInclusive_158_, v_endExclusive_159_);
lean_dec(v_endExclusive_159_);
lean_dec(v_startInclusive_158_);
v___x_161_ = lean_string_utf8_get(v___x_160_, v___x_129_);
v___x_162_ = 97;
v___x_163_ = lean_uint32_dec_le(v___x_162_, v___x_161_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
v___x_164_ = lean_string_utf8_set(v___x_160_, v___x_129_, v___x_161_);
v_it_140_ = v_it_157_;
v_out_141_ = v___x_164_;
goto v___jp_139_;
}
else
{
uint32_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = 122;
v___x_166_ = lean_uint32_dec_le(v___x_161_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
v___x_167_ = lean_string_utf8_set(v___x_160_, v___x_129_, v___x_161_);
v_it_140_ = v_it_157_;
v_out_141_ = v___x_167_;
goto v___jp_139_;
}
else
{
uint32_t v___x_168_; uint32_t v___x_169_; lean_object* v___x_170_; 
v___x_168_ = 4294967264;
v___x_169_ = lean_uint32_add(v___x_161_, v___x_168_);
v___x_170_ = lean_string_utf8_set(v___x_160_, v___x_129_, v___x_169_);
v_it_140_ = v_it_157_;
v_out_141_ = v___x_170_;
goto v___jp_139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2___boxed(lean_object* v___x_195_, lean_object* v___x_196_, lean_object* v___x_197_, lean_object* v_fst_198_, lean_object* v___x_199_, lean_object* v___x_200_, lean_object* v___x_201_, lean_object* v_it_202_, lean_object* v_acc_203_, lean_object* v_hP_204_, lean_object* v_recur_205_){
_start:
{
uint32_t v___x_1609__boxed_206_; lean_object* v_res_207_; 
v___x_1609__boxed_206_ = lean_unbox_uint32(v___x_200_);
lean_dec(v___x_200_);
v_res_207_ = l_Std_Http_Request_instToStringHead___lam__2(v___x_195_, v___x_196_, v___x_197_, v_fst_198_, v___x_199_, v___x_1609__boxed_206_, v___x_201_, v_it_202_, v_acc_203_, v_hP_204_, v_recur_205_);
lean_dec_ref(v___x_201_);
lean_dec_ref(v_fst_198_);
lean_dec(v___x_197_);
lean_dec(v___x_196_);
lean_dec_ref(v___x_195_);
return v_res_207_;
}
}
static lean_object* _init_l_Std_Http_Request_instToStringHead___lam__3___closed__3(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__2));
v___x_212_ = lean_string_utf8_byte_size(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Std_Http_Request_instToStringHead___lam__3___boxed__const__1(void){
_start:
{
uint32_t v___x_214_; lean_object* v___x_215_; 
v___x_214_ = 45;
v___x_215_ = lean_box_uint32(v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__3(lean_object* v_x_216_){
_start:
{
lean_object* v_fst_217_; lean_object* v_snd_218_; lean_object* v___y_220_; lean_object* v___f_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v_it_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___f_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_fst_217_ = lean_ctor_get(v_x_216_, 0);
lean_inc_n(v_fst_217_, 2);
v_snd_218_ = lean_ctor_get(v_x_216_, 1);
lean_inc(v_snd_218_);
lean_dec_ref(v_x_216_);
v___f_224_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__1));
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_string_utf8_byte_size(v_fst_217_);
v___x_227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_227_, 0, v_fst_217_);
lean_ctor_set(v___x_227_, 1, v___x_225_);
lean_ctor_set(v___x_227_, 2, v___x_226_);
lean_inc_ref(v___x_227_);
v_it_228_ = l_String_Slice_splitToSubslice___redArg(v___x_227_, v___f_224_);
v___x_229_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__2));
v___x_230_ = lean_obj_once(&l_Std_Http_Request_instToStringHead___lam__3___closed__3, &l_Std_Http_Request_instToStringHead___lam__3___closed__3_once, _init_l_Std_Http_Request_instToStringHead___lam__3___closed__3);
v___x_231_ = l_Std_Http_Request_instToStringHead___lam__3___boxed__const__1;
v___f_232_ = lean_alloc_closure((void*)(l_Std_Http_Request_instToStringHead___lam__2___boxed), 11, 7);
lean_closure_set(v___f_232_, 0, v___x_229_);
lean_closure_set(v___f_232_, 1, v___x_225_);
lean_closure_set(v___f_232_, 2, v___x_230_);
lean_closure_set(v___f_232_, 3, v_fst_217_);
lean_closure_set(v___f_232_, 4, v___x_226_);
lean_closure_set(v___f_232_, 5, v___x_231_);
lean_closure_set(v___f_232_, 6, v___x_227_);
v___x_233_ = lean_box(0);
v___x_234_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_232_, v_it_228_, v___x_233_, lean_box(0));
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v___x_235_; 
v___x_235_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__4));
v___y_220_ = v___x_235_;
goto v___jp_219_;
}
else
{
lean_object* v_val_236_; 
v_val_236_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_val_236_);
lean_dec_ref(v___x_234_);
v___y_220_ = v_val_236_;
goto v___jp_219_;
}
v___jp_219_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__0));
v___x_222_ = lean_string_append(v___y_220_, v___x_221_);
v___x_223_ = lean_string_append(v___x_222_, v_snd_218_);
lean_dec(v_snd_218_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__6(lean_object* v___f_312_, lean_object* v___f_313_, lean_object* v___f_314_, lean_object* v___f_315_, lean_object* v___f_316_, lean_object* v_req_317_){
_start:
{
uint8_t v_method_318_; uint8_t v_version_319_; lean_object* v_uri_320_; lean_object* v_headers_321_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v_port_444_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v_host_462_; lean_object* v_port_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v_port_493_; lean_object* v___y_494_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v_host_505_; lean_object* v_port_506_; lean_object* v___y_507_; lean_object* v___y_518_; 
v_method_318_ = lean_ctor_get_uint8(v_req_317_, sizeof(void*)*2);
v_version_319_ = lean_ctor_get_uint8(v_req_317_, sizeof(void*)*2 + 1);
v_uri_320_ = lean_ctor_get(v_req_317_, 0);
lean_inc(v_uri_320_);
v_headers_321_ = lean_ctor_get(v_req_317_, 1);
lean_inc_ref(v_headers_321_);
lean_dec_ref(v_req_317_);
switch(v_method_318_)
{
case 0:
{
lean_object* v___x_590_; 
v___x_590_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__26));
v___y_518_ = v___x_590_;
goto v___jp_517_;
}
case 1:
{
lean_object* v___x_591_; 
v___x_591_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__27));
v___y_518_ = v___x_591_;
goto v___jp_517_;
}
case 2:
{
lean_object* v___x_592_; 
v___x_592_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__28));
v___y_518_ = v___x_592_;
goto v___jp_517_;
}
case 3:
{
lean_object* v___x_593_; 
v___x_593_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__29));
v___y_518_ = v___x_593_;
goto v___jp_517_;
}
case 4:
{
lean_object* v___x_594_; 
v___x_594_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__30));
v___y_518_ = v___x_594_;
goto v___jp_517_;
}
case 5:
{
lean_object* v___x_595_; 
v___x_595_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__31));
v___y_518_ = v___x_595_;
goto v___jp_517_;
}
case 6:
{
lean_object* v___x_596_; 
v___x_596_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__32));
v___y_518_ = v___x_596_;
goto v___jp_517_;
}
case 7:
{
lean_object* v___x_597_; 
v___x_597_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__33));
v___y_518_ = v___x_597_;
goto v___jp_517_;
}
case 8:
{
lean_object* v___x_598_; 
v___x_598_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__34));
v___y_518_ = v___x_598_;
goto v___jp_517_;
}
case 9:
{
lean_object* v___x_599_; 
v___x_599_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__35));
v___y_518_ = v___x_599_;
goto v___jp_517_;
}
case 10:
{
lean_object* v___x_600_; 
v___x_600_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__36));
v___y_518_ = v___x_600_;
goto v___jp_517_;
}
case 11:
{
lean_object* v___x_601_; 
v___x_601_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__37));
v___y_518_ = v___x_601_;
goto v___jp_517_;
}
case 12:
{
lean_object* v___x_602_; 
v___x_602_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__38));
v___y_518_ = v___x_602_;
goto v___jp_517_;
}
case 13:
{
lean_object* v___x_603_; 
v___x_603_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__39));
v___y_518_ = v___x_603_;
goto v___jp_517_;
}
case 14:
{
lean_object* v___x_604_; 
v___x_604_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__40));
v___y_518_ = v___x_604_;
goto v___jp_517_;
}
case 15:
{
lean_object* v___x_605_; 
v___x_605_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__41));
v___y_518_ = v___x_605_;
goto v___jp_517_;
}
case 16:
{
lean_object* v___x_606_; 
v___x_606_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__42));
v___y_518_ = v___x_606_;
goto v___jp_517_;
}
case 17:
{
lean_object* v___x_607_; 
v___x_607_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__43));
v___y_518_ = v___x_607_;
goto v___jp_517_;
}
case 18:
{
lean_object* v___x_608_; 
v___x_608_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__44));
v___y_518_ = v___x_608_;
goto v___jp_517_;
}
case 19:
{
lean_object* v___x_609_; 
v___x_609_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__45));
v___y_518_ = v___x_609_;
goto v___jp_517_;
}
case 20:
{
lean_object* v___x_610_; 
v___x_610_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__46));
v___y_518_ = v___x_610_;
goto v___jp_517_;
}
case 21:
{
lean_object* v___x_611_; 
v___x_611_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__47));
v___y_518_ = v___x_611_;
goto v___jp_517_;
}
case 22:
{
lean_object* v___x_612_; 
v___x_612_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__48));
v___y_518_ = v___x_612_;
goto v___jp_517_;
}
case 23:
{
lean_object* v___x_613_; 
v___x_613_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__49));
v___y_518_ = v___x_613_;
goto v___jp_517_;
}
case 24:
{
lean_object* v___x_614_; 
v___x_614_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__50));
v___y_518_ = v___x_614_;
goto v___jp_517_;
}
case 25:
{
lean_object* v___x_615_; 
v___x_615_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__51));
v___y_518_ = v___x_615_;
goto v___jp_517_;
}
case 26:
{
lean_object* v___x_616_; 
v___x_616_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__52));
v___y_518_ = v___x_616_;
goto v___jp_517_;
}
case 27:
{
lean_object* v___x_617_; 
v___x_617_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__53));
v___y_518_ = v___x_617_;
goto v___jp_517_;
}
case 28:
{
lean_object* v___x_618_; 
v___x_618_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__54));
v___y_518_ = v___x_618_;
goto v___jp_517_;
}
case 29:
{
lean_object* v___x_619_; 
v___x_619_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__55));
v___y_518_ = v___x_619_;
goto v___jp_517_;
}
case 30:
{
lean_object* v___x_620_; 
v___x_620_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__56));
v___y_518_ = v___x_620_;
goto v___jp_517_;
}
case 31:
{
lean_object* v___x_621_; 
v___x_621_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__57));
v___y_518_ = v___x_621_;
goto v___jp_517_;
}
case 32:
{
lean_object* v___x_622_; 
v___x_622_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__58));
v___y_518_ = v___x_622_;
goto v___jp_517_;
}
case 33:
{
lean_object* v___x_623_; 
v___x_623_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__59));
v___y_518_ = v___x_623_;
goto v___jp_517_;
}
case 34:
{
lean_object* v___x_624_; 
v___x_624_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__60));
v___y_518_ = v___x_624_;
goto v___jp_517_;
}
case 35:
{
lean_object* v___x_625_; 
v___x_625_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__61));
v___y_518_ = v___x_625_;
goto v___jp_517_;
}
case 36:
{
lean_object* v___x_626_; 
v___x_626_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__62));
v___y_518_ = v___x_626_;
goto v___jp_517_;
}
case 37:
{
lean_object* v___x_627_; 
v___x_627_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__63));
v___y_518_ = v___x_627_;
goto v___jp_517_;
}
case 38:
{
lean_object* v___x_628_; 
v___x_628_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__64));
v___y_518_ = v___x_628_;
goto v___jp_517_;
}
default: 
{
lean_object* v___x_629_; 
v___x_629_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__65));
v___y_518_ = v___x_629_;
goto v___jp_517_;
}
}
v___jp_322_:
{
lean_object* v_entries_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; size_t v_sz_330_; size_t v___x_331_; lean_object* v_pairs_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_entries_325_ = lean_ctor_get(v_headers_321_, 0);
lean_inc_ref(v_entries_325_);
lean_dec_ref(v_headers_321_);
v___x_326_ = lean_string_append(v___y_323_, v___y_324_);
v___x_327_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__0));
v___x_328_ = lean_string_append(v___x_326_, v___x_327_);
v___x_329_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__10));
v_sz_330_ = lean_array_size(v_entries_325_);
v___x_331_ = ((size_t)0ULL);
v_pairs_332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_329_, v___f_312_, v_sz_330_, v___x_331_, v_entries_325_);
v___x_333_ = lean_array_to_list(v_pairs_332_);
v___x_334_ = l_String_intercalate(v___x_327_, v___x_333_);
v___x_335_ = lean_string_append(v___x_328_, v___x_334_);
lean_dec_ref(v___x_334_);
v___x_336_ = lean_string_append(v___x_335_, v___x_327_);
return v___x_336_;
}
v___jp_337_:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_string_append(v___y_338_, v___y_340_);
lean_dec_ref(v___y_340_);
v___x_342_ = lean_string_append(v___x_341_, v___y_339_);
switch(v_version_319_)
{
case 0:
{
lean_object* v___x_343_; 
v___x_343_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__11));
v___y_323_ = v___x_342_;
v___y_324_ = v___x_343_;
goto v___jp_322_;
}
case 1:
{
lean_object* v___x_344_; 
v___x_344_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__12));
v___y_323_ = v___x_342_;
v___y_324_ = v___x_344_;
goto v___jp_322_;
}
case 2:
{
lean_object* v___x_345_; 
v___x_345_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__13));
v___y_323_ = v___x_342_;
v___y_324_ = v___x_345_;
goto v___jp_322_;
}
default: 
{
lean_object* v___x_346_; 
v___x_346_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__14));
v___y_323_ = v___x_342_;
v___y_324_ = v___x_346_;
goto v___jp_322_;
}
}
}
v___jp_347_:
{
if (lean_obj_tag(v___y_348_) == 0)
{
lean_dec_ref(v___f_313_);
v___y_338_ = v___y_349_;
v___y_339_ = v___y_350_;
v___y_340_ = v___y_351_;
goto v___jp_337_;
}
else
{
lean_object* v_val_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_val_352_ = lean_ctor_get(v___y_348_, 0);
lean_inc(v_val_352_);
lean_dec_ref(v___y_348_);
v___x_353_ = lean_array_get_size(v_val_352_);
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_nat_dec_eq(v___x_353_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_encodedParams_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_356_ = lean_array_to_list(v_val_352_);
v___x_357_ = lean_box(0);
v_encodedParams_358_ = l_List_mapTR_loop___redArg(v___f_313_, v___x_356_, v___x_357_);
v___x_359_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__15));
v___x_360_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__16));
v___x_361_ = l_String_intercalate(v___x_360_, v_encodedParams_358_);
v___x_362_ = lean_string_append(v___x_359_, v___x_361_);
lean_dec_ref(v___x_361_);
v___x_363_ = lean_string_append(v___y_351_, v___x_362_);
lean_dec_ref(v___x_362_);
v___y_338_ = v___y_349_;
v___y_339_ = v___y_350_;
v___y_340_ = v___x_363_;
goto v___jp_337_;
}
else
{
lean_dec(v_val_352_);
lean_dec_ref(v___f_313_);
v___y_338_ = v___y_349_;
v___y_339_ = v___y_350_;
v___y_340_ = v___y_351_;
goto v___jp_337_;
}
}
}
v___jp_364_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_372_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_373_ = lean_string_append(v___y_370_, v___x_372_);
v___x_374_ = lean_string_append(v___x_373_, v___y_368_);
lean_dec_ref(v___y_368_);
v___x_375_ = lean_string_append(v___x_374_, v___y_369_);
lean_dec_ref(v___y_369_);
v___x_376_ = lean_string_append(v___x_375_, v___y_365_);
lean_dec_ref(v___y_365_);
v___x_377_ = lean_string_append(v___x_376_, v___y_371_);
lean_dec_ref(v___y_371_);
v___y_338_ = v___y_366_;
v___y_339_ = v___y_367_;
v___y_340_ = v___x_377_;
goto v___jp_337_;
}
v___jp_378_:
{
if (lean_obj_tag(v___y_379_) == 0)
{
lean_object* v___x_386_; 
v___x_386_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__4));
v___y_365_ = v___y_385_;
v___y_366_ = v___y_380_;
v___y_367_ = v___y_381_;
v___y_368_ = v___y_382_;
v___y_369_ = v___y_383_;
v___y_370_ = v___y_384_;
v___y_371_ = v___x_386_;
goto v___jp_364_;
}
else
{
lean_object* v_val_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_val_387_ = lean_ctor_get(v___y_379_, 0);
lean_inc(v_val_387_);
lean_dec_ref(v___y_379_);
v___x_388_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__18));
v___x_389_ = l_Std_Http_URI_EncodedFragment_encode(v_val_387_);
lean_dec(v_val_387_);
v___x_390_ = lean_string_from_utf8_unchecked(v___x_389_);
v___x_391_ = lean_string_append(v___x_388_, v___x_390_);
lean_dec_ref(v___x_390_);
v___y_365_ = v___y_385_;
v___y_366_ = v___y_380_;
v___y_367_ = v___y_381_;
v___y_368_ = v___y_382_;
v___y_369_ = v___y_383_;
v___y_370_ = v___y_384_;
v___y_371_ = v___x_391_;
goto v___jp_364_;
}
}
v___jp_392_:
{
lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_400_ = lean_array_get_size(v___y_397_);
v___x_401_ = lean_unsigned_to_nat(0u);
v___x_402_ = lean_nat_dec_eq(v___x_400_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v_encodedParams_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_403_ = lean_array_to_list(v___y_397_);
v___x_404_ = lean_box(0);
v_encodedParams_405_ = l_List_mapTR_loop___redArg(v___f_314_, v___x_403_, v___x_404_);
v___x_406_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__15));
v___x_407_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__16));
v___x_408_ = l_String_intercalate(v___x_407_, v_encodedParams_405_);
v___x_409_ = lean_string_append(v___x_406_, v___x_408_);
lean_dec_ref(v___x_408_);
v___y_379_ = v___y_394_;
v___y_380_ = v___y_393_;
v___y_381_ = v___y_395_;
v___y_382_ = v___y_396_;
v___y_383_ = v___y_399_;
v___y_384_ = v___y_398_;
v___y_385_ = v___x_409_;
goto v___jp_378_;
}
else
{
lean_object* v___x_410_; 
lean_dec_ref(v___y_397_);
lean_dec_ref(v___f_314_);
v___x_410_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__4));
v___y_379_ = v___y_394_;
v___y_380_ = v___y_393_;
v___y_381_ = v___y_395_;
v___y_382_ = v___y_396_;
v___y_383_ = v___y_399_;
v___y_384_ = v___y_398_;
v___y_385_ = v___x_410_;
goto v___jp_378_;
}
}
v___jp_411_:
{
lean_object* v_segments_419_; uint8_t v_absolute_420_; lean_object* v___x_421_; lean_object* v___x_422_; size_t v_sz_423_; size_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_result_427_; 
v_segments_419_ = lean_ctor_get(v___y_415_, 0);
lean_inc_ref(v_segments_419_);
v_absolute_420_ = lean_ctor_get_uint8(v___y_415_, sizeof(void*)*1);
lean_dec_ref(v___y_415_);
v___x_421_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__19));
v___x_422_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__10));
v_sz_423_ = lean_array_size(v_segments_419_);
v___x_424_ = ((size_t)0ULL);
v___x_425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_422_, v___f_315_, v_sz_423_, v___x_424_, v_segments_419_);
v___x_426_ = lean_array_to_list(v___x_425_);
v_result_427_ = l_String_intercalate(v___x_421_, v___x_426_);
if (v_absolute_420_ == 0)
{
v___y_393_ = v___y_413_;
v___y_394_ = v___y_412_;
v___y_395_ = v___y_414_;
v___y_396_ = v___y_418_;
v___y_397_ = v___y_416_;
v___y_398_ = v___y_417_;
v___y_399_ = v_result_427_;
goto v___jp_392_;
}
else
{
lean_object* v___x_428_; 
v___x_428_ = lean_string_append(v___x_421_, v_result_427_);
lean_dec_ref(v_result_427_);
v___y_393_ = v___y_413_;
v___y_394_ = v___y_412_;
v___y_395_ = v___y_414_;
v___y_396_ = v___y_418_;
v___y_397_ = v___y_416_;
v___y_398_ = v___y_417_;
v___y_399_ = v___x_428_;
goto v___jp_392_;
}
}
v___jp_429_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_string_append(v___y_437_, v___y_434_);
lean_dec_ref(v___y_434_);
v___x_441_ = lean_string_append(v___x_440_, v___y_439_);
lean_dec_ref(v___y_439_);
lean_inc_ref(v___y_432_);
v___x_442_ = lean_string_append(v___y_432_, v___x_441_);
lean_dec_ref(v___x_441_);
v___y_412_ = v___y_431_;
v___y_413_ = v___y_430_;
v___y_414_ = v___y_433_;
v___y_415_ = v___y_435_;
v___y_416_ = v___y_436_;
v___y_417_ = v___y_438_;
v___y_418_ = v___x_442_;
goto v___jp_411_;
}
v___jp_443_:
{
switch(lean_obj_tag(v_port_444_))
{
case 0:
{
lean_object* v___x_454_; 
v___x_454_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__4));
v___y_430_ = v___y_447_;
v___y_431_ = v___y_446_;
v___y_432_ = v___y_445_;
v___y_433_ = v___y_448_;
v___y_434_ = v___y_453_;
v___y_435_ = v___y_449_;
v___y_436_ = v___y_451_;
v___y_437_ = v___y_450_;
v___y_438_ = v___y_452_;
v___y_439_ = v___x_454_;
goto v___jp_429_;
}
case 1:
{
lean_object* v___x_455_; 
v___x_455_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___y_430_ = v___y_447_;
v___y_431_ = v___y_446_;
v___y_432_ = v___y_445_;
v___y_433_ = v___y_448_;
v___y_434_ = v___y_453_;
v___y_435_ = v___y_449_;
v___y_436_ = v___y_451_;
v___y_437_ = v___y_450_;
v___y_438_ = v___y_452_;
v___y_439_ = v___x_455_;
goto v___jp_429_;
}
default: 
{
uint16_t v_port_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v_port_456_ = lean_ctor_get_uint16(v_port_444_, 0);
lean_dec_ref(v_port_444_);
v___x_457_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_458_ = lean_uint16_to_nat(v_port_456_);
v___x_459_ = l_Nat_reprFast(v___x_458_);
v___x_460_ = lean_string_append(v___x_457_, v___x_459_);
lean_dec_ref(v___x_459_);
v___y_430_ = v___y_447_;
v___y_431_ = v___y_446_;
v___y_432_ = v___y_445_;
v___y_433_ = v___y_448_;
v___y_434_ = v___y_453_;
v___y_435_ = v___y_449_;
v___y_436_ = v___y_451_;
v___y_437_ = v___y_450_;
v___y_438_ = v___y_452_;
v___y_439_ = v___x_460_;
goto v___jp_429_;
}
}
}
v___jp_461_:
{
switch(lean_obj_tag(v_host_462_))
{
case 0:
{
lean_object* v_name_472_; 
v_name_472_ = lean_ctor_get(v_host_462_, 0);
lean_inc_ref(v_name_472_);
lean_dec_ref(v_host_462_);
v_port_444_ = v_port_463_;
v___y_445_ = v___y_466_;
v___y_446_ = v___y_465_;
v___y_447_ = v___y_464_;
v___y_448_ = v___y_467_;
v___y_449_ = v___y_468_;
v___y_450_ = v___y_471_;
v___y_451_ = v___y_469_;
v___y_452_ = v___y_470_;
v___y_453_ = v_name_472_;
goto v___jp_443_;
}
case 1:
{
lean_object* v_ipv4_473_; lean_object* v___x_474_; 
v_ipv4_473_ = lean_ctor_get(v_host_462_, 0);
lean_inc_ref(v_ipv4_473_);
lean_dec_ref(v_host_462_);
v___x_474_ = lean_uv_ntop_v4(v_ipv4_473_);
lean_dec_ref(v_ipv4_473_);
v_port_444_ = v_port_463_;
v___y_445_ = v___y_466_;
v___y_446_ = v___y_465_;
v___y_447_ = v___y_464_;
v___y_448_ = v___y_467_;
v___y_449_ = v___y_468_;
v___y_450_ = v___y_471_;
v___y_451_ = v___y_469_;
v___y_452_ = v___y_470_;
v___y_453_ = v___x_474_;
goto v___jp_443_;
}
default: 
{
lean_object* v_ipv6_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_ipv6_475_ = lean_ctor_get(v_host_462_, 0);
lean_inc_ref(v_ipv6_475_);
lean_dec_ref(v_host_462_);
v___x_476_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__20));
v___x_477_ = lean_uv_ntop_v6(v_ipv6_475_);
lean_dec_ref(v_ipv6_475_);
v___x_478_ = lean_string_append(v___x_476_, v___x_477_);
lean_dec_ref(v___x_477_);
v___x_479_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__21));
v___x_480_ = lean_string_append(v___x_478_, v___x_479_);
v_port_444_ = v_port_463_;
v___y_445_ = v___y_466_;
v___y_446_ = v___y_465_;
v___y_447_ = v___y_464_;
v___y_448_ = v___y_467_;
v___y_449_ = v___y_468_;
v___y_450_ = v___y_471_;
v___y_451_ = v___y_469_;
v___y_452_ = v___y_470_;
v___y_453_ = v___x_480_;
goto v___jp_443_;
}
}
}
v___jp_481_:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_string_append(v___y_482_, v___y_483_);
lean_dec_ref(v___y_483_);
v___x_488_ = lean_string_append(v___x_487_, v___y_486_);
lean_dec_ref(v___y_486_);
v___y_338_ = v___y_484_;
v___y_339_ = v___y_485_;
v___y_340_ = v___x_488_;
goto v___jp_337_;
}
v___jp_489_:
{
switch(lean_obj_tag(v_port_493_))
{
case 0:
{
lean_object* v___x_495_; 
v___x_495_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__4));
v___y_482_ = v___y_490_;
v___y_483_ = v___y_494_;
v___y_484_ = v___y_491_;
v___y_485_ = v___y_492_;
v___y_486_ = v___x_495_;
goto v___jp_481_;
}
case 1:
{
lean_object* v___x_496_; 
v___x_496_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___y_482_ = v___y_490_;
v___y_483_ = v___y_494_;
v___y_484_ = v___y_491_;
v___y_485_ = v___y_492_;
v___y_486_ = v___x_496_;
goto v___jp_481_;
}
default: 
{
uint16_t v_port_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_port_497_ = lean_ctor_get_uint16(v_port_493_, 0);
lean_dec_ref(v_port_493_);
v___x_498_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_499_ = lean_uint16_to_nat(v_port_497_);
v___x_500_ = l_Nat_reprFast(v___x_499_);
v___x_501_ = lean_string_append(v___x_498_, v___x_500_);
lean_dec_ref(v___x_500_);
v___y_482_ = v___y_490_;
v___y_483_ = v___y_494_;
v___y_484_ = v___y_491_;
v___y_485_ = v___y_492_;
v___y_486_ = v___x_501_;
goto v___jp_481_;
}
}
}
v___jp_502_:
{
switch(lean_obj_tag(v_host_505_))
{
case 0:
{
lean_object* v_name_508_; 
v_name_508_ = lean_ctor_get(v_host_505_, 0);
lean_inc_ref(v_name_508_);
lean_dec_ref(v_host_505_);
v___y_490_ = v___y_507_;
v___y_491_ = v___y_503_;
v___y_492_ = v___y_504_;
v_port_493_ = v_port_506_;
v___y_494_ = v_name_508_;
goto v___jp_489_;
}
case 1:
{
lean_object* v_ipv4_509_; lean_object* v___x_510_; 
v_ipv4_509_ = lean_ctor_get(v_host_505_, 0);
lean_inc_ref(v_ipv4_509_);
lean_dec_ref(v_host_505_);
v___x_510_ = lean_uv_ntop_v4(v_ipv4_509_);
lean_dec_ref(v_ipv4_509_);
v___y_490_ = v___y_507_;
v___y_491_ = v___y_503_;
v___y_492_ = v___y_504_;
v_port_493_ = v_port_506_;
v___y_494_ = v___x_510_;
goto v___jp_489_;
}
default: 
{
lean_object* v_ipv6_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_ipv6_511_ = lean_ctor_get(v_host_505_, 0);
lean_inc_ref(v_ipv6_511_);
lean_dec_ref(v_host_505_);
v___x_512_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__20));
v___x_513_ = lean_uv_ntop_v6(v_ipv6_511_);
lean_dec_ref(v_ipv6_511_);
v___x_514_ = lean_string_append(v___x_512_, v___x_513_);
lean_dec_ref(v___x_513_);
v___x_515_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__21));
v___x_516_ = lean_string_append(v___x_514_, v___x_515_);
v___y_490_ = v___y_507_;
v___y_491_ = v___y_503_;
v___y_492_ = v___y_504_;
v_port_493_ = v_port_506_;
v___y_494_ = v___x_516_;
goto v___jp_489_;
}
}
}
v___jp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__22));
lean_inc_ref(v___y_518_);
v___x_520_ = lean_string_append(v___y_518_, v___x_519_);
switch(lean_obj_tag(v_uri_320_))
{
case 0:
{
lean_object* v_path_521_; lean_object* v_query_522_; lean_object* v_segments_523_; uint8_t v_absolute_524_; lean_object* v___x_525_; lean_object* v___x_526_; size_t v_sz_527_; size_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v_result_531_; 
lean_dec_ref(v___f_315_);
lean_dec_ref(v___f_314_);
v_path_521_ = lean_ctor_get(v_uri_320_, 0);
lean_inc_ref(v_path_521_);
v_query_522_ = lean_ctor_get(v_uri_320_, 1);
lean_inc(v_query_522_);
lean_dec_ref(v_uri_320_);
v_segments_523_ = lean_ctor_get(v_path_521_, 0);
lean_inc_ref(v_segments_523_);
v_absolute_524_ = lean_ctor_get_uint8(v_path_521_, sizeof(void*)*1);
lean_dec_ref(v_path_521_);
v___x_525_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__19));
v___x_526_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__10));
v_sz_527_ = lean_array_size(v_segments_523_);
v___x_528_ = ((size_t)0ULL);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_526_, v___f_316_, v_sz_527_, v___x_528_, v_segments_523_);
v___x_530_ = lean_array_to_list(v___x_529_);
v_result_531_ = l_String_intercalate(v___x_525_, v___x_530_);
if (v_absolute_524_ == 0)
{
v___y_348_ = v_query_522_;
v___y_349_ = v___x_520_;
v___y_350_ = v___x_519_;
v___y_351_ = v_result_531_;
goto v___jp_347_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = lean_string_append(v___x_525_, v_result_531_);
lean_dec_ref(v_result_531_);
v___y_348_ = v_query_522_;
v___y_349_ = v___x_520_;
v___y_350_ = v___x_519_;
v___y_351_ = v___x_532_;
goto v___jp_347_;
}
}
case 1:
{
lean_object* v_uri_533_; lean_object* v_authority_534_; 
lean_dec_ref(v___f_316_);
lean_dec_ref(v___f_313_);
v_uri_533_ = lean_ctor_get(v_uri_320_, 0);
lean_inc_ref(v_uri_533_);
lean_dec_ref(v_uri_320_);
v_authority_534_ = lean_ctor_get(v_uri_533_, 1);
if (lean_obj_tag(v_authority_534_) == 0)
{
lean_object* v_scheme_535_; lean_object* v_path_536_; lean_object* v_query_537_; lean_object* v_fragment_538_; lean_object* v___x_539_; 
v_scheme_535_ = lean_ctor_get(v_uri_533_, 0);
lean_inc_ref(v_scheme_535_);
v_path_536_ = lean_ctor_get(v_uri_533_, 2);
lean_inc_ref(v_path_536_);
v_query_537_ = lean_ctor_get(v_uri_533_, 3);
lean_inc_ref(v_query_537_);
v_fragment_538_ = lean_ctor_get(v_uri_533_, 4);
lean_inc(v_fragment_538_);
lean_dec_ref(v_uri_533_);
v___x_539_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__4));
v___y_412_ = v_fragment_538_;
v___y_413_ = v___x_520_;
v___y_414_ = v___x_519_;
v___y_415_ = v_path_536_;
v___y_416_ = v_query_537_;
v___y_417_ = v_scheme_535_;
v___y_418_ = v___x_539_;
goto v___jp_411_;
}
else
{
lean_object* v_val_540_; lean_object* v_scheme_541_; lean_object* v_path_542_; lean_object* v_query_543_; lean_object* v_fragment_544_; lean_object* v_userInfo_545_; lean_object* v_host_546_; lean_object* v_port_547_; lean_object* v___x_548_; 
v_val_540_ = lean_ctor_get(v_authority_534_, 0);
lean_inc(v_val_540_);
v_scheme_541_ = lean_ctor_get(v_uri_533_, 0);
lean_inc_ref(v_scheme_541_);
v_path_542_ = lean_ctor_get(v_uri_533_, 2);
lean_inc_ref(v_path_542_);
v_query_543_ = lean_ctor_get(v_uri_533_, 3);
lean_inc_ref(v_query_543_);
v_fragment_544_ = lean_ctor_get(v_uri_533_, 4);
lean_inc(v_fragment_544_);
lean_dec_ref(v_uri_533_);
v_userInfo_545_ = lean_ctor_get(v_val_540_, 0);
lean_inc(v_userInfo_545_);
v_host_546_ = lean_ctor_get(v_val_540_, 1);
lean_inc_ref(v_host_546_);
v_port_547_ = lean_ctor_get(v_val_540_, 2);
lean_inc(v_port_547_);
lean_dec(v_val_540_);
v___x_548_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__23));
if (lean_obj_tag(v_userInfo_545_) == 0)
{
lean_object* v___x_549_; 
v___x_549_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__4));
v_host_462_ = v_host_546_;
v_port_463_ = v_port_547_;
v___y_464_ = v___x_520_;
v___y_465_ = v_fragment_544_;
v___y_466_ = v___x_548_;
v___y_467_ = v___x_519_;
v___y_468_ = v_path_542_;
v___y_469_ = v_query_543_;
v___y_470_ = v_scheme_541_;
v___y_471_ = v___x_549_;
goto v___jp_461_;
}
else
{
lean_object* v_val_550_; lean_object* v_password_551_; 
v_val_550_ = lean_ctor_get(v_userInfo_545_, 0);
lean_inc(v_val_550_);
lean_dec_ref(v_userInfo_545_);
v_password_551_ = lean_ctor_get(v_val_550_, 1);
if (lean_obj_tag(v_password_551_) == 0)
{
lean_object* v_username_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_username_552_ = lean_ctor_get(v_val_550_, 0);
lean_inc_ref(v_username_552_);
lean_dec(v_val_550_);
v___x_553_ = lean_string_from_utf8_unchecked(v_username_552_);
v___x_554_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__24));
v___x_555_ = lean_string_append(v___x_553_, v___x_554_);
v_host_462_ = v_host_546_;
v_port_463_ = v_port_547_;
v___y_464_ = v___x_520_;
v___y_465_ = v_fragment_544_;
v___y_466_ = v___x_548_;
v___y_467_ = v___x_519_;
v___y_468_ = v_path_542_;
v___y_469_ = v_query_543_;
v___y_470_ = v_scheme_541_;
v___y_471_ = v___x_555_;
goto v___jp_461_;
}
else
{
lean_object* v_username_556_; lean_object* v_val_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
lean_inc_ref(v_password_551_);
v_username_556_ = lean_ctor_get(v_val_550_, 0);
lean_inc_ref(v_username_556_);
lean_dec(v_val_550_);
v_val_557_ = lean_ctor_get(v_password_551_, 0);
lean_inc(v_val_557_);
lean_dec_ref(v_password_551_);
v___x_558_ = lean_string_from_utf8_unchecked(v_username_556_);
v___x_559_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_560_ = lean_string_append(v___x_558_, v___x_559_);
v___x_561_ = lean_string_from_utf8_unchecked(v_val_557_);
v___x_562_ = lean_string_append(v___x_560_, v___x_561_);
lean_dec_ref(v___x_561_);
v___x_563_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__24));
v___x_564_ = lean_string_append(v___x_562_, v___x_563_);
v_host_462_ = v_host_546_;
v_port_463_ = v_port_547_;
v___y_464_ = v___x_520_;
v___y_465_ = v_fragment_544_;
v___y_466_ = v___x_548_;
v___y_467_ = v___x_519_;
v___y_468_ = v_path_542_;
v___y_469_ = v_query_543_;
v___y_470_ = v_scheme_541_;
v___y_471_ = v___x_564_;
goto v___jp_461_;
}
}
}
}
case 2:
{
lean_object* v_authority_565_; lean_object* v_userInfo_566_; 
lean_dec_ref(v___f_316_);
lean_dec_ref(v___f_315_);
lean_dec_ref(v___f_314_);
lean_dec_ref(v___f_313_);
v_authority_565_ = lean_ctor_get(v_uri_320_, 0);
lean_inc_ref(v_authority_565_);
lean_dec_ref(v_uri_320_);
v_userInfo_566_ = lean_ctor_get(v_authority_565_, 0);
if (lean_obj_tag(v_userInfo_566_) == 0)
{
lean_object* v_host_567_; lean_object* v_port_568_; lean_object* v___x_569_; 
v_host_567_ = lean_ctor_get(v_authority_565_, 1);
lean_inc_ref(v_host_567_);
v_port_568_ = lean_ctor_get(v_authority_565_, 2);
lean_inc(v_port_568_);
lean_dec_ref(v_authority_565_);
v___x_569_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__4));
v___y_503_ = v___x_520_;
v___y_504_ = v___x_519_;
v_host_505_ = v_host_567_;
v_port_506_ = v_port_568_;
v___y_507_ = v___x_569_;
goto v___jp_502_;
}
else
{
lean_object* v_val_570_; lean_object* v_password_571_; 
v_val_570_ = lean_ctor_get(v_userInfo_566_, 0);
lean_inc(v_val_570_);
v_password_571_ = lean_ctor_get(v_val_570_, 1);
if (lean_obj_tag(v_password_571_) == 0)
{
lean_object* v_host_572_; lean_object* v_port_573_; lean_object* v_username_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_host_572_ = lean_ctor_get(v_authority_565_, 1);
lean_inc_ref(v_host_572_);
v_port_573_ = lean_ctor_get(v_authority_565_, 2);
lean_inc(v_port_573_);
lean_dec_ref(v_authority_565_);
v_username_574_ = lean_ctor_get(v_val_570_, 0);
lean_inc_ref(v_username_574_);
lean_dec(v_val_570_);
v___x_575_ = lean_string_from_utf8_unchecked(v_username_574_);
v___x_576_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__24));
v___x_577_ = lean_string_append(v___x_575_, v___x_576_);
v___y_503_ = v___x_520_;
v___y_504_ = v___x_519_;
v_host_505_ = v_host_572_;
v_port_506_ = v_port_573_;
v___y_507_ = v___x_577_;
goto v___jp_502_;
}
else
{
lean_object* v_host_578_; lean_object* v_port_579_; lean_object* v_username_580_; lean_object* v_val_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
lean_inc_ref(v_password_571_);
v_host_578_ = lean_ctor_get(v_authority_565_, 1);
lean_inc_ref(v_host_578_);
v_port_579_ = lean_ctor_get(v_authority_565_, 2);
lean_inc(v_port_579_);
lean_dec_ref(v_authority_565_);
v_username_580_ = lean_ctor_get(v_val_570_, 0);
lean_inc_ref(v_username_580_);
lean_dec(v_val_570_);
v_val_581_ = lean_ctor_get(v_password_571_, 0);
lean_inc(v_val_581_);
lean_dec_ref(v_password_571_);
v___x_582_ = lean_string_from_utf8_unchecked(v_username_580_);
v___x_583_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_584_ = lean_string_append(v___x_582_, v___x_583_);
v___x_585_ = lean_string_from_utf8_unchecked(v_val_581_);
v___x_586_ = lean_string_append(v___x_584_, v___x_585_);
lean_dec_ref(v___x_585_);
v___x_587_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__24));
v___x_588_ = lean_string_append(v___x_586_, v___x_587_);
v___y_503_ = v___x_520_;
v___y_504_ = v___x_519_;
v_host_505_ = v_host_578_;
v_port_506_ = v_port_579_;
v___y_507_ = v___x_588_;
goto v___jp_502_;
}
}
}
default: 
{
lean_object* v___x_589_; 
lean_dec_ref(v___f_316_);
lean_dec_ref(v___f_315_);
lean_dec_ref(v___f_314_);
lean_dec_ref(v___f_313_);
v___x_589_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__25));
v___y_338_ = v___x_520_;
v___y_339_ = v___x_519_;
v___y_340_ = v___x_589_;
goto v___jp_337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2(lean_object* v___x_638_, lean_object* v___x_639_, lean_object* v___x_640_, lean_object* v_name_641_, lean_object* v___x_642_, uint32_t v___x_643_, lean_object* v___x_644_, lean_object* v_it_645_, lean_object* v_acc_646_, lean_object* v_hP_647_, lean_object* v_recur_648_){
_start:
{
lean_object* v_it_650_; lean_object* v_out_651_; lean_object* v_it_667_; lean_object* v_startInclusive_668_; lean_object* v_endExclusive_669_; 
if (lean_obj_tag(v_it_645_) == 0)
{
lean_object* v_currPos_681_; lean_object* v_searcher_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_704_; 
v_currPos_681_ = lean_ctor_get(v_it_645_, 0);
v_searcher_682_ = lean_ctor_get(v_it_645_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_it_645_);
if (v_isSharedCheck_704_ == 0)
{
v___x_684_ = v_it_645_;
v_isShared_685_ = v_isSharedCheck_704_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_searcher_682_);
lean_inc(v_currPos_681_);
lean_dec(v_it_645_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_704_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
uint8_t v___x_686_; 
v___x_686_ = lean_nat_dec_eq(v_searcher_682_, v___x_642_);
if (v___x_686_ == 0)
{
uint32_t v___x_687_; uint8_t v___x_688_; 
lean_dec(v___x_642_);
v___x_687_ = lean_string_utf8_get_fast(v_name_641_, v_searcher_682_);
v___x_688_ = lean_uint32_dec_eq(v___x_687_, v___x_643_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_string_utf8_next_fast(v_name_641_, v_searcher_682_);
lean_dec(v_searcher_682_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_689_);
v___x_691_ = v___x_684_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_currPos_681_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___x_689_);
v___x_691_ = v_reuseFailAlloc_693_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; 
v___x_692_ = lean_apply_4(v_recur_648_, v___x_691_, v_acc_646_, lean_box(0), lean_box(0));
return v___x_692_;
}
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v_slice_697_; lean_object* v_nextIt_699_; 
v___x_694_ = lean_string_utf8_next_fast(v_name_641_, v_searcher_682_);
v___x_695_ = lean_nat_sub(v___x_694_, v_searcher_682_);
v___x_696_ = lean_nat_add(v_searcher_682_, v___x_695_);
lean_dec(v___x_695_);
v_slice_697_ = l_String_Slice_subslice_x21(v___x_644_, v_currPos_681_, v_searcher_682_);
lean_inc(v___x_696_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_696_);
lean_ctor_set(v___x_684_, 0, v___x_696_);
v_nextIt_699_ = v___x_684_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_696_);
v_nextIt_699_ = v_reuseFailAlloc_702_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v_startInclusive_700_; lean_object* v_endExclusive_701_; 
v_startInclusive_700_ = lean_ctor_get(v_slice_697_, 0);
lean_inc(v_startInclusive_700_);
v_endExclusive_701_ = lean_ctor_get(v_slice_697_, 1);
lean_inc(v_endExclusive_701_);
lean_dec_ref(v_slice_697_);
v_it_667_ = v_nextIt_699_;
v_startInclusive_668_ = v_startInclusive_700_;
v_endExclusive_669_ = v_endExclusive_701_;
goto v___jp_666_;
}
}
}
else
{
lean_object* v___x_703_; 
lean_del_object(v___x_684_);
lean_dec(v_searcher_682_);
v___x_703_ = lean_box(1);
v_it_667_ = v___x_703_;
v_startInclusive_668_ = v_currPos_681_;
v_endExclusive_669_ = v___x_642_;
goto v___jp_666_;
}
}
}
else
{
lean_dec_ref(v_recur_648_);
lean_dec(v___x_642_);
return v_acc_646_;
}
v___jp_649_:
{
if (lean_obj_tag(v_acc_646_) == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_652_, 0, v_out_651_);
v___x_653_ = lean_apply_4(v_recur_648_, v_it_650_, v___x_652_, lean_box(0), lean_box(0));
return v___x_653_;
}
else
{
lean_object* v_val_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_665_; 
v_val_654_ = lean_ctor_get(v_acc_646_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_acc_646_);
if (v_isSharedCheck_665_ == 0)
{
v___x_656_ = v_acc_646_;
v_isShared_657_ = v_isSharedCheck_665_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_val_654_);
lean_dec(v_acc_646_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_665_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_658_ = lean_string_utf8_extract(v___x_638_, v___x_639_, v___x_640_);
v___x_659_ = lean_string_append(v_val_654_, v___x_658_);
lean_dec_ref(v___x_658_);
v___x_660_ = lean_string_append(v___x_659_, v_out_651_);
lean_dec_ref(v_out_651_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_660_);
v___x_662_ = v___x_656_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_664_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_663_; 
v___x_663_ = lean_apply_4(v_recur_648_, v_it_650_, v___x_662_, lean_box(0), lean_box(0));
return v___x_663_;
}
}
}
}
v___jp_666_:
{
lean_object* v___x_670_; uint32_t v___x_671_; uint32_t v___x_672_; uint8_t v___x_673_; 
v___x_670_ = lean_string_utf8_extract(v_name_641_, v_startInclusive_668_, v_endExclusive_669_);
lean_dec(v_endExclusive_669_);
lean_dec(v_startInclusive_668_);
v___x_671_ = lean_string_utf8_get(v___x_670_, v___x_639_);
v___x_672_ = 97;
v___x_673_ = lean_uint32_dec_le(v___x_672_, v___x_671_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
v___x_674_ = lean_string_utf8_set(v___x_670_, v___x_639_, v___x_671_);
v_it_650_ = v_it_667_;
v_out_651_ = v___x_674_;
goto v___jp_649_;
}
else
{
uint32_t v___x_675_; uint8_t v___x_676_; 
v___x_675_ = 122;
v___x_676_ = lean_uint32_dec_le(v___x_671_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
v___x_677_ = lean_string_utf8_set(v___x_670_, v___x_639_, v___x_671_);
v_it_650_ = v_it_667_;
v_out_651_ = v___x_677_;
goto v___jp_649_;
}
else
{
uint32_t v___x_678_; uint32_t v___x_679_; lean_object* v___x_680_; 
v___x_678_ = 4294967264;
v___x_679_ = lean_uint32_add(v___x_671_, v___x_678_);
v___x_680_ = lean_string_utf8_set(v___x_670_, v___x_639_, v___x_679_);
v_it_650_ = v_it_667_;
v_out_651_ = v___x_680_;
goto v___jp_649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___boxed(lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v_name_708_, lean_object* v___x_709_, lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v_it_712_, lean_object* v_acc_713_, lean_object* v_hP_714_, lean_object* v_recur_715_){
_start:
{
uint32_t v___x_3141__boxed_716_; lean_object* v_res_717_; 
v___x_3141__boxed_716_ = lean_unbox_uint32(v___x_710_);
lean_dec(v___x_710_);
v_res_717_ = l_Std_Http_Request_instEncodeV11Head___lam__2(v___x_705_, v___x_706_, v___x_707_, v_name_708_, v___x_709_, v___x_3141__boxed_716_, v___x_711_, v_it_712_, v_acc_713_, v_hP_714_, v_recur_715_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v_name_708_);
lean_dec(v___x_707_);
lean_dec(v___x_706_);
lean_dec_ref(v___x_705_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0(lean_object* v_buf_718_, lean_object* v_name_719_, lean_object* v_value_720_){
_start:
{
lean_object* v___y_722_; lean_object* v___f_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_it_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___f_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___f_741_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__1));
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_string_utf8_byte_size(v_name_719_);
lean_inc_ref(v_name_719_);
v___x_744_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_744_, 0, v_name_719_);
lean_ctor_set(v___x_744_, 1, v___x_742_);
lean_ctor_set(v___x_744_, 2, v___x_743_);
lean_inc_ref(v___x_744_);
v_it_745_ = l_String_Slice_splitToSubslice___redArg(v___x_744_, v___f_741_);
v___x_746_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__2));
v___x_747_ = lean_obj_once(&l_Std_Http_Request_instToStringHead___lam__3___closed__3, &l_Std_Http_Request_instToStringHead___lam__3___closed__3_once, _init_l_Std_Http_Request_instToStringHead___lam__3___closed__3);
v___x_748_ = l_Std_Http_Request_instToStringHead___lam__3___boxed__const__1;
v___f_749_ = lean_alloc_closure((void*)(l_Std_Http_Request_instEncodeV11Head___lam__2___boxed), 11, 7);
lean_closure_set(v___f_749_, 0, v___x_746_);
lean_closure_set(v___f_749_, 1, v___x_742_);
lean_closure_set(v___f_749_, 2, v___x_747_);
lean_closure_set(v___f_749_, 3, v_name_719_);
lean_closure_set(v___f_749_, 4, v___x_743_);
lean_closure_set(v___f_749_, 5, v___x_748_);
lean_closure_set(v___f_749_, 6, v___x_744_);
v___x_750_ = lean_box(0);
v___x_751_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_749_, v_it_745_, v___x_750_, lean_box(0));
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v___x_752_; 
v___x_752_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__4));
v___y_722_ = v___x_752_;
goto v___jp_721_;
}
else
{
lean_object* v_val_753_; 
v_val_753_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_val_753_);
lean_dec_ref(v___x_751_);
v___y_722_ = v_val_753_;
goto v___jp_721_;
}
v___jp_721_:
{
lean_object* v_data_723_; lean_object* v_size_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_740_; 
v_data_723_ = lean_ctor_get(v_buf_718_, 0);
v_size_724_ = lean_ctor_get(v_buf_718_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_buf_718_);
if (v_isSharedCheck_740_ == 0)
{
v___x_726_ = v_buf_718_;
v_isShared_727_ = v_isSharedCheck_740_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_size_724_);
lean_inc(v_data_723_);
lean_dec(v_buf_718_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_740_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_728_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__0));
v___x_729_ = lean_string_append(v___y_722_, v___x_728_);
v___x_730_ = lean_string_append(v___x_729_, v_value_720_);
v___x_731_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__0));
v___x_732_ = lean_string_append(v___x_730_, v___x_731_);
v___x_733_ = lean_string_to_utf8(v___x_732_);
lean_dec_ref(v___x_732_);
lean_inc_ref(v___x_733_);
v___x_734_ = lean_array_push(v_data_723_, v___x_733_);
v___x_735_ = lean_byte_array_size(v___x_733_);
lean_dec_ref(v___x_733_);
v___x_736_ = lean_nat_add(v_size_724_, v___x_735_);
lean_dec(v_size_724_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v___x_736_);
lean_ctor_set(v___x_726_, 0, v___x_734_);
v___x_738_ = v___x_726_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___boxed(lean_object* v_buf_754_, lean_object* v_name_755_, lean_object* v_value_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Std_Http_Request_instEncodeV11Head___lam__0(v_buf_754_, v_name_755_, v_value_756_);
lean_dec_ref(v_value_756_);
return v_res_757_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__0));
v___x_759_ = lean_string_to_utf8(v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__1(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0);
v___x_761_ = lean_byte_array_size(v___x_760_);
return v___x_761_;
}
}
static uint8_t _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__2(void){
_start:
{
uint32_t v___x_762_; uint8_t v___x_763_; 
v___x_762_ = 32;
v___x_763_ = lean_uint32_to_uint8(v___x_762_);
return v___x_763_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3(void){
_start:
{
uint8_t v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_764_ = lean_uint8_once(&l_Std_Http_Request_instEncodeV11Head___lam__4___closed__2, &l_Std_Http_Request_instEncodeV11Head___lam__4___closed__2_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__2);
v___x_765_ = lean_unsigned_to_nat(1u);
v___x_766_ = lean_mk_empty_array_with_capacity(v___x_765_);
v___x_767_ = lean_box(v___x_764_);
v___x_768_ = lean_array_push(v___x_766_, v___x_767_);
v___x_769_ = lean_byte_array_mk(v___x_768_);
return v___x_769_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__4(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3);
v___x_771_ = lean_byte_array_size(v___x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__4(lean_object* v___f_772_, lean_object* v___f_773_, lean_object* v___f_774_, lean_object* v___f_775_, lean_object* v___f_776_, lean_object* v_buffer_777_, lean_object* v_req_778_){
_start:
{
uint8_t v_method_779_; uint8_t v_version_780_; lean_object* v_uri_781_; lean_object* v_headers_782_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v_port_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v_host_850_; lean_object* v_port_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v_port_966_; lean_object* v___y_967_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v_host_985_; lean_object* v_port_986_; lean_object* v___y_987_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1017_; 
v_method_779_ = lean_ctor_get_uint8(v_req_778_, sizeof(void*)*2);
v_version_780_ = lean_ctor_get_uint8(v_req_778_, sizeof(void*)*2 + 1);
v_uri_781_ = lean_ctor_get(v_req_778_, 0);
lean_inc(v_uri_781_);
v_headers_782_ = lean_ctor_get(v_req_778_, 1);
lean_inc_ref(v_headers_782_);
lean_dec_ref(v_req_778_);
switch(v_method_779_)
{
case 0:
{
lean_object* v___x_1097_; 
v___x_1097_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__26));
v___y_1017_ = v___x_1097_;
goto v___jp_1016_;
}
case 1:
{
lean_object* v___x_1098_; 
v___x_1098_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__27));
v___y_1017_ = v___x_1098_;
goto v___jp_1016_;
}
case 2:
{
lean_object* v___x_1099_; 
v___x_1099_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__28));
v___y_1017_ = v___x_1099_;
goto v___jp_1016_;
}
case 3:
{
lean_object* v___x_1100_; 
v___x_1100_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__29));
v___y_1017_ = v___x_1100_;
goto v___jp_1016_;
}
case 4:
{
lean_object* v___x_1101_; 
v___x_1101_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__30));
v___y_1017_ = v___x_1101_;
goto v___jp_1016_;
}
case 5:
{
lean_object* v___x_1102_; 
v___x_1102_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__31));
v___y_1017_ = v___x_1102_;
goto v___jp_1016_;
}
case 6:
{
lean_object* v___x_1103_; 
v___x_1103_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__32));
v___y_1017_ = v___x_1103_;
goto v___jp_1016_;
}
case 7:
{
lean_object* v___x_1104_; 
v___x_1104_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__33));
v___y_1017_ = v___x_1104_;
goto v___jp_1016_;
}
case 8:
{
lean_object* v___x_1105_; 
v___x_1105_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__34));
v___y_1017_ = v___x_1105_;
goto v___jp_1016_;
}
case 9:
{
lean_object* v___x_1106_; 
v___x_1106_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__35));
v___y_1017_ = v___x_1106_;
goto v___jp_1016_;
}
case 10:
{
lean_object* v___x_1107_; 
v___x_1107_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__36));
v___y_1017_ = v___x_1107_;
goto v___jp_1016_;
}
case 11:
{
lean_object* v___x_1108_; 
v___x_1108_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__37));
v___y_1017_ = v___x_1108_;
goto v___jp_1016_;
}
case 12:
{
lean_object* v___x_1109_; 
v___x_1109_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__38));
v___y_1017_ = v___x_1109_;
goto v___jp_1016_;
}
case 13:
{
lean_object* v___x_1110_; 
v___x_1110_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__39));
v___y_1017_ = v___x_1110_;
goto v___jp_1016_;
}
case 14:
{
lean_object* v___x_1111_; 
v___x_1111_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__40));
v___y_1017_ = v___x_1111_;
goto v___jp_1016_;
}
case 15:
{
lean_object* v___x_1112_; 
v___x_1112_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__41));
v___y_1017_ = v___x_1112_;
goto v___jp_1016_;
}
case 16:
{
lean_object* v___x_1113_; 
v___x_1113_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__42));
v___y_1017_ = v___x_1113_;
goto v___jp_1016_;
}
case 17:
{
lean_object* v___x_1114_; 
v___x_1114_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__43));
v___y_1017_ = v___x_1114_;
goto v___jp_1016_;
}
case 18:
{
lean_object* v___x_1115_; 
v___x_1115_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__44));
v___y_1017_ = v___x_1115_;
goto v___jp_1016_;
}
case 19:
{
lean_object* v___x_1116_; 
v___x_1116_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__45));
v___y_1017_ = v___x_1116_;
goto v___jp_1016_;
}
case 20:
{
lean_object* v___x_1117_; 
v___x_1117_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__46));
v___y_1017_ = v___x_1117_;
goto v___jp_1016_;
}
case 21:
{
lean_object* v___x_1118_; 
v___x_1118_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__47));
v___y_1017_ = v___x_1118_;
goto v___jp_1016_;
}
case 22:
{
lean_object* v___x_1119_; 
v___x_1119_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__48));
v___y_1017_ = v___x_1119_;
goto v___jp_1016_;
}
case 23:
{
lean_object* v___x_1120_; 
v___x_1120_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__49));
v___y_1017_ = v___x_1120_;
goto v___jp_1016_;
}
case 24:
{
lean_object* v___x_1121_; 
v___x_1121_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__50));
v___y_1017_ = v___x_1121_;
goto v___jp_1016_;
}
case 25:
{
lean_object* v___x_1122_; 
v___x_1122_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__51));
v___y_1017_ = v___x_1122_;
goto v___jp_1016_;
}
case 26:
{
lean_object* v___x_1123_; 
v___x_1123_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__52));
v___y_1017_ = v___x_1123_;
goto v___jp_1016_;
}
case 27:
{
lean_object* v___x_1124_; 
v___x_1124_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__53));
v___y_1017_ = v___x_1124_;
goto v___jp_1016_;
}
case 28:
{
lean_object* v___x_1125_; 
v___x_1125_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__54));
v___y_1017_ = v___x_1125_;
goto v___jp_1016_;
}
case 29:
{
lean_object* v___x_1126_; 
v___x_1126_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__55));
v___y_1017_ = v___x_1126_;
goto v___jp_1016_;
}
case 30:
{
lean_object* v___x_1127_; 
v___x_1127_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__56));
v___y_1017_ = v___x_1127_;
goto v___jp_1016_;
}
case 31:
{
lean_object* v___x_1128_; 
v___x_1128_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__57));
v___y_1017_ = v___x_1128_;
goto v___jp_1016_;
}
case 32:
{
lean_object* v___x_1129_; 
v___x_1129_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__58));
v___y_1017_ = v___x_1129_;
goto v___jp_1016_;
}
case 33:
{
lean_object* v___x_1130_; 
v___x_1130_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__59));
v___y_1017_ = v___x_1130_;
goto v___jp_1016_;
}
case 34:
{
lean_object* v___x_1131_; 
v___x_1131_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__60));
v___y_1017_ = v___x_1131_;
goto v___jp_1016_;
}
case 35:
{
lean_object* v___x_1132_; 
v___x_1132_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__61));
v___y_1017_ = v___x_1132_;
goto v___jp_1016_;
}
case 36:
{
lean_object* v___x_1133_; 
v___x_1133_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__62));
v___y_1017_ = v___x_1133_;
goto v___jp_1016_;
}
case 37:
{
lean_object* v___x_1134_; 
v___x_1134_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__63));
v___y_1017_ = v___x_1134_;
goto v___jp_1016_;
}
case 38:
{
lean_object* v___x_1135_; 
v___x_1135_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__64));
v___y_1017_ = v___x_1135_;
goto v___jp_1016_;
}
default: 
{
lean_object* v___x_1136_; 
v___x_1136_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__65));
v___y_1017_ = v___x_1136_;
goto v___jp_1016_;
}
}
v___jp_783_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_buffer_795_; lean_object* v_buffer_796_; lean_object* v_data_797_; lean_object* v_size_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_807_; 
v___x_787_ = lean_string_to_utf8(v___y_786_);
lean_inc_ref(v___x_787_);
v___x_788_ = lean_array_push(v___y_785_, v___x_787_);
v___x_789_ = lean_byte_array_size(v___x_787_);
lean_dec_ref(v___x_787_);
v___x_790_ = lean_nat_add(v___y_784_, v___x_789_);
lean_dec(v___y_784_);
v___x_791_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__0);
v___x_792_ = lean_array_push(v___x_788_, v___x_791_);
v___x_793_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__4___closed__1, &l_Std_Http_Request_instEncodeV11Head___lam__4___closed__1_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__1);
v___x_794_ = lean_nat_add(v___x_790_, v___x_793_);
lean_dec(v___x_790_);
v_buffer_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_795_, 0, v___x_792_);
lean_ctor_set(v_buffer_795_, 1, v___x_794_);
v_buffer_796_ = l_Std_Http_Headers_fold___redArg(v_headers_782_, v_buffer_795_, v___f_772_);
lean_dec_ref(v_headers_782_);
v_data_797_ = lean_ctor_get(v_buffer_796_, 0);
v_size_798_ = lean_ctor_get(v_buffer_796_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_buffer_796_);
if (v_isSharedCheck_807_ == 0)
{
v___x_800_ = v_buffer_796_;
v_isShared_801_ = v_isSharedCheck_807_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_size_798_);
lean_inc(v_data_797_);
lean_dec(v_buffer_796_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_807_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_802_ = lean_array_push(v_data_797_, v___x_791_);
v___x_803_ = lean_nat_add(v_size_798_, v___x_793_);
lean_dec(v_size_798_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v___x_803_);
lean_ctor_set(v___x_800_, 0, v___x_802_);
v___x_805_ = v___x_800_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
v___jp_808_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_814_ = lean_string_to_utf8(v___y_813_);
lean_dec_ref(v___y_813_);
lean_inc_ref(v___x_814_);
v___x_815_ = lean_array_push(v___y_812_, v___x_814_);
v___x_816_ = lean_byte_array_size(v___x_814_);
lean_dec_ref(v___x_814_);
v___x_817_ = lean_nat_add(v___y_809_, v___x_816_);
lean_dec(v___y_809_);
v___x_818_ = lean_array_push(v___x_815_, v___y_810_);
v___x_819_ = lean_nat_add(v___x_817_, v___y_811_);
lean_dec(v___x_817_);
switch(v_version_780_)
{
case 0:
{
lean_object* v___x_820_; 
v___x_820_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__11));
v___y_784_ = v___x_819_;
v___y_785_ = v___x_818_;
v___y_786_ = v___x_820_;
goto v___jp_783_;
}
case 1:
{
lean_object* v___x_821_; 
v___x_821_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__12));
v___y_784_ = v___x_819_;
v___y_785_ = v___x_818_;
v___y_786_ = v___x_821_;
goto v___jp_783_;
}
case 2:
{
lean_object* v___x_822_; 
v___x_822_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__13));
v___y_784_ = v___x_819_;
v___y_785_ = v___x_818_;
v___y_786_ = v___x_822_;
goto v___jp_783_;
}
default: 
{
lean_object* v___x_823_; 
v___x_823_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__14));
v___y_784_ = v___x_819_;
v___y_785_ = v___x_818_;
v___y_786_ = v___x_823_;
goto v___jp_783_;
}
}
}
v___jp_824_:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_string_append(v___y_827_, v___y_825_);
lean_dec_ref(v___y_825_);
v___x_833_ = lean_string_append(v___x_832_, v___y_831_);
lean_dec_ref(v___y_831_);
v___y_809_ = v___y_826_;
v___y_810_ = v___y_828_;
v___y_811_ = v___y_829_;
v___y_812_ = v___y_830_;
v___y_813_ = v___x_833_;
goto v___jp_808_;
}
v___jp_834_:
{
switch(lean_obj_tag(v_port_835_))
{
case 0:
{
lean_object* v___x_842_; 
v___x_842_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__4));
v___y_825_ = v___y_841_;
v___y_826_ = v___y_837_;
v___y_827_ = v___y_836_;
v___y_828_ = v___y_838_;
v___y_829_ = v___y_839_;
v___y_830_ = v___y_840_;
v___y_831_ = v___x_842_;
goto v___jp_824_;
}
case 1:
{
lean_object* v___x_843_; 
v___x_843_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___y_825_ = v___y_841_;
v___y_826_ = v___y_837_;
v___y_827_ = v___y_836_;
v___y_828_ = v___y_838_;
v___y_829_ = v___y_839_;
v___y_830_ = v___y_840_;
v___y_831_ = v___x_843_;
goto v___jp_824_;
}
default: 
{
uint16_t v_port_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_port_844_ = lean_ctor_get_uint16(v_port_835_, 0);
lean_dec_ref(v_port_835_);
v___x_845_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_846_ = lean_uint16_to_nat(v_port_844_);
v___x_847_ = l_Nat_reprFast(v___x_846_);
v___x_848_ = lean_string_append(v___x_845_, v___x_847_);
lean_dec_ref(v___x_847_);
v___y_825_ = v___y_841_;
v___y_826_ = v___y_837_;
v___y_827_ = v___y_836_;
v___y_828_ = v___y_838_;
v___y_829_ = v___y_839_;
v___y_830_ = v___y_840_;
v___y_831_ = v___x_848_;
goto v___jp_824_;
}
}
}
v___jp_849_:
{
switch(lean_obj_tag(v_host_850_))
{
case 0:
{
lean_object* v_name_857_; 
v_name_857_ = lean_ctor_get(v_host_850_, 0);
lean_inc_ref(v_name_857_);
lean_dec_ref(v_host_850_);
v_port_835_ = v_port_851_;
v___y_836_ = v___y_856_;
v___y_837_ = v___y_852_;
v___y_838_ = v___y_853_;
v___y_839_ = v___y_854_;
v___y_840_ = v___y_855_;
v___y_841_ = v_name_857_;
goto v___jp_834_;
}
case 1:
{
lean_object* v_ipv4_858_; lean_object* v___x_859_; 
v_ipv4_858_ = lean_ctor_get(v_host_850_, 0);
lean_inc_ref(v_ipv4_858_);
lean_dec_ref(v_host_850_);
v___x_859_ = lean_uv_ntop_v4(v_ipv4_858_);
lean_dec_ref(v_ipv4_858_);
v_port_835_ = v_port_851_;
v___y_836_ = v___y_856_;
v___y_837_ = v___y_852_;
v___y_838_ = v___y_853_;
v___y_839_ = v___y_854_;
v___y_840_ = v___y_855_;
v___y_841_ = v___x_859_;
goto v___jp_834_;
}
default: 
{
lean_object* v_ipv6_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_ipv6_860_ = lean_ctor_get(v_host_850_, 0);
lean_inc_ref(v_ipv6_860_);
lean_dec_ref(v_host_850_);
v___x_861_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__20));
v___x_862_ = lean_uv_ntop_v6(v_ipv6_860_);
lean_dec_ref(v_ipv6_860_);
v___x_863_ = lean_string_append(v___x_861_, v___x_862_);
lean_dec_ref(v___x_862_);
v___x_864_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__21));
v___x_865_ = lean_string_append(v___x_863_, v___x_864_);
v_port_835_ = v_port_851_;
v___y_836_ = v___y_856_;
v___y_837_ = v___y_852_;
v___y_838_ = v___y_853_;
v___y_839_ = v___y_854_;
v___y_840_ = v___y_855_;
v___y_841_ = v___x_865_;
goto v___jp_834_;
}
}
}
v___jp_866_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_876_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_877_ = lean_string_append(v___y_868_, v___x_876_);
v___x_878_ = lean_string_append(v___x_877_, v___y_869_);
lean_dec_ref(v___y_869_);
v___x_879_ = lean_string_append(v___x_878_, v___y_871_);
lean_dec_ref(v___y_871_);
v___x_880_ = lean_string_append(v___x_879_, v___y_872_);
lean_dec_ref(v___y_872_);
v___x_881_ = lean_string_append(v___x_880_, v___y_875_);
lean_dec_ref(v___y_875_);
v___y_809_ = v___y_867_;
v___y_810_ = v___y_870_;
v___y_811_ = v___y_873_;
v___y_812_ = v___y_874_;
v___y_813_ = v___x_881_;
goto v___jp_808_;
}
v___jp_882_:
{
if (lean_obj_tag(v___y_888_) == 0)
{
lean_object* v___x_892_; 
v___x_892_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__4));
v___y_867_ = v___y_883_;
v___y_868_ = v___y_884_;
v___y_869_ = v___y_885_;
v___y_870_ = v___y_887_;
v___y_871_ = v___y_886_;
v___y_872_ = v___y_891_;
v___y_873_ = v___y_889_;
v___y_874_ = v___y_890_;
v___y_875_ = v___x_892_;
goto v___jp_866_;
}
else
{
lean_object* v_val_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_val_893_ = lean_ctor_get(v___y_888_, 0);
lean_inc(v_val_893_);
lean_dec_ref(v___y_888_);
v___x_894_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__18));
v___x_895_ = l_Std_Http_URI_EncodedFragment_encode(v_val_893_);
lean_dec(v_val_893_);
v___x_896_ = lean_string_from_utf8_unchecked(v___x_895_);
v___x_897_ = lean_string_append(v___x_894_, v___x_896_);
lean_dec_ref(v___x_896_);
v___y_867_ = v___y_883_;
v___y_868_ = v___y_884_;
v___y_869_ = v___y_885_;
v___y_870_ = v___y_887_;
v___y_871_ = v___y_886_;
v___y_872_ = v___y_891_;
v___y_873_ = v___y_889_;
v___y_874_ = v___y_890_;
v___y_875_ = v___x_897_;
goto v___jp_866_;
}
}
v___jp_898_:
{
lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_908_ = lean_array_get_size(v___y_899_);
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = lean_nat_dec_eq(v___x_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v_encodedParams_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_911_ = lean_array_to_list(v___y_899_);
v___x_912_ = lean_box(0);
v_encodedParams_913_ = l_List_mapTR_loop___redArg(v___f_773_, v___x_911_, v___x_912_);
v___x_914_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__15));
v___x_915_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__16));
v___x_916_ = l_String_intercalate(v___x_915_, v_encodedParams_913_);
v___x_917_ = lean_string_append(v___x_914_, v___x_916_);
lean_dec_ref(v___x_916_);
v___y_883_ = v___y_900_;
v___y_884_ = v___y_901_;
v___y_885_ = v___y_902_;
v___y_886_ = v___y_907_;
v___y_887_ = v___y_903_;
v___y_888_ = v___y_905_;
v___y_889_ = v___y_904_;
v___y_890_ = v___y_906_;
v___y_891_ = v___x_917_;
goto v___jp_882_;
}
else
{
lean_object* v___x_918_; 
lean_dec_ref(v___y_899_);
lean_dec_ref(v___f_773_);
v___x_918_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__4));
v___y_883_ = v___y_900_;
v___y_884_ = v___y_901_;
v___y_885_ = v___y_902_;
v___y_886_ = v___y_907_;
v___y_887_ = v___y_903_;
v___y_888_ = v___y_905_;
v___y_889_ = v___y_904_;
v___y_890_ = v___y_906_;
v___y_891_ = v___x_918_;
goto v___jp_882_;
}
}
v___jp_919_:
{
lean_object* v_segments_929_; uint8_t v_absolute_930_; lean_object* v___x_931_; lean_object* v___x_932_; size_t v_sz_933_; size_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v_result_937_; 
v_segments_929_ = lean_ctor_get(v___y_922_, 0);
lean_inc_ref(v_segments_929_);
v_absolute_930_ = lean_ctor_get_uint8(v___y_922_, sizeof(void*)*1);
lean_dec_ref(v___y_922_);
v___x_931_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__19));
v___x_932_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__10));
v_sz_933_ = lean_array_size(v_segments_929_);
v___x_934_ = ((size_t)0ULL);
v___x_935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_932_, v___f_774_, v_sz_933_, v___x_934_, v_segments_929_);
v___x_936_ = lean_array_to_list(v___x_935_);
v_result_937_ = l_String_intercalate(v___x_931_, v___x_936_);
if (v_absolute_930_ == 0)
{
v___y_899_ = v___y_920_;
v___y_900_ = v___y_921_;
v___y_901_ = v___y_923_;
v___y_902_ = v___y_928_;
v___y_903_ = v___y_924_;
v___y_904_ = v___y_926_;
v___y_905_ = v___y_925_;
v___y_906_ = v___y_927_;
v___y_907_ = v_result_937_;
goto v___jp_898_;
}
else
{
lean_object* v___x_938_; 
v___x_938_ = lean_string_append(v___x_931_, v_result_937_);
lean_dec_ref(v_result_937_);
v___y_899_ = v___y_920_;
v___y_900_ = v___y_921_;
v___y_901_ = v___y_923_;
v___y_902_ = v___y_928_;
v___y_903_ = v___y_924_;
v___y_904_ = v___y_926_;
v___y_905_ = v___y_925_;
v___y_906_ = v___y_927_;
v___y_907_ = v___x_938_;
goto v___jp_898_;
}
}
v___jp_939_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = lean_string_append(v___y_942_, v___y_941_);
lean_dec_ref(v___y_941_);
v___x_953_ = lean_string_append(v___x_952_, v___y_951_);
lean_dec_ref(v___y_951_);
lean_inc_ref(v___y_947_);
v___x_954_ = lean_string_append(v___y_947_, v___x_953_);
lean_dec_ref(v___x_953_);
v___y_920_ = v___y_940_;
v___y_921_ = v___y_943_;
v___y_922_ = v___y_945_;
v___y_923_ = v___y_944_;
v___y_924_ = v___y_946_;
v___y_925_ = v___y_949_;
v___y_926_ = v___y_948_;
v___y_927_ = v___y_950_;
v___y_928_ = v___x_954_;
goto v___jp_919_;
}
v___jp_955_:
{
switch(lean_obj_tag(v_port_966_))
{
case 0:
{
lean_object* v___x_968_; 
v___x_968_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__4));
v___y_940_ = v___y_956_;
v___y_941_ = v___y_967_;
v___y_942_ = v___y_957_;
v___y_943_ = v___y_958_;
v___y_944_ = v___y_960_;
v___y_945_ = v___y_959_;
v___y_946_ = v___y_961_;
v___y_947_ = v___y_962_;
v___y_948_ = v___y_964_;
v___y_949_ = v___y_963_;
v___y_950_ = v___y_965_;
v___y_951_ = v___x_968_;
goto v___jp_939_;
}
case 1:
{
lean_object* v___x_969_; 
v___x_969_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___y_940_ = v___y_956_;
v___y_941_ = v___y_967_;
v___y_942_ = v___y_957_;
v___y_943_ = v___y_958_;
v___y_944_ = v___y_960_;
v___y_945_ = v___y_959_;
v___y_946_ = v___y_961_;
v___y_947_ = v___y_962_;
v___y_948_ = v___y_964_;
v___y_949_ = v___y_963_;
v___y_950_ = v___y_965_;
v___y_951_ = v___x_969_;
goto v___jp_939_;
}
default: 
{
uint16_t v_port_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_port_970_ = lean_ctor_get_uint16(v_port_966_, 0);
lean_dec_ref(v_port_966_);
v___x_971_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_972_ = lean_uint16_to_nat(v_port_970_);
v___x_973_ = l_Nat_reprFast(v___x_972_);
v___x_974_ = lean_string_append(v___x_971_, v___x_973_);
lean_dec_ref(v___x_973_);
v___y_940_ = v___y_956_;
v___y_941_ = v___y_967_;
v___y_942_ = v___y_957_;
v___y_943_ = v___y_958_;
v___y_944_ = v___y_960_;
v___y_945_ = v___y_959_;
v___y_946_ = v___y_961_;
v___y_947_ = v___y_962_;
v___y_948_ = v___y_964_;
v___y_949_ = v___y_963_;
v___y_950_ = v___y_965_;
v___y_951_ = v___x_974_;
goto v___jp_939_;
}
}
}
v___jp_975_:
{
switch(lean_obj_tag(v_host_985_))
{
case 0:
{
lean_object* v_name_988_; 
v_name_988_ = lean_ctor_get(v_host_985_, 0);
lean_inc_ref(v_name_988_);
lean_dec_ref(v_host_985_);
v___y_956_ = v___y_976_;
v___y_957_ = v___y_987_;
v___y_958_ = v___y_977_;
v___y_959_ = v___y_979_;
v___y_960_ = v___y_978_;
v___y_961_ = v___y_980_;
v___y_962_ = v___y_981_;
v___y_963_ = v___y_983_;
v___y_964_ = v___y_982_;
v___y_965_ = v___y_984_;
v_port_966_ = v_port_986_;
v___y_967_ = v_name_988_;
goto v___jp_955_;
}
case 1:
{
lean_object* v_ipv4_989_; lean_object* v___x_990_; 
v_ipv4_989_ = lean_ctor_get(v_host_985_, 0);
lean_inc_ref(v_ipv4_989_);
lean_dec_ref(v_host_985_);
v___x_990_ = lean_uv_ntop_v4(v_ipv4_989_);
lean_dec_ref(v_ipv4_989_);
v___y_956_ = v___y_976_;
v___y_957_ = v___y_987_;
v___y_958_ = v___y_977_;
v___y_959_ = v___y_979_;
v___y_960_ = v___y_978_;
v___y_961_ = v___y_980_;
v___y_962_ = v___y_981_;
v___y_963_ = v___y_983_;
v___y_964_ = v___y_982_;
v___y_965_ = v___y_984_;
v_port_966_ = v_port_986_;
v___y_967_ = v___x_990_;
goto v___jp_955_;
}
default: 
{
lean_object* v_ipv6_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_ipv6_991_ = lean_ctor_get(v_host_985_, 0);
lean_inc_ref(v_ipv6_991_);
lean_dec_ref(v_host_985_);
v___x_992_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__20));
v___x_993_ = lean_uv_ntop_v6(v_ipv6_991_);
lean_dec_ref(v_ipv6_991_);
v___x_994_ = lean_string_append(v___x_992_, v___x_993_);
lean_dec_ref(v___x_993_);
v___x_995_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__21));
v___x_996_ = lean_string_append(v___x_994_, v___x_995_);
v___y_956_ = v___y_976_;
v___y_957_ = v___y_987_;
v___y_958_ = v___y_977_;
v___y_959_ = v___y_979_;
v___y_960_ = v___y_978_;
v___y_961_ = v___y_980_;
v___y_962_ = v___y_981_;
v___y_963_ = v___y_983_;
v___y_964_ = v___y_982_;
v___y_965_ = v___y_984_;
v_port_966_ = v_port_986_;
v___y_967_ = v___x_996_;
goto v___jp_955_;
}
}
}
v___jp_997_:
{
if (lean_obj_tag(v___y_998_) == 0)
{
lean_dec_ref(v___f_775_);
v___y_809_ = v___y_999_;
v___y_810_ = v___y_1000_;
v___y_811_ = v___y_1001_;
v___y_812_ = v___y_1002_;
v___y_813_ = v___y_1003_;
goto v___jp_808_;
}
else
{
lean_object* v_val_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v_val_1004_ = lean_ctor_get(v___y_998_, 0);
lean_inc(v_val_1004_);
lean_dec_ref(v___y_998_);
v___x_1005_ = lean_array_get_size(v_val_1004_);
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_nat_dec_eq(v___x_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v_encodedParams_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1008_ = lean_array_to_list(v_val_1004_);
v___x_1009_ = lean_box(0);
v_encodedParams_1010_ = l_List_mapTR_loop___redArg(v___f_775_, v___x_1008_, v___x_1009_);
v___x_1011_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__15));
v___x_1012_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__16));
v___x_1013_ = l_String_intercalate(v___x_1012_, v_encodedParams_1010_);
v___x_1014_ = lean_string_append(v___x_1011_, v___x_1013_);
lean_dec_ref(v___x_1013_);
v___x_1015_ = lean_string_append(v___y_1003_, v___x_1014_);
lean_dec_ref(v___x_1014_);
v___y_809_ = v___y_999_;
v___y_810_ = v___y_1000_;
v___y_811_ = v___y_1001_;
v___y_812_ = v___y_1002_;
v___y_813_ = v___x_1015_;
goto v___jp_808_;
}
else
{
lean_dec(v_val_1004_);
lean_dec_ref(v___f_775_);
v___y_809_ = v___y_999_;
v___y_810_ = v___y_1000_;
v___y_811_ = v___y_1001_;
v___y_812_ = v___y_1002_;
v___y_813_ = v___y_1003_;
goto v___jp_808_;
}
}
}
v___jp_1016_:
{
lean_object* v_data_1018_; lean_object* v_size_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_data_1018_ = lean_ctor_get(v_buffer_777_, 0);
lean_inc_ref(v_data_1018_);
v_size_1019_ = lean_ctor_get(v_buffer_777_, 1);
lean_inc(v_size_1019_);
lean_dec_ref(v_buffer_777_);
v___x_1020_ = lean_string_to_utf8(v___y_1017_);
lean_inc_ref(v___x_1020_);
v___x_1021_ = lean_array_push(v_data_1018_, v___x_1020_);
v___x_1022_ = lean_byte_array_size(v___x_1020_);
lean_dec_ref(v___x_1020_);
v___x_1023_ = lean_nat_add(v_size_1019_, v___x_1022_);
lean_dec(v_size_1019_);
v___x_1024_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__3);
v___x_1025_ = lean_array_push(v___x_1021_, v___x_1024_);
v___x_1026_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__4___closed__4, &l_Std_Http_Request_instEncodeV11Head___lam__4___closed__4_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__4___closed__4);
v___x_1027_ = lean_nat_add(v___x_1023_, v___x_1026_);
lean_dec(v___x_1023_);
switch(lean_obj_tag(v_uri_781_))
{
case 0:
{
lean_object* v_path_1028_; lean_object* v_query_1029_; lean_object* v_segments_1030_; uint8_t v_absolute_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; size_t v_sz_1034_; size_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v_result_1038_; 
lean_dec_ref(v___f_774_);
lean_dec_ref(v___f_773_);
v_path_1028_ = lean_ctor_get(v_uri_781_, 0);
lean_inc_ref(v_path_1028_);
v_query_1029_ = lean_ctor_get(v_uri_781_, 1);
lean_inc(v_query_1029_);
lean_dec_ref(v_uri_781_);
v_segments_1030_ = lean_ctor_get(v_path_1028_, 0);
lean_inc_ref(v_segments_1030_);
v_absolute_1031_ = lean_ctor_get_uint8(v_path_1028_, sizeof(void*)*1);
lean_dec_ref(v_path_1028_);
v___x_1032_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__19));
v___x_1033_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__10));
v_sz_1034_ = lean_array_size(v_segments_1030_);
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1033_, v___f_776_, v_sz_1034_, v___x_1035_, v_segments_1030_);
v___x_1037_ = lean_array_to_list(v___x_1036_);
v_result_1038_ = l_String_intercalate(v___x_1032_, v___x_1037_);
if (v_absolute_1031_ == 0)
{
v___y_998_ = v_query_1029_;
v___y_999_ = v___x_1027_;
v___y_1000_ = v___x_1024_;
v___y_1001_ = v___x_1026_;
v___y_1002_ = v___x_1025_;
v___y_1003_ = v_result_1038_;
goto v___jp_997_;
}
else
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_string_append(v___x_1032_, v_result_1038_);
lean_dec_ref(v_result_1038_);
v___y_998_ = v_query_1029_;
v___y_999_ = v___x_1027_;
v___y_1000_ = v___x_1024_;
v___y_1001_ = v___x_1026_;
v___y_1002_ = v___x_1025_;
v___y_1003_ = v___x_1039_;
goto v___jp_997_;
}
}
case 1:
{
lean_object* v_uri_1040_; lean_object* v_authority_1041_; 
lean_dec_ref(v___f_776_);
lean_dec_ref(v___f_775_);
v_uri_1040_ = lean_ctor_get(v_uri_781_, 0);
lean_inc_ref(v_uri_1040_);
lean_dec_ref(v_uri_781_);
v_authority_1041_ = lean_ctor_get(v_uri_1040_, 1);
if (lean_obj_tag(v_authority_1041_) == 0)
{
lean_object* v_scheme_1042_; lean_object* v_path_1043_; lean_object* v_query_1044_; lean_object* v_fragment_1045_; lean_object* v___x_1046_; 
v_scheme_1042_ = lean_ctor_get(v_uri_1040_, 0);
lean_inc_ref(v_scheme_1042_);
v_path_1043_ = lean_ctor_get(v_uri_1040_, 2);
lean_inc_ref(v_path_1043_);
v_query_1044_ = lean_ctor_get(v_uri_1040_, 3);
lean_inc_ref(v_query_1044_);
v_fragment_1045_ = lean_ctor_get(v_uri_1040_, 4);
lean_inc(v_fragment_1045_);
lean_dec_ref(v_uri_1040_);
v___x_1046_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__4));
v___y_920_ = v_query_1044_;
v___y_921_ = v___x_1027_;
v___y_922_ = v_path_1043_;
v___y_923_ = v_scheme_1042_;
v___y_924_ = v___x_1024_;
v___y_925_ = v_fragment_1045_;
v___y_926_ = v___x_1026_;
v___y_927_ = v___x_1025_;
v___y_928_ = v___x_1046_;
goto v___jp_919_;
}
else
{
lean_object* v_val_1047_; lean_object* v_scheme_1048_; lean_object* v_path_1049_; lean_object* v_query_1050_; lean_object* v_fragment_1051_; lean_object* v_userInfo_1052_; lean_object* v_host_1053_; lean_object* v_port_1054_; lean_object* v___x_1055_; 
v_val_1047_ = lean_ctor_get(v_authority_1041_, 0);
lean_inc(v_val_1047_);
v_scheme_1048_ = lean_ctor_get(v_uri_1040_, 0);
lean_inc_ref(v_scheme_1048_);
v_path_1049_ = lean_ctor_get(v_uri_1040_, 2);
lean_inc_ref(v_path_1049_);
v_query_1050_ = lean_ctor_get(v_uri_1040_, 3);
lean_inc_ref(v_query_1050_);
v_fragment_1051_ = lean_ctor_get(v_uri_1040_, 4);
lean_inc(v_fragment_1051_);
lean_dec_ref(v_uri_1040_);
v_userInfo_1052_ = lean_ctor_get(v_val_1047_, 0);
lean_inc(v_userInfo_1052_);
v_host_1053_ = lean_ctor_get(v_val_1047_, 1);
lean_inc_ref(v_host_1053_);
v_port_1054_ = lean_ctor_get(v_val_1047_, 2);
lean_inc(v_port_1054_);
lean_dec(v_val_1047_);
v___x_1055_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__23));
if (lean_obj_tag(v_userInfo_1052_) == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__4));
v___y_976_ = v_query_1050_;
v___y_977_ = v___x_1027_;
v___y_978_ = v_scheme_1048_;
v___y_979_ = v_path_1049_;
v___y_980_ = v___x_1024_;
v___y_981_ = v___x_1055_;
v___y_982_ = v___x_1026_;
v___y_983_ = v_fragment_1051_;
v___y_984_ = v___x_1025_;
v_host_985_ = v_host_1053_;
v_port_986_ = v_port_1054_;
v___y_987_ = v___x_1056_;
goto v___jp_975_;
}
else
{
lean_object* v_val_1057_; lean_object* v_password_1058_; 
v_val_1057_ = lean_ctor_get(v_userInfo_1052_, 0);
lean_inc(v_val_1057_);
lean_dec_ref(v_userInfo_1052_);
v_password_1058_ = lean_ctor_get(v_val_1057_, 1);
if (lean_obj_tag(v_password_1058_) == 0)
{
lean_object* v_username_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_username_1059_ = lean_ctor_get(v_val_1057_, 0);
lean_inc_ref(v_username_1059_);
lean_dec(v_val_1057_);
v___x_1060_ = lean_string_from_utf8_unchecked(v_username_1059_);
v___x_1061_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__24));
v___x_1062_ = lean_string_append(v___x_1060_, v___x_1061_);
v___y_976_ = v_query_1050_;
v___y_977_ = v___x_1027_;
v___y_978_ = v_scheme_1048_;
v___y_979_ = v_path_1049_;
v___y_980_ = v___x_1024_;
v___y_981_ = v___x_1055_;
v___y_982_ = v___x_1026_;
v___y_983_ = v_fragment_1051_;
v___y_984_ = v___x_1025_;
v_host_985_ = v_host_1053_;
v_port_986_ = v_port_1054_;
v___y_987_ = v___x_1062_;
goto v___jp_975_;
}
else
{
lean_object* v_username_1063_; lean_object* v_val_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_inc_ref(v_password_1058_);
v_username_1063_ = lean_ctor_get(v_val_1057_, 0);
lean_inc_ref(v_username_1063_);
lean_dec(v_val_1057_);
v_val_1064_ = lean_ctor_get(v_password_1058_, 0);
lean_inc(v_val_1064_);
lean_dec_ref(v_password_1058_);
v___x_1065_ = lean_string_from_utf8_unchecked(v_username_1063_);
v___x_1066_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_1067_ = lean_string_append(v___x_1065_, v___x_1066_);
v___x_1068_ = lean_string_from_utf8_unchecked(v_val_1064_);
v___x_1069_ = lean_string_append(v___x_1067_, v___x_1068_);
lean_dec_ref(v___x_1068_);
v___x_1070_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__24));
v___x_1071_ = lean_string_append(v___x_1069_, v___x_1070_);
v___y_976_ = v_query_1050_;
v___y_977_ = v___x_1027_;
v___y_978_ = v_scheme_1048_;
v___y_979_ = v_path_1049_;
v___y_980_ = v___x_1024_;
v___y_981_ = v___x_1055_;
v___y_982_ = v___x_1026_;
v___y_983_ = v_fragment_1051_;
v___y_984_ = v___x_1025_;
v_host_985_ = v_host_1053_;
v_port_986_ = v_port_1054_;
v___y_987_ = v___x_1071_;
goto v___jp_975_;
}
}
}
}
case 2:
{
lean_object* v_authority_1072_; lean_object* v_userInfo_1073_; 
lean_dec_ref(v___f_776_);
lean_dec_ref(v___f_775_);
lean_dec_ref(v___f_774_);
lean_dec_ref(v___f_773_);
v_authority_1072_ = lean_ctor_get(v_uri_781_, 0);
lean_inc_ref(v_authority_1072_);
lean_dec_ref(v_uri_781_);
v_userInfo_1073_ = lean_ctor_get(v_authority_1072_, 0);
if (lean_obj_tag(v_userInfo_1073_) == 0)
{
lean_object* v_host_1074_; lean_object* v_port_1075_; lean_object* v___x_1076_; 
v_host_1074_ = lean_ctor_get(v_authority_1072_, 1);
lean_inc_ref(v_host_1074_);
v_port_1075_ = lean_ctor_get(v_authority_1072_, 2);
lean_inc(v_port_1075_);
lean_dec_ref(v_authority_1072_);
v___x_1076_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__4));
v_host_850_ = v_host_1074_;
v_port_851_ = v_port_1075_;
v___y_852_ = v___x_1027_;
v___y_853_ = v___x_1024_;
v___y_854_ = v___x_1026_;
v___y_855_ = v___x_1025_;
v___y_856_ = v___x_1076_;
goto v___jp_849_;
}
else
{
lean_object* v_val_1077_; lean_object* v_password_1078_; 
v_val_1077_ = lean_ctor_get(v_userInfo_1073_, 0);
lean_inc(v_val_1077_);
v_password_1078_ = lean_ctor_get(v_val_1077_, 1);
if (lean_obj_tag(v_password_1078_) == 0)
{
lean_object* v_host_1079_; lean_object* v_port_1080_; lean_object* v_username_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_host_1079_ = lean_ctor_get(v_authority_1072_, 1);
lean_inc_ref(v_host_1079_);
v_port_1080_ = lean_ctor_get(v_authority_1072_, 2);
lean_inc(v_port_1080_);
lean_dec_ref(v_authority_1072_);
v_username_1081_ = lean_ctor_get(v_val_1077_, 0);
lean_inc_ref(v_username_1081_);
lean_dec(v_val_1077_);
v___x_1082_ = lean_string_from_utf8_unchecked(v_username_1081_);
v___x_1083_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__24));
v___x_1084_ = lean_string_append(v___x_1082_, v___x_1083_);
v_host_850_ = v_host_1079_;
v_port_851_ = v_port_1080_;
v___y_852_ = v___x_1027_;
v___y_853_ = v___x_1024_;
v___y_854_ = v___x_1026_;
v___y_855_ = v___x_1025_;
v___y_856_ = v___x_1084_;
goto v___jp_849_;
}
else
{
lean_object* v_host_1085_; lean_object* v_port_1086_; lean_object* v_username_1087_; lean_object* v_val_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_inc_ref(v_password_1078_);
v_host_1085_ = lean_ctor_get(v_authority_1072_, 1);
lean_inc_ref(v_host_1085_);
v_port_1086_ = lean_ctor_get(v_authority_1072_, 2);
lean_inc(v_port_1086_);
lean_dec_ref(v_authority_1072_);
v_username_1087_ = lean_ctor_get(v_val_1077_, 0);
lean_inc_ref(v_username_1087_);
lean_dec(v_val_1077_);
v_val_1088_ = lean_ctor_get(v_password_1078_, 0);
lean_inc(v_val_1088_);
lean_dec_ref(v_password_1078_);
v___x_1089_ = lean_string_from_utf8_unchecked(v_username_1087_);
v___x_1090_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_1091_ = lean_string_append(v___x_1089_, v___x_1090_);
v___x_1092_ = lean_string_from_utf8_unchecked(v_val_1088_);
v___x_1093_ = lean_string_append(v___x_1091_, v___x_1092_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__24));
v___x_1095_ = lean_string_append(v___x_1093_, v___x_1094_);
v_host_850_ = v_host_1085_;
v_port_851_ = v_port_1086_;
v___y_852_ = v___x_1027_;
v___y_853_ = v___x_1024_;
v___y_854_ = v___x_1026_;
v___y_855_ = v___x_1025_;
v___y_856_ = v___x_1095_;
goto v___jp_849_;
}
}
}
default: 
{
lean_object* v___x_1096_; 
lean_dec_ref(v___f_776_);
lean_dec_ref(v___f_775_);
lean_dec_ref(v___f_774_);
lean_dec_ref(v___f_773_);
v___x_1096_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__25));
v___y_809_ = v___x_1027_;
v___y_810_ = v___x_1024_;
v___y_811_ = v___x_1026_;
v___y_812_ = v___x_1025_;
v___y_813_ = v___x_1096_;
goto v___jp_808_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__0(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; 
v___x_1143_ = l_Std_Http_Headers_empty;
v___x_1144_ = lean_box(3);
v___x_1145_ = 1;
v___x_1146_ = 8;
v___x_1147_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1147_, 0, v___x_1144_);
lean_ctor_set(v___x_1147_, 1, v___x_1143_);
lean_ctor_set_uint8(v___x_1147_, sizeof(void*)*2, v___x_1146_);
lean_ctor_set_uint8(v___x_1147_, sizeof(void*)*2 + 1, v___x_1145_);
return v___x_1147_;
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__1(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = l_Std_Http_Extensions_empty;
v___x_1149_ = lean_obj_once(&l_Std_Http_Request_new___closed__0, &l_Std_Http_Request_new___closed__0_once, _init_l_Std_Http_Request_new___closed__0);
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
lean_ctor_set(v___x_1150_, 1, v___x_1148_);
return v___x_1150_;
}
}
static lean_object* _init_l_Std_Http_Request_new(void){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_obj_once(&l_Std_Http_Request_new___closed__1, &l_Std_Http_Request_new___closed__1_once, _init_l_Std_Http_Request_new___closed__1);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method(lean_object* v_builder_1152_, uint8_t v_method_1153_){
_start:
{
lean_object* v_line_1154_; lean_object* v_extensions_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1172_; 
v_line_1154_ = lean_ctor_get(v_builder_1152_, 0);
v_extensions_1155_ = lean_ctor_get(v_builder_1152_, 1);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_builder_1152_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1157_ = v_builder_1152_;
v_isShared_1158_ = v_isSharedCheck_1172_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_extensions_1155_);
lean_inc(v_line_1154_);
lean_dec(v_builder_1152_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1172_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
uint8_t v_version_1159_; lean_object* v_uri_1160_; lean_object* v_headers_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1171_; 
v_version_1159_ = lean_ctor_get_uint8(v_line_1154_, sizeof(void*)*2 + 1);
v_uri_1160_ = lean_ctor_get(v_line_1154_, 0);
v_headers_1161_ = lean_ctor_get(v_line_1154_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_line_1154_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1163_ = v_line_1154_;
v_isShared_1164_ = v_isSharedCheck_1171_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_headers_1161_);
lean_inc(v_uri_1160_);
lean_dec(v_line_1154_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1171_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_uri_1160_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_headers_1161_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*2 + 1, v_version_1159_);
v___x_1166_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1168_; 
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*2, v_method_1153_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1166_);
v___x_1168_ = v___x_1157_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_extensions_1155_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method___boxed(lean_object* v_builder_1173_, lean_object* v_method_1174_){
_start:
{
uint8_t v_method_boxed_1175_; lean_object* v_res_1176_; 
v_method_boxed_1175_ = lean_unbox(v_method_1174_);
v_res_1176_ = l_Std_Http_Request_Builder_method(v_builder_1173_, v_method_boxed_1175_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version(lean_object* v_builder_1177_, uint8_t v_version_1178_){
_start:
{
lean_object* v_line_1179_; lean_object* v_extensions_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1197_; 
v_line_1179_ = lean_ctor_get(v_builder_1177_, 0);
v_extensions_1180_ = lean_ctor_get(v_builder_1177_, 1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_builder_1177_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1182_ = v_builder_1177_;
v_isShared_1183_ = v_isSharedCheck_1197_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_extensions_1180_);
lean_inc(v_line_1179_);
lean_dec(v_builder_1177_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1197_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
uint8_t v_method_1184_; lean_object* v_uri_1185_; lean_object* v_headers_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1196_; 
v_method_1184_ = lean_ctor_get_uint8(v_line_1179_, sizeof(void*)*2);
v_uri_1185_ = lean_ctor_get(v_line_1179_, 0);
v_headers_1186_ = lean_ctor_get(v_line_1179_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_line_1179_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1188_ = v_line_1179_;
v_isShared_1189_ = v_isSharedCheck_1196_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_headers_1186_);
lean_inc(v_uri_1185_);
lean_dec(v_line_1179_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1196_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_uri_1185_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_headers_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1195_, sizeof(void*)*2, v_method_1184_);
v___x_1191_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1193_; 
lean_ctor_set_uint8(v___x_1191_, sizeof(void*)*2 + 1, v_version_1178_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1191_);
v___x_1193_ = v___x_1182_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_extensions_1180_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version___boxed(lean_object* v_builder_1198_, lean_object* v_version_1199_){
_start:
{
uint8_t v_version_boxed_1200_; lean_object* v_res_1201_; 
v_version_boxed_1200_ = lean_unbox(v_version_1199_);
v_res_1201_ = l_Std_Http_Request_Builder_version(v_builder_1198_, v_version_boxed_1200_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri(lean_object* v_builder_1202_, lean_object* v_uri_1203_){
_start:
{
lean_object* v_line_1204_; lean_object* v_extensions_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1223_; 
v_line_1204_ = lean_ctor_get(v_builder_1202_, 0);
v_extensions_1205_ = lean_ctor_get(v_builder_1202_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_builder_1202_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1207_ = v_builder_1202_;
v_isShared_1208_ = v_isSharedCheck_1223_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_extensions_1205_);
lean_inc(v_line_1204_);
lean_dec(v_builder_1202_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1223_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
uint8_t v_method_1209_; uint8_t v_version_1210_; lean_object* v_headers_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1221_; 
v_method_1209_ = lean_ctor_get_uint8(v_line_1204_, sizeof(void*)*2);
v_version_1210_ = lean_ctor_get_uint8(v_line_1204_, sizeof(void*)*2 + 1);
v_headers_1211_ = lean_ctor_get(v_line_1204_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_line_1204_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v_line_1204_, 0);
lean_dec(v_unused_1222_);
v___x_1213_ = v_line_1204_;
v_isShared_1214_ = v_isSharedCheck_1221_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_headers_1211_);
lean_dec(v_line_1204_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1221_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v_uri_1203_);
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_uri_1203_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_headers_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1220_, sizeof(void*)*2, v_method_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1220_, sizeof(void*)*2 + 1, v_version_1210_);
v___x_1216_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1218_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1216_);
v___x_1218_ = v___x_1207_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_extensions_1205_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(lean_object* v_msg_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = l_Std_Http_instInhabitedRequestTarget_default;
v___x_1226_ = lean_panic_fn_borrowed(v___x_1225_, v_msg_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___lam__0(lean_object* v___x_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_pos_1233_; lean_object* v_array_1234_; lean_object* v_idx_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v_pos_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_pos_1233_);
v_array_1234_ = lean_ctor_get(v_pos_1233_, 0);
v_idx_1235_ = lean_ctor_get(v_pos_1233_, 1);
v___x_1236_ = lean_byte_array_size(v_array_1234_);
v___x_1237_ = lean_nat_dec_lt(v_idx_1235_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_dec(v_pos_1233_);
return v___x_1232_;
}
else
{
lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1245_; 
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; lean_object* v_unused_1247_; 
v_unused_1246_ = lean_ctor_get(v___x_1232_, 1);
lean_dec(v_unused_1246_);
v_unused_1247_ = lean_ctor_get(v___x_1232_, 0);
lean_dec(v_unused_1247_);
v___x_1239_ = v___x_1232_;
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
else
{
lean_dec(v___x_1232_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___lam__0___closed__1));
if (v_isShared_1240_ == 0)
{
lean_ctor_set_tag(v___x_1239_, 1);
lean_ctor_set(v___x_1239_, 1, v___x_1241_);
v___x_1243_ = v___x_1239_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_pos_1233_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
else
{
return v___x_1232_;
}
}
}
static lean_object* _init_l_Std_Http_Request_Builder_uri_x21___closed__5(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1261_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__4));
v___x_1262_ = lean_unsigned_to_nat(12u);
v___x_1263_ = lean_unsigned_to_nat(45u);
v___x_1264_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__3));
v___x_1265_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__2));
v___x_1266_ = l_mkPanicMessageWithDecl(v___x_1265_, v___x_1264_, v___x_1263_, v___x_1262_, v___x_1261_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21(lean_object* v_builder_1267_, lean_object* v_uri_1268_){
_start:
{
lean_object* v___y_1270_; lean_object* v___f_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___f_1291_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__1));
v___x_1292_ = lean_string_to_utf8(v_uri_1268_);
v___x_1293_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1291_, v___x_1292_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_dec_ref(v___x_1293_);
v___x_1294_ = lean_obj_once(&l_Std_Http_Request_Builder_uri_x21___closed__5, &l_Std_Http_Request_Builder_uri_x21___closed__5_once, _init_l_Std_Http_Request_Builder_uri_x21___closed__5);
v___x_1295_ = l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(v___x_1294_);
v___y_1270_ = v___x_1295_;
goto v___jp_1269_;
}
else
{
lean_object* v_a_1296_; 
v_a_1296_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1296_);
lean_dec_ref(v___x_1293_);
v___y_1270_ = v_a_1296_;
goto v___jp_1269_;
}
v___jp_1269_:
{
lean_object* v_line_1271_; lean_object* v_extensions_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1290_; 
v_line_1271_ = lean_ctor_get(v_builder_1267_, 0);
v_extensions_1272_ = lean_ctor_get(v_builder_1267_, 1);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_builder_1267_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1274_ = v_builder_1267_;
v_isShared_1275_ = v_isSharedCheck_1290_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_extensions_1272_);
lean_inc(v_line_1271_);
lean_dec(v_builder_1267_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1290_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
uint8_t v_method_1276_; uint8_t v_version_1277_; lean_object* v_headers_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1288_; 
v_method_1276_ = lean_ctor_get_uint8(v_line_1271_, sizeof(void*)*2);
v_version_1277_ = lean_ctor_get_uint8(v_line_1271_, sizeof(void*)*2 + 1);
v_headers_1278_ = lean_ctor_get(v_line_1271_, 1);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_line_1271_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v_line_1271_, 0);
lean_dec(v_unused_1289_);
v___x_1280_ = v_line_1271_;
v_isShared_1281_ = v_isSharedCheck_1288_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_headers_1278_);
lean_dec(v_line_1271_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1288_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___y_1270_);
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___y_1270_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_headers_1278_);
lean_ctor_set_uint8(v_reuseFailAlloc_1287_, sizeof(void*)*2, v_method_1276_);
lean_ctor_set_uint8(v_reuseFailAlloc_1287_, sizeof(void*)*2 + 1, v_version_1277_);
v___x_1283_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1285_; 
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1283_);
v___x_1285_ = v___x_1274_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_extensions_1272_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___boxed(lean_object* v_builder_1297_, lean_object* v_uri_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Std_Http_Request_Builder_uri_x21(v_builder_1297_, v_uri_1298_);
lean_dec_ref(v_uri_1298_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headers(lean_object* v_builder_1300_, lean_object* v_headers_1301_){
_start:
{
lean_object* v_line_1302_; lean_object* v_extensions_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1321_; 
v_line_1302_ = lean_ctor_get(v_builder_1300_, 0);
v_extensions_1303_ = lean_ctor_get(v_builder_1300_, 1);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_builder_1300_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1305_ = v_builder_1300_;
v_isShared_1306_ = v_isSharedCheck_1321_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_extensions_1303_);
lean_inc(v_line_1302_);
lean_dec(v_builder_1300_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1321_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
uint8_t v_method_1307_; uint8_t v_version_1308_; lean_object* v_uri_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1319_; 
v_method_1307_ = lean_ctor_get_uint8(v_line_1302_, sizeof(void*)*2);
v_version_1308_ = lean_ctor_get_uint8(v_line_1302_, sizeof(void*)*2 + 1);
v_uri_1309_ = lean_ctor_get(v_line_1302_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_line_1302_);
if (v_isSharedCheck_1319_ == 0)
{
lean_object* v_unused_1320_; 
v_unused_1320_ = lean_ctor_get(v_line_1302_, 1);
lean_dec(v_unused_1320_);
v___x_1311_ = v_line_1302_;
v_isShared_1312_ = v_isSharedCheck_1319_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_uri_1309_);
lean_dec(v_line_1302_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1319_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 1, v_headers_1301_);
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_uri_1309_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_headers_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*2, v_method_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*2 + 1, v_version_1308_);
v___x_1314_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1316_; 
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v___x_1314_);
v___x_1316_ = v___x_1305_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_extensions_1303_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(lean_object* v_i_1322_, lean_object* v_x_1323_){
_start:
{
if (lean_obj_tag(v_x_1323_) == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1324_ = lean_unsigned_to_nat(1u);
v___x_1325_ = lean_mk_empty_array_with_capacity(v___x_1324_);
v___x_1326_ = lean_array_push(v___x_1325_, v_i_1322_);
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
return v___x_1327_;
}
else
{
lean_object* v_val_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1336_; 
v_val_1328_ = lean_ctor_get(v_x_1323_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_x_1323_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1330_ = v_x_1323_;
v_isShared_1331_ = v_isSharedCheck_1336_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_val_1328_);
lean_dec(v_x_1323_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1336_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1332_ = lean_array_push(v_val_1328_, v_i_1322_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1332_);
v___x_1334_ = v___x_1330_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(lean_object* v_i_1337_, lean_object* v_a_1338_, lean_object* v_x_1339_){
_start:
{
if (lean_obj_tag(v_x_1339_) == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v_val_1342_; lean_object* v___x_1343_; 
v___x_1340_ = lean_box(0);
v___x_1341_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(v_i_1337_, v___x_1340_);
v_val_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_val_1342_);
lean_dec(v___x_1341_);
v___x_1343_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1343_, 0, v_a_1338_);
lean_ctor_set(v___x_1343_, 1, v_val_1342_);
lean_ctor_set(v___x_1343_, 2, v_x_1339_);
return v___x_1343_;
}
else
{
lean_object* v_key_1344_; lean_object* v_value_1345_; lean_object* v_tail_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1361_; 
v_key_1344_ = lean_ctor_get(v_x_1339_, 0);
v_value_1345_ = lean_ctor_get(v_x_1339_, 1);
v_tail_1346_ = lean_ctor_get(v_x_1339_, 2);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_x_1339_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1348_ = v_x_1339_;
v_isShared_1349_ = v_isSharedCheck_1361_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_tail_1346_);
lean_inc(v_value_1345_);
lean_inc(v_key_1344_);
lean_dec(v_x_1339_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1361_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
uint8_t v___x_1350_; 
v___x_1350_ = lean_string_dec_eq(v_key_1344_, v_a_1338_);
if (v___x_1350_ == 0)
{
lean_object* v_tail_1351_; lean_object* v___x_1353_; 
v_tail_1351_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_1337_, v_a_1338_, v_tail_1346_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 2, v_tail_1351_);
v___x_1353_ = v___x_1348_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_key_1344_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_value_1345_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v_tail_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v_val_1357_; lean_object* v___x_1359_; 
lean_dec(v_key_1344_);
v___x_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1355_, 0, v_value_1345_);
v___x_1356_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(v_i_1337_, v___x_1355_);
v_val_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_val_1357_);
lean_dec(v___x_1356_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 1, v_val_1357_);
lean_ctor_set(v___x_1348_, 0, v_a_1338_);
v___x_1359_ = v___x_1348_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1338_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_val_1357_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v_tail_1346_);
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
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(lean_object* v_a_1362_, lean_object* v_x_1363_){
_start:
{
if (lean_obj_tag(v_x_1363_) == 0)
{
uint8_t v___x_1364_; 
v___x_1364_ = 0;
return v___x_1364_;
}
else
{
lean_object* v_key_1365_; lean_object* v_tail_1366_; uint8_t v___x_1367_; 
v_key_1365_ = lean_ctor_get(v_x_1363_, 0);
v_tail_1366_ = lean_ctor_get(v_x_1363_, 2);
v___x_1367_ = lean_string_dec_eq(v_key_1365_, v_a_1362_);
if (v___x_1367_ == 0)
{
v_x_1363_ = v_tail_1366_;
goto _start;
}
else
{
return v___x_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg___boxed(lean_object* v_a_1369_, lean_object* v_x_1370_){
_start:
{
uint8_t v_res_1371_; lean_object* v_r_1372_; 
v_res_1371_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1369_, v_x_1370_);
lean_dec(v_x_1370_);
lean_dec_ref(v_a_1369_);
v_r_1372_ = lean_box(v_res_1371_);
return v_r_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1373_, lean_object* v_x_1374_){
_start:
{
if (lean_obj_tag(v_x_1374_) == 0)
{
return v_x_1373_;
}
else
{
lean_object* v_key_1375_; lean_object* v_value_1376_; lean_object* v_tail_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1400_; 
v_key_1375_ = lean_ctor_get(v_x_1374_, 0);
v_value_1376_ = lean_ctor_get(v_x_1374_, 1);
v_tail_1377_ = lean_ctor_get(v_x_1374_, 2);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_x_1374_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1379_ = v_x_1374_;
v_isShared_1380_ = v_isSharedCheck_1400_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_tail_1377_);
lean_inc(v_value_1376_);
lean_inc(v_key_1375_);
lean_dec(v_x_1374_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1400_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; uint64_t v___x_1382_; uint64_t v___x_1383_; uint64_t v___x_1384_; uint64_t v_fold_1385_; uint64_t v___x_1386_; uint64_t v___x_1387_; uint64_t v___x_1388_; size_t v___x_1389_; size_t v___x_1390_; size_t v___x_1391_; size_t v___x_1392_; size_t v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1381_ = lean_array_get_size(v_x_1373_);
v___x_1382_ = lean_string_hash(v_key_1375_);
v___x_1383_ = 32ULL;
v___x_1384_ = lean_uint64_shift_right(v___x_1382_, v___x_1383_);
v_fold_1385_ = lean_uint64_xor(v___x_1382_, v___x_1384_);
v___x_1386_ = 16ULL;
v___x_1387_ = lean_uint64_shift_right(v_fold_1385_, v___x_1386_);
v___x_1388_ = lean_uint64_xor(v_fold_1385_, v___x_1387_);
v___x_1389_ = lean_uint64_to_usize(v___x_1388_);
v___x_1390_ = lean_usize_of_nat(v___x_1381_);
v___x_1391_ = ((size_t)1ULL);
v___x_1392_ = lean_usize_sub(v___x_1390_, v___x_1391_);
v___x_1393_ = lean_usize_land(v___x_1389_, v___x_1392_);
v___x_1394_ = lean_array_uget_borrowed(v_x_1373_, v___x_1393_);
lean_inc(v___x_1394_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 2, v___x_1394_);
v___x_1396_ = v___x_1379_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_key_1375_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_value_1376_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_array_uset(v_x_1373_, v___x_1393_, v___x_1396_);
v_x_1373_ = v___x_1397_;
v_x_1374_ = v_tail_1377_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1401_, lean_object* v_source_1402_, lean_object* v_target_1403_){
_start:
{
lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1404_ = lean_array_get_size(v_source_1402_);
v___x_1405_ = lean_nat_dec_lt(v_i_1401_, v___x_1404_);
if (v___x_1405_ == 0)
{
lean_dec_ref(v_source_1402_);
lean_dec(v_i_1401_);
return v_target_1403_;
}
else
{
lean_object* v_es_1406_; lean_object* v___x_1407_; lean_object* v_source_1408_; lean_object* v_target_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v_es_1406_ = lean_array_fget(v_source_1402_, v_i_1401_);
v___x_1407_ = lean_box(0);
v_source_1408_ = lean_array_fset(v_source_1402_, v_i_1401_, v___x_1407_);
v_target_1409_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1403_, v_es_1406_);
v___x_1410_ = lean_unsigned_to_nat(1u);
v___x_1411_ = lean_nat_add(v_i_1401_, v___x_1410_);
lean_dec(v_i_1401_);
v_i_1401_ = v___x_1411_;
v_source_1402_ = v_source_1408_;
v_target_1403_ = v_target_1409_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(lean_object* v_data_1413_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v_nbuckets_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1414_ = lean_array_get_size(v_data_1413_);
v___x_1415_ = lean_unsigned_to_nat(2u);
v_nbuckets_1416_ = lean_nat_mul(v___x_1414_, v___x_1415_);
v___x_1417_ = lean_unsigned_to_nat(0u);
v___x_1418_ = lean_box(0);
v___x_1419_ = lean_mk_array(v_nbuckets_1416_, v___x_1418_);
v___x_1420_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v___x_1417_, v_data_1413_, v___x_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(lean_object* v_i_1421_, lean_object* v_m_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_size_1424_; lean_object* v_buckets_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1475_; 
v_size_1424_ = lean_ctor_get(v_m_1422_, 0);
v_buckets_1425_ = lean_ctor_get(v_m_1422_, 1);
v_isSharedCheck_1475_ = !lean_is_exclusive(v_m_1422_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1427_ = v_m_1422_;
v_isShared_1428_ = v_isSharedCheck_1475_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_buckets_1425_);
lean_inc(v_size_1424_);
lean_dec(v_m_1422_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1475_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; uint64_t v___x_1430_; uint64_t v___x_1431_; uint64_t v___x_1432_; uint64_t v_fold_1433_; uint64_t v___x_1434_; uint64_t v___x_1435_; uint64_t v___x_1436_; size_t v___x_1437_; size_t v___x_1438_; size_t v___x_1439_; size_t v___x_1440_; size_t v___x_1441_; lean_object* v_bkt_1442_; uint8_t v___x_1443_; 
v___x_1429_ = lean_array_get_size(v_buckets_1425_);
v___x_1430_ = lean_string_hash(v_a_1423_);
v___x_1431_ = 32ULL;
v___x_1432_ = lean_uint64_shift_right(v___x_1430_, v___x_1431_);
v_fold_1433_ = lean_uint64_xor(v___x_1430_, v___x_1432_);
v___x_1434_ = 16ULL;
v___x_1435_ = lean_uint64_shift_right(v_fold_1433_, v___x_1434_);
v___x_1436_ = lean_uint64_xor(v_fold_1433_, v___x_1435_);
v___x_1437_ = lean_uint64_to_usize(v___x_1436_);
v___x_1438_ = lean_usize_of_nat(v___x_1429_);
v___x_1439_ = ((size_t)1ULL);
v___x_1440_ = lean_usize_sub(v___x_1438_, v___x_1439_);
v___x_1441_ = lean_usize_land(v___x_1437_, v___x_1440_);
v_bkt_1442_ = lean_array_uget_borrowed(v_buckets_1425_, v___x_1441_);
v___x_1443_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1423_, v_bkt_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v_size_x27_1447_; lean_object* v___x_1448_; lean_object* v_buckets_x27_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1444_ = lean_unsigned_to_nat(1u);
v___x_1445_ = lean_mk_empty_array_with_capacity(v___x_1444_);
v___x_1446_ = lean_array_push(v___x_1445_, v_i_1421_);
v_size_x27_1447_ = lean_nat_add(v_size_1424_, v___x_1444_);
lean_dec(v_size_1424_);
lean_inc(v_bkt_1442_);
v___x_1448_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1448_, 0, v_a_1423_);
lean_ctor_set(v___x_1448_, 1, v___x_1446_);
lean_ctor_set(v___x_1448_, 2, v_bkt_1442_);
v_buckets_x27_1449_ = lean_array_uset(v_buckets_1425_, v___x_1441_, v___x_1448_);
v___x_1450_ = lean_unsigned_to_nat(4u);
v___x_1451_ = lean_nat_mul(v_size_x27_1447_, v___x_1450_);
v___x_1452_ = lean_unsigned_to_nat(3u);
v___x_1453_ = lean_nat_div(v___x_1451_, v___x_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_array_get_size(v_buckets_x27_1449_);
v___x_1455_ = lean_nat_dec_le(v___x_1453_, v___x_1454_);
lean_dec(v___x_1453_);
if (v___x_1455_ == 0)
{
lean_object* v_val_1456_; lean_object* v___x_1458_; 
v_val_1456_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_buckets_x27_1449_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v_val_1456_);
lean_ctor_set(v___x_1427_, 0, v_size_x27_1447_);
v___x_1458_ = v___x_1427_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_size_x27_1447_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_val_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
else
{
lean_object* v___x_1461_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v_buckets_x27_1449_);
lean_ctor_set(v___x_1427_, 0, v_size_x27_1447_);
v___x_1461_ = v___x_1427_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_size_x27_1447_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_buckets_x27_1449_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
else
{
lean_object* v___x_1463_; lean_object* v_buckets_x27_1464_; lean_object* v_bkt_x27_1465_; lean_object* v___y_1467_; uint8_t v___x_1472_; 
lean_inc(v_bkt_1442_);
v___x_1463_ = lean_box(0);
v_buckets_x27_1464_ = lean_array_uset(v_buckets_1425_, v___x_1441_, v___x_1463_);
lean_inc_ref(v_a_1423_);
v_bkt_x27_1465_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_1421_, v_a_1423_, v_bkt_1442_);
v___x_1472_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1423_, v_bkt_x27_1465_);
lean_dec_ref(v_a_1423_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = lean_unsigned_to_nat(1u);
v___x_1474_ = lean_nat_sub(v_size_1424_, v___x_1473_);
lean_dec(v_size_1424_);
v___y_1467_ = v___x_1474_;
goto v___jp_1466_;
}
else
{
v___y_1467_ = v_size_1424_;
goto v___jp_1466_;
}
v___jp_1466_:
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1468_ = lean_array_uset(v_buckets_x27_1464_, v___x_1441_, v_bkt_x27_1465_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v___x_1468_);
lean_ctor_set(v___x_1427_, 0, v___y_1467_);
v___x_1470_ = v___x_1427_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___y_1467_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header(lean_object* v_builder_1476_, lean_object* v_key_1477_, lean_object* v_value_1478_){
_start:
{
lean_object* v_line_1479_; lean_object* v_headers_1480_; lean_object* v_extensions_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1512_; 
v_line_1479_ = lean_ctor_get(v_builder_1476_, 0);
lean_inc_ref(v_line_1479_);
v_headers_1480_ = lean_ctor_get(v_line_1479_, 1);
lean_inc_ref(v_headers_1480_);
v_extensions_1481_ = lean_ctor_get(v_builder_1476_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_builder_1476_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v_builder_1476_, 0);
lean_dec(v_unused_1513_);
v___x_1483_ = v_builder_1476_;
v_isShared_1484_ = v_isSharedCheck_1512_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_extensions_1481_);
lean_dec(v_builder_1476_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1512_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
uint8_t v_method_1485_; uint8_t v_version_1486_; lean_object* v_uri_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1510_; 
v_method_1485_ = lean_ctor_get_uint8(v_line_1479_, sizeof(void*)*2);
v_version_1486_ = lean_ctor_get_uint8(v_line_1479_, sizeof(void*)*2 + 1);
v_uri_1487_ = lean_ctor_get(v_line_1479_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_line_1479_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v_line_1479_, 1);
lean_dec(v_unused_1511_);
v___x_1489_ = v_line_1479_;
v_isShared_1490_ = v_isSharedCheck_1510_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_uri_1487_);
lean_dec(v_line_1479_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1510_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v_entries_1491_; lean_object* v_indexes_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1509_; 
v_entries_1491_ = lean_ctor_get(v_headers_1480_, 0);
v_indexes_1492_ = lean_ctor_get(v_headers_1480_, 1);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_headers_1480_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1494_ = v_headers_1480_;
v_isShared_1495_ = v_isSharedCheck_1509_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_indexes_1492_);
lean_inc(v_entries_1491_);
lean_dec(v_headers_1480_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1509_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v_i_1496_; lean_object* v___x_1497_; lean_object* v_entries_1498_; lean_object* v_indexes_1499_; lean_object* v___x_1501_; 
v_i_1496_ = lean_array_get_size(v_entries_1491_);
lean_inc_ref(v_key_1477_);
v___x_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1497_, 0, v_key_1477_);
lean_ctor_set(v___x_1497_, 1, v_value_1478_);
v_entries_1498_ = lean_array_push(v_entries_1491_, v___x_1497_);
v_indexes_1499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1496_, v_indexes_1492_, v_key_1477_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v_indexes_1499_);
lean_ctor_set(v___x_1494_, 0, v_entries_1498_);
v___x_1501_ = v___x_1494_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_entries_1498_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_indexes_1499_);
v___x_1501_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1503_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1501_);
v___x_1503_ = v___x_1489_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_uri_1487_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v___x_1501_);
lean_ctor_set_uint8(v_reuseFailAlloc_1507_, sizeof(void*)*2, v_method_1485_);
lean_ctor_set_uint8(v_reuseFailAlloc_1507_, sizeof(void*)*2 + 1, v_version_1486_);
v___x_1503_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1505_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1503_);
v___x_1505_ = v___x_1483_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_extensions_1481_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(lean_object* v_00_u03b2_1514_, lean_object* v_a_1515_, lean_object* v_x_1516_){
_start:
{
uint8_t v___x_1517_; 
v___x_1517_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1515_, v_x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1518_, lean_object* v_a_1519_, lean_object* v_x_1520_){
_start:
{
uint8_t v_res_1521_; lean_object* v_r_1522_; 
v_res_1521_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(v_00_u03b2_1518_, v_a_1519_, v_x_1520_);
lean_dec(v_x_1520_);
lean_dec_ref(v_a_1519_);
v_r_1522_ = lean_box(v_res_1521_);
return v_r_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1(lean_object* v_00_u03b2_1523_, lean_object* v_data_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_data_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1526_, lean_object* v_i_1527_, lean_object* v_source_1528_, lean_object* v_target_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v_i_1527_, v_source_1528_, v_target_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1531_, lean_object* v_x_1532_, lean_object* v_x_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1532_, v_x_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x21(lean_object* v_builder_1535_, lean_object* v_key_1536_, lean_object* v_value_1537_){
_start:
{
lean_object* v_line_1538_; lean_object* v_headers_1539_; lean_object* v_extensions_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1573_; 
v_line_1538_ = lean_ctor_get(v_builder_1535_, 0);
lean_inc_ref(v_line_1538_);
v_headers_1539_ = lean_ctor_get(v_line_1538_, 1);
lean_inc_ref(v_headers_1539_);
v_extensions_1540_ = lean_ctor_get(v_builder_1535_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_builder_1535_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; 
v_unused_1574_ = lean_ctor_get(v_builder_1535_, 0);
lean_dec(v_unused_1574_);
v___x_1542_ = v_builder_1535_;
v_isShared_1543_ = v_isSharedCheck_1573_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_extensions_1540_);
lean_dec(v_builder_1535_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1573_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
uint8_t v_method_1544_; uint8_t v_version_1545_; lean_object* v_uri_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1571_; 
v_method_1544_ = lean_ctor_get_uint8(v_line_1538_, sizeof(void*)*2);
v_version_1545_ = lean_ctor_get_uint8(v_line_1538_, sizeof(void*)*2 + 1);
v_uri_1546_ = lean_ctor_get(v_line_1538_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_line_1538_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v_line_1538_, 1);
lean_dec(v_unused_1572_);
v___x_1548_ = v_line_1538_;
v_isShared_1549_ = v_isSharedCheck_1571_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_uri_1546_);
lean_dec(v_line_1538_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1571_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v_entries_1550_; lean_object* v_indexes_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1570_; 
v_entries_1550_ = lean_ctor_get(v_headers_1539_, 0);
v_indexes_1551_ = lean_ctor_get(v_headers_1539_, 1);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_headers_1539_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1553_ = v_headers_1539_;
v_isShared_1554_ = v_isSharedCheck_1570_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_indexes_1551_);
lean_inc(v_entries_1550_);
lean_dec(v_headers_1539_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1570_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v_key_1555_; lean_object* v_value_1556_; lean_object* v_i_1557_; lean_object* v___x_1558_; lean_object* v_entries_1559_; lean_object* v_indexes_1560_; lean_object* v___x_1562_; 
v_key_1555_ = l_Std_Http_Header_Name_ofString_x21(v_key_1536_);
v_value_1556_ = l_Std_Http_Header_Value_ofString_x21(v_value_1537_);
v_i_1557_ = lean_array_get_size(v_entries_1550_);
lean_inc_ref(v_key_1555_);
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v_key_1555_);
lean_ctor_set(v___x_1558_, 1, v_value_1556_);
v_entries_1559_ = lean_array_push(v_entries_1550_, v___x_1558_);
v_indexes_1560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1557_, v_indexes_1551_, v_key_1555_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 1, v_indexes_1560_);
lean_ctor_set(v___x_1553_, 0, v_entries_1559_);
v___x_1562_ = v___x_1553_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_entries_1559_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_indexes_1560_);
v___x_1562_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1564_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 1, v___x_1562_);
v___x_1564_ = v___x_1548_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_uri_1546_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v___x_1562_);
lean_ctor_set_uint8(v_reuseFailAlloc_1568_, sizeof(void*)*2, v_method_1544_);
lean_ctor_set_uint8(v_reuseFailAlloc_1568_, sizeof(void*)*2 + 1, v_version_1545_);
v___x_1564_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1566_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1564_);
v___x_1566_ = v___x_1542_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_extensions_1540_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x3f(lean_object* v_builder_1575_, lean_object* v_key_1576_, lean_object* v_value_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Std_Http_Header_Name_ofString_x3f(v_key_1576_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v___x_1579_; 
lean_dec_ref(v_value_1577_);
lean_dec_ref(v_builder_1575_);
v___x_1579_ = lean_box(0);
return v___x_1579_;
}
else
{
lean_object* v_val_1580_; lean_object* v___x_1581_; 
v_val_1580_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_val_1580_);
lean_dec_ref(v___x_1578_);
v___x_1581_ = l_Std_Http_Header_Value_ofString_x3f(v_value_1577_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v___x_1582_; 
lean_dec(v_val_1580_);
lean_dec_ref(v_builder_1575_);
v___x_1582_ = lean_box(0);
return v___x_1582_;
}
else
{
lean_object* v_line_1583_; lean_object* v_headers_1584_; lean_object* v_val_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1625_; 
v_line_1583_ = lean_ctor_get(v_builder_1575_, 0);
lean_inc_ref(v_line_1583_);
v_headers_1584_ = lean_ctor_get(v_line_1583_, 1);
lean_inc_ref(v_headers_1584_);
v_val_1585_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1587_ = v___x_1581_;
v_isShared_1588_ = v_isSharedCheck_1625_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_val_1585_);
lean_dec(v___x_1581_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1625_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v_extensions_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1623_; 
v_extensions_1589_ = lean_ctor_get(v_builder_1575_, 1);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_builder_1575_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; 
v_unused_1624_ = lean_ctor_get(v_builder_1575_, 0);
lean_dec(v_unused_1624_);
v___x_1591_ = v_builder_1575_;
v_isShared_1592_ = v_isSharedCheck_1623_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_extensions_1589_);
lean_dec(v_builder_1575_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1623_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
uint8_t v_method_1593_; uint8_t v_version_1594_; lean_object* v_uri_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1621_; 
v_method_1593_ = lean_ctor_get_uint8(v_line_1583_, sizeof(void*)*2);
v_version_1594_ = lean_ctor_get_uint8(v_line_1583_, sizeof(void*)*2 + 1);
v_uri_1595_ = lean_ctor_get(v_line_1583_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_line_1583_);
if (v_isSharedCheck_1621_ == 0)
{
lean_object* v_unused_1622_; 
v_unused_1622_ = lean_ctor_get(v_line_1583_, 1);
lean_dec(v_unused_1622_);
v___x_1597_ = v_line_1583_;
v_isShared_1598_ = v_isSharedCheck_1621_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_uri_1595_);
lean_dec(v_line_1583_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1621_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v_entries_1599_; lean_object* v_indexes_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1620_; 
v_entries_1599_ = lean_ctor_get(v_headers_1584_, 0);
v_indexes_1600_ = lean_ctor_get(v_headers_1584_, 1);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_headers_1584_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1602_ = v_headers_1584_;
v_isShared_1603_ = v_isSharedCheck_1620_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_indexes_1600_);
lean_inc(v_entries_1599_);
lean_dec(v_headers_1584_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1620_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v_i_1604_; lean_object* v___x_1605_; lean_object* v_entries_1606_; lean_object* v_indexes_1607_; lean_object* v___x_1609_; 
v_i_1604_ = lean_array_get_size(v_entries_1599_);
lean_inc(v_val_1580_);
v___x_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1605_, 0, v_val_1580_);
lean_ctor_set(v___x_1605_, 1, v_val_1585_);
v_entries_1606_ = lean_array_push(v_entries_1599_, v___x_1605_);
v_indexes_1607_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1604_, v_indexes_1600_, v_val_1580_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 1, v_indexes_1607_);
lean_ctor_set(v___x_1602_, 0, v_entries_1606_);
v___x_1609_ = v___x_1602_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_entries_1606_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_indexes_1607_);
v___x_1609_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 1, v___x_1609_);
v___x_1611_ = v___x_1597_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_uri_1595_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v___x_1609_);
lean_ctor_set_uint8(v_reuseFailAlloc_1618_, sizeof(void*)*2, v_method_1593_);
lean_ctor_set_uint8(v_reuseFailAlloc_1618_, sizeof(void*)*2 + 1, v_version_1594_);
v___x_1611_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1613_; 
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1611_);
v___x_1613_ = v___x_1591_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_extensions_1589_);
v___x_1613_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1615_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1613_);
v___x_1615_ = v___x_1587_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
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
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headerOpt(lean_object* v_builder_1626_, lean_object* v_key_1627_, lean_object* v_value_1628_){
_start:
{
if (lean_obj_tag(v_value_1628_) == 0)
{
lean_dec_ref(v_key_1627_);
return v_builder_1626_;
}
else
{
lean_object* v_val_1629_; lean_object* v___x_1630_; 
v_val_1629_ = lean_ctor_get(v_value_1628_, 0);
lean_inc(v_val_1629_);
lean_dec_ref(v_value_1628_);
v___x_1630_ = l_Std_Http_Request_Builder_header(v_builder_1626_, v_key_1627_, v_val_1629_);
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension___redArg(lean_object* v_builder_1632_, lean_object* v_inst_1633_, lean_object* v_data_1634_){
_start:
{
lean_object* v_line_1635_; lean_object* v_extensions_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1647_; 
v_line_1635_ = lean_ctor_get(v_builder_1632_, 0);
v_extensions_1636_ = lean_ctor_get(v_builder_1632_, 1);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_builder_1632_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1638_ = v_builder_1632_;
v_isShared_1639_ = v_isSharedCheck_1647_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_extensions_1636_);
lean_inc(v_line_1635_);
lean_dec(v_builder_1632_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1647_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v_dyn_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1645_; 
v_dyn_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_1640_, 0, v_inst_1633_);
lean_ctor_set(v_dyn_1640_, 1, v_data_1634_);
v___x_1641_ = ((lean_object*)(l_Std_Http_Request_Builder_extension___redArg___closed__0));
v___x_1642_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_1640_);
v___x_1643_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1641_, v___x_1642_, v_dyn_1640_, v_extensions_1636_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 1, v___x_1643_);
v___x_1645_ = v___x_1638_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_line_1635_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension(lean_object* v_00_u03b1_1648_, lean_object* v_builder_1649_, lean_object* v_inst_1650_, lean_object* v_data_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Std_Http_Request_Builder_extension___redArg(v_builder_1649_, v_inst_1650_, v_data_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object* v_builder_1653_, lean_object* v_body_1654_){
_start:
{
lean_object* v_line_1655_; lean_object* v_extensions_1656_; lean_object* v___x_1657_; 
v_line_1655_ = lean_ctor_get(v_builder_1653_, 0);
v_extensions_1656_ = lean_ctor_get(v_builder_1653_, 1);
lean_inc(v_extensions_1656_);
lean_inc_ref(v_line_1655_);
v___x_1657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1657_, 0, v_line_1655_);
lean_ctor_set(v___x_1657_, 1, v_body_1654_);
lean_ctor_set(v___x_1657_, 2, v_extensions_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg___boxed(lean_object* v_builder_1658_, lean_object* v_body_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1658_, v_body_1659_);
lean_dec_ref(v_builder_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body(lean_object* v_t_1661_, lean_object* v_builder_1662_, lean_object* v_body_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1662_, v_body_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___boxed(lean_object* v_t_1665_, lean_object* v_builder_1666_, lean_object* v_body_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Std_Http_Request_Builder_body(v_t_1665_, v_builder_1666_, v_body_1667_);
lean_dec_ref(v_builder_1666_);
return v_res_1668_;
}
}
static lean_object* _init_l_Std_Http_Request_get___closed__0(void){
_start:
{
uint8_t v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = 8;
v___x_1670_ = l_Std_Http_Request_new;
v___x_1671_ = l_Std_Http_Request_Builder_method(v___x_1670_, v___x_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_get(lean_object* v_uri_1672_){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_obj_once(&l_Std_Http_Request_get___closed__0, &l_Std_Http_Request_get___closed__0_once, _init_l_Std_Http_Request_get___closed__0);
v___x_1674_ = l_Std_Http_Request_Builder_uri(v___x_1673_, v_uri_1672_);
return v___x_1674_;
}
}
static lean_object* _init_l_Std_Http_Request_post___closed__0(void){
_start:
{
uint8_t v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = 23;
v___x_1676_ = l_Std_Http_Request_new;
v___x_1677_ = l_Std_Http_Request_Builder_method(v___x_1676_, v___x_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_post(lean_object* v_uri_1678_){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_obj_once(&l_Std_Http_Request_post___closed__0, &l_Std_Http_Request_post___closed__0_once, _init_l_Std_Http_Request_post___closed__0);
v___x_1680_ = l_Std_Http_Request_Builder_uri(v___x_1679_, v_uri_1678_);
return v___x_1680_;
}
}
static lean_object* _init_l_Std_Http_Request_put___closed__0(void){
_start:
{
uint8_t v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = 27;
v___x_1682_ = l_Std_Http_Request_new;
v___x_1683_ = l_Std_Http_Request_Builder_method(v___x_1682_, v___x_1681_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_put(lean_object* v_uri_1684_){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = lean_obj_once(&l_Std_Http_Request_put___closed__0, &l_Std_Http_Request_put___closed__0_once, _init_l_Std_Http_Request_put___closed__0);
v___x_1686_ = l_Std_Http_Request_Builder_uri(v___x_1685_, v_uri_1684_);
return v___x_1686_;
}
}
static lean_object* _init_l_Std_Http_Request_delete___closed__0(void){
_start:
{
uint8_t v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = 7;
v___x_1688_ = l_Std_Http_Request_new;
v___x_1689_ = l_Std_Http_Request_Builder_method(v___x_1688_, v___x_1687_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_delete(lean_object* v_uri_1690_){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_obj_once(&l_Std_Http_Request_delete___closed__0, &l_Std_Http_Request_delete___closed__0_once, _init_l_Std_Http_Request_delete___closed__0);
v___x_1692_ = l_Std_Http_Request_Builder_uri(v___x_1691_, v_uri_1690_);
return v___x_1692_;
}
}
static lean_object* _init_l_Std_Http_Request_patch___closed__0(void){
_start:
{
uint8_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = 22;
v___x_1694_ = l_Std_Http_Request_new;
v___x_1695_ = l_Std_Http_Request_Builder_method(v___x_1694_, v___x_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_patch(lean_object* v_uri_1696_){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = lean_obj_once(&l_Std_Http_Request_patch___closed__0, &l_Std_Http_Request_patch___closed__0_once, _init_l_Std_Http_Request_patch___closed__0);
v___x_1698_ = l_Std_Http_Request_Builder_uri(v___x_1697_, v_uri_1696_);
return v___x_1698_;
}
}
static lean_object* _init_l_Std_Http_Request_head___closed__0(void){
_start:
{
uint8_t v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1699_ = 9;
v___x_1700_ = l_Std_Http_Request_new;
v___x_1701_ = l_Std_Http_Request_Builder_method(v___x_1700_, v___x_1699_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_head(lean_object* v_uri_1702_){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = lean_obj_once(&l_Std_Http_Request_head___closed__0, &l_Std_Http_Request_head___closed__0_once, _init_l_Std_Http_Request_head___closed__0);
v___x_1704_ = l_Std_Http_Request_Builder_uri(v___x_1703_, v_uri_1702_);
return v___x_1704_;
}
}
static lean_object* _init_l_Std_Http_Request_options___closed__0(void){
_start:
{
uint8_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = 20;
v___x_1706_ = l_Std_Http_Request_new;
v___x_1707_ = l_Std_Http_Request_Builder_method(v___x_1706_, v___x_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_options(lean_object* v_uri_1708_){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_obj_once(&l_Std_Http_Request_options___closed__0, &l_Std_Http_Request_options___closed__0_once, _init_l_Std_Http_Request_options___closed__0);
v___x_1710_ = l_Std_Http_Request_Builder_uri(v___x_1709_, v_uri_1708_);
return v___x_1710_;
}
}
static lean_object* _init_l_Std_Http_Request_connect___closed__0(void){
_start:
{
uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = 5;
v___x_1712_ = l_Std_Http_Request_new;
v___x_1713_ = l_Std_Http_Request_Builder_method(v___x_1712_, v___x_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_connect(lean_object* v_uri_1714_){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = lean_obj_once(&l_Std_Http_Request_connect___closed__0, &l_Std_Http_Request_connect___closed__0_once, _init_l_Std_Http_Request_connect___closed__0);
v___x_1716_ = l_Std_Http_Request_Builder_uri(v___x_1715_, v_uri_1714_);
return v___x_1716_;
}
}
static lean_object* _init_l_Std_Http_Request_trace___closed__0(void){
_start:
{
uint8_t v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = 32;
v___x_1718_ = l_Std_Http_Request_new;
v___x_1719_ = l_Std_Http_Request_Builder_method(v___x_1718_, v___x_1717_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_trace(lean_object* v_uri_1720_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = lean_obj_once(&l_Std_Http_Request_trace___closed__0, &l_Std_Http_Request_trace___closed__0_once, _init_l_Std_Http_Request_trace___closed__0);
v___x_1722_ = l_Std_Http_Request_Builder_uri(v___x_1721_, v_uri_1720_);
return v___x_1722_;
}
}
lean_object* runtime_initialize_Std_Http_Data_Extensions(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Method(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Version(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Headers(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_URI(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Request(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Http_Data_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Method(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_URI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Request_instInhabitedHead_default = _init_l_Std_Http_Request_instInhabitedHead_default();
lean_mark_persistent(l_Std_Http_Request_instInhabitedHead_default);
l_Std_Http_Request_instInhabitedHead = _init_l_Std_Http_Request_instInhabitedHead();
lean_mark_persistent(l_Std_Http_Request_instInhabitedHead);
l_Std_Http_Request_instToStringHead___lam__3___boxed__const__1 = _init_l_Std_Http_Request_instToStringHead___lam__3___boxed__const__1();
lean_mark_persistent(l_Std_Http_Request_instToStringHead___lam__3___boxed__const__1);
l_Std_Http_Request_new = _init_l_Std_Http_Request_new();
lean_mark_persistent(l_Std_Http_Request_new);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_Request(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Http_Data_Extensions(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Method(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Version(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Headers(uint8_t builtin);
lean_object* initialize_Std_Http_Data_URI(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_Request(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Http_Data_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Method(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_URI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_Request(builtin);
}
#ifdef __cplusplus
}
#endif
