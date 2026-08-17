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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_Http_URI_Query_formatOption(lean_object*);
lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_get_size(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__0_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__1 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__1_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__2 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__2_value;
static lean_once_cell_t l_Std_Http_Request_instToStringHead___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__3;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__4 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1;
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2(lean_object*);
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__0 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__0_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__1 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__1_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__2 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__2_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__3 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__3_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__4 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__4_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__5 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__5_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__6 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__6_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__7 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__7_value;
static const lean_ctor_object l_Std_Http_Request_instToStringHead___lam__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__1_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__2_value)}};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__8 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__8_value;
static const lean_ctor_object l_Std_Http_Request_instToStringHead___lam__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__8_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__3_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__4_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__5_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__6_value)}};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__9 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__9_value;
static const lean_ctor_object l_Std_Http_Request_instToStringHead___lam__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__9_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__7_value)}};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__10 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__10_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.0"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__11 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__11_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.1"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__12 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__12_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/2.0"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__13 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__13_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/3.0"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__14 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__14_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__15 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__15_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__16 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__16_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__17 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__17_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__18 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__18_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__19 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__19_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__20 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__20_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "//"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__21 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__21_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__22 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__22_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__23 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__23_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ACL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__24 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__24_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BASELINE-CONTROL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__25 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__25_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "BIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__26 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__26_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CHECKIN"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__27 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__27_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CHECKOUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__28 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__28_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CONNECT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__29 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__29_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COPY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__30 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__30_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DELETE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__31 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__31_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__32 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__32_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__33 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__33_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "LABEL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__34 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__34_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LINK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__35 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__35_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LOCK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__36 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__36_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MERGE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__37 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__37_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKACTIVITY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__38 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__38_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKCALENDAR"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__39 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__39_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MKCOL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__40 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__40_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MKREDIRECTREF"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__41 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__41_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MKWORKSPACE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__42 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__42_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MOVE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__43 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__43_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__44 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__44_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ORDERPATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__45 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__45_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__46 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__46_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__47 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__47_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRI"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__48 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__48_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PROPFIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__49 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__49_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PROPPATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__50 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__50_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__51 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__51_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "QUERY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__52 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__52_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REBIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__53 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__53_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REPORT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__54 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__54_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SEARCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__55 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__55_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TRACE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__56 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__56_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNBIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__57 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__57_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UNCHECKOUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__58 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__58_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLINK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__59 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__59_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLOCK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__60 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__60_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UPDATE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__61 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__61_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UPDATEREDIRECTREF"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__62 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__62_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__4___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "VERSION-CONTROL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__4___closed__63 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__4___closed__63_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__0 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__1 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__1_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__4, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___closed__1_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value)} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__2 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Http_Request_instToStringHead = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3___closed__4;
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Request_instEncodeV11Head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instEncodeV11Head___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instEncodeV11Head___closed__0 = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__0_value;
static const lean_closure_object l_Std_Http_Request_instEncodeV11Head___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instEncodeV11Head___lam__3, .m_arity = 5, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__0_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value)} };
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
lean_object* v___x_123_; 
v___x_123_ = lean_string_from_utf8_unchecked(v_x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__1(lean_object* v___x_124_, lean_object* v___x_125_, lean_object* v___x_126_, lean_object* v_fst_127_, lean_object* v___x_128_, uint32_t v___x_129_, lean_object* v___x_130_, lean_object* v_it_131_, lean_object* v_acc_132_, lean_object* v_hP_133_, lean_object* v_recur_134_){
_start:
{
lean_object* v_it_136_; lean_object* v_out_137_; lean_object* v_it_153_; lean_object* v_startInclusive_154_; lean_object* v_endExclusive_155_; 
if (lean_obj_tag(v_it_131_) == 0)
{
lean_object* v_currPos_167_; lean_object* v_searcher_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_190_; 
v_currPos_167_ = lean_ctor_get(v_it_131_, 0);
v_searcher_168_ = lean_ctor_get(v_it_131_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v_it_131_);
if (v_isSharedCheck_190_ == 0)
{
v___x_170_ = v_it_131_;
v_isShared_171_ = v_isSharedCheck_190_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_searcher_168_);
lean_inc(v_currPos_167_);
lean_dec(v_it_131_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_190_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
uint8_t v___x_172_; 
v___x_172_ = lean_nat_dec_eq(v_searcher_168_, v___x_128_);
if (v___x_172_ == 0)
{
uint32_t v___x_173_; uint8_t v___x_174_; 
lean_dec(v___x_128_);
v___x_173_ = lean_string_utf8_get_fast(v_fst_127_, v_searcher_168_);
v___x_174_ = lean_uint32_dec_eq(v___x_173_, v___x_129_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = lean_string_utf8_next_fast(v_fst_127_, v_searcher_168_);
lean_dec(v_searcher_168_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v___x_175_);
v___x_177_ = v___x_170_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_currPos_167_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v___x_175_);
v___x_177_ = v_reuseFailAlloc_179_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; 
v___x_178_ = lean_apply_4(v_recur_134_, v___x_177_, v_acc_132_, lean_box(0), lean_box(0));
return v___x_178_;
}
}
else
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v_slice_183_; lean_object* v_nextIt_185_; 
v___x_180_ = lean_string_utf8_next_fast(v_fst_127_, v_searcher_168_);
v___x_181_ = lean_nat_sub(v___x_180_, v_searcher_168_);
v___x_182_ = lean_nat_add(v_searcher_168_, v___x_181_);
lean_dec(v___x_181_);
v_slice_183_ = l_String_Slice_subslice_x21(v___x_130_, v_currPos_167_, v_searcher_168_);
lean_inc(v___x_182_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v___x_182_);
lean_ctor_set(v___x_170_, 0, v___x_182_);
v_nextIt_185_ = v___x_170_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_182_);
v_nextIt_185_ = v_reuseFailAlloc_188_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v_startInclusive_186_; lean_object* v_endExclusive_187_; 
v_startInclusive_186_ = lean_ctor_get(v_slice_183_, 0);
lean_inc(v_startInclusive_186_);
v_endExclusive_187_ = lean_ctor_get(v_slice_183_, 1);
lean_inc(v_endExclusive_187_);
lean_dec_ref(v_slice_183_);
v_it_153_ = v_nextIt_185_;
v_startInclusive_154_ = v_startInclusive_186_;
v_endExclusive_155_ = v_endExclusive_187_;
goto v___jp_152_;
}
}
}
else
{
lean_object* v___x_189_; 
lean_del_object(v___x_170_);
lean_dec(v_searcher_168_);
v___x_189_ = lean_box(1);
v_it_153_ = v___x_189_;
v_startInclusive_154_ = v_currPos_167_;
v_endExclusive_155_ = v___x_128_;
goto v___jp_152_;
}
}
}
else
{
lean_dec_ref(v_recur_134_);
lean_dec(v___x_128_);
return v_acc_132_;
}
v___jp_135_:
{
if (lean_obj_tag(v_acc_132_) == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_138_, 0, v_out_137_);
v___x_139_ = lean_apply_4(v_recur_134_, v_it_136_, v___x_138_, lean_box(0), lean_box(0));
return v___x_139_;
}
else
{
lean_object* v_val_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_151_; 
v_val_140_ = lean_ctor_get(v_acc_132_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v_acc_132_);
if (v_isSharedCheck_151_ == 0)
{
v___x_142_ = v_acc_132_;
v_isShared_143_ = v_isSharedCheck_151_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_val_140_);
lean_dec(v_acc_132_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_151_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_144_ = lean_string_utf8_extract_fast(v___x_124_, v___x_125_, v___x_126_);
v___x_145_ = lean_string_append(v_val_140_, v___x_144_);
lean_dec_ref(v___x_144_);
v___x_146_ = lean_string_append(v___x_145_, v_out_137_);
lean_dec_ref(v_out_137_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_146_);
v___x_148_ = v___x_142_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_146_);
v___x_148_ = v_reuseFailAlloc_150_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; 
v___x_149_ = lean_apply_4(v_recur_134_, v_it_136_, v___x_148_, lean_box(0), lean_box(0));
return v___x_149_;
}
}
}
}
v___jp_152_:
{
lean_object* v___x_156_; uint32_t v___x_157_; uint32_t v___x_158_; uint8_t v___x_159_; 
v___x_156_ = lean_string_utf8_extract_fast(v_fst_127_, v_startInclusive_154_, v_endExclusive_155_);
lean_dec(v_endExclusive_155_);
lean_dec(v_startInclusive_154_);
v___x_157_ = lean_string_utf8_get(v___x_156_, v___x_125_);
v___x_158_ = 97;
v___x_159_ = lean_uint32_dec_le(v___x_158_, v___x_157_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
v___x_160_ = lean_string_utf8_set(v___x_156_, v___x_125_, v___x_157_);
v_it_136_ = v_it_153_;
v_out_137_ = v___x_160_;
goto v___jp_135_;
}
else
{
uint32_t v___x_161_; uint8_t v___x_162_; 
v___x_161_ = 122;
v___x_162_ = lean_uint32_dec_le(v___x_157_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
v___x_163_ = lean_string_utf8_set(v___x_156_, v___x_125_, v___x_157_);
v_it_136_ = v_it_153_;
v_out_137_ = v___x_163_;
goto v___jp_135_;
}
else
{
uint32_t v___x_164_; uint32_t v___x_165_; lean_object* v___x_166_; 
v___x_164_ = 4294967264;
v___x_165_ = lean_uint32_add(v___x_157_, v___x_164_);
v___x_166_ = lean_string_utf8_set(v___x_156_, v___x_125_, v___x_165_);
v_it_136_ = v_it_153_;
v_out_137_ = v___x_166_;
goto v___jp_135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__1___boxed(lean_object* v___x_191_, lean_object* v___x_192_, lean_object* v___x_193_, lean_object* v_fst_194_, lean_object* v___x_195_, lean_object* v___x_196_, lean_object* v___x_197_, lean_object* v_it_198_, lean_object* v_acc_199_, lean_object* v_hP_200_, lean_object* v_recur_201_){
_start:
{
uint32_t v___x_1497__boxed_202_; lean_object* v_res_203_; 
v___x_1497__boxed_202_ = lean_unbox_uint32(v___x_196_);
lean_dec(v___x_196_);
v_res_203_ = l_Std_Http_Request_instToStringHead___lam__1(v___x_191_, v___x_192_, v___x_193_, v_fst_194_, v___x_195_, v___x_1497__boxed_202_, v___x_197_, v_it_198_, v_acc_199_, v_hP_200_, v_recur_201_);
lean_dec_ref(v___x_197_);
lean_dec_ref(v_fst_194_);
lean_dec(v___x_193_);
lean_dec(v___x_192_);
lean_dec_ref(v___x_191_);
return v_res_203_;
}
}
static lean_object* _init_l_Std_Http_Request_instToStringHead___lam__2___closed__3(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__2));
v___x_208_ = lean_string_utf8_byte_size(v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1(void){
_start:
{
uint32_t v___x_210_; lean_object* v___x_211_; 
v___x_210_ = 45;
v___x_211_ = lean_box_uint32(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2(lean_object* v_x_212_){
_start:
{
lean_object* v_fst_213_; lean_object* v_snd_214_; lean_object* v___y_216_; lean_object* v___f_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_it_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___f_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_fst_213_ = lean_ctor_get(v_x_212_, 0);
lean_inc_n(v_fst_213_, 2);
v_snd_214_ = lean_ctor_get(v_x_212_, 1);
lean_inc(v_snd_214_);
lean_dec_ref(v_x_212_);
v___f_220_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__1));
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_string_utf8_byte_size(v_fst_213_);
v___x_223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_223_, 0, v_fst_213_);
lean_ctor_set(v___x_223_, 1, v___x_221_);
lean_ctor_set(v___x_223_, 2, v___x_222_);
lean_inc_ref(v___x_223_);
v_it_224_ = l_String_Slice_splitToSubslice___redArg(v___x_223_, v___f_220_);
v___x_225_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__2));
v___x_226_ = lean_obj_once(&l_Std_Http_Request_instToStringHead___lam__2___closed__3, &l_Std_Http_Request_instToStringHead___lam__2___closed__3_once, _init_l_Std_Http_Request_instToStringHead___lam__2___closed__3);
v___x_227_ = l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1;
v___f_228_ = lean_alloc_closure((void*)(l_Std_Http_Request_instToStringHead___lam__1___boxed), 11, 7);
lean_closure_set(v___f_228_, 0, v___x_225_);
lean_closure_set(v___f_228_, 1, v___x_221_);
lean_closure_set(v___f_228_, 2, v___x_226_);
lean_closure_set(v___f_228_, 3, v_fst_213_);
lean_closure_set(v___f_228_, 4, v___x_222_);
lean_closure_set(v___f_228_, 5, v___x_227_);
lean_closure_set(v___f_228_, 6, v___x_223_);
v___x_229_ = lean_box(0);
v___x_230_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_228_, v_it_224_, v___x_229_, lean_box(0));
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v___x_231_; 
v___x_231_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_216_ = v___x_231_;
goto v___jp_215_;
}
else
{
lean_object* v_val_232_; 
v_val_232_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_val_232_);
lean_dec_ref_known(v___x_230_, 1);
v___y_216_ = v_val_232_;
goto v___jp_215_;
}
v___jp_215_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__0));
v___x_218_ = lean_string_append(v___y_216_, v___x_217_);
v___x_219_ = lean_string_append(v___x_218_, v_snd_214_);
lean_dec(v_snd_214_);
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__4(lean_object* v___f_306_, lean_object* v___f_307_, lean_object* v___f_308_, lean_object* v_req_309_){
_start:
{
uint8_t v_method_310_; uint8_t v_version_311_; lean_object* v_uri_312_; lean_object* v_headers_313_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v_port_416_; lean_object* v___y_417_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v_host_433_; lean_object* v_port_434_; lean_object* v___y_435_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v_port_457_; lean_object* v___y_458_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v_host_469_; lean_object* v_port_470_; lean_object* v___y_471_; lean_object* v___y_482_; 
v_method_310_ = lean_ctor_get_uint8(v_req_309_, sizeof(void*)*2);
v_version_311_ = lean_ctor_get_uint8(v_req_309_, sizeof(void*)*2 + 1);
v_uri_312_ = lean_ctor_get(v_req_309_, 0);
lean_inc(v_uri_312_);
v_headers_313_ = lean_ctor_get(v_req_309_, 1);
lean_inc_ref(v_headers_313_);
lean_dec_ref(v_req_309_);
switch(v_method_310_)
{
case 0:
{
lean_object* v___x_554_; 
v___x_554_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__24));
v___y_482_ = v___x_554_;
goto v___jp_481_;
}
case 1:
{
lean_object* v___x_555_; 
v___x_555_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__25));
v___y_482_ = v___x_555_;
goto v___jp_481_;
}
case 2:
{
lean_object* v___x_556_; 
v___x_556_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__26));
v___y_482_ = v___x_556_;
goto v___jp_481_;
}
case 3:
{
lean_object* v___x_557_; 
v___x_557_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__27));
v___y_482_ = v___x_557_;
goto v___jp_481_;
}
case 4:
{
lean_object* v___x_558_; 
v___x_558_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__28));
v___y_482_ = v___x_558_;
goto v___jp_481_;
}
case 5:
{
lean_object* v___x_559_; 
v___x_559_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__29));
v___y_482_ = v___x_559_;
goto v___jp_481_;
}
case 6:
{
lean_object* v___x_560_; 
v___x_560_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__30));
v___y_482_ = v___x_560_;
goto v___jp_481_;
}
case 7:
{
lean_object* v___x_561_; 
v___x_561_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__31));
v___y_482_ = v___x_561_;
goto v___jp_481_;
}
case 8:
{
lean_object* v___x_562_; 
v___x_562_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__32));
v___y_482_ = v___x_562_;
goto v___jp_481_;
}
case 9:
{
lean_object* v___x_563_; 
v___x_563_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__33));
v___y_482_ = v___x_563_;
goto v___jp_481_;
}
case 10:
{
lean_object* v___x_564_; 
v___x_564_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__34));
v___y_482_ = v___x_564_;
goto v___jp_481_;
}
case 11:
{
lean_object* v___x_565_; 
v___x_565_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__35));
v___y_482_ = v___x_565_;
goto v___jp_481_;
}
case 12:
{
lean_object* v___x_566_; 
v___x_566_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__36));
v___y_482_ = v___x_566_;
goto v___jp_481_;
}
case 13:
{
lean_object* v___x_567_; 
v___x_567_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__37));
v___y_482_ = v___x_567_;
goto v___jp_481_;
}
case 14:
{
lean_object* v___x_568_; 
v___x_568_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__38));
v___y_482_ = v___x_568_;
goto v___jp_481_;
}
case 15:
{
lean_object* v___x_569_; 
v___x_569_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__39));
v___y_482_ = v___x_569_;
goto v___jp_481_;
}
case 16:
{
lean_object* v___x_570_; 
v___x_570_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__40));
v___y_482_ = v___x_570_;
goto v___jp_481_;
}
case 17:
{
lean_object* v___x_571_; 
v___x_571_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__41));
v___y_482_ = v___x_571_;
goto v___jp_481_;
}
case 18:
{
lean_object* v___x_572_; 
v___x_572_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__42));
v___y_482_ = v___x_572_;
goto v___jp_481_;
}
case 19:
{
lean_object* v___x_573_; 
v___x_573_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__43));
v___y_482_ = v___x_573_;
goto v___jp_481_;
}
case 20:
{
lean_object* v___x_574_; 
v___x_574_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__44));
v___y_482_ = v___x_574_;
goto v___jp_481_;
}
case 21:
{
lean_object* v___x_575_; 
v___x_575_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__45));
v___y_482_ = v___x_575_;
goto v___jp_481_;
}
case 22:
{
lean_object* v___x_576_; 
v___x_576_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__46));
v___y_482_ = v___x_576_;
goto v___jp_481_;
}
case 23:
{
lean_object* v___x_577_; 
v___x_577_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__47));
v___y_482_ = v___x_577_;
goto v___jp_481_;
}
case 24:
{
lean_object* v___x_578_; 
v___x_578_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__48));
v___y_482_ = v___x_578_;
goto v___jp_481_;
}
case 25:
{
lean_object* v___x_579_; 
v___x_579_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__49));
v___y_482_ = v___x_579_;
goto v___jp_481_;
}
case 26:
{
lean_object* v___x_580_; 
v___x_580_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__50));
v___y_482_ = v___x_580_;
goto v___jp_481_;
}
case 27:
{
lean_object* v___x_581_; 
v___x_581_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__51));
v___y_482_ = v___x_581_;
goto v___jp_481_;
}
case 28:
{
lean_object* v___x_582_; 
v___x_582_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__52));
v___y_482_ = v___x_582_;
goto v___jp_481_;
}
case 29:
{
lean_object* v___x_583_; 
v___x_583_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__53));
v___y_482_ = v___x_583_;
goto v___jp_481_;
}
case 30:
{
lean_object* v___x_584_; 
v___x_584_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__54));
v___y_482_ = v___x_584_;
goto v___jp_481_;
}
case 31:
{
lean_object* v___x_585_; 
v___x_585_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__55));
v___y_482_ = v___x_585_;
goto v___jp_481_;
}
case 32:
{
lean_object* v___x_586_; 
v___x_586_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__56));
v___y_482_ = v___x_586_;
goto v___jp_481_;
}
case 33:
{
lean_object* v___x_587_; 
v___x_587_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__57));
v___y_482_ = v___x_587_;
goto v___jp_481_;
}
case 34:
{
lean_object* v___x_588_; 
v___x_588_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__58));
v___y_482_ = v___x_588_;
goto v___jp_481_;
}
case 35:
{
lean_object* v___x_589_; 
v___x_589_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__59));
v___y_482_ = v___x_589_;
goto v___jp_481_;
}
case 36:
{
lean_object* v___x_590_; 
v___x_590_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__60));
v___y_482_ = v___x_590_;
goto v___jp_481_;
}
case 37:
{
lean_object* v___x_591_; 
v___x_591_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__61));
v___y_482_ = v___x_591_;
goto v___jp_481_;
}
case 38:
{
lean_object* v___x_592_; 
v___x_592_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__62));
v___y_482_ = v___x_592_;
goto v___jp_481_;
}
default: 
{
lean_object* v___x_593_; 
v___x_593_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__63));
v___y_482_ = v___x_593_;
goto v___jp_481_;
}
}
v___jp_314_:
{
lean_object* v_entries_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; size_t v_sz_322_; size_t v___x_323_; lean_object* v_pairs_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_entries_317_ = lean_ctor_get(v_headers_313_, 0);
lean_inc_ref(v_entries_317_);
lean_dec_ref(v_headers_313_);
v___x_318_ = lean_string_append(v___y_315_, v___y_316_);
v___x_319_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__0));
v___x_320_ = lean_string_append(v___x_318_, v___x_319_);
v___x_321_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_322_ = lean_array_size(v_entries_317_);
v___x_323_ = ((size_t)0ULL);
v_pairs_324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_321_, v___f_306_, v_sz_322_, v___x_323_, v_entries_317_);
v___x_325_ = lean_array_to_list(v_pairs_324_);
v___x_326_ = l_String_intercalate(v___x_319_, v___x_325_);
v___x_327_ = lean_string_append(v___x_320_, v___x_326_);
lean_dec_ref(v___x_326_);
v___x_328_ = lean_string_append(v___x_327_, v___x_319_);
return v___x_328_;
}
v___jp_329_:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_string_append(v___y_330_, v___y_332_);
lean_dec_ref(v___y_332_);
v___x_334_ = lean_string_append(v___x_333_, v___y_331_);
switch(v_version_311_)
{
case 0:
{
lean_object* v___x_335_; 
v___x_335_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__11));
v___y_315_ = v___x_334_;
v___y_316_ = v___x_335_;
goto v___jp_314_;
}
case 1:
{
lean_object* v___x_336_; 
v___x_336_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__12));
v___y_315_ = v___x_334_;
v___y_316_ = v___x_336_;
goto v___jp_314_;
}
case 2:
{
lean_object* v___x_337_; 
v___x_337_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__13));
v___y_315_ = v___x_334_;
v___y_316_ = v___x_337_;
goto v___jp_314_;
}
default: 
{
lean_object* v___x_338_; 
v___x_338_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__14));
v___y_315_ = v___x_334_;
v___y_316_ = v___x_338_;
goto v___jp_314_;
}
}
}
v___jp_339_:
{
lean_object* v_queryStr_344_; lean_object* v___x_345_; 
v_queryStr_344_ = l_Std_Http_URI_Query_formatOption(v___y_342_);
v___x_345_ = lean_string_append(v___y_343_, v_queryStr_344_);
lean_dec_ref(v_queryStr_344_);
v___y_330_ = v___y_340_;
v___y_331_ = v___y_341_;
v___y_332_ = v___x_345_;
goto v___jp_329_;
}
v___jp_346_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_354_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_355_ = lean_string_append(v___y_352_, v___x_354_);
v___x_356_ = lean_string_append(v___x_355_, v___y_349_);
lean_dec_ref(v___y_349_);
v___x_357_ = lean_string_append(v___x_356_, v___y_350_);
lean_dec_ref(v___y_350_);
v___x_358_ = lean_string_append(v___x_357_, v___y_351_);
lean_dec_ref(v___y_351_);
v___x_359_ = lean_string_append(v___x_358_, v___y_353_);
lean_dec_ref(v___y_353_);
v___y_330_ = v___y_347_;
v___y_331_ = v___y_348_;
v___y_332_ = v___x_359_;
goto v___jp_329_;
}
v___jp_360_:
{
lean_object* v_queryPart_368_; 
v_queryPart_368_ = l_Std_Http_URI_Query_formatOption(v___y_366_);
if (lean_obj_tag(v___y_361_) == 0)
{
lean_object* v___x_369_; 
v___x_369_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_347_ = v___y_362_;
v___y_348_ = v___y_363_;
v___y_349_ = v___y_364_;
v___y_350_ = v___y_367_;
v___y_351_ = v_queryPart_368_;
v___y_352_ = v___y_365_;
v___y_353_ = v___x_369_;
goto v___jp_346_;
}
else
{
lean_object* v_val_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_val_370_ = lean_ctor_get(v___y_361_, 0);
lean_inc(v_val_370_);
lean_dec_ref_known(v___y_361_, 1);
v___x_371_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__16));
v___x_372_ = l_Std_Http_URI_EncodedFragment_encode(v_val_370_);
lean_dec(v_val_370_);
v___x_373_ = lean_string_from_utf8_unchecked(v___x_372_);
v___x_374_ = lean_string_append(v___x_371_, v___x_373_);
lean_dec_ref(v___x_373_);
v___y_347_ = v___y_362_;
v___y_348_ = v___y_363_;
v___y_349_ = v___y_364_;
v___y_350_ = v___y_367_;
v___y_351_ = v_queryPart_368_;
v___y_352_ = v___y_365_;
v___y_353_ = v___x_374_;
goto v___jp_346_;
}
}
v___jp_375_:
{
lean_object* v_segments_383_; uint8_t v_absolute_384_; lean_object* v___x_385_; lean_object* v___x_386_; size_t v_sz_387_; size_t v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v_result_391_; 
v_segments_383_ = lean_ctor_get(v___y_378_, 0);
lean_inc_ref(v_segments_383_);
v_absolute_384_ = lean_ctor_get_uint8(v___y_378_, sizeof(void*)*1);
lean_dec_ref(v___y_378_);
v___x_385_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_386_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_387_ = lean_array_size(v_segments_383_);
v___x_388_ = ((size_t)0ULL);
v___x_389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_386_, v___f_307_, v_sz_387_, v___x_388_, v_segments_383_);
v___x_390_ = lean_array_to_list(v___x_389_);
v_result_391_ = l_String_intercalate(v___x_385_, v___x_390_);
if (v_absolute_384_ == 0)
{
v___y_361_ = v___y_376_;
v___y_362_ = v___y_377_;
v___y_363_ = v___y_379_;
v___y_364_ = v___y_382_;
v___y_365_ = v___y_381_;
v___y_366_ = v___y_380_;
v___y_367_ = v_result_391_;
goto v___jp_360_;
}
else
{
lean_object* v___x_392_; 
v___x_392_ = lean_string_append(v___x_385_, v_result_391_);
lean_dec_ref(v_result_391_);
v___y_361_ = v___y_376_;
v___y_362_ = v___y_377_;
v___y_363_ = v___y_379_;
v___y_364_ = v___y_382_;
v___y_365_ = v___y_381_;
v___y_366_ = v___y_380_;
v___y_367_ = v___x_392_;
goto v___jp_360_;
}
}
v___jp_393_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_string_append(v___y_398_, v___y_396_);
lean_dec_ref(v___y_396_);
v___x_405_ = lean_string_append(v___x_404_, v___y_403_);
lean_dec_ref(v___y_403_);
lean_inc_ref(v___y_395_);
v___x_406_ = lean_string_append(v___y_395_, v___x_405_);
lean_dec_ref(v___x_405_);
v___y_376_ = v___y_394_;
v___y_377_ = v___y_397_;
v___y_378_ = v___y_399_;
v___y_379_ = v___y_400_;
v___y_380_ = v___y_402_;
v___y_381_ = v___y_401_;
v___y_382_ = v___x_406_;
goto v___jp_375_;
}
v___jp_407_:
{
switch(lean_obj_tag(v_port_416_))
{
case 0:
{
lean_object* v___x_418_; 
v___x_418_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_394_ = v___y_408_;
v___y_395_ = v___y_409_;
v___y_396_ = v___y_417_;
v___y_397_ = v___y_411_;
v___y_398_ = v___y_410_;
v___y_399_ = v___y_412_;
v___y_400_ = v___y_413_;
v___y_401_ = v___y_415_;
v___y_402_ = v___y_414_;
v___y_403_ = v___x_418_;
goto v___jp_393_;
}
case 1:
{
lean_object* v___x_419_; 
v___x_419_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_394_ = v___y_408_;
v___y_395_ = v___y_409_;
v___y_396_ = v___y_417_;
v___y_397_ = v___y_411_;
v___y_398_ = v___y_410_;
v___y_399_ = v___y_412_;
v___y_400_ = v___y_413_;
v___y_401_ = v___y_415_;
v___y_402_ = v___y_414_;
v___y_403_ = v___x_419_;
goto v___jp_393_;
}
default: 
{
uint16_t v_port_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_port_420_ = lean_ctor_get_uint16(v_port_416_, 0);
lean_dec_ref_known(v_port_416_, 0);
v___x_421_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_422_ = lean_uint16_to_nat(v_port_420_);
v___x_423_ = l_Nat_reprFast(v___x_422_);
v___x_424_ = lean_string_append(v___x_421_, v___x_423_);
lean_dec_ref(v___x_423_);
v___y_394_ = v___y_408_;
v___y_395_ = v___y_409_;
v___y_396_ = v___y_417_;
v___y_397_ = v___y_411_;
v___y_398_ = v___y_410_;
v___y_399_ = v___y_412_;
v___y_400_ = v___y_413_;
v___y_401_ = v___y_415_;
v___y_402_ = v___y_414_;
v___y_403_ = v___x_424_;
goto v___jp_393_;
}
}
}
v___jp_425_:
{
switch(lean_obj_tag(v_host_433_))
{
case 0:
{
lean_object* v_name_436_; 
v_name_436_ = lean_ctor_get(v_host_433_, 0);
lean_inc_ref(v_name_436_);
lean_dec_ref_known(v_host_433_, 1);
v___y_408_ = v___y_426_;
v___y_409_ = v___y_427_;
v___y_410_ = v___y_435_;
v___y_411_ = v___y_428_;
v___y_412_ = v___y_429_;
v___y_413_ = v___y_430_;
v___y_414_ = v___y_432_;
v___y_415_ = v___y_431_;
v_port_416_ = v_port_434_;
v___y_417_ = v_name_436_;
goto v___jp_407_;
}
case 1:
{
lean_object* v_ipv4_437_; lean_object* v___x_438_; 
v_ipv4_437_ = lean_ctor_get(v_host_433_, 0);
lean_inc_ref(v_ipv4_437_);
lean_dec_ref_known(v_host_433_, 1);
v___x_438_ = lean_uv_ntop_v4(v_ipv4_437_);
lean_dec_ref(v_ipv4_437_);
v___y_408_ = v___y_426_;
v___y_409_ = v___y_427_;
v___y_410_ = v___y_435_;
v___y_411_ = v___y_428_;
v___y_412_ = v___y_429_;
v___y_413_ = v___y_430_;
v___y_414_ = v___y_432_;
v___y_415_ = v___y_431_;
v_port_416_ = v_port_434_;
v___y_417_ = v___x_438_;
goto v___jp_407_;
}
default: 
{
lean_object* v_ipv6_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_ipv6_439_ = lean_ctor_get(v_host_433_, 0);
lean_inc_ref(v_ipv6_439_);
lean_dec_ref_known(v_host_433_, 1);
v___x_440_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_441_ = lean_uv_ntop_v6(v_ipv6_439_);
lean_dec_ref(v_ipv6_439_);
v___x_442_ = lean_string_append(v___x_440_, v___x_441_);
lean_dec_ref(v___x_441_);
v___x_443_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_444_ = lean_string_append(v___x_442_, v___x_443_);
v___y_408_ = v___y_426_;
v___y_409_ = v___y_427_;
v___y_410_ = v___y_435_;
v___y_411_ = v___y_428_;
v___y_412_ = v___y_429_;
v___y_413_ = v___y_430_;
v___y_414_ = v___y_432_;
v___y_415_ = v___y_431_;
v_port_416_ = v_port_434_;
v___y_417_ = v___x_444_;
goto v___jp_407_;
}
}
}
v___jp_445_:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_string_append(v___y_446_, v___y_449_);
lean_dec_ref(v___y_449_);
v___x_452_ = lean_string_append(v___x_451_, v___y_450_);
lean_dec_ref(v___y_450_);
v___y_330_ = v___y_447_;
v___y_331_ = v___y_448_;
v___y_332_ = v___x_452_;
goto v___jp_329_;
}
v___jp_453_:
{
switch(lean_obj_tag(v_port_457_))
{
case 0:
{
lean_object* v___x_459_; 
v___x_459_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_446_ = v___y_454_;
v___y_447_ = v___y_455_;
v___y_448_ = v___y_456_;
v___y_449_ = v___y_458_;
v___y_450_ = v___x_459_;
goto v___jp_445_;
}
case 1:
{
lean_object* v___x_460_; 
v___x_460_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_446_ = v___y_454_;
v___y_447_ = v___y_455_;
v___y_448_ = v___y_456_;
v___y_449_ = v___y_458_;
v___y_450_ = v___x_460_;
goto v___jp_445_;
}
default: 
{
uint16_t v_port_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_port_461_ = lean_ctor_get_uint16(v_port_457_, 0);
lean_dec_ref_known(v_port_457_, 0);
v___x_462_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_463_ = lean_uint16_to_nat(v_port_461_);
v___x_464_ = l_Nat_reprFast(v___x_463_);
v___x_465_ = lean_string_append(v___x_462_, v___x_464_);
lean_dec_ref(v___x_464_);
v___y_446_ = v___y_454_;
v___y_447_ = v___y_455_;
v___y_448_ = v___y_456_;
v___y_449_ = v___y_458_;
v___y_450_ = v___x_465_;
goto v___jp_445_;
}
}
}
v___jp_466_:
{
switch(lean_obj_tag(v_host_469_))
{
case 0:
{
lean_object* v_name_472_; 
v_name_472_ = lean_ctor_get(v_host_469_, 0);
lean_inc_ref(v_name_472_);
lean_dec_ref_known(v_host_469_, 1);
v___y_454_ = v___y_471_;
v___y_455_ = v___y_467_;
v___y_456_ = v___y_468_;
v_port_457_ = v_port_470_;
v___y_458_ = v_name_472_;
goto v___jp_453_;
}
case 1:
{
lean_object* v_ipv4_473_; lean_object* v___x_474_; 
v_ipv4_473_ = lean_ctor_get(v_host_469_, 0);
lean_inc_ref(v_ipv4_473_);
lean_dec_ref_known(v_host_469_, 1);
v___x_474_ = lean_uv_ntop_v4(v_ipv4_473_);
lean_dec_ref(v_ipv4_473_);
v___y_454_ = v___y_471_;
v___y_455_ = v___y_467_;
v___y_456_ = v___y_468_;
v_port_457_ = v_port_470_;
v___y_458_ = v___x_474_;
goto v___jp_453_;
}
default: 
{
lean_object* v_ipv6_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_ipv6_475_ = lean_ctor_get(v_host_469_, 0);
lean_inc_ref(v_ipv6_475_);
lean_dec_ref_known(v_host_469_, 1);
v___x_476_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_477_ = lean_uv_ntop_v6(v_ipv6_475_);
lean_dec_ref(v_ipv6_475_);
v___x_478_ = lean_string_append(v___x_476_, v___x_477_);
lean_dec_ref(v___x_477_);
v___x_479_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_480_ = lean_string_append(v___x_478_, v___x_479_);
v___y_454_ = v___y_471_;
v___y_455_ = v___y_467_;
v___y_456_ = v___y_468_;
v_port_457_ = v_port_470_;
v___y_458_ = v___x_480_;
goto v___jp_453_;
}
}
}
v___jp_481_:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__20));
lean_inc_ref(v___y_482_);
v___x_484_ = lean_string_append(v___y_482_, v___x_483_);
switch(lean_obj_tag(v_uri_312_))
{
case 0:
{
lean_object* v_path_485_; lean_object* v_query_486_; lean_object* v_segments_487_; uint8_t v_absolute_488_; lean_object* v___x_489_; lean_object* v___x_490_; size_t v_sz_491_; size_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v_result_495_; 
lean_dec_ref(v___f_307_);
v_path_485_ = lean_ctor_get(v_uri_312_, 0);
lean_inc_ref(v_path_485_);
v_query_486_ = lean_ctor_get(v_uri_312_, 1);
lean_inc(v_query_486_);
lean_dec_ref_known(v_uri_312_, 2);
v_segments_487_ = lean_ctor_get(v_path_485_, 0);
lean_inc_ref(v_segments_487_);
v_absolute_488_ = lean_ctor_get_uint8(v_path_485_, sizeof(void*)*1);
lean_dec_ref(v_path_485_);
v___x_489_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_490_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_491_ = lean_array_size(v_segments_487_);
v___x_492_ = ((size_t)0ULL);
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_490_, v___f_308_, v_sz_491_, v___x_492_, v_segments_487_);
v___x_494_ = lean_array_to_list(v___x_493_);
v_result_495_ = l_String_intercalate(v___x_489_, v___x_494_);
if (v_absolute_488_ == 0)
{
v___y_340_ = v___x_484_;
v___y_341_ = v___x_483_;
v___y_342_ = v_query_486_;
v___y_343_ = v_result_495_;
goto v___jp_339_;
}
else
{
lean_object* v___x_496_; 
v___x_496_ = lean_string_append(v___x_489_, v_result_495_);
lean_dec_ref(v_result_495_);
v___y_340_ = v___x_484_;
v___y_341_ = v___x_483_;
v___y_342_ = v_query_486_;
v___y_343_ = v___x_496_;
goto v___jp_339_;
}
}
case 1:
{
lean_object* v_uri_497_; lean_object* v_authority_498_; 
lean_dec_ref(v___f_308_);
v_uri_497_ = lean_ctor_get(v_uri_312_, 0);
lean_inc_ref(v_uri_497_);
lean_dec_ref_known(v_uri_312_, 1);
v_authority_498_ = lean_ctor_get(v_uri_497_, 1);
if (lean_obj_tag(v_authority_498_) == 0)
{
lean_object* v_scheme_499_; lean_object* v_path_500_; lean_object* v_query_501_; lean_object* v_fragment_502_; lean_object* v___x_503_; 
v_scheme_499_ = lean_ctor_get(v_uri_497_, 0);
lean_inc_ref(v_scheme_499_);
v_path_500_ = lean_ctor_get(v_uri_497_, 2);
lean_inc_ref(v_path_500_);
v_query_501_ = lean_ctor_get(v_uri_497_, 3);
lean_inc(v_query_501_);
v_fragment_502_ = lean_ctor_get(v_uri_497_, 4);
lean_inc(v_fragment_502_);
lean_dec_ref(v_uri_497_);
v___x_503_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_376_ = v_fragment_502_;
v___y_377_ = v___x_484_;
v___y_378_ = v_path_500_;
v___y_379_ = v___x_483_;
v___y_380_ = v_query_501_;
v___y_381_ = v_scheme_499_;
v___y_382_ = v___x_503_;
goto v___jp_375_;
}
else
{
lean_object* v_val_504_; lean_object* v_scheme_505_; lean_object* v_path_506_; lean_object* v_query_507_; lean_object* v_fragment_508_; lean_object* v_userInfo_509_; lean_object* v_host_510_; lean_object* v_port_511_; lean_object* v___x_512_; 
v_val_504_ = lean_ctor_get(v_authority_498_, 0);
lean_inc(v_val_504_);
v_scheme_505_ = lean_ctor_get(v_uri_497_, 0);
lean_inc_ref(v_scheme_505_);
v_path_506_ = lean_ctor_get(v_uri_497_, 2);
lean_inc_ref(v_path_506_);
v_query_507_ = lean_ctor_get(v_uri_497_, 3);
lean_inc(v_query_507_);
v_fragment_508_ = lean_ctor_get(v_uri_497_, 4);
lean_inc(v_fragment_508_);
lean_dec_ref(v_uri_497_);
v_userInfo_509_ = lean_ctor_get(v_val_504_, 0);
lean_inc(v_userInfo_509_);
v_host_510_ = lean_ctor_get(v_val_504_, 1);
lean_inc_ref(v_host_510_);
v_port_511_ = lean_ctor_get(v_val_504_, 2);
lean_inc(v_port_511_);
lean_dec(v_val_504_);
v___x_512_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__21));
if (lean_obj_tag(v_userInfo_509_) == 0)
{
lean_object* v___x_513_; 
v___x_513_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_426_ = v_fragment_508_;
v___y_427_ = v___x_512_;
v___y_428_ = v___x_484_;
v___y_429_ = v_path_506_;
v___y_430_ = v___x_483_;
v___y_431_ = v_scheme_505_;
v___y_432_ = v_query_507_;
v_host_433_ = v_host_510_;
v_port_434_ = v_port_511_;
v___y_435_ = v___x_513_;
goto v___jp_425_;
}
else
{
lean_object* v_val_514_; lean_object* v_password_515_; 
v_val_514_ = lean_ctor_get(v_userInfo_509_, 0);
lean_inc(v_val_514_);
lean_dec_ref_known(v_userInfo_509_, 1);
v_password_515_ = lean_ctor_get(v_val_514_, 1);
if (lean_obj_tag(v_password_515_) == 0)
{
lean_object* v_username_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_username_516_ = lean_ctor_get(v_val_514_, 0);
lean_inc_ref(v_username_516_);
lean_dec(v_val_514_);
v___x_517_ = lean_string_from_utf8_unchecked(v_username_516_);
v___x_518_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_519_ = lean_string_append(v___x_517_, v___x_518_);
v___y_426_ = v_fragment_508_;
v___y_427_ = v___x_512_;
v___y_428_ = v___x_484_;
v___y_429_ = v_path_506_;
v___y_430_ = v___x_483_;
v___y_431_ = v_scheme_505_;
v___y_432_ = v_query_507_;
v_host_433_ = v_host_510_;
v_port_434_ = v_port_511_;
v___y_435_ = v___x_519_;
goto v___jp_425_;
}
else
{
lean_object* v_username_520_; lean_object* v_val_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
lean_inc_ref(v_password_515_);
v_username_520_ = lean_ctor_get(v_val_514_, 0);
lean_inc_ref(v_username_520_);
lean_dec(v_val_514_);
v_val_521_ = lean_ctor_get(v_password_515_, 0);
lean_inc(v_val_521_);
lean_dec_ref_known(v_password_515_, 1);
v___x_522_ = lean_string_from_utf8_unchecked(v_username_520_);
v___x_523_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_524_ = lean_string_append(v___x_522_, v___x_523_);
v___x_525_ = lean_string_from_utf8_unchecked(v_val_521_);
v___x_526_ = lean_string_append(v___x_524_, v___x_525_);
lean_dec_ref(v___x_525_);
v___x_527_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_528_ = lean_string_append(v___x_526_, v___x_527_);
v___y_426_ = v_fragment_508_;
v___y_427_ = v___x_512_;
v___y_428_ = v___x_484_;
v___y_429_ = v_path_506_;
v___y_430_ = v___x_483_;
v___y_431_ = v_scheme_505_;
v___y_432_ = v_query_507_;
v_host_433_ = v_host_510_;
v_port_434_ = v_port_511_;
v___y_435_ = v___x_528_;
goto v___jp_425_;
}
}
}
}
case 2:
{
lean_object* v_authority_529_; lean_object* v_userInfo_530_; 
lean_dec_ref(v___f_308_);
lean_dec_ref(v___f_307_);
v_authority_529_ = lean_ctor_get(v_uri_312_, 0);
lean_inc_ref(v_authority_529_);
lean_dec_ref_known(v_uri_312_, 1);
v_userInfo_530_ = lean_ctor_get(v_authority_529_, 0);
if (lean_obj_tag(v_userInfo_530_) == 0)
{
lean_object* v_host_531_; lean_object* v_port_532_; lean_object* v___x_533_; 
v_host_531_ = lean_ctor_get(v_authority_529_, 1);
lean_inc_ref(v_host_531_);
v_port_532_ = lean_ctor_get(v_authority_529_, 2);
lean_inc(v_port_532_);
lean_dec_ref(v_authority_529_);
v___x_533_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_467_ = v___x_484_;
v___y_468_ = v___x_483_;
v_host_469_ = v_host_531_;
v_port_470_ = v_port_532_;
v___y_471_ = v___x_533_;
goto v___jp_466_;
}
else
{
lean_object* v_val_534_; lean_object* v_password_535_; 
v_val_534_ = lean_ctor_get(v_userInfo_530_, 0);
lean_inc(v_val_534_);
v_password_535_ = lean_ctor_get(v_val_534_, 1);
if (lean_obj_tag(v_password_535_) == 0)
{
lean_object* v_host_536_; lean_object* v_port_537_; lean_object* v_username_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_host_536_ = lean_ctor_get(v_authority_529_, 1);
lean_inc_ref(v_host_536_);
v_port_537_ = lean_ctor_get(v_authority_529_, 2);
lean_inc(v_port_537_);
lean_dec_ref(v_authority_529_);
v_username_538_ = lean_ctor_get(v_val_534_, 0);
lean_inc_ref(v_username_538_);
lean_dec(v_val_534_);
v___x_539_ = lean_string_from_utf8_unchecked(v_username_538_);
v___x_540_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_541_ = lean_string_append(v___x_539_, v___x_540_);
v___y_467_ = v___x_484_;
v___y_468_ = v___x_483_;
v_host_469_ = v_host_536_;
v_port_470_ = v_port_537_;
v___y_471_ = v___x_541_;
goto v___jp_466_;
}
else
{
lean_object* v_host_542_; lean_object* v_port_543_; lean_object* v_username_544_; lean_object* v_val_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
lean_inc_ref(v_password_535_);
v_host_542_ = lean_ctor_get(v_authority_529_, 1);
lean_inc_ref(v_host_542_);
v_port_543_ = lean_ctor_get(v_authority_529_, 2);
lean_inc(v_port_543_);
lean_dec_ref(v_authority_529_);
v_username_544_ = lean_ctor_get(v_val_534_, 0);
lean_inc_ref(v_username_544_);
lean_dec(v_val_534_);
v_val_545_ = lean_ctor_get(v_password_535_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v_password_535_, 1);
v___x_546_ = lean_string_from_utf8_unchecked(v_username_544_);
v___x_547_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_548_ = lean_string_append(v___x_546_, v___x_547_);
v___x_549_ = lean_string_from_utf8_unchecked(v_val_545_);
v___x_550_ = lean_string_append(v___x_548_, v___x_549_);
lean_dec_ref(v___x_549_);
v___x_551_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_552_ = lean_string_append(v___x_550_, v___x_551_);
v___y_467_ = v___x_484_;
v___y_468_ = v___x_483_;
v_host_469_ = v_host_542_;
v_port_470_ = v_port_543_;
v___y_471_ = v___x_552_;
goto v___jp_466_;
}
}
}
default: 
{
lean_object* v___x_553_; 
lean_dec_ref(v___f_308_);
lean_dec_ref(v___f_307_);
v___x_553_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__23));
v___y_330_ = v___x_484_;
v___y_331_ = v___x_483_;
v___y_332_ = v___x_553_;
goto v___jp_329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1(lean_object* v___x_600_, lean_object* v___x_601_, lean_object* v___x_602_, lean_object* v_name_603_, lean_object* v___x_604_, uint32_t v___x_605_, lean_object* v___x_606_, lean_object* v_it_607_, lean_object* v_acc_608_, lean_object* v_hP_609_, lean_object* v_recur_610_){
_start:
{
lean_object* v_it_612_; lean_object* v_out_613_; lean_object* v_it_629_; lean_object* v_startInclusive_630_; lean_object* v_endExclusive_631_; 
if (lean_obj_tag(v_it_607_) == 0)
{
lean_object* v_currPos_643_; lean_object* v_searcher_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_666_; 
v_currPos_643_ = lean_ctor_get(v_it_607_, 0);
v_searcher_644_ = lean_ctor_get(v_it_607_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_it_607_);
if (v_isSharedCheck_666_ == 0)
{
v___x_646_ = v_it_607_;
v_isShared_647_ = v_isSharedCheck_666_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_searcher_644_);
lean_inc(v_currPos_643_);
lean_dec(v_it_607_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_666_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
uint8_t v___x_648_; 
v___x_648_ = lean_nat_dec_eq(v_searcher_644_, v___x_604_);
if (v___x_648_ == 0)
{
uint32_t v___x_649_; uint8_t v___x_650_; 
lean_dec(v___x_604_);
v___x_649_ = lean_string_utf8_get_fast(v_name_603_, v_searcher_644_);
v___x_650_ = lean_uint32_dec_eq(v___x_649_, v___x_605_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_651_ = lean_string_utf8_next_fast(v_name_603_, v_searcher_644_);
lean_dec(v_searcher_644_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 1, v___x_651_);
v___x_653_ = v___x_646_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_currPos_643_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v___x_651_);
v___x_653_ = v_reuseFailAlloc_655_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_654_; 
v___x_654_ = lean_apply_4(v_recur_610_, v___x_653_, v_acc_608_, lean_box(0), lean_box(0));
return v___x_654_;
}
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v_slice_659_; lean_object* v_nextIt_661_; 
v___x_656_ = lean_string_utf8_next_fast(v_name_603_, v_searcher_644_);
v___x_657_ = lean_nat_sub(v___x_656_, v_searcher_644_);
v___x_658_ = lean_nat_add(v_searcher_644_, v___x_657_);
lean_dec(v___x_657_);
v_slice_659_ = l_String_Slice_subslice_x21(v___x_606_, v_currPos_643_, v_searcher_644_);
lean_inc(v___x_658_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 1, v___x_658_);
lean_ctor_set(v___x_646_, 0, v___x_658_);
v_nextIt_661_ = v___x_646_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_658_);
v_nextIt_661_ = v_reuseFailAlloc_664_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v_startInclusive_662_; lean_object* v_endExclusive_663_; 
v_startInclusive_662_ = lean_ctor_get(v_slice_659_, 0);
lean_inc(v_startInclusive_662_);
v_endExclusive_663_ = lean_ctor_get(v_slice_659_, 1);
lean_inc(v_endExclusive_663_);
lean_dec_ref(v_slice_659_);
v_it_629_ = v_nextIt_661_;
v_startInclusive_630_ = v_startInclusive_662_;
v_endExclusive_631_ = v_endExclusive_663_;
goto v___jp_628_;
}
}
}
else
{
lean_object* v___x_665_; 
lean_del_object(v___x_646_);
lean_dec(v_searcher_644_);
v___x_665_ = lean_box(1);
v_it_629_ = v___x_665_;
v_startInclusive_630_ = v_currPos_643_;
v_endExclusive_631_ = v___x_604_;
goto v___jp_628_;
}
}
}
else
{
lean_dec_ref(v_recur_610_);
lean_dec(v___x_604_);
return v_acc_608_;
}
v___jp_611_:
{
if (lean_obj_tag(v_acc_608_) == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v_out_613_);
v___x_615_ = lean_apply_4(v_recur_610_, v_it_612_, v___x_614_, lean_box(0), lean_box(0));
return v___x_615_;
}
else
{
lean_object* v_val_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_627_; 
v_val_616_ = lean_ctor_get(v_acc_608_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v_acc_608_);
if (v_isSharedCheck_627_ == 0)
{
v___x_618_ = v_acc_608_;
v_isShared_619_ = v_isSharedCheck_627_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_val_616_);
lean_dec(v_acc_608_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_627_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_620_ = lean_string_utf8_extract_fast(v___x_600_, v___x_601_, v___x_602_);
v___x_621_ = lean_string_append(v_val_616_, v___x_620_);
lean_dec_ref(v___x_620_);
v___x_622_ = lean_string_append(v___x_621_, v_out_613_);
lean_dec_ref(v_out_613_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_622_);
v___x_624_ = v___x_618_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_626_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; 
v___x_625_ = lean_apply_4(v_recur_610_, v_it_612_, v___x_624_, lean_box(0), lean_box(0));
return v___x_625_;
}
}
}
}
v___jp_628_:
{
lean_object* v___x_632_; uint32_t v___x_633_; uint32_t v___x_634_; uint8_t v___x_635_; 
v___x_632_ = lean_string_utf8_extract_fast(v_name_603_, v_startInclusive_630_, v_endExclusive_631_);
lean_dec(v_endExclusive_631_);
lean_dec(v_startInclusive_630_);
v___x_633_ = lean_string_utf8_get(v___x_632_, v___x_601_);
v___x_634_ = 97;
v___x_635_ = lean_uint32_dec_le(v___x_634_, v___x_633_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
v___x_636_ = lean_string_utf8_set(v___x_632_, v___x_601_, v___x_633_);
v_it_612_ = v_it_629_;
v_out_613_ = v___x_636_;
goto v___jp_611_;
}
else
{
uint32_t v___x_637_; uint8_t v___x_638_; 
v___x_637_ = 122;
v___x_638_ = lean_uint32_dec_le(v___x_633_, v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
v___x_639_ = lean_string_utf8_set(v___x_632_, v___x_601_, v___x_633_);
v_it_612_ = v_it_629_;
v_out_613_ = v___x_639_;
goto v___jp_611_;
}
else
{
uint32_t v___x_640_; uint32_t v___x_641_; lean_object* v___x_642_; 
v___x_640_ = 4294967264;
v___x_641_ = lean_uint32_add(v___x_633_, v___x_640_);
v___x_642_ = lean_string_utf8_set(v___x_632_, v___x_601_, v___x_641_);
v_it_612_ = v_it_629_;
v_out_613_ = v___x_642_;
goto v___jp_611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1___boxed(lean_object* v___x_667_, lean_object* v___x_668_, lean_object* v___x_669_, lean_object* v_name_670_, lean_object* v___x_671_, lean_object* v___x_672_, lean_object* v___x_673_, lean_object* v_it_674_, lean_object* v_acc_675_, lean_object* v_hP_676_, lean_object* v_recur_677_){
_start:
{
uint32_t v___x_2999__boxed_678_; lean_object* v_res_679_; 
v___x_2999__boxed_678_ = lean_unbox_uint32(v___x_672_);
lean_dec(v___x_672_);
v_res_679_ = l_Std_Http_Request_instEncodeV11Head___lam__1(v___x_667_, v___x_668_, v___x_669_, v_name_670_, v___x_671_, v___x_2999__boxed_678_, v___x_673_, v_it_674_, v_acc_675_, v_hP_676_, v_recur_677_);
lean_dec_ref(v___x_673_);
lean_dec_ref(v_name_670_);
lean_dec(v___x_669_);
lean_dec(v___x_668_);
lean_dec_ref(v___x_667_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0(lean_object* v_buf_680_, lean_object* v_name_681_, lean_object* v_value_682_){
_start:
{
lean_object* v___y_684_; lean_object* v___f_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_it_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___f_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___f_703_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__1));
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = lean_string_utf8_byte_size(v_name_681_);
lean_inc_ref(v_name_681_);
v___x_706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_706_, 0, v_name_681_);
lean_ctor_set(v___x_706_, 1, v___x_704_);
lean_ctor_set(v___x_706_, 2, v___x_705_);
lean_inc_ref(v___x_706_);
v_it_707_ = l_String_Slice_splitToSubslice___redArg(v___x_706_, v___f_703_);
v___x_708_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__2));
v___x_709_ = lean_obj_once(&l_Std_Http_Request_instToStringHead___lam__2___closed__3, &l_Std_Http_Request_instToStringHead___lam__2___closed__3_once, _init_l_Std_Http_Request_instToStringHead___lam__2___closed__3);
v___x_710_ = l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1;
v___f_711_ = lean_alloc_closure((void*)(l_Std_Http_Request_instEncodeV11Head___lam__1___boxed), 11, 7);
lean_closure_set(v___f_711_, 0, v___x_708_);
lean_closure_set(v___f_711_, 1, v___x_704_);
lean_closure_set(v___f_711_, 2, v___x_709_);
lean_closure_set(v___f_711_, 3, v_name_681_);
lean_closure_set(v___f_711_, 4, v___x_705_);
lean_closure_set(v___f_711_, 5, v___x_710_);
lean_closure_set(v___f_711_, 6, v___x_706_);
v___x_712_ = lean_box(0);
v___x_713_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_711_, v_it_707_, v___x_712_, lean_box(0));
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v___x_714_; 
v___x_714_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_684_ = v___x_714_;
goto v___jp_683_;
}
else
{
lean_object* v_val_715_; 
v_val_715_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_val_715_);
lean_dec_ref_known(v___x_713_, 1);
v___y_684_ = v_val_715_;
goto v___jp_683_;
}
v___jp_683_:
{
lean_object* v_data_685_; lean_object* v_size_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_702_; 
v_data_685_ = lean_ctor_get(v_buf_680_, 0);
v_size_686_ = lean_ctor_get(v_buf_680_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_buf_680_);
if (v_isSharedCheck_702_ == 0)
{
v___x_688_ = v_buf_680_;
v_isShared_689_ = v_isSharedCheck_702_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_size_686_);
lean_inc(v_data_685_);
lean_dec(v_buf_680_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_702_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_690_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__0));
v___x_691_ = lean_string_append(v___y_684_, v___x_690_);
v___x_692_ = lean_string_append(v___x_691_, v_value_682_);
v___x_693_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__0));
v___x_694_ = lean_string_append(v___x_692_, v___x_693_);
v___x_695_ = lean_string_to_utf8(v___x_694_);
lean_dec_ref(v___x_694_);
lean_inc_ref(v___x_695_);
v___x_696_ = lean_array_push(v_data_685_, v___x_695_);
v___x_697_ = lean_byte_array_size(v___x_695_);
lean_dec_ref(v___x_695_);
v___x_698_ = lean_nat_add(v_size_686_, v___x_697_);
lean_dec(v_size_686_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v___x_698_);
lean_ctor_set(v___x_688_, 0, v___x_696_);
v___x_700_ = v___x_688_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___boxed(lean_object* v_buf_716_, lean_object* v_name_717_, lean_object* v_value_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Std_Http_Request_instEncodeV11Head___lam__0(v_buf_716_, v_name_717_, v_value_718_);
lean_dec_ref(v_value_718_);
return v_res_719_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__0));
v___x_721_ = lean_string_to_utf8(v___x_720_);
return v___x_721_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0);
v___x_723_ = lean_byte_array_size(v___x_722_);
return v___x_723_;
}
}
static uint8_t _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2(void){
_start:
{
uint32_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = 32;
v___x_725_ = lean_uint32_to_uint8(v___x_724_);
return v___x_725_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3(void){
_start:
{
uint8_t v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_726_ = lean_uint8_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2);
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_mk_empty_array_with_capacity(v___x_727_);
v___x_729_ = lean_box(v___x_726_);
v___x_730_ = lean_array_push(v___x_728_, v___x_729_);
v___x_731_ = lean_byte_array_mk(v___x_730_);
return v___x_731_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__4(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3);
v___x_733_ = lean_byte_array_size(v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3(lean_object* v___f_734_, lean_object* v___f_735_, lean_object* v___f_736_, lean_object* v_buffer_737_, lean_object* v_req_738_){
_start:
{
uint8_t v_method_739_; uint8_t v_version_740_; lean_object* v_uri_741_; lean_object* v_headers_742_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v_port_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v_host_813_; lean_object* v_port_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_896_; lean_object* v_port_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v_host_919_; lean_object* v_port_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_947_; 
v_method_739_ = lean_ctor_get_uint8(v_req_738_, sizeof(void*)*2);
v_version_740_ = lean_ctor_get_uint8(v_req_738_, sizeof(void*)*2 + 1);
v_uri_741_ = lean_ctor_get(v_req_738_, 0);
lean_inc(v_uri_741_);
v_headers_742_ = lean_ctor_get(v_req_738_, 1);
lean_inc_ref(v_headers_742_);
lean_dec_ref(v_req_738_);
switch(v_method_739_)
{
case 0:
{
lean_object* v___x_1027_; 
v___x_1027_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__24));
v___y_947_ = v___x_1027_;
goto v___jp_946_;
}
case 1:
{
lean_object* v___x_1028_; 
v___x_1028_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__25));
v___y_947_ = v___x_1028_;
goto v___jp_946_;
}
case 2:
{
lean_object* v___x_1029_; 
v___x_1029_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__26));
v___y_947_ = v___x_1029_;
goto v___jp_946_;
}
case 3:
{
lean_object* v___x_1030_; 
v___x_1030_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__27));
v___y_947_ = v___x_1030_;
goto v___jp_946_;
}
case 4:
{
lean_object* v___x_1031_; 
v___x_1031_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__28));
v___y_947_ = v___x_1031_;
goto v___jp_946_;
}
case 5:
{
lean_object* v___x_1032_; 
v___x_1032_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__29));
v___y_947_ = v___x_1032_;
goto v___jp_946_;
}
case 6:
{
lean_object* v___x_1033_; 
v___x_1033_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__30));
v___y_947_ = v___x_1033_;
goto v___jp_946_;
}
case 7:
{
lean_object* v___x_1034_; 
v___x_1034_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__31));
v___y_947_ = v___x_1034_;
goto v___jp_946_;
}
case 8:
{
lean_object* v___x_1035_; 
v___x_1035_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__32));
v___y_947_ = v___x_1035_;
goto v___jp_946_;
}
case 9:
{
lean_object* v___x_1036_; 
v___x_1036_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__33));
v___y_947_ = v___x_1036_;
goto v___jp_946_;
}
case 10:
{
lean_object* v___x_1037_; 
v___x_1037_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__34));
v___y_947_ = v___x_1037_;
goto v___jp_946_;
}
case 11:
{
lean_object* v___x_1038_; 
v___x_1038_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__35));
v___y_947_ = v___x_1038_;
goto v___jp_946_;
}
case 12:
{
lean_object* v___x_1039_; 
v___x_1039_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__36));
v___y_947_ = v___x_1039_;
goto v___jp_946_;
}
case 13:
{
lean_object* v___x_1040_; 
v___x_1040_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__37));
v___y_947_ = v___x_1040_;
goto v___jp_946_;
}
case 14:
{
lean_object* v___x_1041_; 
v___x_1041_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__38));
v___y_947_ = v___x_1041_;
goto v___jp_946_;
}
case 15:
{
lean_object* v___x_1042_; 
v___x_1042_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__39));
v___y_947_ = v___x_1042_;
goto v___jp_946_;
}
case 16:
{
lean_object* v___x_1043_; 
v___x_1043_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__40));
v___y_947_ = v___x_1043_;
goto v___jp_946_;
}
case 17:
{
lean_object* v___x_1044_; 
v___x_1044_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__41));
v___y_947_ = v___x_1044_;
goto v___jp_946_;
}
case 18:
{
lean_object* v___x_1045_; 
v___x_1045_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__42));
v___y_947_ = v___x_1045_;
goto v___jp_946_;
}
case 19:
{
lean_object* v___x_1046_; 
v___x_1046_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__43));
v___y_947_ = v___x_1046_;
goto v___jp_946_;
}
case 20:
{
lean_object* v___x_1047_; 
v___x_1047_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__44));
v___y_947_ = v___x_1047_;
goto v___jp_946_;
}
case 21:
{
lean_object* v___x_1048_; 
v___x_1048_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__45));
v___y_947_ = v___x_1048_;
goto v___jp_946_;
}
case 22:
{
lean_object* v___x_1049_; 
v___x_1049_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__46));
v___y_947_ = v___x_1049_;
goto v___jp_946_;
}
case 23:
{
lean_object* v___x_1050_; 
v___x_1050_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__47));
v___y_947_ = v___x_1050_;
goto v___jp_946_;
}
case 24:
{
lean_object* v___x_1051_; 
v___x_1051_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__48));
v___y_947_ = v___x_1051_;
goto v___jp_946_;
}
case 25:
{
lean_object* v___x_1052_; 
v___x_1052_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__49));
v___y_947_ = v___x_1052_;
goto v___jp_946_;
}
case 26:
{
lean_object* v___x_1053_; 
v___x_1053_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__50));
v___y_947_ = v___x_1053_;
goto v___jp_946_;
}
case 27:
{
lean_object* v___x_1054_; 
v___x_1054_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__51));
v___y_947_ = v___x_1054_;
goto v___jp_946_;
}
case 28:
{
lean_object* v___x_1055_; 
v___x_1055_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__52));
v___y_947_ = v___x_1055_;
goto v___jp_946_;
}
case 29:
{
lean_object* v___x_1056_; 
v___x_1056_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__53));
v___y_947_ = v___x_1056_;
goto v___jp_946_;
}
case 30:
{
lean_object* v___x_1057_; 
v___x_1057_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__54));
v___y_947_ = v___x_1057_;
goto v___jp_946_;
}
case 31:
{
lean_object* v___x_1058_; 
v___x_1058_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__55));
v___y_947_ = v___x_1058_;
goto v___jp_946_;
}
case 32:
{
lean_object* v___x_1059_; 
v___x_1059_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__56));
v___y_947_ = v___x_1059_;
goto v___jp_946_;
}
case 33:
{
lean_object* v___x_1060_; 
v___x_1060_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__57));
v___y_947_ = v___x_1060_;
goto v___jp_946_;
}
case 34:
{
lean_object* v___x_1061_; 
v___x_1061_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__58));
v___y_947_ = v___x_1061_;
goto v___jp_946_;
}
case 35:
{
lean_object* v___x_1062_; 
v___x_1062_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__59));
v___y_947_ = v___x_1062_;
goto v___jp_946_;
}
case 36:
{
lean_object* v___x_1063_; 
v___x_1063_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__60));
v___y_947_ = v___x_1063_;
goto v___jp_946_;
}
case 37:
{
lean_object* v___x_1064_; 
v___x_1064_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__61));
v___y_947_ = v___x_1064_;
goto v___jp_946_;
}
case 38:
{
lean_object* v___x_1065_; 
v___x_1065_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__62));
v___y_947_ = v___x_1065_;
goto v___jp_946_;
}
default: 
{
lean_object* v___x_1066_; 
v___x_1066_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__63));
v___y_947_ = v___x_1066_;
goto v___jp_946_;
}
}
v___jp_743_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v_buffer_755_; lean_object* v_buffer_756_; lean_object* v_data_757_; lean_object* v_size_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_767_; 
v___x_747_ = lean_string_to_utf8(v___y_746_);
lean_inc_ref(v___x_747_);
v___x_748_ = lean_array_push(v___y_744_, v___x_747_);
v___x_749_ = lean_byte_array_size(v___x_747_);
lean_dec_ref(v___x_747_);
v___x_750_ = lean_nat_add(v___y_745_, v___x_749_);
lean_dec(v___y_745_);
v___x_751_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0);
v___x_752_ = lean_array_push(v___x_748_, v___x_751_);
v___x_753_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1);
v___x_754_ = lean_nat_add(v___x_750_, v___x_753_);
lean_dec(v___x_750_);
v_buffer_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_755_, 0, v___x_752_);
lean_ctor_set(v_buffer_755_, 1, v___x_754_);
v_buffer_756_ = l_Std_Http_Headers_fold___redArg(v_headers_742_, v_buffer_755_, v___f_734_);
lean_dec_ref(v_headers_742_);
v_data_757_ = lean_ctor_get(v_buffer_756_, 0);
v_size_758_ = lean_ctor_get(v_buffer_756_, 1);
v_isSharedCheck_767_ = !lean_is_exclusive(v_buffer_756_);
if (v_isSharedCheck_767_ == 0)
{
v___x_760_ = v_buffer_756_;
v_isShared_761_ = v_isSharedCheck_767_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_size_758_);
lean_inc(v_data_757_);
lean_dec(v_buffer_756_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_767_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_762_ = lean_array_push(v_data_757_, v___x_751_);
v___x_763_ = lean_nat_add(v_size_758_, v___x_753_);
lean_dec(v_size_758_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v___x_763_);
lean_ctor_set(v___x_760_, 0, v___x_762_);
v___x_765_ = v___x_760_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
v___jp_768_:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_774_ = lean_string_to_utf8(v___y_773_);
lean_dec_ref(v___y_773_);
lean_inc_ref(v___x_774_);
v___x_775_ = lean_array_push(v___y_769_, v___x_774_);
v___x_776_ = lean_byte_array_size(v___x_774_);
lean_dec_ref(v___x_774_);
v___x_777_ = lean_nat_add(v___y_772_, v___x_776_);
lean_dec(v___y_772_);
v___x_778_ = lean_array_push(v___x_775_, v___y_770_);
v___x_779_ = lean_nat_add(v___x_777_, v___y_771_);
lean_dec(v___x_777_);
switch(v_version_740_)
{
case 0:
{
lean_object* v___x_780_; 
v___x_780_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__11));
v___y_744_ = v___x_778_;
v___y_745_ = v___x_779_;
v___y_746_ = v___x_780_;
goto v___jp_743_;
}
case 1:
{
lean_object* v___x_781_; 
v___x_781_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__12));
v___y_744_ = v___x_778_;
v___y_745_ = v___x_779_;
v___y_746_ = v___x_781_;
goto v___jp_743_;
}
case 2:
{
lean_object* v___x_782_; 
v___x_782_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__13));
v___y_744_ = v___x_778_;
v___y_745_ = v___x_779_;
v___y_746_ = v___x_782_;
goto v___jp_743_;
}
default: 
{
lean_object* v___x_783_; 
v___x_783_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__14));
v___y_744_ = v___x_778_;
v___y_745_ = v___x_779_;
v___y_746_ = v___x_783_;
goto v___jp_743_;
}
}
}
v___jp_784_:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_string_append(v___y_785_, v___y_790_);
lean_dec_ref(v___y_790_);
v___x_793_ = lean_string_append(v___x_792_, v___y_791_);
lean_dec_ref(v___y_791_);
v___y_769_ = v___y_786_;
v___y_770_ = v___y_787_;
v___y_771_ = v___y_788_;
v___y_772_ = v___y_789_;
v___y_773_ = v___x_793_;
goto v___jp_768_;
}
v___jp_794_:
{
switch(lean_obj_tag(v_port_799_))
{
case 0:
{
lean_object* v___x_802_; 
v___x_802_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_785_ = v___y_795_;
v___y_786_ = v___y_796_;
v___y_787_ = v___y_797_;
v___y_788_ = v___y_798_;
v___y_789_ = v___y_800_;
v___y_790_ = v___y_801_;
v___y_791_ = v___x_802_;
goto v___jp_784_;
}
case 1:
{
lean_object* v___x_803_; 
v___x_803_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_785_ = v___y_795_;
v___y_786_ = v___y_796_;
v___y_787_ = v___y_797_;
v___y_788_ = v___y_798_;
v___y_789_ = v___y_800_;
v___y_790_ = v___y_801_;
v___y_791_ = v___x_803_;
goto v___jp_784_;
}
default: 
{
uint16_t v_port_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_port_804_ = lean_ctor_get_uint16(v_port_799_, 0);
lean_dec_ref_known(v_port_799_, 0);
v___x_805_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_806_ = lean_uint16_to_nat(v_port_804_);
v___x_807_ = l_Nat_reprFast(v___x_806_);
v___x_808_ = lean_string_append(v___x_805_, v___x_807_);
lean_dec_ref(v___x_807_);
v___y_785_ = v___y_795_;
v___y_786_ = v___y_796_;
v___y_787_ = v___y_797_;
v___y_788_ = v___y_798_;
v___y_789_ = v___y_800_;
v___y_790_ = v___y_801_;
v___y_791_ = v___x_808_;
goto v___jp_784_;
}
}
}
v___jp_809_:
{
switch(lean_obj_tag(v_host_813_))
{
case 0:
{
lean_object* v_name_817_; 
v_name_817_ = lean_ctor_get(v_host_813_, 0);
lean_inc_ref(v_name_817_);
lean_dec_ref_known(v_host_813_, 1);
v___y_795_ = v___y_816_;
v___y_796_ = v___y_810_;
v___y_797_ = v___y_811_;
v___y_798_ = v___y_812_;
v_port_799_ = v_port_814_;
v___y_800_ = v___y_815_;
v___y_801_ = v_name_817_;
goto v___jp_794_;
}
case 1:
{
lean_object* v_ipv4_818_; lean_object* v___x_819_; 
v_ipv4_818_ = lean_ctor_get(v_host_813_, 0);
lean_inc_ref(v_ipv4_818_);
lean_dec_ref_known(v_host_813_, 1);
v___x_819_ = lean_uv_ntop_v4(v_ipv4_818_);
lean_dec_ref(v_ipv4_818_);
v___y_795_ = v___y_816_;
v___y_796_ = v___y_810_;
v___y_797_ = v___y_811_;
v___y_798_ = v___y_812_;
v_port_799_ = v_port_814_;
v___y_800_ = v___y_815_;
v___y_801_ = v___x_819_;
goto v___jp_794_;
}
default: 
{
lean_object* v_ipv6_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_ipv6_820_ = lean_ctor_get(v_host_813_, 0);
lean_inc_ref(v_ipv6_820_);
lean_dec_ref_known(v_host_813_, 1);
v___x_821_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_822_ = lean_uv_ntop_v6(v_ipv6_820_);
lean_dec_ref(v_ipv6_820_);
v___x_823_ = lean_string_append(v___x_821_, v___x_822_);
lean_dec_ref(v___x_822_);
v___x_824_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_825_ = lean_string_append(v___x_823_, v___x_824_);
v___y_795_ = v___y_816_;
v___y_796_ = v___y_810_;
v___y_797_ = v___y_811_;
v___y_798_ = v___y_812_;
v_port_799_ = v_port_814_;
v___y_800_ = v___y_815_;
v___y_801_ = v___x_825_;
goto v___jp_794_;
}
}
}
v___jp_826_:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_836_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_837_ = lean_string_append(v___y_829_, v___x_836_);
v___x_838_ = lean_string_append(v___x_837_, v___y_831_);
lean_dec_ref(v___y_831_);
v___x_839_ = lean_string_append(v___x_838_, v___y_833_);
lean_dec_ref(v___y_833_);
v___x_840_ = lean_string_append(v___x_839_, v___y_834_);
lean_dec_ref(v___y_834_);
v___x_841_ = lean_string_append(v___x_840_, v___y_835_);
lean_dec_ref(v___y_835_);
v___y_769_ = v___y_827_;
v___y_770_ = v___y_828_;
v___y_771_ = v___y_830_;
v___y_772_ = v___y_832_;
v___y_773_ = v___x_841_;
goto v___jp_768_;
}
v___jp_842_:
{
lean_object* v_queryPart_852_; 
v_queryPart_852_ = l_Std_Http_URI_Query_formatOption(v___y_844_);
if (lean_obj_tag(v___y_848_) == 0)
{
lean_object* v___x_853_; 
v___x_853_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_827_ = v___y_843_;
v___y_828_ = v___y_846_;
v___y_829_ = v___y_845_;
v___y_830_ = v___y_847_;
v___y_831_ = v___y_849_;
v___y_832_ = v___y_850_;
v___y_833_ = v___y_851_;
v___y_834_ = v_queryPart_852_;
v___y_835_ = v___x_853_;
goto v___jp_826_;
}
else
{
lean_object* v_val_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_val_854_ = lean_ctor_get(v___y_848_, 0);
lean_inc(v_val_854_);
lean_dec_ref_known(v___y_848_, 1);
v___x_855_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__16));
v___x_856_ = l_Std_Http_URI_EncodedFragment_encode(v_val_854_);
lean_dec(v_val_854_);
v___x_857_ = lean_string_from_utf8_unchecked(v___x_856_);
v___x_858_ = lean_string_append(v___x_855_, v___x_857_);
lean_dec_ref(v___x_857_);
v___y_827_ = v___y_843_;
v___y_828_ = v___y_846_;
v___y_829_ = v___y_845_;
v___y_830_ = v___y_847_;
v___y_831_ = v___y_849_;
v___y_832_ = v___y_850_;
v___y_833_ = v___y_851_;
v___y_834_ = v_queryPart_852_;
v___y_835_ = v___x_858_;
goto v___jp_826_;
}
}
v___jp_859_:
{
lean_object* v_segments_869_; uint8_t v_absolute_870_; lean_object* v___x_871_; lean_object* v___x_872_; size_t v_sz_873_; size_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v_result_877_; 
v_segments_869_ = lean_ctor_get(v___y_866_, 0);
lean_inc_ref(v_segments_869_);
v_absolute_870_ = lean_ctor_get_uint8(v___y_866_, sizeof(void*)*1);
lean_dec_ref(v___y_866_);
v___x_871_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_872_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_873_ = lean_array_size(v_segments_869_);
v___x_874_ = ((size_t)0ULL);
v___x_875_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_872_, v___f_735_, v_sz_873_, v___x_874_, v_segments_869_);
v___x_876_ = lean_array_to_list(v___x_875_);
v_result_877_ = l_String_intercalate(v___x_871_, v___x_876_);
if (v_absolute_870_ == 0)
{
v___y_843_ = v___y_861_;
v___y_844_ = v___y_860_;
v___y_845_ = v___y_863_;
v___y_846_ = v___y_862_;
v___y_847_ = v___y_864_;
v___y_848_ = v___y_865_;
v___y_849_ = v___y_868_;
v___y_850_ = v___y_867_;
v___y_851_ = v_result_877_;
goto v___jp_842_;
}
else
{
lean_object* v___x_878_; 
v___x_878_ = lean_string_append(v___x_871_, v_result_877_);
lean_dec_ref(v_result_877_);
v___y_843_ = v___y_861_;
v___y_844_ = v___y_860_;
v___y_845_ = v___y_863_;
v___y_846_ = v___y_862_;
v___y_847_ = v___y_864_;
v___y_848_ = v___y_865_;
v___y_849_ = v___y_868_;
v___y_850_ = v___y_867_;
v___y_851_ = v___x_878_;
goto v___jp_842_;
}
}
v___jp_879_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_string_append(v___y_890_, v___y_887_);
lean_dec_ref(v___y_887_);
v___x_893_ = lean_string_append(v___x_892_, v___y_891_);
lean_dec_ref(v___y_891_);
lean_inc_ref(v___y_880_);
v___x_894_ = lean_string_append(v___y_880_, v___x_893_);
lean_dec_ref(v___x_893_);
v___y_860_ = v___y_882_;
v___y_861_ = v___y_881_;
v___y_862_ = v___y_884_;
v___y_863_ = v___y_883_;
v___y_864_ = v___y_885_;
v___y_865_ = v___y_886_;
v___y_866_ = v___y_888_;
v___y_867_ = v___y_889_;
v___y_868_ = v___x_894_;
goto v___jp_859_;
}
v___jp_895_:
{
switch(lean_obj_tag(v_port_897_))
{
case 0:
{
lean_object* v___x_908_; 
v___x_908_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_880_ = v___y_896_;
v___y_881_ = v___y_899_;
v___y_882_ = v___y_898_;
v___y_883_ = v___y_901_;
v___y_884_ = v___y_900_;
v___y_885_ = v___y_902_;
v___y_886_ = v___y_903_;
v___y_887_ = v___y_907_;
v___y_888_ = v___y_904_;
v___y_889_ = v___y_905_;
v___y_890_ = v___y_906_;
v___y_891_ = v___x_908_;
goto v___jp_879_;
}
case 1:
{
lean_object* v___x_909_; 
v___x_909_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_880_ = v___y_896_;
v___y_881_ = v___y_899_;
v___y_882_ = v___y_898_;
v___y_883_ = v___y_901_;
v___y_884_ = v___y_900_;
v___y_885_ = v___y_902_;
v___y_886_ = v___y_903_;
v___y_887_ = v___y_907_;
v___y_888_ = v___y_904_;
v___y_889_ = v___y_905_;
v___y_890_ = v___y_906_;
v___y_891_ = v___x_909_;
goto v___jp_879_;
}
default: 
{
uint16_t v_port_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_port_910_ = lean_ctor_get_uint16(v_port_897_, 0);
lean_dec_ref_known(v_port_897_, 0);
v___x_911_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_912_ = lean_uint16_to_nat(v_port_910_);
v___x_913_ = l_Nat_reprFast(v___x_912_);
v___x_914_ = lean_string_append(v___x_911_, v___x_913_);
lean_dec_ref(v___x_913_);
v___y_880_ = v___y_896_;
v___y_881_ = v___y_899_;
v___y_882_ = v___y_898_;
v___y_883_ = v___y_901_;
v___y_884_ = v___y_900_;
v___y_885_ = v___y_902_;
v___y_886_ = v___y_903_;
v___y_887_ = v___y_907_;
v___y_888_ = v___y_904_;
v___y_889_ = v___y_905_;
v___y_890_ = v___y_906_;
v___y_891_ = v___x_914_;
goto v___jp_879_;
}
}
}
v___jp_915_:
{
switch(lean_obj_tag(v_host_919_))
{
case 0:
{
lean_object* v_name_928_; 
v_name_928_ = lean_ctor_get(v_host_919_, 0);
lean_inc_ref(v_name_928_);
lean_dec_ref_known(v_host_919_, 1);
v___y_896_ = v___y_916_;
v_port_897_ = v_port_920_;
v___y_898_ = v___y_918_;
v___y_899_ = v___y_917_;
v___y_900_ = v___y_922_;
v___y_901_ = v___y_921_;
v___y_902_ = v___y_923_;
v___y_903_ = v___y_924_;
v___y_904_ = v___y_925_;
v___y_905_ = v___y_926_;
v___y_906_ = v___y_927_;
v___y_907_ = v_name_928_;
goto v___jp_895_;
}
case 1:
{
lean_object* v_ipv4_929_; lean_object* v___x_930_; 
v_ipv4_929_ = lean_ctor_get(v_host_919_, 0);
lean_inc_ref(v_ipv4_929_);
lean_dec_ref_known(v_host_919_, 1);
v___x_930_ = lean_uv_ntop_v4(v_ipv4_929_);
lean_dec_ref(v_ipv4_929_);
v___y_896_ = v___y_916_;
v_port_897_ = v_port_920_;
v___y_898_ = v___y_918_;
v___y_899_ = v___y_917_;
v___y_900_ = v___y_922_;
v___y_901_ = v___y_921_;
v___y_902_ = v___y_923_;
v___y_903_ = v___y_924_;
v___y_904_ = v___y_925_;
v___y_905_ = v___y_926_;
v___y_906_ = v___y_927_;
v___y_907_ = v___x_930_;
goto v___jp_895_;
}
default: 
{
lean_object* v_ipv6_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_ipv6_931_ = lean_ctor_get(v_host_919_, 0);
lean_inc_ref(v_ipv6_931_);
lean_dec_ref_known(v_host_919_, 1);
v___x_932_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_933_ = lean_uv_ntop_v6(v_ipv6_931_);
lean_dec_ref(v_ipv6_931_);
v___x_934_ = lean_string_append(v___x_932_, v___x_933_);
lean_dec_ref(v___x_933_);
v___x_935_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_936_ = lean_string_append(v___x_934_, v___x_935_);
v___y_896_ = v___y_916_;
v_port_897_ = v_port_920_;
v___y_898_ = v___y_918_;
v___y_899_ = v___y_917_;
v___y_900_ = v___y_922_;
v___y_901_ = v___y_921_;
v___y_902_ = v___y_923_;
v___y_903_ = v___y_924_;
v___y_904_ = v___y_925_;
v___y_905_ = v___y_926_;
v___y_906_ = v___y_927_;
v___y_907_ = v___x_936_;
goto v___jp_895_;
}
}
}
v___jp_937_:
{
lean_object* v_queryStr_944_; lean_object* v___x_945_; 
v_queryStr_944_ = l_Std_Http_URI_Query_formatOption(v___y_938_);
v___x_945_ = lean_string_append(v___y_943_, v_queryStr_944_);
lean_dec_ref(v_queryStr_944_);
v___y_769_ = v___y_939_;
v___y_770_ = v___y_940_;
v___y_771_ = v___y_941_;
v___y_772_ = v___y_942_;
v___y_773_ = v___x_945_;
goto v___jp_768_;
}
v___jp_946_:
{
lean_object* v_data_948_; lean_object* v_size_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_data_948_ = lean_ctor_get(v_buffer_737_, 0);
lean_inc_ref(v_data_948_);
v_size_949_ = lean_ctor_get(v_buffer_737_, 1);
lean_inc(v_size_949_);
lean_dec_ref(v_buffer_737_);
v___x_950_ = lean_string_to_utf8(v___y_947_);
lean_inc_ref(v___x_950_);
v___x_951_ = lean_array_push(v_data_948_, v___x_950_);
v___x_952_ = lean_byte_array_size(v___x_950_);
lean_dec_ref(v___x_950_);
v___x_953_ = lean_nat_add(v_size_949_, v___x_952_);
lean_dec(v_size_949_);
v___x_954_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3);
v___x_955_ = lean_array_push(v___x_951_, v___x_954_);
v___x_956_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__4, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__4_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__4);
v___x_957_ = lean_nat_add(v___x_953_, v___x_956_);
lean_dec(v___x_953_);
switch(lean_obj_tag(v_uri_741_))
{
case 0:
{
lean_object* v_path_958_; lean_object* v_query_959_; lean_object* v_segments_960_; uint8_t v_absolute_961_; lean_object* v___x_962_; lean_object* v___x_963_; size_t v_sz_964_; size_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v_result_968_; 
lean_dec_ref(v___f_735_);
v_path_958_ = lean_ctor_get(v_uri_741_, 0);
lean_inc_ref(v_path_958_);
v_query_959_ = lean_ctor_get(v_uri_741_, 1);
lean_inc(v_query_959_);
lean_dec_ref_known(v_uri_741_, 2);
v_segments_960_ = lean_ctor_get(v_path_958_, 0);
lean_inc_ref(v_segments_960_);
v_absolute_961_ = lean_ctor_get_uint8(v_path_958_, sizeof(void*)*1);
lean_dec_ref(v_path_958_);
v___x_962_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_963_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_964_ = lean_array_size(v_segments_960_);
v___x_965_ = ((size_t)0ULL);
v___x_966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_963_, v___f_736_, v_sz_964_, v___x_965_, v_segments_960_);
v___x_967_ = lean_array_to_list(v___x_966_);
v_result_968_ = l_String_intercalate(v___x_962_, v___x_967_);
if (v_absolute_961_ == 0)
{
v___y_938_ = v_query_959_;
v___y_939_ = v___x_955_;
v___y_940_ = v___x_954_;
v___y_941_ = v___x_956_;
v___y_942_ = v___x_957_;
v___y_943_ = v_result_968_;
goto v___jp_937_;
}
else
{
lean_object* v___x_969_; 
v___x_969_ = lean_string_append(v___x_962_, v_result_968_);
lean_dec_ref(v_result_968_);
v___y_938_ = v_query_959_;
v___y_939_ = v___x_955_;
v___y_940_ = v___x_954_;
v___y_941_ = v___x_956_;
v___y_942_ = v___x_957_;
v___y_943_ = v___x_969_;
goto v___jp_937_;
}
}
case 1:
{
lean_object* v_uri_970_; lean_object* v_authority_971_; 
lean_dec_ref(v___f_736_);
v_uri_970_ = lean_ctor_get(v_uri_741_, 0);
lean_inc_ref(v_uri_970_);
lean_dec_ref_known(v_uri_741_, 1);
v_authority_971_ = lean_ctor_get(v_uri_970_, 1);
if (lean_obj_tag(v_authority_971_) == 0)
{
lean_object* v_scheme_972_; lean_object* v_path_973_; lean_object* v_query_974_; lean_object* v_fragment_975_; lean_object* v___x_976_; 
v_scheme_972_ = lean_ctor_get(v_uri_970_, 0);
lean_inc_ref(v_scheme_972_);
v_path_973_ = lean_ctor_get(v_uri_970_, 2);
lean_inc_ref(v_path_973_);
v_query_974_ = lean_ctor_get(v_uri_970_, 3);
lean_inc(v_query_974_);
v_fragment_975_ = lean_ctor_get(v_uri_970_, 4);
lean_inc(v_fragment_975_);
lean_dec_ref(v_uri_970_);
v___x_976_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_860_ = v_query_974_;
v___y_861_ = v___x_955_;
v___y_862_ = v___x_954_;
v___y_863_ = v_scheme_972_;
v___y_864_ = v___x_956_;
v___y_865_ = v_fragment_975_;
v___y_866_ = v_path_973_;
v___y_867_ = v___x_957_;
v___y_868_ = v___x_976_;
goto v___jp_859_;
}
else
{
lean_object* v_val_977_; lean_object* v_scheme_978_; lean_object* v_path_979_; lean_object* v_query_980_; lean_object* v_fragment_981_; lean_object* v_userInfo_982_; lean_object* v_host_983_; lean_object* v_port_984_; lean_object* v___x_985_; 
v_val_977_ = lean_ctor_get(v_authority_971_, 0);
lean_inc(v_val_977_);
v_scheme_978_ = lean_ctor_get(v_uri_970_, 0);
lean_inc_ref(v_scheme_978_);
v_path_979_ = lean_ctor_get(v_uri_970_, 2);
lean_inc_ref(v_path_979_);
v_query_980_ = lean_ctor_get(v_uri_970_, 3);
lean_inc(v_query_980_);
v_fragment_981_ = lean_ctor_get(v_uri_970_, 4);
lean_inc(v_fragment_981_);
lean_dec_ref(v_uri_970_);
v_userInfo_982_ = lean_ctor_get(v_val_977_, 0);
lean_inc(v_userInfo_982_);
v_host_983_ = lean_ctor_get(v_val_977_, 1);
lean_inc_ref(v_host_983_);
v_port_984_ = lean_ctor_get(v_val_977_, 2);
lean_inc(v_port_984_);
lean_dec(v_val_977_);
v___x_985_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__21));
if (lean_obj_tag(v_userInfo_982_) == 0)
{
lean_object* v___x_986_; 
v___x_986_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_916_ = v___x_985_;
v___y_917_ = v___x_955_;
v___y_918_ = v_query_980_;
v_host_919_ = v_host_983_;
v_port_920_ = v_port_984_;
v___y_921_ = v_scheme_978_;
v___y_922_ = v___x_954_;
v___y_923_ = v___x_956_;
v___y_924_ = v_fragment_981_;
v___y_925_ = v_path_979_;
v___y_926_ = v___x_957_;
v___y_927_ = v___x_986_;
goto v___jp_915_;
}
else
{
lean_object* v_val_987_; lean_object* v_password_988_; 
v_val_987_ = lean_ctor_get(v_userInfo_982_, 0);
lean_inc(v_val_987_);
lean_dec_ref_known(v_userInfo_982_, 1);
v_password_988_ = lean_ctor_get(v_val_987_, 1);
if (lean_obj_tag(v_password_988_) == 0)
{
lean_object* v_username_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_username_989_ = lean_ctor_get(v_val_987_, 0);
lean_inc_ref(v_username_989_);
lean_dec(v_val_987_);
v___x_990_ = lean_string_from_utf8_unchecked(v_username_989_);
v___x_991_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_992_ = lean_string_append(v___x_990_, v___x_991_);
v___y_916_ = v___x_985_;
v___y_917_ = v___x_955_;
v___y_918_ = v_query_980_;
v_host_919_ = v_host_983_;
v_port_920_ = v_port_984_;
v___y_921_ = v_scheme_978_;
v___y_922_ = v___x_954_;
v___y_923_ = v___x_956_;
v___y_924_ = v_fragment_981_;
v___y_925_ = v_path_979_;
v___y_926_ = v___x_957_;
v___y_927_ = v___x_992_;
goto v___jp_915_;
}
else
{
lean_object* v_username_993_; lean_object* v_val_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_inc_ref(v_password_988_);
v_username_993_ = lean_ctor_get(v_val_987_, 0);
lean_inc_ref(v_username_993_);
lean_dec(v_val_987_);
v_val_994_ = lean_ctor_get(v_password_988_, 0);
lean_inc(v_val_994_);
lean_dec_ref_known(v_password_988_, 1);
v___x_995_ = lean_string_from_utf8_unchecked(v_username_993_);
v___x_996_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_997_ = lean_string_append(v___x_995_, v___x_996_);
v___x_998_ = lean_string_from_utf8_unchecked(v_val_994_);
v___x_999_ = lean_string_append(v___x_997_, v___x_998_);
lean_dec_ref(v___x_998_);
v___x_1000_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_1001_ = lean_string_append(v___x_999_, v___x_1000_);
v___y_916_ = v___x_985_;
v___y_917_ = v___x_955_;
v___y_918_ = v_query_980_;
v_host_919_ = v_host_983_;
v_port_920_ = v_port_984_;
v___y_921_ = v_scheme_978_;
v___y_922_ = v___x_954_;
v___y_923_ = v___x_956_;
v___y_924_ = v_fragment_981_;
v___y_925_ = v_path_979_;
v___y_926_ = v___x_957_;
v___y_927_ = v___x_1001_;
goto v___jp_915_;
}
}
}
}
case 2:
{
lean_object* v_authority_1002_; lean_object* v_userInfo_1003_; 
lean_dec_ref(v___f_736_);
lean_dec_ref(v___f_735_);
v_authority_1002_ = lean_ctor_get(v_uri_741_, 0);
lean_inc_ref(v_authority_1002_);
lean_dec_ref_known(v_uri_741_, 1);
v_userInfo_1003_ = lean_ctor_get(v_authority_1002_, 0);
if (lean_obj_tag(v_userInfo_1003_) == 0)
{
lean_object* v_host_1004_; lean_object* v_port_1005_; lean_object* v___x_1006_; 
v_host_1004_ = lean_ctor_get(v_authority_1002_, 1);
lean_inc_ref(v_host_1004_);
v_port_1005_ = lean_ctor_get(v_authority_1002_, 2);
lean_inc(v_port_1005_);
lean_dec_ref(v_authority_1002_);
v___x_1006_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_810_ = v___x_955_;
v___y_811_ = v___x_954_;
v___y_812_ = v___x_956_;
v_host_813_ = v_host_1004_;
v_port_814_ = v_port_1005_;
v___y_815_ = v___x_957_;
v___y_816_ = v___x_1006_;
goto v___jp_809_;
}
else
{
lean_object* v_val_1007_; lean_object* v_password_1008_; 
v_val_1007_ = lean_ctor_get(v_userInfo_1003_, 0);
lean_inc(v_val_1007_);
v_password_1008_ = lean_ctor_get(v_val_1007_, 1);
if (lean_obj_tag(v_password_1008_) == 0)
{
lean_object* v_host_1009_; lean_object* v_port_1010_; lean_object* v_username_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_host_1009_ = lean_ctor_get(v_authority_1002_, 1);
lean_inc_ref(v_host_1009_);
v_port_1010_ = lean_ctor_get(v_authority_1002_, 2);
lean_inc(v_port_1010_);
lean_dec_ref(v_authority_1002_);
v_username_1011_ = lean_ctor_get(v_val_1007_, 0);
lean_inc_ref(v_username_1011_);
lean_dec(v_val_1007_);
v___x_1012_ = lean_string_from_utf8_unchecked(v_username_1011_);
v___x_1013_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_1014_ = lean_string_append(v___x_1012_, v___x_1013_);
v___y_810_ = v___x_955_;
v___y_811_ = v___x_954_;
v___y_812_ = v___x_956_;
v_host_813_ = v_host_1009_;
v_port_814_ = v_port_1010_;
v___y_815_ = v___x_957_;
v___y_816_ = v___x_1014_;
goto v___jp_809_;
}
else
{
lean_object* v_host_1015_; lean_object* v_port_1016_; lean_object* v_username_1017_; lean_object* v_val_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
lean_inc_ref(v_password_1008_);
v_host_1015_ = lean_ctor_get(v_authority_1002_, 1);
lean_inc_ref(v_host_1015_);
v_port_1016_ = lean_ctor_get(v_authority_1002_, 2);
lean_inc(v_port_1016_);
lean_dec_ref(v_authority_1002_);
v_username_1017_ = lean_ctor_get(v_val_1007_, 0);
lean_inc_ref(v_username_1017_);
lean_dec(v_val_1007_);
v_val_1018_ = lean_ctor_get(v_password_1008_, 0);
lean_inc(v_val_1018_);
lean_dec_ref_known(v_password_1008_, 1);
v___x_1019_ = lean_string_from_utf8_unchecked(v_username_1017_);
v___x_1020_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_1021_ = lean_string_append(v___x_1019_, v___x_1020_);
v___x_1022_ = lean_string_from_utf8_unchecked(v_val_1018_);
v___x_1023_ = lean_string_append(v___x_1021_, v___x_1022_);
lean_dec_ref(v___x_1022_);
v___x_1024_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_1025_ = lean_string_append(v___x_1023_, v___x_1024_);
v___y_810_ = v___x_955_;
v___y_811_ = v___x_954_;
v___y_812_ = v___x_956_;
v_host_813_ = v_host_1015_;
v_port_814_ = v_port_1016_;
v___y_815_ = v___x_957_;
v___y_816_ = v___x_1025_;
goto v___jp_809_;
}
}
}
default: 
{
lean_object* v___x_1026_; 
lean_dec_ref(v___f_736_);
lean_dec_ref(v___f_735_);
v___x_1026_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__23));
v___y_769_ = v___x_955_;
v___y_770_ = v___x_954_;
v___y_771_ = v___x_956_;
v___y_772_ = v___x_957_;
v___y_773_ = v___x_1026_;
goto v___jp_768_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__0(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; 
v___x_1072_ = l_Std_Http_Headers_empty;
v___x_1073_ = lean_box(3);
v___x_1074_ = 1;
v___x_1075_ = 8;
v___x_1076_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1076_, 0, v___x_1073_);
lean_ctor_set(v___x_1076_, 1, v___x_1072_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*2, v___x_1075_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*2 + 1, v___x_1074_);
return v___x_1076_;
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__1(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = l_Std_Http_Extensions_empty;
v___x_1078_ = lean_obj_once(&l_Std_Http_Request_new___closed__0, &l_Std_Http_Request_new___closed__0_once, _init_l_Std_Http_Request_new___closed__0);
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v___x_1077_);
return v___x_1079_;
}
}
static lean_object* _init_l_Std_Http_Request_new(void){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_obj_once(&l_Std_Http_Request_new___closed__1, &l_Std_Http_Request_new___closed__1_once, _init_l_Std_Http_Request_new___closed__1);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method(lean_object* v_builder_1081_, uint8_t v_method_1082_){
_start:
{
lean_object* v_line_1083_; lean_object* v_extensions_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1101_; 
v_line_1083_ = lean_ctor_get(v_builder_1081_, 0);
v_extensions_1084_ = lean_ctor_get(v_builder_1081_, 1);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_builder_1081_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1086_ = v_builder_1081_;
v_isShared_1087_ = v_isSharedCheck_1101_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_extensions_1084_);
lean_inc(v_line_1083_);
lean_dec(v_builder_1081_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1101_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
uint8_t v_version_1088_; lean_object* v_uri_1089_; lean_object* v_headers_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1100_; 
v_version_1088_ = lean_ctor_get_uint8(v_line_1083_, sizeof(void*)*2 + 1);
v_uri_1089_ = lean_ctor_get(v_line_1083_, 0);
v_headers_1090_ = lean_ctor_get(v_line_1083_, 1);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_line_1083_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1092_ = v_line_1083_;
v_isShared_1093_ = v_isSharedCheck_1100_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_headers_1090_);
lean_inc(v_uri_1089_);
lean_dec(v_line_1083_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1100_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_uri_1089_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_headers_1090_);
lean_ctor_set_uint8(v_reuseFailAlloc_1099_, sizeof(void*)*2 + 1, v_version_1088_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1097_; 
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*2, v_method_1082_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1095_);
v___x_1097_ = v___x_1086_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_extensions_1084_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method___boxed(lean_object* v_builder_1102_, lean_object* v_method_1103_){
_start:
{
uint8_t v_method_boxed_1104_; lean_object* v_res_1105_; 
v_method_boxed_1104_ = lean_unbox(v_method_1103_);
v_res_1105_ = l_Std_Http_Request_Builder_method(v_builder_1102_, v_method_boxed_1104_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version(lean_object* v_builder_1106_, uint8_t v_version_1107_){
_start:
{
lean_object* v_line_1108_; lean_object* v_extensions_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1126_; 
v_line_1108_ = lean_ctor_get(v_builder_1106_, 0);
v_extensions_1109_ = lean_ctor_get(v_builder_1106_, 1);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_builder_1106_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1111_ = v_builder_1106_;
v_isShared_1112_ = v_isSharedCheck_1126_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_extensions_1109_);
lean_inc(v_line_1108_);
lean_dec(v_builder_1106_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1126_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
uint8_t v_method_1113_; lean_object* v_uri_1114_; lean_object* v_headers_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1125_; 
v_method_1113_ = lean_ctor_get_uint8(v_line_1108_, sizeof(void*)*2);
v_uri_1114_ = lean_ctor_get(v_line_1108_, 0);
v_headers_1115_ = lean_ctor_get(v_line_1108_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_line_1108_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1117_ = v_line_1108_;
v_isShared_1118_ = v_isSharedCheck_1125_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_headers_1115_);
lean_inc(v_uri_1114_);
lean_dec(v_line_1108_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1125_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_uri_1114_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_headers_1115_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*2, v_method_1113_);
v___x_1120_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1122_; 
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*2 + 1, v_version_1107_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1120_);
v___x_1122_ = v___x_1111_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_extensions_1109_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version___boxed(lean_object* v_builder_1127_, lean_object* v_version_1128_){
_start:
{
uint8_t v_version_boxed_1129_; lean_object* v_res_1130_; 
v_version_boxed_1129_ = lean_unbox(v_version_1128_);
v_res_1130_ = l_Std_Http_Request_Builder_version(v_builder_1127_, v_version_boxed_1129_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri(lean_object* v_builder_1131_, lean_object* v_uri_1132_){
_start:
{
lean_object* v_line_1133_; lean_object* v_extensions_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1152_; 
v_line_1133_ = lean_ctor_get(v_builder_1131_, 0);
v_extensions_1134_ = lean_ctor_get(v_builder_1131_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_builder_1131_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1136_ = v_builder_1131_;
v_isShared_1137_ = v_isSharedCheck_1152_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_extensions_1134_);
lean_inc(v_line_1133_);
lean_dec(v_builder_1131_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1152_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
uint8_t v_method_1138_; uint8_t v_version_1139_; lean_object* v_headers_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1150_; 
v_method_1138_ = lean_ctor_get_uint8(v_line_1133_, sizeof(void*)*2);
v_version_1139_ = lean_ctor_get_uint8(v_line_1133_, sizeof(void*)*2 + 1);
v_headers_1140_ = lean_ctor_get(v_line_1133_, 1);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_line_1133_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v_line_1133_, 0);
lean_dec(v_unused_1151_);
v___x_1142_ = v_line_1133_;
v_isShared_1143_ = v_isSharedCheck_1150_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_headers_1140_);
lean_dec(v_line_1133_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1150_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v_uri_1132_);
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_uri_1132_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_headers_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, sizeof(void*)*2, v_method_1138_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, sizeof(void*)*2 + 1, v_version_1139_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1145_);
v___x_1147_ = v___x_1136_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_extensions_1134_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(lean_object* v_msg_1153_){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = l_Std_Http_instInhabitedRequestTarget_default;
v___x_1155_ = lean_panic_fn_borrowed(v___x_1154_, v_msg_1153_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___lam__0(lean_object* v___x_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_1159_, v___y_1160_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_pos_1162_; lean_object* v_array_1163_; lean_object* v_idx_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
v_pos_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_pos_1162_);
v_array_1163_ = lean_ctor_get(v_pos_1162_, 0);
v_idx_1164_ = lean_ctor_get(v_pos_1162_, 1);
v___x_1165_ = lean_byte_array_size(v_array_1163_);
v___x_1166_ = lean_nat_dec_lt(v_idx_1164_, v___x_1165_);
if (v___x_1166_ == 0)
{
lean_dec(v_pos_1162_);
return v___x_1161_;
}
else
{
lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1174_; 
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; lean_object* v_unused_1176_; 
v_unused_1175_ = lean_ctor_get(v___x_1161_, 1);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v___x_1161_, 0);
lean_dec(v_unused_1176_);
v___x_1168_ = v___x_1161_;
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
else
{
lean_dec(v___x_1161_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1170_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___lam__0___closed__1));
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 1);
lean_ctor_set(v___x_1168_, 1, v___x_1170_);
v___x_1172_ = v___x_1168_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_pos_1162_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
else
{
return v___x_1161_;
}
}
}
static lean_object* _init_l_Std_Http_Request_Builder_uri_x21___closed__5(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1190_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__4));
v___x_1191_ = lean_unsigned_to_nat(12u);
v___x_1192_ = lean_unsigned_to_nat(45u);
v___x_1193_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__3));
v___x_1194_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__2));
v___x_1195_ = l_mkPanicMessageWithDecl(v___x_1194_, v___x_1193_, v___x_1192_, v___x_1191_, v___x_1190_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21(lean_object* v_builder_1196_, lean_object* v_uri_1197_){
_start:
{
lean_object* v___y_1199_; lean_object* v___f_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___f_1220_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__1));
v___x_1221_ = lean_string_to_utf8(v_uri_1197_);
v___x_1222_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1220_, v___x_1221_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec_ref_known(v___x_1222_, 1);
v___x_1223_ = lean_obj_once(&l_Std_Http_Request_Builder_uri_x21___closed__5, &l_Std_Http_Request_Builder_uri_x21___closed__5_once, _init_l_Std_Http_Request_Builder_uri_x21___closed__5);
v___x_1224_ = l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(v___x_1223_);
v___y_1199_ = v___x_1224_;
goto v___jp_1198_;
}
else
{
lean_object* v_a_1225_; 
v_a_1225_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1222_, 1);
v___y_1199_ = v_a_1225_;
goto v___jp_1198_;
}
v___jp_1198_:
{
lean_object* v_line_1200_; lean_object* v_extensions_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1219_; 
v_line_1200_ = lean_ctor_get(v_builder_1196_, 0);
v_extensions_1201_ = lean_ctor_get(v_builder_1196_, 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_builder_1196_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1203_ = v_builder_1196_;
v_isShared_1204_ = v_isSharedCheck_1219_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_extensions_1201_);
lean_inc(v_line_1200_);
lean_dec(v_builder_1196_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1219_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
uint8_t v_method_1205_; uint8_t v_version_1206_; lean_object* v_headers_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1217_; 
v_method_1205_ = lean_ctor_get_uint8(v_line_1200_, sizeof(void*)*2);
v_version_1206_ = lean_ctor_get_uint8(v_line_1200_, sizeof(void*)*2 + 1);
v_headers_1207_ = lean_ctor_get(v_line_1200_, 1);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_line_1200_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v_line_1200_, 0);
lean_dec(v_unused_1218_);
v___x_1209_ = v_line_1200_;
v_isShared_1210_ = v_isSharedCheck_1217_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_headers_1207_);
lean_dec(v_line_1200_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1217_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v___y_1199_);
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___y_1199_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_headers_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1216_, sizeof(void*)*2, v_method_1205_);
lean_ctor_set_uint8(v_reuseFailAlloc_1216_, sizeof(void*)*2 + 1, v_version_1206_);
v___x_1212_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1214_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1212_);
v___x_1214_ = v___x_1203_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_extensions_1201_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___boxed(lean_object* v_builder_1226_, lean_object* v_uri_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Std_Http_Request_Builder_uri_x21(v_builder_1226_, v_uri_1227_);
lean_dec_ref(v_uri_1227_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headers(lean_object* v_builder_1229_, lean_object* v_headers_1230_){
_start:
{
lean_object* v_line_1231_; lean_object* v_extensions_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1250_; 
v_line_1231_ = lean_ctor_get(v_builder_1229_, 0);
v_extensions_1232_ = lean_ctor_get(v_builder_1229_, 1);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_builder_1229_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1234_ = v_builder_1229_;
v_isShared_1235_ = v_isSharedCheck_1250_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_extensions_1232_);
lean_inc(v_line_1231_);
lean_dec(v_builder_1229_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1250_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
uint8_t v_method_1236_; uint8_t v_version_1237_; lean_object* v_uri_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1248_; 
v_method_1236_ = lean_ctor_get_uint8(v_line_1231_, sizeof(void*)*2);
v_version_1237_ = lean_ctor_get_uint8(v_line_1231_, sizeof(void*)*2 + 1);
v_uri_1238_ = lean_ctor_get(v_line_1231_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_line_1231_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v_line_1231_, 1);
lean_dec(v_unused_1249_);
v___x_1240_ = v_line_1231_;
v_isShared_1241_ = v_isSharedCheck_1248_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_uri_1238_);
lean_dec(v_line_1231_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1248_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 1, v_headers_1230_);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_uri_1238_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_headers_1230_);
lean_ctor_set_uint8(v_reuseFailAlloc_1247_, sizeof(void*)*2, v_method_1236_);
lean_ctor_set_uint8(v_reuseFailAlloc_1247_, sizeof(void*)*2 + 1, v_version_1237_);
v___x_1243_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1245_; 
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1243_);
v___x_1245_ = v___x_1234_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_extensions_1232_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(lean_object* v_i_1251_, lean_object* v_x_1252_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1253_ = lean_unsigned_to_nat(1u);
v___x_1254_ = lean_mk_empty_array_with_capacity(v___x_1253_);
v___x_1255_ = lean_array_push(v___x_1254_, v_i_1251_);
v___x_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
else
{
lean_object* v_val_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1265_; 
v_val_1257_ = lean_ctor_get(v_x_1252_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_x_1252_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1259_ = v_x_1252_;
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_val_1257_);
lean_dec(v_x_1252_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = lean_array_push(v_val_1257_, v_i_1251_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1261_);
v___x_1263_ = v___x_1259_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(lean_object* v_i_1266_, lean_object* v_a_1267_, lean_object* v_x_1268_){
_start:
{
if (lean_obj_tag(v_x_1268_) == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v_val_1271_; lean_object* v___x_1272_; 
v___x_1269_ = lean_box(0);
v___x_1270_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(v_i_1266_, v___x_1269_);
v_val_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_val_1271_);
lean_dec(v___x_1270_);
v___x_1272_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1272_, 0, v_a_1267_);
lean_ctor_set(v___x_1272_, 1, v_val_1271_);
lean_ctor_set(v___x_1272_, 2, v_x_1268_);
return v___x_1272_;
}
else
{
lean_object* v_key_1273_; lean_object* v_value_1274_; lean_object* v_tail_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1290_; 
v_key_1273_ = lean_ctor_get(v_x_1268_, 0);
v_value_1274_ = lean_ctor_get(v_x_1268_, 1);
v_tail_1275_ = lean_ctor_get(v_x_1268_, 2);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_x_1268_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1277_ = v_x_1268_;
v_isShared_1278_ = v_isSharedCheck_1290_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_tail_1275_);
lean_inc(v_value_1274_);
lean_inc(v_key_1273_);
lean_dec(v_x_1268_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1290_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
uint8_t v___x_1279_; 
v___x_1279_ = lean_string_dec_eq(v_key_1273_, v_a_1267_);
if (v___x_1279_ == 0)
{
lean_object* v_tail_1280_; lean_object* v___x_1282_; 
v_tail_1280_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_1266_, v_a_1267_, v_tail_1275_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 2, v_tail_1280_);
v___x_1282_ = v___x_1277_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_key_1273_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_value_1274_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v_tail_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v_val_1286_; lean_object* v___x_1288_; 
lean_dec(v_key_1273_);
v___x_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1284_, 0, v_value_1274_);
v___x_1285_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(v_i_1266_, v___x_1284_);
v_val_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_val_1286_);
lean_dec(v___x_1285_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v_val_1286_);
lean_ctor_set(v___x_1277_, 0, v_a_1267_);
v___x_1288_ = v___x_1277_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1267_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_val_1286_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_tail_1275_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(lean_object* v_a_1291_, lean_object* v_x_1292_){
_start:
{
if (lean_obj_tag(v_x_1292_) == 0)
{
uint8_t v___x_1293_; 
v___x_1293_ = 0;
return v___x_1293_;
}
else
{
lean_object* v_key_1294_; lean_object* v_tail_1295_; uint8_t v___x_1296_; 
v_key_1294_ = lean_ctor_get(v_x_1292_, 0);
v_tail_1295_ = lean_ctor_get(v_x_1292_, 2);
v___x_1296_ = lean_string_dec_eq(v_key_1294_, v_a_1291_);
if (v___x_1296_ == 0)
{
v_x_1292_ = v_tail_1295_;
goto _start;
}
else
{
return v___x_1296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg___boxed(lean_object* v_a_1298_, lean_object* v_x_1299_){
_start:
{
uint8_t v_res_1300_; lean_object* v_r_1301_; 
v_res_1300_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1298_, v_x_1299_);
lean_dec(v_x_1299_);
lean_dec_ref(v_a_1298_);
v_r_1301_ = lean_box(v_res_1300_);
return v_r_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1302_, lean_object* v_x_1303_){
_start:
{
if (lean_obj_tag(v_x_1303_) == 0)
{
return v_x_1302_;
}
else
{
lean_object* v_key_1304_; lean_object* v_value_1305_; lean_object* v_tail_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1329_; 
v_key_1304_ = lean_ctor_get(v_x_1303_, 0);
v_value_1305_ = lean_ctor_get(v_x_1303_, 1);
v_tail_1306_ = lean_ctor_get(v_x_1303_, 2);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_x_1303_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1308_ = v_x_1303_;
v_isShared_1309_ = v_isSharedCheck_1329_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_tail_1306_);
lean_inc(v_value_1305_);
lean_inc(v_key_1304_);
lean_dec(v_x_1303_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1329_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; uint64_t v___x_1311_; uint64_t v___x_1312_; uint64_t v___x_1313_; uint64_t v_fold_1314_; uint64_t v___x_1315_; uint64_t v___x_1316_; uint64_t v___x_1317_; size_t v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1310_ = lean_array_get_size(v_x_1302_);
v___x_1311_ = lean_string_hash(v_key_1304_);
v___x_1312_ = 32ULL;
v___x_1313_ = lean_uint64_shift_right(v___x_1311_, v___x_1312_);
v_fold_1314_ = lean_uint64_xor(v___x_1311_, v___x_1313_);
v___x_1315_ = 16ULL;
v___x_1316_ = lean_uint64_shift_right(v_fold_1314_, v___x_1315_);
v___x_1317_ = lean_uint64_xor(v_fold_1314_, v___x_1316_);
v___x_1318_ = lean_uint64_to_usize(v___x_1317_);
v___x_1319_ = lean_usize_of_nat(v___x_1310_);
v___x_1320_ = ((size_t)1ULL);
v___x_1321_ = lean_usize_sub(v___x_1319_, v___x_1320_);
v___x_1322_ = lean_usize_land(v___x_1318_, v___x_1321_);
v___x_1323_ = lean_array_uget_borrowed(v_x_1302_, v___x_1322_);
lean_inc(v___x_1323_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 2, v___x_1323_);
v___x_1325_ = v___x_1308_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_key_1304_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_value_1305_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_array_uset(v_x_1302_, v___x_1322_, v___x_1325_);
v_x_1302_ = v___x_1326_;
v_x_1303_ = v_tail_1306_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1330_, lean_object* v_source_1331_, lean_object* v_target_1332_){
_start:
{
lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1333_ = lean_array_get_size(v_source_1331_);
v___x_1334_ = lean_nat_dec_lt(v_i_1330_, v___x_1333_);
if (v___x_1334_ == 0)
{
lean_dec_ref(v_source_1331_);
lean_dec(v_i_1330_);
return v_target_1332_;
}
else
{
lean_object* v_es_1335_; lean_object* v___x_1336_; lean_object* v_source_1337_; lean_object* v_target_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_es_1335_ = lean_array_fget(v_source_1331_, v_i_1330_);
v___x_1336_ = lean_box(0);
v_source_1337_ = lean_array_fset(v_source_1331_, v_i_1330_, v___x_1336_);
v_target_1338_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1332_, v_es_1335_);
v___x_1339_ = lean_unsigned_to_nat(1u);
v___x_1340_ = lean_nat_add(v_i_1330_, v___x_1339_);
lean_dec(v_i_1330_);
v_i_1330_ = v___x_1340_;
v_source_1331_ = v_source_1337_;
v_target_1332_ = v_target_1338_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(lean_object* v_data_1342_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v_nbuckets_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1343_ = lean_array_get_size(v_data_1342_);
v___x_1344_ = lean_unsigned_to_nat(2u);
v_nbuckets_1345_ = lean_nat_mul(v___x_1343_, v___x_1344_);
v___x_1346_ = lean_unsigned_to_nat(0u);
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_mk_array(v_nbuckets_1345_, v___x_1347_);
v___x_1349_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v___x_1346_, v_data_1342_, v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(lean_object* v_i_1350_, lean_object* v_m_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_size_1353_; lean_object* v_buckets_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1404_; 
v_size_1353_ = lean_ctor_get(v_m_1351_, 0);
v_buckets_1354_ = lean_ctor_get(v_m_1351_, 1);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_m_1351_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1356_ = v_m_1351_;
v_isShared_1357_ = v_isSharedCheck_1404_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_buckets_1354_);
lean_inc(v_size_1353_);
lean_dec(v_m_1351_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1404_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; uint64_t v___x_1359_; uint64_t v___x_1360_; uint64_t v___x_1361_; uint64_t v_fold_1362_; uint64_t v___x_1363_; uint64_t v___x_1364_; uint64_t v___x_1365_; size_t v___x_1366_; size_t v___x_1367_; size_t v___x_1368_; size_t v___x_1369_; size_t v___x_1370_; lean_object* v_bkt_1371_; uint8_t v___x_1372_; 
v___x_1358_ = lean_array_get_size(v_buckets_1354_);
v___x_1359_ = lean_string_hash(v_a_1352_);
v___x_1360_ = 32ULL;
v___x_1361_ = lean_uint64_shift_right(v___x_1359_, v___x_1360_);
v_fold_1362_ = lean_uint64_xor(v___x_1359_, v___x_1361_);
v___x_1363_ = 16ULL;
v___x_1364_ = lean_uint64_shift_right(v_fold_1362_, v___x_1363_);
v___x_1365_ = lean_uint64_xor(v_fold_1362_, v___x_1364_);
v___x_1366_ = lean_uint64_to_usize(v___x_1365_);
v___x_1367_ = lean_usize_of_nat(v___x_1358_);
v___x_1368_ = ((size_t)1ULL);
v___x_1369_ = lean_usize_sub(v___x_1367_, v___x_1368_);
v___x_1370_ = lean_usize_land(v___x_1366_, v___x_1369_);
v_bkt_1371_ = lean_array_uget_borrowed(v_buckets_1354_, v___x_1370_);
v___x_1372_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1352_, v_bkt_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v_size_x27_1376_; lean_object* v___x_1377_; lean_object* v_buckets_x27_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; 
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = lean_mk_empty_array_with_capacity(v___x_1373_);
v___x_1375_ = lean_array_push(v___x_1374_, v_i_1350_);
v_size_x27_1376_ = lean_nat_add(v_size_1353_, v___x_1373_);
lean_dec(v_size_1353_);
lean_inc(v_bkt_1371_);
v___x_1377_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1377_, 0, v_a_1352_);
lean_ctor_set(v___x_1377_, 1, v___x_1375_);
lean_ctor_set(v___x_1377_, 2, v_bkt_1371_);
v_buckets_x27_1378_ = lean_array_uset(v_buckets_1354_, v___x_1370_, v___x_1377_);
v___x_1379_ = lean_unsigned_to_nat(4u);
v___x_1380_ = lean_nat_mul(v_size_x27_1376_, v___x_1379_);
v___x_1381_ = lean_unsigned_to_nat(3u);
v___x_1382_ = lean_nat_div(v___x_1380_, v___x_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_array_get_size(v_buckets_x27_1378_);
v___x_1384_ = lean_nat_dec_le(v___x_1382_, v___x_1383_);
lean_dec(v___x_1382_);
if (v___x_1384_ == 0)
{
lean_object* v_val_1385_; lean_object* v___x_1387_; 
v_val_1385_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_buckets_x27_1378_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v_val_1385_);
lean_ctor_set(v___x_1356_, 0, v_size_x27_1376_);
v___x_1387_ = v___x_1356_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_size_x27_1376_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_val_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
else
{
lean_object* v___x_1390_; 
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v_buckets_x27_1378_);
lean_ctor_set(v___x_1356_, 0, v_size_x27_1376_);
v___x_1390_ = v___x_1356_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_size_x27_1376_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_buckets_x27_1378_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
lean_object* v___x_1392_; lean_object* v_buckets_x27_1393_; lean_object* v_bkt_x27_1394_; lean_object* v___y_1396_; uint8_t v___x_1401_; 
lean_inc(v_bkt_1371_);
v___x_1392_ = lean_box(0);
v_buckets_x27_1393_ = lean_array_uset(v_buckets_1354_, v___x_1370_, v___x_1392_);
lean_inc_ref(v_a_1352_);
v_bkt_x27_1394_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_1350_, v_a_1352_, v_bkt_1371_);
v___x_1401_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1352_, v_bkt_x27_1394_);
lean_dec_ref(v_a_1352_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_unsigned_to_nat(1u);
v___x_1403_ = lean_nat_sub(v_size_1353_, v___x_1402_);
lean_dec(v_size_1353_);
v___y_1396_ = v___x_1403_;
goto v___jp_1395_;
}
else
{
v___y_1396_ = v_size_1353_;
goto v___jp_1395_;
}
v___jp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1397_ = lean_array_uset(v_buckets_x27_1393_, v___x_1370_, v_bkt_x27_1394_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v___x_1397_);
lean_ctor_set(v___x_1356_, 0, v___y_1396_);
v___x_1399_ = v___x_1356_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___y_1396_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header(lean_object* v_builder_1405_, lean_object* v_key_1406_, lean_object* v_value_1407_){
_start:
{
lean_object* v_line_1408_; lean_object* v_headers_1409_; lean_object* v_extensions_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1441_; 
v_line_1408_ = lean_ctor_get(v_builder_1405_, 0);
lean_inc_ref(v_line_1408_);
v_headers_1409_ = lean_ctor_get(v_line_1408_, 1);
lean_inc_ref(v_headers_1409_);
v_extensions_1410_ = lean_ctor_get(v_builder_1405_, 1);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_builder_1405_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; 
v_unused_1442_ = lean_ctor_get(v_builder_1405_, 0);
lean_dec(v_unused_1442_);
v___x_1412_ = v_builder_1405_;
v_isShared_1413_ = v_isSharedCheck_1441_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_extensions_1410_);
lean_dec(v_builder_1405_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1441_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
uint8_t v_method_1414_; uint8_t v_version_1415_; lean_object* v_uri_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1439_; 
v_method_1414_ = lean_ctor_get_uint8(v_line_1408_, sizeof(void*)*2);
v_version_1415_ = lean_ctor_get_uint8(v_line_1408_, sizeof(void*)*2 + 1);
v_uri_1416_ = lean_ctor_get(v_line_1408_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_line_1408_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v_line_1408_, 1);
lean_dec(v_unused_1440_);
v___x_1418_ = v_line_1408_;
v_isShared_1419_ = v_isSharedCheck_1439_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_uri_1416_);
lean_dec(v_line_1408_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1439_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_entries_1420_; lean_object* v_indexes_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1438_; 
v_entries_1420_ = lean_ctor_get(v_headers_1409_, 0);
v_indexes_1421_ = lean_ctor_get(v_headers_1409_, 1);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_headers_1409_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1423_ = v_headers_1409_;
v_isShared_1424_ = v_isSharedCheck_1438_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_indexes_1421_);
lean_inc(v_entries_1420_);
lean_dec(v_headers_1409_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1438_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v_i_1425_; lean_object* v___x_1426_; lean_object* v_entries_1427_; lean_object* v_indexes_1428_; lean_object* v___x_1430_; 
v_i_1425_ = lean_array_get_size(v_entries_1420_);
lean_inc_ref(v_key_1406_);
v___x_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1426_, 0, v_key_1406_);
lean_ctor_set(v___x_1426_, 1, v_value_1407_);
v_entries_1427_ = lean_array_push(v_entries_1420_, v___x_1426_);
v_indexes_1428_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1425_, v_indexes_1421_, v_key_1406_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v_indexes_1428_);
lean_ctor_set(v___x_1423_, 0, v_entries_1427_);
v___x_1430_ = v___x_1423_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_entries_1427_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_indexes_1428_);
v___x_1430_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1432_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v___x_1430_);
v___x_1432_ = v___x_1418_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_uri_1416_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v___x_1430_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, sizeof(void*)*2, v_method_1414_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, sizeof(void*)*2 + 1, v_version_1415_);
v___x_1432_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1434_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1432_);
v___x_1434_ = v___x_1412_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_extensions_1410_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(lean_object* v_00_u03b2_1443_, lean_object* v_a_1444_, lean_object* v_x_1445_){
_start:
{
uint8_t v___x_1446_; 
v___x_1446_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1444_, v_x_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1447_, lean_object* v_a_1448_, lean_object* v_x_1449_){
_start:
{
uint8_t v_res_1450_; lean_object* v_r_1451_; 
v_res_1450_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(v_00_u03b2_1447_, v_a_1448_, v_x_1449_);
lean_dec(v_x_1449_);
lean_dec_ref(v_a_1448_);
v_r_1451_ = lean_box(v_res_1450_);
return v_r_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1(lean_object* v_00_u03b2_1452_, lean_object* v_data_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_data_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1455_, lean_object* v_i_1456_, lean_object* v_source_1457_, lean_object* v_target_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v_i_1456_, v_source_1457_, v_target_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1461_, v_x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x21(lean_object* v_builder_1464_, lean_object* v_key_1465_, lean_object* v_value_1466_){
_start:
{
lean_object* v_line_1467_; lean_object* v_headers_1468_; lean_object* v_extensions_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1502_; 
v_line_1467_ = lean_ctor_get(v_builder_1464_, 0);
lean_inc_ref(v_line_1467_);
v_headers_1468_ = lean_ctor_get(v_line_1467_, 1);
lean_inc_ref(v_headers_1468_);
v_extensions_1469_ = lean_ctor_get(v_builder_1464_, 1);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_builder_1464_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; 
v_unused_1503_ = lean_ctor_get(v_builder_1464_, 0);
lean_dec(v_unused_1503_);
v___x_1471_ = v_builder_1464_;
v_isShared_1472_ = v_isSharedCheck_1502_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_extensions_1469_);
lean_dec(v_builder_1464_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1502_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
uint8_t v_method_1473_; uint8_t v_version_1474_; lean_object* v_uri_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1500_; 
v_method_1473_ = lean_ctor_get_uint8(v_line_1467_, sizeof(void*)*2);
v_version_1474_ = lean_ctor_get_uint8(v_line_1467_, sizeof(void*)*2 + 1);
v_uri_1475_ = lean_ctor_get(v_line_1467_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_line_1467_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v_line_1467_, 1);
lean_dec(v_unused_1501_);
v___x_1477_ = v_line_1467_;
v_isShared_1478_ = v_isSharedCheck_1500_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_uri_1475_);
lean_dec(v_line_1467_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1500_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v_entries_1479_; lean_object* v_indexes_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1499_; 
v_entries_1479_ = lean_ctor_get(v_headers_1468_, 0);
v_indexes_1480_ = lean_ctor_get(v_headers_1468_, 1);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_headers_1468_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1482_ = v_headers_1468_;
v_isShared_1483_ = v_isSharedCheck_1499_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_indexes_1480_);
lean_inc(v_entries_1479_);
lean_dec(v_headers_1468_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1499_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v_key_1484_; lean_object* v_value_1485_; lean_object* v_i_1486_; lean_object* v___x_1487_; lean_object* v_entries_1488_; lean_object* v_indexes_1489_; lean_object* v___x_1491_; 
v_key_1484_ = l_Std_Http_Header_Name_ofString_x21(v_key_1465_);
v_value_1485_ = l_Std_Http_Header_Value_ofString_x21(v_value_1466_);
v_i_1486_ = lean_array_get_size(v_entries_1479_);
lean_inc_ref(v_key_1484_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v_key_1484_);
lean_ctor_set(v___x_1487_, 1, v_value_1485_);
v_entries_1488_ = lean_array_push(v_entries_1479_, v___x_1487_);
v_indexes_1489_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1486_, v_indexes_1480_, v_key_1484_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v_indexes_1489_);
lean_ctor_set(v___x_1482_, 0, v_entries_1488_);
v___x_1491_ = v___x_1482_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_entries_1488_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_indexes_1489_);
v___x_1491_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 1, v___x_1491_);
v___x_1493_ = v___x_1477_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_uri_1475_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v___x_1491_);
lean_ctor_set_uint8(v_reuseFailAlloc_1497_, sizeof(void*)*2, v_method_1473_);
lean_ctor_set_uint8(v_reuseFailAlloc_1497_, sizeof(void*)*2 + 1, v_version_1474_);
v___x_1493_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1493_);
v___x_1495_ = v___x_1471_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_extensions_1469_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x3f(lean_object* v_builder_1504_, lean_object* v_key_1505_, lean_object* v_value_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Std_Http_Header_Name_ofString_x3f(v_key_1505_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v___x_1508_; 
lean_dec_ref(v_value_1506_);
lean_dec_ref(v_builder_1504_);
v___x_1508_ = lean_box(0);
return v___x_1508_;
}
else
{
lean_object* v_val_1509_; lean_object* v___x_1510_; 
v_val_1509_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_val_1509_);
lean_dec_ref_known(v___x_1507_, 1);
v___x_1510_ = l_Std_Http_Header_Value_ofString_x3f(v_value_1506_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v___x_1511_; 
lean_dec(v_val_1509_);
lean_dec_ref(v_builder_1504_);
v___x_1511_ = lean_box(0);
return v___x_1511_;
}
else
{
lean_object* v_line_1512_; lean_object* v_headers_1513_; lean_object* v_val_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1554_; 
v_line_1512_ = lean_ctor_get(v_builder_1504_, 0);
lean_inc_ref(v_line_1512_);
v_headers_1513_ = lean_ctor_get(v_line_1512_, 1);
lean_inc_ref(v_headers_1513_);
v_val_1514_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1516_ = v___x_1510_;
v_isShared_1517_ = v_isSharedCheck_1554_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_val_1514_);
lean_dec(v___x_1510_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1554_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v_extensions_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1552_; 
v_extensions_1518_ = lean_ctor_get(v_builder_1504_, 1);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_builder_1504_);
if (v_isSharedCheck_1552_ == 0)
{
lean_object* v_unused_1553_; 
v_unused_1553_ = lean_ctor_get(v_builder_1504_, 0);
lean_dec(v_unused_1553_);
v___x_1520_ = v_builder_1504_;
v_isShared_1521_ = v_isSharedCheck_1552_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_extensions_1518_);
lean_dec(v_builder_1504_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1552_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
uint8_t v_method_1522_; uint8_t v_version_1523_; lean_object* v_uri_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1550_; 
v_method_1522_ = lean_ctor_get_uint8(v_line_1512_, sizeof(void*)*2);
v_version_1523_ = lean_ctor_get_uint8(v_line_1512_, sizeof(void*)*2 + 1);
v_uri_1524_ = lean_ctor_get(v_line_1512_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_line_1512_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v_line_1512_, 1);
lean_dec(v_unused_1551_);
v___x_1526_ = v_line_1512_;
v_isShared_1527_ = v_isSharedCheck_1550_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_uri_1524_);
lean_dec(v_line_1512_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1550_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v_entries_1528_; lean_object* v_indexes_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1549_; 
v_entries_1528_ = lean_ctor_get(v_headers_1513_, 0);
v_indexes_1529_ = lean_ctor_get(v_headers_1513_, 1);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_headers_1513_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1531_ = v_headers_1513_;
v_isShared_1532_ = v_isSharedCheck_1549_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_indexes_1529_);
lean_inc(v_entries_1528_);
lean_dec(v_headers_1513_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1549_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_i_1533_; lean_object* v___x_1534_; lean_object* v_entries_1535_; lean_object* v_indexes_1536_; lean_object* v___x_1538_; 
v_i_1533_ = lean_array_get_size(v_entries_1528_);
lean_inc(v_val_1509_);
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v_val_1509_);
lean_ctor_set(v___x_1534_, 1, v_val_1514_);
v_entries_1535_ = lean_array_push(v_entries_1528_, v___x_1534_);
v_indexes_1536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1533_, v_indexes_1529_, v_val_1509_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 1, v_indexes_1536_);
lean_ctor_set(v___x_1531_, 0, v_entries_1535_);
v___x_1538_ = v___x_1531_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_entries_1535_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_indexes_1536_);
v___x_1538_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1540_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 1, v___x_1538_);
v___x_1540_ = v___x_1526_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_uri_1524_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1538_);
lean_ctor_set_uint8(v_reuseFailAlloc_1547_, sizeof(void*)*2, v_method_1522_);
lean_ctor_set_uint8(v_reuseFailAlloc_1547_, sizeof(void*)*2 + 1, v_version_1523_);
v___x_1540_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1542_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1540_);
v___x_1542_ = v___x_1520_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_extensions_1518_);
v___x_1542_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1544_; 
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1542_);
v___x_1544_ = v___x_1516_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
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
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headerOpt(lean_object* v_builder_1555_, lean_object* v_key_1556_, lean_object* v_value_1557_){
_start:
{
if (lean_obj_tag(v_value_1557_) == 0)
{
lean_dec_ref(v_key_1556_);
return v_builder_1555_;
}
else
{
lean_object* v_val_1558_; lean_object* v___x_1559_; 
v_val_1558_ = lean_ctor_get(v_value_1557_, 0);
lean_inc(v_val_1558_);
lean_dec_ref_known(v_value_1557_, 1);
v___x_1559_ = l_Std_Http_Request_Builder_header(v_builder_1555_, v_key_1556_, v_val_1558_);
return v___x_1559_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension___redArg(lean_object* v_builder_1561_, lean_object* v_inst_1562_, lean_object* v_data_1563_){
_start:
{
lean_object* v_line_1564_; lean_object* v_extensions_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1576_; 
v_line_1564_ = lean_ctor_get(v_builder_1561_, 0);
v_extensions_1565_ = lean_ctor_get(v_builder_1561_, 1);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_builder_1561_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1567_ = v_builder_1561_;
v_isShared_1568_ = v_isSharedCheck_1576_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_extensions_1565_);
lean_inc(v_line_1564_);
lean_dec(v_builder_1561_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1576_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v_dyn_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
v_dyn_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_1569_, 0, v_inst_1562_);
lean_ctor_set(v_dyn_1569_, 1, v_data_1563_);
v___x_1570_ = ((lean_object*)(l_Std_Http_Request_Builder_extension___redArg___closed__0));
v___x_1571_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_1569_);
v___x_1572_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1570_, v___x_1571_, v_dyn_1569_, v_extensions_1565_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 1, v___x_1572_);
v___x_1574_ = v___x_1567_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_line_1564_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension(lean_object* v_00_u03b1_1577_, lean_object* v_builder_1578_, lean_object* v_inst_1579_, lean_object* v_data_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Std_Http_Request_Builder_extension___redArg(v_builder_1578_, v_inst_1579_, v_data_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object* v_builder_1582_, lean_object* v_body_1583_){
_start:
{
lean_object* v_line_1584_; lean_object* v_extensions_1585_; lean_object* v___x_1586_; 
v_line_1584_ = lean_ctor_get(v_builder_1582_, 0);
v_extensions_1585_ = lean_ctor_get(v_builder_1582_, 1);
lean_inc(v_extensions_1585_);
lean_inc_ref(v_line_1584_);
v___x_1586_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1586_, 0, v_line_1584_);
lean_ctor_set(v___x_1586_, 1, v_body_1583_);
lean_ctor_set(v___x_1586_, 2, v_extensions_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg___boxed(lean_object* v_builder_1587_, lean_object* v_body_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1587_, v_body_1588_);
lean_dec_ref(v_builder_1587_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body(lean_object* v_t_1590_, lean_object* v_builder_1591_, lean_object* v_body_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1591_, v_body_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___boxed(lean_object* v_t_1594_, lean_object* v_builder_1595_, lean_object* v_body_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Std_Http_Request_Builder_body(v_t_1594_, v_builder_1595_, v_body_1596_);
lean_dec_ref(v_builder_1595_);
return v_res_1597_;
}
}
static lean_object* _init_l_Std_Http_Request_get___closed__0(void){
_start:
{
uint8_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = 8;
v___x_1599_ = l_Std_Http_Request_new;
v___x_1600_ = l_Std_Http_Request_Builder_method(v___x_1599_, v___x_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_get(lean_object* v_uri_1601_){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_obj_once(&l_Std_Http_Request_get___closed__0, &l_Std_Http_Request_get___closed__0_once, _init_l_Std_Http_Request_get___closed__0);
v___x_1603_ = l_Std_Http_Request_Builder_uri(v___x_1602_, v_uri_1601_);
return v___x_1603_;
}
}
static lean_object* _init_l_Std_Http_Request_post___closed__0(void){
_start:
{
uint8_t v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1604_ = 23;
v___x_1605_ = l_Std_Http_Request_new;
v___x_1606_ = l_Std_Http_Request_Builder_method(v___x_1605_, v___x_1604_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_post(lean_object* v_uri_1607_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = lean_obj_once(&l_Std_Http_Request_post___closed__0, &l_Std_Http_Request_post___closed__0_once, _init_l_Std_Http_Request_post___closed__0);
v___x_1609_ = l_Std_Http_Request_Builder_uri(v___x_1608_, v_uri_1607_);
return v___x_1609_;
}
}
static lean_object* _init_l_Std_Http_Request_put___closed__0(void){
_start:
{
uint8_t v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1610_ = 27;
v___x_1611_ = l_Std_Http_Request_new;
v___x_1612_ = l_Std_Http_Request_Builder_method(v___x_1611_, v___x_1610_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_put(lean_object* v_uri_1613_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_obj_once(&l_Std_Http_Request_put___closed__0, &l_Std_Http_Request_put___closed__0_once, _init_l_Std_Http_Request_put___closed__0);
v___x_1615_ = l_Std_Http_Request_Builder_uri(v___x_1614_, v_uri_1613_);
return v___x_1615_;
}
}
static lean_object* _init_l_Std_Http_Request_delete___closed__0(void){
_start:
{
uint8_t v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = 7;
v___x_1617_ = l_Std_Http_Request_new;
v___x_1618_ = l_Std_Http_Request_Builder_method(v___x_1617_, v___x_1616_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_delete(lean_object* v_uri_1619_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_obj_once(&l_Std_Http_Request_delete___closed__0, &l_Std_Http_Request_delete___closed__0_once, _init_l_Std_Http_Request_delete___closed__0);
v___x_1621_ = l_Std_Http_Request_Builder_uri(v___x_1620_, v_uri_1619_);
return v___x_1621_;
}
}
static lean_object* _init_l_Std_Http_Request_patch___closed__0(void){
_start:
{
uint8_t v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1622_ = 22;
v___x_1623_ = l_Std_Http_Request_new;
v___x_1624_ = l_Std_Http_Request_Builder_method(v___x_1623_, v___x_1622_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_patch(lean_object* v_uri_1625_){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = lean_obj_once(&l_Std_Http_Request_patch___closed__0, &l_Std_Http_Request_patch___closed__0_once, _init_l_Std_Http_Request_patch___closed__0);
v___x_1627_ = l_Std_Http_Request_Builder_uri(v___x_1626_, v_uri_1625_);
return v___x_1627_;
}
}
static lean_object* _init_l_Std_Http_Request_head___closed__0(void){
_start:
{
uint8_t v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = 9;
v___x_1629_ = l_Std_Http_Request_new;
v___x_1630_ = l_Std_Http_Request_Builder_method(v___x_1629_, v___x_1628_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_head(lean_object* v_uri_1631_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = lean_obj_once(&l_Std_Http_Request_head___closed__0, &l_Std_Http_Request_head___closed__0_once, _init_l_Std_Http_Request_head___closed__0);
v___x_1633_ = l_Std_Http_Request_Builder_uri(v___x_1632_, v_uri_1631_);
return v___x_1633_;
}
}
static lean_object* _init_l_Std_Http_Request_options___closed__0(void){
_start:
{
uint8_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = 20;
v___x_1635_ = l_Std_Http_Request_new;
v___x_1636_ = l_Std_Http_Request_Builder_method(v___x_1635_, v___x_1634_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_options(lean_object* v_uri_1637_){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = lean_obj_once(&l_Std_Http_Request_options___closed__0, &l_Std_Http_Request_options___closed__0_once, _init_l_Std_Http_Request_options___closed__0);
v___x_1639_ = l_Std_Http_Request_Builder_uri(v___x_1638_, v_uri_1637_);
return v___x_1639_;
}
}
static lean_object* _init_l_Std_Http_Request_connect___closed__0(void){
_start:
{
uint8_t v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = 5;
v___x_1641_ = l_Std_Http_Request_new;
v___x_1642_ = l_Std_Http_Request_Builder_method(v___x_1641_, v___x_1640_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_connect(lean_object* v_uri_1643_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = lean_obj_once(&l_Std_Http_Request_connect___closed__0, &l_Std_Http_Request_connect___closed__0_once, _init_l_Std_Http_Request_connect___closed__0);
v___x_1645_ = l_Std_Http_Request_Builder_uri(v___x_1644_, v_uri_1643_);
return v___x_1645_;
}
}
static lean_object* _init_l_Std_Http_Request_trace___closed__0(void){
_start:
{
uint8_t v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = 32;
v___x_1647_ = l_Std_Http_Request_new;
v___x_1648_ = l_Std_Http_Request_Builder_method(v___x_1647_, v___x_1646_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_trace(lean_object* v_uri_1649_){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_obj_once(&l_Std_Http_Request_trace___closed__0, &l_Std_Http_Request_trace___closed__0_once, _init_l_Std_Http_Request_trace___closed__0);
v___x_1651_ = l_Std_Http_Request_Builder_uri(v___x_1650_, v_uri_1649_);
return v___x_1651_;
}
}
lean_object* runtime_initialize_Std_Http_Data_Extensions(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Method(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Version(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Headers(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_URI(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Request(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1 = _init_l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1();
lean_mark_persistent(l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1);
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
